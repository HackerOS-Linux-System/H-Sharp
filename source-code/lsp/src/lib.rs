mod diagnostics;
mod symbols;
mod hover;
mod completion;
mod docstore;

use lsp_server::{Connection, Message, Notification, Request, RequestId, Response};
use lsp_types::{
    notification::{DidChangeTextDocument, DidCloseTextDocument, DidOpenTextDocument, Notification as _, PublishDiagnostics},
    request::{Completion, DocumentSymbolRequest, HoverRequest, Request as _},
    HoverProviderCapability, InitializeParams, OneOf, PublishDiagnosticsParams,
    ServerCapabilities, TextDocumentSyncCapability, TextDocumentSyncKind,
    CompletionOptions,
};

use docstore::DocStore;

fn main() -> anyhow::Result<()> {
    // stdio is the transport every LSP client speaks by default — no
    // socket/port configuration needed on the editor side at all, which
    // is exactly why LSP servers conventionally default to it.
    let (connection, io_threads) = Connection::stdio();

    let server_capabilities = ServerCapabilities {
        text_document_sync: Some(TextDocumentSyncCapability::Kind(TextDocumentSyncKind::FULL)),
        hover_provider: Some(HoverProviderCapability::Simple(true)),
        document_symbol_provider: Some(OneOf::Left(true)),
        completion_provider: Some(CompletionOptions {
            trigger_characters: Some(vec![":".to_string(), ".".to_string()]),
            ..Default::default()
        }),
        ..Default::default()
    };

    let initialize_params = connection.initialize(serde_json::to_value(server_capabilities)?)?;
    let _params: InitializeParams = serde_json::from_value(initialize_params)?;

    let mut docs = DocStore::new();
    main_loop(&connection, &mut docs)?;
    io_threads.join()?;
    Ok(())
}

fn main_loop(connection: &Connection, docs: &mut DocStore) -> anyhow::Result<()> {
    for msg in &connection.receiver {
        match msg {
            Message::Request(req) => {
                if connection.handle_shutdown(&req)? {
                    return Ok(());
                }
                handle_request(connection, docs, req)?;
            }
            Message::Notification(not) => {
                handle_notification(connection, docs, not)?;
            }
            Message::Response(_) => {
                // We don't currently send requests *to* the client (e.g.
                // `workspace/configuration`), so we never expect a
                // response back — nothing to do here yet.
            }
        }
    }
    Ok(())
}

fn handle_request(connection: &Connection, docs: &DocStore, req: Request) -> anyhow::Result<()> {
    match req.method.as_str() {
        DocumentSymbolRequest::METHOD => {
            let (id, params) = cast_request::<DocumentSymbolRequest>(req)?;
            let result = docs.get(&params.text_document.uri)
                .map(|doc| symbols::document_symbols(&doc.text))
                .unwrap_or_else(|| lsp_types::DocumentSymbolResponse::Nested(vec![]));
            respond(connection, id, result)?;
        }
        HoverRequest::METHOD => {
            let (id, params) = cast_request::<HoverRequest>(req)?;
            let uri = &params.text_document_position_params.text_document.uri;
            let pos = params.text_document_position_params.position;
            let result = docs.get(uri).and_then(|doc| hover::hover_at(&doc.text, pos));
            respond(connection, id, result)?;
        }
        Completion::METHOD => {
            let (id, params) = cast_request::<Completion>(req)?;
            let uri = &params.text_document_position.text_document.uri;
            let result = docs.get(uri)
                .map(|doc| completion::completions(&doc.text))
                .unwrap_or_else(completion::builtin_completions);
            respond(connection, id, Some(lsp_types::CompletionResponse::Array(result)))?;
        }
        _ => {}
    }
    Ok(())
}

fn handle_notification(connection: &Connection, docs: &mut DocStore, not: Notification) -> anyhow::Result<()> {
    match not.method.as_str() {
        DidOpenTextDocument::METHOD => {
            let params: lsp_types::DidOpenTextDocumentParams = serde_json::from_value(not.params)?;
            let uri = params.text_document.uri.clone();
            docs.open(uri.clone(), params.text_document.text);
            publish_diagnostics(connection, docs, &uri)?;
        }
        DidChangeTextDocument::METHOD => {
            let params: lsp_types::DidChangeTextDocumentParams = serde_json::from_value(not.params)?;
            let uri = params.text_document.uri.clone();
            // FULL sync (see `text_document_sync` above): each change
            // event carries the document's entire new text, so there's no
            // incremental patching to do here — simplest correct thing
            // for a first version, at the cost of re-sending the whole
            // document on every keystroke (fine at H#-program sizes; would
            // need incremental sync for huge files).
            if let Some(change) = params.content_changes.into_iter().last() {
                docs.update(uri.clone(), change.text);
            }
            publish_diagnostics(connection, docs, &uri)?;
        }
        DidCloseTextDocument::METHOD => {
            let params: lsp_types::DidCloseTextDocumentParams = serde_json::from_value(not.params)?;
            docs.close(&params.text_document.uri);
        }
        _ => {}
    }
    Ok(())
}

fn publish_diagnostics(connection: &Connection, docs: &DocStore, uri: &lsp_types::Url) -> anyhow::Result<()> {
    let Some(doc) = docs.get(uri) else { return Ok(()); };
    let diags = diagnostics::compute(&doc.text, uri.as_str());
    let params = PublishDiagnosticsParams { uri: uri.clone(), diagnostics: diags, version: None };
    connection.sender.send(Message::Notification(Notification {
        method: PublishDiagnostics::METHOD.to_string(),
        params: serde_json::to_value(params)?,
    }))?;
    Ok(())
}

fn cast_request<R>(req: Request) -> anyhow::Result<(RequestId, R::Params)>
where
    R: lsp_types::request::Request,
    R::Params: serde::de::DeserializeOwned,
{
    let params = serde_json::from_value(req.params)?;
    Ok((req.id, params))
}

fn respond<T: serde::Serialize>(connection: &Connection, id: RequestId, result: T) -> anyhow::Result<()> {
    connection.sender.send(Message::Response(Response {
        id,
        result: Some(serde_json::to_value(result)?),
        error: None,
    }))?;
    Ok(())
}
