use std::collections::HashMap;
use lsp_types::Url;

pub struct Document {
    pub text: String,
}

pub struct DocStore {
    docs: HashMap<Url, Document>,
}

impl DocStore {
    pub fn new() -> Self {
        Self { docs: HashMap::new() }
    }

    pub fn open(&mut self, uri: Url, text: String) {
        self.docs.insert(uri, Document { text });
    }

    pub fn update(&mut self, uri: Url, text: String) {
        self.docs.insert(uri, Document { text });
    }

    pub fn close(&mut self, uri: &Url) {
        self.docs.remove(uri);
    }

    pub fn get(&self, uri: &Url) -> Option<&Document> {
        self.docs.get(uri)
    }
}
