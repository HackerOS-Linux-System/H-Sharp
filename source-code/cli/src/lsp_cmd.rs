pub fn run() {
    if let Err(e) = hsharp_lsp::run() {
        eprintln!("h# lsp: {}", e);
        std::process::exit(1);
    }
}
