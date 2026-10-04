use colored::Colorize;
use std::path::{Path, PathBuf};

use hsharp_compiler::{compile, CompileOptions, OutputKind, TargetTriple};
use hsharp_hlib::{HlibArchive, HlibBuilder, Language};

use crate::LibCommand;

pub fn run(cmd: LibCommand) {
    match cmd {
        LibCommand::Build { file, output, lib_version, target, sign, release } => {
            cmd_build(file, output, lib_version, target, sign, release)
        }
        LibCommand::Inspect { file } => cmd_inspect(&file),
        LibCommand::Verify { file, pubkey } => cmd_verify(&file, pubkey.as_deref()),
        LibCommand::Keygen { out } => cmd_keygen(&out),
        LibCommand::Bind { file, into } => cmd_bind(&file, &into),
    }
}

fn die(msg: impl AsRef<str>) -> ! {
    eprintln!("{} {}", "Error:".red().bold(), msg.as_ref());
    std::process::exit(1);
}

// ─── h# lib build ───────────────────────────────────────────────────────────

fn cmd_build(
    file: PathBuf,
    output: Option<String>,
    lib_version: String,
    target: Option<String>,
    sign: Option<PathBuf>,
    release: bool,
) {
    let stem = file.file_stem().and_then(|s| s.to_str()).unwrap_or("mylib").to_string();
    let out_hlib = output.unwrap_or_else(|| format!("build/{}.hlib", stem));
    if let Some(parent) = Path::new(&out_hlib).parent() {
        std::fs::create_dir_all(parent).ok();
    }
    std::fs::create_dir_all("build").ok();

    let triple = match target {
        Some(t) => TargetTriple::from_str(&t).unwrap_or_else(|| die(format!("unknown target `{t}`. Run `h# targets` to list them."))),
        None => TargetTriple::host(),
    };

    // ── Read + parse (identical to `h# compile`) ────────────────────────
    let source = std::fs::read_to_string(&file)
        .unwrap_or_else(|e| die(format!("cannot read `{}`: {}", file.display(), e)));
    crate::edition_cmd::begin_build();
    let parsed = hsharp_parser::parse(&source, &file.display().to_string());
    if parsed.has_errors() {
        eprintln!("{}", parsed.render_errors());
        die("parsing failed.");
    }
    // The edition the library's sources are written against (its own
    // `using`, else the default resolved in `main`) — recorded in the
    // manifest so consumers on any edition can tell what they're linking.
    let lib_edition = hsharp_parser::edition::effective_edition(&parsed.module);

    // ── Resolve `mod`/`use "std -> x"`/`use "bit -> x"` ─────────────────
    let mut module = parsed.module.clone();
    {
        let mut resolver = hsharp_compiler::modules::ModuleResolver::new(&file);
        let entry_dir = file.parent().unwrap_or_else(|| Path::new("."));
        match resolver.expand_program(&module, entry_dir) {
            Ok(items) => module.items = items,
            Err(e) => die(format!("{}", e)),
        }
    }

    crate::edition_cmd::end_build(false);

    // ── Compile to a shared object at build/<stem>.hlib.tmp<suffix> ─────
    let tmp_stem = format!("build/.hlib-{}", stem);
    let opts = CompileOptions {
        target: triple.clone(),
        optimize: release,
        static_link: true,
        debug_info: false,
        output: tmp_stem.clone(),
        output_kind: OutputKind::SharedLib,
        default_mem_mode: None,
    };
    println!("  {} {} (target: {})", "Compiling:".green().bold(), file.display(), triple.llvm_triple);
    match compile(&module, &source, &opts) {
        Ok(()) => {}
        Err(hsharp_compiler::CompileError::Diagnostics(_)) => die("compilation failed (type errors above)."),
        Err(e) => die(format!("{}", e)),
    }
    let so_path = format!("{}{}", tmp_stem, opts.output_kind.file_suffix(&triple));
    let so_bytes = std::fs::read(&so_path)
        .unwrap_or_else(|e| die(format!("compiled .so vanished at `{}`: {}", so_path, e)));

    // ── Extract exports + AST from the *resolved* module ────────────────
    let summary = crate::hlib_export::summarize_exports(&module);
    let header_json = serde_json::to_vec_pretty(&summary.symbols)
        .unwrap_or_else(|e| die(format!("failed to serialize header: {e}")));
    let ast_json = serde_json::to_vec_pretty(&summary.pub_items)
        .unwrap_or_else(|e| die(format!("failed to serialize AST: {e}")));

    let generic_count = summary.symbols.iter().filter(|s| s.generic).count();
    println!(
        "  {} {} export(s) ({} generic — carried via AST only)",
        "Exports:".green().bold(),
        summary.symbols.len(),
        generic_count
    );

    // ── Package ──────────────────────────────────────────────────────────
    let mut builder = HlibBuilder::new(stem.clone(), lib_version, Language::Hsharp);
    builder.set_language_version(env!("CARGO_PKG_VERSION"));
    builder.set_edition(lib_edition.as_str());
    builder.add_shared_object(&triple.llvm_triple, &so_bytes).unwrap_or_else(|e| die(format!("{e}")));
    builder.add_header(&header_json).unwrap_or_else(|e| die(format!("{e}")));
    if !summary.pub_items.is_empty() {
        builder.add_ast(&ast_json).unwrap_or_else(|e| die(format!("{e}")));
    }
    for sym in &summary.symbols {
        builder.add_export(sym.clone());
    }

    let signing_key_hex = sign.map(|p| {
        std::fs::read_to_string(&p)
            .unwrap_or_else(|e| die(format!("cannot read signing key `{}`: {}", p.display(), e)))
            .trim()
            .to_string()
    });

    let manifest = builder
        .finish(Path::new(&out_hlib), signing_key_hex.as_deref())
        .unwrap_or_else(|e| die(format!("{e}")));

    let _ = std::fs::remove_file(&so_path);

    println!(
        "{} {} → {} ({} artifact(s){})",
        "✓".green().bold(),
        file.display(),
        out_hlib.bold(),
        manifest.artifacts.len(),
        if manifest.signature.is_some() { ", signed" } else { ", unsigned" },
    );
}

// ─── h# lib inspect ─────────────────────────────────────────────────────────

fn cmd_inspect(file: &Path) {
    let archive = HlibArchive::open(file).unwrap_or_else(|e| die(format!("{e}")));
    let m = &archive.manifest;
    println!("{} {} v{} ({})", "hlib:".bold(), m.name, m.version, m.language.as_str());
    println!("  spec version:     {}", m.hlib_spec_version);
    println!("  abi version:      {}", m.abi_version);
    println!("  built by:         {} {}", m.language.as_str(), m.language_version);
    if m.language == Language::Hsharp {
        println!("  edition:          {}", m.edition);
    }
    println!("  created at:       {}", m.created_at);
    if !m.description.is_empty() {
        println!("  description:      {}", m.description);
    }
    println!("  signed:           {}", if m.signature.is_some() { "yes" } else { "no" });
    if let Some(sig) = &m.signature {
        println!("    public key:     {}", sig.public_key);
    }
    println!("  artifacts ({}):", m.artifacts.len());
    for a in &m.artifacts {
        println!(
            "    {:<10} {:<45} {} bytes  sha256:{}",
            format!("{:?}", a.kind),
            a.path,
            a.size,
            &a.sha256[..16]
        );
    }
    println!("  exports ({}):", m.exports.len());
    for e in &m.exports {
        println!(
            "    {}{}",
            e.signature,
            if e.generic { "  [generic — AST only]" } else { "" }
        );
    }
}

// ─── h# lib verify ──────────────────────────────────────────────────────────

fn cmd_verify(file: &Path, pubkey: Option<&str>) {
    let archive = HlibArchive::open(file).unwrap_or_else(|e| die(format!("{e}")));
    archive.verify_checksums().unwrap_or_else(|e| die(format!("checksum verification failed: {e}")));
    println!("{} checksums OK ({} entries)", "✓".green().bold(), archive.manifest.artifacts.len());

    match pubkey {
        Some(pk) => {
            archive.verify_signature(pk).unwrap_or_else(|e| die(format!("signature verification failed: {e}")));
            println!("{} signature OK (public key {}…)", "✓".green().bold(), &pk[..pk.len().min(16)]);
        }
        None => {
            println!(
                "{} no --pubkey given — skipped signature verification (archive signed: {})",
                "!".yellow().bold(),
                archive.manifest.signature.is_some()
            );
        }
    }
}

// ─── h# lib keygen ──────────────────────────────────────────────────────────

fn cmd_keygen(out: &Path) {
    let (signing_hex, verifying_hex) = hsharp_hlib::sign::generate_keypair();
    std::fs::write(out, &signing_hex).unwrap_or_else(|e| die(format!("cannot write `{}`: {}", out.display(), e)));
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        if let Ok(meta) = std::fs::metadata(out) {
            let mut perms = meta.permissions();
            perms.set_mode(0o600);
            let _ = std::fs::set_permissions(out, perms);
        }
    }
    println!("{} secret signing key written to {} (keep it private!)", "✓".green().bold(), out.display());
    println!("  public key (share this / commit it to your trust store):");
    println!("  {}", verifying_hex.bold());
}

// ─── h# lib bind ────────────────────────────────────────────────────────────

fn cmd_bind(file: &Path, into: &Path) {
    let archive = HlibArchive::open(file).unwrap_or_else(|e| die(format!("{e}")));
    archive.verify_checksums().unwrap_or_else(|e| die(format!("checksum verification failed: {e}")));

    std::fs::create_dir_all(into).ok();
    archive.extract_to_dir(into).unwrap_or_else(|e| die(format!("{e}")));

    let m = &archive.manifest;
    let so_artifact = m.artifacts.iter().find(|a| matches!(a.kind, hsharp_hlib::ArtifactKind::SharedObject));

    let mut stub = String::new();
    stub.push_str(&format!("// Auto-generated by `h# lib bind` from {}\n", file.display()));
    stub.push_str(&format!("// {} v{} ({}) — do not edit by hand, re-run `h# lib bind` instead.\n\n", m.name, m.version, m.language.as_str()));

    let non_generic_fns: Vec<_> = m
        .exports
        .iter()
        .filter(|e| !e.generic && matches!(e.kind, hsharp_hlib::ExportedSymbolKind::Function))
        .collect();

    if let Some(so) = so_artifact {
        let lib_path = into.join(&so.path);
        stub.push_str(&format!(
            "extern dynamic [rust, \"{}\"] is\n",
            lib_path.display()
        ));
        for e in &non_generic_fns {
            stub.push_str(&format!("    {}\n", e.signature));
        }
        stub.push_str("end\n");
    }

    let generic_names: Vec<&str> = m.exports.iter().filter(|e| e.generic).map(|e| e.name.as_str()).collect();
    if !generic_names.is_empty() {
        stub.push_str(&format!(
            "\n// The following exports carry unresolved type parameters and are only\n// available via the AST artifact — see {}/ast/{}.ast.json.\n// H# does not yet auto-splice these into your module; for now, copy the\n// relevant source from the AST (or from the producer's own source) directly:\n// {}\n",
            into.display(), m.name, generic_names.join(", ")
        ));
    }

    let stub_path = into.join(format!("{}_hlib_bind.h#", m.name));
    std::fs::write(&stub_path, stub).unwrap_or_else(|e| die(format!("cannot write `{}`: {}", stub_path.display(), e)));

    println!("{} extracted {} artifact(s) to {}", "✓".green().bold(), m.artifacts.len(), into.display());
    println!("  generated binding: {}", stub_path.display().to_string().bold());
    println!("  use it with:       mod {}_hlib_bind;", m.name);
}
