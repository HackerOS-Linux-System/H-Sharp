use colored::Colorize;
use std::collections::HashMap;
use std::process::Command;
use std::path::PathBuf;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ScriptError {
    #[error("Błąd komendy `{cmd}`: {reason}")]
    CommandFailed { cmd: String, reason: String },

    #[error("Niezdefiniowana zmienna: ${0}")]
    UndefinedVar(String),

    #[error("Zależność `{pkg}` nie jest dostępna i nie udało się jej zainstalować.\n  Powód: {reason}\n  Spróbuj ręcznie: sudo apt install -y {pkg}")]
    DepFailed { pkg: String, reason: String },

    #[error("Błąd parsowania w linii {line}: {msg}")]
    ParseError { line: usize, msg: String },

    #[error("IO: {0}")]
    Io(#[from] std::io::Error),
}

/// Typ wartości w skrypcie
#[derive(Debug, Clone)]
pub enum ScriptVal {
    Str(String),
    Int(i64),
    Float(f64),
    Bool(bool),
    List(Vec<ScriptVal>),
    Nil,
}

impl ScriptVal {
    pub fn to_str(&self) -> String {
        match self {
            ScriptVal::Str(s)   => s.clone(),
            ScriptVal::Int(n)   => n.to_string(),
            ScriptVal::Float(f) => f.to_string(),
            ScriptVal::Bool(b)  => b.to_string(),
            ScriptVal::Nil      => String::new(),
            ScriptVal::List(v)  => v.iter().map(|x| x.to_str()).collect::<Vec<_>>().join(" "),
        }
    }

    pub fn is_truthy(&self) -> bool {
        match self {
            ScriptVal::Bool(b)  => *b,
            ScriptVal::Nil      => false,
            ScriptVal::Int(0)   => false,
            ScriptVal::Str(s)   => !s.is_empty(),
            ScriptVal::List(v)  => !v.is_empty(),
            _                   => true,
        }
    }
}

/// Węzły AST skryptu
#[derive(Debug, Clone)]
pub enum ScriptNode {
    /// // pkg1 pkg2  - zależności systemowe
    Dep(Vec<String>),
    /// $nazwa = expr
    Assign { name: String, value: ScriptExpr },
    /// ;; args...
    Print(Vec<ScriptExpr>),
    /// > / >> / >>> komenda args
    Shell { cmd: String, args: Vec<ScriptExpr>, mode: ShellMode },
    /// > cmd | cmd | cmd
    Pipe(Vec<(String, Vec<ScriptExpr>)>),
    /// ? cond [ body ] ?? [ else ]
    If { cond: ScriptCond, body: Vec<ScriptNode>, else_body: Vec<ScriptNode> },
    /// @ $var w iter [ body ]
    For { var: String, iter: ScriptIter, body: Vec<ScriptNode> },
    /// ;fn nazwa $args [ body ]
    FnDef { name: String, params: Vec<String>, body: Vec<ScriptNode> },
    /// ;call nazwa args
    FnCall { name: String, args: Vec<ScriptExpr> },
    /// ;exit kod
    Exit(i32),
    /// Pusty / komentarz
    Noop,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ShellMode {
    Normal,   // >
    WithVars, // >>
    Isolated, // >>>
}

#[derive(Debug, Clone)]
pub enum ScriptExpr {
    Lit(String),
    Var(String),
    EnvVar(String),
    Capture(String, Vec<ScriptExpr>),
    Interp(Vec<ScriptExpr>),
}

impl ScriptExpr {
    pub fn resolve(&self, env: &ScriptEnv) -> Result<String, ScriptError> {
        match self {
            ScriptExpr::Lit(s)   => Ok(s.clone()),
            ScriptExpr::Var(n)   => {
                env.get(n).map(|v| v.to_str())
                .ok_or_else(|| ScriptError::UndefinedVar(n.clone()))
            }
            ScriptExpr::EnvVar(n) => Ok(std::env::var(n).unwrap_or_default()),
            ScriptExpr::Interp(parts) => {
                let mut out = String::new();
                for p in parts { out.push_str(&p.resolve(env)?); }
                Ok(out)
            }
            ScriptExpr::Capture(cmd, args) => {
                let mut a = Vec::new();
                for x in args { a.push(x.resolve(env)?); }
                let out = Command::new(cmd).args(&a).output()
                .map_err(|e| ScriptError::CommandFailed { cmd: cmd.clone(), reason: e.to_string() })?;
                Ok(String::from_utf8_lossy(&out.stdout).trim_end_matches('\n').to_string())
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum ScriptCond {
    Eq(ScriptExpr, ScriptExpr),
    NotEq(ScriptExpr, ScriptExpr),
    Lt(ScriptExpr, ScriptExpr),
    Gt(ScriptExpr, ScriptExpr),
    Truthy(ScriptExpr),
    Not(Box<ScriptCond>),
    And(Box<ScriptCond>, Box<ScriptCond>),
    Or(Box<ScriptCond>, Box<ScriptCond>),
}

#[derive(Debug, Clone)]
pub enum ScriptIter {
    Range(i64, i64),
    Expr(ScriptExpr),
    Capture(String, Vec<ScriptExpr>),
}

/// Środowisko wykonania skryptu
pub struct ScriptEnv {
    vars: HashMap<String, ScriptVal>,
    fns:  HashMap<String, (Vec<String>, Vec<ScriptNode>)>,
    pub cwd: PathBuf,
    /// Kod wyjścia ostatniej komendy (dostępny jako %?)
    pub last_exit: i32,
}

impl ScriptEnv {
    pub fn new() -> Self {
        Self {
            vars: HashMap::new(),
            fns:  HashMap::new(),
            cwd:  std::env::current_dir().unwrap_or_else(|_| PathBuf::from(".")),
            last_exit: 0,
        }
    }

    pub fn get(&self, name: &str) -> Option<&ScriptVal> {
        self.vars.get(name)
    }

    pub fn set(&mut self, name: String, val: ScriptVal) {
        self.vars.insert(name, val);
    }

    pub fn def_fn(&mut self, name: String, params: Vec<String>, body: Vec<ScriptNode>) {
        self.fns.insert(name, (params, body));
    }

    pub fn get_fn(&self, name: &str) -> Option<&(Vec<String>, Vec<ScriptNode>)> {
        self.fns.get(name)
    }
}

impl Default for ScriptEnv { fn default() -> Self { Self::new() } }

/// Główny runner skryptu
pub struct ScriptRunner {
    pub env: ScriptEnv,
}

impl ScriptRunner {
    pub fn new() -> Self { Self { env: ScriptEnv::new() } }

    pub fn run(&mut self, nodes: &[ScriptNode]) -> Result<(), ScriptError> {
        for node in nodes { self.run_node(node)?; }
        Ok(())
    }

    fn run_node(&mut self, node: &ScriptNode) -> Result<(), ScriptError> {
        match node {
            ScriptNode::Noop => {}

            // ── // pkg1 pkg2 ───────────────────────────────────────────────
            ScriptNode::Dep(pkgs) => {
                for pkg in pkgs { self.ensure_dep(pkg)?; }
            }

            // ── $var = expr ────────────────────────────────────────────────
            ScriptNode::Assign { name, value } => {
                let s = value.resolve(&self.env)?;
                let typed = if let Ok(n) = s.parse::<i64>() { ScriptVal::Int(n) }
                else if let Ok(f) = s.parse::<f64>() { ScriptVal::Float(f) }
                else { ScriptVal::Str(s) };
                self.env.set(name.clone(), typed);
            }

            // ── ;; args ────────────────────────────────────────────────────
            ScriptNode::Print(args) => {
                let parts: Vec<String> = args.iter()
                .map(|a| a.resolve(&self.env))
                .collect::<Result<_, _>>()?;
                println!("{}", parts.join(" "));
            }

            // ── > / >> / >>> komenda ───────────────────────────────────────
            ScriptNode::Shell { cmd, args, mode } => {
                let code = self.exec_shell(cmd, args, mode)?;
                self.env.last_exit = code;
                self.env.set("?".to_string(), ScriptVal::Int(code as i64));
            }

            // ── pipe ───────────────────────────────────────────────────────
            ScriptNode::Pipe(steps) => {
                let code = self.exec_pipe(steps)?;
                self.env.last_exit = code;
                self.env.set("?".to_string(), ScriptVal::Int(code as i64));
            }

            // ── ? cond [ ] ?? [ ] ──────────────────────────────────────────
            ScriptNode::If { cond, body, else_body } => {
                if self.eval_cond(cond)? { self.run(body)? }
                else { self.run(else_body)? }
            }

            // ── @ $var w iter [ ] ─────────────────────────────────────────
            ScriptNode::For { var, iter, body } => {
                for item in self.resolve_iter(iter)? {
                    self.env.set(var.clone(), ScriptVal::Str(item));
                    self.run(body)?;
                }
            }

            // ── ;fn ───────────────────────────────────────────────────────
            ScriptNode::FnDef { name, params, body } => {
                self.env.def_fn(name.clone(), params.clone(), body.clone());
            }

            // ── ;call ─────────────────────────────────────────────────────
            ScriptNode::FnCall { name, args } => {
                let (params, body) = self.env.get_fn(name)
                .cloned()
                .ok_or_else(|| ScriptError::UndefinedVar(format!("fn:{}", name)))?;

                let arg_vals: Vec<String> = args.iter()
                .map(|a| a.resolve(&self.env))
                .collect::<Result<_, _>>()?;

                let mut saved: HashMap<String, Option<ScriptVal>> = HashMap::new();
                for (i, p) in params.iter().enumerate() {
                    saved.insert(p.clone(), self.env.vars.get(p).cloned());
                    let v = arg_vals.get(i).cloned().unwrap_or_default();
                    self.env.set(p.clone(), ScriptVal::Str(v));
                }

                self.run(&body)?;

                for (p, old) in saved {
                    match old {
                        Some(v) => { self.env.set(p, v); }
                        None    => { self.env.vars.remove(&p); }
                    }
                }
            }

            ScriptNode::Exit(code) => std::process::exit(*code),
        }
        Ok(())
    }

    // ── Wykonanie komendy ──────────────────────────────────────────────────

    fn exec_shell(
        &self,
        cmd: &str,
        args: &[ScriptExpr],
        mode: &ShellMode,
    ) -> Result<i32, ScriptError> {
        let args_r: Vec<String> = args.iter()
        .map(|a| a.resolve(&self.env))
        .collect::<Result<_, _>>()?;

        let mut command = match mode {
            ShellMode::Isolated => {
                let mut c = Command::new(cmd);
                c.env_clear();
                c.env("PATH", "/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin");
                c.env("HOME", std::env::var("HOME").unwrap_or_default());
                c
            }
            _ => Command::new(cmd),
        };

        command.args(&args_r).current_dir(&self.env.cwd);

        if *mode == ShellMode::WithVars {
            for (k, v) in &self.env.vars {
                command.env(k.to_uppercase(), v.to_str());
            }
        }

        let status = command.status()
        .map_err(|e| ScriptError::CommandFailed {
            cmd: cmd.to_string(),
                 reason: e.to_string(),
        })?;

        let code = status.code().unwrap_or(-1);
        if !status.success() {
            eprintln!("{} `{}` → kod wyjścia {}", "⚠".yellow(), cmd, code);
        }
        Ok(code)
    }

    fn exec_pipe(&self, steps: &[(String, Vec<ScriptExpr>)]) -> Result<i32, ScriptError> {
        if steps.is_empty() { return Ok(0); }

        let mut parts = Vec::new();
        for (cmd, args) in steps {
            let mut tokens = vec![cmd.clone()];
            for a in args { tokens.push(a.resolve(&self.env)?); }
            let quoted = tokens.iter()
            .map(|s| format!("'{}'", s.replace('\'', "'\\''")))
            .collect::<Vec<_>>()
            .join(" ");
            parts.push(quoted);
        }

        let pipe_str = parts.join(" | ");
        let status = Command::new("sh")
        .arg("-c")
        .arg(&pipe_str)
        .current_dir(&self.env.cwd)
        .status()
        .map_err(|e| ScriptError::CommandFailed {
            cmd: pipe_str.clone(),
                 reason: e.to_string(),
        })?;

        let code = status.code().unwrap_or(-1);
        if !status.success() {
            eprintln!("{} pipe → kod {}", "⚠".yellow(), code);
        }
        Ok(code)
    }

    fn eval_cond(&self, cond: &ScriptCond) -> Result<bool, ScriptError> {
        match cond {
            ScriptCond::Truthy(e) => {
                Ok(ScriptVal::Str(e.resolve(&self.env)?).is_truthy())
            }
            ScriptCond::Eq(a, b)  => Ok(a.resolve(&self.env)? == b.resolve(&self.env)?),
            ScriptCond::NotEq(a, b) => Ok(a.resolve(&self.env)? != b.resolve(&self.env)?),
            ScriptCond::Lt(a, b)  => {
                let av = a.resolve(&self.env)?.parse::<f64>().unwrap_or(0.0);
                let bv = b.resolve(&self.env)?.parse::<f64>().unwrap_or(0.0);
                Ok(av < bv)
            }
            ScriptCond::Gt(a, b)  => {
                let av = a.resolve(&self.env)?.parse::<f64>().unwrap_or(0.0);
                let bv = b.resolve(&self.env)?.parse::<f64>().unwrap_or(0.0);
                Ok(av > bv)
            }
            ScriptCond::Not(c)    => Ok(!self.eval_cond(c)?),
            ScriptCond::And(a, b) => Ok(self.eval_cond(a)? && self.eval_cond(b)?),
            ScriptCond::Or(a, b)  => Ok(self.eval_cond(a)? || self.eval_cond(b)?),
        }
    }

    fn resolve_iter(&mut self, iter: &ScriptIter) -> Result<Vec<String>, ScriptError> {
        match iter {
            ScriptIter::Range(from, to) => {
                Ok((*from..*to).map(|n| n.to_string()).collect())
            }
            ScriptIter::Expr(e) => {
                let val = e.resolve(&self.env)?;
                Ok(val.lines().map(|l| l.to_string()).filter(|l| !l.is_empty()).collect())
            }
            ScriptIter::Capture(cmd, args) => {
                let args_r: Vec<String> = args.iter()
                .map(|a| a.resolve(&self.env))
                .collect::<Result<_, _>>()?;
                let out = Command::new(cmd)
                .args(&args_r)
                .output()
                .map_err(|e| ScriptError::CommandFailed {
                    cmd: cmd.clone(),
                         reason: e.to_string(),
                })?;
                Ok(String::from_utf8_lossy(&out.stdout)
                .lines()
                .filter(|l| !l.is_empty())
                .map(|l| l.to_string())
                .collect())
            }
        }
    }

    // ── Zależności systemowe // pkg ────────────────────────────────────────

    fn ensure_dep(&self, pkg: &str) -> Result<(), ScriptError> {
        // 1. Sprawdź czy jest w PATH (np. curl, git, node)
        if which::which(pkg).is_ok() {
            println!("{} {} dostępny", "✓".green(), pkg.bold());
            return Ok(());
        }

        // 2. Sprawdź przez dpkg -l (zainstalowany ale może nie w PATH)
        if let Ok(out) = Command::new("dpkg").args(["-l", pkg]).output() {
            if out.status.success() {
                let stdout = String::from_utf8_lossy(&out.stdout);
                if stdout.contains(&format!("ii  {}", pkg)) {
                    println!("{} {} zainstalowany (dpkg)", "✓".green(), pkg.bold());
                    return Ok(());
                }
            }
        }

        // 3. Pakiet nie znaleziony - próbuj apt install
        println!("{} {} nie znaleziony - instaluję...", "→".cyan(), pkg.bold());

        // Najpierw apt-get update (cicho)
        let _ = Command::new("sudo")
        .args(["apt-get", "update", "-qq"])
        .output();

        // Instalacja
        let result = Command::new("sudo")
        .args(["apt-get", "install", "-y", "--no-install-recommends", pkg])
        .output();

        match result {
            Ok(out) if out.status.success() => {
                println!("{} {} zainstalowany pomyślnie", "✓".green().bold(), pkg.bold());
                Ok(())
            }
            Ok(out) => {
                // apt nie zadziałało - pokaż błąd
                let stderr = String::from_utf8_lossy(&out.stderr);
                let apt_error = stderr.lines()
                .filter(|l| l.contains("E:") || l.contains("error"))
                .collect::<Vec<_>>()
                .join(", ");

                eprintln!(
                    "{} Nie można zainstalować `{}`",
                    "[BŁĄD ZALEŻNOŚCI]".red().bold(),
                          pkg.bold()
                );
                eprintln!("  {} {}", "→".red(), apt_error.trim());
                eprintln!(
                    "  {} Spróbuj ręcznie: {}",
                    "?".cyan(),
                          format!("sudo apt install -y {}", pkg).bold()
                );

                Err(ScriptError::DepFailed {
                    pkg: pkg.to_string(),
                    reason: apt_error,
                })
            }
            Err(e) => {
                eprintln!(
                    "{} Nie można uruchomić apt dla `{}`: {}",
                    "[BŁĄD ZALEŻNOŚCI]".red().bold(),
                          pkg.bold(),
                          e
                );
                Err(ScriptError::DepFailed {
                    pkg: pkg.to_string(),
                    reason: e.to_string(),
                })
            }
        }
    }
}

impl Default for ScriptRunner { fn default() -> Self { Self::new() } }

// ══════════════════════════════════════════════════════════════════
//  Parser sekcji skryptowej
// ══════════════════════════════════════════════════════════════════

pub struct ScriptParser<'a> {
    lines: Vec<&'a str>,
    pos:   usize,
}

impl<'a> ScriptParser<'a> {
    pub fn new(src: &'a str) -> Self {
        Self { lines: src.lines().collect(), pos: 0 }
    }

    pub fn parse_all(&mut self) -> Result<Vec<ScriptNode>, ScriptError> {
        let mut nodes = Vec::new();
        while self.pos < self.lines.len() {
            let line = self.lines[self.pos].trim();
            if line == "---" { self.pos += 1; break; }
            if let Some(node) = self.parse_line(line)? {
                nodes.push(node);
            }
            self.pos += 1;
        }
        Ok(nodes)
    }

    fn parse_line(&mut self, line: &str) -> Result<Option<ScriptNode>, ScriptError> {
        let line = line.trim();
        if line.is_empty() { return Ok(None); }

        // ! komentarz H# (jednolinijkowy)
        if line.starts_with('!') && !line.starts_with("!!") {
            return Ok(Some(ScriptNode::Noop));
        }

        // ── // zależność systemowa ─────────────────────────────────────────
        if line.starts_with("// ") || line == "//" {
            let rest = line.strip_prefix("//").unwrap_or("").trim();
            if rest.is_empty() { return Ok(Some(ScriptNode::Noop)); }
            let pkgs: Vec<String> = rest
            .split_whitespace()
            .map(|s| s.to_string())
            .collect();
            return Ok(Some(ScriptNode::Dep(pkgs)));
        }

        // ── $var = wartość ─────────────────────────────────────────────────
        if line.starts_with('$') {
            if let Some(eq_pos) = line.find(" = ") {
                let name = line[1..eq_pos].trim().to_string();
                let val_str = line[eq_pos + 3..].trim();

                // $var = > komenda  (przechwycenie)
                let value = if val_str.starts_with("> ") {
                    let shell_str = val_str.strip_prefix("> ").unwrap_or("").trim();
                    let mut parts = self.tokenize(shell_str);
                    if parts.is_empty() { return Ok(Some(ScriptNode::Noop)); }
                    let cmd = match parts.remove(0) {
                        ScriptExpr::Lit(s) => s,
                        other => return Err(ScriptError::ParseError {
                            line: self.pos,
                            msg: "Komenda musi być tekstem".to_string(),
                        }),
                    };
                    ScriptExpr::Capture(cmd, parts)
                } else {
                    self.parse_expr(val_str)
                };

                return Ok(Some(ScriptNode::Assign { name, value }));
            }
        }

        // ── ;; wyświetlanie ───────────────────────────────────────────────
        if line.starts_with(";;") {
            let rest = line.strip_prefix(";;").unwrap_or("").trim();
            let args = self.parse_expr_list(rest);
            return Ok(Some(ScriptNode::Print(args)));
        }

        // ── ;fn definicja ─────────────────────────────────────────────────
        if line.starts_with(";fn ") {
            return self.parse_fn_def(line);
        }

        // ── ;call wywołanie ───────────────────────────────────────────────
        if line.starts_with(";call ") {
            return self.parse_fn_call(line);
        }

        // ── ;exit ─────────────────────────────────────────────────────────
        if line.starts_with(";exit") {
            let code = line.strip_prefix(";exit").unwrap_or("").trim()
            .parse::<i32>().unwrap_or(0);
            return Ok(Some(ScriptNode::Exit(code)));
        }

        // ── ? warunek [ body ] ────────────────────────────────────────────
        if line.starts_with("? ") {
            return self.parse_if(line);
        }

        // ── @ $var w iter [ body ] ────────────────────────────────────────
        if line.starts_with("@ ") {
            return self.parse_for(line);
        }

        // ── >>> izolowana komenda ─────────────────────────────────────────
        if line.starts_with(">>> ") {
            let rest = line.strip_prefix(">>> ").unwrap_or("").trim();
            return self.parse_shell_line(rest, ShellMode::Isolated);
        }

        // ── >> ze zmiennymi ───────────────────────────────────────────────
        if line.starts_with(">> ") {
            let rest = line.strip_prefix(">> ").unwrap_or("").trim();
            return self.parse_shell_line(rest, ShellMode::WithVars);
        }

        // ── > komenda (lub pipe) ──────────────────────────────────────────
        if line.starts_with("> ") {
            let rest = line.strip_prefix("> ").unwrap_or("").trim();
            if rest.contains(" | ") {
                return self.parse_pipe(rest);
            }
            return self.parse_shell_line(rest, ShellMode::Normal);
        }

        Ok(None)
    }

    fn parse_shell_line(&self, rest: &str, mode: ShellMode) -> Result<Option<ScriptNode>, ScriptError> {
        let mut parts = self.tokenize(rest);
        if parts.is_empty() { return Ok(None); }
        let cmd = match parts.remove(0) {
            ScriptExpr::Lit(s) => s,
            _ => return Err(ScriptError::ParseError {
                line: self.pos,
                msg: "Komenda musi być tekstem".to_string(),
            }),
        };
        Ok(Some(ScriptNode::Shell { cmd, args: parts, mode }))
    }

    fn parse_pipe(&self, rest: &str) -> Result<Option<ScriptNode>, ScriptError> {
        let steps: Vec<(String, Vec<ScriptExpr>)> = rest
        .split(" | ")
        .map(|step| {
            let mut parts = self.tokenize(step.trim());
            let cmd = match parts.first() {
                Some(ScriptExpr::Lit(s)) => s.clone(),
             _ => "sh".to_string(),
            };
            if !parts.is_empty() { parts.remove(0); }
            (cmd, parts)
        })
        .collect();
        Ok(Some(ScriptNode::Pipe(steps)))
    }

    fn parse_if(&mut self, line: &str) -> Result<Option<ScriptNode>, ScriptError> {
        // ? $a == "b" [
        let rest = line.strip_prefix("? ").unwrap_or("").trim().trim_end_matches('[').trim();
        let cond = self.parse_cond(rest);
        self.pos += 1;
        let body = self.parse_block()?;

        let else_body = if self.pos < self.lines.len() {
            let next = self.lines[self.pos].trim();
            if next.starts_with("?? [") || next == "??[" || next == "??" {
                self.pos += 1;
                self.parse_block()?
            } else { vec![] }
        } else { vec![] };

        Ok(Some(ScriptNode::If { cond, body, else_body }))
    }

    fn parse_for(&mut self, line: &str) -> Result<Option<ScriptNode>, ScriptError> {
        // @ $i w 1..5 [
        // @ $plik w > ls /tmp [
        let rest = line.strip_prefix("@ ").unwrap_or("").trim().trim_end_matches('[').trim();

        let w_idx = rest.find(" w ").ok_or_else(|| ScriptError::ParseError {
            line: self.pos,
            msg: "Brak 'w' w pętli @ - użyj: @ $var w 1..5 [".to_string(),
        })?;

        let var = rest[..w_idx].trim().trim_start_matches('$').to_string();
        let iter_str = rest[w_idx + 3..].trim();

        let iter = if iter_str.starts_with("> ") {
            let shell_part = iter_str.strip_prefix("> ").unwrap_or("").trim();
            let mut parts = self.tokenize(shell_part);
            let cmd = match parts.first() {
                Some(ScriptExpr::Lit(s)) => s.clone(),
                _ => "sh".to_string(),
            };
            if !parts.is_empty() { parts.remove(0); }
            ScriptIter::Capture(cmd, parts)
        } else if iter_str.contains("..") {
            let v: Vec<&str> = iter_str.splitn(2, "..").collect();
            let from = v.first().and_then(|s| s.parse::<i64>().ok()).unwrap_or(0);
            let to   = v.get(1).and_then(|s| s.trim_start_matches('=').parse::<i64>().ok()).unwrap_or(0);
            // 1..=5 → range include
            let to = if iter_str.contains("..=") { to + 1 } else { to };
            ScriptIter::Range(from, to)
        } else {
            ScriptIter::Expr(self.parse_expr(iter_str))
        };

        self.pos += 1;
        let body = self.parse_block()?;
        Ok(Some(ScriptNode::For { var, iter, body }))
    }

    fn parse_fn_def(&mut self, line: &str) -> Result<Option<ScriptNode>, ScriptError> {
        // ;fn nazwa $arg1 $arg2 [
        let rest = line.strip_prefix(";fn ").unwrap_or("").trim().trim_end_matches('[').trim();
        let mut parts = rest.split_whitespace();
        let name = parts.next().unwrap_or("").to_string();
        let params: Vec<String> = parts.map(|p| p.trim_start_matches('$').to_string()).collect();
        self.pos += 1;
        let body = self.parse_block()?;
        Ok(Some(ScriptNode::FnDef { name, params, body }))
    }

    fn parse_fn_call(&self, line: &str) -> Result<Option<ScriptNode>, ScriptError> {
        // ;call nazwa arg1 arg2
        let rest = line.strip_prefix(";call ").unwrap_or("").trim();
        let mut it = rest.splitn(2, ' ');
        let name = it.next().unwrap_or("").to_string();
        let args_str = it.next().unwrap_or("").trim();
        let args = self.parse_expr_list(args_str);
        Ok(Some(ScriptNode::FnCall { name, args }))
    }

    fn parse_block(&mut self) -> Result<Vec<ScriptNode>, ScriptError> {
        let mut nodes = Vec::new();
        while self.pos < self.lines.len() {
            let line = self.lines[self.pos].trim();
            if line == "]" || line == "---" { self.pos += 1; break; }
            if let Some(node) = self.parse_line(line)? {
                nodes.push(node);
            }
            self.pos += 1;
        }
        Ok(nodes)
    }

    fn parse_cond(&self, s: &str) -> ScriptCond {
        let s = s.trim();
        if let Some((a, b)) = s.split_once(" == ") {
            ScriptCond::Eq(self.parse_expr(a.trim()), self.parse_expr(b.trim()))
        } else if let Some((a, b)) = s.split_once(" != ") {
            ScriptCond::NotEq(self.parse_expr(a.trim()), self.parse_expr(b.trim()))
        } else if let Some((a, b)) = s.split_once(" < ") {
            ScriptCond::Lt(self.parse_expr(a.trim()), self.parse_expr(b.trim()))
        } else if let Some((a, b)) = s.split_once(" > ") {
            ScriptCond::Gt(self.parse_expr(a.trim()), self.parse_expr(b.trim()))
        } else if let Some(rest) = s.strip_prefix("! ") {
            ScriptCond::Not(Box::new(self.parse_cond(rest)))
        } else {
            ScriptCond::Truthy(self.parse_expr(s))
        }
    }

    /// Parsuje pojedyncze wyrażenie
    fn parse_expr(&self, s: &str) -> ScriptExpr {
        let s = s.trim();

        // $zmienna
        if s.starts_with('$') && !s.contains(' ') {
            return ScriptExpr::Var(s[1..].to_string());
        }

        // %ENV_VAR
        if s.starts_with('%') && !s.contains(' ') {
            return ScriptExpr::EnvVar(s[1..].to_string());
        }

        // "cytowany string z $interpolacją"
        if s.starts_with('"') && s.ends_with('"') && s.len() >= 2 {
            let inner = &s[1..s.len()-1];
            if inner.contains('$') {
                return self.interp(inner);
            }
            return ScriptExpr::Lit(inner.to_string());
        }

        ScriptExpr::Lit(s.to_string())
    }

    /// Parsuje listę wyrażeń oddzielonych spacjami (z cytatami)
    fn parse_expr_list(&self, s: &str) -> Vec<ScriptExpr> {
        self.tokenize(s)
    }

    /// Tokenizuje linie z szanowaniem "cytatów" i $zmiennych
    fn tokenize(&self, s: &str) -> Vec<ScriptExpr> {
        let mut result = Vec::new();
        let mut cur = String::new();
        let mut in_quote = false;
        let chars: Vec<char> = s.trim().chars().collect();
        let mut i = 0;

        while i < chars.len() {
            match chars[i] {
                '"' if !in_quote => { in_quote = true; i += 1; }
                '"' if in_quote  => {
                    in_quote = false;
                    if cur.contains('$') { result.push(self.interp(&cur)); }
                    else { result.push(ScriptExpr::Lit(cur.clone())); }
                    cur.clear();
                    i += 1;
                }
                ' ' | '\t' if !in_quote => {
                    if !cur.is_empty() {
                        result.push(self.atom(&cur));
                        cur.clear();
                    }
                    i += 1;
                }
                c => { cur.push(c); i += 1; }
            }
        }
        if !cur.is_empty() { result.push(self.atom(&cur)); }
        result
    }

    fn atom(&self, s: &str) -> ScriptExpr {
        if s.starts_with('$') { ScriptExpr::Var(s[1..].to_string()) }
        else if s.starts_with('%') { ScriptExpr::EnvVar(s[1..].to_string()) }
        else { ScriptExpr::Lit(s.to_string()) }
    }

    /// Parsuje string z $interpolacjami: "cześć $imie jak się masz"
    fn interp(&self, s: &str) -> ScriptExpr {
        let mut parts = Vec::new();
        let mut cur = String::new();
        let chars: Vec<char> = s.chars().collect();
        let mut i = 0;

        while i < chars.len() {
            if chars[i] == '$' {
                if !cur.is_empty() { parts.push(ScriptExpr::Lit(cur.clone())); cur.clear(); }
                i += 1;
                let mut var = String::new();
                while i < chars.len() && (chars[i].is_alphanumeric() || chars[i] == '_') {
                    var.push(chars[i]); i += 1;
                }
                parts.push(ScriptExpr::Var(var));
            } else {
                cur.push(chars[i]); i += 1;
            }
        }
        if !cur.is_empty() { parts.push(ScriptExpr::Lit(cur)); }

        if parts.len() == 1 { parts.remove(0) } else { ScriptExpr::Interp(parts) }
    }
}

// ══════════════════════════════════════════════════════════════════
//  Publiczne API
// ══════════════════════════════════════════════════════════════════

/// Parsuje i uruchamia sekcję skryptową z tekstu
pub fn run_script_section(src: &str) -> Result<(), ScriptError> {
    let mut parser = ScriptParser::new(src);
    let nodes = parser.parse_all()?;
    let mut runner = ScriptRunner::new();
    runner.run(&nodes)
}

/// Uruchamia plik .hl przez interpreter H#
pub fn run_hl_file(path: &std::path::Path) -> Result<(), Box<dyn std::error::Error>> {
    hsharp_compiler::interpreter::run_file(path)?;
    Ok(())
}

/// Sprawdza składnię pliku .hl
pub fn check_hl_file(path: &std::path::Path) -> Result<(), Box<dyn std::error::Error>> {
    let source = std::fs::read_to_string(path)?;
    let name = path.file_stem().and_then(|s| s.to_str()).unwrap_or("script");
    let _module = hsharp_parser::parse(&source, name)?;
    println!("{} {} - składnia poprawna", "✓".green(), path.display());
    Ok(())
}
