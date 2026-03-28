use colored::Colorize;

// ─── Typy diagnostyki ────────────────────────────────────────────────────────

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Severity {
    Error,
    Warning,
    Info,
    Hint,
}

impl Severity {
    fn label(&self) -> &'static str {
        match self {
            Severity::Error   => "błąd",
            Severity::Warning => "uwaga",
            Severity::Info    => "info",
            Severity::Hint    => "podpowiedź",
        }
    }

    fn emoji(&self) -> &'static str {
        match self {
            Severity::Error   => "✗",
            Severity::Warning => "⚠",
            Severity::Info    => "→",
            Severity::Hint    => "?",
        }
    }

    fn color(&self, s: &str) -> String {
        match self {
            Severity::Error   => s.red().bold().to_string(),
            Severity::Warning => s.yellow().bold().to_string(),
            Severity::Info    => s.cyan().to_string(),
            Severity::Hint    => s.green().to_string(),
        }
    }
}

// ─── Etykieta wskazująca miejsce w kodzie ────────────────────────────────────

#[derive(Debug, Clone)]
pub struct Label {
    /// Numer linii (1-based)
    pub line: usize,
    /// Kolumna startu (0-based)
    pub col_start: usize,
    /// Kolumna końca (0-based)
    pub col_end: usize,
    /// Wiadomość pod strzałkami
    pub message: String,
}

impl Label {
    pub fn new(line: usize, col_start: usize, col_end: usize, msg: impl Into<String>) -> Self {
        Self { line, col_start, col_end, message: msg.into() }
    }
}

// ─── Główna struktura diagnostyki ────────────────────────────────────────────

pub struct Diagnostic {
    pub severity:    Severity,
    pub title:       String,
    pub file:        Option<String>,
    pub source_lines: Vec<String>,
    pub labels:      Vec<Label>,
    pub explanation: Option<String>,
    pub suggestion:  Option<String>,
    pub note:        Option<String>,
    /// Tryb skryptowy - jeszcze bardziej przyjazny
    pub script_mode: bool,
}

impl Diagnostic {
    pub fn error(title: impl Into<String>) -> Self {
        Self {
            severity:     Severity::Error,
            title:        title.into(),
            file:         None,
            source_lines: vec![],
            labels:       vec![],
            explanation:  None,
            suggestion:   None,
            note:         None,
            script_mode:  false,
        }
    }

    pub fn warning(title: impl Into<String>) -> Self {
        Self { severity: Severity::Warning, title: title.into(), ..Self::error("") }
    }

    pub fn file(mut self, f: impl Into<String>) -> Self {
        self.file = Some(f.into()); self
    }

    pub fn source(mut self, src: &str) -> Self {
        self.source_lines = src.lines().map(|l| l.to_string()).collect(); self
    }

    pub fn label(mut self, l: Label) -> Self {
        self.labels.push(l); self
    }

    pub fn explain(mut self, e: impl Into<String>) -> Self {
        self.explanation = Some(e.into()); self
    }

    pub fn suggest(mut self, s: impl Into<String>) -> Self {
        self.suggestion = Some(s.into()); self
    }

    pub fn note(mut self, n: impl Into<String>) -> Self {
        self.note = Some(n.into()); self
    }

    pub fn script(mut self) -> Self {
        self.script_mode = true; self
    }

    // ── Renderowanie ─────────────────────────────────────────────────────────

    pub fn print(&self) {
        let sev   = &self.severity;
        let width = 60usize;

        // ╭─ nagłówek
        let file_part = self.file.as_deref().unwrap_or("?");
        let header = if self.script_mode {
            format!(
                "{}─ {} {} '{}' {}",
                "╭".dimmed(),
                    sev.emoji(),
                    sev.color(sev.label()),
                    file_part.bold(),
                    "─".repeat(width.saturating_sub(file_part.len() + 12))
            )
        } else {
            format!(
                "{}─[{}]─ {} {}",
                "╭".dimmed(),
                    sev.color(sev.label()),
                    "w pliku".dimmed(),
                    file_part.bold()
            )
        };
        println!("{}", header);

        // │ tytuł błędu
        println!("{}  {}", "│".dimmed(), sev.color(&self.title));
        println!("{}", "│".dimmed());

        // │ fragmenty kodu z etykietami
        for label in &self.labels {
            self.print_label(label);
        }

        // │ wyjaśnienie
        if let Some(exp) = &self.explanation {
            println!("{}", "│".dimmed());
            println!("{}  {} {}", "│".dimmed(), "Co się stało:".bold(), exp);
        }

        // │ sugestia
        if let Some(sug) = &self.suggestion {
            println!("{}", "│".dimmed());
            if self.script_mode {
                println!("{}  {} {}", "│".dimmed(), "Jak naprawić →".green().bold(), sug);
            } else {
                println!("{}  {} {}", "│".dimmed(), "Sugestia:".green().bold(), sug);
            }
        }

        // │ notatka
        if let Some(note) = &self.note {
            println!("{}", "│".dimmed());
            println!("{}  {} {}", "│".dimmed(), "Notatka:".cyan(), note);
        }

        // ╰─ stopka
        println!("{}", "╰────────────────────────────────────────────────────".dimmed());
        println!();
    }

    fn print_label(&self, label: &Label) {
        if self.source_lines.is_empty() { return; }

        let line_idx = label.line.saturating_sub(1);

        // Linia kontekstu przed
        if line_idx > 0 {
            if let Some(prev) = self.source_lines.get(line_idx - 1) {
                println!(
                    "{}  {} {} {}",
                    "│".dimmed(),
                         format!("{:>4}", label.line - 1).dimmed(),
                             "│".dimmed(),
                         prev.dimmed()
                );
            }
        }

        // Błędna linia
        if let Some(line_src) = self.source_lines.get(line_idx) {
            println!(
                "{}  {} {} {}",
                "│".dimmed(),
                     format!("{:>4}", label.line).yellow(),
                         "│".dimmed(),
                     line_src
            );

            // Strzałki ^^^^
            let col_s = label.col_start.min(line_src.len());
            let col_e = label.col_end.min(line_src.len()).max(col_s + 1);
            let arrows = "^".repeat(col_e - col_s);
            let pad    = " ".repeat(col_s);

            println!(
                "{}       {} {}  {}",
                "│".dimmed(),
                     "│".dimmed(),
                     format!("{}{}", pad, arrows).red().bold(),
                         label.message.red()
            );
        }

        // Linia kontekstu po
        if let Some(next) = self.source_lines.get(line_idx + 1) {
            println!(
                "{}  {} {} {}",
                "│".dimmed(),
                     format!("{:>4}", label.line + 1).dimmed(),
                         "│".dimmed(),
                     next.dimmed()
            );
        }
    }
}

// ─── Pomocnicze funkcje publiczne ─────────────────────────────────────────────

/// Wyświetla baner startowy H#
pub fn print_banner() {
    println!("{}", r#"  H# ─ HackerOS Language"#.cyan().bold());
    println!("{}", "  następca Hacker Lang · bezpieczna pamięć · składnia Ruby+Rust".dimmed());
    println!();
}

pub fn print_success(msg: &str) {
    println!("{} {}", "✓".green().bold(), msg.bold());
}

pub fn print_warning(msg: &str) {
    println!("{} {}", "⚠".yellow().bold(), msg);
}

pub fn print_info(msg: &str) {
    println!("{} {}", "→".cyan(), msg);
}

// ─── Tłumaczenie błędów kompilatora na przyjazny format ──────────────────────

pub fn print_compile_error(err: &hsharp_compiler::CompileError, file: &str, source: &str) {
    use hsharp_compiler::CompileError;

    match err {
        CompileError::Parse(msg) => {
            // Próbuj wyciągnąć numer linii z wiadomości parsera
            let (line, col, clean_msg) = extract_location(msg);

            let mut d = Diagnostic::error(
                friendly_parse_msg(&clean_msg)
            )
            .file(file)
            .source(source)
            .explain(&clean_msg)
            .suggest(parse_suggestion(&clean_msg));

            if let (Some(l), Some(c)) = (line, col) {
                let src_lines: Vec<&str> = source.lines().collect();
                let line_src = src_lines.get(l.saturating_sub(1)).copied().unwrap_or("");
                let end_col = (c + 10).min(line_src.len());
                d = d.label(Label::new(l, c.saturating_sub(1), end_col, "tutaj jest problem"));
            }

            d.print();
        }

        CompileError::Type { errors } => {
            for raw in errors.lines() {
                if raw.trim().is_empty() { continue; }
                let (line, col, msg) = extract_location(raw);

                let mut d = Diagnostic::error(friendly_type_msg(raw))
                .file(file)
                .source(source)
                .explain(raw)
                .suggest(type_suggestion(raw));

                if let (Some(l), Some(c)) = (line, col) {
                    d = d.label(Label::new(l, c.saturating_sub(1), c + 8, "niezgodny typ"));
                }

                d.print();
            }
        }

        CompileError::Codegen(e) => {
            Diagnostic::error("Błąd wewnętrzny generatora kodu")
            .file(file)
            .explain(&e.to_string())
            .note("To może być bug w kompilatorze H# - zgłoś na GitHubie")
            .print();
        }

        CompileError::Io(e) => {
            Diagnostic::error("Nie można odczytać pliku")
            .file(file)
            .explain(&e.to_string())
            .suggest("Sprawdź czy plik istnieje i masz do niego dostęp")
            .print();
        }

        CompileError::Link(msg) => {
            Diagnostic::error("Błąd linkowania")
            .file(file)
            .explain(msg)
            .suggest("Upewnij się że gcc jest zainstalowany: sudo apt install gcc")
            .print();
        }
    }
}

/// Błąd runtime interpretera (.hl) - tryb skryptowy, bardziej przyjazny
pub fn print_script_error(err: &str, file: &str, source: &str, line_hint: Option<usize>) {
    let (line, col, clean) = extract_location(err);
    let actual_line = line.or(line_hint);

    let mut d = Diagnostic::error(friendly_runtime_msg(err))
    .file(file)
    .source(source)
    .script()
    .explain(err)
    .suggest(runtime_suggestion(err));

    if let Some(l) = actual_line {
        let src_lines: Vec<&str> = source.lines().collect();
        let line_src = src_lines.get(l.saturating_sub(1)).copied().unwrap_or("");
        let c = col.unwrap_or(0);
        let end_col = (c + 12).min(line_src.len().max(c + 1));
        d = d.label(Label::new(l, c, end_col, "tu wywaliło"));
    }

    d.print();
}

/// Błąd sekcji skryptowej
pub fn print_scripting_error(err: &str, file: &str, source: &str) {
    let (line, _, _) = extract_location(err);

    let mut d = Diagnostic::error(friendly_script_section_msg(err))
    .file(file)
    .source(source)
    .script()
    .explain(err)
    .suggest(script_section_suggestion(err));

    if let Some(l) = line {
        let src_lines: Vec<&str> = source.lines().collect();
        let line_src = src_lines.get(l.saturating_sub(1)).copied().unwrap_or("");
        d = d.label(Label::new(l, 0, line_src.len().max(1), "ta linia ma problem"));
    }

    d.print();
}

// ─── Pomocnicze - wyciąganie lokalizacji z wiadomości błędu ──────────────────

/// Próbuje wyciągnąć (linia, kolumna, czysta_wiadomość) z surowego stringa błędu.
/// Obsługuje formaty: "linii 12:5", "line 12", "at line 12, column 5" itp.
fn extract_location(msg: &str) -> (Option<usize>, Option<usize>, String) {
    // Format naszego parsera: "Błąd składni w linii L:C"
    if let Some(rest) = msg.find("linii ").map(|i| &msg[i + 6..]) {
        let mut parts = rest.splitn(2, ':');
        let line = parts.next().and_then(|s| s.trim().parse::<usize>().ok());
        let col  = parts.next().and_then(|s| s.trim().split_whitespace().next()
        .and_then(|n| n.parse::<usize>().ok()));
        let clean = msg.to_string();
        return (line, col, clean);
    }

    // Format: "line N column M" lub "L:C"
    let re_lc = |s: &str| -> Option<(usize, usize)> {
        let mut nums = s.split(|c: char| !c.is_ascii_digit())
        .filter(|s| !s.is_empty())
        .filter_map(|n| n.parse::<usize>().ok());
        let l = nums.next()?;
        let c = nums.next().unwrap_or(0);
        Some((l, c))
    };

    if let Some((l, c)) = re_lc(msg) {
        if l > 0 && l < 100_000 {
            return (Some(l), Some(c), msg.to_string());
        }
    }

    (None, None, msg.to_string())
}

// ─── Przyjazne wiadomości ─────────────────────────────────────────────────────

fn friendly_parse_msg(msg: &str) -> String {
    if msg.contains("Oczekiwano") || msg.contains("expected") {
        "Coś nie zgadza się w składni — spodziewałem się czegoś innego".to_string()
    } else if msg.contains(']') || msg.contains('[') {
        "Brakuje nawiasu kwadratowego — bloki H# otwieramy [ i zamykamy ]".to_string()
    } else if msg.contains("EOF") || msg.contains("koniec") {
        "Plik urwał się w połowie — prawdopodobnie brakuje zamykającego ]".to_string()
    } else {
        "Nie rozumiem tej linii — sprawdź składnię H#".to_string()
    }
}

fn friendly_type_msg(msg: &str) -> String {
    if msg.contains("Int") && msg.contains("Str") {
        "Próbujesz połączyć liczbę z tekstem — to wymaga jawnej konwersji".to_string()
    } else if msg.contains("niezgodność") || msg.contains("TypeMismatch") || msg.contains("mismatch") {
        "Typy nie pasują do siebie — H# pilnuje żebyś mieszał gruszek z jabłkami".to_string()
    } else if msg.contains("Niezdefiniowana zmienna") || msg.contains("UndefinedVar") {
        "Ta zmienna nie istnieje w tym miejscu — może literówka?".to_string()
    } else if msg.contains("Niezdefiniowana funkcja") {
        "Nie znam tej funkcji — może zapomniano ją zdefiniować albo zaimportować?".to_string()
    } else if msg.contains("ArgCount") || msg.contains("argumentów") {
        "Zła liczba argumentów — funkcja oczekuje innej liczby parametrów".to_string()
    } else {
        "Problem z typami — H# dba o bezpieczeństwo danych".to_string()
    }
}

fn friendly_runtime_msg(msg: &str) -> String {
    if msg.contains("DivisionByZero") || msg.contains("zero") {
        "Dzielenie przez zero — to matematyczny błąd, H# nie może kontynuować".to_string()
    } else if msg.contains("IndexOutOfBounds") || msg.contains("poza zakresem") {
        "Indeks poza listą — próbujesz sięgnąć po element który nie istnieje".to_string()
    } else if msg.contains("UndefinedVar") || msg.contains("Niezdefiniowana zmienna") {
        "Ta zmienna nie istnieje — może literówka lub zapomniałeś ją zadeklarować?".to_string()
    } else if msg.contains("TypeError") || msg.contains("Błąd typów") {
        "Zły typ danych — H# nie może wykonać tej operacji na tym typie wartości".to_string()
    } else if msg.contains("Exception") || msg.contains("panic") {
        "Wyjątek zatrzymał skrypt — nieoczekiwany błąd w trakcie działania".to_string()
    } else {
        "Coś poszło nie tak podczas działania skryptu".to_string()
    }
}

fn friendly_script_section_msg(msg: &str) -> String {
    if msg.contains("Niezdefiniowana zmienna") || msg.contains("$") {
        "Ta zmienna skryptowa nie istnieje — użyj $nazwa = \"wartość\" żeby ją zdefiniować".to_string()
    } else if msg.contains("Błąd komendy") || msg.contains("CommandFailed") {
        "Komenda nie zadziałała — sprawdź czy jest zainstalowana i dobrze napisana".to_string()
    } else if msg.contains("Zależność") || msg.contains("DepFailed") {
        "Nie można zainstalować zależności — sprawdź połączenie z internetem i uprawnienia".to_string()
    } else if msg.contains("ParseError") || msg.contains("parsowania") {
        "Nie rozumiem tej linii skryptu — sprawdź składnię sekcji ---".to_string()
    } else {
        "Problem w sekcji skryptowej".to_string()
    }
}

// ─── Sugestie naprawy ─────────────────────────────────────────────────────────

fn parse_suggestion(msg: &str) -> String {
    if msg.contains(']') || msg.contains('[') {
        "Sprawdź czy każdy [ ma swój ] — bloki H# muszą być zamknięte".to_string()
    } else if msg.contains("fn") {
        "Funkcje definiujemy: fn nazwa(param: Typ) -> Typ [ ciało ]".to_string()
    } else if msg.contains("Claas") || msg.contains("class") {
        "Klasy definiujemy: Claas Nazwa [ pola i metody ]".to_string()
    } else {
        "Sprawdź dokumentację składni H# w README.md".to_string()
    }
}

fn type_suggestion(msg: &str) -> String {
    if msg.contains("Int") && msg.contains("Str") {
        "Zamień liczbę na tekst: wartość as Str — np. `liczba as Str`".to_string()
    } else if msg.contains("Float") && msg.contains("Int") {
        "Możesz skonwertować: wartość as Int lub wartość as Float".to_string()
    } else if msg.contains("Niezdefiniowana zmienna") {
        "Zadeklaruj zmienną przed użyciem: let nazwa: Typ = wartość".to_string()
    } else if msg.contains("ArgCount") {
        "Sprawdź sygnaturę funkcji — podaj dokładnie tyle argumentów ile wymaga".to_string()
    } else {
        "Sprawdź typy zmiennych i upewnij się że operacja jest dozwolona dla tych typów".to_string()
    }
}

fn runtime_suggestion(msg: &str) -> String {
    if msg.contains("zero") {
        "Sprawdź czy dzielnik nie jest zerem przed dzieleniem: if dzielnik != 0 [ ... ]".to_string()
    } else if msg.contains("poza") || msg.contains("IndexOut") {
        "Sprawdź długość listy przed dostępem: if i < lista.len() [ ... ]".to_string()
    } else if msg.contains("zmienna") || msg.contains("UndefinedVar") {
        "Zadeklaruj zmienną: let $nazwa = \"wartość\" (w skrypcie) lub let nazwa: Typ = wartość".to_string()
    } else if msg.contains("TypeError") {
        "Użyj `typeof(wartość)` żeby sprawdzić aktualny typ zmiennej".to_string()
    } else {
        "Użyj `h# check plik.hl` żeby sprawdzić składnię przed uruchomieniem".to_string()
    }
}

fn script_section_suggestion(msg: &str) -> String {
    if msg.contains("$") {
        "Zdefiniuj zmienną: $nazwa = \"wartość\" (bez let w sekcji skryptowej)".to_string()
    } else if msg.contains("Zależność") || msg.contains("dep") {
        "Sprawdź pisownię pakietu i połączenie z internetem, lub zainstaluj ręcznie: sudo apt install <pakiet>".to_string()
    } else if msg.contains("komenda") || msg.contains("CommandFailed") {
        "Sprawdź czy komenda jest dostępna: which <komenda> — dodaj // <pakiet> jeśli trzeba".to_string()
    } else {
        "Składnia sekcji skryptowej: > komenda, // dep, $var = val, ;; wypisz, ? warunek [".to_string()
    }
}
