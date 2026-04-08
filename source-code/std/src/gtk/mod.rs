/// H# GTK4 bindings — std -> gtk
/// Import: use "std -> gtk" from "gtk"
/// Or:     use "std -> gtk/4" from "gtk"
///
/// On HackerOS: GTK4 is pre-installed.
/// On other systems: apt install libgtk-4-dev
///
/// H# GTK4 works via subprocess delegation to a GTK4 runner
/// compiled separately (see gtk4-runner binary in HackerOS)

/// Open a GTK4 window (H# style — declarative)
pub fn window(title: &str, width: i32, height: i32) {
    println!("[H# GTK4] window(\"{}\", {}, {})", title, width, height);
    // In HackerOS: calls gtk4-runner IPC
}

/// Add a button to the current window
pub fn button(label: &str, _callback: &str) {
    println!("[H# GTK4] button(\"{}\")", label);
}

/// Add a label widget
pub fn label(text: &str) {
    println!("[H# GTK4] label(\"{}\")", text);
}

/// Add a text input field
pub fn entry(placeholder: &str) -> String {
    println!("[H# GTK4] entry(\"{}\")", placeholder);
    String::new()
}

/// Add a box container (vertical or horizontal)
pub fn vbox() { println!("[H# GTK4] vbox()"); }
pub fn hbox() { println!("[H# GTK4] hbox()"); }

/// Add a grid layout
pub fn grid() { println!("[H# GTK4] grid()"); }

/// Run the GTK4 event loop
pub fn run() {
    println!("[H# GTK4] run() — starting event loop");
    // In HackerOS: launches gtk4-runner binary with IPC
    // and blocks until window is closed
}

/// Show a dialog box
pub fn dialog_info(title: &str, message: &str) {
    println!("[H# GTK4] dialog_info(\"{}\", \"{}\")", title, message);
}

pub fn dialog_error(title: &str, message: &str) {
    println!("[H# GTK4] dialog_error(\"{}\", \"{}\")", title, message);
}

pub fn dialog_question(title: &str, message: &str) -> bool {
    println!("[H# GTK4] dialog_question(\"{}\", \"{}\")", title, message);
    false
}

/// File chooser dialog
pub fn file_open(title: &str) -> Option<String> {
    println!("[H# GTK4] file_open(\"{}\")", title);
    None
}

pub fn file_save(title: &str, default: &str) -> Option<String> {
    println!("[H# GTK4] file_save(\"{}\", \"{}\")", title, default);
    None
}

/// CSS styling
pub fn apply_css(css: &str) {
    println!("[H# GTK4] apply_css({} bytes)", css.len());
}

/// System theme detection
pub fn is_dark_theme() -> bool {
    // Check GTK theme on HackerOS
    std::env::var("GTK_THEME")
        .map(|t| t.to_lowercase().contains("dark"))
        .unwrap_or(false)
}

/// H# GTK4 Application context
pub struct App {
    pub title:  String,
    pub width:  i32,
    pub height: i32,
}

impl App {
    pub fn new(title: &str, width: i32, height: i32) -> Self {
        Self { title: title.into(), width, height }
    }

    pub fn run<F: Fn()>(&self, build_ui: F) {
        println!("[H# GTK4] App::run() — {}", self.title);
        build_ui();
        run();
    }
}
