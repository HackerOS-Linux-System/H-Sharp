use std::io::BufRead;
pub fn read_line(prompt: &str) -> String {
    print!("{}", prompt);
    let _ = std::io::Write::flush(&mut std::io::stdout());
    let stdin = std::io::stdin();
    let mut line = String::new();
    stdin.lock().read_line(&mut line).ok();
    line.trim_end_matches('\n').trim_end_matches('\r').to_string()
}
