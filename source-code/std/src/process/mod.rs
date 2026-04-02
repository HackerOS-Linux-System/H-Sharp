pub use std::process::{exit, Command};
pub fn run(cmd: &str, args: &[&str]) -> Result<String, std::io::Error> {
    let out = Command::new(cmd).args(args).output()?;
    Ok(String::from_utf8_lossy(&out.stdout).to_string())
}
