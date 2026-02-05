use pyo3::prelude::*;
use pyo3::types::PyModule;
use std::fs;

fn main() -> PyResult<()> {
    Python::with_gil(|py| {
        let code = fs::read_to_string("./main.py").expect("Failed to read main.py");
        let module = PyModule::from_code(py, &code, "main.py", "main")?;
        let func = module.getattr("main")?;
        func.call0()?;
        Ok(())
    })
}
