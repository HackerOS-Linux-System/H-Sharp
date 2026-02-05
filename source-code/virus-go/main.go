package main

import (
	"bufio"
	"fmt"
	"io"
	"net/http"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strings"
	"time"
)

// --- AESTHETICS ---
const (
	ColorReset  = "\033[0m"
	ColorRed    = "\033[31m"
	ColorGreen  = "\033[32m"
	ColorYellow = "\033[33m"
	ColorBlue   = "\033[34m"
	ColorPurple = "\033[35m"
	ColorCyan   = "\033[36m"
	ColorWhite  = "\033[37m"
	ColorBold   = "\033[1m"
)

func logInfo(msg string)    { fmt.Printf("%s[INFO]%s  %s\n", ColorBlue, ColorReset, msg) }
func logSuccess(msg string) { fmt.Printf("%s[OKAY]%s  %s\n", ColorGreen, ColorReset, msg) }
func logWarn(msg string)    { fmt.Printf("%s[WARN]%s  %s\n", ColorYellow, ColorReset, msg) }
func logError(msg string)   { fmt.Printf("%s[ERR!]%s  %s\n", ColorRed, ColorReset, msg) }
func logStep(step string)   { fmt.Printf("%s==>%s %s%s%s\n", ColorPurple, ColorReset, ColorBold, step, ColorReset) }

// --- CONFIG ---
const (
	CACHE_DIR = ".cache"
	BUILD_DIR = "build"

	// RAW GitHub URLs for repository indexes
	BYTES_REPO_URL = "https://raw.githubusercontent.com/Bytes-Repository/bytes.io/main/repository/bytes.io"
	VIRUS_REPO_URL = "https://raw.githubusercontent.com/Bytes-Repository/virus.io/main/repo/virus.io"
)

func main() {
	if len(os.Args) < 2 {
		printHelp()
		os.Exit(1)
	}

	command := os.Args[1]

	switch command {
		case "build":
			if len(os.Args) < 3 {
				logError("Usage: virus build <file.hcs>")
				return
			}
			srcFile := os.Args[2]
			startBuildPipeline(srcFile)

		case "clean":
			cleanBuild()

		default:
			logError(fmt.Sprintf("Unknown command: %s", command))
			printHelp()
	}
}

func printHelp() {
	fmt.Println(ColorCyan + "Virus - HackerOS Build System (v2.1)" + ColorReset)
	fmt.Println("Usage:")
	fmt.Println("  virus build <file.hcs>   Compile H# project (Auto-resolve deps & runtime)")
	fmt.Println("  virus clean              Remove build artifacts")
}

func cleanBuild() {
	logStep("Cleaning build artifacts...")
	os.RemoveAll(CACHE_DIR)
	os.RemoveAll(BUILD_DIR)
	logSuccess("Clean complete.")
}

// ==========================================
// BUILD PIPELINE
// ==========================================
func startBuildPipeline(srcFile string) {
	startTime := time.Now()
	projectName := strings.TrimSuffix(filepath.Base(srcFile), filepath.Ext(srcFile))

	// 1. ENVIRONMENT SETUP
	logStep(fmt.Sprintf("Compiling %s (H# -> Binary)...", projectName))

	wd, _ := os.Getwd()
	cachePath := filepath.Join(wd, CACHE_DIR)
	buildPath := filepath.Join(wd, BUILD_DIR)

	dirs := []string{
		filepath.Join(cachePath, "src"),
		filepath.Join(cachePath, "libs"),
		filepath.Join(cachePath, "rust_build", "src"),
		buildPath,
	}

	for _, d := range dirs {
		os.MkdirAll(d, 0755)
	}

	// 2. SETUP VIRTUAL ENVIRONMENT & RUNTIME
	// We create a venv in .cache/venv and install deps there.
	// The generated python code will modify sys.path to point to this venv.
	logInfo("Checking Python Virtual Environment...")
	if err := ensureVenv(cachePath); err != nil {
		logError("Failed to create/verify venv.")
		os.Exit(1)
	}

	logInfo("Installing Runtime (numpy, polars, numba) in venv...")
	if err := installPythonRuntimeDeps(cachePath); err != nil {
		logError("Failed to install Python dependencies.")
		logError(err.Error())
		os.Exit(1)
	}

	// 3. TRANSPILATION (H# -> Python)
	logInfo("Transpiling H# source...")
	home, _ := os.UserHomeDir()
	hstPath := filepath.Join(home, ".hackeros", "h-sharp", "hst")

	if _, err := os.Stat(hstPath); os.IsNotExist(err) {
		if _, err := os.Stat("hsf/main.py"); err == nil {
			hstPath = "hsf/main.py"
		} else {
			hstPath = "main.py"
		}
	}

	cmd := exec.Command("python3", hstPath, srcFile)
	pythonCode, err := cmd.CombinedOutput()
	if err != nil {
		logError("Transpilation Failed:")
		fmt.Println(string(pythonCode))
		os.Exit(1)
	}

	pythonOutPath := filepath.Join(cachePath, "src", "app.py")
	os.WriteFile(pythonOutPath, pythonCode, 0644)
	logSuccess("Generated intermediate Python code.")

	// 4. DEPENDENCY RESOLUTION
	logInfo("Resolving dependencies (Bytes & Virus)...")
	resolveDependencies(srcFile, cachePath)

	// 5. NATIVE PACKAGING (Rust + PyO3)
	logInfo("Generating Rust + PyO3 host...")
	generateRustProject(cachePath, projectName, pythonCode)

	// 6. COMPILATION
	logInfo("Compiling native binary (cargo)...")
	rustProjectDir := filepath.Join(cachePath, "rust_build")

	buildCmd := exec.Command("cargo", "build", "--release")
	buildCmd.Dir = rustProjectDir

	if out, err := buildCmd.CombinedOutput(); err != nil {
		logError("Rust Compilation Failed.")
		fmt.Println(string(out))
		os.Exit(1)
	}

	// 7. FINALIZE
	binaryName := "hsharp_app"
	if os.PathSeparator == '\\' {
		binaryName += ".exe"
	}

	targetBin := filepath.Join(rustProjectDir, "target", "release", binaryName)
	finalBin := filepath.Join(buildPath, projectName)

	input, err := os.ReadFile(targetBin)
	if err != nil {
		logError("Could not find compiled binary.")
		return
	}
	os.WriteFile(finalBin, input, 0755)
	os.Chmod(finalBin, 0755) // Ensure executable

	elapsed := time.Since(startTime)
	logStep("Build Finished Successfully!")
	fmt.Printf("   %sBinary:%s %s\n", ColorBold, ColorReset, finalBin)
	fmt.Printf("   %sTime:%s   %s\n", ColorBold, ColorReset, elapsed)
}

// ==========================================
// PYTHON VENV & RUNTIME MANAGER
// ==========================================
func ensureVenv(cachePath string) error {
	venvPath := filepath.Join(cachePath, "venv")

	// Check if bin/pip exists
	pipPath := filepath.Join(venvPath, "bin", "pip")
	if _, err := os.Stat(pipPath); err == nil {
		return nil // Venv exists
	}

	logWarn("Creating new virtual environment...")
	cmd := exec.Command("python3", "-m", "venv", venvPath)
	return cmd.Run()
}

func installPythonRuntimeDeps(cachePath string) error {
	// Uses the pip inside the venv to install deps
	venvPath := filepath.Join(cachePath, "venv")
	pipPath := filepath.Join(venvPath, "bin", "pip")

	pkgs := []string{"numpy", "polars", "numba"}

	// Fast check: look for folders in lib/pythonX.Y/site-packages is hard to do portably in Go
	// without knowing python version. We'll just run pip install.
	// Pip is fast if packages are already there.

	args := append([]string{"install", "--disable-pip-version-check"}, pkgs...)
	cmd := exec.Command(pipPath, args...)
	out, err := cmd.CombinedOutput()
	if err != nil {
		fmt.Println(string(out))
		return err
	}
	return nil
}

// ==========================================
// DEPENDENCY MANAGER (REAL DOWNLOADS)
// ==========================================
func resolveDependencies(srcFile string, cachePath string) {
	content, _ := os.ReadFile(srcFile)
	strContent := string(content)

	re := regexp.MustCompile(`#\s*<(virus|bytes):([a-zA-Z0-9_\-\.]+)>`)
	matches := re.FindAllStringSubmatch(strContent, -1)

	for _, match := range matches {
		repoType := match[1]
		pkgName := match[2]

		logInfo(fmt.Sprintf("Fetching %s:%s...", repoType, pkgName))

		var repoUrl string
		var targetPath string
		var isBinary bool

		if repoType == "virus" {
			repoUrl = VIRUS_REPO_URL
			targetPath = filepath.Join(cachePath, "virus", pkgName, pkgName+".so")
			isBinary = false
		} else {
			repoUrl = BYTES_REPO_URL
			targetPath = filepath.Join(cachePath, "bytes", pkgName)
			isBinary = true
		}

		// 1. Get Repo Index
		downloadUrl, err := fetchPackageUrlFromRepo(repoUrl, pkgName)
		if err != nil {
			logError(fmt.Sprintf("Failed to resolve %s: %v", pkgName, err))
			continue
		}

		// 2. Download Artifact
		os.MkdirAll(filepath.Dir(targetPath), 0755)
		err = downloadFile(downloadUrl, targetPath)
		if err != nil {
			logError(fmt.Sprintf("Download failed for %s: %v", pkgName, err))
			continue
		}

		if isBinary {
			os.Chmod(targetPath, 0755)
		}
		logSuccess(fmt.Sprintf("Installed %s", pkgName))
	}
}

// Parses the remote .io file to find the package URL
func fetchPackageUrlFromRepo(repoIndexUrl string, pkgName string) (string, error) {
	resp, err := http.Get(repoIndexUrl)
	if err != nil {
		return "", err
	}
	defer resp.Body.Close()

	if resp.StatusCode != 200 {
		return "", fmt.Errorf("repo index unreachable (HTTP %d)", resp.StatusCode)
	}

	scanner := bufio.NewScanner(resp.Body)
	for scanner.Scan() {
		line := strings.TrimSpace(scanner.Text())
		if line == "" || strings.HasPrefix(line, "#") {
			continue
		}

		parts := strings.Fields(strings.ReplaceAll(line, "=", " "))
		if len(parts) >= 1 {
			currentPkg := parts[0]
			if currentPkg == pkgName {
				if len(parts) >= 2 {
					return parts[1], nil
				}
				return "", fmt.Errorf("no URL found for package in index")
			}
		}
	}

	return "", fmt.Errorf("package not found in repository index")
}

func downloadFile(url string, dest string) error {
	resp, err := http.Get(url)
	if err != nil {
		return err
	}
	defer resp.Body.Close()

	if resp.StatusCode != 200 {
		return fmt.Errorf("HTTP %d", resp.StatusCode)
	}

	out, err := os.Create(dest)
	if err != nil {
		return err
	}
	defer out.Close()

	_, err = io.Copy(out, resp.Body)
	return err
}

// ==========================================
// RUST GENERATOR
// ==========================================
func generateRustProject(cachePath string, projectName string, pythonCode []byte) {
	rustDir := filepath.Join(cachePath, "rust_build")

	cargoToml := fmt.Sprintf(`[package]
	name = "hsharp_app"
	version = "0.1.0"
	edition = "2021"

	[dependencies]
	pyo3 = { version = "0.19.0", features = ["auto-initialize"] }

	[[bin]]
	name = "hsharp_app"
	path = "src/main.rs"
	`)
	os.WriteFile(filepath.Join(rustDir, "Cargo.toml"), []byte(cargoToml), 0644)

	safePyCode := strings.ReplaceAll(string(pythonCode), "`", "` + \"`\" + `")

	// Fixed the logic to explicitly CALL the main function
	mainRs := fmt.Sprintf(`
	use pyo3::prelude::*;
	use pyo3::types::PyModule;

	fn main() -> PyResult<()> {
	let py_app = r#"%s"#;

	Python::with_gil(|py| {
	let app = PyModule::from_code(py, py_app, "app.py", "app")?;

	// Explicitly look for 'main' function and call it
	// This solves the issue where "if __name__ == '__main__':" is not triggered
	// because from_code treats it as an import.
	if let Ok(main_fn) = app.getattr("main") {
		main_fn.call0()?;
} else {
	// If there is no main function, top-level code has already run via from_code
}

Ok(())
})
}
`, safePyCode)

	os.WriteFile(filepath.Join(rustDir, "src", "main.rs"), []byte(mainRs), 0644)
}
