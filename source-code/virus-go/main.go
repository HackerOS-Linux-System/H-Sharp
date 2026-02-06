package main

import (
	"bufio"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strconv"
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

	// System path for H# Core Libraries
	// In dev/local environment, you might want to mock this or use a relative path
	CORE_LIB_PATH = "/usr/lib/h-sharp/core"

	// RAW GitHub URLs for repository indexes
	BYTES_REPO_URL = "https://raw.githubusercontent.com/Bytes-Repository/bytes.io/main/repository/bytes.io"
	VIRUS_REPO_URL = "https://raw.githubusercontent.com/Bytes-Repository/virus.io/main/repo/virus.io"
)

type ProjectInfo struct {
	Name       string
	Entrypoint string
}

// Struct for JSON errors from HST (Python)
type HstError struct {
	Type     string   `json:"type"`
	Msg      string   `json:"msg"`
	Line     int      `json:"line"`
	Col      int      `json:"col"`
	Expected []string `json:"expected"`
}

func main() {
	if len(os.Args) < 2 {
		printHelp()
		os.Exit(1)
	}

	command := os.Args[1]

	switch command {
		case "build":
			handleBuildCommand()

		case "clean":
			cleanBuild()

		default:
			logError(fmt.Sprintf("Unknown command: %s", command))
			printHelp()
	}
}

func printHelp() {
	fmt.Println(ColorCyan + "Virus - HackerOS Build System (v2.2)" + ColorReset)
	fmt.Println("Usage:")
	fmt.Println("  virus build              Compile project (requires Virus.hk/hcl/toml)")
	fmt.Println("  virus build <file.hcs>   Compile single H# file")
	fmt.Println("  virus clean              Remove build artifacts (.cache, build)")
}

func cleanBuild() {
	logStep("Cleaning build artifacts...")

	dirs := []string{CACHE_DIR, BUILD_DIR}
	for _, d := range dirs {
		if _, err := os.Stat(d); !os.IsNotExist(err) {
			fmt.Printf("Removing %s...\n", d)
			os.RemoveAll(d)
		}
	}

	logSuccess("Clean complete.")
}

// ==========================================
// PROJECT DETECTION & BUILD
// ==========================================
func handleBuildCommand() {
	var srcFile string
	var projectName string

	// Check if argument provided (legacy mode) or project mode
	if len(os.Args) >= 3 {
		srcFile = os.Args[2]
		projectName = strings.TrimSuffix(filepath.Base(srcFile), filepath.Ext(srcFile))
	} else {
		// Project Mode
		config, err := detectProjectConfig()
		if err != nil {
			logError(err.Error())
			return
		}
		logInfo(fmt.Sprintf("Project detected: %s", config.Name))
		srcFile = config.Entrypoint
		projectName = config.Name
	}

	startBuildPipeline(srcFile, projectName)
}

func detectProjectConfig() (ProjectInfo, error) {
	// Priority: .hk > .hcl > .toml
	if _, err := os.Stat("Virus.hk"); err == nil {
		return parseHK("Virus.hk")
	}
	if _, err := os.Stat("Virus.hcl"); err == nil {
		return ProjectInfo{Name: "ProjectHCL", Entrypoint: "src/main.hcs"}, nil // Simplified HCL
	}
	if _, err := os.Stat("Virus.toml"); err == nil {
		return ProjectInfo{Name: "ProjectTOML", Entrypoint: "src/main.hcs"}, nil // Simplified TOML
	}

	return ProjectInfo{}, fmt.Errorf("No project file (Virus.hk, .hcl, .toml) found. Usage: virus build <file.hcs>")
}

// Parses custom .hk format
func parseHK(path string) (ProjectInfo, error) {
	file, err := os.Open(path)
	if err != nil {
		return ProjectInfo{}, err
	}
	defer file.Close()

	info := ProjectInfo{
		Name:       "UnknownApp",
		Entrypoint: "src/main.hcs", // Default convention
	}

	scanner := bufio.NewScanner(file)
	currentSection := ""

	for scanner.Scan() {
		line := strings.TrimSpace(scanner.Text())
		if line == "" || strings.HasPrefix(line, "!") {
			continue
		}

		if strings.HasPrefix(line, "[") && strings.HasSuffix(line, "]") {
			currentSection = strings.Trim(line, "[]")
			continue
		}

		if strings.HasPrefix(line, "->") {
			// Parse: -> key => value
			content := strings.TrimPrefix(line, "->")
			parts := strings.SplitN(content, "=>", 2)
			if len(parts) == 2 {
				key := strings.TrimSpace(parts[0])
				val := strings.TrimSpace(parts[1])

				if currentSection == "metadata" {
					if key == "name" {
						info.Name = val
					}
				}
				// Allow overriding entrypoint if defined in future specs
				if currentSection == "build" && key == "entrypoint" {
					info.Entrypoint = val
				}
			}
		}
	}

	// Check if source exists
	if _, err := os.Stat(info.Entrypoint); os.IsNotExist(err) {
		return info, fmt.Errorf("Entrypoint not found: %s", info.Entrypoint)
	}

	return info, nil
}

// ==========================================
// BUILD PIPELINE
// ==========================================
func startBuildPipeline(srcFile string, projectName string) {
	startTime := time.Now()

	// 1. ENVIRONMENT SETUP
	logStep(fmt.Sprintf("Compiling %s (H# -> Binary)...", projectName))

	wd, _ := os.Getwd()
	cachePath := filepath.Join(wd, CACHE_DIR)
	buildPath := filepath.Join(wd, BUILD_DIR)

	dirs := []string{
		filepath.Join(cachePath, "src"),
		filepath.Join(cachePath, "libs"),
		filepath.Join(cachePath, "core"),
		filepath.Join(cachePath, "rust_build", "src"),
		buildPath,
	}

	for _, d := range dirs {
		os.MkdirAll(d, 0755)
	}

	// 2. SETUP VIRTUAL ENVIRONMENT & RUNTIME
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
	pythonCode, err := transpileHSharp(srcFile, cachePath)
	if err != nil {
		// Error handling is inside transpileHSharp
		os.Exit(1)
	}

	pythonOutPath := filepath.Join(cachePath, "src", "app.py")
	os.WriteFile(pythonOutPath, pythonCode, 0644)
	logSuccess("Generated intermediate Python code.")

	// 4. DEPENDENCY RESOLUTION
	logInfo("Resolving dependencies (Bytes, Virus, Core, Rust)...")

	// Scan the generated Python code for markers (RUST_DEP) and raw import lines
	// Note: We use the *source H#* for imports usually, but HST now puts markers in Python too.
	// Let's scan the original file for core imports to trigger builds.
	resolveDependencies(srcFile, cachePath)
	rustDeps := extractRustDependencies(pythonCode)

	// 5. NATIVE PACKAGING (Rust + PyO3)
	logInfo("Generating Rust + PyO3 host...")
	generateRustProject(cachePath, projectName, pythonCode, rustDeps)

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
// TRANSPILER WRAPPER
// ==========================================
func transpileHSharp(srcFile string, cachePath string) ([]byte, error) {
	home, _ := os.UserHomeDir()
	hstBin := filepath.Join(home, ".hackeros", "h-sharp", "hst")
	var cmd *exec.Cmd

	if _, err := os.Stat(hstBin); err == nil {
		cmd = exec.Command(hstBin, srcFile)
	} else {
		hstScript := "hsf/main.py"
		if _, err := os.Stat(hstScript); os.IsNotExist(err) {
			hstScript = "main.py"
		}
		cmd = exec.Command("python3", hstScript, srcFile)
	}

	pythonCode, err := cmd.CombinedOutput()
	outputStr := string(pythonCode)

	if err != nil {
		// 1. JSON Error
		if strings.Contains(outputStr, "__HST_JSON_ERR__") {
			parts := strings.Split(outputStr, "__HST_JSON_ERR__")
			if len(parts) > 1 {
				jsonStr := strings.TrimSpace(parts[1])
				var hstErr HstError
				if jErr := json.Unmarshal([]byte(jsonStr), &hstErr); jErr == nil {
					finalMsg := hstErr.Msg
					if len(hstErr.Expected) > 0 {
						finalMsg += fmt.Sprintf(". Expected: %v", hstErr.Expected)
					}
					reportPrettyError(srcFile, hstErr.Line, hstErr.Col, finalMsg, outputStr)
					return nil, err
				}
			}
		}

		// 2. Fallback Error
		logError("Transpilation Failed.")
		lineRegex := regexp.MustCompile(`line\s+(\d+)`)
		colRegex := regexp.MustCompile(`column\s+(\d+)`)
		lineMatch := lineRegex.FindStringSubmatch(outputStr)
		colMatch := colRegex.FindStringSubmatch(outputStr)

		lineNum := 1
		colNum := 1
		if len(lineMatch) > 1 { lineNum, _ = strconv.Atoi(lineMatch[1]) }
		if len(colMatch) > 1 { colNum, _ = strconv.Atoi(colMatch[1]) }

		reportPrettyError(srcFile, lineNum, colNum, "Syntax Error", outputStr)
		return nil, err
	}
	return pythonCode, nil
}

// ==========================================
// DEPENDENCY MANAGER
// ==========================================
func resolveDependencies(srcFile string, cachePath string) {
	content, _ := os.ReadFile(srcFile)
	strContent := string(content)

	// Regex for standard imports: # <type:name>
	re := regexp.MustCompile(`#\s*<(virus|bytes|core):([a-zA-Z0-9_\-\.]+)>`)
	matches := re.FindAllStringSubmatch(strContent, -1)

	for _, match := range matches {
		repoType := match[1]
		pkgName := match[2]

		if repoType == "core" {
			compileCoreModule(pkgName, cachePath)
			continue
		}

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

		downloadUrl, err := fetchPackageUrlFromRepo(repoUrl, pkgName)
		if err != nil {
			logWarn(fmt.Sprintf("Failed to resolve %s: %v. Using fallback/stub.", pkgName, err))
			continue
		}

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

// Compiles a system .hcs file to a shared object (.so)
func compileCoreModule(name string, cachePath string) {
	// 1. Check if cached lib already exists
	libName := fmt.Sprintf("lib%s.so", name)
	finalLibPath := filepath.Join(cachePath, "core", libName)
	if _, err := os.Stat(finalLibPath); err == nil {
		// logInfo(fmt.Sprintf("Core library %s already built.", name))
		return
	}

	logInfo(fmt.Sprintf("Building Core Library: %s", name))

	// 2. Locate source file
	// Default system path
	sourcePath := filepath.Join(CORE_LIB_PATH, name+".hcs")

	// Dev Fallback: Check local folder "core/"
	if _, err := os.Stat(sourcePath); os.IsNotExist(err) {
		wd, _ := os.Getwd()
		localSource := filepath.Join(wd, "core", name+".hcs")
		if _, err := os.Stat(localSource); err == nil {
			sourcePath = localSource
		} else {
			logError(fmt.Sprintf("Core library not found: %s (checked %s and %s)", name, CORE_LIB_PATH, localSource))
			return
		}
	}

	// 3. Recursive Build process
	// We need a separate temp build dir for the lib
	libBuildDir := filepath.Join(cachePath, "build_core", name)
	os.MkdirAll(libBuildDir, 0755)

	// Transpile
	pyCode, err := transpileHSharp(sourcePath, cachePath)
	if err != nil {
		logError(fmt.Sprintf("Failed to transpile core lib %s", name))
		return
	}

	// Generate Rust Library Project
	rustLibDir := filepath.Join(libBuildDir, "rust")
	os.MkdirAll(filepath.Join(rustLibDir, "src"), 0755)

	// Create Cargo.toml for cdylib
	cargoToml := fmt.Sprintf(`[package]
	name = "%s"
	version = "0.1.0"
	edition = "2021"

	[lib]
	name = "%s"
	crate-type = ["cdylib"]

	[dependencies]
	pyo3 = { version = "0.19.0", features = ["extension-module"] }
	`, name, name)

	os.WriteFile(filepath.Join(rustLibDir, "Cargo.toml"), []byte(cargoToml), 0644)

	// Create lib.rs (Wrapper for Python module)
	safePyCode := strings.ReplaceAll(string(pyCode), "`", "` + \"`\" + `")
	libRs := fmt.Sprintf(`
	use pyo3::prelude::*;

	#[pymodule]
	fn %s(py: Python, m: &PyModule) -> PyResult<()> {
	let code = r#"%s"#;
	let compiled_mod = PyModule::from_code(py, code, "%s.py", "%s")?;

	// Copy attributes from compiled H# module to this extension module
	for (key, value) in compiled_mod.dict().iter() {
		m.add(&key.to_string(), value)?;
}
Ok(())
}
`, name, safePyCode, name, name)

	os.WriteFile(filepath.Join(rustLibDir, "src", "lib.rs"), []byte(libRs), 0644)

	// Compile
	cmd := exec.Command("cargo", "build", "--release")
	cmd.Dir = rustLibDir
	if out, err := cmd.CombinedOutput(); err != nil {
		logError(fmt.Sprintf("Failed to compile core lib %s: %s", name, string(out)))
		return
	}

	// Move artifact
	builtLib := filepath.Join(rustLibDir, "target", "release", libName)
	if _, err := os.Stat(builtLib); os.IsNotExist(err) {
		// On Linux/Mac it's libname.so, on Windows it's name.dll.
		// For simplicity let's check generic fallback or strict naming.
		// PyO3 usually outputs libname.so on Linux.
		logError("Compiled artifact not found.")
		return
	}

	// Copy to cache
	input, _ := os.ReadFile(builtLib)
	os.WriteFile(finalLibPath, input, 0755)
	logSuccess(fmt.Sprintf("Core Lib %s compiled & linked.", name))
}

func extractRustDependencies(pythonCode []byte) []string {
	var deps []string
	strCode := string(pythonCode)
	// Match: # H#_RUST_DEP: crate_name
	re := regexp.MustCompile(`#\s*H#_RUST_DEP:\s*([a-zA-Z0-9_\-]+)`)
	matches := re.FindAllStringSubmatch(strCode, -1)

	for _, m := range matches {
		if len(m) > 1 {
			deps = append(deps, m[1])
		}
	}
	return deps
}

func fetchPackageUrlFromRepo(repoIndexUrl string, pkgName string) (string, error) {
	resp, err := http.Get(repoIndexUrl)
	if err != nil {
		return "", err
	}
	defer resp.Body.Close()

	scanner := bufio.NewScanner(resp.Body)
	for scanner.Scan() {
		line := strings.TrimSpace(scanner.Text())
		if line == "" || strings.HasPrefix(line, "#") || strings.HasPrefix(line, "!") { continue }
		if strings.HasPrefix(line, "[") && strings.HasSuffix(line, "]") { continue }
		line = strings.TrimPrefix(line, "->")
		line = strings.TrimSpace(line)
		line = strings.ReplaceAll(line, "=>", "=")
		parts := strings.SplitN(line, "=", 2)
		if len(parts) >= 2 {
			currentPkg := strings.TrimSpace(parts[0])
			if currentPkg == pkgName {
				url := strings.TrimSpace(parts[1])
				if url != "" { return url, nil }
			}
		}
	}
	return "", fmt.Errorf("package not found in repository index")
}

func downloadFile(url string, dest string) error {
	resp, err := http.Get(url)
	if err != nil { return err }
	defer resp.Body.Close()
	if resp.StatusCode != 200 { return fmt.Errorf("HTTP %d", resp.StatusCode) }
	out, err := os.Create(dest)
	if err != nil { return err }
	defer out.Close()
	_, err = io.Copy(out, resp.Body)
	return err
}

// ==========================================
// RUST GENERATOR
// ==========================================
func generateRustProject(cachePath string, projectName string, pythonCode []byte, rustDeps []string) {
	rustDir := filepath.Join(cachePath, "rust_build")

	// Inject extra dependencies
	depString := ""
	for _, dep := range rustDeps {
		depString += fmt.Sprintf("%s = \"*\"\n", dep)
	}

	cargoToml := fmt.Sprintf(`[package]
	name = "hsharp_app"
	version = "0.1.0"
	edition = "2021"

	[dependencies]
	pyo3 = { version = "0.19.0", features = ["auto-initialize"] }
	%s

	[[bin]]
	name = "hsharp_app"
	path = "src/main.rs"
	`, depString)
	os.WriteFile(filepath.Join(rustDir, "Cargo.toml"), []byte(cargoToml), 0644)

	safePyCode := strings.ReplaceAll(string(pythonCode), "`", "` + \"`\" + `")

	mainRs := fmt.Sprintf(`
	use pyo3::prelude::*;
	use pyo3::types::PyModule;

	fn main() -> PyResult<()> {
	// Embedded H# Code (Transpiled to Python)
	let py_app = r#"%s"#;

	Python::with_gil(|py| {
	let app = PyModule::from_code(py, py_app, "app.py", "app")?;

	if let Ok(main_fn) = app.getattr("main") {
		main_fn.call0()?;
}

Ok(())
})
}
`, safePyCode)

	os.WriteFile(filepath.Join(rustDir, "src", "main.rs"), []byte(mainRs), 0644)
}

// ==========================================
// ERROR REPORTING (Rust Integration)
// ==========================================
func reportPrettyError(file string, line int, col int, msg string, fullLog string) {
	home, _ := os.UserHomeDir()
	hsErrorsBin := filepath.Join(home, ".hackeros", "h-sharp", "hs-errors")

	if _, err := os.Stat(hsErrorsBin); os.IsNotExist(err) {
		wd, _ := os.Getwd()
		localBin := filepath.Join(wd, "hs-errors", "target", "release", "hs-errors")
		if _, err := os.Stat(localBin); err == nil {
			hsErrorsBin = localBin
		} else {
			fmt.Println("\n" + ColorRed + ">>> HS-ERRORS BINARY NOT FOUND <<<" + ColorReset)
			fmt.Println(fullLog)
			return
		}
	}

	cmd := exec.Command(hsErrorsBin,
			    "--file", file,
		     "--line", strconv.Itoa(line),
			    "--col", strconv.Itoa(col),
			    "--msg", msg,
	)
	cmd.Stdout = os.Stdout
	cmd.Stderr = os.Stderr
	cmd.Run()
}

// ==========================================
// VENV UTILS
// ==========================================
func ensureVenv(cachePath string) error {
	venvPath := filepath.Join(cachePath, "venv")
	pipPath := filepath.Join(venvPath, "bin", "pip")
	if _, err := os.Stat(pipPath); err == nil { return nil }
	logWarn("Creating new virtual environment...")
	cmd := exec.Command("python3", "-m", "venv", venvPath)
	return cmd.Run()
}

func installPythonRuntimeDeps(cachePath string) error {
	venvPath := filepath.Join(cachePath, "venv")
	pipPath := filepath.Join(venvPath, "bin", "pip")
	pkgs := []string{"numpy", "polars", "numba"}
	args := append([]string{"install", "--disable-pip-version-check"}, pkgs...)
	cmd := exec.Command(pipPath, args...)
	out, err := cmd.CombinedOutput()
	if err != nil { fmt.Println(string(out)); return err }
	return nil
}
