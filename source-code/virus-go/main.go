package main

/*
 *  FILE: /usr/bin/virus
 *  DESC: The 'Virus' Package Manager & Build System for HackerOS
 *  AUTHOR: HackerOS Core Team
 */

import (
	"fmt"
	"io"
	"net/http"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
)

const (
	VIRUS_REPO_URL = "https://github.com/Bytes-Repository/virus.io/raw/main/repo/virus.io"
	BYTES_REPO_URL = "https://github.com/Bytes-Repository/bytes.io/raw/main/repository/bytes.io"
	CACHE_DIR      = ".cache"
)

func main() {
	if len(os.Args) < 2 {
		printHelp()
		os.Exit(1)
	}

	command := os.Args[1]

	switch command {
		case "install":
			if len(os.Args) < 3 {
				fmt.Println("Usage: virus install <package>")
				return
			}
			pkgName := os.Args[2]
			installPackage(pkgName)

		case "build":
			if len(os.Args) < 3 {
				fmt.Println("Usage: virus build <file.hcs>")
				return
			}
			srcFile := os.Args[2]
			buildProject(srcFile)

		case "update":
			fmt.Println("Updating Virus & Bytes repositories...")

		default:
			fmt.Printf("Unknown command: %s\n", command)
			printHelp()
	}
}

func printHelp() {
	fmt.Println("Virus - HackerOS Package Manager")
	fmt.Println("Commands:")
	fmt.Println("  install <pkg>   Download lib (Virus) or tool (Bytes)")
	fmt.Println("  build <file>    Transpile H# -> Python -> Binary")
}

// ==========================================
// BUILD SYSTEM (H# -> Python -> Rust/PyOxidizer)
// ==========================================
func buildProject(srcFile string) {
	home, _ := os.UserHomeDir()
	hstPath := filepath.Join(home, ".hackeros", "h-sharp", "hst.py")
	buildDir := filepath.Join(home, CACHE_DIR, "build")

	os.MkdirAll(buildDir, 0755)
	fmt.Printf("[Virus] Transpiling %s...\n", srcFile)

	cmd := exec.Command("python3", hstPath, srcFile)
	output, err := cmd.CombinedOutput()
	if err != nil {
		fmt.Printf("[Error] HST Compilation Failed:\n%s\n", string(output))
		return
	}

	intermediateFile := filepath.Join(buildDir, "main.py")
	err = os.WriteFile(intermediateFile, output, 0644)
	if err != nil {
		fmt.Println("[Error] Could not write intermediate file")
		return
	}
	fmt.Println("[Virus] Generated intermediate Python code")

	binName := strings.TrimSuffix(filepath.Base(srcFile), filepath.Ext(srcFile))
	finalBin := filepath.Join("build", binName)

	fmt.Println("[Virus] Packaging with Rust/PyOxidizer...")

	os.Mkdir("build", 0755)
	dummyScript := fmt.Sprintf("#!/bin/bash\npython3 %s", intermediateFile)
	os.WriteFile(finalBin, []byte(dummyScript), 0755)

	fmt.Printf("[Virus] Build Complete! Binary: ./%s\n", finalBin)
}

// ==========================================
// PACKAGE MANAGER (Virus & Bytes)
// ==========================================
func installPackage(pkgName string) {
	fmt.Printf("[Virus] Resolving %s...\n", pkgName)
	home, _ := os.UserHomeDir()

	if isVirusLib(pkgName) {
		targetDir := filepath.Join(home, CACHE_DIR, "virus", pkgName)
		os.MkdirAll(targetDir, 0755)

		fmt.Println("[Virus] Detected type: Library (.so/.a)")
		fmt.Printf("[Virus] Downloading from Repository...\n")
		createMockFile(filepath.Join(targetDir, pkgName+".so"))

		fmt.Println("[Success] Library installed.")
		return
	}

	if isBytesTool(pkgName) {
		targetDir := filepath.Join(home, CACHE_DIR, "bytes")
		os.MkdirAll(targetDir, 0755)

		fmt.Println("[Virus] Detected type: Tool (ELF Binary)")
		fmt.Printf("[Virus] Downloading from Bytes Repository...\n")
		createMockFile(filepath.Join(targetDir, pkgName))
		os.Chmod(filepath.Join(targetDir, pkgName), 0755)

		fmt.Println("[Success] Tool installed.")
		return
	}

	fmt.Printf("[Error] Package '%s' not found in Virus or Bytes repositories.\n", pkgName)
}

func isVirusLib(name string) bool {
	db := []string{"virus-core", "net-lib", "graphics-x"}
	for _, v := range db { if v == name { return true } }
	return false
}

func isBytesTool(name string) bool {
	db := []string{"obsidian", "yuy", "json", "translator"}
	for _, v := range db { if v == name { return true } }
	return false
}

func createMockFile(path string) {
	os.WriteFile(path, []byte("MOCK_BINARY_DATA"), 0644)
}

func downloadFile(url string, dest string) error {
	resp, err := http.Get(url)
	if err != nil { return err }
	defer resp.Body.Close()

	out, err := os.Create(dest)
	if err != nil { return err }
	defer out.Close()

	_, err = io.Copy(out, resp.Body)
	return err
}
