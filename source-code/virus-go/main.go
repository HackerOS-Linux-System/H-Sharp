package main

import (
	"flag"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
)

func main() {
	outputFlag := flag.String("o", "", "Output binary file name (defaults to input base name without extension)")
	flag.Parse()
	args := flag.Args()
	if len(args) < 1 {
		fmt.Println("Usage: virus <input_file> [-o output_binary]")
		os.Exit(1)
	}
	input := args[0]
	ext := strings.ToLower(filepath.Ext(input))
	var inputForHsc string
	tempJson := "/tmp/hsharp_program.json"
	tempO := "/tmp/hsharp_output.o"
	home := os.Getenv("HOME")
	if home == "" {
		fmt.Println("Error: HOME environment variable not set")
		os.Exit(1)
	}
	hsharpDir := filepath.Join(home, ".hackeros/h-sharp")
	hsfPath := filepath.Join(hsharpDir, "hsf.py")
	hscPath := filepath.Join(hsharpDir, "hsc")
	// Determine output file name
	outputFile := *outputFlag
	if outputFile == "" {
		outputFile = strings.TrimSuffix(filepath.Base(input), ext)
	}
	// Handle .hla files: frontend (hsf) -> json
	if ext == ".hla" {
		// Call python3 hsf.py input -o tempJson
		cmd := exec.Command("python3", hsfPath, input, "-o", tempJson)
		cmd.Stdout = os.Stdout
		cmd.Stderr = os.Stderr
		if err := cmd.Run(); err != nil {
			fmt.Printf("Error running hsf: %v\n", err)
			os.Exit(1)
		}
		inputForHsc = tempJson
	} else if ext == ".hcs" || ext == ".json" {
		// Assume .hcs or .json is the IR, directly use for hsc
		inputForHsc = input
	} else {
		fmt.Println("Error: Unsupported file extension. Supported: .hla, .hcs, .json")
		os.Exit(1)
	}
	// Call hsc inputForHsc tempO
	cmd := exec.Command(hscPath, inputForHsc, tempO)
	cmd.Stdout = os.Stdout
	cmd.Stderr = os.Stderr
	if err := cmd.Run(); err != nil {
		fmt.Printf("Error running hsc: %v\n", err)
		os.Exit(1)
	}
	// Link with gcc to produce executable
	cmd = exec.Command("gcc", tempO, "-o", outputFile)
	cmd.Stdout = os.Stdout
	cmd.Stderr = os.Stderr
	if err := cmd.Run(); err != nil {
		fmt.Printf("Error linking with gcc: %v\n", err)
		os.Exit(1)
	}
	fmt.Printf("Compilation successful. Binary written to %s\n", outputFile)
}
