#!/usr/bin/env bash

OUTPUT_FILE="ir_output.txt"
> "$OUTPUT_FILE"

echo "=== Kompilacja: bytes_final ===" >> "$OUTPUT_FILE"
./target/release/hsharp compile bytes-and-hacker/bytes_final/src/main.h# --emit-ir >> "$OUTPUT_FILE" 2>&1

echo -e "\n\n=== Kompilacja: hacker_hsharp ===" >> "$OUTPUT_FILE"
./target/release/hsharp compile bytes-and-hacker/hacker_hsharp/src/main.h# --emit-ir >> "$OUTPUT_FILE" 2>&1

echo "Gotowe! Wyniki kompilacji zostały zapisane w pliku $OUTPUT_FILE"
