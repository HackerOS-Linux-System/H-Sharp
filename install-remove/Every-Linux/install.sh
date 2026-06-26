#!/bin/bash

# Sprawdzenie, czy skrypt jest uruchomiony jako root
if [ "$EUID" -ne 0 ]; then
  echo "Błąd: Uruchom ten skrypt za pomocą sudo!"
  exit 1
fi

echo "Rozpoczynam pobieranie składników języka H#..."

# 1. Pobieranie pliku 'bytes' do /usr/bin/bytes
echo "Pobieranie: bytes -> /usr/bin/bytes"
curl -L "https://github.com/HackerOS-Linux-System/H-Sharp/releases/download/v0.7/bytes" -o /usr/bin/bytes

# 2. Pobieranie binarki 'hsharp' i zapisanie jej jako /usr/bin/h#
echo "Pobieranie: hsharp -> /usr/bin/h#"
curl -L "https://github.com/HackerOS-Linux-System/H-Sharp/releases/download/v0.7/hsharp" -o "/usr/bin/h#"

# 3. Nadanie uprawnień wykonywalności dla obu plików
echo "Nadawanie uprawnień wykonywalności..."
chmod +x /usr/bin/bytes
chmod +x "/usr/bin/h#"

echo "Gotowe! Narzędzia H# zostały zainstalowane w /usr/bin."
