#!/bin/bash

# Sprawdzenie, czy skrypt jest uruchomiony jako root
if [ "$EUID" -ne 0 ]; then
  echo "Błąd: Uruchom ten skrypt za pomocą sudo!"
  exit 1
fi

echo "Rozpoczynam usuwanie składników języka H# z /usr/bin..."

# 1. Usuwanie pliku /usr/bin/bytes
if [ -f /usr/bin/bytes ]; then
  rm /usr/bin/bytes
  echo "Usunięto: /usr/bin/bytes"
else
  echo "Plik /usr/bin/bytes nie istniał."
fi

# 2. Usuwanie pliku /usr/bin/h#
if [ -f "/usr/bin/h#" ]; then
  rm "/usr/bin/h#"
  echo "Usunięto: /usr/bin/h#"
else
  echo "Plik /usr/bin/h# nie istniał."
fi

echo "Proces usuwania zakończony."
