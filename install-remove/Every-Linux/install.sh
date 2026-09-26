#!/bin/sh

# Pobranie głównego narzędzia H#
sudo curl -L https://github.com/HackerOS-Linux-System/H-Sharp/releases/download/v0.9/hsharp -o /usr/bin/h#
sudo chmod a+x /usr/bin/h#

# Utworzenie katalogu dla bibliotek standardowych
sudo mkdir -p /usr/lib/HackerOS
sudo mkdir -p /usr/lib/HackerOS/H#

# Pobranie i wypakowanie katalogu std z repozytorium
sudo curl -L https://github.com/HackerOS-Linux-System/H-Sharp/archive/refs/heads/main.tar.gz | tar -xz --strip-components=1 -C /usr/lib/HackerOS/H# H-Sharp-main/std
