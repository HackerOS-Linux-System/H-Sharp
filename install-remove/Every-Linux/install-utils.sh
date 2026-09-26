#!/bin/sh

# Pobieranie plików
sudo curl -L https://github.com/Bytes-Repository/bytes/releases/download/v0.9/bytes -o /usr/bin/bytes
sudo curl -L https://github.com/Bytes-Repository/vira/releases/download/v0.9/vira -o /usr/bin/vira
sudo curl -L https://github.com/Bytes-Repository/fast/releases/download/v0.9/fast -o /usr/bin/fast

# Nadanie praw do wykonania
sudo chmod a+x /usr/bin/bytes
sudo chmod a+x /usr/bin/vira 
sudo chmod a+x /usr/bin/fast
