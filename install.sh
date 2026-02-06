# 1. Tworzenie katalogu (użycie zmiennej $USER)
mkdir -p /home/$USER/.hackeros/h-sharp

# 2. Pobieranie pliku do /tmp
wget https://github.com/HackerOS-Linux-System/H-Sharp/releases/download/v0.2.0/bin.zip -P /tmp

# 3. Rozpakowanie zawartości do tymczasowego folderu
unzip /tmp/bin.zip -d /tmp/hsharp_temp

# 4. Nadanie uprawnień wykonywania
chmod a+x /tmp/hsharp_temp/*

# 5. Przenoszenie binarek (użycie sudo dla /usr/bin/)
sudo mv /tmp/hsharp_temp/virus-go /usr/bin/
sudo mv /tmp/hsharp_temp/virus /usr/bin/
mv /tmp/hsharp_temp/hst /home/$USER/.hackeros/h-sharp/
mv /tmp/hsharp_temp/hs-errors /home/$USER/.hackeros/h-sharp/

# 6. Porządkowanie katalogu /tmp
rm -rf /tmp/hsharp_temp /tmp/bin.zip
