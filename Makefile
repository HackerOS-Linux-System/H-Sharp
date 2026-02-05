# Wykrywanie systemu operacyjnego
ifeq ($(OS),Windows_NT)
    RM = del /Q
    MKDIR = mkdir
    # Na Windowsie ścieżka domowa to USERPROFILE
    DEST_DIR = $(USERPROFILE)\.hackeros\h-sharp
    BIN_DIR = C:\Windows\System32
    EXT = .exe
else
    RM = rm -f
    MKDIR = mkdir -p
    DEST_DIR = $(HOME)/.hackeros/h-sharp
    BIN_DIR = /usr/bin
    EXT =
endif

.PHONY: all hst hs-errors clean

all: hst hs-errors

# Obsługa projektu Python + Rust (hst)
hst:
	cd source-code/hst && \
	python -m venv venv && \
	./venv/bin/pip install lark && \
	cargo build --release
	$(MKDIR) $(DEST_DIR)
	cp source-code/hst/target/release/hst$(EXT) $(DEST_DIR)/

# Obsługa projektu Rust (hs-errors)
hs-errors:
	cd source-code/hs-errors && \
	cargo build --release
	$(MKDIR) $(DEST_DIR)
	cp source-code/hs-errors/target/release/hs-errors$(EXT) $(DEST_DIR)/

clean:
	@echo "Czyszczenie plików binarnych..."
	# Tutaj możesz dodać komendy usuwające targety
