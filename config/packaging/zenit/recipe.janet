(def stage (os/getenv "ZPM_PACKAGE_STAGE_DIR"))

(defn fail [msg]
  (eprint "recipe.janet: " msg)
  (os/exit 1))

(defn run [cmd]
  # `os/shell` zwraca kod wyjścia polecenia (jak C-owe system()) --
  # zero == sukces.
  (def code (os/shell cmd))
  (unless (zero? code)
    (fail (string "'" cmd "' zakończone kodem " code))))

(defn ensure-dir [path]
  # `os/mkdir` w Janet nie jest rekurencyjne i zgłasza błąd, jeśli katalog
  # już istnieje -- oba przypadki nieszkodliwe, więc łykamy błąd.
  (try (os/mkdir path) ([_] nil)))

(defn ensure-dir-p [path]
  # Rekurencyjny wariant `ensure-dir` -- buduje drzewo katalog po
  # katalogu (potrzebne dla usr/share/licenses/hsharp).
  (var acc "")
  (each part (string/split "/" path)
    (when (> (length part) 0)
      (set acc (string acc "/" part))
      (ensure-dir acc))))

# config/packaging/zpk/recipe.janet leży trzy poziomy pod korzeniem repo
# (config/packaging/zpk -> config/packaging -> config -> <root>) --
# zpk zawsze ustawia cwd recipe na katalog z zpk.build, więc korzeń repo
# liczymy względem (os/cwd), niezależnie skąd faktycznie wywołano `zpk
# build`.
(def repo-root (string (os/cwd) "/../../.."))
(def target-dir (string repo-root "/target/release"))

(def prebuilt (os/getenv "ZPK_PACKAGING_PREBUILT_BIN"))

(def bin-path
  (if (and prebuilt (> (length prebuilt) 0))
    # CI/operator już zbudował `hsharp` wcześniej w tym samym biegu
    # (np. osobny krok `cargo build --release -p hsharp-cli`) -- nie
    # buduj drugi raz, użyj gotowej ścieżki.
    prebuilt
    (do
      (run (string "command -v cargo >/dev/null 2>&1 || "
                   "{ echo \"recipe.janet: brak 'cargo' w PATH -- zainstaluj Rust (rustup)\" >&2; exit 1; }"))
      # LLVM 21 wymagane przez source-code/compiler (backend LLVM) --
      # patrz build.hl i .github/workflows/build.yml. Nie nadpisujemy
      # zmiennej, jeśli operator już ją ustawił (np. Fedora/openSUSE,
      # gdzie llvm-config-21 jest wykrywane automatycznie i nadpisanie
      # mogłoby wskazać na złą ścieżkę).
      (unless (os/getenv "LLVM_SYS_211_PREFIX")
        (os/setenv "LLVM_SYS_211_PREFIX" "/usr/lib/llvm-21"))
      (run (string "cd " repo-root " && cargo build --release --locked -p hsharp-cli"))
      (string target-dir "/hsharp"))))

(unless (os/stat bin-path :mode)
  (fail (string "nie znaleziono zbudowanej binarki: " bin-path)))

(def bin-dir (string stage "/usr/bin"))
(ensure-dir stage)
(ensure-dir (string stage "/usr"))
(ensure-dir bin-dir)

(def dest (string bin-dir "/hsharp"))
(spit dest (slurp bin-path))
(run (string "chmod +x " dest))

# `h#` to symlink do `hsharp`, nie kopia -- ta sama konwencja co w
# config/packaging/debian/build.sh i config/packaging/arch/PKGBUILD.
(run (string "ln -sf hsharp " bin-dir "/h#"))

# Licencja -- ta sama konwencja co PKGBUILD (usr/share/licenses/<pkg>/LICENSE).
(def license-src (string repo-root "/LICENSE"))
(when (os/stat license-src :mode)
  (def license-dir (string stage "/usr/share/licenses/hsharp"))
  (ensure-dir-p license-dir)
  (spit (string license-dir "/LICENSE") (slurp license-src)))
