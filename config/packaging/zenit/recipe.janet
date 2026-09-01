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

(defn try-run [cmd]
  # Jak `run`, ale nie przerywa recipe przy niepowodzeniu -- zwraca
  # true/false. Do kroków, które są "najlepszym wysiłkiem".
  (zero? (os/shell cmd)))

(defn shell-out [cmd]
  # Uruchamia polecenie i zwraca [ok stdout-przycięte].
  (def proc (os/spawn ["/bin/sh" "-c" cmd] :p {:out :pipe}))
  (def out (:read (proc :out) :all))
  (def code (:wait proc))
  [(zero? code) (string/trimr (or out ""))])

(defn have? [tool]
  (zero? (os/shell (string "command -v " tool " >/dev/null 2>&1"))))

(defn root? []
  (zero? (os/shell "test \"$(id -u)\" = 0")))

(defn sudo- []
  (if (root?) "" (if (have? "sudo") "sudo " "")))

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

# ---------------------------------------------------------------------
# Auto-instalacja brakujących narzędzi -- wykrywa menedżer pakietów
# (apt/dnf/pacman/zypper/apk/brew), nie tylko apt/Debian.
# ---------------------------------------------------------------------

(defn detect-pm []
  (cond
    (have? "apt-get") :apt
    (have? "dnf") :dnf
    (have? "pacman") :pacman
    (have? "zypper") :zypper
    (have? "apk") :apk
    (have? "brew") :brew
    :none))

(defn pm-install [pkgs-by-pm]
  (def pm (detect-pm))
  (def pkgs (get pkgs-by-pm pm))
  (if (not pkgs)
    false
    (let [sudo (sudo-)]
      (case pm
        :apt (try-run (string sudo "apt-get update && " sudo "env DEBIAN_FRONTEND=noninteractive apt-get install -y " pkgs))
        :dnf (try-run (string sudo "dnf install -y " pkgs))
        :pacman (try-run (string sudo "pacman -Sy --noconfirm " pkgs))
        :zypper (try-run (string sudo "zypper --non-interactive install " pkgs))
        :apk (try-run (string sudo "apk add --no-cache " pkgs))
        :brew (try-run (string "brew install " pkgs))
        false))))

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
    # buduj drugi raz, użyj gotowej ścieżki. Pomijamy też całą poniższą
    # logikę instalowania cargo/LLVM.
    prebuilt
    (do
      # -----------------------------------------------------------
      # cargo -- jeśli brak, próbujemy najpierw pakiet dystrybucyjny,
      # a w ostateczności oficjalny instalator rustup (działa
      # identycznie na każdej dystrybucji, nie wymaga roota).
      # -----------------------------------------------------------
      (defn ensure-cargo []
        (unless (have? "cargo")
          (eprint "recipe.janet: brak 'cargo' -- próbuję zainstalować (" (detect-pm) ")...")
          (unless (pm-install {:apt "cargo" :dnf "cargo" :pacman "rust" :zypper "cargo" :apk "cargo" :brew "rust"})
            (eprint "recipe.janet: menedżer pakietów nie ma 'cargo' -- próbuję rustup (oficjalny instalator)...")
            (try-run "curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --default-toolchain stable")
            (def cargo-bin-dir (string (os/getenv "HOME") "/.cargo/bin"))
            (when (os/stat (string cargo-bin-dir "/cargo") :mode)
              (os/setenv "PATH" (string cargo-bin-dir ":" (os/getenv "PATH"))))))
        (unless (have? "cargo")
          (fail "nie udało się zapewnić 'cargo' -- zainstaluj Rust ręcznie (rustup) i uruchom ponownie")))

      (ensure-cargo)

      # -----------------------------------------------------------
      # LLVM 21 (backend kompilatora H#, patrz build.hl i
      # .github/workflows/build.yml) -- szukamy istniejącej instalacji
      # w typowych miejscach, a jeśli jej brak, instalujemy pakietem
      # dystrybucyjnym; na apt-owych systemach ze zbyt starym LLVM
      # (np. Debian stable) spadamy na oficjalny skrypt
      # bootstrapujący apt.llvm.org -- dokładnie to, co trzeba było
      # zrobić ręcznie.
      # -----------------------------------------------------------
      (defn find-llvm-prefix []
        (def env-prefix (os/getenv "LLVM_SYS_211_PREFIX"))
        (cond
          (and env-prefix (> (length env-prefix) 0) (os/stat env-prefix :mode)) env-prefix
          (os/stat "/usr/lib/llvm-21" :mode) "/usr/lib/llvm-21"
          (os/stat "/usr/lib64/llvm-21" :mode) "/usr/lib64/llvm-21"
          (os/stat "/usr/local/opt/llvm@21" :mode) "/usr/local/opt/llvm@21"
          (have? "llvm-config-21")
            (let [r (shell-out "llvm-config-21 --prefix")] (if (r 0) (r 1) nil))
          (and (have? "llvm-config")
               (let [r (shell-out "llvm-config --version")] (and (r 0) (string/has-prefix? "21." (r 1)))))
            (let [r (shell-out "llvm-config --prefix")] (if (r 0) (r 1) nil))
          nil))

      (defn ensure-llvm []
        (var prefix (find-llvm-prefix))
        (when (not prefix)
          (eprint "recipe.janet: brak LLVM 21 -- próbuję zainstalować (" (detect-pm) ")...")
          (pm-install {:apt "llvm-21-dev libpolly-21-dev" :dnf "llvm-devel" :pacman "llvm" :zypper "llvm-devel" :apk "llvm-dev" :brew "llvm@21"})
          (set prefix (find-llvm-prefix)))
        (when (and (not prefix) (have? "apt-get"))
          (eprint "recipe.janet: nadal brak LLVM 21 -- próbuję apt.llvm.org (llvm.sh)...")
          (when (try-run "curl -fsSL -o /tmp/zpk-llvm.sh https://apt.llvm.org/llvm.sh && chmod +x /tmp/zpk-llvm.sh")
            (try-run (string (sudo-) "/tmp/zpk-llvm.sh 21")))
          (set prefix (find-llvm-prefix)))
        (unless prefix
          (fail "nie udało się zapewnić LLVM 21 -- zainstaluj ręcznie (pakiet 'llvm-21-dev'/'llvm') i ustaw LLVM_SYS_211_PREFIX"))
        # Nie nadpisujemy zmiennej, jeśli operator już ją ustawił na
        # coś istniejącego (find-llvm-prefix to sprawdza jako pierwsze).
        (os/setenv "LLVM_SYS_211_PREFIX" prefix))

      (ensure-llvm)

      # -----------------------------------------------------------
      # Build. `--locked` wymaga zgodnego Cargo.lock -- jeśli go nie
      # ma (świeży checkout bez commitowanego locka) albo jest
      # niezgodny z Cargo.toml, samo `--locked` odmawia go
      # dogenerować. Generujemy/regenerujemy lockfile jawnie zamiast
      # od razu poddawać się.
      # -----------------------------------------------------------
      (def lockfile (string repo-root "/Cargo.lock"))
      (unless (os/stat lockfile :mode)
        (eprint "recipe.janet: brak Cargo.lock -- generuję (cargo generate-lockfile)...")
        (run (string "cd " repo-root " && cargo generate-lockfile")))

      (unless (try-run (string "cd " repo-root " && cargo build --release --locked -p hsharp-cli"))
        (eprint "recipe.janet: 'cargo build --locked' nie powiodło się (prawdopodobnie Cargo.lock niezgodny z Cargo.toml) -- regeneruję lockfile i próbuję ponownie bez --locked...")
        (run (string "cd " repo-root " && cargo generate-lockfile"))
        (run (string "cd " repo-root " && cargo build --release -p hsharp-cli")))

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
