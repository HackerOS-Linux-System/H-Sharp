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

# Pakiet Zenit ma dawać w /usr/bin WYŁĄCZNIE `h#` -- bez osobnej binarki
# `hsharp` obok (to inaczej niż debian/arch/macos, które trzymają
# `hsharp` + symlink `h#`; tu celowo zostaje tylko jedna nazwa na PATH).
(def dest (string bin-dir "/h#"))
(spit dest (slurp bin-path))
(run (string "chmod +x " dest))

# ---------------------------------------------------------------------
# std -- kopiujemy zawartość repo-root/std do
# /usr/lib/HackerOS/H#/std wewnątrz stage'a (czyli finalnie do
# /usr/lib/HackerOS/H#/std na docelowym systemie). To DOKŁADNIE ścieżka,
# pod którą hsharp-compiler/hsharp-interpreter/hsharp-typecheck
# rozwiązują `use "std -> lib"` (patrz stała STD_LIB_ROOT w
# source-code/interpreter/src/helpers.rs oraz identyczny literał w
# source-code/compiler/src/modules.rs) -- bez tego katalogu `h#`
# zbudowany przez tę receptę nie potrafi skompilować/uruchomić NICZEGO,
# co robi `use "std -> ..."`, łącznie z `bytes` niżej.
# ---------------------------------------------------------------------
(def std-src (string repo-root "/std"))
(unless (os/stat std-src :mode)
  (fail (string "nie znaleziono katalogu std w repo: " std-src)))

(def hackeros-hsharp-dir (string stage "/usr/lib/HackerOS/H#"))
(ensure-dir-p hackeros-hsharp-dir)
# `cp -r` z katalogiem docelowym, który już istnieje, kopiuje `std` DO
# środka niego (nie nadpisuje go samego) -- stąd wynik to
# .../HackerOS/H#/std/*.h#, a nie .../HackerOS/H#/*.h# bezpośrednio.
(run (string "cp -r " std-src " " hackeros-hsharp-dir))

# ---------------------------------------------------------------------
# Ta sama std musi też fizycznie istnieć pod /usr/lib/HackerOS/H#/std
# na MASZYNIE BUDUJĄCEJ (nie tylko w stage'u) -- świeżo zbudowany `h#`
# szuka jej pod tą stałą, wpisaną na sztywno ścieżką, żeby móc
# skompilować `bytes` w kroku poniżej, zanim jeszcze cokolwiek z tego
# pakietu trafi do instalatora użytkownika. Ten sam wzorzec co
# ensure-cargo/ensure-llvm wyżej: dogaduj brakującą zależność builda,
# zamiast zakładać, że ktoś zrobił to ręcznie wcześniej.
# ---------------------------------------------------------------------
(defn ensure-host-std []
  (def host-std-dir "/usr/lib/HackerOS/H#/std")
  (unless (os/stat host-std-dir :mode)
    (eprint "recipe.janet: brak " host-std-dir " na hoście -- instaluję z ./std, żeby świeżo zbudowany h# mógł skompilować 'bytes'...")
    (def sudo (sudo-))
    (run (string sudo "mkdir -p /usr/lib/HackerOS/H#"))
    (run (string sudo "cp -r " std-src " /usr/lib/HackerOS/H#"))))

(ensure-host-std)

# ---------------------------------------------------------------------
# Manager pakietów `bytes` -- klonujemy Bytes-Repository/bytes, budujemy
# go świeżo zbudowanym `h#` (nie systemowym -- w tym momencie pakiet
# jeszcze nie jest zainstalowany, więc na PATH nic o nazwie `h#` nie
# musi w ogóle istnieć) i wynikową binarkę `build/main` wstawiamy do
# stage'a jako /usr/bin/bytes. Cały ten krok dzieje się TERAZ, w
# recepcie budującej pakiet -- w finalnym .zpk ląduje już gotowa,
# skompilowana binarka `bytes`, nic więcej się nie klonuje ani nie
# kompiluje na maszynie użytkownika przy instalacji.
# ---------------------------------------------------------------------
(defn ensure-git []
  (unless (have? "git")
    (eprint "recipe.janet: brak 'git' -- próbuję zainstalować (" (detect-pm) ")...")
    (pm-install {:apt "git" :dnf "git" :pacman "git" :zypper "git" :apk "git" :brew "git"}))
  (unless (have? "git")
    (fail "nie udało się zapewnić 'git' -- zainstaluj ręcznie i uruchom ponownie")))

(ensure-git)

(def bytes-workdir
  (let [r (shell-out "mktemp -d")]
    (if (r 0) (r 1) (fail "nie udało się utworzyć katalogu tymczasowego dla 'bytes'"))))

(run (string "git clone https://github.com/Bytes-Repository/bytes.git " bytes-workdir "/bytes"))

(def bytes-dir (string bytes-workdir "/bytes"))

# `bin-path` to jeszcze niespakowana binarka `hsharp` (ta sama, którą
# wyżej skopiowaliśmy do stage'a jako `h#`) -- wołamy ją bezpośrednio po
# pełnej ścieżce, więc nie zależy to od tego, czy `h#`/`hsharp` jest
# gdziekolwiek na PATH tej maszyny.
(run (string "cd " bytes-dir " && " bin-path " compile src/main.h#"))

(def bytes-bin-path (string bytes-dir "/build/main"))
(unless (os/stat bytes-bin-path :mode)
  (fail (string "'bytes' skompilowane, ale nie znaleziono wynikowej binarki: " bytes-bin-path)))

(def bytes-dest (string bin-dir "/bytes"))
(spit bytes-dest (slurp bytes-bin-path))
(run (string "chmod +x " bytes-dest))

# Sprzątanie katalogu tymczasowego -- best effort, nie przerywa builda.
(try-run (string "rm -rf " bytes-workdir))

# Licencja -- ta sama konwencja co PKGBUILD (usr/share/licenses/<pkg>/LICENSE).
(def license-src (string repo-root "/LICENSE"))
(when (os/stat license-src :mode)
  (def license-dir (string stage "/usr/share/licenses/hsharp"))
  (ensure-dir-p license-dir)
  (spit (string license-dir "/LICENSE") (slurp license-src)))
