# workspace-special — eiv scanner suite

Demonstracja **bytes workspace-special** — trybu wielojęzycznego, w którym
każdy member może być napisany w innym języku i buduje się jako osobny
artefakt (binarny lub biblioteka).

```
eiv-suite/
├── bytes.hk                 ← root workspace config (tryb: special)
│
├── shared-types/            ← H#  library (.a)
│   ├── bytes.hk
│   └── src/types.h#         — wspólne typy: ScanResult, Severity, JsonBuilder
│
├── core-net/                ← C++ shared library (.so)
│   ├── bytes.hk
│   └── src/main.cpp         — raw sockets: Modbus, BACnet, UPnP, banner grab
│
├── analysis/                ← Rust cdylib (.so)
│   ├── bytes.hk
│   ├── Cargo.toml
│   └── src/main.rs          — EVM bytecode static analysis + entropy score
│
├── web3/                    ← Odin binary
│   ├── bytes.hk
│   └── src/main.odin        — ABI calldata decoder + risk flags
│
└── eiv/                     ← H# binary (główne narzędzie)
    ├── bytes.hk
    └── src/main.h#          — scanner CLI: moduły scada/iot/web3
```

## Budowanie

```bash
# Zbuduj cały workspace (kolejność: shared-types → core-net → analysis → web3 → eiv)
bytes build

# Tylko wybrany member
bytes build --member eiv
bytes build --member analysis

# Uruchom główne narzędzie
bytes run --file eiv/src/main.h#
```

## eiv — co robi każdy moduł

### `--module=scada`
Skanuje sieć pod kątem przemysłowych systemów sterowania (ICS/SCADA).

```bash
eiv --module=scada --target=10.0.0.0/24
eiv --module=scada --target=192.168.100.50 --ports=all
```

Protokoły: **Modbus TCP** (502), **BACnet/IP** (47808),
**Profinet** (34964), **EtherNet/IP** (44818).

Wysyła bezpieczne, niskopoziomowe zapytania (raw sockets przez `core-net`)
— nie wywołuje wykonania kodu na PLC, tylko identyfikuje i odczytuje rejestry.

### `--module=iot`
Fingerprinting urządzeń IoT i skanowanie znanych podatności.

```bash
eiv --module=iot --target=192.168.1.50
eiv --module=iot --target=192.168.1.50 --aggressive
```

Sprawdza: **Telnet** (cleartext, CRITICAL), **UPnP M-SEARCH**,
**mDNS fingerprinting**, bannery HTTP/SSH, znane CVE dla wykrytego firmware.

### `--module=web3`
Statyczna analiza bytecode'u smart kontraktów EVM.

```bash
eiv --module=web3 --source=./contract.hex
eiv --module=web3 --source=./contract.bin
```

Wykrywa: **Reentrancy**, **Integer Overflow**, **Unprotected SELFDESTRUCT**,
**tx.origin auth**, **DELEGATECALL injection**. Silnik napisany w Rust
(`analysis` member) — zero zewnętrznych zależności, analiza w pamięci.

## Powiązania między members

```
eiv (H#)
  │
  ├── extern dynamic [c++, "core-net"]    →  core-net.so
  │     eiv_raw_send, eiv_modbus_probe,
  │     eiv_bacnet_probe, eiv_upnp_probe,
  │     eiv_mdns_probe, eiv_banner_grab
  │
  ├── extern dynamic [rust, "analysis"]   →  analysis.so
  │     eiv_web3_analyze, eiv_entropy_score
  │
  └── (shared-types skompilowany jako .a i zlinkowany statycznie)

web3 (Odin)  ←  samodzielne narzędzie pomocnicze, brak linku z eiv
```

## Dlaczego workspace-special?

Standardowy workspace w `bytes` buduje wiele paczek H# i linkuje je razem.
Tryb **special** pozwala na:

1. **Różne języki** w jednym projekcie — każdy member ma własny toolchain.
2. **Różne typy artefaktów** — binarki, `.so`, `.a` w jednym `bytes build`.
3. **Jawna kolejność budowania** (`build-order` w root `bytes.hk`) —
   biblioteki są gotowe zanim binarka próbuje je zlinkować.
4. **Wspólny cache** — `.cache/` w katalogu workspace jest współdzielony
   między memberami (incremental builds).

## Przykładowy output (demo mode)

```
  ┌─────────────────────────────────────────────────┐
  │  eiv  specialized recon scanner  v0.8            │
  │  SCADA / IoT / Web3  ·  HackerOS / H#           │
  └─────────────────────────────────────────────────┘

  ═══ SCADA/ICS Scan ═══
  [SCADA] scanning 192.168.100.50
  Protocols: Modbus TCP (502) · BACnet (47808) · Profinet (34964) · EtherNet/IP (44818)

  ✓  Modbus TCP 192.168.100.50:502
       Protocol : Modbus TCP
       Firmware : detected
       Coils    : 142
       Risk     : CRITICAL
       Note     : ⚠ Large number of exposed coils

  ═══ IoT Device Scan ═══
  [IoT] scanning 192.168.1.100
  Mode: aggressive — extended port range + firmware fingerprinting

  [CRITICAL] Telnet open on 192.168.1.100:23
             Cleartext credentials — immediate remediation required

  [HIGH]     UPnP exposed on 192.168.1.100
             UPnP can be exploited for internal port forwarding

  Known CVEs : CVE-2017-7577,CVE-2016-1000110
  Risk       : CRITICAL

  ═══ Smart Contract Analysis ═══
  [Web3] analyzing smart contract bytecode

  [CRITICAL] Reentrancy — offset 0x0000
             CALL before state update detected
             Fix: use Checks-Effects-Interactions pattern

  [CRITICAL] UnprotectedSelfDestruct — offset 0x0080
             SELFDESTRUCT reachable without access guard
             Fix: add onlyOwner modifier

  [HIGH]     IntegerOverflow — offset 0x0100
             Unchecked arithmetic ADD/MUL in pre-0.8 ABI
             Fix: use SafeMath or Solidity >=0.8
```
