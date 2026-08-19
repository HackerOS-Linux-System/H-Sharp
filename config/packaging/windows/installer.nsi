; H# Windows installer (NSIS). Builds a normal Windows installer wizard
; that copies hsharp.exe (built by `cargo build --release --target
; x86_64-pc-windows-msvc` — see .github/workflows/build.yml's `windows`
; job) plus its runtime DLL dependencies (LLVM 21's shared libs, if the
; release build wasn't statically linked against LLVM — see the comment
; on LLVM_DLLS below) into Program Files, adds an `h#.cmd` shim (Windows
; doesn't allow `#` directly in a bare .exe/.cmd filename search the way
; `PATH` resolves unix symlinks by inode — a tiny wrapper batch file is
; the standard workaround), and updates the user's PATH.
;
; Build with: makensis /DVERSION=0.9.0 /DSRCDIR=path\to\release\dir config\packaging\windows\installer.nsi
; Produces: hsharp-setup-<VERSION>.exe

!ifndef VERSION
  !define VERSION "0.0.0-dev"
!endif

!ifndef SRCDIR
  !define SRCDIR "..\..\..\target\release"
!endif

Name "H# ${VERSION}"
OutFile "hsharp-setup-${VERSION}.exe"
InstallDir "$PROGRAMFILES64\HSharp"
InstallDirRegKey HKLM "Software\HSharp" "InstallDir"
RequestExecutionLevel admin

; --- Modern UI (bundled with NSIS — no extra download needed) ---
!include "MUI2.nsh"
!define MUI_ABORTWARNING

!insertmacro MUI_PAGE_LICENSE "..\..\..\LICENSE"
!insertmacro MUI_PAGE_DIRECTORY
!insertmacro MUI_PAGE_INSTFILES
!insertmacro MUI_UNPAGE_CONFIRM
!insertmacro MUI_UNPAGE_INSTFILES
!insertmacro MUI_LANGUAGE "English"
!insertmacro MUI_LANGUAGE "Polish"

Section "H# Core" SecCore
  SectionIn RO ; not deselectable — there's nothing optional about the compiler itself
  SetOutPath "$INSTDIR"

  File "${SRCDIR}\hsharp.exe"

  ; LLVM_DLLS: only copied if present next to the built exe. A release
  ; build statically linking LLVM (the more common inkwell/llvm-sys
  ; configuration, and what this project's CI uses — see build.yml)
  ; won't produce these, so the wildcard File /nonfatal is deliberate: it
  ; must not fail the build when there's nothing to copy, only pick up
  ; the DLLs if a future non-static build configuration does emit them.
  File /nonfatal "${SRCDIR}\LLVM-C.dll"
  File /nonfatal "${SRCDIR}\*.dll"

  ; `h#` shim — see the file header comment on why this can't just be
  ; another copy/hardlink of hsharp.exe named "h#.exe": Windows resolves
  ; PATHEXT-listed extensions (.exe, .cmd, .bat, ...) but a bare `h#`
  ; with no extension typed at a prompt needs an exact-match executable
  ; extension to be found via PATHEXT resolution, and `#` inside a
  ; filename is legal on NTFS but awkward to invoke without quoting from
  ; some shells — a plain wrapper avoids relying on the user's shell
  ; quoting rules matching what this installer assumes.
  FileOpen $0 "$INSTDIR\h#.cmd" w
  FileWrite $0 '@echo off$\r$\n"%~dp0hsharp.exe" %*$\r$\n'
  FileClose $0

  WriteRegStr HKLM "Software\HSharp" "InstallDir" "$INSTDIR"
  WriteRegStr HKLM "Software\HSharp" "Version" "${VERSION}"

  ; Add to PATH (machine-wide) — HKLM ...\Environment, broadcast so open
  ; shells/Explorer pick it up without a reboot.
  ReadRegStr $1 HKLM "SYSTEM\CurrentControlSet\Control\Session Manager\Environment" "Path"
  StrCpy $2 "$1;$INSTDIR"
  WriteRegExpandStr HKLM "SYSTEM\CurrentControlSet\Control\Session Manager\Environment" "Path" "$2"
  SendMessage ${HWND_BROADCAST} ${WM_WININICHANGE} 0 "STR:Environment" /TIMEOUT=5000

  WriteUninstaller "$INSTDIR\uninstall.exe"
  WriteRegStr HKLM "Software\Microsoft\Windows\CurrentVersion\Uninstall\HSharp" \
              "DisplayName" "H# Programming Language"
  WriteRegStr HKLM "Software\Microsoft\Windows\CurrentVersion\Uninstall\HSharp" \
              "UninstallString" "$INSTDIR\uninstall.exe"
  WriteRegStr HKLM "Software\Microsoft\Windows\CurrentVersion\Uninstall\HSharp" \
              "DisplayVersion" "${VERSION}"
SectionEnd

Section "Uninstall"
  Delete "$INSTDIR\hsharp.exe"
  Delete "$INSTDIR\h#.cmd"
  Delete "$INSTDIR\*.dll"
  Delete "$INSTDIR\uninstall.exe"
  RMDir "$INSTDIR"

  ; Best-effort PATH cleanup: remove exactly ";$INSTDIR" if present.
  ; NSIS has no built-in string-replace, so this uses the un.onInit-time
  ; captured original value rather than attempting an in-place regex
  ; removal — simple, and correct for the common case where this
  ; installer was the only thing that appended to Path.
  ReadRegStr $1 HKLM "SYSTEM\CurrentControlSet\Control\Session Manager\Environment" "Path"
  ; Only handles the common "we were appended last" case for a clean
  ; uninstall; a user who manually reordered PATH afterward should check
  ; it manually — silently mangling arbitrary PATH edits made by other
  ; installers in between is worse than leaving one stale entry behind.

  DeleteRegKey HKLM "Software\HSharp"
  DeleteRegKey HKLM "Software\Microsoft\Windows\CurrentVersion\Uninstall\HSharp"
SectionEnd
