# Software Inventory — `milnes` (Dana Scott box)

Programs installed for the Lean 4 / Rust-semantics / proof-assistant tutoring
environment. Host: `milnes` (Apple Silicon, 24 GB / 512 GB); user account
`scott`; home `/Users/scott`. Package root: Homebrew at `/opt/homebrew`.

_Snapshot: 2026-08-01 (America/Los_Angeles). Living document — updated as the
remaining background installs report in._

Status legend: **OK** = verified on-box · **installing** = background job running ·
**pending‑sudo** = downloaded, needs your password to finish (`.pkg` install).

| # | Program | Version | On PATH / location | Install method | Status |
|---|---------|---------|--------------------|----------------|--------|
| 1 | Homebrew | 6.0.14 | `/opt/homebrew/bin/brew` | bootstrap script | **OK** |
| 2 | git | (Xcode CLT) | `/usr/bin/git` | Xcode Command Line Tools | **OK** |
| 3 | GitHub CLI (`gh`) | latest | `/opt/homebrew/bin/gh` | `brew install gh` | **OK** (auth: `briangmilnes`) |
| 4 | GNU Emacs | 30.2 | `/Applications/Emacs.app`, `/opt/homebrew/bin/emacs` | `brew install --cask emacs` | **OK** |
| 5 | elan (Lean toolchain mgr) | 4.2.3 | `/opt/homebrew/bin/elan` | `brew install elan-init` | **OK** |
| 6 | Lean 4 | 4.32.2 | `/opt/homebrew/bin/lean` | via elan (`leanprover/lean4:v4.32.2`) | **OK** |
| 7 | Lake (Lean build) | 5.0.0 | `/opt/homebrew/bin/lake` | via elan | **OK** |
| 8 | poppler (`pdftotext` etc.) | 26.07.0 | `/opt/homebrew/bin/pdftotext` | `brew install poppler` | **OK** |
| 9 | tesseract (OCR) | 5.5.3 | `/opt/homebrew/bin/tesseract` | `brew install tesseract` (eng/osd/snum) | **OK** |
| 10 | Verus | 0.2026.07.27.31579f0 | `~/projects/verus`, wrapper `/opt/homebrew/bin/verus` | prebuilt release (arm64-macos) | **installing** |
| 11 | OCaml + opam | — | `~/projects/rocq` (local switch) | `brew install opam` + switch | **installing** |
| 12 | Rocq Prover (ex-Coq) | — | `~/projects/rocq/_opam/bin`, `/opt/homebrew/bin/rocq` | opam (`rocq-prover`) | **installing** |
| 13 | Visual Studio Code | — | `/Applications`, `/opt/homebrew/bin/code` | `brew install --cask visual-studio-code` | **installing** |
| 14 | — VS Code ext: Lean 4 | `leanprover.lean4` | — | `code --install-extension` | **installing** |
| 15 | — VS Code ext: Live Share | `ms-vsliveshare.vsliveshare` | — | `code --install-extension` | **installing** |
| 16 | Google Chrome | — | `/Applications` | `brew install --cask google-chrome` | **installing** |
| 17 | MacTeX (no GUI) | — | `/Library/TeX/texbin` | `brew install --cask mactex-no-gui` | **pending‑sudo** |
| 18 | Wolfram Engine | — | `/Applications` | `brew install --cask wolfram-engine` | **pending‑sudo** |

## Steps that still need your password (`sudo`)

Downloaded to the Homebrew cache already, so these install from cache — run in
**Terminal.app** or **`M-x ansi-term`** (never `M-x shell` — the `.pkg` `sudo`
step needs a real TTY):

```bash
brew install --cask mactex-no-gui
```
```bash
brew install --cask wolfram-engine
```

Also outstanding: `sudo scutil --set ComputerName milnes` (HostName /
LocalHostName are already `milnes`; only the display `ComputerName` still reads
"Dana's MacBook Pro").

## Notes

- On this box the Lean proxies (`lake`, `lean`) live at `/opt/homebrew/bin`, not
  `~/.elan/bin` — use plain `lake` / `lean`.
- Verus and Rocq are exposed on PATH via `/opt/homebrew/bin` (wrapper/symlink) to
  avoid editing `~/.zshrc`; no shell‑rc changes were needed for them.
