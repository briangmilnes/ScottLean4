---
round: 1
from: orchestrator
to: user
subject: milnes-patch-reboot-restart
project-tz: America/Los_Angeles
opened: 2026-0801
status: open
---

# Round 1 — Patch macOS (Tahoe 26.6) + reboot; resume checklist

Goal: safely apply the pending macOS update and reboot `milnes`, then confirm the
environment still works and finish the few remaining **[you]** (password/GUI)
items. A reboot is **safe right now** — all background downloads have completed
(nothing in-flight to lose). The reboot's re-login also *arms* two things that
are already configured but not yet live: the **Ctrl-1…9 desktop hotkeys** and the
**`~/.zshrc` PATH/prompt changes**.

Legend: **[you]** needs your password / a GUI / a browser login. **[claude]** I
can run once you're back.

## Status snapshot — verified on-box (2026-08-01)

Installed and tested (0-error / smoke-passed):
- Homebrew 6.0.14, git, **gh** (auth `briangmilnes`), git identity (Brian).
- **Emacs 30.2** (`/Applications/Emacs.app` + CLI); `M-x shell` dirtrack **fixed**
  (`~/.zshrc` uses `%d` absolute prompt; `~/.emacs` regexp captures from `/`).
- **Lean**: elan 4.2.3, Lean 4.32.2, Lake 5.0.0. Builds: Beeson Mathlib smoke ✅,
  core `ScottLean4` ✅ (**0 errors**, 13 `sorry`).
- **Verus** 0.2026.07.27.31579f0 (+ rustup 1.29.0, toolchains `stable`/`1.97.1`);
  proof smoke test **2 verified, 0 errors**.
- **Rust**: `cargo`/`rustc` 1.97.1 on PATH via `~/.zshrc` (`/opt/homebrew/opt/rustup/bin`).
- **Rocq** 9.2.0 + OCaml 5.3.0 + opam 2.5.2 at `~/projects/rocq`; `.v` compile ✅.
- **poppler** 26.07.0, **tesseract** 5.5.3.
- **VS Code** + extensions **Lean 4** & **Live Share**; **Chrome**; **KeePassXC**.
- Repos: `ScottLean4`, `ComputAItionalThinking` (+symlink), `GRASE`, `APAS-VERUS`.
- `~/projects/RustSemantics/`: **6 paper PDFs** + **6 artifacts** (5 git clones +
  `verusbelt`/lambda-verus tarball extracted).
- `tutorials/`: 4 Lean tutorials (CADE2021, Theorem Proving in Lean 4,
  Mathematics in Lean, Hitchhiker's Guide / Logical Verification 2024).
- Ctrl-1…9 → Desktop 1…9 written (arms on re-login); `docs/SoftwareInventory.md`.
- **MacTeX** 6.4 GB `.pkg` **cached** (install is instant, but needs sudo).

## Step 1 — Patch: install macOS Tahoe 26.6 **[you]**
Current: **26.5.1**. Pending: **macOS Tahoe 26.6** (~3.8 GB, requires restart).
System Settings → General → Software Update → Update Now. (Or, in Terminal.app:
`sudo softwareupdate -i -a -R` — needs your password; `-R` reboots.)

> A reboot now loses nothing — all our downloads are done. Do this whenever ready.

## Step 2 — After reboot: sudo / GUI installs **[you]**
Run the `.pkg`/GUI items the reboot's fresh session enables. Use **Terminal.app**
or **`M-x ansi-term`** for sudo (never `M-x shell`).

1. **MacTeX** (from cache, instant): `brew install --cask mactex-no-gui`
   Then open a new shell; verify `pdflatex --version` (PATH added via
   `/etc/paths.d/TeX` automatically).
2. **Wolfram** — the pre-download **failed** earlier (`Connection reset by peer`
   from Wolfram's CDN). Retry: `brew install --cask wolfram-engine`. Note it also
   needs a **free Wolfram account** to activate the kernel. (Alt: Wolfram Player,
   or full Mathematica if Dana has a CMU license.)
3. **ComputerName**: `sudo scutil --set ComputerName milnes` (HostName /
   LocalHostName are already `milnes`; only the display name still reads
   "Dana's MacBook Pro").
4. **Chrome Markdown extension**: install **Markdown Viewer (simov)** from the Web
   Store, then `chrome://extensions` → Details → enable **"Allow access to file
   URLs"** (renders local `.md`).

## Step 3 — After reboot: verification checklist
The reboot changes these; confirm each:
- [ ] **Ctrl-1…5** switch to Desktop 1…5 (you have 5 spaces; 6–9 activate as you
      add desktops). If not: System Settings → Keyboard → Shortcuts → Mission
      Control shows "Switch to Desktop N" ticked.
- [ ] New terminal: `brew`, `lake`, `verus`, `rocq`, `cargo`, `rustc` all resolve
      (`command -v …`).
- [ ] Fresh `M-x shell`: `cd ScottLean4` updates the buffer's directory (dirtrack).
- [ ] Smoke: `cd ~/projects/ScottLean4 && lake build` → 0 errors.
- [ ] `pdflatex --version` (after Step 2.1).

## Step 4 — What I can finish once you're back **[claude]**
- Finalize `~/projects/RustSemantics/README.md` (papers + artifacts inventory).
- Refresh `docs/SoftwareInventory.md` to all-green (VS Code/Chrome/Verus/Rocq/
  Rust/KeePassXC done; MacTeX/Wolfram per Step 2).
- Optional plotting setup: `pip install matplotlib` + scaffold `tutorials/plotting/`
  (pgfplots + matplotlib + Wolfram examples) — see round-0 step 9c.
- A bespoke **Scott-domain / fixed-point** Lean exercise, if wanted.

## Report back
Tell me the Step 3 results (or just "rebooted, back") and I'll pick up Step 4.
