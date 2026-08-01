---
round: 0
from: orchestrator
to: user
subject: milnes-new-mac-setup
project-tz: America/Los_Angeles
opened: 2026-0801
status: open
---

# Round 0 — New Mac (`milnes`) software setup

Goal: reproduce the full working environment on the new machine **`milnes`**
(24 GB / 512 GB) so Dana's Lean 4 / Mathlib / projective-geometry tutoring runs,
plus the paper→Lean pipeline tooling. Steps you run are marked **[you]** (need
your password, a browser login, or GUI); steps Claude can run once it's on the
machine are marked **[claude]**.

> **Gotchas we already hit — don't repeat them:**
> - **`sudo`/`.pkg` installs (MacTeX) fail in `M-x shell`** (dumb terminal, no
>   TTY for the password). Run those in **`M-x ansi-term`** (a real terminal
>   *inside* Emacs) or Terminal.app.
> - `brew`, `lake`, `gh`, `pdftotext`, `tesseract` live in `/opt/homebrew/bin`
>   (and `~/.elan/bin`); a fresh non-login shell may not have them on `PATH`
>   until you open a new terminal after step 2.
> - `tesseract` here can't read images from `/tmp` and can't read `.png`; OCR by
>   writing **TIFF into the project dir** (see step 9 notes).

## 1. Xcode Command Line Tools **[you]**
```bash
xcode-select --install
```
Verify: `git --version` prints a version.

## 2. Homebrew + PATH **[you]**
```bash
/bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"
```
Then add brew to the shell (Apple Silicon path):
```bash
echo 'eval "$(/opt/homebrew/bin/brew shellenv)"' >> ~/.zprofile
eval "$(/opt/homebrew/bin/brew shellenv)"
```
Open a **new** terminal. Verify: `brew --version`.

## 3. Git identity + GitHub auth **[you]**
```bash
git config --global user.name  "Brian Milnes"
git config --global user.email "briangmilnes@gmail.com"
brew install gh
gh auth login          # GitHub.com → HTTPS → Yes → Login with a web browser
```
Verify: `gh auth status` shows logged in. (This also fixes git push — no tokens.)

## 4. Shell — `~/.zshrc` **[claude]**
Recreate `~/.zshrc` with: cwd-in-prompt, `up1`–`up4` aliases, Emacs-aware plain
prompt, brew on PATH. (Claude has the exact file from the old machine; it can
write it. Key contents: blue `%~` prompt in real terminals, plain `%~ %#` inside
`$INSIDE_EMACS`, `PROMPT_EOL_MARK=''`, `up1..up4`, `eval brew shellenv`.)

## 5. Emacs — `~/.emacs` **[claude]**
Three settings we need in the shell hook (Claude has the exact block):
- `(setq explicit-shell-file-name "/bin/zsh")`
- `comint-process-echoes t` (kills the double-echo)
- prompt-based `dirtrack-mode` (directory tracking follows `cd` and `up1/up2`)
**Reminder:** use `M-x ansi-term` (not `M-x shell`) for anything needing `sudo`.

## 6. VS Code + Lean 4 + Live Share **[you]**
```bash
brew install --cask visual-studio-code
```
Launch VS Code once → Command Palette (⇧⌘P) → "Shell Command: Install 'code' command in PATH".
Install extensions: **Lean 4** (`leanprover.lean4`) and **Live Share** (for pairing).

## 7. Lean toolchain (elan) **[claude/you]**
Opening any `.lean` in VS Code installs `elan` + the toolchain automatically.
Or explicitly:
```bash
brew install elan-init && elan default leanprover/lean4:v4.32.2
```
Verify: `~/.elan/bin/lake --version`.

## 8. CLI tooling **[you]**
```bash
brew install poppler tesseract      # pdftotext/pdftoppm/pdfinfo + OCR
```
Verify: `/opt/homebrew/bin/pdftotext -v` and `/opt/homebrew/bin/tesseract --version`.

## 9. LaTeX — MacTeX **[you, in `M-x ansi-term`]**
```bash
brew install --cask mactex-no-gui
```
**Run this in `M-x ansi-term` or Terminal.app**, not `M-x shell` — the `.pkg`
step runs `sudo` and needs a real terminal for the password. ~6 GB download (slow
CTAN mirror, 20–50 min) + install. Open a new terminal after; verify:
`/Library/TeX/texbin/pdflatex --version`.

## 10. Clone the repositories **[claude]**
```bash
cd ~/projects
git clone https://github.com/briangmilnes/ScottLean4.git
# sibling repos the project references:
git clone https://github.com/briangmilnes/ComputAItionalThinking.git
git clone https://github.com/briangmilnes/GRASE.git
```
Note: `ScottLean4/ComputAItionalThinking/` is gitignored in the ScottLean4 repo;
clone it separately (or symlink) so the CLAUDE.md import resolves.

## 11. Mathlib cache (for the Beeson port) **[claude]**
```bash
cd ~/projects/ScottLean4/Beeson/lean4
~/.elan/bin/lake exe cache get     # ~5,500 prebuilt oleans, ~90 s; NOT a source build
~/.elan/bin/lake build             # smoke test (import Mathlib) should pass
```
Also verify the core library: `cd ~/projects/ScottLean4 && ~/.elan/bin/lake build`
(38 Scott modules, ~100 `sorry` warnings, 0 errors).

## 12. Chrome + Markdown rendering **[you]**
```bash
brew install --cask google-chrome
```
Install a Markdown extension (e.g. "Markdown Reader"), then **`chrome://extensions`
→ Details → turn on "Allow access to file URLs"** so local `.md` renders. (Or just
read docs on GitHub, which renders server-side.)

## 13. Claude Code **[you]**
Install/sign in to Claude Code on `milnes`, same account as this machine.

## 14. Final verification checklist
- [ ] `brew --version`, `gh auth status` OK
- [ ] `~/.elan/bin/lake build` in `ScottLean4/` → 0 errors
- [ ] `lake exe cache get` + `lake build` in `Beeson/lean4/` → Mathlib smoke passes
- [ ] `/Library/TeX/texbin/pdflatex --version` OK
- [ ] `pdftotext`, `tesseract` present
- [ ] VS Code opens a `.lean` file with the Infoview goal state
- [ ] Live Share installed (for the pairing session)

## Files NOT in the repo (recreate locally on `milnes`)
- `HarperBook/PFPL.pdf` / `.txt` — CUP copyright, kept local.
- `MathTexts/DifferentialGeometry/doCarmo.pdf` / `.txt` — commercial, kept local.
- `ComputAItionalThinking/` and `GRASE/` — separate repos (step 10).
- `~/.zshrc`, `~/.emacs` — recreate (steps 4–5).

## Report back
When done, capture results in
`reports/r0000-report-from-user-to-orchestrator-milnes-new-mac-setup.md`
(or tell Claude and it will).
