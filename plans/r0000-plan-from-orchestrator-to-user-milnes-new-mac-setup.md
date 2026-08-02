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

## Progress — milnes handoff (2026-08-01)

Bootstrap done by hand. Accounts: `Scott` (admin, Dana's) and `milnes` (admin);
currently working in the **Scott** account as Brian — account ownership is a TODO.
- [x] Booted, FileVault on; both accounts admin.
- [x] Machine renamed to `milnes` (ComputerName / HostName / LocalHostName).
- [x] Step 1 — Xcode Command Line Tools (git works).
- [x] Step 2 — Homebrew installed + on PATH (`brew --version` OK).
- [x] Step 3 — git identity (Brian) + `gh auth login` via browser.
- [~] Emacs installing (`brew install --cask emacs`).
- [~] Claude Code installing (native `curl … | bash`) — to drive the rest on-machine.

**Remaining — hand these to the milnes Claude agent (it runs them from this plan):**
clone repos (step 10) · `~/.zshrc` + `~/.emacs` (steps 4–5; **contents in the
Appendix** so no old-machine copy needed) · VS Code + Lean 4 + Live Share (6) ·
elan (7) · poppler + tesseract (8) · MacTeX **in `M-x ansi-term`** (9) ·
Mathematica/Wolfram + plotting (9b–9c) · `lake exe cache get` + build (11) ·
Chrome + Markdown (12) · verification (14).

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

## 9b. Mathematica / Wolfram — to open Dana's `.nb` notebooks **[you]**
Dana's 37 recovered course notebooks (`ScottClasses/`) are Mathematica `.nb`
files and need a Wolfram app to open.
- If Dana has a Mathematica license (e.g. via CMU), install full **Mathematica**.
- Otherwise the free **Wolfram Engine** (CLI kernel) or **Wolfram Player** (GUI
  viewer/runner, no save) opens them:
```bash
brew install --cask wolfram-engine        # free kernel; Player is a download from wolfram.com
```
Verify: open `ScottClasses/15-491/Lectures/01.ComplexNumbers.nb`.

## 9c. Plotting — pick one on the box **[you/claude]**
- **Mathematica** — nothing more to install if 9b is done (matches his notebooks).
- **Python/matplotlib**: `python3 -m pip install --user matplotlib`
- **LaTeX TikZ/pgfplots**: already available via MacTeX (step 9).

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
- [ ] Mathematica/Wolfram opens a `.nb` notebook
- [ ] a plotting option chosen and working

## Files NOT in the repo (recreate locally on `milnes`)
- `HarperBook/PFPL.pdf` / `.txt` — CUP copyright, kept local.
- `MathTexts/DifferentialGeometry/doCarmo.pdf` / `.txt` — commercial, kept local.
- `ComputAItionalThinking/` and `GRASE/` — separate repos (step 10).
- `~/.zshrc`, `~/.emacs` — recreate (steps 4–5).

## Report back
When done, capture results in
`reports/r0000-report-from-user-to-orchestrator-milnes-new-mac-setup.md`
(or tell Claude and it will).

## Appendix — dotfile contents (for the milnes agent)

### `~/.zshrc`
```zsh
# ~/.zshrc — personal zsh configuration

if [[ -n "$INSIDE_EMACS" ]]; then
    # Running inside an Emacs "dumb" shell: keep it plain.
    # %d (absolute path, not %~) so Emacs dirtrack captures a leading `/`.
    PROMPT='%d %# '
    PROMPT_EOL_MARK=''
else
    # Real terminal (Terminal.app, iTerm, VS Code)
    PROMPT='%F{blue}%~%f %# '
    precmd() { print -Pn "\e]2;%~\a" }
fi

# Directory-up shortcuts
alias up1='cd ..'
alias up2='cd ../..'
alias up3='cd ../../..'
alias up4='cd ../../../..'

# Homebrew (Apple Silicon) on PATH if installed
[ -x /opt/homebrew/bin/brew ] && eval "$(/opt/homebrew/bin/brew shellenv)"

# History
HISTFILE=~/.zsh_history
HISTSIZE=10000
SAVEHIST=10000
setopt SHARE_HISTORY

# Completion
autoload -Uz compinit && compinit
```

### `~/.emacs` — the shell/terminal block this project needs
```elisp
(setq explicit-shell-file-name "/bin/zsh")

;; M-x shell: strip the pty's duplicate echo, and track the working directory
;; from the PROMPT (follows cd, pushd/popd, and the up1/up2 aliases).
(add-hook 'shell-mode-hook
          (lambda ()
            (setq comint-process-echoes t)
            (shell-dirtrack-mode -1)
            ;; Capture from the literal `/` and exclude CR/space/newline, so zsh's
            ;; ZLE carriage-return prompt prefix can't sneak into the path. Requires
            ;; the in-Emacs PROMPT to use %d (absolute) — see ~/.zshrc above.
            (setq-local dirtrack-list '("\\(/[^ \r\n]*\\) [#%] " 1 nil))
            (dirtrack-mode 1)))

(add-to-list 'default-frame-alist '(background-color . "white"))
```
Brian's full personal `~/.emacs` lives on the old machine — copy it over for the
rest; the block above is the minimum this project relies on. **Reminder:** run
`sudo`/`.pkg` installs (MacTeX) in `M-x ansi-term`, never `M-x shell`.
