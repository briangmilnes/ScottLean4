---
round: r0001
from: orchestrator
to: user
subject: toolchain-audit
date: 2026-0806-13:10
started: 2026-0806-12:25
finished: 2026-0806-13:10
related:
  - plans/r0001-plan-from-orchestrator-to-orchestrator-toolchain-audit.md
  - reports/r0001-report-from-agent1-to-orchestrator-lean-build.md
  - reports/r0001-report-from-agent2-to-orchestrator-vscode.md
  - reports/r0001-report-from-agent3-to-orchestrator-pdf-pipeline.md
---

# r0001 — Toolchain audit: result

Host: Linux 7.0.0-28-generic x86_64, X11/GDM session, bash. Elapsed 45 minutes,
three subagents run concurrently plus orchestrator measurement.

All four acceptance criteria are met.

| # | Criterion | Measurement |
| -- | --------- | ----------- |
| 1 | `lake build` exits 0 | 0 errors, 0 warnings, 0 `sorry`, 3 jobs, both source modules |
| 2 | VS Code Lean server and infoview | confirmed by the user at the GUI |
| 3 | `md2pdf.sh` renders 0 tofu | 0 missing characters on `PaperInventory.md` and `INDEX.md`, exit 0 |
| 4 | macOS rendering unchanged | macOS code path proved identical, 10 executable lines, empty diff |

## What was wrong, and what fixed it

Four defects were found. Two were predicted in the plan; two were not.

**D1 — no Lean build on this host.** `ScottDomains/.lake` was absent, so Mathlib
was neither fetched nor built. `lake exe cache get` exit 0 in 192 s with **0
bytes downloaded**: `~/projects/PFPL` had already pinned the identical Mathlib
revision `905b9581`, so all 8,638 oleans were in `~/.cache/mathlib` and only
needed decompressing (7.4 s). `lake build` exit 0 in 2 s, 924 jobs. On a host
with a cold cache expect roughly 440 MB of olean download, not the 1–3 CPU-hour
source build. Determinism rests on the 9 commit SHAs in `lake-manifest.json`.

**D2 — `lake build` covered half the source.** Not in the plan; found by agent1.
`defaultTargets = ["ScottDomains"]` with a `lean_lib` carrying no `globs`, and
`ScottDomains.lean` does not import `ScottDomains.ExistingTheories`, so plain
`lake build` elaborated 1 of 2 modules. A Mathlib bump could have broken the
unreferenced file while the build still exited 0. Fixed by adding
`globs = ["ScottDomains.+"]`; the build now reports 3 jobs and elaborates both.

**D3 — the PDF pipeline could not run here at all.** Two independent causes,
where the plan predicted one. First, `scripts/md2pdf.sh` is `#!/bin/zsh` and
uses the zsh-only `${0:A:h}`; zsh was not installed, so the script exited 127
before reaching LaTeX. The user installed zsh (5.9), which leaves the script
untouched — the alternative, rewriting it for bash, would edit a file both macs
execute. Second, the fonts.

**D4 — the wrong font package.** The plan named `fonts-stix`. That package is
STIX **1.x** — families `STIXGeneral`, `STIX Math`, `STIXSizeOneSym` — and
contains no STIX Two whatsoever; agent3 established this by reading family names
out of the candidate `.deb` with `fc-query`. `STIX Two Text` and `STIX Two Math`
come from **`texlive-fonts-extra`**, or from CTAN `stix2-otf` with no root at
all. `texlive-science` is unused by this pipeline.

A measurement error of the orchestrator's belongs in the record: the baseline
declared all five fonts missing on the evidence of `fc-list`. `fc-list` is the
wrong instrument. `texlive-fonts-extra` installs fonts into the texmf tree,
where lualatex resolves them via kpathsea and fontconfig never indexes them —
so `fc-list` reports nothing while `kpsewhich` and lualatex both find the font.
After the install, `\setmainfont{STIX Two Text}` succeeded on a host whose
`fc-list` still showed no STIX Two.

## The header change

`scripts/md-pdf-header.tex` named five fonts, three of which (`Menlo`,
`Arial Unicode MS`, `Apple Symbols`) ship only with macOS and have no Debian
equivalent. The fix is a per-platform branch in one file, selected by
`\IfFontExistsTF{Menlo}`.

The governing requirement was the user's: **the symbols Dana Scott is used to
must not change.** That is discharged two ways, neither of them a judgment call.

1. The macOS branch is the previous header verbatim. Comparing executable lines
   (comments and indentation stripped) of the previous header against the macOS
   branch: 10 lines against 10 lines, `diff -u` empty. On a mac the same
   fallback chain, the same `STIX Two Text`, the same `Menlo` run as before.
2. A false negative on the branch test cannot silently substitute fonts on a
   mac. `\IfFontExistsTF` and `\setmonofont` use the same luaotfload name
   lookup, so if the test failed on a mac then the previous header's
   `\setmonofont{Menlo}` would have failed there too — and the macs render
   these documents today.

The Linux branch keeps `STIX Two Text` as the main face and substitutes
`DejaVu Sans Mono` for Menlo and `DejaVu Sans` / `Noto Sans Symbols2` for the
two Apple fallbacks, retaining `STIX Two Math` at the head of the chain. Two
traps agent3 found are documented in the file, because each yields a broken PDF
with no obvious cause: no `#` may appear inside `\directlua` (TeX doubles the
catcode-6 `#` and the Lua chunk aborts), and naming an unregistered fallback
table in `RawFeature` makes the font itself unloadable rather than ignoring the
feature. The applied header avoids both by construction — literal tables, and
`add_fallback` always runs first.

Rejected alternative: agent3's header, 86 added lines, discriminating by a Lua
probe of four families and degrading to `DejaVu Serif` / `Latin Modern Mono`
when families are absent. Both versions measure 0 tofu. The extra 53 lines
handle configurations that exist on none of the three machines in use — a Linux
host with STIX Two Math but no STIX Two Text, or with no fallback family at all.

Verification of the applied header on this host: `md2pdf.sh` exit 0, 4 pages,
78,471 bytes, 0 missing characters. Seven faces embedded and subsetted — STIX
Two Text regular/bold/italic, STIX Two Math, DejaVu Sans, DejaVu Sans Mono
regular/bold. agent3 independently measured the same configuration at 0 missing
characters over a 58-code-point corpus drawn from `SymbolMap.tex`,
`PaperInventory.md` and `INDEX.md`, cross-checked by `pdftotext` recovering
58/58.

## Corrections to the plan

| # | Plan Part 3 row | Correction |
| -- | --------------- | ---------- |
| 1 | row 2, `fonts-stix` | wrong package, ships STIX 1.x. Use `texlive-fonts-extra` or CTAN `stix2-otf` |
| 2 | row 3, `texlive-science` | unused by this pipeline |
| 3 | row 4, upgrade the Lean4 extension | no-op. Installed 0.0.239 **is** the marketplace latest (published 2026-07-29) |
| 4 | row 5, `~/.elan/bin` PATH | not applicable. `gnome-shell`, `systemd --user` and the running `code` process all carry it as the first PATH entry |
| 5 | not in the plan | `zsh` was required, and was the first of the two PDF defects |

Rows 3 and 4 were predictions the orchestrator made from experience with Linux
hosts; agent2 refuted both by measurement — the marketplace gallery API for the
version, and `/proc/<pid>/environ` for the PATH.

## Editor configuration

`lean4.input.languages` defaulted to `["lean4","lean"]`, so the `\`-prefixed
abbreviations did not fire in Markdown — relevant because the domain-theory
notes in `ScottDomains/docs/` carry the same symbols as the proofs. Added
`markdown` in two workspace settings files, repo root and `ScottDomains/`,
because VS Code applies workspace settings from the folder actually opened and
`ScottDomains/` is opened as its own folder. Workspace scope rather than
host-local user settings, so the change reaches both macs through git. The
array replaces rather than extends the extension default, so both defaults are
listed explicitly.

Live Share (`ms-vsliveshare.vsliveshare` v1.1.122) was installed, since
`docs/SoftwareInventory.md` and `docs/Curriculum.md` name it as how tutoring
sessions pair on Lean. The user deferred signing in; the extension is dormant
until a session is started or joined.

## Facts worth keeping

- **The repo-root `mathlib/` copy is safe and nearly free.** 8,264 files
  byte-identical to `ScottDomains/.lake/packages/mathlib` at the same commit
  `905b9581`, on no import path (no lakefile, no `lean-toolchain`, 0 oleans,
  `LEAN_PATH` unset), costing 113 MiB of a 7.4 GiB tree — 1.5%. Keep it.
- **Do not open it in VS Code.** agent2 read `findLeanProjectRootInfo` out of
  the extension: the walk-up starts at the opened file's directory looking for
  `lean-toolchain`. `mathlib/` has none, so the extension resolves to the
  Mathlib-less root project and the infoview fails. Read Mathlib source under
  `ScottDomains/.lake/packages/mathlib/` instead.
- **Disk is the binding constraint.** The volume sat at 97%, 15 GiB free, after
  `ScottDomains/.lake` took 7.4 GiB. `Playground/` and `Beeson/lean4/` pin the
  same Mathlib and are unbuilt; each would add roughly another 7 GiB, so two
  more such builds exhaust it. The shared cache is not the cost.
- **elan on PATH depends on X11.** `/etc/gdm3/Xsession` sources `~/.profile`,
  which is the only place elan is set — not `.bashrc`, not `/etc/environment`.
  A switch to a Wayland session would skip it. Insurance is step 9 of
  `scripts/manualsetup.sh`.

## Artifacts

Plan: `ScottDomains/plans/r0001-plan-from-orchestrator-to-orchestrator-toolchain-audit.md`.
Subagent reports: `…-from-agent1-…-lean-build.md`, `…-from-agent2-…-vscode.md`,
`…-from-agent3-…-pdf-pipeline.md`. Logs:
`ScottDomains/logs/lake-build.2026-0806-12:30.agent1.log`,
`ScottDomains/logs/md2pdf.2026-0806-12:56.agent3.log`.

Code changed: `ScottDomains/lakefile.toml` (globs), `scripts/md-pdf-header.tex`
(per-platform branch), `.vscode/settings.json` and
`ScottDomains/.vscode/settings.json` (new), `scripts/manualsetup.sh` (new).

## Open, for the user

1. Render one Markdown file on a mac before the next PDF goes to Dana. Criterion
   4 is proved by construction, but a render is cheap insurance.
2. Decide the disk question before building `Playground/` or `Beeson/lean4/`.
3. Live Share sign-in, whenever tutoring sessions need it.
