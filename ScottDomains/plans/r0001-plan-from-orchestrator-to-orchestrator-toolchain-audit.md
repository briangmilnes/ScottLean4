---
round: r0001
from: orchestrator
to: orchestrator
subject: toolchain-audit
date: 2026-0806-12:25
status: pending
---

# r0001 — Toolchain audit and install plan (this Linux host)

Goal: bring this host to the state the two macs were in — Lean 4 + Mathlib
builds `ScottDomains`, VS Code drives interactive proofs, and `scripts/md2pdf.sh`
renders Markdown to PDF with zero missing glyphs for exchange with Dana Scott.

Host: Linux 7.0.0-28-generic, x86_64, bash. Project root
`/home/milnes/projects/ScottLean4`, GRASE dirs under `ScottDomains/`.

## Part 1 — Baseline measurement (already taken by the orchestrator)

Do not re-measure these; start from them.

| #  | Component | Found | State |
| -- | --------- | ----- | ----- |
| 1  | `elan` | 4.2.3 (2026-06-08), `~/.elan/bin` | present |
| 2  | `lean` | 4.32.2, commit `f3b06c7` | present, matches both `lean-toolchain` pins |
| 3  | `lake` | 5.0.0-src+f3b06c7 | present |
| 4  | `ScottDomains/.lake` | absent | **never built on this host** |
| 5  | root `.lake` | absent | root `lakefile.toml` has no Mathlib require |
| 6  | `mathlib/` at repo root | 113 MB source, tracked in repo HEAD `40f8c90`, no `.lake` | reading copy, not a Lake dependency |
| 7  | `code` (VS Code) | 1.130.0, x64 | present |
| 8  | `leanprover.lean4` extension | 0.0.239 | present |
| 9  | `pandoc` | 3.9.0.2 (+server +lua) | present |
| 10 | `lualatex` | LuaHBTeX 1.17.0, TeX Live 2023/Debian | present |
| 11 | `pdflatex`, `tlmgr` | present | TeX Live 2023 Debian packaging |
| 12 | `git`, `curl`, `gh`, `python3`, `node` v22.20.0, `npm` | present | — |
| 13 | Font `STIX Two Text` | **missing** | `md2pdf.sh` main font |
| 14 | Font `STIX Two Math` | **missing** | fallback #1 |
| 15 | Font `Menlo` | **missing** | macOS-only; `md2pdf.sh` mono font |
| 16 | Font `Arial Unicode MS` | **missing** | fallback #2 |
| 17 | Font `Apple Symbols` | **missing** | fallback #3 |
| 18 | Fonts `DejaVu Sans`, `DejaVu Sans Mono`, `Noto Sans Symbols2` | present | Linux substitution candidates |

Two defects follow from the baseline:

- **D1 (Lean).** `ScottDomains` has no `.lake`, so Mathlib is neither fetched nor
  cached here. Building Mathlib from source is roughly 1–3 CPU-hours; `lake exe
  cache get` downloads prebuilt `.olean` files in minutes. The cache is only
  valid for the exact Mathlib revision pinned in `lakefile.toml` (`v4.32.2`),
  which matches the installed toolchain — so the cache path should hit.
- **D2 (PDF).** `scripts/md-pdf-header.tex` names five fonts, all absent here;
  three of them (`Menlo`, `Arial Unicode MS`, `Apple Symbols`) ship with macOS
  and cannot be installed from Debian packages. `scripts/md2pdf.sh` therefore
  fails or silently drops glyphs on this host. The fix must keep the existing
  macOS behavior working — the two macs still render these files — so the header
  needs per-platform font selection, not replacement.

## Part 2 — Subagent fan-out

Three independent subagents, launched concurrently. Each is read-mostly for
diagnosis; each proposes install commands and does not run privileged installs
without confirmation.

### Subagent A1 — Lean 4 / Mathlib build

Scope: `ScottDomains/` and repo root.

1. Confirm `elan show` lists `leanprover/lean4:v4.32.2` as installed and default.
2. In `ScottDomains/`, run `lake exe cache get`, then `lake build`. Report elapsed
   wall-clock, downloaded bytes, and the exact error text on any failure.
3. Report the build outcome as a measurement: modules built, error count, warning
   count, and `sorry` count across `ScottDomains/**/*.lean` (count via
   `grep -rn '\bsorry\b'`, excluding comments where it is easy to do so).
4. Check whether `mathlib/` at repo root duplicates the Lake-fetched Mathlib
   (`ScottDomains/.lake/packages/mathlib`). Report the disk cost of both and
   whether the root copy is referenced by any import path. **Do not delete it** —
   it is tracked in git and may be Dana's reading copy.
5. Check `~/.cache/mathlib` size and whether the cache is shared across projects.
6. Report whether `lake build` is reproducible from a clean `.lake` and what the
   one-command bootstrap for a fresh host is.

Deliverable: `ScottDomains/reports/r0001-report-from-agent1-to-orchestrator-lean-build.md`,
with build logs written to `ScottDomains/logs/lake-build.YYYY-MMDD-HH:MM.agent1.log`.

### Subagent A2 — VS Code and interactive proof loop

Scope: editor configuration only; no Lean rebuilds.

1. Compare installed `leanprover.lean4@0.0.239` against the latest published
   version (`code --install-extension leanprover.lean4` is the upgrade path;
   check the marketplace version first, do not upgrade unprompted). Report both
   version numbers and whether 0.0.239 supports Lean 4.32.2.
2. Verify the extension's Lean server starts against `ScottDomains/`: report
   whether the infoview renders and whether `elan` on `PATH` is visible to a
   VS Code session launched from a desktop launcher (not just from this shell) —
   the common Linux failure is `~/.elan/bin` missing from the desktop
   environment's `PATH`.
3. Report the abbreviation/unicode-input configuration (`lean4.input.*`) and
   whether it matches what the macs used, since Dana types the symbols directly.
4. Check for a workspace file or `.vscode/settings.json` in the repo; report
   whether opening `ScottDomains/` as its own folder (rather than the repo root)
   is required for the Lean server to find `lakefile.toml`.
5. List any missing convenience extensions the macs had. Propose, do not install.

Deliverable: `ScottDomains/reports/r0001-report-from-agent2-to-orchestrator-vscode.md`.

### Subagent A3 — LaTeX and Markdown-to-PDF pipeline

Scope: `scripts/md2pdf.sh`, `scripts/md-pdf-header.tex`, `scripts/tex2pdf.sh`,
`scripts/lean2tex.sh`, and the existing PDFs under `ScottDomains/docs/`.

1. Reproduce the failure: run `scripts/md2pdf.sh` on `ScottDomains/docs/PaperInventory.md`
   to a scratch output path and capture the exact lualatex/luaotfload error.
2. Enumerate what TeX Live 2023/Debian actually provides here: check for
   `texlive-latex-extra`, `texlive-fonts-extra`, `texlive-luatex`,
   `texlive-science`, and `fonts-stix` / `fonts-texgyre` via `dpkg -l`. Report
   which are missing and the exact `apt-get install` line to add them.
3. Design a per-platform font block for `md-pdf-header.tex` that preserves the
   current macOS rendering and adds a Linux branch. Candidate Linux mapping:
   main `STIX Two Text` (from `fonts-stix`), mono `DejaVu Sans Mono`, fallback
   chain `STIX Two Math` → `DejaVu Sans` → `Noto Sans Symbols2`. Select the
   branch by testing font availability inside `\directlua`, so one header file
   works on both platforms and the two macs are unaffected.
4. Validate glyph coverage empirically, not by inspection: render
   `ScottDomains/docs/PaperInventory.md` and `INDEX.md`, then count tofu
   (missing-glyph) boxes. The repo already treats "0 tofu" as the acceptance
   criterion (see commit `1137a05`). Report the tofu count before and after.
   Use the symbol set in `ScottDomains/docs/SymbolMap.tex` as the test corpus —
   it is the project's own inventory of the domain-theory symbols in use.
5. Confirm the round-trip Dana needs: Markdown in, PDF out, opens in macOS
   Preview/Safari with correct symbols. Report the rendered file sizes and page
   counts.

Deliverable: `ScottDomains/reports/r0001-report-from-agent3-to-orchestrator-pdf-pipeline.md`,
plus the proposed `md-pdf-header.tex` diff (proposed, not applied).

## Part 3 — Install commands (orchestrator's current best estimate)

Subagents confirm or correct these; they are not yet executed.

| #  | Need | Command | Privilege |
| -- | ---- | ------- | --------- |
| 1  | Mathlib oleans | `cd ScottDomains && lake exe cache get && lake build` | user |
| 2  | STIX fonts | `sudo apt-get install fonts-stix` | root |
| 3  | Extra TeX packages | `sudo apt-get install texlive-latex-extra texlive-fonts-extra texlive-luatex texlive-science` | root |
| 4  | Lean4 extension upgrade | `code --install-extension leanprover.lean4` | user |
| 5  | `PATH` for desktop VS Code | append `~/.elan/bin` to `~/.profile` or the desktop entry | user |

Root-privilege steps (#2, #3) are handed to the user as instructions rather than
run by an agent.

## Part 4 — Acceptance criteria

The round closes when all four hold, each stated as a measurement:

1. `cd ScottDomains && lake build` exits 0 with zero errors; warning count and
   `sorry` count reported.
2. VS Code opens `ScottDomains/`, the Lean server reaches "ready", and the
   infoview shows the goal state for one theorem in an existing file.
3. `scripts/md2pdf.sh ScottDomains/docs/PaperInventory.md` exits 0 and the PDF
   renders 0 tofu boxes.
4. `scripts/md-pdf-header.tex` still renders correctly on macOS — verified by the
   user on a mac, or by inspection showing the macOS branch is byte-identical to
   the current header.

## Part 5 — Reporting

Each subagent writes its report to `ScottDomains/reports/` under this round ID.
The orchestrator then writes
`ScottDomains/reports/r0001-report-from-orchestrator-to-user-toolchain-audit.md`
consolidating the three, listing every command the user must run as root, and
recording the final measurements against Part 4.
