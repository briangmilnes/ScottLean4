---
round: r0002
from: orchestrator
to: orchestrator
subject: session-restart
date: 2026-0806-13:10
status: pending
related:
  - plans/r0001-plan-from-orchestrator-to-orchestrator-toolchain-audit.md
  - reports/r0001-report-from-orchestrator-to-user-toolchain-audit.md
---

# r0002 — Session restart

State handoff so a fresh agent resumes without re-deriving r0001. Read
`ScottDomains/reports/r0001-report-from-orchestrator-to-user-toolchain-audit.md`
first; this file records only what that report does not — branch state, what is
in flight, and what remains undecided.

## Where things stand

Branch `main`, working tree committed as of 2026-0806-13:10. Round r0001 is
closed: the Linux host builds `ScottDomains` against Mathlib, VS Code drives
interactive proofs, and `scripts/md2pdf.sh` renders Markdown to PDF at 0 tofu
while leaving the macOS rendering byte-identical.

No work is in flight. The three r0001 subagents have all reported and exited.

## Environment facts a fresh agent should not re-measure

| # | Fact | Value |
| -- | ---- | ----- |
| 1 | Lean toolchain | 4.32.2, commit `f3b06c7`, via elan 4.2.3; both `lean-toolchain` files pin it |
| 2 | Mathlib | rev `905b9581` (`v4.32.2`), 9 deps pinned in `lake-manifest.json` |
| 3 | Build | `cd ScottDomains && lake build` → 3 jobs, 0 errors, 0 warnings, 0 `sorry`, ~2 s |
| 4 | Olean cache | `~/.cache/mathlib`, 874 MiB, shared host-wide across projects |
| 5 | Disk | volume at 97%, 15 GiB free; `ScottDomains/.lake` is 7.4 GiB |
| 6 | VS Code | 1.130.0, `leanprover.lean4@0.0.239` (marketplace latest), Live Share installed but not signed in |
| 7 | PDF | pandoc 3.9.0.2 + lualatex 1.17.0; zsh 5.9; STIX Two from `texlive-fonts-extra` in the texmf tree |
| 8 | Font instrument | `kpsewhich`, not `fc-list` — fontconfig does not index the texmf tree |

## Resume steps

1. `cd /home/milnes/projects/ScottLean4 && git status --short` — expect empty.
   This repo is written from two machines, so `git pull --rebase` first.
2. `cd ScottDomains && lake build` — expect `Build completed successfully (3 jobs).`
   If it wants to rebuild Mathlib, the toolchain or the pin moved; check
   `lean-toolchain` against `lake-manifest.json` before letting it run.
3. `scripts/md2pdf.sh ScottDomains/docs/PaperInventory.md /tmp` — expect exit 0,
   4 pages. This is the fastest check that the font path is still intact.
4. Open `ScottDomains/` as its own VS Code folder, not the repo root.

## Open decisions

| # | Decision | Context |
| -- | -------- | ------- |
| 1 | Whether to build `Playground/` or `Beeson/lean4/` on this host | Each adds ~7 GiB to a volume with 15 GiB free. Two would exhaust it |
| 2 | Whether to render one Markdown file on a mac | r0001 criterion 4 is proved by construction; a real render is cheap insurance before the next PDF goes to Dana |
| 3 | Live Share sign-in | Deferred by the user. `docs/Curriculum.md` names it as how tutoring sessions pair on Lean |
| 4 | Whether `md2pdf.sh` should become interpreter-neutral | Currently `#!/bin/zsh` with zsh-only `${0:A:h}`; zsh is installed here so nothing is broken. Rewriting for bash edits a file both macs execute |

## Next substantive work

r0001 was infrastructure; none of it advanced the mathematics. The domain-theory
development itself is 2 source files and 59 lines, of which
`ScottDomains/ExistingTheories.lean` is a `#check` catalog of the 8 Mathlib
declarations being reused (`OmegaCompletePartialOrder`, `CompletePartialOrder`,
`ScottContinuous`, `ScottContinuousOn`, `Topology.IsScott`,
`Topology.IsScottHausdorff`, `OrderHom.lfp`, `OrderHom.gfp`).

`ScottDomains/docs/PaperInventory.md` states the work remaining as roughly 13
definitions to write, 28 theorems to prove, and 12 results reusable from
Mathlib. That inventory, not the toolchain, is where the next round starts.
