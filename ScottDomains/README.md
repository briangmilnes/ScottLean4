# ScottDomains — moved

The Lean package that was here now lives in **Dana Scott's own repository**:

- on disk: `~/projects/ScottProjects/ScottDomains`
- on GitHub: <https://github.com/DanaSScott/ScottProjects/tree/main/ScottDomains>

145 modules, 52,261 lines, `lake build` completing 1560 jobs with zero errors —
including the 18-module `EquilogicalSpaces/` formalization of §3 of Bauer,
Birkedal and Scott, *Equilogical Spaces*, TCS **315**(1):35–59, 2004.

The move was mechanical rather than a refactor. Measured with
`scripts/import-closure.sh`, the library's only external dependency is Mathlib,
and no Lean file outside the package imports it, so not one `import` line
changed and the pinned Mathlib revision is identical in both repositories.

## What stayed here, and why

This directory is now the **process record** for that work — ScottLean4's
history, not the library's:

| directory | files | what it is |
| --------- | ----- | ---------- |
| `logs/` | 707 | GRASE build telemetry, per `standards/LoggingStandard.md` |
| `prompts/` | 334 | reconstructed user↔assistant interactions, `scripts/save-prompts.sh` |
| `reports/` | 122 | GRASE execution reports |
| `plans/` | 78 | GRASE plans |
| `analyses/` | 37 | analytical data-products about the codebase |
| `GunterScott90Images/` | 41 | figures extracted from Gunter–Scott 1990 |
| `papers/` | 11 | the cited sources |

`papers/` stayed for a specific reason: those are third-party copyrighted PDFs,
and they are `.gitignore`d in `ScottProjects` rather than republished there, so
this repository remains their only tracked copy. The module docstrings in the
moved library still name them by the package-relative path
`ScottDomains/papers/…`, which resolves against *this* directory.

`docs/` did move, so `docs/Performance.md` — the measured build costs — is now
at `~/projects/ScottProjects/ScottDomains/docs/Performance.md`.

## Building it

```
cd ~/projects/ScottProjects/ScottDomains && lake build
```

`scripts/compile.sh` in this repository was repointed at the new location, and
writes its logs to `~/projects/ScottProjects/ScottDomains/logs/` — beside the
package it measures, tracked in that repository. The 707 logs here are the
historical record of the runs made while the package still lived in this
repository; no new ones are written to them.
