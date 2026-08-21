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

### One paper in `papers/` is two chapters, not one

`Gunter Mosses Scott 1989 … MS-CIS-89-16.pdf` reads from its filename like a
three-author paper. It is not. The Penn tech report (LOGIC & COMPUTATION 04,
dated February 14, 1989, marked *"To appear in North Holland's Handbook of
Theoretical Computer Science"*) binds together the preprints of **two** Handbook
chapters:

| # | pages | chapter | authors | published as |
| - | ----- | ------- | ------- | ------------ |
| 1 | 1–46 | Semantic Domains | Gunter & Scott | HTCS Vol. B (1990), pp. 633–674 — held as `papers/Gunter Scott 1990.pdf` |
| 2 | 47– | Denotational Semantics | Mosses | its own HTCS chapter |

So Mosses authored the half that has nothing to do with the chapter this
development formalizes, which is why `scripts/bibliography-cites.sh` reports him
cited by zero modules and zero documents while "Gunter" appears in 101 of 145
modules. That zero is correct, not a missing citation.

Chapter 1 and the published chapter are the same seven sections with the chapter
prefix dropped, subsection titles matching one for one, so a citation converts by
deleting the `1.`:

    report §1.2.3  =  published §2.3        report §1.3.1  =  published §3.1
    report §1.6.2  =  published §6.2        report §1.7.4  =  published §7.4

The module docstrings cite the **published** numbering. The report is therefore
usable as an independent witness to a printed sentence thirteen months earlier —
worth reaching for where a printed statement is under suspicion, as with the
results this development had to name `…_printed_false`. Whether the preprint's
proofs differ from the published ones has not been checked; only the titles and
tables of contents were compared.

## Building it

```
cd ~/projects/ScottProjects/ScottDomains && lake build
```

`scripts/compile.sh` in this repository was repointed at the new location, and
writes its logs to `~/projects/ScottProjects/ScottDomains/logs/` — beside the
package it measures, tracked in that repository. The 707 logs here are the
historical record of the runs made while the package still lived in this
repository; no new ones are written to them.
