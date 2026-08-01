# ScottLean4

A Lean 4 workspace for Dana Scott's formalization work: writing definitions and
theorems in Lean 4 and having the Lean kernel machine-check the proofs. Claude
Code assists as a Lean 4 expert, under a terminology discipline imported from the
`ComputAItionalThinking` ruleset.

## Directory layout

| Path                          | What it is                                                                                     |
| ----------------------------- | ---------------------------------------------------------------------------------------------- |
| `CLAUDE.md`                   | Instructions Claude Code reads on start: a Turing-Award-logician / Lean 4 persona, and an import of the ruleset below. |
| `docs/ForDana.md`             | Setup and working advice for Dana — environment, VS Code, reading these files, and the goal view. **Start here.** |
| `lean-toolchain`              | Pins the Lean 4 version (`leanprover/lean4:v4.32.2`). The VS Code extension reads this and installs the matching toolchain. |
| `lakefile.toml`               | The Lake build configuration; declares the `ScottLean` library. |
| `ScottLean.lean`              | Root module — imports every module in the library. |
| `ScottLean/Basic.lean`        | First module: a few kernel-checked starter theorems to open in the goal view. |
| `ComputAItionalThinking/`     | A cloned repository holding the agent ruleset and computer-science glossaries. See its own `README.md`. |
| `.claude/settings.local.json` | Per-user permission settings for Claude Code (file read/write under `~/projects`, git, web search). |

Build the library from the project root with `lake build`.

## Getting started

Read [`docs/ForDana.md`](docs/ForDana.md) first — it covers installing the Lean 4
toolchain in VS Code, opening the goal view, and reading the Markdown files in
this project.

## The imported ruleset

`CLAUDE.md` imports `ComputAItionalThinking/ComputAItionalThinkingRules.md`, which
asks the agent to speak in precise computer-science terms and avoid analogies and
metaphors, and points at large glossaries the agent greps on demand. Read
`ComputAItionalThinking/README.md` for how that repository is organized.

## Terminology

Here **verified** means **formally verified** — the Lean kernel accepted a proof
of a stated specification. A successful `lake build` or a passing test is
**"built and tested,"** never "verified." Keep the two distinct when reporting
what a session established.
