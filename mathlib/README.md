# Mathlib — read-only source snapshot

This directory is a **source-only snapshot of Mathlib**, vendored here so it can
be read directly (e.g. the `Mathlib/CategoryTheory/` development) without digging
into a build directory. It is **reference only** — the Lean build does *not* use
these files.

- **Version:** `v4.32.2` (upstream commit `905b95818e`)
- **Upstream:** https://github.com/leanprover-community/mathlib4
- **License:** Apache License 2.0 — see [`LICENSE`](LICENSE). Redistribution is
  permitted under that license; this snapshot preserves it unmodified.
- **Contents:** the `Mathlib/` `.lean` source tree only. No `.git` history and no
  compiled `.olean` build artifacts (those live under `Beeson/lean4/.lake/` when
  the project is actually built).
- **Size:** 8,264 `.lean` files, ~2.28 M lines.

## Where to start reading

| Topic | File |
|-------|------|
| Category (Quiver → CategoryStruct → Category) | `Mathlib/CategoryTheory/Category/Basic.lean` |
| Functors | `Mathlib/CategoryTheory/Functor/Basic.lean` |
| Natural transformations | `Mathlib/CategoryTheory/NatTrans.lean` |
| Cartesian closed (CCC) | `Mathlib/CategoryTheory/Monoidal/Closed/Cartesian.lean` |

Because this is pinned to `v4.32.2` — the same toolchain the project builds
against — line numbers here match what the Lean LSP / Infoview reports.

## Editing

Do **not** edit these files as if they were the build's Mathlib. To experiment,
write a scratch `.lean` under `Beeson/lean4/` with, e.g.,
`import Mathlib.CategoryTheory.Category.Basic`, and work there.

To refresh this snapshot to a newer Mathlib later, re-copy the `Mathlib/` tree and
`LICENSE` from `Beeson/lean4/.lake/packages/mathlib/` after bumping the toolchain.
