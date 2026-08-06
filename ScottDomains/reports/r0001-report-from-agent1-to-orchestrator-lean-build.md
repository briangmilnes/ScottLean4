---
round: r0001
from: agent1
to: orchestrator
subject: lean-build
date: 2026-0806-12:38
started: 2026-0806-12:28
finished: 2026-0806-12:38
related:
  - plans/r0001-plan-from-orchestrator-to-orchestrator-toolchain-audit.md
  - logs/lake-build.2026-0806-12:30.agent1.log
---

# r0001 — Subagent A1: Lean 4 / Mathlib build on this Linux host

Defect **D1** of the plan ("`ScottDomains` has no `.lake`, so Mathlib is neither
fetched nor cached here") is closed. `ScottDomains` now builds. Full lake output,
ANSI-stripped, is in `ScottDomains/logs/lake-build.2026-0806-12:30.agent1.log`.

## 1. Toolchain (task 1)

`elan show` reports two installed toolchains and one active:

| # | Field | Value |
| - | ----- | ----- |
| 1 | installed | `leanprover/lean4:v4.32.2` (resolved from default `stable`) |
| 2 | installed | `leanprover/lean4:v4.33.0-rc1` |
| 3 | active | `leanprover/lean4:v4.32.2`, overridden by `/home/milnes/projects/ScottLean4/lean-toolchain` |
| 4 | lean version | 4.32.2, `x86_64-unknown-linux-gnu`, commit `f3b06c705e6c85f5314019d5d3baab0fec5b580c`, Release |

v4.32.2 is installed and is the resolved default; the repo-root `lean-toolchain`
file also pins it explicitly, so the pin and the default agree. The second
toolchain (`v4.33.0-rc1`) exists because `~/projects/DifferentialGeometry` pins
it; it is not selected inside this repo.

## 2. Fetch and build (task 2)

Both commands exited 0. Wall-clock and byte counts:

| # | Command | Exit | Wall-clock | Bytes downloaded (olean cache) |
| - | ------- | ---- | ---------- | ------------------------------ |
| 1 | `lake exe cache get` | 0 | 192 s | **0** — `cache` reported `No files to download` |
| 2 | `lake build` | 0 | 2 s | — |
| 3 | `lake build ScottDomains.ExistingTheories` | 0 | 2 s | — |

The 192 s of command 1 decomposes into: `git clone` of the 9 pinned packages
(mathlib and 8 transitive dependencies), a 26-job build of the `cache`
executable itself, and 7,402 ms decompressing 8,638 already-cached `.ltar`
archives out of `~/.cache/mathlib`. The zero-byte download is not a property of
Mathlib — it is a property of *this host*: `~/projects/PFPL` had already
populated the shared olean cache at the identical Mathlib revision
`905b95818eb32af7874a58b427f50c1711a5e96c`. See section 5.

No failures, so there is no error text to quote.

## 3. Build outcome as measurement (task 3)

| # | Metric | Count |
| - | ------ | ----- |
| 1 | Lake jobs in the dependency graph | 924 |
| 2 | Modules elaborated by `lake build` (default target) | 1 — `ScottDomains` |
| 3 | Modules elaborated by the explicit second invocation | 1 — `ScottDomains.ExistingTheories` |
| 4 | Modules retrieved pre-built from the olean cache | 922 |
| 5 | Lean **errors** | 0 |
| 6 | Lean **warnings** | 0 |
| 7 | Lean `info` messages | 8 (the eight `#check` outputs in `ExistingTheories.lean`) |
| 8 | `sorry` occurrences across `ScottDomains/**/*.lean` | **0** |
| 9 | Source `.lean` files (excluding `.lake/`) | 2 |
| 10 | Source lines | 59 (`ScottDomains.lean` 31, `ScottDomains/ExistingTheories.lean` 28) |
| 11 | Artifacts produced | `ScottDomains.olean`, `ScottDomains.ilean`, `ScottDomains/ExistingTheories.olean`, `.ilean` |

The `sorry` count is 0 by direct measurement: `grep -rn '\bsorry\b'` over the two
source files returns no lines at all, so no comment-vs-code disambiguation was
needed. With 59 source lines and 0 proof obligations outstanding, the library is
currently a re-export surface, not yet a development — `ScottDomains.lean` is
five `import` lines plus commentary, and `ExistingTheories.lean` is eight
`#check`s used as a clickable index into Mathlib.

All eight `#check`s resolve against the pinned revision, which is the useful
result: every Mathlib name the project depends on
(`OmegaCompletePartialOrder`, `CompletePartialOrder`, `ScottContinuous`,
`ScottContinuousOn`, `Topology.IsScott`, `Topology.IsScottHausdorff`,
`OrderHom.lfp`, `OrderHom.gfp`) exists at `905b9581` with the signatures the file
expects. The elaborated signatures are recorded verbatim in the log.

### Defect found: one of two source modules is outside the default target

`lakefile.toml` sets `defaultTargets = ["ScottDomains"]` and declares
`[[lean_lib]] name = "ScottDomains"` with no `globs` field, so the library root
is the single module `ScottDomains`. `ScottDomains.lean` does not import
`ScottDomains.ExistingTheories`, and nothing else does. Consequently plain
`lake build` elaborates 1 of the 2 source files; `ExistingTheories.lean` is
built only when named explicitly, as in row 3 above.

This is a live risk rather than a present failure: today the unbuilt file
compiles, but a Mathlib bump that renames any of those eight declarations would
leave `lake build` exiting 0 while the file is broken. The one-line correction,
**proposed and not applied** (it edits a tracked file and is outside A1's
read-mostly scope):

```toml
[[lean_lib]]
name = "ScottDomains"
globs = ["ScottDomains.+"]
```

`ScottDomains.+` denotes the root module together with all its submodules, so
every file under `ScottDomains/` enters the default target. Acceptance criterion
1 of the plan ("`lake build` exits 0 with zero errors") is met as written, but it
only covers half the source until this is changed.

## 4. Repo-root `mathlib/` versus the Lake-fetched Mathlib (task 4)

**The root copy is not on any import path, and it is an exact duplicate of the
source half of the fetched package.** Nothing was deleted or modified.

| # | Tree | Apparent bytes | On disk | `.lean` files | Oleans |
| - | ---- | -------------- | ------- | ------------- | ------ |
| 1 | `mathlib/` (repo root, tracked in git) | 96,145,295 | 113 MiB | 8,264 | 0 |
| 2 | `ScottDomains/.lake/packages/mathlib/` (whole package) | — | 7.0 GiB | — | 8,275 |
| 3 | `ScottDomains/.lake/packages/mathlib/Mathlib/` (source subtree only) | — | 113 MiB | 8,264 | — |
| 4 | `ScottDomains/.lake/` (all 9 packages plus build output) | 7,505,995,442 | 7.4 GiB | — | — |

Evidence that row 1 duplicates row 3: `diff -rq mathlib/Mathlib
ScottDomains/.lake/packages/mathlib/Mathlib` exits 0 with zero differing
entries — 8,264 files, byte-identical. `LICENSE` is identical too; only
`README.md` differs, because the root copy carries a hand-written snapshot note
instead of the upstream mathlib4 README. That note states the intent explicitly:
"source-only snapshot of Mathlib, vendored here so it can be read directly …
reference only — the Lean build does *not* use these files. Version: `v4.32.2`
(upstream commit `905b95818e`)." The commit it names is the revision Lake
actually resolved, so the reading copy and the built copy are the same Mathlib.

Evidence that row 1 is not on any import path:

1. No `[[require]]` anywhere in the repo points at a local path; the three
   Mathlib-using lakefiles (`ScottDomains/`, `Playground/`, `Beeson/lean4/`) all
   require the git URL `https://github.com/leanprover-community/mathlib4` at
   `rev = "v4.32.2"`.
2. `mathlib/` has no `lakefile.toml`, no `lakefile.lean`, no `lean-toolchain`,
   and no `.lake/` — it is not a package Lake could resolve.
3. It contains 0 `.olean` files, so nothing could import from it even if it were
   on `LEAN_PATH`.
4. `LEAN_PATH` is unset in the environment; Lake constructs it from the manifest.
5. Module resolution would look for `Mathlib.X` at `<searchRoot>/Mathlib/X.lean`.
   The files here live at `<repo>/mathlib/Mathlib/X.lean`, one directory deeper,
   and `<repo>/Mathlib` does not exist. No search root makes them reachable.

Disk-cost note: the duplication costs 113 MiB of the 7.4 GiB total, i.e. 1.5%.
The tracked copy is the cheap part; the 7.0 GiB package is the expensive part and
is git-ignored (`.gitignore:17` matches `ScottDomains/.lake`, confirmed with
`git check-ignore -v`). Removing the root snapshot would save 113 MiB and lose
Dana Scott's direct-reading path, so the measurement argues for keeping it.

Free space is now 15 GiB with the filesystem at 97% used, down from 23 GiB
before this round. That is the constraint worth flagging: `Playground/` and
`Beeson/lean4/` pin the same Mathlib revision and have not been built here.
Building either adds roughly another 7 GiB unless the packages directory is
shared, because Lake keeps a per-project `.lake/packages` tree. Two more such
builds would exhaust the volume.

## 5. `~/.cache/mathlib` and cross-project sharing (task 5)

| # | Metric | Value |
| - | ------ | ----- |
| 1 | Size | 879,889,363 bytes (874 MiB) |
| 2 | Entries | 17,282 `.ltar` archives, flat, no subdirectories |
| 3 | Archives consumed by this fetch | 8,638 |
| 4 | Archives downloaded by this fetch | 0 |

**The cache is shared host-wide across every Lean project of this user**, and
that sharing is what made this round cheap. The path `~/.cache/mathlib` is
per-user, not per-project; `cache get` keys entries by the hash of a module's
transitive input, so any project pinning the same Mathlib revision reads the same
archives. Two other projects on this host already use it:

| # | Project | `lean-toolchain` | Mathlib `HEAD` | `.lake/packages/mathlib` |
| - | ------- | ---------------- | -------------- | ------------------------ |
| 1 | `~/projects/PFPL` | `v4.32.2` | `905b95818e` | 7.0 GiB |
| 2 | `~/projects/DifferentialGeometry` | `v4.33.0-rc1` | `79d0395a18` | 7.1 GiB |

`PFPL` pins byte-for-byte the revision `ScottDomains` resolves to, which is why
`cache get` reported `No files to download`. The 17,282 archives span at least
these two revisions; 8,638 of them served this build.

The 874 MiB cache is not duplicated per project — only the decompressed 7.0 GiB
package tree is. So the storage model is: one shared compressed cache, plus one
7 GiB decompressed tree per project that builds against Mathlib.

## 6. Reproducibility and fresh-host bootstrap (task 6)

**The one-command bootstrap is:**

```sh
cd /home/milnes/projects/ScottLean4/ScottDomains && lake exe cache get && lake build
```

This is exactly row 1 of Part 3 of the plan; it is confirmed correct, requires no
root privilege, and needs no preparatory step beyond `elan` having v4.32.2
(which `lean-toolchain` will install on demand).

**`lake build` is reproducible from a clean `.lake`, and this run is the
evidence.** Baseline item 4 of the plan recorded `ScottDomains/.lake` as absent;
the two commands above ran against that empty state and reached exit 0. The run
just performed *was* the clean-`.lake` reproduction, so no second wipe-and-retry
was needed — which also avoided re-spending 7.4 GiB on a volume at 97%.

Determinism rests on `ScottDomains/lake-manifest.json`, which pins all 9 packages
to exact commit SHAs (mathlib `905b9581`, plus `plausible`, `LeanSearchClient`,
`importGraph`, `proofwidgets`, `aesop`, `batteries`, `Qq`, `Cli`). Lake resolves
those SHAs rather than the symbolic `inputRev`, so a rebuild fetches identical
sources. Two external preconditions remain and are not under the repo's control:
reachability of `github.com` for the 9 clones, and reachability of the
leanprover-community olean cache endpoint when `~/.cache/mathlib` is cold.

**Cost on a genuinely fresh host** (empty `~/.cache/mathlib`) will be higher than
the 192 s measured here. The olean download would be roughly 440 MB — an
estimate, not a measurement, obtained as 8,638 archives × the 50,914-byte mean
archive size in the present 874 MiB / 17,282-file cache. Wall-clock would be that
transfer plus the ~192 s of clone, `cache` build, and decompression. The
alternative of building Mathlib from source is the 1–3 CPU-hour path the plan
estimated and is not needed.

## Status against Part 4 acceptance criterion 1

Criterion 1 — "`cd ScottDomains && lake build` exits 0 with zero errors; warning
count and `sorry` count reported" — is **met**: exit 0, 0 errors, 0 warnings,
0 `sorry`. The qualification in section 3 stands: as `lakefile.toml` is written
today, that command covers 1 of the 2 source modules, and the second was built
separately, also with 0 errors and 0 warnings.

Criteria 2 (VS Code infoview) and 3–4 (PDF pipeline) are outside A1's scope and
belong to A2 and A3.
