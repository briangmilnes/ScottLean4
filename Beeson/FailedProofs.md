# Beeson development — failed / abandoned proof paths

Source: `Beeson/*.lean` — Michael Beeson's **Lean 3** development of intuitionistic
NF set theory (`inf*`), Church numbers (`ChurchNumbers*`), and Dedekind-finiteness
(`Dedekind*`), plus two metaprogramming support files (`mario`, `barton`).

**These are Lean 3 files and are analyzed as source text only** — they do not
compile under the Lean 4 toolchain in this repo and were not compiled.

Scope measured: **51** `.lean` files, **84,492** total lines.

## Summary (measurements)

| Quantity | Count |
| --- | --- |
| Executable `sorry` (real proof holes) | **2** (both in `inf29.lean`, lines 1661, 1667) |
| `sorry` tokens inside abandoned/commented blocks (not executed) | 4 (`inf16` ×1, `inf19` ×2, `inf29` ×1) |
| `admit` | **0** |
| `#exit` | **0** |
| Files with a commented-out abandoned proof block (≥3 tactic lines in `/- … -/`) | 3 (`inf16`, `inf19`, `inf29`) |
| Files judged **superseded / abandoned** | **7** (`inf19`, `inf20`, `inf21`, `inf29`, `ChurchNumbers11`, `barton`, `stratify`) |
| Files judged **live** (in the canonical dependency closure) | 44 |

**Key structural finding.** The numbered families are **not** independent redo
attempts. Every `infN` file begins `import inf(N-1)` and every `ChurchNumbersN`
begins `import ChurchNumbers(N-1)`; the development is one **additive import DAG**,
not a pile of parallel rewrites. Consequently "superseded" here means a file that
is **not reachable from the apex file `inf32.lean`** (a dead side-branch leaf or an
unused support file), while every reachable earlier file is a **live dependency**,
not a discarded draft.

## How "canonical vs superseded" was determined (evidence)

Method: parse every `import` line, build the module DAG, compute in-degree (how
many files import each module), identify leaves (in-degree 0), and compute the
transitive dependency closure of the newest leaf.

- **Apex / canonical = `inf32.lean`** — newest mtime (2025-12-02), in-degree 0
  (imported by nobody), and it pulls in the longest chain: it imports `inf31`
  **and** `ChurchNumbers12`, tying the two families together. Its header even
  documents the choice: `-- but not inf29 which has sorry`.
- Transitive closure of `inf32` = **44** files. These are all live: each is
  imported (directly or transitively) by the apex and must type-check for it to
  build.
- **7 files fall outside that closure** — the abandoned set:
  - `inf19` — leaf (in-degree 0), off `inf18`; contains a `/- … -/` block labeled
    *"this lemma uses sorry and is not used"* (lemma `expquad2`, 2 commented `sorry`).
  - `inf20 → inf21` — a dead branch off `inf18`; `inf21` is a leaf, `inf20` only
    feeds `inf21`, and neither is reached by `inf32`.
  - `inf29` — leaf off `inf28`; the **only file with executable `sorry`** (lemmas
    `notnotusc`, `uscseparable`, both `begin sorry, end` stubs). Beeson explicitly
    disowns it: `inf30`, `inf31`, and `inf32` each carry `-- but not inf29 which has sorry`.
  - `ChurchNumbers11` — leaf off `ChurchNumbers10`; `inf32` reaches Church numbers
    via `ChurchNumbers12` instead, so `ChurchNumbers11` is the dropped fork.
  - `barton` — Lean 3 metaprogramming, a variant of `mario` (defines
    `#axioms_all2` vs `mario`'s `#axioms_all`); in-degree 0, imported by nobody.
  - `stratify` — 2-line stub (`import tactic`), in-degree 0.

## Per-file table

`#sorry` counts **executable** holes only (a `sorry` inside a `/- … -/` block or a
`--` comment is not counted here; see the Summary for those). `cmt-proof?` = the
file contains a `/- … -/` block holding an abandoned tactic proof (≥3 tactic lines).

| file | lines | #sorry | #admit | cmt-proof? | role |
| --- | ---: | ---: | ---: | --- | --- |
| `inf.lean` | 4430 | 0 | 0 | no | support (live dep) — root of the `inf` family (`import tactic.basic`, `import mario`) |
| `inf1.lean` | 1875 | 0 | 0 | no | support (live dep) |
| `inf2.lean` | 1092 | 0 | 0 | no | support (live dep) |
| `inf3.lean` | 2825 | 0 | 0 | no | support (live dep) |
| `inf4.lean` | 1310 | 0 | 0 | no | support (live dep) |
| `inf5.lean` | 2769 | 0 | 0 | no | support (live dep) |
| `inf6.lean` | 2291 | 0 | 0 | no | support (live dep) — also `import IntuitionisticLogic` |
| `inf7.lean` | 1072 | 0 | 0 | no | support (live dep) |
| `inf8.lean` | 2147 | 0 | 0 | no | support (live dep) |
| `inf9.lean` | 3253 | 0 | 0 | no | support (live dep) |
| `inf10.lean` | 3502 | 0 | 0 | no | support (live dep) |
| `inf11.lean` | 2447 | 0 | 0 | no | support (live dep) |
| `inf12.lean` | 682 | 0 | 0 | no | support (live dep) |
| `inf13.lean` | 1468 | 0 | 0 | no | support (live dep) |
| `inf14.lean` | 941 | 0 | 0 | no | support (live dep) |
| `inf15.lean` | 2549 | 0 | 0 | no | support (live dep) |
| `inf16.lean` | 1587 | 0 | 0 | **yes** | support (live dep) — 53-tactic-line commented-out proof of `similar` ending in `sorry` |
| `inf17.lean` | 1538 | 0 | 0 | no | support (live dep) — junction: imported by `inf18` and by `ChurchNumbers` |
| `inf18.lean` | 2131 | 0 | 0 | no | support (live dep) — branch point (imported by `inf19`, `inf20`, `inf22`) |
| `inf19.lean` | 295 | 0 | 0 | **yes** | **superseded (abandoned)** — leaf; block noted *"this lemma uses sorry and is not used"* (2 commented `sorry`) |
| `inf20.lean` | 1129 | 0 | 0 | no | **superseded (abandoned)** — dead branch off `inf18`, only feeds `inf21` |
| `inf21.lean` | 821 | 0 | 0 | no | **superseded (abandoned)** — leaf, not reached by `inf32` |
| `inf22.lean` | 1478 | 0 | 0 | no | support (live dep) |
| `inf23.lean` | 1672 | 0 | 0 | no | support (live dep) — also `import Dedekind2` |
| `inf24.lean` | 3151 | 0 | 0 | no | support (live dep) |
| `inf25.lean` | 1092 | 0 | 0 | no | support (live dep) |
| `inf26.lean` | 730 | 0 | 0 | no | support (live dep) |
| `inf27.lean` | 2922 | 0 | 0 | no | support (live dep) |
| `inf28.lean` | 2355 | 0 | 0 | no | support (live dep) — branch point (imported by `inf29`, `inf30`) |
| `inf29.lean` | 2017 | **2** | 0 | **yes** | **superseded (abandoned)** — leaf; 2 executable `sorry` (lines 1661, 1667); disowned by `inf30/31/32` |
| `inf30.lean` | 2294 | 0 | 0 | no | support (live dep) |
| `inf31.lean` | 1318 | 0 | 0 | no | support (live dep) |
| `inf32.lean` | 1072 | 0 | 0 | no | **canonical (apex)** — newest (2025-12-02); `import inf31 ChurchNumbers12` |
| `ChurchNumbers.lean` | 2246 | 0 | 0 | no | support (live dep) — newest CN file (2025-12-02); `import inf17`; foundational (feeds `Dedekind`) |
| `ChurchNumbers2.lean` | 3280 | 0 | 0 | no | support (live dep) — `import Dedekind2` |
| `ChurchNumbers3.lean` | 1868 | 0 | 0 | no | support (live dep) |
| `ChurchNumbers4.lean` | 1008 | 0 | 0 | no | support (live dep) |
| `ChurchNumbers5.lean` | 1554 | 0 | 0 | no | support (live dep) |
| `ChurchNumbers6.lean` | 1200 | 0 | 0 | no | support (live dep) |
| `ChurchNumbers7.lean` | 926 | 0 | 0 | no | support (live dep) |
| `ChurchNumbers8.lean` | 1783 | 0 | 0 | no | support (live dep) |
| `ChurchNumbers9.lean` | 922 | 0 | 0 | no | support (live dep) |
| `ChurchNumbers10.lean` | 2917 | 0 | 0 | no | support (live dep) — imported by `ChurchNumbers11` and `ChurchNumbers12` |
| `ChurchNumbers11.lean` | 1572 | 0 | 0 | no | **superseded (abandoned)** — leaf off CN10; `inf32` uses CN12 instead |
| `ChurchNumbers12.lean` | 207 | 0 | 0 | no | support (live dep) — reached by the apex `inf32` |
| `Dedekind.lean` | 1241 | 0 | 0 | no | support (live dep) — `import ChurchNumbers` |
| `Dedekind2.lean` | 1013 | 0 | 0 | no | support (live dep) — `import Dedekind`; imported by `ChurchNumbers2` and `inf23` |
| `IntuitionisticLogic.lean` | 471 | 0 | 0 | no | support (live dep) — 30 propositional/intuitionistic `Prop` lemmas; `import mario` (only for `#axioms_all`) |
| `mario.lean` | 61 | 0 | 0 | no | support (tooling) — Lean 3 `meta`/`user_command` `#axioms_all`; imported by `inf`, `IntuitionisticLogic` |
| `barton.lean` | 17 | 0 | 0 | no | **superseded (tooling, unused)** — variant of `mario` (`#axioms_all2`); in-degree 0 |
| `stratify.lean` | 2 | 0 | 0 | no | **superseded (stub)** — `import tactic` only; in-degree 0 |

## Per-family narrative

### `inf` family — one additive chain with three dead branches

`inf → inf1 → … → inf17 → inf18`, then `inf18` forks three ways:

- `inf18 → inf19` — **dead leaf** (the `expquad2` block noted "uses sorry and is not used").
- `inf18 → inf20 → inf21` — **dead branch** (leaf `inf21`).
- `inf18 → inf22 → inf23 → … → inf28`, then `inf28` forks:
  - `inf28 → inf29` — **dead leaf** (2 executable `sorry`, explicitly disowned).
  - `inf28 → inf30 → inf31 → inf32` — **the live spine ending at the apex.**

So the canonical `inf` file is **`inf32`** (2025-12-02). Its dependency closure is
sorry-free: the only executable holes in the whole development live in `inf29`,
which is off the live path and which Beeson annotated out.

### `ChurchNumbers` family — a 2021 chain re-touched in 2025, plus a fresh root

The numbered chain `ChurchNumbers2 → 3 → … → 10 → {11, 12}` was built mostly in
2021 (`CN4–CN8` dated Jul 2021 / Aug 2023) and partly re-edited in Nov 2025
(`CN3`, `CN9`, `CN10`). `ChurchNumbers11` is the **dropped fork** (leaf); the apex
reaches Church numbers through `ChurchNumbers12`. Separately, the unnumbered
`ChurchNumbers.lean` (2025-12-02, `import inf17`) is **not** a superseding rewrite:
it is a *foundational* file feeding `Dedekind → Dedekind2 → ChurchNumbers2`, i.e.
it sits underneath the numbered chain, not above it.

### `Dedekind` family — 2 files, both live

`Dedekind2 → Dedekind → ChurchNumbers`. Both are in the apex closure; `Dedekind2`
is a junction imported by both `ChurchNumbers2` and `inf23`.

### Metaprogramming support — `mario`, `barton`, `stratify`

`mario.lean` is the live tooling file (defines the `#axioms_all` diagnostic
command, imported by `inf` and `IntuitionisticLogic`). `barton.lean` is a near-copy
defining `#axioms_all2`, imported by nobody — **superseded tooling**.
`stratify.lean` is a 2-line stub — **abandoned**.

### `IntuitionisticLogic` — clean

30 propositional/intuitionistic `Prop` lemmas (Heyting, Kleene, double-negation
translation results). No `sorry`, no `admit`, no abandoned block; the source's own
`#axioms_all -- this file is clean`. This is the file chosen for the Deliverable B
pilot port (see `Beeson/lean4/`).
