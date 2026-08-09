---
round: r0048
from: agent1
to: orchestrator
subject: result-2
date: 2026-0809-14:02
started: 2026-0809-13:47
finished: 2026-0809-14:02
related:
  - plans/r0048-plan-from-orchestrator-to-orchestrator-find-two-and-fifteen.md
  - ScottDomains/A1Theorem2.lean
---

# r0048, result 2 — outcome 1: it exists, it was absent, it is now proved

## 1. Headline

| # | Measurement | Value |
| -- | ----------- | ----- |
| 1 | outcome | **1** — the result exists in the paper and was not in the tree |
| 2 | heading word the paper uses | **Theorem** (not Proposition, not Corollary) |
| 3 | printed folio / physical PDF page | **6 / 7**; proof continues on **7 / 8** |
| 4 | declarations added | 10 in `ScottDomains/A1Theorem2.lean` |
| 5 | `sorry` added | **0** — package total unchanged at 0 |
| 6 | build | zero errors, zero warnings, 1365 jobs, wall 5.05 s |
| 7 | axiom footprint of `theorem2` | `[propext, Classical.choice, Quot.sound]` |
| 8 | paper's numbered-result count, re-derived | **30, contiguous 1–30** — the figure was right |

## 2. What the printed page says

Physical PDF page 7 of `papers/Gunter Scott 1990.pdf`, printed folio 6, read from
a 600 dpi `pdftoppm` rendering. The paper prints "Schroder-Bernstein" without the
umlaut.

> *The Schroder-Bernstein Theorem.* As a set-theoretic application of the Fixed
> Point Theorem we offer the proof of the following:
>
> **Theorem 2 (Schroder-Bernstein)** *Let `S` and `T` be sets. If `f : S → T` and
> `g : T → S` are injections, then there is a bijection `h : S → T`.*

The proof, which is what makes this a distinct result rather than a citation,
runs from folio 6 onto folio 7 (physical page 8):

> **Proof:** The function `Y ↦ (T − f*(S)) ∪ f*(g*(Y))` from `P T` to `P T` is
> easily seen to be continuous with respect to the inclusion ordering. Hence, by
> the Fixed Point Theorem, there is a subset `Y = (T − f*(S)) ∪ f*(g*(Y))`. In
> particular, `T − Y = f*(S − g*(Y))` since
> `T − Y = T − ((T − f*(S)) ∪ f*(g*(Y))) = (T − (T − f*(S))) ∩ (T − (f*(g*(Y)))) = f*(S) ∩ (T − (f*(g*(Y)))) = f*(S − g*(Y))`.
> Now define `h : S → T` by `h(x) = y` if `x = g(y)` for some `y ∈ Y`, and
> `h(x) = f(x)` otherwise. This makes sense because `g` is an injection.
> Moreover, `h` itself is an injection since `f` and `g` are injections. To see
> that it is a surjection, suppose `y ∈ T`. If `y ∈ Y`, then `h(g(y)) = y`. If
> `y ∉ Y`, then `y ∈ f*(S − g*(Y))`, so `y = f(x) = h(x)` for some `x`. Thus `h`
> is a bijection.

No printed defect found. The four-step set computation is correct as printed, and
each step reproduces in Lean without amendment.

## 3. Why outcome 2 does not hold

The orchestrator's mid-task correction — result 15 turned out to be
**Proposition 15**, invisible to instruments that grep only `thm|theorem|lem|lemma`
— does not transfer. Result 2 is headed **Theorem**, confirmed from the rendered
page, so no heading-word blind spot is in play here.

Absence from the tree was then checked under any name, not only numbered ones:

| # | Search | Hits in `ScottDomains/ScottDomains/` before this round |
| -- | ----- | ----: |
| 1 | `prop2`, `cor2`, `Prop2`, `Cor2` | 0 |
| 2 | `Proposition 2`, `Corollary 2` (exact) | 0 |
| 3 | `Schr`, `schroeder`, `Bernstein` | **1** — a docstring line, no declaration |
| 4 | `Function.Bijective` | 0 |

Row 3 is `Kleene/Extension.lean:18`, which says `f*` "is the operator the paper's
own proof of Theorem 2 (Schröder–Bernstein) is written in". The operator was
built there in an earlier round and never used. Nothing stated the theorem.

**`PaperInventory.md` row 2.2 is a mapping, not a discharge.** It records Theorem 2
as covered by Mathlib's `Function.Embedding.schroeder_bernstein`. That lemma is
Zermelo's transfinite argument, proved from `OrderHom.lfp` — Knaster–Tarski over a
complete lattice. Gunter & Scott derive Theorem 2 from **Theorem 1**, the Kleene
fixed-point theorem for a *cpo* and a *continuous* map, and `FixedPoint.lean`'s
own docstring already records that neither of those two fixed-point theorems
implies the other. So the paper's Theorem 2 is a distinct result-with-proof and
the Mathlib citation does not stand in for it.

This also corrects r0043 agent1's sentence "every conjunct of Theorem 1, 2, 3,
Lemma 4, 5, Theorem 6 and Theorem 7 — all 15 — is stated and proved." Result 2's
`S+P` label was inherited from r0040 row 3, whose evidence column names a
**Mathlib** declaration. Every other row in that group names a declaration in this
package. Result 2 was the one row where "stated and proved" meant "stated and
proved somewhere else".

## 4. What was added

`ScottDomains/ScottDomains/A1Theorem2.lean`, namespace `ScottDomains.R48.Agent1`,
206 lines. It follows the paper's proof step for step and reuses what earlier
rounds built for exactly this purpose.

| # | Declaration | Role | Paper's sentence |
| -- | ---------- | ---- | ---------------- |
| 1 | `sbOp` | `def` | `Y ↦ (T − f*(S)) ∪ f*(g*(Y))` from `P T` to `P T` |
| 2 | `scottContinuous_sbOp` | thm | "easily seen to be continuous with respect to the inclusion ordering" |
| 3 | `sbFix` | `def` | "there is a subset `Y = (T − f*(S)) ∪ f*(g*(Y))`" |
| 4 | `isLeast_sbFix` | thm | Theorem 1 applied to `sbOp` |
| 5 | `sbOp_sbFix` | thm | the fixed-point equation itself |
| 6 | `mem_extension_iff` | thm | `x ∈ f*(X) ↔ ∃ …`, `Iff.rfl` |
| 7 | `sbFix_sdiff` | thm | **`T − Y = f*(S − g*(Y))`** — the paper's four-step computation |
| 8 | `sbBij` | `def` | `h(x) = y` if `x = g(y)` for some `y ∈ Y`, else `f(x)` |
| 9 | `sbBij_pos` / `sbBij_neg` | thm | the two branches of `h` |
| 10 | `apply_notMem_of_notMem` | thm | `x ∉ g*(Y)` ⟹ `f x ∉ Y`, the branch-disjointness step |
| 11 | **`theorem2`** | thm | **Theorem 2 itself** |

The statement, with no instance binder added:

```lean
theorem theorem2 (f : S → T) (g : T → S) (hf : Function.Injective f)
    (hg : Function.Injective g) : ∃ h : S → T, Function.Bijective h
```

Two sets ⇒ two types; two injections ⇒ two `Function.Injective` hypotheses; "there
is a bijection `h : S → T`" ⇒ `∃ h : S → T, Function.Bijective h`. Nothing else is
assumed.

**The `[Nonempty T]` trap was avoided deliberately.** The obvious way to write `h`
is `Function.invFun g` on the `x ∈ g*(Y)` branch, and `Function.invFun` carries
`[Nonempty T]`. Adding it would have been r0044's dominant defect mode — an added
instance binder is a weakening, not a transcription. `h` is instead defined by
`dite` on `∃ y, y ∈ Y ∧ g y = x`, taking the witness with `Exists.choose`, which
needs no nonemptiness at all.

### Where the work is

* Continuity (row 2) is three lines. `sbOp` is a constant union the composite
  `f* ∘ g*`, and `Kleene/Extension.lean` already proved `f*` Scott continuous from
  preservation of *arbitrary* unions, so directedness is never spent. This is the
  first consumer of `scottContinuous_extension`.
* Row 7 is the content. `f`'s injectivity is spent exactly once before `h` is
  built, in the paper's last step `f*(S) ∩ (T − f*(g*(Y))) = f*(S − g*(Y))`, which
  is `Set.image_sdiff`.
* `g`'s injectivity is spent exactly once, in surjectivity, to identify the
  witness chosen at `g y` with `y`.
* The paper's "`h` itself is an injection since `f` and `g` are injections" hides
  a mixed case it does not mention: `x₁ ∈ g*(Y)` and `x₂ ∉ g*(Y)`. That case is
  closed by row 10 — the two branches land in `Y` and in `T − Y` respectively —
  and row 10 is an immediate consequence of row 7. The paper's argument is
  therefore complete, but only because the set computation it performs three
  paragraphs earlier is doing this work.

## 5. Measurements

Build, `scripts/compile.sh -r r0048`, log
`ScottDomains/logs/compile-20260809-135633.agent1.log`:

    exit 0 · wall 0:05.05 · 1365 jobs · lake errors 0 · sorry 0 · other warnings 0

`ScottDomains.A1Theorem2` built in 798 ms. First compile attempt succeeded; no
statement was weakened to make it pass.

Axioms, `scripts/axioms.sh`:

| # | Declaration | Axioms |
| -- | ---------- | ------ |
| 1 | `theorem2` | `[propext, Classical.choice, Quot.sound]` |
| 2 | `scottContinuous_sbOp` | `[propext, Classical.choice, Quot.sound]` |
| 3 | `isLeast_sbFix` | `[propext, Classical.choice, Quot.sound]` |
| 4 | `sbOp_sbFix` | `[propext, Classical.choice, Quot.sound]` |
| 5 | `sbFix_sdiff` | `[propext, Classical.choice, Quot.sound]` |
| 6 | `mem_extension_iff` | **none** |
| 7 | `sbBij_pos` | `[propext, Classical.choice, Quot.sound]` |
| 8 | `sbBij_neg` | `[propext, Classical.choice, Quot.sound]` |
| 9 | `apply_notMem_of_notMem` | `[propext, Classical.choice, Quot.sound]` |

No `sorryAx` anywhere. `Classical.choice` is genuinely used, not incidental: `h`
selects a witness.

## 6. The "30 numbered results" figure is correct

The orchestrator flagged this count as never verified against the printed text.
It is now verified. `pdftotext -layout` over all 47 pages, then
`grep -oE "(Theorem|Lemma|Proposition|Corollary) [0-9]+"`. Result headings are
plain ASCII, so the Type 3 font defect that corrupts operator glyphs does not
affect this measurement.

| # | Measurement | Value |
| -- | ----------- | ----: |
| 1 | headings at start of line (the declaration form) | **30** |
| 2 | distinct numbers used | **30** |
| 3 | range | **1 … 30, contiguous — no gap, no repeat** |
| 4 | headed `Theorem` | 16 |
| 5 | headed `Lemma` | 13 |
| 6 | headed `Proposition` | **1** — result 15 only |
| 7 | headed `Corollary` | **0** |

Full list: Theorems 1, 2, 3, 6, 7, 11, 12, 14, 16, 18, 21, 22, 25, 26, 27, 29;
Lemmas 4, 5, 8, 9, 10, 13, 17, 19, 20, 23, 24, 28, 30; Proposition 15.

So **outcome 3 is refuted**, for result 2 and for the paper as a whole: the
numbering skips nothing, and `PropertiesVsTheorems.md`'s figure of 30 needs no
correction. Row 6 of that table is the whole of the r0048 measurement defect —
one Proposition among 29 Theorems and Lemmas, and both instruments that produced
this round's assignment grep only `thm|theorem|lem|lemma`.

## 7. For the orchestrator

1. `docs/Status.md` line 62, "Theorem 2 — not quoted anywhere in the tree or the
   docs", is now false. It is quoted verbatim, with folio and physical page, in
   `A1Theorem2.lean`'s module docstring and again on `theorem2` itself, and it is
   proved.
2. With agent2's Proposition 15, **30 of 30 numbered results are now quoted in the
   tree**, and the "28 of 30" figure was wrong on both rows for two different
   reasons: result 15 was a grep blind spot, result 2 was a real absence.
3. `PaperInventory.md` row 2.2 should now name `ScottDomains.R48.Agent1.theorem2`
   as the in-package statement, keeping the Mathlib pointer as a cross-reference
   and saying why the two proofs differ (Kleene vs. Knaster–Tarski).
4. `scripts/numbered-status.sh` matches `(thm|theorem|lem|lemma)_?N` over
   declaration names. Extending it with `prop|proposition|cor|corollary` costs one
   alternation and removes the class of defect that produced this round. It would
   still have missed result 2, which was genuinely absent — the two failures are
   independent.
5. Nothing in the package depends on `A1Theorem2`; it is a leaf. Merging it cannot
   perturb any existing proof.
