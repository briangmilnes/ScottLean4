# PFPL in Lean 4 — Status

Formalization of Robert Harper, *Practical Foundations for Programming
Languages*, 2nd ed. (Cambridge University Press, 2016) in Lean 4.

**Source text:** the author-authorized free *Abbreviated online edition, with
corrections* — <https://www.cs.cmu.edu/~rwh/pfpl/abbrev.pdf> (linked from
<https://www.cs.cmu.edu/~rwh/pfpl.html>). Local, untracked copies:
`PFPL.pdf` and `PFPL.txt` (`pdftotext -layout`, 11,820 lines).

> Status reported as measurement, not verdict. "Formally verified" below means
> the Lean kernel accepted the derivation; a mere successful build is called
> "compiles."

## Snapshot (measured)

| Measure | Value |
| --- | --- |
| Lean source files | **1** — `pilot/LanguageE_Statics.lean` (95 lines) |
| `inductive` declarations | 3 — `Ty`, `Exp`, `HasType` |
| `abbrev` | 1 — `Ctx` |
| `notation` | 1 — `Γ ⊢ e : τ` |
| `def` | 0 |
| **`theorem` / `lemma`** | **0** |
| `example` (kernel-checked derivations) | 2 |
| **Proof holes (`sorry` / `admit`)** | **0** |
| Build | **compiles, exit 0** — core Lean 4, **no Mathlib**, standalone (not in the Lake library) |

Definitional declarations: **5** (3 `inductive` + 1 `abbrev` + 1 `notation`).
Proved theorems: **0**. Proof holes: **0**.

## What is formalized

PFPL **Chapter 4, *Statics*** — §4.1 (Syntax) and §4.2 (Type System) — the
language **E**:

- `Ty` — the two types `num`, `str`.
- `Exp` — the eight expression forms `var, num, str, plus, times, cat, len, letE`
  (the syntax chart, p. 36).
- `Ctx := List (String × Ty)` — typing contexts.
- `HasType : Ctx → Exp → Ty → Prop` — the statics `Γ ⊢ e : τ`, one constructor
  per typing rule (4.1a)–(4.1h), pp. 36–37.
- Two `example` derivations (`⊢ len("abc") + 2 : num` and
  `⊢ let x be 3 in x + x : num`) that the kernel accepts — a rendering check,
  not book content.

**Modelling choice:** concrete named variables (`String`) with a list context,
rather than Harper's abstract binding trees / generic hypothetical judgment. The
freshness side condition on `let` (rule 4.1h) is handled informally by context
lookup. A de Bruijn presentation would remove that informality.

## What is NOT yet formalized

- §4.3 **Structural Properties** — weakening, substitution, decomposition. These
  are the first *theorems*; currently **0 of them** are stated or proved.
- Ch. 5 **Dynamics** — transition, structural, contextual, equational.
- Ch. 6 **Type Safety** — preservation and progress.

## Scope of the book, and what is renderable

The full book is **19 parts, 49 chapters (+2 appendices), ~300 numbered
sections**. The free abbreviated edition contains full body text for only **17
chapters**: 1, 2, 3, 4, 5, 6, 9, 10, 11, 16, 19, 28, 29, 34, 35, 37, 40. Only
these can be faithfully rendered from this source (see `OUTLINE.md` for the
per-chapter map with `PFPL.txt` line anchors).

**Progress against renderable scope:** ≈ **1 of 17 chapters**, and within
Chapter 4 the statics only (not the §4.3 structural-property theorems).

## Build / check

Standalone, no Mathlib:

```bash
cd HarperBook
lake env lean pilot/LanguageE_Statics.lean   # compiles: exit 0, 0 errors, 0 holes
```

## Suggested next steps (increasing theorem content)

1. **§4.3 structural properties** for E — weakening and substitution as the first
   proved `theorem`s over `HasType`.
2. **Ch. 5 dynamics** for E — a small-step `Step : Exp → Exp → Prop`.
3. **Ch. 6 type safety** — preservation and progress, the payoff theorems.
4. Migrate `let` binding to de Bruijn (or an explicit α-equivalence, cf.
   `../Playground/Playground/LambdaNamed.lean`) to make the freshness condition
   formal rather than informal.
