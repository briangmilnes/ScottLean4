---
round: r0031
from: agent1
to: orchestrator
subject: computable-functions
date: 2026-0806-20:15
started: 2026-0806-19:50
finished: 2026-0806-20:15
related:
  - plans/r0031-plan-from-orchestrator-to-agent1-computable-functions.md
---

# r0031 agent1 — §3.2's computable function, formalized against `REPred`

## Measurement

| # | Quantity | Value |
| -- | -------- | ----- |
| 1 | Final build (whole library) | `Build completed successfully (1060 jobs).` |
| 2 | Errors | 0 |
| 3 | Warnings | 1 — the pre-existing declared `sorry` at `Skeleton/Section6.lean:196` (`thm18`) |
| 4 | `sorry` in the development | 1, unchanged; **0** in the new module |
| 5 | New module | `ScottDomains/ScottDomains/ComputableFunction.lean`, 158 lines, 7 declarations (3 definitions, 4 theorems) |
| 6 | Files changed outside the new module | 0 |
| 7 | Axioms, all 7 declarations | `[propext, Classical.choice, Quot.sound]`; **no `sorryAx`** |
| 8 | Job-count delta from the new module | 972 → 1060 (+88, the `Mathlib.Computability.*` import chain) |
| 9 | Build cost | wall 0:00.70 (warm), 792 MiB peak RSS single process |
| 10 | Commit (branch `agent1`) | see the closing section |

The module built clean on the first compile; there was no error-fixing loop.

## 1. Was `REPred` the right notion? Yes.

The plan's claim checks out. `Mathlib/Computability/RE.lean:157` (in the pinned
dependency at `ScottDomains/.lake/packages/mathlib`, not only the root `mathlib/`
clone) defines

    def REPred {α} [Primcodable α] (p : α → Prop) :=
      Partrec fun a => Part.assert (p a) fun _ => Part.some ()

"`p` is the domain of a partial recursive function". That is the textbook
characterization of a recursively enumerable predicate — `Partrec.dom_re` in the
same file is the statement that a partial recursive function's domain is r.e. —
and it is exactly what §3.2's "recursively enumerable" means. The old grep failed
on capitalization: `RePred` versus `REPred`.

One structural point that made the formalization cheaper than expected: the
paper's r.e. set is a set of **indices**, `{m | eₘ ⊑ f(dₙ)} ⊆ ℕ`. The only
`Primcodable` instance required is therefore the one on `ℕ` (and on `ℕ × ℕ` for
the uniform variant). **Deliverable 3 of the plan does not arise**: no
`Primcodable` structure on `K(D)` has to be built, and none was. Moving
recursion-theoretic questions onto a countable index set is what a presentation
is for.

## 2. The paper's wording, extracted from the PDF

`pdftotext -layout "ScottDomains/papers/Gunter Scott 1990.pdf"`, §3.2, the
sentence immediately after the definition of an effective presentation
(ligature damage from the extraction repaired, wording otherwise untouched):

> If ⟨D, d⟩ and ⟨E, e⟩ are effectively presented domains, then a continuous
> function f : D → E is said to be computable (with respect to d and e) if and
> only if, for every n ∈ ℕ, the set {m | eₘ ⊑ f(dₙ)} is recursively enumerable.

The paraphrase already in `EffectivePresentation.lean`'s docstring matches this
verbatim; nothing was lost, unlike the `Pf` case r0029 found.

## 3. What the kernel accepted

```lean
def IsComputable (d : EffectivePresentation α) (e : EffectivePresentation β)
    (f : ScottHom α β) : Prop :=
  ∀ n : ℕ, REPred fun m : ℕ => e.enum m ≤ f (d.enum n)
```

Continuity is carried by the type: `f : ScottHom α β` bundles its
`ScottContinuous` proof, so "a continuous function `f : D → E` is said to be
computable" is rendered with no side condition, and *a computable function is
continuous* holds by `ScottHom.scottContinuous` without a theorem.

The other six declarations:

| # | Declaration | Statement |
| -- | ----------- | --------- |
| 1 | `rePred_comp` | r.e. is closed under precomposition with a computable function: `REPred p → Computable g → REPred (p ∘ g)`. This is `Partrec.comp` read through the definition of `REPred`; Mathlib does not state it |
| 2 | `IsUniformlyComputable d e f` | the uniform strengthening: `REPred fun p : ℕ × ℕ => e.enum p.2 ≤ f (d.enum p.1)` |
| 3 | `RecursiveLE d` | `ComputablePred fun p : ℕ × ℕ => d.enum p.1 ≤ d.enum p.2` — the recursion-theoretic reading of condition 1 |
| 4 | `IsUniformlyComputable.isComputable` | uniform ⟹ the paper's, by `rePred_comp` along `m ↦ (n, m)` |
| 5 | `isUniformlyComputable_of_enumMap` | if `e` has `RecursiveLE`, `t : ℕ → ℕ` is `Computable`, and `f (dₙ) = e_{t n}` for all `n`, then `f` is uniformly computable |
| 6 | `isUniformlyComputable_id`, `isUniformlyComputable_const` | the identity and the constants at basis elements, as instances of 5 |

All in `namespace ScottDomains.Computable`, as instructed.

## 4. Two findings the orchestrator must decide on

### 4.1 The paper's quantifier is non-uniform, and no closure property survives it

`for every n ∈ ℕ, the set {m | eₘ ⊑ f(dₙ)} is recursively enumerable` puts `n`
*outside* the r.e. claim. It does not ask that an index for that r.e. set be
computable from `n`. `IsComputable` is that literal reading — I did not
strengthen it.

Every closure property, however, needs the uniform reading (the single relation
`{(n, m) | eₘ ⊑ f(dₙ)}` is r.e.), which is what the surrounding literature on
effectively given domains normally means. So the module defines both, proves
`IsUniformlyComputable → IsComputable`, and proves the closure results only for
the uniform one. The converse is false in general and is not claimed. Whether the
development should adopt the uniform reading as *the* definition is a decision
about the paper, not about Lean, and I left it open rather than take it.

### 4.2 `EffectivePresentation.decidableLE` is too weak to prove anything computable

`EffectivePresentation` renders the paper's condition 1 as a Lean `DecidablePred`
instance. `EffectivePresentation.lean`'s own docstring argues that this is
faithful, and for conditions 1 and 2 *as the paper uses them* it is. But a Lean
`Decidable` instance may be `Classical.dec`; there is no route from
`DecidablePred p` to `ComputablePred p`, which additionally ties the decision
procedure to `Nat.Partrec`. Consequently:

**No computability theorem whatsoever follows from `EffectivePresentation`
alone** — not even that the identity `D → D` is computable. Every theorem in
section 3 above takes `RecursiveLE` as an explicit hypothesis. I did not weaken
any statement to avoid this; I made the missing hypothesis visible.

The fix, if the orchestrator wants one, is to add a field to
`EffectivePresentation`:

    computableLE : ComputablePred fun p : ℕ × ℕ => enum p.1 ≤ enum p.2

That is a change to a shared module, so per the plan I stopped and am reporting
it instead. Note that `decidableLE` would then be derivable from it
(`ComputablePred` packs a `DecidablePred`), so the field would replace rather
than accompany the existing one — which makes it a breaking change for every
construction of an `EffectivePresentation`.

## 5. What I did not attempt: composition

If `f : D → E` and `g : E → F` are computable then, expanding `g(f(dₙ))` as the
directed supremum of `{g(eₘ) | eₘ ⊑ f(dₙ)}`,

    c_k ⊑ g(f(dₙ))  ↔  ∃ m, eₘ ⊑ f(dₙ) ∧ c_k ⊑ g(eₘ).

Composition therefore needs r.e. predicates closed under conjunction **and**
under existential quantification over `ℕ`. Measured: Mathlib v4.32.2's entire
`REPred` API is five lemmas — `REPred.of_eq`, `Partrec.dom_re`,
`ComputablePred.to_re`, `ComputablePred.computable_iff_re_compl_re`, and its
primed variant — plus two uses in `Halting.lean`, and 11 occurrences of the
identifier library-wide. Neither closure property is present.

Conjunction is short (a `Partrec.bind`, then `Partrec.dom_re` and `REPred.of_eq`).
The projection theorem is not: with only an r.e. inner predicate it requires a
dovetailing search over `Nat.Partrec.Code.evaln` with `evaln_complete`, which is
recursion theory rather than domain theory and is well outside "cheap to
discharge". I built neither, since an unused conjunction lemma buys nothing
(ruleset principle 2). Composition is stated nowhere in the module — not
`sorry`ed, not assumed — and the reasoning above is recorded in the module
docstring so the next reader does not rediscover it.

If the orchestrator wants composition, the unit of work is a Mathlib-shaped
lemma `REPred fun a => ∃ n, P a n` from `REPred (uncurry P)`. Estimate: 60–120
lines against `evaln`, with real risk in the `encode`/`decode` bookkeeping.

## 6. Two smaller notes

1. **`ScottHom.id` was not used.** It lives in `FinitaryProjectionPoset`, whose
   import closure includes `Theorem6` and `Skeleton.Section6` (the module holding
   the development's only `sorry`). `isUniformlyComputable_id` is stated instead
   for an arbitrary `f : ScottHom α α` with `∀ x, f x = x`, which is strictly more
   general and which `ScottHom.id` discharges with `fun _ => rfl` at any call
   site. No duplicate identity definition was introduced.

2. **The namespace `ScottDomains.Computable` does not shadow Mathlib's
   `Computable`.** This was a merge hazard worth measuring rather than assuming,
   so I compiled a probe file: after `open ScottDomains`, both
   `Computable (fun n : ℕ => n) := Computable.id` and
   `Computable.const 3` still elaborate, and they still do under
   `open ScottDomains.Computable` as well. Exit status 0, no ambiguity errors.

## 7. Stale records to correct (I did not edit them)

Both are outside the one file I own, so I am reporting rather than changing them:

| # | Location | The false claim |
| -- | -------- | --------------- |
| 1 | `ScottDomains/ScottDomains/EffectivePresentation.lean:32–39`, the "What is deliberately absent" section | "this Mathlib (v4.32.2) has no `RePred` or equivalent under a ready name — a grep across the whole library finds no definition of r.e. predicates" |
| 2 | `ScottDomains/docs/PaperInventory.md` | the same gap, recorded since r0022 |

Both should now point at `ScottDomains/ComputableFunction.lean`. Item 1 also
deserves the qualification from finding 4.2: reading condition 1 as
`DecidablePred` is faithful to the paper's *use* of it, but it is strictly weaker
than what a computability theorem needs.

## 8. Verbatim build line and commits

```
Build completed successfully (1060 jobs).
compile: exit 0 · wall 0:00.70 · mem 792 MiB single / 787 MiB tree pss / 791 MiB tree rss · jobs 1060 · diagnostics 0 · lake errors 0 · sorry 1 · other warnings 0
```

Log: `ScottDomains/logs/compile-20260806-201136.agent1.log`.
Module-only build: `ScottDomains/logs/compile-20260806-201034.agent1.log`
(919 jobs, 0 errors, 0 warnings, 0 `sorry`).

Commit on branch `agent1`: **`cf0cc3c`** (one commit — the module, this report,
and the two build logs). `scripts/gitcp.sh` then reported "There is no tracking
information for the current branch", which is the expected outcome: agents commit
and do not push.
