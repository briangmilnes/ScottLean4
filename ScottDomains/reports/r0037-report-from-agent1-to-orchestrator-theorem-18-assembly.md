---
round: r0037
from: agent1
to: orchestrator
subject: theorem-18-assembly
date: 2026-0807-11:45
started: 2026-0807-11:14
finished: 2026-0807-11:45
related:
  - plans/r0037-plan-from-orchestrator-to-agent1-theorem-18-assembly.md
  - plans/r0037-plan-from-orchestrator-to-orchestrator-last-four.md
---

# r0037 stream 1 — Theorem 18, the assembly half

One new module, `ScottDomains/ScottDomains/JungFinite.lean`, namespace
`ScottDomains.JungFinite`. Nothing else in the development was edited except one
line added to `INDEX.md`. No declaration was added to `JungSFP.lean`,
`Section62.lean`, `MinimalUpperBounds.lean` or `Skeleton/Section6.lean`.

## Measurement

| # | Quantity | Before | After | Measured by |
| -- | -------- | ------ | ----- | ----------- |
| 1 | Build | 1218 jobs, 0 errors | `Build completed successfully (1218 jobs).`, 0 errors, 0 diagnostics, 0 non-`sorry` warnings | `scripts/compile.sh -r r0037`, log `compile-20260807-114025.agent1.log` |
| 2 | `sorry` | 1 (`Skeleton/Section6.lean:197`) | **1**, the same one, unchanged | `scripts/counts.sh` |
| 3 | Modules / lines / theorems | 66 / 23596 / 1119 | 67 / 24304 / 1141 | `scripts/counts.sh` |
| 4 | New module | — | 714 lines, 23 live declarations (1 commented out as unused) | `wc -l`, `grep` |
| 5 | Axioms of the five headline results | — | `[propext, Classical.choice, Quot.sound]`, no `sorryAx` | `scripts/axioms.sh` |

Row 5 covers `lemma129`, `exists_monotone_seq`,
`exists_strictMono_mem_mubClosure`, `lemma22`, `thm18_of_propertyM`.

`Skeleton/Section6.lean`'s `sorry` was **not** touched, per the plan: stream 2's
Theorem 1.37 is not in this worktree, and one further prerequisite is open here
too (below).

## What is proved

Ranked against the plan's acceptance list, this is **item 2 minus one
hypothesis**: Lemma 1.29 and step 4 are both proved and `thm18_of_propertyM` is
assembled from steps 1–5, but it carries **two** explicit hypotheses rather than
one.

1. **Jung's Lemma 1.29** — `lemma129`, plus the general-poset form
   `minimalUpperBounds_finite_of_pairs` and its witness set
   `exists_finite_complete_upperBoundsIn`. Property m together with property M at
   pairs gives property M at every finite subset of `K(D)`. This is the join
   between `JungSFP.lemma217` (property M at a *pair*) and
   `isBifinite_iff_mubClosure` (property M at *every* finite subset), and it is
   what the plan identified as the missing link between two proved results.
2. **König's lemma graded by `ℕ`** — `exists_monotone_seq`, with `climbDown`,
   `desc`, `climbDown_mem`, `subset_biUnion_desc`,
   `desc_subset_insert_biUnion`. Finite nonempty levels with an infinite union
   and a descent relation admit a monotone transversal.
3. **The stages of `U` under property M** — `mubStep_finite`, `mubIter_finite`,
   `mubDiff`, `mubDiff_finite`, `mubDiff_nonempty`, `exists_mem_mubDiff_le`,
   `mubDiff_ne`, and `exists_strictMono_mem_mubClosure`, which is Jung's "we find
   a global selection function … `C = {s(n)}` is a chain in `U^∞(A)`" in full.
4. **Jung's Lemma 2.2** — `lemma22`, given Corollary 1.36 as a hypothesis. Its
   middle step is `apply_eq_self_of_mem_mubClosure_compacts`, a strengthening of
   `Section62.apply_eq_self_of_mem_mubClosure` that drops the hypothesis `hgA`
   ("`g` maps `A` into `A`"); at `A = K(D)` that hypothesis is Jung's
   Proposition 1.41, itself a corollary of 1.36, so keeping it would have made the
   file depend on the open step twice.
   `JungSFP.minimal_upperBounds_of_mem_minimalUpperBounds` removes it.
5. **The assembly** — `thm18_of_propertyM`, `IsBifinite α` from
   `[Domain α] [Domain (ScottHom α α)]` plus two hypotheses.

Countability of `K(D → D)` is spent exactly once, in `JungSFP.lemma217`, reached
through `Domain.countable_compacts (α := ScottHom α α)` inside
`thm18_of_propertyM`. r0031's (★) does not appear anywhere in the file.

## Rado or König, and why

**König.** Three measured reasons.

1. Jung's Theorem 2.1 (Rado's Compactness Theorem) is stated for an arbitrary
   index set `I` and proved by Tychonoff on `∏_{i∈I} Aᵢ`. Lemma 2.2 applies it at
   `I = ℕ` with the fibers `Bₙ`, which is exactly König's lemma for a finitely
   branching tree of height `ω`.
2. Mathlib's only form of Rado is
   `nonempty_sections_of_finite_inverse_system` in
   `Mathlib/CategoryTheory/CofilteredSystem.lean` (there is also
   `Mathlib/Topology/Category/TopCat/Limits/Konig.lean`, which is the same result
   via `TopCat`). Using it means presenting the system as a functor out of a
   category and importing the product topology; the development's imports are
   otherwise fine-grained order-theory files. Searching Mathlib for a bare
   `ℕ`-graded König statement found none.
3. The elementary proof costs about 100 lines and needs no topology, no category
   theory, and **no cardinality hypothesis**.

Point 3 is a correction to the development, and to my plan. The plan and
`Skeleton/Section6.lean:193` both say case (c) "needs König's lemma against the
countability of `K(D)` carried by `Domain.countable_compacts`". It does not: the
grading by `ℕ` that König needs is supplied by the `U`-iteration itself, not by an
enumeration of `K(D)`. Countability remains indispensable to Theorem 18 — without
it the statement is false — but it is spent in step 3, not step 4. This is
recorded in the module docstring.

## Corrections to the plan from the source

Per rule 6, the source wins; two divergences, both checked against
`papers/Jung 1989 Cartesian Closed Categories of Domains.pdf` (physical pages
41–42 for Lemma 1.29, 56–57 for Theorem 2.1 and Lemma 2.2, 51 for Corollary 1.36
and Theorem 1.37).

1. **Lemma 1.29 is not "pairs ⟹ all finite sets".** Jung, p. 40: "A poset `D`
   with property m has property M **if and only if the empty set and each pair of
   elements** have a finite set of minimal upper bounds." The empty-set clause is
   not redundant: an infinite antichain has property m and every pair has an empty
   — hence finite — mub-set, but `mub(∅)` is the whole antichain. The formalization
   carries the clause as a hypothesis of the general-poset form
   `minimalUpperBounds_finite_of_pairs`; over `K(D)` in a cpo it is discharged for
   free by `minimalUpperBounds_compacts_empty` (`mub(∅) = {⊥}`), so `lemma129`
   carries only the pair hypothesis, exactly as the plan expected. The plan's
   *conclusion* was right; its *statement* of Jung's lemma was missing a clause,
   and a formalization that omitted it would have been unprovable.
2. **Rado's theorem is Jung's Theorem 2.1, not a step the development can skip
   silently** — see the previous section. Also, the plan's route sketch for
   Lemma 2.2 ("Rado extracts an infinite chain … a compact `f ≪ id` fixing `A`
   fixes all of `U^∞(A)`") is accurate; what it does not say is that the middle
   step as previously stated in `Section62.lean` needs Proposition 1.41, which is
   Corollary 1.36 again. That is why item 4 above restates it.

## What remains between this work and `thm18`

Exactly two hypotheses, both explicit arguments of `thm18_of_propertyM`, neither
stubbed with `sorry`:

| # | Hypothesis | Jung | Owner |
| -- | ---------- | ---- | ----- |
| 1 | `hm : ∀ v ⊆ K(D) finite, HasCompleteMub (compacts α) v` — property m | Theorem 1.37 | **stream 2 this round** |
| 2 | `hcor : FixedPointOfCompactDeflationIsCompact α` | Corollary 1.36 | **open** |

With both, `thm18` is `thm18_of_propertyM hcor hm` — one `exact`. Note that
hypothesis 1 is stated for *every* finite subset of `K(D)`, which is what
`lemma129` and `isBifinite_iff_mubClosure` need; `JungSFP.lemma217` needs only its
instance at a pair. If stream 2 delivers property m only at pairs, Lemma 1.29
cannot consume it and Theorem 1.37's full strength (bicompleteness) is still
required. Jung's Theorem 1.37 gives the full form, so this should not bind.

### Hypothesis 2, and what was measured about it

`FixedPointOfCompactDeflationIsCompact α` says: a compact `f ⊑ id` in `[D → D]`
with `f(d) = d` forces `IsCompactElement d`. That is Corollary 1.36 at `g = idD`,
specialized to fixed points, and it is the only use Lemma 2.2 makes of the
corollary.

Jung derives 1.36 from Proposition 1.34, which restricts to the principal ideal
`↓e` and cites Proposition 1.22 — continuity of the function space of a retract —
to obtain `f|↓e ≪ id↓e`. Neither 1.22 nor 1.5 is formalized here.

Two direct routes were tried and both fail on one identified condition each; the
detail is in the docstring of `FixedPointOfCompactDeflationIsCompact` so the next
attempt does not repeat them.

* The restriction to `↓c` itself is **cheap**: `ScottHom` and `IsCompactElement`
  need only `PartialOrder`, which `↥(Set.Iic c)` inherits, so no cpo structure on
  the subtype has to be built. Given `IsCompactElement (f|↓c)`, the argument
  finishes in one step — the constants `{c_s | s ∈ S}` are directed on `↓c` with
  least upper bound the top `c_c ⊒ f|↓c`, and `f|↓c ⊑ c_s` evaluated at `c` gives
  `c = f(c) ⊑ s`.
* `IsCompactElement (f|↓c)` is what does not follow. Extending a directed family
  from `↓c` to `D` by the **identity** outside `↓c` is monotone only for functions
  below `id↓c` — for `x ⊑ c`, `y ⋣ c`, `x ⊑ y` it must produce `h(x) ⊑ y`, and
  `h(x) ⊑ x ⊑ y` is the only route — while `IsCompactElement` quantifies over
  every directed family. Extending by the **constant `c`** instead is monotone for
  every `h`, but then `f ⊑ ext(h)` fails off `↓c`, where `f(x) ⊑ x` gives nothing
  below `c`. Each variant satisfies one of the two conditions and violates the
  other, which is precisely why Jung's proof needs a retraction and not merely a
  restriction.

A further family of would-be counterexample constructions on `D` itself was
checked and discarded: every "truncation at `s`" that is Scott continuous on `D`
without meets (`x ↦ if f(x) ⊑ s then f(x) else x`, `x ↦ if x ⊑ s then f(x) else x`,
`x ↦ if k ⊑ x then f(x) else ⊥` for compact `k`) is **antitone** in the index and
lies **above** `f`, so none of them contradicts compactness of `f`. The obstacle
is structural: an increasing family witnessing failure of compactness has to
truncate, and truncation in a domain with no binary meets is available only inside
a principal ideal.

## Files

* `ScottDomains/ScottDomains/JungFinite.lean` — new, 714 lines.
* `INDEX.md` — one line added.
* `ScottDomains/logs/compile-20260807-11*.agent1.log` — five build runs.

Commits on branch `agent1`: `aaaa74f` (Lemma 1.29), `20de10d` (König),
`ebd7095` (stages and chain), `a02a051` (Lemma 2.2 and assembly), plus this
report. Not pushed, per the agent/orchestrator split.
