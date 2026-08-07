---
round: r0036
from: agent3
to: orchestrator
subject: theorem-27
date: 2026-0807-08:57
started: 2026-0807-08:37
finished: 2026-0807-08:57
related:
  - plans/r0036-plan-from-orchestrator-to-agent3-theorem-27.md
  - plans/r0036-plan-from-orchestrator-to-orchestrator-five-way-open-results.md
---

# r0036 stream 3 — Theorem 27, unconditional

## Result

Acceptance item 1, the top of the ranked list, landed in full. `Atomless.thm27`
is Theorem 27 with no hypothesis:

    theorem thm27 (D : Type u) [CompletePartialOrder D] [Domain D] [BoundedComplete D] :
        ∃ (e : ScottHom D Dyadic.U) (p : ScottHom Dyadic.U D),
          ScottHom.IsEmbeddingProjectionPair e p

`Dyadic.IsNormallyRepresented ↥(compacts D)` — the single assumed input at
`Dyadic.lean:447` — is proved, as `Atomless.isNormallyRepresented_compacts`. The
general form `Atomless.isNormallyRepresented` proves it for **any** countable
poset with a least element in which bounded pairs have least upper bounds, which
is the paper's own hypothesis on `A`.

Kernel-checked axioms of `thm27`, `isNormallyRepresented` and
`isNormalIn_range_psi`: `[propext, Classical.choice, Quot.sound]`. No `sorryAx`,
no new named `Prop` standing in for a proof.

## Neither the one-sided embedding nor full uniqueness was needed

The plan asked which of the two Boolean-algebra facts sufficed. The measured
answer is **neither**, and the Boolean algebra `B = U₀ ∪ {∅}` never appears in
the proof. The plan's own most valuable observation — that Theorem 27 consumes
only the embedding of a countable Boolean algebra into the atomless one, not
Vaught's categoricity theorem — is correct as far as it goes, but it does not go
far enough: Theorem 27 does not consume a Boolean-algebra embedding either.

What it consumes is exactly three properties of a map `ψ : A → U₀`:

| # | Property | Name |
| -- | -------- | ---- |
| 1 | `a ≤ b ↔ ψ a ≤ ψ b` (`U₀` ordered by superset) | `psi_le_psi` |
| 2 | `ψ ⊥ = [0, 1)` | `psi_bot` |
| 3 | `ψ a ∩ ψ b` empty when `{a,b}` is unbounded, `ψ (a ⊔ b)` when bounded | `bddAbove_of_psiSet_inter_nonempty`, `psiSet_inter` |

Property 3 is what makes `range ψ` normal, and normality is the paper's own final
clause — the one it asserts without proof, and which the plan expected to need
work. Here it is a four-line consequence of property 3
(`isNormalIn_range_psi`): two members of `range ψ` above a common `X ∈ U₀` share
a point, so their preimages are bounded, and the image of the join is again
above `X`.

`ψ` is built directly, so the categoricity half was never proved and the
one-sided back-and-forth was never proved either.

## The construction, and why it is cheaper than the paper's route

Read a point `s ∈ S` as an infinite sequence of binary digits: at level `n` it
lies in exactly one block `[j/2ⁿ, (j+1)/2ⁿ)` with `j = addr n s = ⌊s · 2ⁿ⌋`, and
`addr (n+1) s / 2 = addr n s` — the address grows one digit per level. Label the
nodes of that binary tree with elements of `A` along a fixed enumeration
`enum : ℕ → A`: `st A 0 j = ⊥`, and `st A (n+1) j` adjoins `enum n` to the parent
label when the last digit `j % 2` is `1` and the step is *legal*, else repeats
the parent label. Then

    ψ a = {s ∈ S | a ≤ st A (idx a + 1) (addr (idx a + 1) s)}.

The whole difficulty sits in one side condition. `Legal n z` requires that
`{z, enum n}` be bounded **and** that `z ⊔ enum n` carry no `enum i` with `i < n`
that `z` does not already carry. Without the second conjunct the set of branches
carrying `a` is open but not closed — `a` could first appear at arbitrarily deep
levels, for instance when `a ≤ u ⊔ v` while `a ≰ u` and `a ≰ v` — so `ψ a` would
not be a finite union of intervals and would not lie in `U₀` at all. With it,
whether a branch carries `enum i` is decided at level `i + 1` and never revisited
(`br_stable`), so `ψ a` depends on the first `idx a + 1` binary digits alone,
which is precisely to say it is a finite union of dyadic half-open intervals
(`isBasic_block`).

That side condition is the same mathematics as the paper's atom splitting: in the
Boolean-algebra proof one refuses to place a new generator inside an atom of the
finite subalgebra built so far unless the atom splits, and the refusal is
permanent. Here the refusal is the `else` branch of `step`. Stating it as a
condition on one element of `A` rather than on the atoms of a finite subalgebra
is what removes the need for Boolean algebras, atomlessness, countable
categoricity and the finite-partial-isomorphism ideal of
`Mathlib/Order/CountableDenseLinearOrder.lean`.

Surjectivity of `ψ` onto a *normal* subposet — the step the paper skips — comes
from the branch `digits b`, which takes `enum n` on board exactly when
`enum n ≤ b`. `digits_spec` proves in one induction that this branch is legal at
every step, that its labels never rise above `b`, and that it reaches every
`enum i ≤ b`. That single lemma gives non-emptiness of `ψ b` and order
reflection at once.

## Where the source contradicts the plan and the prior docstring

Process rule 7 says the source wins and the report should say so.

1. **§7.3 read directly** (`pdftotext -layout`, lines 1583–1599 of the extract)
   confirms the `Dyadic.lean` docstring's quotation verbatim, including two
   sentences the docstring omits: "The map `i : x ↦ ↑x` is a monotone injection
   which preserves existing least upper bounds" and "a subset `u ⊆ A` is bounded
   just in case `⋂_{x ∈ u} ↑x` is non-empty". The second is exactly property 3
   above, which is evidence the property list is the right cut of the paragraph.
   Nothing in the source contradicts the plan's summary of it.

2. **Two claims in `Dyadic.lean`'s docstring are now false and were corrected in
   this commit.** It said the proof of `IsNormallyRepresented` "needs the
   uniqueness up to isomorphism of the countable atomless Boolean algebra —
   Vaught's theorem", and that "nothing weaker will do, because the paper's `j`
   is exactly the embedding that theorem supplies". Both are refuted by
   `Atomless`. The measurement that motivated the split stands and is kept:
   Mathlib v4.32.2 has zero occurrences of `IsAtomless` in `Mathlib/` and zero
   occurrences of "atomless" in `Mathlib/ModelTheory/`. The plan repeated the
   first claim; it is the plan and the docstring that were wrong, not the paper.

3. `Mathlib/Order/CountableDenseLinearOrder.lean` was read as the plan directed.
   It is a correct template for Vaught's theorem and was not used, because the
   route it templates turned out to be unnecessary.

## Measurements

| # | Quantity | Value |
| -- | -------- | ----- |
| 1 | Module build (`ScottDomains.Atomless`) | `Build completed successfully (1036 jobs).` — 0 errors, 0 diagnostics, 0 warnings, 0 `sorry`; wall 1.92 s, peak RSS 1817 MiB |
| 2 | Full build (`scripts/compile.sh -r r0036`) | `Build completed successfully (1213 jobs).` — 0 errors, 0 non-`sorry` warnings; wall 4.52 s replay, peak RSS 1822 MiB single |
| 3 | `sorry` | **2**, both pre-existing and both outside this stream: `Skeleton/Recovered.lean:258` (thm14, agent1), `Skeleton/Section6.lean:197` (thm18, agent2). None introduced. |
| 4 | New module | `ScottDomains/ScottDomains/Atomless.lean`, 679 lines, 77 top-level declarations |
| 5 | Repo counts (`scripts/counts.sh`) | modules 62 (+1), lines 20186 (+689), theorems 962 (+56) |
| 6 | Axioms | `thm27`, `isNormallyRepresented`, `isNormalIn_range_psi` each `[propext, Classical.choice, Quot.sound]` |
| 7 | Numbered results | Theorem 27 moves from conditional to proved; 23 of 29 by this stream alone |

## Non-vacuity

Three witnesses are compiled in the module, because a class with no instance and
a theorem quantified over it are unfalsifiable:

* `instance : CountableBC U₀` — `U₀` satisfies the new class, via
  `U₀.exists_isLUB_pair`, the same fact `U`'s bounded completeness consumes;
* `example : Dyadic.IsNormallyRepresented U₀` together with
  `example : Nontrivial U₀` — `psi` is applied to a poset with at least two
  elements, and `psi_injective` makes its image have at least two, so the
  conclusion is not satisfied by a one-point subposet;
* `example : … := thm27 Dyadic.U` — Theorem 27 instantiated at `D = U`,
  exercising `Domain`, `BoundedComplete`, `CountableBC ↥(compacts U)` and the
  `IsEmbeddingProjectionPair` conclusion end to end.

## Files changed

| # | File | Change |
| -- | ---- | ------ |
| 1 | `ScottDomains/ScottDomains/Atomless.lean` | new, 679 lines, namespace `ScottDomains.Atomless` |
| 2 | `ScottDomains/ScottDomains/Dyadic.lean` | docstring only — the two false claims corrected, `thm27` and `IsNormallyRepresented` doc-comments repointed at `Atomless`. No statement or proof touched. |
| 3 | `INDEX.md` | entry for the new module; the `Dyadic.lean` line's description of what is left open corrected |
| 4 | `ScottDomains/logs/compile-*.agent3.log` | three build logs |

`Dyadic.thm27` keeps its hypothesis: `Atomless` imports `Dyadic`, so the
unconditional statement cannot live in `Dyadic` without a cycle. It is
`Atomless.thm27`, and `Dyadic.thm27`'s doc-comment now says so.

## For the orchestrator

1. `docs/PaperInventory.md` rows for Theorem 27 need Theorem 27 moved from `~` to
   `✓`; per the round plan that update is the orchestrator's, from measured
   counts, not this report's numbers.
2. `scripts/axioms.sh -i ScottDomains.Atomless -i <other agents' modules>` is
   worth running as the composition check. `Atomless` introduces one class
   (`CountableBC`) and the names `psi`, `st`, `br`, `enum`, `idx`, `jn`, `step`,
   `Legal`, `digits`, `pt`, `addr`, `blockLeft`, `blockRight` — all inside
   `ScottDomains.Atomless`, none colliding with an existing namespace.
3. Commits on `agent3`: `8b5cc6c` (the module) and `a6620ba` (witnesses,
   docstring corrections, INDEX). Not pushed, per rule 8.
