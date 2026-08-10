import ScottDomains.JungSFP
import Mathlib.Order.Zorn

/-!
# Jung's step 1: bicompleteness, and property m as its corollary

This file formalizes the part of **Jung 1989, Theorem 1.37** that the development
can reach, and locates the part it cannot. It is step 1 of the five into which
`ScottDomains/Section62.lean` decomposes Theorem 18, and it is the hypothesis
`ScottDomains/JungSFP.lean`'s `jung_lemma_2_17` carries explicitly.

Everything below is read off the PDF in `ScottDomains/papers/Jung 1989 Cartesian
Closed Categories of Domains.pdf`, quoted rather than paraphrased.

## The statement, corrected against the source

The r0037 plan describes this stream's target as "if `[D → D]` is continuous then
`K(D)` has property m". **That is not what Theorem 1.37 says.** The source reads:

> **Theorem 1.37** A dcpo with continuous function space is bicomplete.

and *bicomplete* is defined in §1.1:

> If all directed sets in `D` have a supremum, then we say that `D` is a
> directed-complete partial order or dcpo for short. If, in addition, `Dᵒᵖ` is
> also a dcpo, then we call the poset **bicomplete**.

Property m is a *consequence*, drawn one section later where Jung applies the
theorem (Theorem 2.3's proof, verbatim):

> We have proved in Theorem 1.37 that a dcpo with algebraic function space is
> bicomplete, **hence `D` has property m**.

Jung leaves that "hence" unproved. The plan's description compresses the two
steps into one, and the compression hides the fact that the second step is short
while the first is long. Separating them is the whole content of this file:
**the "hence" is proved here in full; Theorem 1.37 itself is not.**

## What is proved

Three groups, in dependency order.

1. **The order-theoretic definitions and the dual Zorn step** — `IsBicomplete`,
   `HasChainInfima`, `IsBicomplete.hasChainInfima`, `exists_minimal_mem`.
   `exists_minimal_mem` is the order dual of Mathlib's `zorn_le₀`, obtained the
   way Mathlib's own `zorn_superset` obtains it, by instantiating at `Dᵒᵈ`.

2. **Jung's "hence": property m from infima of chains** —
   `exists_minimal_upperBounds_le`. For *any* subset `A` of `D` and any upper
   bound `x` of `A` there is a minimal upper bound of `A` below `x`. The proof is
   Zorn downwards inside `ub(A) ∩ ↓x`: a chain there has an infimum by hypothesis,
   that infimum is still an upper bound of `A` (each `a ∈ A` is a *lower* bound of
   the chain, so it is below the greatest lower bound) and is still below `x`.

   The hypothesis used is `HasChainInfima`, not `IsBicomplete` — infima of
   nonempty **chains**, not of all filtered sets. This is strictly weaker, so the
   result is strictly stronger, and it is the honest hypothesis: Zorn's lemma
   quantifies over chains and nothing here needs more. Jung reduces filtered sets
   to chains in the opposite direction, through his Theorem 1.2 (Iwamura's lemma);
   see the obstruction note for why that reduction is not available.

3. **The bridge to the development's relative form** —
   `hasCompleteMub_of_hasChainInfima`, `hasCompleteMub_pair`,
   `forall_hasCompleteMub_of_jung_theorem_1_37`, `jung_lemma_2_17_of_jung_theorem_1_37`. `HasCompleteMub A u`
   quantifies over upper bounds *in `A`*; Jung's property m quantifies over all of
   `D`. `JungSFP.mem_minimalUpperBounds_of_minimal` converts one to the other for a
   finite set of compacts in an algebraic dcpo, so item 2 lands in exactly the
   shape `jung_lemma_2_17`'s hypothesis and `isBifinite_iff_mubClosure`'s first conjunct
   are stated in. Nothing in `JungSFP.lean` or `MinimalUpperBounds.lean` had to
   change; the discharge is by application.

## The named remainder: `Theorem137`

`Theorem137 D` is Theorem 1.37 stated as a `Prop` — `IsAlgebraic (ScottHom D D) →
IsBicomplete D`. It is **not proved** and **no `sorry` stands in for it**: every
theorem below that needs it takes it as an explicit hypothesis. Two deviations
from Jung's statement, both weakenings of what is assumed to be proved:

* Jung's hypothesis is "continuous function space"; `Theorem137` assumes the stronger
  `IsAlgebraic (ScottHom D D)`, because **at this point in the import order** no
  predicate for a continuous dcpo is available. Algebraic implies continuous, so
  `Theorem137` is the weaker proposition, and it is the one Theorem 18 consumes —
  `JungSFP.lean` records the identical deviation for `jung_lemma_2_13`.

  *Correction, r0049/agent8.* The clause read "because the development has no
  predicate for a continuous dcpo", which was a claim about the whole package and
  is false: `JungBicomplete.IsContinuousDcpo` is that predicate, with
  `isContinuousDcpo_of_isAlgebraic` proving the implication this deviation
  appeals to. `JungBicomplete.lean` imports this module, so the predicate cannot
  be used *here* — the scope, not the claim, is what the sentence got wrong. It
  now names its scope, per `docs/ScopedClaims.md`.
* Jung's Theorem 1.42 ("a dcpo with algebraic function space is itself algebraic")
  is not formalized, so `[IsAlgebraic D]` stays an explicit instance hypothesis
  wherever item 3 is used rather than being derived from the function space.

## Precisely-located obstruction: what Theorem 1.37 costs

Jung's proof, quoted in full, is eleven lines. Reading it against what is on disk
gives the following dependency list. It is the *actual* list, taken from the
source; the r0037 plan's three-item summary ("ordinal-indexed codirected nets,
interpolation, a retraction onto `A ∪ αᵒᵖ`") is second-hand from r0036's report,
and it is right as far as it goes but omits the first and largest item.

1. **Corollary 1.3, dually** — "By Corollary 1.3 we have to find infima only for
   monotone injective nets `s : αᵒᵖ → D` where `α` is an ordinal number."
   Corollary 1.3 is a corollary of **Theorem 1.2**: "A partially ordered set `D`
   is a dcpo if and only if each chain in `D` has a supremum", which Jung
   attributes to Iwamura and does not prove. This is the reduction of directed
   completeness to chain completeness, and it is the step that lets the rest of
   the proof assume a well-ordered index. **Mathlib does not have it** — see the
   survey below — and neither does this development.

2. **The retraction `r` onto `A ∪ αᵒᵖ`**, where `A = lb(αᵒᵖ)`, defined by
   `r x = x` on `A` and `r x = ⋀{γ ∈ αᵒᵖ | γ ≥ x}` off it. Its well-definedness
   is not immediate: the infimum written on the right is an infimum of a proper
   initial segment of the chain, so it exists only under a transfinite induction
   on `α` (a least-counterexample argument), and landing it *inside* the chain
   needs the chain first normalized so that every limit stage is the infimum of
   its predecessors. Jung compresses both to "Since `α` is an ordinal there exists
   no strictly increasing infinite sequence in `αᵒᵖ` and so the retraction is
   continuous."

3. **Proposition 1.22** — "Let `D` be a dcpo with a continuous function space
   `[D → D]` and let `E` be a retract of `D`. Then `[E → E]` is a retract of
   `[D → D]` and hence a continuous dcpo." Two sub-results the development lacks:
   the retraction–embedding pair on function spaces, and "a retract of a
   continuous dcpo is continuous". `Projection.lean` and `NormalProjection.lean`
   carry projections but neither result.

4. **Interpolation, Proposition 1.8** — `x ≪ y` implies `x ≪ z ≪ y` for some `z`,
   in a continuous dcpo. Applied twice, to lift `x'' ≪ x` and `y'' ≪ y` to
   `x'' ≪ x' ≪ x` and `y'' ≪ y' ≪ y`. Zero occurrences of interpolation in
   `ScottDomains/`.

5. **The successor family `g_β`** — `g_β x = τ(f x)` for `x ∈ αᵒᵖ`, `x ≤ β`, and
   `x` otherwise, with `τ γ = γ + 1` the successor along the chain. These
   approximate `id_{D'}` but none dominates `f`, which contradicts `f ≪ id_{D'}`.
   This is the only part that is a proof script over machinery items 1–4 build.

Item 1 alone is a theorem of independent difficulty. Items 2 and 3 are new
developments over a sub-dcpo `D' = A ∪ αᵒᵖ` that must carry its own
`CompletePartialOrder` instance and its own function space.

## Mathlib survey, measured

Run before building anything, per the plan's step 2. Results, with the command
that produced each:

| Item | Present? | Measurement |
| ---- | -------- | ----------- |
| Zorn's lemma, upward | yes | `zorn_le₀`, `Mathlib/Order/Zorn.lean:110` |
| Zorn's lemma, downward | **no** | `grep -rn "zorn_ge" Mathlib/` → 0 hits; obtained here at `Dᵒᵈ`, exactly as `zorn_superset` (`Zorn.lean:152`) does |
| `Minimal`/`Maximal` duality | yes | `minimal_toDual`, `Mathlib/Order/Minimal.lean:73` |
| Iwamura's lemma (chain-complete ⟺ directed-complete) | **no** | `grep -rn "Iwamura\|Markowsky" Mathlib/` → 0 hits. `ChainCompletePartialOrder` exists (`Mathlib/Order/BourbakiWitt.lean:53`) with an instance to `OmegaCompletePartialOrder` but **none** to `CompletePartialOrder`; the implication is not in the library |
| Ordinal-indexed nets in a poset | **no** | `grep -rln "Ordinal" Mathlib/Order/` → 3 files, all unrelated (`InitialSeg`, `Extension/Well`, `Filter/Cocardinal`). There is no ordinal-indexed chain API for posets |
| Transfinite recursion | yes | `Ordinal.limitRecOn`, `Mathlib/SetTheory/Ordinal/Arithmetic.lean:158` |
| Codirected sets | partial | `IsCodirectedOrder` is a whole-type class (`Mathlib/Order/Directed.lean:194`); the set-level form is `DirectedOn (· ≥ ·)`, which is what `IsBicomplete` uses |
| `IsGLB` | yes | `Mathlib/Order/Bounds/Basic.lean` |

**Conclusion of the survey.** The Zorn half of the work is one Mathlib call. The
ordinal half is not expressible over existing Mathlib: item 1 of the obstruction
list is a missing theorem, not a missing notation, and items 2–5 would be built
on top of a chain API that Mathlib does not carry. That is the measured reason
this file proves Jung's "hence" and states Theorem 1.37 rather than proving it.

## The other source on disk

`ScottDomains/papers/Abramsky Jung Domain Theory 1994.pdf` §4.2–4.3 covers the
same classification (Theorem 4.3.4 is Jung's Theorem 2.14, Theorem 4.3.5 is
Smyth's Theorem 2.3) but gives **no proof of this step**: it routes through
coherence (Lemma 4.3.1, Lemma 4.3.2) and cites [Jun89] and [Jun90] for the
proofs. Its Exercise 4.3.11(1) is Jung's Theorem 1.35 and its Exercise 4.3.11(10)
— "Prove that FS-domains have infima for downward directed sets" — is the
bicompleteness statement, set as an exercise. So Jung 1989 is the only proof of
Theorem 1.37 on disk, and there is no cheaper route in the other paper.
-/

namespace ScottDomains.JungNets

open ScottDomains

/-! ## Bicompleteness, and infima of chains -/

section Order

variable {D : Type*} [Preorder D]

/-- **Jung 1989, §1.1, Definition.** A poset is *bicomplete* if it is a dcpo and
its order dual is a dcpo. Stated as the second half only — the types this is used
at already carry `CompletePartialOrder` — so: every **filtered** subset (nonempty,
and every pair has a lower bound in the set) has a greatest lower bound. -/
def IsBicomplete (D : Type*) [Preorder D] : Prop :=
  ∀ s : Set D, s.Nonempty → DirectedOn (· ≥ ·) s → ∃ i : D, IsGLB s i

/-- The weaker hypothesis that property m actually consumes: every nonempty
**chain** has a greatest lower bound.

Jung passes from filtered sets to chains via his Theorem 1.2 (Iwamura's lemma),
which is not available **in this module**; but the passage is only needed in the
direction `chains ⟹ filtered sets`, and this development never needs that
direction. Stating the results below over `HasChainInfima` makes them strictly
stronger and removes the dependency.

*Correction, r0049/agent8.* The clause read "which is not available here", read
package-wide by every later round. It is false package-wide: `Iwamura.lean`
proves Theorem 1.2 — `exists_chain_directed_cover` is Iwamura's lemma itself and
`hasDirectedSuprema_of_hasWellOrderedSuprema` is Markowsky's theorem — and
`Iwamura.jung_theorem_1_37_chains_iff_jung_theorem_1_37` makes the chain and filtered forms the same
proposition. `Iwamura.lean` imports this module, so the results are unavailable
*here* and only here. -/
def HasChainInfima (D : Type*) [Preorder D] : Prop :=
  ∀ c : Set D, c.Nonempty → IsChain (· ≤ ·) c → ∃ i : D, IsGLB c i

/-- A nonempty chain is filtered: of any two members one is below the other, and
it lies in the set. So bicompleteness gives infima of chains. -/
theorem IsBicomplete.hasChainInfima (h : IsBicomplete D) : HasChainInfima D := by
  intro c hne hc
  refine h c hne ?_
  intro x hx y hy
  rcases eq_or_ne x y with rfl | hxy
  · exact ⟨x, hx, le_rfl, le_rfl⟩
  · rcases hc hx hy hxy with hle | hle
    · exact ⟨x, hx, le_rfl, hle⟩
    · exact ⟨y, hy, hle, le_rfl⟩

/-- **Zorn's lemma downwards.** Mathlib has `zorn_le₀` (chains bounded above give
a maximal element) but no `zorn_ge₀`; this is its order dual, obtained by
instantiating `zorn_le₀` at `Dᵒᵈ` exactly as Mathlib's own `zorn_superset` does
(`Mathlib/Order/Zorn.lean:152`). `IsChain.symm` converts the dual order's chain
condition back to the original order's. -/
theorem exists_minimal_mem (s : Set D)
    (h : ∀ c ⊆ s, IsChain (· ≤ ·) c → ∃ lb ∈ s, ∀ z ∈ c, lb ≤ z) :
    ∃ m, Minimal (· ∈ s) m :=
  (@zorn_le₀ Dᵒᵈ _ s) fun c hcs hc => h c hcs hc.symm

/-- **Jung's "hence": property m from infima of chains.** For any subset `A` of
`D` and any upper bound `x` of `A`, some minimal upper bound of `A` lies below
`x` — Jung's property m, quantified over all of `D` and over arbitrary (not
merely finite) `A`.

This is the implication Jung asserts without proof in the proof of Theorem 2.3
("is bicomplete, hence `D` has property m") and again after Corollary 1.33 ("a
bifinite domain has a complete set of minimal upper bounds for arbitrary
subsets"). The proof is Zorn's lemma downwards inside `S = ub(A) ∩ ↓x`:

* the empty chain is bounded below in `S` by `x` itself, which is in `S`;
* a nonempty chain `c ⊆ S` has a greatest lower bound `i` by hypothesis. Each
  `a ∈ A` is a *lower* bound of `c`, because every member of `c` is an upper bound
  of `A`; so `a ≤ i` by the "greatest" half, and `i ∈ ub(A)`. And `i ≤ z ≤ x` for
  any member `z` of `c`, so `i ∈ S`.

Minimality inside `S` upgrades to minimality in `ub(A)`: an upper bound `y ≤ m`
satisfies `y ≤ m ≤ x`, so it was in `S` all along. -/
theorem exists_minimal_upperBounds_le (h : HasChainInfima D) (A : Set D) {x : D}
    (hx : x ∈ upperBounds A) :
    ∃ m, Minimal (· ∈ upperBounds A) m ∧ m ≤ x := by
  have key : ∀ c ⊆ {y : D | y ∈ upperBounds A ∧ y ≤ x}, IsChain (· ≤ ·) c →
      ∃ lb ∈ {y : D | y ∈ upperBounds A ∧ y ≤ x}, ∀ z ∈ c, lb ≤ z := by
    intro c hcs hc
    rcases c.eq_empty_or_nonempty with rfl | hne
    · exact ⟨x, ⟨hx, le_rfl⟩, fun z hz => absurd hz (Set.notMem_empty z)⟩
    · obtain ⟨i, hi⟩ := h c hne hc
      refine ⟨i, ⟨fun a ha => hi.2 fun z hz => (hcs hz).1 ha, ?_⟩, fun z hz => hi.1 hz⟩
      obtain ⟨z, hz⟩ := hne
      exact (hi.1 hz).trans (hcs hz).2
  obtain ⟨m, hm⟩ := exists_minimal_mem _ key
  exact ⟨m, ⟨hm.1.1, fun y hy hym => hm.2 ⟨hy, hym.trans hm.1.2⟩ hym⟩, hm.1.2⟩

/-- The same conclusion from bicompleteness, which is the form Theorem 1.37
delivers it in. -/
theorem IsBicomplete.exists_minimal_upperBounds_le (h : IsBicomplete D) (A : Set D) {x : D}
    (hx : x ∈ upperBounds A) :
    ∃ m, Minimal (· ∈ upperBounds A) m ∧ m ≤ x :=
  _root_.ScottDomains.JungNets.exists_minimal_upperBounds_le h.hasChainInfima A hx

end Order

/-! ## The bridge to `HasCompleteMub` -/

section Algebraic

variable {D : Type*} [CompletePartialOrder D] [IsAlgebraic D]

/-- **Property m in the development's relative form.** `HasCompleteMub (compacts D) u`
quantifies over upper bounds *inside* `compacts D` and asks for a minimal upper
bound *inside* `compacts D`; the previous theorem quantifies over all of `D`. For
a finite set of compact elements in an algebraic dcpo the two agree, by
`JungSFP.mem_minimalUpperBounds_of_minimal` (Jung's Proposition 1.9 and its
converse). So this is exactly `jung_lemma_2_17`'s hypothesis, discharged. -/
theorem hasCompleteMub_of_hasChainInfima (h : HasChainInfima D) {u : Set D}
    (hu : u.Finite) (huc : u ⊆ compacts D) : HasCompleteMub (compacts D) u := by
  intro z hz
  obtain ⟨m, hmin, hmz⟩ := exists_minimal_upperBounds_le h u hz.2
  exact ⟨m, JungSFP.mem_minimalUpperBounds_of_minimal hu huc hmin, hmz⟩

/-- The instance at a pair of compact elements — the exact hypothesis
`JungSFP.jung_lemma_2_17` carries. -/
theorem hasCompleteMub_pair (h : HasChainInfima D) {a₁ a₂ : D}
    (ha₁ : IsCompactElement a₁) (ha₂ : IsCompactElement a₂) :
    HasCompleteMub (compacts D) ({a₁, a₂} : Set D) :=
  hasCompleteMub_of_hasChainInfima h (Set.toFinite _)
    (by rintro y (rfl | rfl) <;> assumption)

end Algebraic

/-! ## Theorem 1.37 as a named remainder, and what it discharges -/

section Theorem137

variable {D : Type*} [CompletePartialOrder D]

/-- **Jung 1989, Theorem 1.37**, as a proposition about `D`.

> A dcpo with continuous function space is bicomplete.

Stated with `IsAlgebraic (ScottHom D D)` in place of Jung's "continuous function
space", because no predicate for a continuous dcpo is available **in this
module**; algebraic implies continuous, so this is the weaker proposition, and it
is the one Theorem 18 consumes. **This is not proved here.** No `sorry` stands in
for it: it appears only as an explicit hypothesis of the theorems below. See the
module docstring for the five-item dependency list its proof needs and for the
Mathlib survey showing that the first item — Iwamura's lemma, Jung's Theorem 1.2
— is absent from **Mathlib**.

*Correction, r0049/agent8.* Three clauses were stale, each in the same way: they
stated a fact about this module as a fact about the development.

1. "the development has no predicate for a continuous dcpo" —
   `JungBicomplete.IsContinuousDcpo` is one, with
   `isContinuousDcpo_of_isAlgebraic`.
2. "**This is not proved.**" — `R45.Agent5.jung_theorem_1_37` proves `Theorem137 D` for every
   `D` with `[CompletePartialOrder D] [Domain D]`. That is a discharge **at** an
   added instance binder and not of the `def` as written, which quantifies over
   `[CompletePartialOrder D]` alone; the open case is the non-algebraic one.
   `PropertyM.forall_hasCompleteMub` additionally removes `Theorem137` from the route
   to Theorem 18 entirely.
3. "absent from the library" — the library meant is Mathlib, and there the survey
   stands (r0046 confirmed `JungNets.lean:102` TRUE). It is not absent from this
   development: `Iwamura.lean` proves it. -/
def Theorem137 (D : Type*) [CompletePartialOrder D] : Prop :=
  IsAlgebraic (ScottHom D D) → IsBicomplete D

/-- **The minimal remaining obligation**, weaker than `Theorem137`: infima of nonempty
*chains* rather than of all filtered sets.

Everything below factors through this, because Zorn's lemma quantifies over chains
— see `exists_minimal_upperBounds_le`. Stating it separately measures how much of
Theorem 1.37 the route to Theorem 18 actually spends: not the full dual
directed-completeness, only its restriction to chains. A later round proving
either one discharges every theorem in this file. -/
def Theorem137Chains (D : Type*) [CompletePartialOrder D] : Prop :=
  IsAlgebraic (ScottHom D D) → HasChainInfima D

theorem Theorem137.toChains (h : Theorem137 D) : Theorem137Chains D :=
  fun hAlg => (h hAlg).hasChainInfima

variable [IsAlgebraic D]

/-- **The first conjunct of `isBifinite_iff_mubClosure`, reduced to Theorem 1.37.**

`MinimalUpperBounds.isBifinite_iff_mubClosure` splits bifiniteness of `D` into

* `∀ v, v.Finite → v ⊆ compacts D → HasCompleteMub (compacts D) v` — property m;
* `∀ u, u.Finite → u ⊆ compacts D → (mubClosure (compacts D) u).Finite` — Jung's
  Lemma 2.2, which is step 4.

This theorem is the first of the two, modulo `Theorem137`. It is the shape the
Theorem 18 assembly consumes, so nothing downstream has to restate it. -/
theorem forall_hasCompleteMub_of_jung_theorem_1_37 (h : Theorem137 D)
    (hAlg : IsAlgebraic (ScottHom D D)) :
    ∀ v : Set D, v.Finite → v ⊆ compacts D → HasCompleteMub (compacts D) v :=
  fun _ hv hvc => hasCompleteMub_of_hasChainInfima (h.toChains hAlg) hv hvc

/-- **`JungSFP.jung_lemma_2_17` with its property-m hypothesis discharged.**

`jung_lemma_2_17` was left carrying `HasCompleteMub (compacts D) {a₁, a₂}` as an explicit
hypothesis because Jung's Theorem 1.37 was absent. This is the same statement with
that hypothesis replaced by `Theorem137 D`, and the proof is one application — the
shapes agree, so `JungSFP.lean` needed no edit. -/
theorem jung_lemma_2_17_of_jung_theorem_1_37 (h : Theorem137 D)
    (hAlg : IsAlgebraic (ScottHom D D))
    (hCount : (compacts (ScottHom D D)).Countable)
    {a₁ a₂ : D} (ha₁ : IsCompactElement a₁) (ha₂ : IsCompactElement a₂) :
    (minimalUpperBounds (compacts D) ({a₁, a₂} : Set D)).Finite :=
  JungSFP.jung_lemma_2_17 hAlg hCount ha₁ ha₂
    (hasCompleteMub_pair (h.toChains hAlg) ha₁ ha₂)

/-- **Property M at every pair of compact elements**, modulo `Theorem137` and
countability of `K(D → D)` — the first disjunct of `JungSFP.jung_theorem_2_14`, proved
outright rather than as a disjunct.

Jung's Lemma 1.29 ("a poset with property m has property M if and only if the
empty set and each pair of elements have a finite set of minimal upper bounds")
lifts this from pairs to all finite sets; that is agent1's stream, and this is the
input it takes. -/
theorem propertyM_pairs_of_jung_theorem_1_37 (h : Theorem137 D)
    (hAlg : IsAlgebraic (ScottHom D D))
    (hCount : (compacts (ScottHom D D)).Countable) :
    ∀ x₁ x₂ : D, IsCompactElement x₁ → IsCompactElement x₂ →
      (minimalUpperBounds (compacts D) ({x₁, x₂} : Set D)).Finite :=
  fun _ _ hx₁ hx₂ => jung_lemma_2_17_of_jung_theorem_1_37 h hAlg hCount hx₁ hx₂

end Theorem137

end ScottDomains.JungNets
