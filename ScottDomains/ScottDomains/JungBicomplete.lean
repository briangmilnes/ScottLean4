import ScottDomains.JungNets
import ScottDomains.FunctionSpaceDomain
import ScottDomains.FinitaryProjectionPoset

/-!
# Jung's Theorem 1.37: the ingredients that are order theory

`ScottDomains/JungNets.lean` states Jung's **Theorem 1.37** — *a dcpo with
continuous function space is bicomplete* — as the unproved `Prop` `Thm137`, and
lists five ingredients its proof needs. This file proves the three of them that
are order theory over what the development already has, and states the two that
are not.

Everything below is read off pages 18, 31 and 50–51 of
`ScottDomains/papers/Jung 1989 Cartesian Closed Categories of Domains.pdf`,
quoted rather than paraphrased.

## Jung's proof, quoted in full (p. 50–51)

> **Theorem 1.37** A dcpo with continuous function space is bicomplete.
>
> *Proof.* By Corollary 1.3 we have to find infima only for monotone injective
> nets `s: αᵒᵖ → D` where `α` is an ordinal number. To simplify notation let us
> identify the ordinal with its image in `D`. Denote by `A` the (possibly empty)
> set of lower bounds for `αᵒᵖ` in `D`. We define a retraction onto `A ∪ αᵒᵖ`:
> `r(x) = x` if `x ∈ A`; `r(x) = ⋀{γ ∈ αᵒᵖ | γ ≥ x}` otherwise. Since `α` is an
> ordinal there exists no strictly increasing infinite sequence in `αᵒᵖ` and so
> the retraction is continuous. We apply Proposition 1.22 and get that the
> function space of `D′ = A ∪ αᵒᵖ` is again continuous.
>
> Assume now that the infimum of `αᵒᵖ` does not exist, that is, the set `A` does
> not have a largest element. Then the set `↡A` cannot be directed. If `A` is not
> empty then we find `x″ ≪ x ∈ A` and `y″ ≪ y ∈ A` such that there is no upper
> bound for `{x″, y″}` in `↡A`. By interpolating we find elements `x′, y′` such
> that `x″ ≪ x′ ≪ x` and `y″ ≪ y′ ≪ y`. For `{x′, y′}` there cannot be an upper
> bound even in `A`. By continuity of the function space of `D′` there is a
> function `f` on `D′` which is way-below `id_{D′}` and which maps `x` above `x′`
> and `y` above `y′`. All elements of `αᵒᵖ` are upper bounds for `{x′, y′}` so by
> construction `αᵒᵖ` is mapped into itself under `f`. If `A` is empty this is
> trivially the case.
>
> We proceed by showing that a function `f` which maps `αᵒᵖ` into itself cannot
> be way-below `id_{D′}`. This contradiction will finish our proof. Consider the
> successor function `τ` on `αᵒᵖ`, defined by `τ(γ) = γ + 1`. The functions
> `g_β(x) = τ ∘ f(x)` if `x ∈ αᵒᵖ, x ≤ β`, and `x` otherwise, approximate
> `id_{D′}` but none of them dominates `f`. ∎

## What is proved here

| # | Jung | Declaration |
| -- | ---- | ----------- |
| 1 | §1.2 definition of a *continuous* dcpo | `IsContinuousDcpo` |
| 2 | algebraic ⟹ continuous (§1.2 remark) | `isContinuousDcpo_of_isAlgebraic` |
| 3 | **Proposition 1.8**, interpolation | `IsContinuousDcpo.exists_wayBelow_wayBelow` |
| 4 | §1.3 definition of a retraction–embedding pair | `IsRetractPair` |
| 5 | a retract of a continuous dcpo is continuous | `IsContinuousDcpo.of_retractPair` |
| 6 | **Proposition 1.22** | `sandwichHom`, `IsRetractPair.sandwichHom`, `prop122` |
| 7 | the second paragraph of the proof above, entire | `exists_isGLB_of_forall_not_mapsTo` |

Item 7 is the whole middle of Jung's proof: from "the infimum of `αᵒᵖ` does not
exist" to "`αᵒᵖ` is mapped into itself under `f`", with `f ≪ id_{D′}`. It is
stated over an abstract dcpo `D′` covered by `lowerBounds C ∪ C`, so a later
round instantiates it at `D′ = A ∪ αᵒᵖ` rather than reproving it. Its two
sub-steps are `exists_isGLB_of_directedOn_wayBelowLower` (Jung's "then the set
`↡A` cannot be directed", contraposed) and `mapsTo_of_forall_not_upperBound`
(his "so by construction `αᵒᵖ` is mapped into itself").

## What is not proved, and why

Two ingredients, both needing the ordinal.

* **Corollary 1.3** — "By Corollary 1.3 we have to find infima only for monotone
  injective nets `s: αᵒᵖ → D`". Jung's Corollary 1.3 is a corollary of his
  Theorem 1.2, Iwamura's lemma, which he does not prove and Mathlib does not
  carry (`JungNets.lean` records the measurement: 0 hits for `Iwamura|Markowsky`
  in `Mathlib/`). This is agent2's stream; it is a hypothesis of everything here
  in the sense that nothing here reduces filtered sets to well-ordered chains.

* **The `g_β` family** — "a function `f` which maps `αᵒᵖ` into itself cannot be
  way-below `id_{D′}`". This is the hypothesis
  `∀ f : ScottHom D' D', f ≪ ScottHom.id → ¬ ∀ γ ∈ C, f γ ∈ C` of
  `exists_isGLB_of_forall_not_mapsTo`. It needs `τ(γ) = γ + 1`, so it needs `C`
  to *be* a well-ordered chain and not merely a set — the one place in Jung's
  proof where the ordinal is used for more than notation.

* **The retraction `r` onto `A ∪ αᵒᵖ`** is what supplies
  `exists_isGLB_of_forall_not_mapsTo`'s `hcover` hypothesis and, through
  `prop122`, its `IsContinuousDcpo (ScottHom D' D')`. It is not built here; see
  the defect below.

## Corrections to `JungNets.lean`'s obstruction list, from the source

Four, all found by reading pp. 18, 31 and 50–51 against that list.

1. **`r` as Jung writes it is not total.** `JungNets.lean` item 2 records that
   `⋀{γ ∈ αᵒᵖ | γ ≥ x}` needs a transfinite induction to exist. There is a
   second, independent defect: that set is **empty** whenever `x` is not below
   the largest element of the chain — `αᵒᵖ`'s largest element is `s(0)`, and
   `x ≰ s(0)` puts nothing in `{γ | γ ≥ x}`. In a dcpo without a top there is no
   `⋀∅`. Jung's two-case formula therefore needs a third case, and the obvious
   repair (send such `x` to `s(0)`) keeps `r` monotone but has to be checked
   against continuity separately.

2. **What interpolation buys is specific.** `JungNets.lean` item 4 says
   interpolation is "applied twice"; it does not say to what end. Jung's use is
   exactly to convert *no upper bound of `{x″, y″}` in `↡A`* into *no upper bound
   of `{x′, y′}` in `A`* — the second is what the final step consumes, the first
   is what non-directedness of `↡A` yields, and interpolation is the only bridge.
   `exists_isGLB_of_forall_not_mapsTo` contains that conversion.

3. **Proposition 1.22's "hence a continuous dcpo" is not Proposition 1.16.**
   Prop 1.16 concerns `im(r)` for a retraction `r : D → D` on one dcpo; Prop 1.22
   concerns a retract `E` given by a retraction–embedding pair `r : D → E`,
   `i : E → D` between two. `IsContinuousDcpo.of_retractPair` proves the pair
   form directly rather than transporting Prop 1.16 across an isomorphism.

4. **Jung's "If `A` is empty" branch is vacuous here.** `A = lowerBounds C` and
   `CompletePartialOrder` extends `OrderBot`, so `⊥ ∈ A` always. The branch is
   kept in the quotation for fidelity and is never taken.

## Deviation from Jung's hypothesis

Jung assumes "`D` has a continuous function space" and derives continuity of `D`
itself from it (Theorem 1.35, via Proposition 1.34 — agent1's stream). This file
takes continuity of `D′` as a hypothesis (`IsContinuousDcpo D'`) alongside
continuity of `[D′ → D′]` rather than deriving it, because Proposition 1.34 is
not on disk. `isContinuousDcpo_of_isAlgebraic` discharges it whenever the domain
at hand is algebraic, which is the case `Thm137` is consumed in.
-/

namespace ScottDomains.JungBicomplete

open ScottDomains

/-! ## Continuous dcpo's and interpolation (Jung §1.2, Proposition 1.8) -/

section Continuous

variable {D : Type*} [CompletePartialOrder D]

/-- Jung's `↡x = {y ∈ D | y ≪ x}` (§1.2, "For an element `x ∈ D` we define the
following subsets"). The development already has `≪`; this is the set form. -/
def wayBelowSet (x : D) : Set D := {y | y ≪ x}

@[simp] theorem mem_wayBelowSet {x y : D} : y ∈ wayBelowSet x ↔ y ≪ x := Iff.rfl

/-- `↡x` is never empty: `⊥ ≪ x`, and `CompletePartialOrder` extends `OrderBot`.
Jung's definition of *directed* forces nonemptiness; Mathlib's `DirectedOn` does
not, so it is carried separately. -/
theorem wayBelowSet_nonempty (x : D) : (wayBelowSet x).Nonempty :=
  ⟨⊥, bot_wayBelow x⟩

/-- **Jung 1989, §1.2, Definition.**

> We say that a dcpo `D` is continuous, if for all `x ∈ D` the set `↡x` is
> directed and `⋁↑↡x = x`.

The development has `IsAlgebraic` but no predicate for a *continuous* dcpo, which
is what `JungNets.lean` records as the reason `Thm137` is stated with the
stronger `IsAlgebraic (ScottHom D D)` in place of Jung's hypothesis. This is that
predicate. -/
def IsContinuousDcpo (D : Type*) [CompletePartialOrder D] : Prop :=
  ∀ x : D, DirectedOn (· ≤ ·) (wayBelowSet x) ∧ IsLUB (wayBelowSet x) x

theorem IsContinuousDcpo.directedOn (h : IsContinuousDcpo D) (x : D) :
    DirectedOn (· ≤ ·) (wayBelowSet x) := (h x).1

theorem IsContinuousDcpo.isLUB (h : IsContinuousDcpo D) (x : D) :
    IsLUB (wayBelowSet x) x := (h x).2

/-- **Every algebraic dcpo is continuous** (Jung §1.2: "Every algebraic dcpo is
also a continuous dcpo but the converse does not hold").

Both halves go through `Domain.lean`'s `wayBelow_iff_exists_compact`, which is
where algebraicity is spent: `y ≪ x` iff `y` factors through a compact `k ≤ x`.
Directedness of `↡x` then reduces to directedness of `compactsBelow x`, and the
least-upper-bound half to `IsAlgebraic.isLUB_compactsBelow`, because every
compact `k ≤ x` is itself a member of `↡x`. -/
theorem isContinuousDcpo_of_isAlgebraic [IsAlgebraic D] : IsContinuousDcpo D := by
  have hmem : ∀ {k x : D}, IsCompactElement k → k ≤ x → k ∈ wayBelowSet x :=
    fun hk hkx => wayBelow_of_isCompactElement hk le_rfl hkx
  intro x
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb
    obtain ⟨k₁, hk₁, hak₁, hk₁x⟩ := wayBelow_iff_exists_compact.mp ha
    obtain ⟨k₂, hk₂, hbk₂, hk₂x⟩ := wayBelow_iff_exists_compact.mp hb
    obtain ⟨k, hk, h₁, h₂⟩ :=
      IsAlgebraic.directedOn_compactsBelow x k₁ ⟨hk₁, hk₁x⟩ k₂ ⟨hk₂, hk₂x⟩
    exact ⟨k, hmem hk.1 hk.2, hak₁.trans h₁, hbk₂.trans h₂⟩
  · intro a ha
    exact WayBelow.le ha
  · intro u hu
    exact (IsAlgebraic.isLUB_compactsBelow x).2 fun k hk => hu (hmem hk.1 hk.2)

/-- **Jung 1989, Proposition 1.8** (interpolation).

> Let `D` be a continuous dcpo and let `x, y` be elements of `D`. If `x` is
> way-below `y` then there is `z ∈ D` such that `x ≪ z ≪ y` holds.

Jung's proof verbatim, with one simplification. He takes
`A = {a | ∃ a′, a ≪ a′ ≪ y}` and shows it directed with supremum `y`; then
`x ≪ y` produces `a ∈ A` above `x`, and `x ≤ a ≪ a′` gives `x ≪ a′ ≪ y`.

* *directed*: given `a ≪ a′ ≪ y` and `b ≪ b′ ≪ y`, directedness of `↡y` supplies
  `c′ ≪ y` above `a′` and `b′`; then `a, b ∈ ↡c′` and directedness of `↡c′`
  supplies `c ≪ c′` above both, and `c ∈ A`.
* *supremum `y`*: every member of `A` is `≤ y`; and an upper bound `u` of `A`
  bounds `↡y′` for each `y′ ≪ y`, hence bounds each such `y′`, hence bounds `↡y`,
  hence `y ≤ u`.

The simplification is nonemptiness: Jung leaves it implicit, and it is `⊥ ≪ ⊥ ≪ y`
here rather than an argument, because `CompletePartialOrder` is pointed. -/
theorem IsContinuousDcpo.exists_wayBelow_wayBelow (hD : IsContinuousDcpo D) {x y : D}
    (h : x ≪ y) : ∃ z, x ≪ z ∧ z ≪ y := by
  set A : Set D := {a | ∃ a', a ≪ a' ∧ a' ≪ y} with hAdef
  have hAne : A.Nonempty := ⟨⊥, ⊥, bot_wayBelow (⊥ : D), bot_wayBelow y⟩
  have hAdir : DirectedOn (· ≤ ·) A := by
    rintro a ⟨a', haa', ha'y⟩ b ⟨b', hbb', hb'y⟩
    obtain ⟨c', hc'y, ha'c, hb'c⟩ := hD.directedOn y a' ha'y b' hb'y
    obtain ⟨c, hcc', hac, hbc⟩ :=
      hD.directedOn c' a (haa'.trans_le ha'c) b (hbb'.trans_le hb'c)
    exact ⟨c, ⟨c', hcc', hc'y⟩, hac, hbc⟩
  have hAlub : IsLUB A y := by
    constructor
    · rintro a ⟨a', haa', ha'y⟩
      exact haa'.le.trans ha'y.le
    · intro u hu
      refine (hD.isLUB y).2 fun y' hy' => ?_
      exact (hD.isLUB y').2 fun z hz => hu ⟨y', hz, hy'⟩
  obtain ⟨a, ⟨a', haa', ha'y⟩, hxa⟩ := h A y hAne hAdir hAlub le_rfl
  exact ⟨a', hxa.trans_wayBelow haa', ha'y⟩

/-- **The bridge to `JungNets.Thm137`'s hypothesis.** `Thm137 D` reads
`IsAlgebraic (ScottHom D D) → IsBicomplete D`, the antecedent standing in for
Jung's "continuous function space" because the development had no predicate for a
continuous dcpo. It now has one, and the antecedent implies it — so the `hFS`
hypothesis of `exists_isGLB_of_forall_not_mapsTo` and of `prop122` is exactly
what `Thm137` hands over, with no gap and no further deviation.

Stated with the algebraicity as an explicit argument rather than an instance,
because that is how `Thm137` carries it. -/
theorem isContinuousDcpo_scottHom_of_isAlgebraic (h : IsAlgebraic (ScottHom D D)) :
    IsContinuousDcpo (ScottHom D D) :=
  @isContinuousDcpo_of_isAlgebraic _ _ h

/-- A witness that `IsContinuousDcpo` is satisfiable. `Domain.lean` makes the
point: a `Prop`-valued definition with no inhabitant is unfalsifiable, and an
error in either conjunct would go undetected. `Prop` is the cheapest witness. -/
example : IsContinuousDcpo Prop := isContinuousDcpo_of_isAlgebraic

end Continuous

/-! ## Retracts, and Proposition 1.22 -/

section Retract

variable {D E : Type*} [CompletePartialOrder D] [CompletePartialOrder E]

/-- **Jung 1989, §1.3, Definition.**

> Continuous functions `r: D → E` and `e: E → D` are said to form a
> retraction–embedding pair, if `r ∘ e` equals the identity function on `E`. …
> If there is a retraction-embedding pair between `D` and `E`, the retraction
> mapping `D` onto `E`, we say that `E` is a retract of `D`.

Stated pointwise, following `Projection.lean`'s `IsEmbeddingProjectionPair`.
Weaker than that predicate: no `e ∘ r ⊑ id_D`, because Jung's retracts are not
required to be projections and Proposition 1.22 does not use the inequality. -/
def IsRetractPair (r : ScottHom D E) (i : ScottHom E D) : Prop := ∀ y : E, r (i y) = y

/-- Every dcpo is a retract of itself. The witness that `IsRetractPair` is
satisfiable, and the degenerate instance of Proposition 1.22. -/
theorem isRetractPair_id : IsRetractPair (ScottHom.id : ScottHom D D) ScottHom.id :=
  fun _ => rfl

variable {r : ScottHom D E} {i : ScottHom E D}

/-- **A retract of a continuous dcpo is continuous.** This is the second half of
Jung's Proposition 1.22 ("and hence a continuous dcpo"). His Proposition 1.16
gives it for the image of a retraction `D → D`; this is the retraction–embedding
form, proved directly rather than by transporting 1.16 across an isomorphism.

The whole proof runs through one set: `S y = r '' ↡(i y)`.

* `S y ⊆ ↡y`. Given `a ≪ i y`, take `s ⊆ E` directed with least upper bound
  `u ≥ y`. Continuity of `i` makes `i '' s` directed with least upper bound
  `i u ≥ i y`, so `a ≤ i t` for some `t ∈ s`, and then `r a ≤ r (i t) = t`.
* `S y` is directed, being a monotone image of the directed set `↡(i y)`.
* `S y` has least upper bound `y`: continuity of `r` carries
  `IsLUB (↡(i y)) (i y)` to `IsLUB (S y) (r (i y))`, and `r (i y) = y`.

Those three make `S y` a directed subset of `↡y` cofinal in it, which is exactly
what both halves of `IsContinuousDcpo` need. -/
theorem IsContinuousDcpo.of_retractPair (h : IsRetractPair r i) (hD : IsContinuousDcpo D) :
    IsContinuousDcpo E := by
  have hsub : ∀ y : E, ⇑r '' wayBelowSet (i y) ⊆ wayBelowSet y := by
    rintro y _ ⟨a, ha, rfl⟩ s u hne hd hlub hyu
    obtain ⟨_, ⟨t, ht, rfl⟩, hat⟩ :=
      ha (⇑i '' s) (i u) (hne.image _) (ScottHom.directedOn_image i hd)
        (i.scottContinuous hne hd hlub) (i.monotone hyu)
    exact ⟨t, ht, (h t) ▸ r.monotone hat⟩
  have hdir : ∀ y : E, DirectedOn (· ≤ ·) (⇑r '' wayBelowSet (i y)) :=
    fun y => ScottHom.directedOn_image r (hD.directedOn (i y))
  have hlub : ∀ y : E, IsLUB (⇑r '' wayBelowSet (i y)) y := by
    intro y
    have := r.scottContinuous (wayBelowSet_nonempty (i y)) (hD.directedOn (i y))
      (hD.isLUB (i y))
    rwa [h y] at this
  have hne : ∀ y : E, (⇑r '' wayBelowSet (i y)).Nonempty :=
    fun y => (wayBelowSet_nonempty (i y)).image _
  intro y
  refine ⟨?_, ?_, ?_⟩
  · intro b₁ hb₁ b₂ hb₂
    obtain ⟨c₁, hc₁, h₁⟩ := hb₁ _ y (hne y) (hdir y) (hlub y) le_rfl
    obtain ⟨c₂, hc₂, h₂⟩ := hb₂ _ y (hne y) (hdir y) (hlub y) le_rfl
    obtain ⟨c, hc, hc₁c, hc₂c⟩ := hdir y c₁ hc₁ c₂ hc₂
    exact ⟨c, hsub y hc, h₁.trans hc₁c, h₂.trans hc₂c⟩
  · intro b hb
    exact WayBelow.le hb
  · intro u hu
    exact (hlub y).2 fun z hz => hu (hsub y hz)

/-- `(f : D → D) ↦ r ∘ f ∘ i`, the operator of Jung's Proposition 1.22. One
definition serves both directions of that proposition: `sandwich i r` is his `R`
and `sandwich r i` is his `I`, the two differing only by swapping `D` and `E`.

`Skeleton/Lemma17.lean`'s `compFun` is the endomorphic special case `q ∘ f ∘ p`
with `p : D → D`, `q : E → E`; it cannot be reused, because Proposition 1.22
needs the two sides of the sandwich to change the *type*. -/
def sandwich (i : ScottHom E D) (r : ScottHom D E) (f : ScottHom D D) : ScottHom E E :=
  ⟨⇑r ∘ ⇑f ∘ ⇑i,
    ScottContinuous.comp (ScottContinuous.comp i.scottContinuous f.scottContinuous)
      r.scottContinuous⟩

@[simp] theorem sandwich_apply (i : ScottHom E D) (r : ScottHom D E) (f : ScottHom D D)
    (y : E) : sandwich i r f y = r (f (i y)) := rfl

/-- `f ↦ r ∘ f ∘ i` is itself Scott continuous on `[D → D]`. Suprema in a function
space are pointwise, so at each `y` the claim is continuity of `r` applied to the
evaluation image of `d` at `i y` — the argument of
`Skeleton/Lemma17.lean`'s `scottContinuous_compFun`, with `p` replaced by the
type-changing `i`. -/
theorem scottContinuous_sandwich (i : ScottHom E D) (r : ScottHom D E) :
    ScottContinuous (sandwich i r) := by
  intro d hne hd F hF
  constructor
  · rintro _ ⟨f, hf, rfl⟩ y
    exact r.monotone (hF.1 hf (i y))
  · intro G hG y
    have hrlub : IsLUB (⇑r '' ((fun f : ScottHom D D => f (i y)) '' d)) (r (F (i y))) :=
      r.scottContinuous (hne.image _) (ScottHom.directedOn_eval_image hd (i y))
        (ScottHom.isLUB_eval_image_of_isLUB hd hF (i y))
    refine hrlub.2 ?_
    rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    exact hG ⟨f, hf, rfl⟩ y

/-- `R(f) = r ∘ f ∘ i` as an element of `[[D → D] → [E → E]]`. -/
noncomputable def sandwichHom (i : ScottHom E D) (r : ScottHom D E) :
    ScottHom (ScottHom D D) (ScottHom E E) :=
  ⟨sandwich i r, scottContinuous_sandwich i r⟩

@[simp] theorem sandwichHom_apply (i : ScottHom E D) (r : ScottHom D E) (f : ScottHom D D)
    (y : E) : sandwichHom i r f y = r (f (i y)) := rfl

/-- **Jung 1989, Proposition 1.22, first half.**

> `[E → E]` is a retract of `[D → D]`.

His proof verbatim: "`R ∘ I(g) = r ∘ i ∘ g ∘ r ∘ i = g`, so `(R, I)` is a
retraction–embedding pair." Two applications of `r ∘ i = id_E`, one at `y` and
one at `g y`. -/
theorem IsRetractPair.sandwichHom (h : IsRetractPair r i) :
    IsRetractPair (JungBicomplete.sandwichHom i r) (JungBicomplete.sandwichHom r i) := by
  intro g
  ext y
  show r (i (g (r (i y)))) = g y
  rw [h y, h (g y)]

/-- **Jung 1989, Proposition 1.22.**

> Let `D` be a dcpo with a continuous function space `[D → D]` and let `E` be a
> retract of `D`. Then `[E → E]` is a retract of `[D → D]` and hence a continuous
> dcpo.

The two halves composed: the function-space retraction pair, then "a retract of a
continuous dcpo is continuous". This is the step Jung applies to `D′ = A ∪ αᵒᵖ`
in the proof of Theorem 1.37, and it is the one of that proof's five ingredients
that costs nothing beyond the function space the development already has. -/
theorem prop122 (h : IsRetractPair r i) (hFS : IsContinuousDcpo (ScottHom D D)) :
    IsContinuousDcpo (ScottHom E E) :=
  IsContinuousDcpo.of_retractPair h.sandwichHom hFS

end Retract

/-! ## The second paragraph of Jung's proof -/

section Endgame

variable {D : Type*} [CompletePartialOrder D]

/-- Jung's `↡A = ⋃_{a ∈ A} ↡a` (§1.2: "For `A` a subset of `D` we define … `↡A`").
It is the set his Theorem 1.37 shows cannot be directed. -/
def wayBelowLower (A : Set D) : Set D := {z | ∃ a ∈ A, z ≪ a}

@[simp] theorem mem_wayBelowLower {A : Set D} {z : D} :
    z ∈ wayBelowLower A ↔ ∃ a ∈ A, z ≪ a := Iff.rfl

/-- **"Then the set `↡A` cannot be directed"**, contraposed: if `↡(lb C)` *is*
directed then `C` has an infimum.

`D` is a dcpo, so the directed set `L = ↡(lb C)` has a least upper bound `⨆L`,
and that bound is the infimum of `C`:

* `⨆L ∈ lb C`. Each `γ ∈ C` bounds `L` above, because `z ≪ a ∈ lb C` gives
  `z ≤ a ≤ γ`; so `⨆L ≤ γ` by leastness.
* `⨆L` is the greatest such. For `a ∈ lb C`, continuity gives `IsLUB (↡a) a`, and
  `⨆L` bounds `↡a` above since `↡a ⊆ L`; so `a ≤ ⨆L`.

Contraposing, "`A` has no largest element" — which is Jung's reading of "the
infimum of `αᵒᵖ` does not exist", and is literally `¬ ∃ i, IsGLB C i`, since a
largest element of `lowerBounds C` *is* a greatest lower bound of `C` — yields
non-directedness of `↡A`. -/
theorem exists_isGLB_of_directedOn_wayBelowLower (hD : IsContinuousDcpo D) {C : Set D}
    (h : DirectedOn (· ≤ ·) (wayBelowLower (lowerBounds C))) : ∃ i, IsGLB C i := by
  refine ⟨sSup (wayBelowLower (lowerBounds C)), fun γ hγ => ?_, fun a ha => ?_⟩
  · refine h.isLUB_sSup.2 ?_
    rintro z ⟨a, ha, hza⟩
    exact hza.le.trans (ha hγ)
  · exact (hD.isLUB a).2 fun z hz => h.isLUB_sSup.1 ⟨a, ha, hz⟩

/-- **"All elements of `αᵒᵖ` are upper bounds for `{x′, y′}` so by construction
`αᵒᵖ` is mapped into itself under `f`."**

`D` is covered by `lowerBounds C ∪ C` — this is what "`D′ = A ∪ αᵒᵖ`" says — and
`{x', y'}` has no upper bound in `lowerBounds C`. For `γ ∈ C`: `x ≤ γ` and
`y ≤ γ` because `x, y ∈ lowerBounds C`, so monotonicity of `f` gives
`x' ≤ f x ≤ f γ` and `y' ≤ f y ≤ f γ`. So `f γ` is an upper bound of `{x', y'}`,
which rules out `f γ ∈ lowerBounds C`, and the cover leaves only `f γ ∈ C`.

Stated for a bare monotone function on a preorder: nothing here needs
completeness, continuity, or `f ≪ id`. -/
theorem mapsTo_of_forall_not_upperBound {D' : Type*} [Preorder D'] {C : Set D'}
    {f : D' → D'} (hf : Monotone f) (hcover : ∀ z : D', z ∈ lowerBounds C ∨ z ∈ C)
    {x y x' y' : D'} (hx : x ∈ lowerBounds C) (hy : y ∈ lowerBounds C)
    (hfx : x' ≤ f x) (hfy : y' ≤ f y)
    (hno : ∀ a ∈ lowerBounds C, ¬(x' ≤ a ∧ y' ≤ a)) :
    ∀ γ ∈ C, f γ ∈ C := by
  intro γ hγ
  rcases hcover (f γ) with hlb | hmem
  · exact absurd ⟨hfx.trans (hf (hx hγ)), hfy.trans (hf (hy hγ))⟩ (hno _ hlb)
  · exact hmem

/-- **Jung 1989, Theorem 1.37, second paragraph, entire.**

Let `D′` be a continuous dcpo with continuous function space, covered by
`lowerBounds C ∪ C`. If no `f ≪ id_{D′}` maps `C` into itself, then `C` has an
infimum.

This is Jung's argument from "Assume now that the infimum of `αᵒᵖ` does not
exist" to "so by construction `αᵒᵖ` is mapped into itself under `f`", run as a
proof by contradiction and packaged so that the remaining hypothesis is exactly
the third paragraph — the `g_β` family, the only step that uses the ordinal.

The seven steps, in Jung's order:

1. No infimum means `lowerBounds C` has no largest element.
2. Hence `↡(lb C)` is not directed
   (`exists_isGLB_of_directedOn_wayBelowLower`, contraposed).
3. So there are `x″ ≪ x ∈ lb C` and `y″ ≪ y ∈ lb C` with no upper bound for
   `{x″, y″}` in `↡(lb C)`.
4. Interpolate (Proposition 1.8): `x″ ≪ x′ ≪ x` and `y″ ≪ y′ ≪ y`.
5. Then `{x′, y′}` has no upper bound even in `lb C`: an upper bound `a` there
   would give `x″ ≪ a` and `y″ ≪ a`, and directedness of `↡a` would produce the
   upper bound in `↡(lb C)` that step 3 denies. **This is the only use of
   interpolation, and it is what it is for.**
6. Continuity of `[D′ → D′]` gives `f ≪ id` with `x′ ≤ f x` and `y′ ≤ f y`: the
   evaluation image of `↡id` at `x` is directed with least upper bound `x`, so
   `x′ ≪ x` is caught by some `f₁ ≪ id`; likewise `f₂` at `y`; directedness of
   `↡id` merges them.
7. `f` maps `C` into `C` (`mapsTo_of_forall_not_upperBound`), contradicting the
   hypothesis. -/
theorem exists_isGLB_of_forall_not_mapsTo (hD : IsContinuousDcpo D)
    (hFS : IsContinuousDcpo (ScottHom D D)) {C : Set D}
    (hcover : ∀ z : D, z ∈ lowerBounds C ∨ z ∈ C)
    (hg : ∀ f : ScottHom D D, f ≪ ScottHom.id → ¬∀ γ ∈ C, f γ ∈ C) :
    ∃ i, IsGLB C i := by
  by_contra hno
  -- Steps 1 and 2: `↡(lb C)` is not directed.
  have hnd : ¬DirectedOn (· ≤ ·) (wayBelowLower (lowerBounds C)) :=
    fun hd => hno (exists_isGLB_of_directedOn_wayBelowLower hD hd)
  -- Step 3: the two elements it fails to bound.
  obtain ⟨x'', ⟨x, hx, hx''x⟩, y'', ⟨y, hy, hy''y⟩, hpair⟩ :
      ∃ a ∈ wayBelowLower (lowerBounds C), ∃ b ∈ wayBelowLower (lowerBounds C),
        ∀ c ∈ wayBelowLower (lowerBounds C), ¬(a ≤ c ∧ b ≤ c) := by
    by_contra hcon
    push Not at hcon
    refine hnd fun a ha b hb => ?_
    obtain ⟨c, hc, hac, hbc⟩ := hcon a ha b hb
    exact ⟨c, hc, hac, hbc⟩
  -- Step 4: interpolate on both sides.
  obtain ⟨x', hx''x', hx'x⟩ := hD.exists_wayBelow_wayBelow hx''x
  obtain ⟨y', hy''y', hy'y⟩ := hD.exists_wayBelow_wayBelow hy''y
  -- Step 5: `{x', y'}` has no upper bound in `lowerBounds C`.
  have hno' : ∀ a ∈ lowerBounds C, ¬(x' ≤ a ∧ y' ≤ a) := by
    rintro a ha ⟨hxa, hya⟩
    obtain ⟨c, hc, h₁, h₂⟩ :=
      hD.directedOn a x'' (hx''x'.trans_le hxa) y'' (hy''y'.trans_le hya)
    exact hpair c ⟨a, ha, hc⟩ ⟨h₁, h₂⟩
  -- Step 6: one function way-below the identity that lifts both `x'` and `y'`.
  have hdirId : DirectedOn (· ≤ ·) (wayBelowSet (ScottHom.id : ScottHom D D)) :=
    hFS.directedOn _
  have hlubId : IsLUB (wayBelowSet (ScottHom.id : ScottHom D D)) ScottHom.id :=
    hFS.isLUB _
  have hev : ∀ z : D, IsLUB ((fun g : ScottHom D D => g z) ''
      wayBelowSet (ScottHom.id : ScottHom D D)) z := by
    intro z
    simpa using ScottHom.isLUB_eval_image_of_isLUB hdirId hlubId z
  have hevne : ∀ z : D, ((fun g : ScottHom D D => g z) ''
      wayBelowSet (ScottHom.id : ScottHom D D)).Nonempty :=
    fun z => (wayBelowSet_nonempty _).image _
  obtain ⟨_, ⟨f₁, hf₁, rfl⟩, hxf₁⟩ :=
    hx'x _ x (hevne x) (ScottHom.directedOn_eval_image hdirId x) (hev x) le_rfl
  obtain ⟨_, ⟨f₂, hf₂, rfl⟩, hyf₂⟩ :=
    hy'y _ y (hevne y) (ScottHom.directedOn_eval_image hdirId y) (hev y) le_rfl
  obtain ⟨f, hf, h₁, h₂⟩ := hdirId f₁ hf₁ f₂ hf₂
  -- Step 7: `f` maps `C` into `C`, which the hypothesis forbids.
  exact hg f hf
    (mapsTo_of_forall_not_upperBound f.monotone hcover hx hy
      (hxf₁.trans (h₁ x)) (hyf₂.trans (h₂ y)) hno')

end Endgame

end ScottDomains.JungBicomplete
