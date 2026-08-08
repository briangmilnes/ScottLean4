import ScottDomains.JungNets

/-!
# Property m at a countable basis: Iwamura's lemma is not on the route

`ScottDomains/JungSFP.lean`'s `lemma217` carries one hypothesis the development
cannot discharge: `HasCompleteMub (compacts D) {a₁, a₂}`, Jung's *property m* at a
pair of compact elements. `ScottDomains/JungNets.lean` discharges it from Jung's
**Theorem 1.37** ("a dcpo with continuous function space is bicomplete"), whose
proof opens with

> By Corollary 1.3 we have to find infima only for monotone injective nets
> `s : αᵒᵖ → D` where `α` is an ordinal number.

and Corollary 1.3 is a corollary of Jung's Theorem 1.2, **Iwamura's lemma**, which
Mathlib does not carry (measured in `JungNets.lean`'s survey: zero hits for
`Iwamura|Markowsky`, and no ordinal-indexed chain API for posets).

This file removes that dependency. The observation is about *cofinality*, and it
is entirely elementary:

* Jung's Zorn-downwards argument (`JungNets.exists_minimal_upperBounds_le`)
  quantifies over **chains**, of arbitrary order type. `JungNets.HasChainInfima`
  is therefore the honest hypothesis, and it is already strictly weaker than
  `IsBicomplete`.
* Iwamura's lemma is what reduces an arbitrary *filtered* set to a *well-ordered*
  net, so that Jung's retraction and successor family have an index to run on.
* But **on a countable basis the reduction is finitary**. The Zorn step of
  property m may be run inside `K(D)` rather than inside `D`: minimality among
  compact upper bounds of a finite set of compacts is the same as minimality in
  all of `D` (Jung's Proposition 1.9 and its converse,
  `JungSFP.mem_minimalUpperBounds_of_minimal`). A chain of compact elements is a
  chain in a *countable* set, and a countable chain has a coinitial descending
  **ω**-sequence — take the minimum of each finite prefix of an enumeration, which
  is `minPrefix` below. No ordinal, no transfinite induction, no Iwamura.

## What is proved, and what it costs

| # | Result | Hypothesis |
| -- | ------ | ---------- |
| 1 | `hasCompleteMub_of_countable` — property m at every finite set of compacts | `(compacts D).Countable` and ω-indexed lower bounds |
| 2 | `countable_compacts_of_scottHom` — `K(D)` is countable when `K([D → D])` is | none beyond `CompletePartialOrder D` |
| 3 | `lemma217_of_omega`, `propertyM_pairs_of_omega`, `forall_hasCompleteMub_of_omega` | `HasOmegaOpInfima D` in place of `JungNets.Thm137 D` |

Item 2 makes item 1's countability hypothesis **free** in `lemma217`'s context:
`a ↦ (a ↘ a)` injects `K(D)` into `K([D → D])`, so Jung's ω-algebraicity of the
function space already supplies it. So the hypothesis `lemma217` now needs is
exactly

    HasOmegaOpInfima D : ∀ y : ℕ → D, Antitone y → ∃ i, IsGLB (Set.range y) i

— greatest lower bounds of **decreasing sequences**, and nothing more. The chain
of weakenings is kernel-checked here:

    IsBicomplete D  ⟹  HasChainInfima D  ⟹  HasOmegaOpInfima D  ⟹  HasOmegaOpBoundsAbove u

(`JungNets.IsBicomplete.hasChainInfima`, `HasChainInfima.hasOmegaOpInfima`,
`HasOmegaOpInfima.hasOmegaOpBoundsAbove`). The last of the four is the one the
proof consumes, and it is relative to the set `u` whose minimal upper bounds are
wanted: *some* lower bound of the sequence that is still an upper bound of `u`.

## Why the ω form is not a restatement of the problem

The second and third implications above are not reversible, and the gap is where
the saving is. `HasChainInfima` asks for infima of chains of every order type —
`ℝᵒᵖ` and `ω₁ᵒᵖ` included — and it is precisely to get a *well-ordered* index that
Jung invokes Iwamura. `HasOmegaOpInfima` asks only for infima of `ωᵒᵖ`.
Specialized to `α = ω`, the three transfinite steps of Jung's Theorem 1.37 proof
collapse:

* his retraction `r x = ⋀{γ ∈ αᵒᵖ | γ ≥ x}` becomes `r x = yₙ` for the largest `n`
  with `yₙ ≥ x`, a maximum over a finite initial segment of `ℕ` — no least-
  counterexample induction, and no normalization of limit stages;
* "since `α` is an ordinal there exists no strictly increasing infinite sequence
  in `αᵒᵖ`", which carries the continuity of `r`, becomes the well-ordering of
  `ℕ`;
* the successor family `g_β` becomes `g_k x = y_{j+1}` where `f x = y_j`, indexed
  by `k : ℕ`.

**Interpolation drops out too, and for a separate reason.** Jung's Proposition 1.8
is applied to lift `x'' ≪ x ∈ A` and `y'' ≪ y ∈ A` to `x'' ≪ x' ≪ x` and
`y'' ≪ y' ≪ y`, so that `{x', y'}` has no upper bound even in `A` and not merely
in `↓A`. In the application that reaches `lemma217` the two elements are `a₁` and
`a₂`, which are **compact**, so `a₁ ≪ a₁` and `a₂ ≪ a₂` and one may take
`x' = x'' = a₁`, `y' = y'' = a₂` outright. `a₁, a₂ ∈ A` because every `yₙ` is an
upper bound of the pair, and "no upper bound of `{a₁, a₂}` in `A`" is exactly the
negation of the conclusion wanted. So items 1 and 4 of `JungNets.lean`'s five-item
dependency list, and the transfinite half of item 2, are all off the route.

What does **not** collapse is Jung's Proposition 1.22 — the function space of a
retract of a dcpo with continuous function space is again continuous, which is
what supplies the `f ≪ id_{D'}` mapping the chain into itself. `JungNets.lean`
records it as absent, and it remains the cost of proving `HasOmegaOpInfima` from
the function space. This file does not prove it — it is a named hypothesis, and
**no `sorry` stands in for it**. What the file establishes is that Iwamura's
lemma **is not on the route to Theorem 18 at all**.

## The negative half of the measurement

Countability and algebraicity alone do **not** give property m, so no argument
that ignores the function space can succeed. The witness: let
`D = {⊥, a₁, a₂} ∪ {xₙ | n ∈ ℕ}` with `a₁, a₂` incomparable, `x₀ > x₁ > x₂ > ⋯`,
and every `xₙ` above both `a₁` and `a₂`. Every ascending chain is finite, so every
directed subset has a maximum and `D` is a dcpo in which every element is compact,
hence algebraic with a countable basis; and `ub{a₁, a₂} = {xₙ}` has no minimal
element, so property m fails at that pair. `HasOmegaOpInfima D` fails there too —
the sequence `xₙ` has no greatest lower bound above `a₁` and `a₂` — which is what
this file's hypothesis is buying, and it is the least it can buy.
-/

namespace ScottDomains.PropertyM

open ScottDomains

/-! ## Coinitial descending sequences in a countable chain -/

section MinPrefix

variable {D : Type*} [Preorder D]

open Classical in
/-- The minimum of the finite prefix `f 0, …, f n` of a sequence, chosen greedily.

For an arbitrary sequence this is only a descending sequence of *some* members of
the prefix; when the range of `f` is a chain it is genuinely the minimum, and that
is what `minPrefix_le` needs the chain hypothesis for. The `≤` test is not
decidable, so the branch is classical, exactly as in `ScottHom.stepFun`. -/
noncomputable def minPrefix (f : ℕ → D) : ℕ → D
  | 0 => f 0
  | (n + 1) => if f (n + 1) ≤ minPrefix f n then f (n + 1) else minPrefix f n

theorem minPrefix_succ_le (f : ℕ → D) (n : ℕ) : minPrefix f (n + 1) ≤ minPrefix f n := by
  classical
  simp only [minPrefix]
  split_ifs with h
  · exact h
  · exact le_rfl

/-- The greedy prefix minimum is antitone by construction — no chain hypothesis. -/
theorem antitone_minPrefix (f : ℕ → D) : Antitone (minPrefix f) :=
  antitone_nat_of_succ_le (minPrefix_succ_le f)

/-- Every value of `minPrefix f` is a value of `f`. -/
theorem minPrefix_mem_range (f : ℕ → D) (n : ℕ) : minPrefix f n ∈ Set.range f := by
  classical
  induction n with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    simp only [minPrefix]
    split_ifs with h
    · exact ⟨n + 1, rfl⟩
    · exact ih

/-- **The prefix minimum is coinitial.** `minPrefix f n ≤ f n`, so any lower bound
of the sequence `minPrefix f` is a lower bound of the whole range of `f`.

This is the only step that uses the chain hypothesis: in the branch where the new
value `f (n + 1)` is *not* below the running minimum, totality on the chain turns
that negation into `minPrefix f n ≤ f (n + 1)`. -/
theorem minPrefix_le {f : ℕ → D} (hc : IsChain (· ≤ ·) (Set.range f)) (n : ℕ) :
    minPrefix f n ≤ f n := by
  classical
  induction n with
  | zero => exact le_rfl
  | succ n _ =>
    simp only [minPrefix]
    split_ifs with h
    · exact le_rfl
    · rcases hc.total (minPrefix_mem_range f n) ⟨n + 1, rfl⟩ with hle | hle
      · exact hle
      · exact absurd hle h

end MinPrefix

/-! ## The hypotheses, and how they sit below `IsBicomplete` -/

section Hypotheses

variable {D : Type*} [Preorder D]

/-- **Greatest lower bounds of decreasing sequences.** The `ωᵒᵖ` fragment of
`JungNets.IsBicomplete`: only sequences `ℕ → D`, not filtered sets and not chains
of arbitrary order type. -/
def HasOmegaOpInfima (D : Type*) [Preorder D] : Prop :=
  ∀ y : ℕ → D, Antitone y → ∃ i : D, IsGLB (Set.range y) i

/-- **The hypothesis the proof below actually consumes**, relative to the set `u`
whose minimal upper bounds are wanted: a decreasing sequence of upper bounds of
`u` has *some* lower bound that is still an upper bound of `u`. No infimum is
asked for, and nothing is asked about sequences that are not upper bounds. -/
def HasOmegaOpBoundsAbove (u : Set D) : Prop :=
  ∀ y : ℕ → D, Antitone y → (∀ n, y n ∈ upperBounds u) →
    ∃ z ∈ upperBounds u, ∀ n, z ≤ y n

/-- A decreasing sequence has a chain for its range, so infima of chains give
infima of decreasing sequences. -/
theorem HasChainInfima.hasOmegaOpInfima (h : JungNets.HasChainInfima D) :
    HasOmegaOpInfima D := by
  intro y hy
  refine h (Set.range y) ⟨y 0, 0, rfl⟩ ?_
  rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩ _
  rcases le_total m n with hmn | hmn
  · exact Or.inr (hy hmn)
  · exact Or.inl (hy hmn)

/-- The greatest lower bound of a decreasing sequence of upper bounds of `u` is
itself an upper bound of `u`: each member of `u` is a *lower* bound of the
sequence, so it sits below the greatest one. -/
theorem HasOmegaOpInfima.hasOmegaOpBoundsAbove (h : HasOmegaOpInfima D) (u : Set D) :
    HasOmegaOpBoundsAbove u := by
  intro y hy hub
  obtain ⟨i, hi⟩ := h y hy
  refine ⟨i, ?_, fun n => hi.1 ⟨n, rfl⟩⟩
  intro a ha
  exact hi.2 (by rintro _ ⟨n, rfl⟩; exact hub n ha)

end Hypotheses

/-! ## A second sufficient condition: a deflation that stabilizes on descending
sequences

`HasOmegaOpBoundsAbove` is an order-theoretic hypothesis about `D`. This section
gives an independent way to obtain it, from the *deflation* machinery instead —
the route r0031's `exists_isCompactElement_le` and agent1's Corollary 1.36 stream
already build on. It is recorded because it is a different attack on the same
obligation, and because it is short. -/

section Deflation

variable {D : Type*} [CompletePartialOrder D]

/-- **A deflation that fixes `u` and stabilizes on decreasing sequences gives
`HasOmegaOpBoundsAbove u`.**

`f` is any monotone self-map below the identity that is above the identity on `u`
(so `f a = a` for `a ∈ u`), and `hstab` says the antitone sequence `n ↦ f (y n)`
is eventually constant for every antitone `y`. Then `f (y N)` is the lower bound
wanted: below `y n` for `n ≤ N` because `f` is monotone and `y` antitone, below
`y n` for `n ≥ N` because it *is* `f (y n) ≤ y n` there, and above every `a ∈ u`
because `a = f a ≤ f (y N)`.

Note which strength is not asked for. r0031's (★) — "a compact deflation has
finite image on the upper bounds of `u`" — is recorded in `Section62.lean` as
equivalent to Theorem 18 rather than below it. Stabilization on each antitone
sequence is weaker than a finite image, and it is all this argument spends. -/
theorem hasOmegaOpBoundsAbove_of_deflation {u : Set D} (f : D → D) (hmono : Monotone f)
    (hle : ∀ d, f d ≤ d) (hfix : ∀ a ∈ u, a ≤ f a)
    (hstab : ∀ y : ℕ → D, Antitone y → ∃ N, ∀ n, N ≤ n → f (y n) = f (y N)) :
    HasOmegaOpBoundsAbove u := by
  intro y hy hub
  obtain ⟨N, hN⟩ := hstab y hy
  refine ⟨f (y N), fun a ha => (hfix a ha).trans (hmono (hub N ha)), fun n => ?_⟩
  rcases le_total N n with h | h
  · exact (hN n h).symm.trans_le (hle (y n))
  · exact (hmono (hy h)).trans (hle (y n))

end Deflation

/-! ## Property m from a countable basis -/

section Countable

variable {D : Type*} [CompletePartialOrder D] [IsAlgebraic D]

/-- **Property m at every finite set of compact elements, from a countable basis
and `ωᵒᵖ` lower bounds.** This is `JungNets.hasCompleteMub_of_hasChainInfima` with
`HasChainInfima` — infima of chains of arbitrary order type — replaced by the
`ωᵒᵖ` fragment, at the cost of `(compacts D).Countable`, which
`countable_compacts_of_scottHom` shows is free wherever `lemma217` applies.

The proof is Zorn downwards, as Jung's is, but run **inside `K(D)`** rather than
inside `D`. That is the whole trick:

* `S = {compact upper bounds of u below x}` is a subset of `compacts D`, hence
  countable, hence every chain in it is countable;
* a countable chain has a coinitial decreasing **ω**-sequence — `minPrefix` of an
  enumeration (`Set.Countable.exists_eq_range`), whose `n`-th term is below the
  `n`-th term of the enumeration (`minPrefix_le`). This is the step Jung takes
  with Corollary 1.3, i.e. with Iwamura's lemma; countability does it in one
  finite minimum per index;
* the hypothesis supplies a lower bound `z` of that sequence still above `u`, and
  algebraicity converts `z` into a *compact* one: the finitely many members of `u`
  all lie in the directed set `compactsBelow z`, so a single compact `q ≤ z`
  dominates them all (`exists_mem_upperBounds_of_directedOn`). `q` is the lower
  bound of the chain that Zorn needs, and it is in `S`;
* minimality inside `S` is minimality among all compact upper bounds, because a
  compact upper bound below `m` is below `x` and so was in `S` already. -/
theorem hasCompleteMub_of_countable (hK : (compacts D).Countable) {u : Set D}
    (hu : u.Finite) (huc : u ⊆ compacts D) (hΩ : HasOmegaOpBoundsAbove u) :
    HasCompleteMub (compacts D) u := by
  classical
  intro x hx
  set S : Set D := {y | y ∈ compacts D ∧ y ∈ upperBounds u ∧ y ≤ x} with hSdef
  have hxS : x ∈ S := ⟨hx.1, hx.2, le_rfl⟩
  have key : ∀ c ⊆ S, IsChain (· ≤ ·) c → ∃ lb ∈ S, ∀ z ∈ c, lb ≤ z := by
    intro c hcS hc
    rcases c.eq_empty_or_nonempty with rfl | hne
    · exact ⟨x, hxS, fun z hz => absurd hz (Set.notMem_empty z)⟩
    · obtain ⟨f, hf⟩ := (hK.mono fun y hy => (hcS hy).1).exists_eq_range hne
      have hrange : Set.range f = c := hf.symm
      have hmem : ∀ n, minPrefix f n ∈ c := fun n => hrange ▸ minPrefix_mem_range f n
      have hchain : IsChain (· ≤ ·) (Set.range f) := hrange ▸ hc
      obtain ⟨z, hzub, hzle⟩ :=
        hΩ (minPrefix f) (antitone_minPrefix f) fun n => (hcS (hmem n)).2.1
      obtain ⟨q, hq, hqub⟩ :=
        exists_mem_upperBounds_of_directedOn (IsAlgebraic.directedOn_compactsBelow z)
          (compactsBelow_nonempty z) hu fun a ha => ⟨a, ⟨huc ha, hzub ha⟩, le_rfl⟩
      have hqz : q ≤ z := hq.2
      have hlower : ∀ w ∈ c, q ≤ w := by
        intro w hw
        obtain ⟨n, rfl⟩ := hrange ▸ hw
        exact hqz.trans ((hzle n).trans (minPrefix_le hchain n))
      exact ⟨q, ⟨hq.1, fun a ha => hqub a ha, (hlower _ (hmem 0)).trans (hcS (hmem 0)).2.2⟩,
        hlower⟩
  obtain ⟨m, hm⟩ := JungNets.exists_minimal_mem S key
  refine ⟨m, ⟨⟨hm.1.1, hm.1.2.1⟩, ?_⟩, hm.1.2.2⟩
  intro y hy hym
  exact hm.2 ⟨hy.1, hy.2, hym.trans hm.1.2.2⟩ hym

/-- The instance at a pair of compact elements — the exact shape
`JungSFP.lemma217`'s hypothesis is stated in. -/
theorem hasCompleteMub_pair_of_countable (hK : (compacts D).Countable) {a₁ a₂ : D}
    (ha₁ : IsCompactElement a₁) (ha₂ : IsCompactElement a₂)
    (hΩ : HasOmegaOpBoundsAbove ({a₁, a₂} : Set D)) :
    HasCompleteMub (compacts D) ({a₁, a₂} : Set D) :=
  hasCompleteMub_of_countable hK (Set.toFinite _)
    (by rintro y (rfl | rfl) <;> assumption) hΩ

end Countable

/-! ## Countability of `K(D)` is free when `K([D → D])` is countable -/

section StepInjection

variable {D : Type*} [CompletePartialOrder D]

/-- `a ↦ (a ↘ a)` is injective on compact elements.

Evaluate the equal step functions at `a₁` and at `a₂`. The first gives
`a₁ = (a₂ ↘ a₂)(a₁)`, which is `a₂` when `a₂ ⊑ a₁` and `⊥` otherwise; the second
gives `a₂ = (a₁ ↘ a₁)(a₂)`. In the first case the two are equal outright; in the
second `a₁ = ⊥`, whence `a₂ = a₁ = ⊥`, which puts us back in the first case. -/
theorem step_self_injective {a₁ a₂ : D} (ha₁ : IsCompactElement a₁)
    (ha₂ : IsCompactElement a₂)
    (h : ScottHom.step ha₁ a₁ = ScottHom.step ha₂ a₂) : a₁ = a₂ := by
  classical
  have e₁ : a₁ = ScottHom.stepFun a₂ a₂ a₁ := by
    have := congrArg (fun g : ScottHom D D => g a₁) h
    simpa only [ScottHom.coe_step, ScottHom.stepFun_self] using this
  have e₂ : ScottHom.stepFun a₁ a₁ a₂ = a₂ := by
    have := congrArg (fun g : ScottHom D D => g a₂) h
    simpa only [ScottHom.coe_step, ScottHom.stepFun_self] using this
  by_cases hle : a₂ ≤ a₁
  · rwa [ScottHom.stepFun_of_le hle] at e₁
  · rw [ScottHom.stepFun_of_not_le hle] at e₁
    rw [ScottHom.stepFun_of_le (e₁ ▸ bot_le : a₁ ≤ a₂)] at e₂
    exact absurd (e₂ ▸ le_rfl : a₂ ≤ a₁) hle

/-- **`K(D)` is countable whenever `K([D → D])` is.** So the countability
hypothesis of `hasCompleteMub_of_countable` costs nothing in `lemma217`'s context,
where `(compacts (ScottHom D D)).Countable` is already assumed — that is Jung's
ω-algebraicity of the function space.

The injection is `a ↦ (a ↘ a)`, compact by `ScottHom.isCompactElement_step` and
injective by `step_self_injective`. -/
theorem countable_compacts_of_scottHom (h : (compacts (ScottHom D D)).Countable) :
    (compacts D).Countable := by
  haveI : Countable ↥(compacts (ScottHom D D)) := h.to_subtype
  have hinj : Function.Injective
      (fun a : ↥(compacts D) =>
        (⟨ScottHom.step a.2 a.1, ScottHom.isCompactElement_step a.2 a.2⟩ :
          ↥(compacts (ScottHom D D)))) := by
    intro a b hab
    exact Subtype.ext (step_self_injective a.2 b.2 (Subtype.ext_iff.mp hab))
  haveI : Countable ↥(compacts D) := hinj.countable
  exact Set.countable_coe_iff.mp inferInstance

end StepInjection

/-! ## `lemma217` with Iwamura's lemma removed from its dependencies -/

section Omega

variable {D : Type*} [CompletePartialOrder D] [IsAlgebraic D]

/-- **The remaining obligation, in its weakest named form.** `JungNets.Thm137` is
`IsAlgebraic (ScottHom D D) → IsBicomplete D`; `JungNets.Thm137Chains` weakens the
conclusion to infima of chains; this weakens it again to infima of decreasing
sequences, which is all the route to Theorem 18 spends once the basis is known to
be countable. -/
def Thm137Omega (D : Type*) [CompletePartialOrder D] : Prop :=
  IsAlgebraic (ScottHom D D) → HasOmegaOpInfima D

theorem Thm137Chains.toOmega {D : Type*} [CompletePartialOrder D]
    (h : JungNets.Thm137Chains D) : Thm137Omega D :=
  fun hAlg => HasChainInfima.hasOmegaOpInfima (h hAlg)

theorem Thm137.toOmega {D : Type*} [CompletePartialOrder D] (h : JungNets.Thm137 D) :
    Thm137Omega D :=
  Thm137Chains.toOmega h.toChains

/-- **`JungSFP.lemma217` with its property-m hypothesis discharged from
`HasOmegaOpInfima` instead of from Jung's Theorem 1.37.**

Compare `JungNets.lemma217_of_thm137`, which spends `Thm137 D`. The countability
hypothesis is the same one `lemma217` already carries; `K(D)`'s countability is
derived from it, so nothing new is assumed beyond decreasing-sequence infima. -/
theorem lemma217_of_omega (hAlg : IsAlgebraic (ScottHom D D))
    (hCount : (compacts (ScottHom D D)).Countable) (hΩ : HasOmegaOpInfima D)
    {a₁ a₂ : D} (ha₁ : IsCompactElement a₁) (ha₂ : IsCompactElement a₂) :
    (minimalUpperBounds (compacts D) ({a₁, a₂} : Set D)).Finite :=
  JungSFP.lemma217 hAlg hCount ha₁ ha₂
    (hasCompleteMub_pair_of_countable (countable_compacts_of_scottHom hCount) ha₁ ha₂
      (hΩ.hasOmegaOpBoundsAbove _))

/-- **Property M at every pair of compact elements**, modulo `Thm137Omega` —
`JungNets.propertyM_pairs_of_thm137` with the same weakening. -/
theorem propertyM_pairs_of_omega (h : Thm137Omega D) (hAlg : IsAlgebraic (ScottHom D D))
    (hCount : (compacts (ScottHom D D)).Countable) :
    ∀ x₁ x₂ : D, IsCompactElement x₁ → IsCompactElement x₂ →
      (minimalUpperBounds (compacts D) ({x₁, x₂} : Set D)).Finite :=
  fun _ _ hx₁ hx₂ => lemma217_of_omega hAlg hCount (h hAlg) hx₁ hx₂

/-- **The first conjunct of `MinimalUpperBounds.isBifinite_iff_mubClosure`, reduced
to `Thm137Omega`** — `JungNets.forall_hasCompleteMub_of_thm137` with the same
weakening. -/
theorem forall_hasCompleteMub_of_omega (h : Thm137Omega D)
    (hAlg : IsAlgebraic (ScottHom D D)) (hCount : (compacts (ScottHom D D)).Countable) :
    ∀ v : Set D, v.Finite → v ⊆ compacts D → HasCompleteMub (compacts D) v :=
  fun _ hv hvc =>
    hasCompleteMub_of_countable (countable_compacts_of_scottHom hCount) hv hvc
      ((h hAlg).hasOmegaOpBoundsAbove _)

end Omega

end ScottDomains.PropertyM
