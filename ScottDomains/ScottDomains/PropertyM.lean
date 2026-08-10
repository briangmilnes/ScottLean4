import ScottDomains.JungNets
import ScottDomains.JungFinite

/-!
# Property m at a pair, proved: Theorem 1.37 and Iwamura's lemma are not on the route

**Result.** `hasCompleteMub_pair` proves `HasCompleteMub (compacts D) {a₁, a₂}` —
the hypothesis `JungSFP.jung_lemma_2_17` carries, Jung's *property m* at a pair of
compact elements — from `IsAlgebraic (ScottHom D D)` and
`(compacts (ScottHom D D)).Countable` and nothing else. Neither
`JungNets.Theorem137`, nor its chain-weakening `JungNets.Theorem137Chains`, nor Iwamura's
lemma appears anywhere in its dependency graph. `propertyM_pairs` is then Jung's
Lemma 2.17 with no remaining hypothesis, `forall_hasCompleteMub` lifts property m
from pairs to every finite set of compacts, and **`theorem_18_of_jung_corollary_1_36` is Theorem 18
with Jung's Corollary 1.36 as its only remaining hypothesis** — one of the two
open propositions instead of both.

The proof is in two halves, and only the first was this file's original plan.

* The **Zorn half** (`hasCompleteMub_of_countable`) is the observation that on a
  countable basis the Zorn step of property m needs only decreasing `ω`-sequences,
  never chains of arbitrary order type. This is what removes Iwamura's lemma.
* The **function-space half** (`hasOmegaOpBoundsAbove_pair`) is **Spreen's
  Lemma 5.8**, found in `papers/Spreen 2005 …pdf` and transcribed in the
  `Spreen` section below. It discharges the `ω`-sequence condition outright,
  which removes Theorem 1.37 as well.

The rest of this docstring records the first half and the measurements taken
along the way; the second half is documented at the `Spreen` section.

## The dependency that is removed

`ScottDomains/JungNets.lean` obtains property m from Jung's **Theorem 1.37** ("a
dcpo with continuous function space is bicomplete"), whose proof opens with

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
| 3 | `jung_lemma_2_17_of_omega`, `propertyM_pairs_of_omega`, `forall_hasCompleteMub_of_omega` | `HasOmegaOpInfima D` in place of `JungNets.Theorem137 D` |
| 4 | `hasOmegaOpBoundsAbove_pair` — Spreen's Lemma 5.8 | `IsAlgebraic (ScottHom D D)` |
| 5 | `hasCompleteMub_pair`, `propertyM_pairs`, `forall_hasCompleteMub` | **none** beyond items 2 and 4 |
| 6 | `theorem_18_of_jung_corollary_1_36` — **Theorem 18** | Jung's Corollary 1.36 only |

Items 5 and 6 need two hypothesis-weakenings of results the development already
had, each proved by re-running the original proof against what it actually uses:
`isNormalIn_of_pairs` (for `MinimalUpperBounds.isNormalIn_of_isMubClosed`) and
`exists_finite_complete_of_pairs` (for
`JungFinite.exists_finite_complete_upperBoundsIn`). Both stated property m at
*every* finite set and both used it only at `∅` and at pairs.

Items 1–3 are the `ωᵒᵖ` reduction; items 4–5 discharge it. Items 1–3 are kept
rather than folded into item 5 because the reduction is the reusable statement:
it holds of any countably based algebraic dcpo, whatever supplies the `ωᵒᵖ`
condition, and it is what makes the pair case of item 4 sufficient.

Item 2 makes item 1's countability hypothesis **free** in `jung_lemma_2_17`'s context:
`a ↦ (a ↘ a)` injects `K(D)` into `K([D → D])`, so Jung's ω-algebraicity of the
function space already supplies it. So the hypothesis `jung_lemma_2_17` now needs is
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
in `↓A`. In the application that reaches `jung_lemma_2_17` the two elements are `a₁` and
`a₂`, which are **compact**, so `a₁ ≪ a₁` and `a₂ ≪ a₂` and one may take
`x' = x'' = a₁`, `y' = y'' = a₂` outright. `a₁, a₂ ∈ A` because every `yₙ` is an
upper bound of the pair, and "no upper bound of `{a₁, a₂}` in `A`" is exactly the
negation of the conclusion wanted. So items 1 and 4 of `JungNets.lean`'s five-item
dependency list, and the transfinite half of item 2, are all off the route.

What does **not** collapse in Jung's proof is his Proposition 1.22 — the function
space of a retract of a dcpo with continuous function space is again continuous,
which is what supplies the `f ≪ id_{D'}` mapping the chain into itself.
`JungNets.lean` records it as absent, and it is the cost of proving
`HasOmegaOpInfima` **Jung's way**. The `Spreen` section below does not go Jung's
way: it builds its approximating family on `D` itself rather than on a retract
`D' = A ∪ αᵒᵖ`, so Proposition 1.22 never arises. That is why the `ωᵒᵖ` condition
is a theorem here and not a hypothesis.

## The negative half of the measurement

Countability and algebraicity alone do **not** give property m, so no argument
that ignores the function space can succeed. The witness: let
`D = {⊥, a₁, a₂} ∪ {xₙ | n ∈ ℕ}` with `a₁, a₂` incomparable, `x₀ > x₁ > x₂ > ⋯`,
and every `xₙ` above both `a₁` and `a₂`. Every ascending chain is finite, so every
directed subset has a maximum and `D` is a dcpo in which every element is compact,
hence algebraic with a countable basis; and `ub{a₁, a₂} = {xₙ}` has no minimal
element, so property m fails at that pair. `HasOmegaOpInfima D` fails there too —
the sequence `xₙ` has no greatest lower bound above `a₁` and `a₂`.

The witness is what forces the shape of the `Spreen` section: **the function space
must be used**, and by Jung's Theorem 1.37 this `D` is precisely a dcpo whose
function space is not algebraic. It also fixes the cost of the `ωᵒᵖ` condition
from below — no weakening of it that ignores `[D → D]` can be a theorem.
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
`countable_compacts_of_scottHom` shows is free wherever `jung_lemma_2_17` applies.

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
`JungSFP.jung_lemma_2_17`'s hypothesis is stated in. -/
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
hypothesis of `hasCompleteMub_of_countable` costs nothing in `jung_lemma_2_17`'s context,
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

/-! ## Spreen's Lemma 5.8: the `ωᵒᵖ` hypothesis discharged from the function space

`HasOmegaOpBoundsAbove {a₁, a₂}` is not a hypothesis after all. It is a theorem of
`IsAlgebraic (ScottHom D D)`, by an argument of **Spreen** that goes through the
function space directly and touches neither bicompleteness nor Iwamura's lemma.

> D. Spreen, *The largest Cartesian closed category of domains, considered
> constructively*, Math. Struct. in Comp. Sci. **15** (2005) 299–321, Lemma 5.8:
> "`U({x₁, x₂})` is complete for `{x₁, x₂}`, for all `x₁, x₂ ∈ D₀`. *Proof.* The
> proof is a modification of Smyth's proof of his analogous result."

Spreen's proof is stated for effectively given domains and its first step —
extracting the decreasing sequence — is recursion-theoretic (he cites Smyth 1983,
Lemma 1, and builds `g ∈ R⁽¹⁾` enumerating a decreasing cofinal sequence of upper
bounds). `hasCompleteMub_of_countable` above is the classical form of that step:
Zorn downwards inside the countable `K(D)`, with `minPrefix` in place of the
recursive enumeration. **What follows is the rest of Spreen's proof**, which is
purely order-theoretic, transcribed with his notation mapped as `y n = δ_{g(n)}`,
`lev x = max {k | x ⊑ δ_{g(k)}}`, `Iinf = ι̃` and `Ihat n = ι̃ₙ`.

The shape of the argument, and why it needs nothing transfinite:

1. Assume a decreasing sequence `y` of upper bounds of `{a₁, a₂}` below which no
   upper bound of the pair lies. Then for every upper bound `x` of the pair the
   set `{k | x ⊑ y k}` is a *proper* down-set of `ℕ`, hence bounded: `lev x` is
   well defined, and `x ⋢ y (lev x + 1)`. This is the whole use of the assumption.
2. `Iinf`, Jung's four-region function with top-region value `y (lev x)`, is Scott
   continuous. Its `attained` clause — the one clause of `JungSFP.IsJungPatch`
   that is not routine — holds because `b ⋢ y (lev b + 1)` and `b = ⨆ s` force
   some member of `s` to fail `⊑ y (lev b + 1)` too, so the level is attained
   inside the directed set.
3. `Iinf` dominates the compact step functions `a₁ ↘ a₁` and `a₂ ↘ a₂`, so
   directedness of `compactsBelow Iinf` — this is the **only** use of
   `IsAlgebraic (ScottHom D D)` — produces one compact `F` between them.
4. `F ⊑ Iinf ∘ F`, checked region by region.
5. `Ihat n`, the same function with `y (lev x)` replaced by `y (lev x + 1)` once
   `lev x ≥ n`, is an increasing sequence with `⨆ₙ Ihat n = Iinf`, so
   `⨆ₙ (Ihat n ∘ F) = Iinf ∘ F ⊒ F`, and compactness of `F` gives one `n̄` with
   `F ⊑ Ihat n̄ ∘ F`.
6. Evaluate at `y n̄`. Put `z = F (y n̄)`; then `a₁, a₂ ⊑ z ⊑ y n̄`, so
   `lev z ≥ n̄`, so `Ihat n̄ z = y (lev z + 1)`, so `z ⊑ y (lev z + 1)` —
   contradicting step 1.

No ordinal, no retraction, no interpolation, no chain infima, and no countability:
this section assumes only `IsAlgebraic (ScottHom D D)` and compactness of the
pair. -/

section Spreen

/-- Composition of bundled Scott-continuous maps.

`ScottDomains.comp` (`Combinator.lean`) is the same two-line definition. It is
repeated rather than imported because `Combinator.lean` imports
`Universality.lean`, and this file needs the composite of two endomaps and nothing
else from that file. -/
def compHom {D : Type*} [Preorder D] (g f : ScottHom D D) : ScottHom D D :=
  ⟨⇑g ∘ ⇑f, ScottContinuous.comp f.scottContinuous g.scottContinuous⟩

@[simp] theorem compHom_apply {D : Type*} [Preorder D] (g f : ScottHom D D) (x : D) :
    compHom g f x = g (f x) := rfl

section Lev

variable {D : Type*} [Preorder D] {y : ℕ → D}

/-- **Spreen's level.** The largest `k` with `x ⊑ y k`, and `0` when there is
none. The junk value at an unbounded `{k | x ≤ y k}` is never reached: every use
below supplies an `m` with `x ⋢ y m`, which the hypothesis of
`hasOmegaOpBoundsAbove_pair` provides for every upper bound of the pair. -/
noncomputable def lev (y : ℕ → D) (x : D) : ℕ := sSup {k | x ≤ y k}

/-- One failure bounds the whole level set: `{k | x ≤ y k}` is a down-set, so it
stops before any `m` at which `x ⋢ y m`. -/
theorem bddAbove_levSet (hy : Antitone y) {x : D} {m : ℕ} (hm : ¬ x ≤ y m) :
    BddAbove {k | x ≤ y k} := by
  refine ⟨m, fun k hk => ?_⟩
  by_contra hlt
  exact hm (le_trans hk (hy (Nat.le_of_lt (not_le.mp hlt))))

theorem le_lev (hy : Antitone y) {x : D} {m k : ℕ} (hm : ¬ x ≤ y m) (hk : x ≤ y k) :
    k ≤ lev y x :=
  le_csSup (bddAbove_levSet hy hm) hk

theorem le_y_lev (hy : Antitone y) {x : D} {m : ℕ} (hm : ¬ x ≤ y m) (h0 : x ≤ y 0) :
    x ≤ y (lev y x) :=
  Nat.sSup_mem ⟨0, h0⟩ (bddAbove_levSet hy hm)

/-- **`x` fails one step past its level.** This is the fact the whole argument
turns on, and it needs no case split on whether the level set is empty: if
`x ⊑ y (lev x + 1)` then `lev x + 1` is in the level set, so `lev x + 1 ≤ lev x`. -/
theorem not_le_y_lev_succ (hy : Antitone y) {x : D} {m : ℕ} (hm : ¬ x ≤ y m) :
    ¬ x ≤ y (lev y x + 1) := fun h => Nat.not_succ_le_self _ (le_lev hy hm h)

theorem lev_le_of_not_le (hy : Antitone y) {x : D} {n : ℕ} (h : ¬ x ≤ y (n + 1)) :
    lev y x ≤ n := by
  rcases Set.eq_empty_or_nonempty {k | x ≤ y k} with he | hne
  · rw [lev, he, csSup_empty]
    exact Nat.zero_le n
  · refine csSup_le hne fun k hk => ?_
    by_contra hlt
    exact h (le_trans hk (hy (not_le.mp hlt)))

/-- The level is antitone: a larger element fails earlier. -/
theorem lev_antitone (hy : Antitone y) {x x' : D} {m : ℕ} (hm : ¬ x ≤ y m)
    (hxx' : x ≤ x') : lev y x' ≤ lev y x :=
  lev_le_of_not_le hy fun h => not_le_y_lev_succ hy hm (hxx'.trans h)

end Lev

/-! ### Spreen's index shift `σₙ` -/

/-- `σₙ` of Spreen's proof: the identity below `n`, and the successor from `n` on.
`Ihat n` uses it to push the top-region value one step down the sequence exactly
at the levels `n` and above. -/
def sig (n i : ℕ) : ℕ := if i < n then i else i + 1

theorem monotone_sig (n : ℕ) : Monotone (sig n) := by
  intro i j hij
  simp only [sig]
  split_ifs <;> omega

theorem self_le_sig (n i : ℕ) : i ≤ sig n i := by
  simp only [sig]
  split_ifs <;> omega

theorem sig_succ_le (n i : ℕ) : sig (n + 1) i ≤ sig n i := by
  simp only [sig]
  split_ifs <;> omega

theorem sig_of_lt (n i : ℕ) (h : i < n) : sig n i = i := if_pos h

theorem sig_of_le (n i : ℕ) (h : n ≤ i) : sig n i = i + 1 := if_neg (Nat.not_lt.mpr h)

/-! ### The theorem -/

variable {D : Type*} [CompletePartialOrder D]

/-- **Spreen 2005, Lemma 5.8**, in the form this development consumes: for a pair
of compact elements, every decreasing sequence of upper bounds has a lower bound
that is again an upper bound.

Together with `hasCompleteMub_of_countable` this discharges `JungSFP.jung_lemma_2_17`'s
property-m hypothesis outright. The only hypothesis on `D` beyond compactness of
the pair is that its function space is algebraic — `JungNets.Theorem137` and
`JungNets.Theorem137Chains` are not used, and neither is Iwamura's lemma. -/
theorem hasOmegaOpBoundsAbove_pair (hAlgF : IsAlgebraic (ScottHom D D)) {a₁ a₂ : D}
    (ha₁ : IsCompactElement a₁) (ha₂ : IsCompactElement a₂) :
    HasOmegaOpBoundsAbove ({a₁, a₂} : Set D) := by
  classical
  intro y hy hub
  by_contra hcon
  haveI := hAlgF
  -- the pair sits below every member of the sequence
  have hy₁ : ∀ n, a₁ ≤ y n := fun n => hub n (Set.mem_insert _ _)
  have hy₂ : ∀ n, a₂ ≤ y n := fun n => hub n (Set.mem_insert_of_mem _ rfl)
  -- step 1: every upper bound of the pair fails somewhere along the sequence
  have hfail : ∀ x : D, a₁ ≤ x → a₂ ≤ x → ∃ m, ¬ x ≤ y m := by
    intro x h₁ h₂
    by_contra hall
    exact hcon ⟨x, by rintro w (rfl | rfl) <;> assumption,
      fun n => not_not.mp fun h => hall ⟨n, h⟩⟩
  -- step 2: the four-region function with top-region value `y (σ (lev x))`
  have hpatch : ∀ σ : ℕ → ℕ, Monotone σ →
      JungSFP.IsJungPatch a₁ a₂ a₁ a₂ (fun x : D => y (σ (lev y x))) := by
    intro σ hσ
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro d d' hd₁ hd₂ hdd'
      obtain ⟨m, hm⟩ := hfail d hd₁ hd₂
      exact hy (hσ (lev_antitone hy hm hdd'))
    · intro d _ _; exact hy₁ _
    · intro d _ _; exact hy₂ _
    · intro s hne hsd b hb hb₁ hb₂
      obtain ⟨d₀, hd₀s, hd₀₁, hd₀₂⟩ :=
        JungSFP.exists_mem_of_isLUB_pair ha₁ ha₂ hne hsd hb hb₁ hb₂
      obtain ⟨m, hm⟩ := hfail b hb₁ hb₂
      have hbfail : ¬ b ≤ y (lev y b + 1) := not_le_y_lev_succ hy hm
      have hex : ∃ d₁ ∈ s, ¬ d₁ ≤ y (lev y b + 1) := by
        by_contra hall
        refine hbfail (hb.2 fun w hw => ?_)
        by_contra hw'
        exact hall ⟨w, hw, hw'⟩
      obtain ⟨d₁, hd₁s, hd₁f⟩ := hex
      obtain ⟨d, hds, hd₀d, hd₁d⟩ := hsd d₀ hd₀s d₁ hd₁s
      refine ⟨d, hds, hd₀₁.trans hd₀d, hd₀₂.trans hd₀d, ?_⟩
      exact hy (hσ (lev_le_of_not_le hy fun h => hd₁f (hd₁d.trans h)))
  -- comparing two four-region functions that differ only in the top region
  have hjmono : ∀ t t' : D → D, (∀ d : D, a₁ ≤ d → a₂ ≤ d → t d ≤ t' d) → ∀ x : D,
      JungSFP.jungFun a₁ a₂ a₁ a₂ t x ≤ JungSFP.jungFun a₁ a₂ a₁ a₂ t' x := by
    intro t t' h x
    by_cases h₁ : a₁ ≤ x
    · by_cases h₂ : a₂ ≤ x
      · rw [JungSFP.jungFun_of_both (t := t) h₁ h₂, JungSFP.jungFun_of_both (t := t') h₁ h₂]
        exact h x h₁ h₂
      · exact le_of_eq ((JungSFP.jungFun_of_left (t := t) h₁ h₂).trans
          (JungSFP.jungFun_of_left (t := t') h₁ h₂).symm)
    · by_cases h₂ : a₂ ≤ x
      · exact le_of_eq ((JungSFP.jungFun_of_right (t := t) h₁ h₂).trans
          (JungSFP.jungFun_of_right (t := t') h₁ h₂).symm)
      · exact le_of_eq ((JungSFP.jungFun_of_neither (t := t) h₁ h₂).trans
          (JungSFP.jungFun_of_neither (t := t') h₁ h₂).symm)
  set Iinf : ScottHom D D :=
    JungSFP.jungHom ha₁ ha₂ a₁ a₂ (fun x : D => y (id (lev y x))) (hpatch id monotone_id)
    with hIinfdef
  set Ihat : ℕ → ScottHom D D := fun n =>
    JungSFP.jungHom ha₁ ha₂ a₁ a₂ (fun x : D => y (sig n (lev y x)))
      (hpatch (sig n) (monotone_sig n)) with hIhatdef
  have hIinf_app : ∀ x : D,
      Iinf x = JungSFP.jungFun a₁ a₂ a₁ a₂ (fun x : D => y (id (lev y x))) x := by
    intro x; rw [hIinfdef]; rfl
  have hIhat_app : ∀ (n : ℕ) (x : D),
      Ihat n x = JungSFP.jungFun a₁ a₂ a₁ a₂ (fun x : D => y (sig n (lev y x))) x := by
    intro n x; rw [hIhatdef]; rfl
  -- `Ihat n ⊑ Iinf`, and `Ihat` increasing in `n`
  have hIhat_le_Iinf : ∀ n : ℕ, Ihat n ≤ Iinf := by
    intro n x
    show Ihat n x ≤ Iinf x
    rw [hIhat_app, hIinf_app]
    exact hjmono _ _ (fun d _ _ => hy (self_le_sig n (lev y d))) x
  have hIhat_mono : Monotone Ihat := by
    refine monotone_nat_of_le_succ fun n => ?_
    intro x
    show Ihat n x ≤ Ihat (n + 1) x
    rw [hIhat_app, hIhat_app]
    exact hjmono _ _ (fun d _ _ => hy (sig_succ_le n (lev y d))) x
  -- step 3: a compact `F` between the two step functions and `Iinf`
  obtain ⟨hstep₁, hstep₂⟩ := JungSFP.step_le_jungHom ha₁ ha₂ (hpatch id monotone_id)
  obtain ⟨F, hFmem, hFub⟩ :=
    exists_mem_upperBounds_of_directedOn (IsAlgebraic.directedOn_compactsBelow Iinf)
      (compactsBelow_nonempty Iinf)
      (Set.toFinite ({ScottHom.step ha₁ a₁, ScottHom.step ha₂ a₂} : Set (ScottHom D D)))
      (by
        rintro g (rfl | rfl)
        · exact ⟨ScottHom.step ha₁ a₁,
            ⟨ScottHom.isCompactElement_step ha₁ ha₁, hstep₁⟩, le_rfl⟩
        · exact ⟨ScottHom.step ha₂ a₂,
            ⟨ScottHom.isCompactElement_step ha₂ ha₂, hstep₂⟩, le_rfl⟩)
  have hFc : IsCompactElement F := hFmem.1
  have hFle : F ≤ Iinf := hFmem.2
  have hFa₁ : ∀ x : D, a₁ ≤ x → a₁ ≤ F x := fun x hx =>
    ((ScottHom.step_le_iff ha₁).mp (hFub _ (Set.mem_insert _ _))).trans (F.monotone hx)
  have hFa₂ : ∀ x : D, a₂ ≤ x → a₂ ≤ F x := fun x hx =>
    ((ScottHom.step_le_iff ha₂).mp (hFub _ (Set.mem_insert_of_mem _ rfl))).trans (F.monotone hx)
  -- step 4: `F ⊑ Iinf ∘ F`
  have hkey : ∀ w : D, w ≤ y 0 → a₁ ≤ w → a₂ ≤ w → w ≤ Iinf w := by
    intro w h0 h₁ h₂
    obtain ⟨m, hm⟩ := hfail w h₁ h₂
    rw [hIinf_app, JungSFP.jungFun_of_both h₁ h₂]
    exact le_y_lev hy hm h0
  have hFcomp : F ≤ compHom Iinf F := by
    intro x
    show F x ≤ Iinf (F x)
    have hx : F x ≤ Iinf x := hFle x
    by_cases h₁ : a₁ ≤ x
    · by_cases h₂ : a₂ ≤ x
      · have hFxle : F x ≤ y (lev y x) := by
          rwa [hIinf_app, JungSFP.jungFun_of_both h₁ h₂] at hx
        exact hkey (F x) (hFxle.trans (hy (Nat.zero_le _))) (hFa₁ x h₁) (hFa₂ x h₂)
      · have hle : F x ≤ a₁ := by
          rwa [hIinf_app, JungSFP.jungFun_of_left h₁ h₂] at hx
        have heq : F x = a₁ := le_antisymm hle (hFa₁ x h₁)
        have hna₂ : ¬ a₂ ≤ a₁ := fun hc => h₂ (hc.trans h₁)
        have hval : Iinf (F x) = a₁ := by
          rw [heq, hIinf_app, JungSFP.jungFun_of_left le_rfl hna₂]
        exact le_of_eq (heq.trans hval.symm)
    · by_cases h₂ : a₂ ≤ x
      · have hle : F x ≤ a₂ := by
          rwa [hIinf_app, JungSFP.jungFun_of_right h₁ h₂] at hx
        have heq : F x = a₂ := le_antisymm hle (hFa₂ x h₂)
        have hna₁ : ¬ a₁ ≤ a₂ := fun hc => h₁ (hc.trans h₂)
        have hval : Iinf (F x) = a₂ := by
          rw [heq, hIinf_app, JungSFP.jungFun_of_right hna₁ le_rfl]
        exact le_of_eq (heq.trans hval.symm)
      · have hle : F x ≤ ⊥ := by
          rwa [hIinf_app, JungSFP.jungFun_of_neither h₁ h₂] at hx
        exact hle.trans bot_le
  -- step 5: `⨆ₙ (Ihat n ∘ F) = Iinf ∘ F`
  have hattain : ∀ w : D, Ihat (lev y w + 1) w = Iinf w := by
    intro w
    rw [hIhat_app, hIinf_app]
    exact JungSFP.jungFun_congr fun _ _ =>
      congrArg y (sig_of_lt _ _ (Nat.lt_succ_self _))
  set s : Set (ScottHom D D) := Set.range (fun n => compHom (Ihat n) F) with hsdef
  have hsne : s.Nonempty := ⟨_, ⟨0, rfl⟩⟩
  have hsd : DirectedOn (· ≤ ·) s := by
    rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
    refine ⟨compHom (Ihat (max m n)) F, ⟨max m n, rfl⟩, fun x => ?_, fun x => ?_⟩
    · exact hIhat_mono (le_max_left m n) (F x)
    · exact hIhat_mono (le_max_right m n) (F x)
  have hlub : IsLUB s (compHom Iinf F) := by
    constructor
    · rintro _ ⟨n, rfl⟩ x
      exact hIhat_le_Iinf n (F x)
    · intro g hg x
      show Iinf (F x) ≤ g x
      have hx : Ihat (lev y (F x) + 1) (F x) ≤ g x :=
        hg (Set.mem_range_self (lev y (F x) + 1)) x
      rwa [hattain] at hx
  -- step 6: compactness of `F`, evaluated at `y n̄`
  obtain ⟨g, hgs, hFg⟩ := hFc s (compHom Iinf F) hsne hsd hlub hFcomp
  obtain ⟨n, rfl⟩ := hgs
  obtain ⟨mn, hmn⟩ := hfail (y n) (hy₁ n) (hy₂ n)
  have hlevyn : n ≤ lev y (y n) := le_lev hy hmn le_rfl
  have hFyn : F (y n) ≤ y n := by
    have hx : F (y n) ≤ Iinf (y n) := hFle (y n)
    rw [hIinf_app, JungSFP.jungFun_of_both (hy₁ n) (hy₂ n)] at hx
    exact hx.trans (hy hlevyn)
  obtain ⟨mz, hmz⟩ := hfail (F (y n)) (hFa₁ _ (hy₁ n)) (hFa₂ _ (hy₂ n))
  have hnlev : n ≤ lev y (F (y n)) := le_lev hy hmz hFyn
  have hcontra : F (y n) ≤ Ihat n (F (y n)) := hFg (y n)
  rw [hIhat_app, JungSFP.jungFun_of_both (hFa₁ _ (hy₁ n)) (hFa₂ _ (hy₂ n)),
    sig_of_le _ _ hnlev] at hcontra
  exact not_le_y_lev_succ hy hmz hcontra

end Spreen

/-! ## `jung_lemma_2_17` with Iwamura's lemma removed from its dependencies -/

section Omega

variable {D : Type*} [CompletePartialOrder D] [IsAlgebraic D]

/-- **The remaining obligation, in its weakest named form.** `JungNets.Theorem137` is
`IsAlgebraic (ScottHom D D) → IsBicomplete D`; `JungNets.Theorem137Chains` weakens the
conclusion to infima of chains; this weakens it again to infima of decreasing
sequences, which is all the route to Theorem 18 spends once the basis is known to
be countable. -/
def Theorem137Omega (D : Type*) [CompletePartialOrder D] : Prop :=
  IsAlgebraic (ScottHom D D) → HasOmegaOpInfima D

theorem Theorem137Chains.toOmega {D : Type*} [CompletePartialOrder D]
    (h : JungNets.Theorem137Chains D) : Theorem137Omega D :=
  fun hAlg => HasChainInfima.hasOmegaOpInfima (h hAlg)

theorem Theorem137.toOmega {D : Type*} [CompletePartialOrder D] (h : JungNets.Theorem137 D) :
    Theorem137Omega D :=
  Theorem137Chains.toOmega h.toChains

/-- **`JungSFP.jung_lemma_2_17` with its property-m hypothesis discharged from
`HasOmegaOpInfima` instead of from Jung's Theorem 1.37.**

Compare `JungNets.jung_lemma_2_17_of_jung_theorem_1_37`, which spends `Theorem137 D`. The countability
hypothesis is the same one `jung_lemma_2_17` already carries; `K(D)`'s countability is
derived from it, so nothing new is assumed beyond decreasing-sequence infima. -/
theorem jung_lemma_2_17_of_omega (hAlg : IsAlgebraic (ScottHom D D))
    (hCount : (compacts (ScottHom D D)).Countable) (hΩ : HasOmegaOpInfima D)
    {a₁ a₂ : D} (ha₁ : IsCompactElement a₁) (ha₂ : IsCompactElement a₂) :
    (minimalUpperBounds (compacts D) ({a₁, a₂} : Set D)).Finite :=
  JungSFP.jung_lemma_2_17 hAlg hCount ha₁ ha₂
    (hasCompleteMub_pair_of_countable (countable_compacts_of_scottHom hCount) ha₁ ha₂
      (hΩ.hasOmegaOpBoundsAbove _))

/-- **Property M at every pair of compact elements**, modulo `Theorem137Omega` —
`JungNets.propertyM_pairs_of_jung_theorem_1_37` with the same weakening. -/
theorem propertyM_pairs_of_omega (h : Theorem137Omega D) (hAlg : IsAlgebraic (ScottHom D D))
    (hCount : (compacts (ScottHom D D)).Countable) :
    ∀ x₁ x₂ : D, IsCompactElement x₁ → IsCompactElement x₂ →
      (minimalUpperBounds (compacts D) ({x₁, x₂} : Set D)).Finite :=
  fun _ _ hx₁ hx₂ => jung_lemma_2_17_of_omega hAlg hCount (h hAlg) hx₁ hx₂

/-- **The first conjunct of `MinimalUpperBounds.isBifinite_iff_mubClosure`, reduced
to `Theorem137Omega`** — `JungNets.forall_hasCompleteMub_of_jung_theorem_1_37` with the same
weakening. -/
theorem forall_hasCompleteMub_of_omega (h : Theorem137Omega D)
    (hAlg : IsAlgebraic (ScottHom D D)) (hCount : (compacts (ScottHom D D)).Countable) :
    ∀ v : Set D, v.Finite → v ⊆ compacts D → HasCompleteMub (compacts D) v :=
  fun _ hv hvc =>
    hasCompleteMub_of_countable (countable_compacts_of_scottHom hCount) hv hvc
      ((h hAlg).hasOmegaOpBoundsAbove _)

end Omega

/-! ## Property m at pairs, unconditionally, and what it discharges

Everything in this section is free of `JungNets.Theorem137`, `JungNets.Theorem137Chains`,
`HasOmegaOpInfima` and Iwamura's lemma. The hypotheses are exactly Jung's
Theorem 2.3: `D` is an algebraic dcpo with least element and `[D → D]` is
ω-algebraic. -/

section Unconditional

variable {D : Type*} [CompletePartialOrder D] [IsAlgebraic D]

/-- **Property m at a pair of compact elements, with no further hypothesis.**
`hasCompleteMub_of_countable` (the Zorn step, on the countable basis) composed
with `hasOmegaOpBoundsAbove_pair` (Spreen's Lemma 5.8, the function-space step).

This is the hypothesis `JungSFP.jung_lemma_2_17` carries, discharged. Compare
`JungNets.hasCompleteMub_pair`, which spends `JungNets.HasChainInfima` and
therefore Jung's Theorem 1.37. -/
theorem hasCompleteMub_pair (hAlgF : IsAlgebraic (ScottHom D D))
    (hCount : (compacts (ScottHom D D)).Countable) {a₁ a₂ : D}
    (ha₁ : IsCompactElement a₁) (ha₂ : IsCompactElement a₂) :
    HasCompleteMub (compacts D) ({a₁, a₂} : Set D) :=
  hasCompleteMub_pair_of_countable (countable_compacts_of_scottHom hCount) ha₁ ha₂
    (hasOmegaOpBoundsAbove_pair hAlgF ha₁ ha₂)

/-- **Jung's Lemma 2.17 with no remaining hypothesis** — property M at every pair
of compact elements, from an ω-algebraic function space alone. Compare
`JungNets.jung_lemma_2_17_of_jung_theorem_1_37` and `JungNets.propertyM_pairs_of_jung_theorem_1_37`. -/
theorem propertyM_pairs (hAlgF : IsAlgebraic (ScottHom D D))
    (hCount : (compacts (ScottHom D D)).Countable) :
    ∀ x₁ x₂ : D, IsCompactElement x₁ → IsCompactElement x₂ →
      (minimalUpperBounds (compacts D) ({x₁, x₂} : Set D)).Finite :=
  fun _ _ hx₁ hx₂ =>
    JungSFP.jung_lemma_2_17 hAlgF hCount hx₁ hx₂ (hasCompleteMub_pair hAlgF hCount hx₁ hx₂)

omit [IsAlgebraic D] in
/-- Property m at the empty set: `⊥` is compact and below everything, so it is the
one minimal element of `K(D)`. `upperBoundsIn A ∅ = A`, so this says every compact
element dominates a minimal compact element. -/
theorem hasCompleteMub_empty : HasCompleteMub (compacts D) (∅ : Set D) := fun _ _ =>
  ⟨⊥, ⟨⟨isCompactElement_bot, fun y hy => absurd hy (Set.notMem_empty y)⟩,
    fun _ _ _ => bot_le⟩, bot_le⟩

/-- **`MinimalUpperBounds.isNormalIn_of_isMubClosed` with its hypothesis cut down
to what its proof actually uses.**

That theorem asks for `HasCompleteMub A v` at *every* finite `v ⊆ N`, but its
proof applies the hypothesis exactly twice: at `v = ∅`, to get nonemptiness of
`N ∩ ↓x`, and at `v = {a, b}`, to get directedness. Nothing else is consumed. The
restatement matters here because `hasCompleteMub_pair` delivers pairs and the
empty set and **not** the general finite case: Jung's Lemma 1.29 (pairs to all
finite sets) is a separate result, and this restatement does not need it.

*Correction, r0049/agent8.* The sentence read "…is a separate result the
development does not have." That is false, and refuted 100 lines below in this
same file: `forall_hasCompleteMub` (`:945`) proves property m at *every* finite
set of compacts from the pair and empty cases, and its own docstring names the
step — "The lift is Jung's Lemma 1.29 argument, which the development already
carries as `JungFinite.exists_finite_complete_upperBoundsIn`".
`JungFinite.jung_lemma_1_29` carries the property-M analogue. The claim was true when
written and went stale inside this file. -/
theorem isNormalIn_of_pairs {α : Type*} [PartialOrder α] {A N : Set α} (hNA : N ⊆ A)
    (hcl : IsMubClosed A N) (hempty : HasCompleteMub A (∅ : Set α))
    (hpair : ∀ a b : α, a ∈ N → b ∈ N → HasCompleteMub A ({a, b} : Set α)) : N ◁ A := by
  refine ⟨hNA, fun x hx => ⟨?_, ?_⟩⟩
  · obtain ⟨m, hm, hmx⟩ := hempty x (by simpa using hx)
    exact ⟨m, hcl ∅ (Set.empty_subset N) Set.finite_empty hm, hmx⟩
  · rintro a ⟨haN, hax⟩ b ⟨hbN, hbx⟩
    have hsub : ({a, b} : Set α) ⊆ N := by rintro z (rfl | rfl) <;> assumption
    have hxub : x ∈ upperBoundsIn A ({a, b} : Set α) :=
      ⟨hx, by rintro z (rfl | rfl) <;> assumption⟩
    obtain ⟨m, hm, hmx⟩ := hpair a b haN hbN x hxub
    have hmub := mem_upperBounds_of_mem_minimalUpperBounds hm
    exact ⟨m, ⟨hcl _ hsub (Set.toFinite _) hm, hmx⟩,
      hmub (Set.mem_insert a _), hmub (Set.mem_insert_of_mem a rfl)⟩

/-- **From a finite complete set of upper bounds to property m.**

`MinimalUpperBounds.hasCompleteMub_of_isNormalIn` is this argument with
`N ∩ ↓x` supplying the finite complete set; here the finite complete set is given
directly, which is the form `JungFinite.exists_finite_complete_upperBoundsIn`
produces. Take `m` minimal in the finite set `M ∩ ↓x`; any upper bound `w ⊑ m` is
itself `⊑ x`, so `M` puts some `z' ⊑ w` in that set, and minimality of `m` gives
`m ⊑ z' ⊑ w`. -/
theorem hasCompleteMub_of_finite_complete {α : Type*} [PartialOrder α] {A u M : Set α}
    (hMfin : M.Finite) (hMsub : M ⊆ upperBoundsIn A u)
    (hMcomp : ∀ x ∈ upperBoundsIn A u, ∃ z ∈ M, z ≤ x) : HasCompleteMub A u := by
  intro x hx
  obtain ⟨z, hzM, hzx⟩ := hMcomp x hx
  set S : Set α := {w | w ∈ M ∧ w ≤ x} with hS
  have hSfin : S.Finite := hMfin.subset fun _ hw => hw.1
  obtain ⟨m, _, hmS, hmmin⟩ := hSfin.exists_le_minimal (a := z) ⟨hzM, hzx⟩
  refine ⟨m, ⟨hMsub hmS.1, ?_⟩, hmS.2⟩
  intro w hw hwm
  obtain ⟨z', hz'M, hz'w⟩ := hMcomp w hw
  exact (hmmin ⟨hz'M, hz'w.trans (hwm.trans hmS.2)⟩ (hz'w.trans hwm)).trans hz'w

/-- **`JungFinite.exists_finite_complete_upperBoundsIn` with its property-m
hypothesis cut down to what its proof uses.**

That theorem asks for `HasCompleteMub A v` at every finite `v ⊆ A`; its induction
applies the hypothesis exactly twice — once at `v = ∅` (the base case) and once at
a **pair** `{y, a}` in the insertion step. Nothing else is consumed. This is the
same restatement as `isNormalIn_of_pairs`, and it is what turns
`hasCompleteMub_pair` into property m at *every* finite set: the finite complete
set of upper bounds it produces feeds `hasCompleteMub_of_finite_complete`.

The proof is `JungFinite.exists_finite_complete_upperBoundsIn`'s, with `hm` split
into `hmEmpty` and `hmPair`. -/
theorem exists_finite_complete_of_pairs {α : Type*} [PartialOrder α] {A u : Set α}
    (hmEmpty : HasCompleteMub A (∅ : Set α))
    (hmPair : ∀ a ∈ A, ∀ b ∈ A, HasCompleteMub A ({a, b} : Set α))
    (hpair : ∀ a ∈ A, ∀ b ∈ A, (minimalUpperBounds A ({a, b} : Set α)).Finite)
    (hempty : (minimalUpperBounds A (∅ : Set α)).Finite) (hu : u.Finite) :
    u ⊆ A → ∃ M : Set α, M.Finite ∧ M ⊆ upperBoundsIn A u ∧
      ∀ x ∈ upperBoundsIn A u, ∃ z ∈ M, z ≤ x := by
  induction u, hu using Set.Finite.induction_on with
  | empty =>
    intro _
    exact ⟨minimalUpperBounds A ∅, hempty, minimalUpperBounds_subset,
      fun x hx => hmEmpty x hx⟩
  | @insert a v _ _ ih =>
    intro hsub
    have haA : a ∈ A := hsub (Set.mem_insert a v)
    obtain ⟨M, hMfin, hMsub, hMcomp⟩ := ih fun z hz => hsub (Set.mem_insert_of_mem a hz)
    refine ⟨⋃ z ∈ M, minimalUpperBounds A ({z, a} : Set α), ?_, ?_, ?_⟩
    · exact hMfin.biUnion fun z hz => hpair z (upperBoundsIn_subset (hMsub hz)) a haA
    · rintro w hw
      obtain ⟨z, hzM, hwz⟩ := Set.mem_iUnion₂.mp hw
      have hwub := minimalUpperBounds_subset hwz
      refine ⟨hwub.1, ?_⟩
      rintro c (rfl | hc)
      · exact hwub.2 (Set.mem_insert_of_mem _ rfl)
      · exact ((hMsub hzM).2 hc).trans (hwub.2 (Set.mem_insert _ _))
    · intro x hx
      obtain ⟨z, hzM, hzx⟩ :=
        hMcomp x ⟨hx.1, fun c hc => hx.2 (Set.mem_insert_of_mem a hc)⟩
      have hxpair : x ∈ upperBoundsIn A ({z, a} : Set α) := by
        refine ⟨hx.1, ?_⟩
        rintro c (rfl | rfl)
        · exact hzx
        · exact hx.2 (Set.mem_insert _ _)
      obtain ⟨m, hmM, hmx⟩ :=
        hmPair z (upperBoundsIn_subset (hMsub hzM)) a haA x hxpair
      exact ⟨m, Set.mem_iUnion₂.mpr ⟨z, hzM, hmM⟩, hmx⟩

/-- **Property m at every finite set of compact elements, unconditionally.**

This is `JungNets.forall_hasCompleteMub_of_jung_theorem_1_37` with `JungNets.Theorem137` — and
hence Iwamura's lemma — removed. The route is: `hasCompleteMub_pair` and
`hasCompleteMub_empty` supply property m at pairs and at `∅`; `propertyM_pairs`
supplies property M at pairs; `exists_finite_complete_of_pairs` lifts them to a
finite complete set of upper bounds for any finite set of compacts; and
`hasCompleteMub_of_finite_complete` turns that back into property m there.

The lift is Jung's Lemma 1.29 argument, which the development already carries as
`JungFinite.exists_finite_complete_upperBoundsIn`; only its hypothesis had to be
weakened. -/
theorem forall_hasCompleteMub (hAlgF : IsAlgebraic (ScottHom D D))
    (hCount : (compacts (ScottHom D D)).Countable) :
    ∀ v : Set D, v.Finite → v ⊆ compacts D → HasCompleteMub (compacts D) v := by
  intro v hv hvc
  obtain ⟨M, hMfin, hMsub, hMcomp⟩ :=
    exists_finite_complete_of_pairs hasCompleteMub_empty
      (fun a ha b hb => hasCompleteMub_pair hAlgF hCount ha hb)
      (fun a ha b hb => propertyM_pairs hAlgF hCount a b ha hb)
      (by rw [JungFinite.minimalUpperBounds_compacts_empty]; exact Set.finite_singleton _)
      hv hvc
  exact hasCompleteMub_of_finite_complete hMfin hMsub hMcomp

/-- **Theorem 18 reduced to one obligation: finiteness of `U^∞`.**

`MinimalUpperBounds.isBifinite_iff_mubClosure` splits bifiniteness into property m
at every finite set of compacts and finiteness of every `mubClosure`. The first
conjunct is what five rounds have spent on Jung's Theorem 1.37 and Iwamura's
lemma. It is **not needed in that generality**: `isNormalIn_of_pairs` reduces it
to pairs and the empty set, and `hasCompleteMub_pair` proves both from the
function space.

So what remains of Theorem 18 is `hfin` alone — Jung's Lemma 2.2, whose ingredients
are Rado's Selection Theorem and his Corollary 1.36, both already located in
`Section62.lean`. -/
theorem isBifinite_of_mubClosure_finite (hAlgF : IsAlgebraic (ScottHom D D))
    (hCount : (compacts (ScottHom D D)).Countable)
    (hfin : ∀ u : Set D, u.Finite → u ⊆ compacts D → (mubClosure (compacts D) u).Finite) :
    IsBifinite D := by
  intro u hu huA
  refine ⟨mubClosure (compacts D) u, hfin u hu huA, ?_, subset_mubClosure⟩
  refine isNormalIn_of_pairs (mubClosure_subset huA) (isMubClosed_mubClosure _ u)
    hasCompleteMub_empty fun a b ha hb => ?_
  exact hasCompleteMub_pair hAlgF hCount (mubClosure_subset huA ha) (mubClosure_subset huA hb)

end Unconditional

/-! ## Theorem 18 with Jung's Theorem 1.37 removed from its hypotheses -/

section Theorem18

variable {D : Type*} [CompletePartialOrder D] [Domain D] [Domain (ScottHom D D)]

/-- **Theorem 18, conditional on Corollary 1.36 alone.**

> **Theorem 18** If `D` and `D → D` are domains, then `D` is bifinite.

`JungFinite.theorem_18_of_propertyM` takes two hypotheses: property m at every finite
set of compacts (Jung's **Theorem 1.37**, five rounds of work, blocked on
Iwamura's lemma) and his **Corollary 1.36**. `forall_hasCompleteMub` proves the
first outright, so only Corollary 1.36 remains.

This is the round's deliverable stated against the assembly the development
already has: `ScottDomains.Theorem18.theorem_18_of_jung_theorem_1_37_chains` takes
`JungNets.Theorem137Chains α` and `FixedPointOfCompactDeflationIsCompact α`; this
takes the second and nothing else. -/
theorem theorem_18_of_jung_corollary_1_36
    (hcor : JungFinite.FixedPointOfCompactDeflationIsCompact D) :
    IsBifinite D :=
  JungFinite.theorem_18_of_propertyM hcor fun v hvc hvfin =>
    forall_hasCompleteMub (inferInstance : IsAlgebraic (ScottHom D D))
      (Domain.countable_compacts (α := ScottHom D D)) v hvfin hvc

end Theorem18

end ScottDomains.PropertyM
