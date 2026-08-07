import ScottDomains.BifiniteUniversal
import ScottDomains.IdealCompletion
-- `Finset.fintype`: `Finset α` is a `Fintype` when `α` is. Needed to show each
-- stage of the chain is finite, and not reachable from the imports above.
import Mathlib.Data.Fintype.Powerset

/-!
# §7.4's chain `I ⊴ I⁺ ⊴ I⁺⁺ ⊴ ⋯`, its colimit, and `V`

Gunter & Scott, *Semantic Domains*, §7.4, quoted from the source PDF
(`papers/Gunter Scott 1990.pdf`):

> **Theorem 29** If `D` is bifinite, then so is `D⁺`. Moreover, if `D ≅ D⁺` and
> `E` is any bifinite domain, then there is a projection `p : D → E`.

> A full proof of the theorem may be found in [Gun87]. We will attempt to offer
> some hint about how the desired fixed point is obtained. At the first step we
> take the domain `I = {⊥}` … The next step `I⁺⁺⁺` has 20 elements (up to
> equivalence in the sense just mentioned) … It should be noted that each stage
> of the construction is embedded in the next one by the map `x ↦ (x, {x})`.

> **Lemma 30** The following operators are p-representable over `V`: `→`, `⇸`,
> `×`, `⊗`, `+`, `⊕`, `()⊥`, `()♯`, `()♭`, `()♮`.

`BifiniteUniversal.thm29` proves the first sentence. This file builds the chain
whose colimit is §7.4's `V`, at the level of **posets** rather than domains:
`Plus D = IdealCompletion (MPair ↥(compacts D))`, so the iteration is an
iteration of `M` on countable posets and Theorem 11 (`IdealCompletion.instDomain`)
is applied once, at the end.

## The identification is part of the construction

`MPair A` is a genuine **pre**-order, not a partial order — `MPair.le_iff`'s
second disjunct is exactly §7.4's own "`(a, {a}) ⊢ (a, {a, b})` and
`(a, {a, b}) ⊢ (a, {a})` so we have identified these elements". So `MPair A` is
not a legal argument to `MPair` again, and the chain cannot be
`Aₙ₊₁ = MPair Aₙ`. `Step A = Antisymmetrization (MPair A) (· ≤ ·)` performs the
identification the paper performs by hand, and the paper's own element counts are
counts *after* it: "The next step `I⁺⁺⁺` has 20 elements (**up to equivalence in
the sense just mentioned**)". `Step` is therefore forced by the source, not a
convenience.

## Where the connecting map is **not** the paper's `x ↦ (x, {x})`

§7.4 says the embedding of each stage in the next is `eta`, `x ↦ (x, {x})`.
**The colimit along `eta` is not a fixed point of `M`, and this file uses a
different chain.** The obstruction is finite and checkable by hand.

Write `Aₙ` for stage `n` and let `(x, u) ∈ M(A_N)`, so that `[(x, u)] ∈ A_{N+1}`.
Read the same pair one stage later: its components in `A_{N+1}` are `eta x` and
`eta '' u`, giving `[(eta x, eta '' u)] ∈ A_{N+2}`. For a colimit map
`M(A_∞) → A_∞` to be well defined these two must agree, i.e. `eta` applied to
`[(x, u)]` must equal `[(eta x, eta '' u)]` in `A_{N+2}`; their bases are
`[(x, u)]` and `[(x, {x})]`, which are equal only when `↑u = ↑x`.
`etaChain_not_wellDefined` exhibits the failure at the paper's own second stage
with `u = ∅`.

The chain that does have `M` as its colimit is the standard one: the connecting
map at stage `n + 1` is `M` applied to the connecting map at stage `n`, starting
from the unique map out of `I = {⊥}`. That is `stgEmb` below. Both chains agree
at stage 0 → 1 — where the only map available is `⊥ ↦ ⊥ = (⊥, {⊥})`, which is
`eta` — and first differ at stage 1 → 2, where `eta` sends `b = (⊥, ∅)` to
`(b, {b})` while `M(eta)` sends it to `(a, ∅)`. Both are among §7.4's five
elements of `I⁺⁺`, so the paper's Figure 4 does not discriminate them.

**The stage sizes do not depend on the choice**, because they are sizes of
`Mⁿ(I)` modulo the identification and the connecting map does not enter: 1, 2, 5,
20 for the order `MPair.le` formalizes, against 1, 2, 5, 21 for the rival Smyth
reading (`scripts/mpair-stages.py`, re-run this round). So the check §7.4's
element counts supply still selects the same order.

## What is built

| # | Name | Content |
| - | ---- | ------- |
| 1 | `Step` | `A ↦ M(A)` followed by §7.4's identification |
| 2 | `Stg n` | stage `n`: `Stg 0 = PUnit`, `Stg (n+1) = Step (Stg n)` |
| 3 | `stgEmb n` | `Stg n ↪o Stg (n+1)`, `M` applied to the previous one |
| 4 | `liftStg` | `Stg n ↪o Stg m` for `n ≤ m`, by `Nat.leRecOn` |
| 5 | `Germ`, `Ainf` | the ω-colimit, as the antisymmetrization of a pre-order on `Σ n, Stg n` |
| 6 | `V` | `IdealCompletion Ainf`; `Domain V` and `IsBifinite V` |

## What is not built

`V ≅ V⁺` is **not** proved. The remaining step is that `M` is finitary — every
element of `M(A_∞)` already lies in the image of some `M(A_N)` — which turns
`Antisymmetrization (MPair Ainf) ≃o Ainf` into a surjectivity statement.
`exists_stage_of_finset` and `exists_stage_mpair` below discharge the finitariness
itself; what is missing is the four transports that carry it to `V⁺`:
`↥(compacts V) ≃o Ainf`, `M` on an `≃o`, `IdealCompletion` on an `≃o`, and
invariance of `IdealCompletion` under antisymmetrization. No `sorry` stands in
for any of them.
-/

namespace ScottDomains.Colimit

open ScottDomains ScottDomains.BifiniteUniversal

universe u v w

/-! ## `M` on order embeddings

`M` is a functor on posets and order-reflecting maps. `mpairMap` is its action on
maps; `mpairMap_le_mpairMap_iff` is that the action again reflects the order, and
`range_mpairMap` identifies its image with `MSub` of the image, which is what
lets `MSub_isNormalIn` be reused. -/

section Functor

variable {α : Type u} {β : Type v} [PartialOrder α] [PartialOrder β]

/-- `M(f)` for an order embedding `f`: apply `f` to the base and to every member
of the cover. `Finset.map` rather than `Finset.image`, so no `DecidableEq` is
needed. -/
def mpairMap (f : α ↪o β) (m : MPair α) : MPair β where
  base := f m.base
  cover := m.cover.map f.toEmbedding
  base_le := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hz
    exact f.map_rel_iff.mpr (m.base_le w hw)

@[simp] theorem mpairMap_base (f : α ↪o β) (m : MPair α) :
    (mpairMap f m).base = f m.base := rfl

@[simp] theorem mpairMap_cover (f : α ↪o β) (m : MPair α) :
    (mpairMap f m).cover = m.cover.map f.toEmbedding := rfl

/-- Every member of the cover is in the up-set it generates. -/
theorem mem_upper_of_mem_cover {m : MPair α} {z : α} (hz : z ∈ m.cover) : z ∈ m.upper :=
  ⟨z, hz, le_rfl⟩

/-- `f` transports the generated up-set: `f y` is in the image pair's up-set
exactly when `y` is in the original's. This is where order-reflection is
spent. -/
theorem mem_upper_mpairMap (f : α ↪o β) {m : MPair α} {y : α} :
    f y ∈ (mpairMap f m).upper ↔ y ∈ m.upper := by
  constructor
  · rintro ⟨z, hz, hzy⟩
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hz
    exact ⟨w, hw, f.map_rel_iff.mp hzy⟩
  · rintro ⟨z, hz, hzy⟩
    exact ⟨f z, Finset.mem_map_of_mem _ hz, f.map_rel_iff.mpr hzy⟩

theorem upper_mpairMap_subset (f : α ↪o β) {m n : MPair α} (h : m.upper ⊆ n.upper) :
    (mpairMap f m).upper ⊆ (mpairMap f n).upper := by
  rintro y ⟨z, hz, hzy⟩
  obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hz
  obtain ⟨w', hw', hw'w⟩ := h (mem_upper_of_mem_cover hw)
  exact ⟨f w', Finset.mem_map_of_mem _ hw', (f.map_rel_iff.mpr hw'w).trans hzy⟩

theorem upper_mpairMap_eq_iff (f : α ↪o β) {m n : MPair α} :
    (mpairMap f m).upper = (mpairMap f n).upper ↔ m.upper = n.upper := by
  constructor
  · intro h
    ext y
    rw [← mem_upper_mpairMap f, ← mem_upper_mpairMap f, h]
  · intro h
    exact Set.Subset.antisymm (upper_mpairMap_subset f h.subset)
      (upper_mpairMap_subset f h.symm.subset)

/-- **`M(f)` reflects the order.** Both disjuncts of `MPair.le_iff` transport:
the printed relation by `mem_upper_mpairMap`, the identification by injectivity
of `f` and `upper_mpairMap_eq_iff`. -/
theorem mpairMap_le_mpairMap_iff (f : α ↪o β) {m n : MPair α} :
    mpairMap f m ≤ mpairMap f n ↔ m ≤ n := by
  rw [MPair.le_iff, MPair.le_iff]
  constructor
  · rintro (h | ⟨hb, hu⟩)
    · exact Or.inl (mem_upper_mpairMap f (m := m) (y := n.base) |>.mp h)
    · exact Or.inr ⟨f.injective hb, (upper_mpairMap_eq_iff f).mp hu⟩
  · rintro (h | ⟨hb, hu⟩)
    · exact Or.inl ((mem_upper_mpairMap f (m := m) (y := n.base)).mpr h)
    · exact Or.inr ⟨congrArg f hb, (upper_mpairMap_eq_iff f).mpr hu⟩

/-- `M(f)`'s range is `M` of `f`'s range: a pair over `β` whose base and cover lie
in `im(f)` is the image of the pair got by pulling both back. This is what makes
`MSub_isNormalIn` applicable to `im(M(f))`. -/
theorem range_mpairMap (f : α ↪o β) : Set.range (mpairMap f) = MSub (Set.range f) := by
  classical
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨m, rfl⟩
    refine ⟨⟨m.base, rfl⟩, ?_⟩
    intro y hy
    obtain ⟨w, _, rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hy)
    exact ⟨w, rfl⟩
  · rintro m ⟨⟨b, hbm⟩, hc⟩
    have hcov : (m.cover.preimage f (f.injective.injOn)).map f.toEmbedding = m.cover := by
      ext y
      constructor
      · intro hy
        obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hy
        exact Finset.mem_preimage.mp hw
      · intro hy
        obtain ⟨w, rfl⟩ := hc (Finset.mem_coe.mpr hy)
        exact Finset.mem_map_of_mem _ (Finset.mem_preimage.mpr hy)
    refine ⟨⟨b, m.cover.preimage f (f.injective.injOn), ?_⟩, ?_⟩
    · intro z hz
      have hz' : m.base ≤ f z := m.base_le _ (Finset.mem_preimage.mp hz)
      rw [← hbm] at hz'
      exact f.map_rel_iff.mp hz'
    · exact MPair.ext hbm hcov

theorem mpairMap_eta (f : α ↪o β) (x : α) : mpairMap f (eta x) = eta (f x) :=
  MPair.ext rfl (by simp [mpairMap, eta])

end Functor

/-! ## Normality transported along an order-reflecting map -/

section NormalTransport

variable {α : Type u} {β : Type v} [Preorder α] [Preorder β]

/-- A monotone order-**reflecting** map carries a normal subposet of `α` to a
normal subposet of its own range: `f '' (S ∩ ↓a) = (f '' S) ∩ ↓(f a)`, the
inclusion `⊇` being where reflection is spent. Companion of
`BifiniteUniversal.isPlotkinOrder_image`. -/
theorem isNormalIn_image_range {f : α → β} (hf : ∀ a b : α, f a ≤ f b ↔ a ≤ b)
    {S : Set α} (h : S ◁ (Set.univ : Set α)) : f '' S ◁ Set.range f := by
  refine ⟨fun _ ⟨a, ha, hfa⟩ => ⟨a, hfa⟩, ?_⟩
  rintro _ ⟨a, rfl⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨s, hsS, hsa⟩ := h.nonempty (Set.mem_univ a)
    exact ⟨f s, ⟨s, hsS, rfl⟩, (hf s a).mpr hsa⟩
  · rintro _ ⟨⟨s₁, hs₁, rfl⟩, hle₁⟩ _ ⟨⟨s₂, hs₂, rfl⟩, hle₂⟩
    obtain ⟨s, ⟨hsS, hsa⟩, h₁, h₂⟩ :=
      h.directedOn (Set.mem_univ a) s₁ ⟨hs₁, (hf s₁ a).mp hle₁⟩ s₂ ⟨hs₂, (hf s₂ a).mp hle₂⟩
    exact ⟨f s, ⟨⟨s, hsS, rfl⟩, (hf s a).mpr hsa⟩, (hf s₁ s).mpr h₁, (hf s₂ s).mpr h₂⟩

/-- The surjective case: a monotone order-reflecting surjection carries a normal
subposet of the whole of `α` to a normal subposet of the whole of `β`. -/
theorem isNormalIn_image_univ {f : α → β} (hf : ∀ a b : α, f a ≤ f b ↔ a ≤ b)
    (hsurj : Function.Surjective f) {S : Set α} (h : S ◁ (Set.univ : Set α)) :
    f '' S ◁ (Set.univ : Set β) := by
  have := isNormalIn_image_range hf h
  rwa [hsurj.range_eq] at this

end NormalTransport

/-! ## One step of the chain -/

section Step

variable (α : Type u) [PartialOrder α]

/-- **One step of §7.4's chain**: `M(A)` with the paper's identification
performed. The identification is not optional — `MPair A` is a pre-order, so
`MPair (MPair A)` does not typecheck, and the paper's own counts are counts after
it. -/
def Step : Type u := Antisymmetrization (MPair α) (· ≤ ·)

instance instPartialOrderStep : PartialOrder (Step α) :=
  inferInstanceAs (PartialOrder (Antisymmetrization (MPair α) (· ≤ ·)))

variable {α}

/-- The class of a pair, as a point of the next stage. -/
def mk (m : MPair α) : Step α := toAntisymmetrization (· ≤ ·) m

theorem mk_surjective : Function.Surjective (mk : MPair α → Step α) :=
  fun q => Quotient.inductionOn' q fun m => ⟨m, rfl⟩

@[simp] theorem mk_le_mk {m n : MPair α} : (mk m : Step α) ≤ mk n ↔ m ≤ n := Iff.rfl

@[elab_as_elim]
protected theorem Step.ind {p : Step α → Prop} (h : ∀ m : MPair α, p (mk m)) (q : Step α) : p q :=
  Quotient.inductionOn' q h

instance instOrderBotStep [OrderBot α] : OrderBot (Step α) where
  bot := mk ⊥
  bot_le q := Step.ind (p := fun r => mk (⊥ : MPair α) ≤ r) (fun _ => mk_le_mk.mpr bot_le) q

@[simp] theorem bot_eq_mk_bot [OrderBot α] : (⊥ : Step α) = mk ⊥ := rfl

instance instCountableStep [Countable α] : Countable (Step α) :=
  inferInstanceAs (Countable (Quotient _))

instance instFiniteStep [Finite α] : Finite (Step α) := by
  haveI : Fintype α := Fintype.ofFinite α
  haveI : Fintype (Finset α) := Finset.fintype
  haveI : Finite (MPair α) :=
    Finite.of_injective (fun m : MPair α => (m.base, m.cover))
      (fun m n h => MPair.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  exact inferInstanceAs (Finite (Quotient _))

/-- `M(f)` on the identified stage. -/
def stepEmb {β : Type v} [PartialOrder β] (f : α ↪o β) : Step α ↪o Step β :=
  OrderEmbedding.ofMapLEIff
    (fun q => Quotient.liftOn' q (fun m => (mk (mpairMap f m) : Step β))
      (fun _ _ h => Quotient.sound' ⟨(mpairMap_le_mpairMap_iff f).mpr h.1,
        (mpairMap_le_mpairMap_iff f).mpr h.2⟩))
    (fun a b => Quotient.inductionOn₂' a b fun _ _ => mpairMap_le_mpairMap_iff f)

@[simp] theorem stepEmb_mk {β : Type v} [PartialOrder β] (f : α ↪o β) (m : MPair α) :
    stepEmb f (mk m) = mk (mpairMap f m) := rfl

theorem range_stepEmb {β : Type v} [PartialOrder β] (f : α ↪o β) :
    Set.range (stepEmb f) = mk '' Set.range (mpairMap f) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨q, rfl⟩
    induction q using Step.ind with
    | h m => exact ⟨mpairMap f m, ⟨m, rfl⟩, rfl⟩
  · rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
    exact ⟨mk m, rfl⟩

theorem stepEmb_bot {β : Type v} [PartialOrder β] [OrderBot α] [OrderBot β] (f : α ↪o β)
    (hf : f ⊥ = ⊥) : stepEmb f (⊥ : Step α) = ⊥ := by
  show mk (mpairMap f (eta ⊥)) = mk (eta ⊥)
  rw [mpairMap_eta, hf]

end Step

/-! ## The stage tower

`Stg n` is carried together with its `PartialOrder`, because `Step` needs its
argument's order to state the next type. A `Sigma`-valued recursion is the
cheapest way to define a type and its instance simultaneously; `Stg_succ` records
that the projection is definitionally the step. -/

/-- Stage `n` of the chain, bundled with its partial order. -/
def stage : ℕ → Σ T : Type, PartialOrder T
  | 0 => ⟨PUnit, inferInstance⟩
  | n + 1 => ⟨@Step (stage n).1 (stage n).2, @instPartialOrderStep (stage n).1 (stage n).2⟩

/-- The carrier of stage `n`: `Stg 0 = I = {⊥}`, `Stg (n+1) = Stg n ⁺`. -/
def Stg (n : ℕ) : Type := (stage n).1

instance instPartialOrderStg (n : ℕ) : PartialOrder (Stg n) := (stage n).2

/-- The same instance keyed on `(stage n).1` instead of on `Stg n`. Typeclass
resolution indexes on the head symbol, and unifying an expected `Stg (n+1)`
against `Step ?α` unfolds through `stage` and leaves the goal in `Sigma.fst`
form; without this alias every such goal fails to synthesize. The two are
definitionally the same instance, so no diamond is created. -/
instance instPartialOrderStageFst (n : ℕ) : PartialOrder (stage n).1 := (stage n).2

theorem Stg_zero : Stg 0 = PUnit := rfl

theorem Stg_succ (n : ℕ) : Stg (n + 1) = Step (Stg n) := rfl

instance instSubsingletonStgZero : Subsingleton (Stg 0) :=
  inferInstanceAs (Subsingleton PUnit)

instance instOrderBotStg : ∀ n : ℕ, OrderBot (Stg n)
  | 0 => { bot := (PUnit.unit : PUnit), bot_le := fun _ => le_of_eq (Subsingleton.elim _ _) }
  | n + 1 => @instOrderBotStep (Stg n) (instPartialOrderStg n) (instOrderBotStg n)

instance instFiniteStg : ∀ n : ℕ, Finite (Stg n)
  | 0 => inferInstanceAs (Finite PUnit)
  | n + 1 => @instFiniteStep (Stg n) (instPartialOrderStg n) (instFiniteStg n)

instance instCountableStg (n : ℕ) : Countable (Stg n) := Finite.to_countable

/-- The connecting map `Stg n ↪o Stg (n+1)`. At stage 0 it is the unique map out
of `I = {⊥}` — which is also §7.4's `x ↦ (x, {x})`, since `⊥ = (⊥, {⊥})` — and at
every later stage it is `M` applied to the previous one. See the module docstring
for why it is *not* `eta` at the later stages. -/
def stgEmb : ∀ n : ℕ, Stg n ↪o Stg (n + 1)
  | 0 => OrderEmbedding.ofMapLEIff (fun _ => (⊥ : Stg 1))
      (fun a b => iff_of_true le_rfl (le_of_eq (Subsingleton.elim a b)))
  | n + 1 =>
      @stepEmb (Stg n) (instPartialOrderStg n) (Stg (n + 1)) (instPartialOrderStg (n + 1))
        (stgEmb n)

theorem stgEmb_succ (n : ℕ) :
    stgEmb (n + 1) =
      @stepEmb (Stg n) (instPartialOrderStg n) (Stg (n + 1)) (instPartialOrderStg (n + 1))
        (stgEmb n) := rfl

theorem stgEmb_bot : ∀ n : ℕ, stgEmb n (⊥ : Stg n) = (⊥ : Stg (n + 1))
  | 0 => rfl
  | n + 1 => stepEmb_bot (stgEmb n) (stgEmb_bot n)

/-- **Each stage is normal in the next.** Stage 0's image is `{⊥}`
(`singleton_bot_isNormalIn`); the step is `MSub_isNormalIn` — `M(N) ◁ M(A)`
whenever `N ◁ A`, which is the lemma Theorem 29's first sentence turns on —
transported through `range_mpairMap` and then through the identification by
`isNormalIn_image_univ`. -/
theorem isNormalIn_range_stgEmb :
    ∀ n : ℕ, Set.range (stgEmb n) ◁ (Set.univ : Set (Stg (n + 1)))
  | 0 => by
    have : Set.range (stgEmb 0) = ({⊥} : Set (Stg 1)) := by
      ext y
      exact ⟨by rintro ⟨x, rfl⟩; rfl, by rintro rfl; exact ⟨PUnit.unit, rfl⟩⟩
    rw [this]
    exact singleton_bot_isNormalIn (Set.mem_univ _)
  | n + 1 => by
    have hM : Set.range (mpairMap (stgEmb n)) ◁ (Set.univ : Set (MPair (Stg (n + 1)))) := by
      rw [range_mpairMap]
      exact MSub_isNormalIn (isNormalIn_range_stgEmb n)
    have hstep : Set.range (stgEmb (n + 1)) =
        (mk : MPair (Stg (n + 1)) → Stg (n + 2)) '' Set.range (mpairMap (stgEmb n)) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        obtain ⟨m, rfl⟩ := mk_surjective (α := Stg n) x
        exact ⟨mpairMap (stgEmb n) m, ⟨m, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨m, rfl⟩, rfl⟩
        exact ⟨mk m, rfl⟩
    rw [hstep]
    exact isNormalIn_image_univ (f := (mk : MPair (Stg (n + 1)) → Stg (n + 2)))
      (fun _ _ => Iff.rfl) mk_surjective hM

/-! ## Lifting across the tower -/

/-- `Stg n → Stg m` for `n ≤ m`, the composite of the connecting maps.
`Nat.leRecOn` gives it without a single dependent cast: the family is `Stg`
itself and the step is `stgEmb`. -/
def liftStg {n m : ℕ} (h : n ≤ m) (x : Stg n) : Stg m :=
  Nat.leRecOn h (fun {k} (y : Stg k) => stgEmb k y) x

@[simp] theorem liftStg_self {n : ℕ} (x : Stg n) : liftStg (le_refl n) x = x :=
  Nat.leRecOn_self x

theorem liftStg_succ {n m : ℕ} (h : n ≤ m) (x : Stg n) (h' : n ≤ m + 1) :
    liftStg h' x = stgEmb m (liftStg h x) := Nat.leRecOn_succ h x

theorem liftStg_trans {n m k : ℕ} (h₁ : n ≤ m) (h₂ : m ≤ k) (x : Stg n) (h : n ≤ k) :
    liftStg h x = liftStg h₂ (liftStg h₁ x) := Nat.leRecOn_trans h₁ h₂ x

theorem liftStg_le_liftStg {n m : ℕ} (h : n ≤ m) (x y : Stg n) :
    liftStg h x ≤ liftStg h y ↔ x ≤ y := by
  induction m, h using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [liftStg_succ hm x, liftStg_succ hm y, (stgEmb m).map_rel_iff]
    exact ih

theorem liftStg_bot {n m : ℕ} (h : n ≤ m) : liftStg h (⊥ : Stg n) = (⊥ : Stg m) := by
  induction m, h using Nat.le_induction with
  | base => simp
  | succ m hm ih => rw [liftStg_succ hm, ih, stgEmb_bot]

/-- `liftStg` bundled as an order embedding. -/
def liftEmb {n m : ℕ} (h : n ≤ m) : Stg n ↪o Stg m :=
  OrderEmbedding.ofMapLEIff (liftStg h) (liftStg_le_liftStg h)

@[simp] theorem liftEmb_apply {n m : ℕ} (h : n ≤ m) (x : Stg n) : liftEmb h x = liftStg h x := rfl

/-- **Every stage is normal in every later stage.** Induction on `n ≤ m`: the
image of a normal set along an order embedding is normal in that embedding's
range (`isNormalIn_image_range`), and the range is normal in the whole of the
next stage (`isNormalIn_range_stgEmb`), so Lemma 4.1 (`IsNormalIn.trans`)
composes them. -/
theorem isNormalIn_range_liftStg {n m : ℕ} (h : n ≤ m) :
    Set.range (liftStg h) ◁ (Set.univ : Set (Stg m)) := by
  induction m, h using Nat.le_induction with
  | base =>
    have : Set.range (liftStg (le_refl n)) = (Set.univ : Set (Stg n)) := by
      ext y; exact ⟨fun _ => Set.mem_univ _, fun _ => ⟨y, by simp⟩⟩
    rw [this]
    exact IsNormalIn.refl _
  | succ m hm ih =>
    have hr : Set.range (liftStg (hm.trans (Nat.le_succ m))) =
        (stgEmb m) '' Set.range (liftStg hm) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨liftStg hm x, ⟨x, rfl⟩, (liftStg_succ hm x _).symm⟩
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, liftStg_succ hm x _⟩
    rw [hr]
    exact IsNormalIn.trans
      (isNormalIn_image_range (fun _ _ => (stgEmb m).map_rel_iff) ih)
      (isNormalIn_range_stgEmb m)

end ScottDomains.Colimit
