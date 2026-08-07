import ScottDomains.BifiniteUniversal
import ScottDomains.IdealCompletion
-- `IsPRepresentable₂` and `Cpo.funSpace`, for stating Lemma 30's first conjunct;
-- `IsEmbeddingProjectionPair`, for stating Theorem 29's second sentence. Both
-- statements are new here only because `V` is.
import ScottDomains.PRepresentable
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
| 6 | `V` | `IdealCompletion Ainf`; `Domain V` (`domain_V`) and `IsBifinite V` (`isBifinite_V`) |
| 7 | `expand` | `A∞ → M(A∞)/≈`, order-reflecting and surjective — `M` is finitary |
| 8 | `idealCongr` | ideal completions agree along a monotone order-reflecting surjection |
| 9 | `isoPlus` | **`V ≅ V⁺`**, and `iso_plus_V` for the cpo form |

`isoPlus` is `idealCongr` applied three times: to `expand` (the fixed point), to
`mk` backwards (the identification), and to `M(toCompacts)` (`A∞ = K(V)`). The
one hypothesis `idealCongr` needs is a monotone order-reflecting **surjection** —
injectivity is not required, which is what lets the identification `M(A) → M(A)/≈`
be an instance of it.

`incl_pointB1_ne_bot` and `principal_pointB1_ne_bot` check that `A∞` and `V` are
not one-point, so `isoPlus` is not vacuous.

## What is not built

Neither of the two results §7.4 defers to [Gun87] is proved; each is now
**statable** for the first time, and each is recorded as a `Prop` at the end of
this file with the missing step named.

| # | statement | what is missing |
| - | --------- | --------------- |
| 1 | `Thm29Second` — Theorem 29's second sentence at `D = V` | the universality argument: extending a normal embedding of a finite normal subposet of `K(E)` into `Stg n` to the next one into `Stg (n+1)` |
| 2 | `Lem30Arrow` — Lemma 30's `→` conjunct | a representation of the function space over `V`; the paper's other **nine** operators are not present in this development as functions `Cpo → Cpo` at all |

No `sorry` stands in for either.
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

/-- `M(f)` is surjective when `f` is: `range_mpairMap` plus `MSub Set.univ = Set.univ`. -/
theorem surjective_mpairMap {f : α ↪o β} (hs : Function.Surjective f) :
    Function.Surjective (mpairMap f) := by
  intro m
  have hm : m ∈ MSub (Set.range f) := by
    rw [hs.range_eq]
    exact ⟨Set.mem_univ _, fun _ _ => Set.mem_univ _⟩
  rw [← range_mpairMap] at hm
  exact hm

theorem mpairMap_congr {f g : α ↪o β} (h : ∀ x, f x = g x) (m : MPair α) :
    mpairMap f m = mpairMap g m := by
  refine MPair.ext (h m.base) (Finset.ext fun y => ?_)
  simp only [mpairMap_cover, Finset.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, (h a).symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, h a⟩

theorem mpairMap_trans {γ : Type w} [PartialOrder γ] (f : α ↪o β) (g : β ↪o γ) (m : MPair α) :
    mpairMap g (mpairMap f m) = mpairMap (f.trans g) m := by
  refine MPair.ext rfl ?_
  simp only [mpairMap_cover, Finset.map_map]
  rfl

end Functor

/-! ## The ideal completion of a pre-order depends only on its poset reflection

A monotone order-**reflecting surjection** — not necessarily injective — induces
an order isomorphism of ideal completions, by direct image and preimage. It is
the one transport the fixed point needs, and it covers all three steps: the
identification `M(A) → M(A)/≈`, the passage between `A∞` and `K(V)`, and the
fixed-point map itself. -/

section IdealTransport

variable {α : Type u} {β : Type v} [Preorder α] [Preorder β] {f : α → β}

theorem isIdeal_image (hf : ∀ a b : α, f a ≤ f b ↔ a ≤ b) (hs : Function.Surjective f)
    (I : IdealCompletion α) : Order.IsIdeal (f '' (I : Set α)) := by
  refine ⟨?_, I.nonempty.image f, ?_⟩
  · intro y z hzy hy
    obtain ⟨a, ha, rfl⟩ := hy
    obtain ⟨b, rfl⟩ := hs z
    exact ⟨b, I.lower ((hf b a).mp hzy) ha, rfl⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨c, hc, hac, hbc⟩ := I.directed a ha b hb
    exact ⟨f c, ⟨c, hc, rfl⟩, (hf a c).mpr hac, (hf b c).mpr hbc⟩

theorem isIdeal_preimage (hf : ∀ a b : α, f a ≤ f b ↔ a ≤ b) (hs : Function.Surjective f)
    (J : IdealCompletion β) : Order.IsIdeal (f ⁻¹' (J : Set β)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b hba ha
    exact J.lower ((hf b a).mpr hba) ha
  · obtain ⟨y, hy⟩ := J.nonempty
    obtain ⟨x, rfl⟩ := hs y
    exact ⟨x, hy⟩
  · intro a ha b hb
    obtain ⟨c, hc, hac, hbc⟩ := J.directed (f a) ha (f b) hb
    obtain ⟨z, rfl⟩ := hs c
    exact ⟨z, hc, (hf a z).mp hac, (hf b z).mp hbc⟩

/-- **The ideal completions of `α` and `β` agree along a monotone order-reflecting
surjection.** Direct image and preimage are mutually inverse: `f⁻¹(f(I)) = I`
needs order-reflection (`f x = f a` forces `x` and `a` equivalent, and `I` is
downward closed), and `f(f⁻¹(J)) = J` needs surjectivity. Injectivity of `f` is
*not* required, which is what lets it be applied to the identification
`MPair A → Step A`. -/
def idealCongr (hf : ∀ a b : α, f a ≤ f b ↔ a ≤ b) (hs : Function.Surjective f) :
    IdealCompletion α ≃o IdealCompletion β where
  toFun I := IdealCompletion.ofIdeal (isIdeal_image hf hs I).toIdeal
  invFun J := IdealCompletion.ofIdeal (isIdeal_preimage hf hs J).toIdeal
  left_inv I := by
    refine SetLike.coe_injective ?_
    show f ⁻¹' (f '' (I : Set α)) = (I : Set α)
    refine Set.Subset.antisymm ?_ (Set.subset_preimage_image _ _)
    rintro x ⟨a, ha, hfa⟩
    exact I.lower ((hf x a).mp (le_of_eq hfa.symm)) ha
  right_inv J := by
    refine SetLike.coe_injective ?_
    show f '' (f ⁻¹' (J : Set β)) = (J : Set β)
    exact Set.image_preimage_eq _ hs
  map_rel_iff' {I I'} := by
    show (f '' (I : Set α) ⊆ f '' (I' : Set α)) ↔ (I : Set α) ⊆ (I' : Set α)
    refine ⟨fun h x hx => ?_, Set.image_mono⟩
    obtain ⟨a, ha, hfa⟩ := h ⟨x, hx, rfl⟩
    exact I'.lower ((hf x a).mp (le_of_eq hfa.symm)) ha

end IdealTransport

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

/-! ## The connecting map is not `eta`, kernel-checked

§7.4 states that "each stage of the construction is embedded in the next one by
the map `x ↦ (x, {x})`". At stage 0 → 1 that is the only map available and it is
`stgEmb 0`. At stage 1 → 2 the two differ, and the difference is what makes the
`eta` chain's colimit fail to be a fixed point of `M`: `eta` sends §7.4's
`b = (⊥, ∅)` to `(b, {b})` while `M` applied to the previous connecting map sends
it to `(a, ∅)`. Both are among §7.4's own five elements of `I⁺⁺`. -/

section EtaCounterexample

/-- §7.4's `b = (⊥, ∅)`, as a point of stage 1. -/
def pointB1 : Stg 1 := mk (⟨(⊥ : Stg 0), ∅, by simp⟩ : MPair (Stg 0))

/-- `b` is not `⊥ = a = (⊥, {⊥})`: the printed relation fails because the cover is
empty, and the identification fails because `∅` and `↑⊥` generate different
up-sets. -/
theorem not_pointB1_le_bot : ¬ (pointB1 ≤ (⊥ : Stg 1)) := by
  rintro (⟨z, hz, -⟩ | ⟨-, hu⟩)
  · exact absurd hz (Finset.notMem_empty z)
  · have hmem : (⊥ : Stg 0) ∈ (⊥ : MPair (Stg 0)).upper := mem_upper_eta.mpr le_rfl
    obtain ⟨z, hz, -⟩ := (Set.ext_iff.mp hu (⊥ : Stg 0)).mpr hmem
    exact absurd hz (Finset.notMem_empty z)

theorem pointB1_ne_bot : pointB1 ≠ (⊥ : Stg 1) := fun h => not_pointB1_le_bot (le_of_eq h)

/-- **The connecting map differs from §7.4's `eta` at the second step.** If they
agreed at `b` then `eta b ⊑ (a, ∅)` in `M(I⁺)`, and both disjuncts of
`MPair.le_iff` force `b ⊑ a = ⊥`, which `not_pointB1_le_bot` refutes. -/
theorem stgEmb_ne_mk_eta : stgEmb 1 pointB1 ≠ mk (eta pointB1) := by
  intro h
  have hstep : (mk (eta pointB1) : Stg 2) ≤ stgEmb 1 pointB1 := le_of_eq h.symm
  have hle : eta pointB1 ≤ mpairMap (stgEmb 0) (⟨(⊥ : Stg 0), ∅, by simp⟩ : MPair (Stg 0)) :=
    hstep
  have hbase : (mpairMap (stgEmb 0) (⟨(⊥ : Stg 0), ∅, by simp⟩ : MPair (Stg 0))).base
      = (⊥ : Stg 1) := stgEmb_bot 0
  rcases hle with hp | ⟨hb, -⟩
  · rw [MPair.PaperLE, hbase] at hp
    exact not_pointB1_le_bot (mem_upper_eta.mp hp)
  · exact pointB1_ne_bot (hbase ▸ hb)

end EtaCounterexample

/-! ## The ω-colimit `A∞` -/

/-- A **germ**: an element of some stage of the chain. -/
def Germ : Type := Σ n : ℕ, Stg n

instance instCountableGerm : Countable Germ := inferInstanceAs (Countable (Σ n : ℕ, Stg n))

/-- The pre-order on germs: lift both to the later of the two stages and compare
there. `germLE_at` says any common stage gives the same answer, because `liftStg`
is an order embedding. -/
def germLE (p q : Germ) : Prop :=
  liftStg (le_max_left p.1 q.1) p.2 ≤ liftStg (le_max_right p.1 q.1) q.2

/-- **The comparison does not depend on the stage it is taken at.** -/
theorem germLE_at {p q : Germ} {N : ℕ} (hp : p.1 ≤ N) (hq : q.1 ≤ N) :
    germLE p q ↔ liftStg hp p.2 ≤ liftStg hq q.2 := by
  have hMN : max p.1 q.1 ≤ N := max_le hp hq
  rw [liftStg_trans (le_max_left p.1 q.1) hMN p.2 hp,
    liftStg_trans (le_max_right p.1 q.1) hMN q.2 hq, liftStg_le_liftStg hMN]
  exact Iff.rfl

theorem germLE_refl (p : Germ) : germLE p p :=
  (germLE_at (le_refl p.1) (le_refl p.1)).mpr le_rfl

theorem germLE_trans {p q r : Germ} (h₁ : germLE p q) (h₂ : germLE q r) : germLE p r := by
  have hp : p.1 ≤ max (max p.1 q.1) r.1 := (le_max_left p.1 q.1).trans (le_max_left _ _)
  have hq : q.1 ≤ max (max p.1 q.1) r.1 := (le_max_right p.1 q.1).trans (le_max_left _ _)
  have hr : r.1 ≤ max (max p.1 q.1) r.1 := le_max_right _ _
  exact (germLE_at hp hr).mpr
    (((germLE_at hp hq).mp h₁).trans ((germLE_at hq hr).mp h₂))

instance instPreorderGerm : Preorder Germ where
  le := germLE
  le_refl := germLE_refl
  le_trans _ _ _ := germLE_trans

/-- **`A∞`**, the ω-colimit of `I ⊴ I⁺ ⊴ I⁺⁺ ⊴ ⋯`: germs modulo the pre-order's
own equivalence, which is the same identification `Step` performs at each finite
stage. -/
def Ainf : Type := Antisymmetrization Germ (· ≤ ·)

instance instPartialOrderAinf : PartialOrder Ainf :=
  inferInstanceAs (PartialOrder (Antisymmetrization Germ (· ≤ ·)))

instance instCountableAinf : Countable Ainf := inferInstanceAs (Countable (Quotient _))

/-- The canonical map from stage `n` into the colimit. -/
def incl (n : ℕ) (x : Stg n) : Ainf := toAntisymmetrization (· ≤ ·) (⟨n, x⟩ : Germ)

theorem incl_surjective (q : Ainf) : ∃ (n : ℕ) (x : Stg n), incl n x = q :=
  Quotient.inductionOn' q fun p => ⟨p.1, p.2, rfl⟩

/-- Comparison in the colimit is comparison at any stage above both indices. -/
theorem incl_le_incl_iff {n m N : ℕ} (x : Stg n) (y : Stg m) (hn : n ≤ N) (hm : m ≤ N) :
    incl n x ≤ incl m y ↔ liftStg hn x ≤ liftStg hm y := germLE_at hn hm

/-- **Each `incl n` is an order embedding**: the colimit does not collapse a
stage. -/
@[simp] theorem incl_le_incl {n : ℕ} (x y : Stg n) : incl n x ≤ incl n y ↔ x ≤ y := by
  rw [incl_le_incl_iff x y (le_refl n) (le_refl n), liftStg_self, liftStg_self]

theorem incl_injective (n : ℕ) : Function.Injective (incl n) := fun x y h =>
  le_antisymm ((incl_le_incl x y).mp h.le) ((incl_le_incl y x).mp h.ge)

theorem incl_lift {n m : ℕ} (h : n ≤ m) (x : Stg n) : incl m (liftStg h x) = incl n x := by
  refine le_antisymm ?_ ?_
  · rw [incl_le_incl_iff _ _ (le_refl m) h, liftStg_self]
  · rw [incl_le_incl_iff _ _ h (le_refl m), liftStg_self]

theorem range_incl_subset {n m : ℕ} (h : n ≤ m) : Set.range (incl n) ⊆ Set.range (incl m) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨liftStg h x, incl_lift h x⟩

theorem incl_zero_le (q : Ainf) : incl 0 (⊥ : Stg 0) ≤ q := by
  obtain ⟨m, y, rfl⟩ := incl_surjective q
  rw [incl_le_incl_iff _ _ (Nat.zero_le m) (le_refl m), liftStg_bot, liftStg_self]
  exact bot_le

instance instOrderBotAinf : OrderBot Ainf where
  bot := incl 0 ⊥
  bot_le := incl_zero_le

/-- Each stage's `⊥` is the colimit's `⊥`, because every connecting map preserves
it (`stgEmb_bot`). -/
theorem incl_bot (n : ℕ) : incl n (⊥ : Stg n) = (⊥ : Ainf) := by
  show incl n ⊥ = incl 0 ⊥
  rw [← liftStg_bot (Nat.zero_le n), incl_lift]

/-- **Every stage is normal in the colimit.** Directedness reduces to
`isNormalIn_range_liftStg` at a stage above both the two elements and the bound;
nonemptiness is `⊥`. -/
theorem isNormalIn_range_incl (n : ℕ) : Set.range (incl n) ◁ (Set.univ : Set Ainf) := by
  refine ⟨Set.subset_univ _,
    fun q _ => ⟨⟨⊥, ⟨(⊥ : Stg n), incl_bot n⟩, Set.mem_Iic.mpr bot_le⟩, ?_⟩⟩
  rintro _ ⟨⟨x₁, rfl⟩, hq₁⟩ _ ⟨⟨x₂, rfl⟩, hq₂⟩
  obtain ⟨m, y, rfl⟩ := incl_surjective q
  have hn : n ≤ max n m := le_max_left n m
  have hm : m ≤ max n m := le_max_right n m
  have h₁ : liftStg hn x₁ ≤ liftStg hm y := (incl_le_incl_iff x₁ y hn hm).mp (Set.mem_Iic.mp hq₁)
  have h₂ : liftStg hn x₂ ≤ liftStg hm y := (incl_le_incl_iff x₂ y hn hm).mp (Set.mem_Iic.mp hq₂)
  obtain ⟨_, ⟨⟨x₃, rfl⟩, hz⟩, hz₁, hz₂⟩ :=
    (isNormalIn_range_liftStg hn).directedOn (Set.mem_univ (liftStg hm y))
      (liftStg hn x₁) ⟨⟨x₁, rfl⟩, Set.mem_Iic.mpr h₁⟩
      (liftStg hn x₂) ⟨⟨x₂, rfl⟩, Set.mem_Iic.mpr h₂⟩
  refine ⟨incl n x₃,
    ⟨⟨x₃, rfl⟩, Set.mem_Iic.mpr ((incl_le_incl_iff x₃ y hn hm).mpr (Set.mem_Iic.mp hz))⟩,
    (incl_le_incl x₁ x₃).mpr ((liftStg_le_liftStg hn x₁ x₃).mp hz₁),
    (incl_le_incl x₂ x₃).mpr ((liftStg_le_liftStg hn x₂ x₃).mp hz₂)⟩

/-- **`M` is finitary at the level of sets**: a finite subset of the colimit
already lies in a single stage, because finitely many indices have a maximum. -/
theorem exists_stage_of_finite {S : Set Ainf} (hS : S.Finite) :
    ∃ N : ℕ, S ⊆ Set.range (incl N) := by
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨0, Set.empty_subset _⟩
  | @insert a s _ _ ih =>
    obtain ⟨N, hN⟩ := ih
    obtain ⟨n, x, rfl⟩ := incl_surjective a
    refine ⟨max n N, ?_⟩
    rintro y (rfl | hy)
    · exact range_incl_subset (le_max_left n N) ⟨x, rfl⟩
    · exact range_incl_subset (le_max_right n N) (hN hy)

/-- **`A∞` is a Plotkin order.** The finite normal subposet witnessing a finite
`u` is a whole stage: finite because every `Stg N` is
(`instFiniteStg`), normal by `isNormalIn_range_incl`, and above `u` by
`exists_stage_of_finite`. -/
theorem isPlotkinOrder_Ainf : IsPlotkinOrder (Set.univ : Set Ainf) := by
  intro u hu _
  obtain ⟨N, hN⟩ := exists_stage_of_finite hu
  exact ⟨Set.range (incl N), Set.finite_range _, isNormalIn_range_incl N, hN⟩

/-! ## `V` -/

/-- **`V`** (Gunter & Scott §7.4): the domain of ideals over the colimit of
`I ⊴ I⁺ ⊴ I⁺⁺ ⊴ ⋯`. Theorem 11 (`IdealCompletion.instDomain`) supplies its whole
domain structure, because `A∞` is a countable pre-order with a least element. -/
abbrev V : Type := IdealCompletion Ainf

/-- `V` is a domain: `A∞` is countable (`instCountableAinf`) with a least element
(`instOrderBotAinf`), which is exactly what **Theorem 11** consumes. -/
theorem domain_V : Domain V := inferInstance

/-- **`V` is bifinite.** `A∞` is a Plotkin order and `principal` reflects the
order, so `isPlotkinOrder_image` carries it onto `K(V) = im(principal)` — the
same two steps `thm29` takes for `D⁺`. -/
theorem isBifinite_V : IsBifinite V := by
  have h := isPlotkinOrder_image
    (f := (IdealCompletion.principal : Ainf → V))
    (fun _ _ => principal_le_principal_iff) isPlotkinOrder_Ainf
  rw [Set.image_univ] at h
  rw [IsBifinite, IdealCompletion.compacts_eq_range_principal]
  exact h

/-! ## `A∞` is a fixed point of `M`

`expand` sends a point of the colimit to its decomposition as a pair over the
colimit: an element of `Stg (n+1)` *is* a class of pairs over `Stg n`, and
pushing its base and cover into `A∞` gives a point of `Step A∞`. It is
well defined precisely because the connecting map is `M` applied to the previous
one — `expandStg_stgEmb` is where that is spent, and it is the step that fails
for §7.4's `eta` chain (`stgEmb_ne_mk_eta`). -/

section FixedPoint

/-- `incl n` as an order embedding. -/
def inclEmb (n : ℕ) : Stg n ↪o Ainf := OrderEmbedding.ofMapLEIff (incl n) incl_le_incl

@[simp] theorem inclEmb_apply (n : ℕ) (x : Stg n) : inclEmb n x = incl n x := rfl

theorem liftStg_one_step (n : ℕ) (x : Stg n) (h : n ≤ n + 1) : liftStg h x = stgEmb n x := by
  rw [liftStg_succ (le_refl n) x h, liftStg_self]

theorem incl_stgEmb (n : ℕ) (x : Stg n) : incl (n + 1) (stgEmb n x) = incl n x := by
  rw [← liftStg_one_step n x (Nat.le_succ n), incl_lift]

/-- The decomposition at a successor stage: a class of pairs over `Stg n` becomes
a class of pairs over `A∞`. -/
def expandSucc (n : ℕ) (x : Step (Stg n)) : Step Ainf :=
  Quotient.liftOn' x (fun m => mk (mpairMap (inclEmb n) m))
    (fun _ _ h => le_antisymm (mk_le_mk.mpr ((mpairMap_le_mpairMap_iff _).mpr h.1))
      (mk_le_mk.mpr ((mpairMap_le_mpairMap_iff _).mpr h.2)))

/-- The decomposition at an arbitrary stage; stage 0 is `⊥`. -/
def expandStg : (n : ℕ) → Stg n → Step Ainf
  | 0, _ => ⊥
  | n + 1, x => expandSucc n x

@[simp] theorem expandStg_zero (x : Stg 0) : expandStg 0 x = ⊥ := rfl

@[simp] theorem expandStg_mk (n : ℕ) (m : MPair (Stg n)) :
    expandStg (n + 1) (mk m) = mk (mpairMap (inclEmb n) m) := rfl

/-- **The decomposition is stable along the chain.** At stage 0 both sides are
`⊥`; at a successor it is exactly `M`'s functoriality applied to
`incl (n+1) ∘ stgEmb n = incl n`. -/
theorem expandStg_stgEmb : ∀ (n : ℕ) (x : Stg n), expandStg (n + 1) (stgEmb n x) = expandStg n x
  | 0, x => by
    have h1 : stgEmb 0 x = (⊥ : Stg 1) := rfl
    rw [h1, expandStg_zero]
    show mk (mpairMap (inclEmb 0) (⊥ : MPair (Stg 0))) = (⊥ : Step Ainf)
    rw [BifiniteUniversal.bot_eq_eta_bot, mpairMap_eta]
    show mk (eta (incl 0 (⊥ : Stg 0))) = mk (⊥ : MPair Ainf)
    rw [incl_bot, BifiniteUniversal.bot_eq_eta_bot]
  | n + 1, x => by
    obtain ⟨m, rfl⟩ := mk_surjective (α := Stg n) x
    have h1 : mpairMap (inclEmb (n + 1)) (mpairMap (stgEmb n) m)
        = mpairMap ((stgEmb n).trans (inclEmb (n + 1))) m := mpairMap_trans _ _ m
    have h2 : mpairMap ((stgEmb n).trans (inclEmb (n + 1))) m = mpairMap (inclEmb n) m :=
      mpairMap_congr (fun y => incl_stgEmb n y) m
    exact congrArg mk (h1.trans h2)

theorem expandStg_lift {n m : ℕ} (h : n ≤ m) (x : Stg n) :
    expandStg m (liftStg h x) = expandStg n x := by
  induction m, h using Nat.le_induction with
  | base => rw [liftStg_self]
  | succ m hm ih => rw [liftStg_succ hm x, expandStg_stgEmb, ih]

/-- **The decomposition reflects the order within a stage.** At stage 0 both
sides are trivially true; at a successor it is `mpairMap_le_mpairMap_iff` for
`incl n`, which is an order embedding. -/
theorem expandStg_le_iff_same :
    ∀ (N : ℕ) (x y : Stg N), expandStg N x ≤ expandStg N y ↔ x ≤ y
  | 0, x, y => iff_of_true le_rfl (le_of_eq (Subsingleton.elim x y))
  | N + 1, x, y => by
    obtain ⟨mx, rfl⟩ := mk_surjective (α := Stg N) x
    obtain ⟨my, rfl⟩ := mk_surjective (α := Stg N) y
    exact mpairMap_le_mpairMap_iff (inclEmb N)

theorem expandStg_le_iff {n m N : ℕ} (x : Stg n) (y : Stg m) (hn : n ≤ N) (hm : m ≤ N) :
    expandStg n x ≤ expandStg m y ↔ liftStg hn x ≤ liftStg hm y := by
  rw [← expandStg_lift hn x, ← expandStg_lift hm y, expandStg_le_iff_same]

/-- **`A∞ → M(A∞)/≈`**, the decomposition of a point of the colimit into a pair
over the colimit. Well defined on the antisymmetrization because
`expandStg_le_iff` makes it order-reflecting and `Step A∞` is a partial order. -/
def expand (q : Ainf) : Step Ainf :=
  Quotient.liftOn' q (fun p : Germ => expandStg p.1 p.2)
    (fun p r h => le_antisymm
      ((expandStg_le_iff p.2 r.2 (le_max_left p.1 r.1) (le_max_right p.1 r.1)).mpr
        ((germLE_at (le_max_left p.1 r.1) (le_max_right p.1 r.1)).mp h.1))
      ((expandStg_le_iff r.2 p.2 (le_max_right p.1 r.1) (le_max_left p.1 r.1)).mpr
        ((germLE_at (le_max_right p.1 r.1) (le_max_left p.1 r.1)).mp h.2)))

@[simp] theorem expand_incl (n : ℕ) (x : Stg n) : expand (incl n x) = expandStg n x := rfl

theorem expand_le_iff (a b : Ainf) : expand a ≤ expand b ↔ a ≤ b := by
  obtain ⟨n, x, rfl⟩ := incl_surjective a
  obtain ⟨m, y, rfl⟩ := incl_surjective b
  rw [expand_incl, expand_incl, expandStg_le_iff x y (le_max_left n m) (le_max_right n m),
    ← incl_le_incl_iff x y (le_max_left n m) (le_max_right n m)]

/-- **`expand` is surjective — `M` is finitary.** A pair over the colimit mentions
only its base and its finite cover, so `exists_stage_of_finite` puts all of them
in one stage `N`; `range_mpairMap` then exhibits the pair as `M(incl N)` of a pair
over `Stg N`, which is a point of `Stg (N+1)`. -/
theorem expand_surjective : Function.Surjective expand := by
  intro q
  obtain ⟨m, rfl⟩ := mk_surjective (α := Ainf) q
  have hfin : (insert m.base (↑m.cover : Set Ainf)).Finite :=
    (m.cover.finite_toSet).insert _
  obtain ⟨N, hN⟩ := exists_stage_of_finite hfin
  have hmem : m ∈ MSub (Set.range (inclEmb N)) :=
    ⟨hN (Set.mem_insert _ _), fun y hy => hN (Set.mem_insert_of_mem _ hy)⟩
  rw [← range_mpairMap] at hmem
  obtain ⟨m', hm'⟩ := hmem
  exact ⟨incl (N + 1) (mk m'), by rw [expand_incl, expandStg_mk, hm']⟩

end FixedPoint

/-! ## `V ≅ V⁺` -/

section Plus

/-- `A∞ → K(V)`, `a ↦ ↓a`. It is the identification of `A∞` with `V`'s basis that
Theorem 11's second conclusion supplies. -/
def toCompacts (a : Ainf) : ↥(compacts V) :=
  ⟨IdealCompletion.principal a, by
    rw [IdealCompletion.compacts_eq_range_principal]; exact ⟨a, rfl⟩⟩

theorem toCompacts_le_iff (a b : Ainf) : toCompacts a ≤ toCompacts b ↔ a ≤ b :=
  principal_le_principal_iff

theorem toCompacts_surjective : Function.Surjective toCompacts := by
  rintro ⟨k, hk⟩
  rw [IdealCompletion.compacts_eq_range_principal] at hk
  obtain ⟨a, rfl⟩ := hk
  exact ⟨a, rfl⟩

def toCompactsEmb : Ainf ↪o ↥(compacts V) :=
  OrderEmbedding.ofMapLEIff toCompacts toCompacts_le_iff

@[simp] theorem toCompactsEmb_apply (a : Ainf) : toCompactsEmb a = toCompacts a := rfl

/-- **`V ≅ V⁺`**, §7.4's fixed point, as a composite of three applications of
`idealCongr`:

| # | step | the surjection |
| - | ---- | -------------- |
| 1 | `V = ideals over A∞ ≅ ideals over M(A∞)/≈` | `expand` |
| 2 | `≅ ideals over M(A∞)` | `mk`, backwards |
| 3 | `≅ ideals over M(K(V)) = V⁺` | `M(toCompacts)` |

Step 1 is the fixed-point content; steps 2 and 3 are bookkeeping. Together with
`isBifinite_V` this is the hypothesis `D ≅ D⁺` of Theorem 29's second
sentence, met by a `D` that this file constructs. -/
noncomputable def isoPlus : V ≃o Plus V :=
  (idealCongr expand_le_iff expand_surjective).trans
    ((idealCongr (fun _ _ => mk_le_mk) (mk_surjective (α := Ainf))).symm.trans
      (idealCongr (fun _ _ => mpairMap_le_mpairMap_iff toCompactsEmb)
        (surjective_mpairMap toCompacts_surjective)))

/-- Consistency check against Theorem 29's **first** sentence: `V⁺` is bifinite
because `V` is, and `isoPlus` says `V` is order-isomorphic to it. -/
theorem isBifinite_plus_V : IsBifinite (Plus V) := thm29 V isBifinite_V

/-- **`V ≅ V⁺` as cpos, not merely as posets.** An `OrderIso` between cpos
preserves directed suprema (`OrderIso.map_sSup_of_directedOn`), so no separate
continuity argument is needed. -/
theorem iso_plus_V :
    ∃ e : V ≃o Plus V, ∀ s : Set V, DirectedOn (· ≤ ·) s → e (sSup s) = sSup (e '' s) :=
  ⟨isoPlus, fun _ hs => isoPlus.map_sSup_of_directedOn hs⟩

end Plus

/-! ## The construction is nondegenerate

`V ≅ V⁺` would hold vacuously of a one-point domain, so the two-element check
below is not decoration. §7.4's own `b = (⊥, ∅)` is the witness, at the paper's
own second stage. -/

/-- **Stage 1 has exactly §7.4's two elements**, `a = ⊥ = (⊥, {⊥})` and
`b = (⊥, ∅)`. With `pointB1_ne_bot` this is the paper's count 2 of the sequence
1, 2, 5, 20, checked by the kernel. The later two counts are measured by
`scripts/mpair-stages.py`, which enumerates `Mⁿ(I)` modulo the same
identification `Step` performs and reports 1, 2, 5, 20 for the order `MPair.le`
formalizes against 1, 2, 5, 21 for the rival Smyth reading. -/
theorem stg_one_eq (x : Stg 1) : x = ⊥ ∨ x = pointB1 := by
  obtain ⟨m, rfl⟩ := mk_surjective (α := Stg 0) x
  rcases Finset.eq_empty_or_nonempty m.cover with h | ⟨z, hz⟩
  · exact Or.inr (congrArg mk (MPair.ext (Subsingleton.elim _ _) h))
  · left
    have hm : m = (⊥ : MPair (Stg 0)) := by
      refine MPair.ext (Subsingleton.elim _ _) ?_
      rw [BifiniteUniversal.bot_eq_eta_bot, eta_cover]
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, fun w _ => Subsingleton.elim _ _⟩
      exact (Subsingleton.elim z (⊥ : Stg 0)) ▸ hz
    rw [hm]
    rfl

/-- `A∞` has at least the two points §7.4's second stage has: `⊥` and `b`. -/
theorem incl_pointB1_ne_bot : incl 1 pointB1 ≠ (⊥ : Ainf) := by
  intro h
  rw [← incl_bot 1] at h
  exact pointB1_ne_bot (incl_injective 1 h)

/-- `V` has at least two points, since `principal` is injective on `A∞`. -/
theorem principal_pointB1_ne_bot :
    (IdealCompletion.principal (incl 1 pointB1) : V) ≠ (⊥ : V) := by
  intro h
  refine incl_pointB1_ne_bot (le_antisymm ?_ bot_le)
  have := h.le
  rw [IdealCompletion.bot_eq_principal] at this
  exact principal_le_principal_iff.mp this

/-! ## What `V` now makes statable

Neither statement below was type-correct before `V` existed, and neither is
proved here. They are recorded as `Prop`-valued definitions so that the exact
proposition is fixed and can be cited, rather than paraphrased.

**Theorem 29's second sentence.** `Thm29Second` is the paper's "if `D ≅ D⁺` and
`E` is any bifinite domain, then there is a projection `p : D → E`", instantiated
at the `D = V` this file constructs — `iso_plus_V` discharges the hypothesis
`D ≅ D⁺` and `isBifinite_V` the standing assumption on `D`. What is missing is
the universality argument itself, which §7.4 states and defers in full to
[Gun87]: given a bifinite `E`, build an embedding–projection pair `E ⇄ V` by
matching `E`'s Plotkin order against the chain `Stg n`. The pieces this file
supplies for it are `isNormalIn_range_incl` (each stage is normal in `A∞`) and
`exists_stage_of_finite` (a finite set of `A∞` lies in one stage); what is not
supplied is the step-by-step extension of a normal embedding `N ◁ K(E)` into
`Stg n` to one of the next finite normal subposet into `Stg (n+1)`, which is
where `M`'s universal property among finite Plotkin orders is used.

**Lemma 30.** The paper lists ten operators, not nine: Lemma 28's nine plus the
convex powerdomain `()♮`, which is the whole reason §7.4 exists ("The convex
powerdomain `()♮` cannot be representable over `U` because it does not preserve
bounded completeness"). Of the ten, only `→` is available in this development as
a function `Cpo → Cpo` — `CombinatorRep.lean` records that `()♯` and `()♭` are
not, and `⊗, +, ⊕, ()⊥, ()♮` are likewise absent — so `Lem30Arrow` is the only
conjunct that can be written down today. -/

/-- **Theorem 29's second sentence**, at the `D = V` built above. Unproved. -/
def Thm29Second : Prop :=
  ∀ (E : Type) [CompletePartialOrder E], IsBifinite E →
    ∃ (g : ScottHom E V) (p : ScottHom V E), ScottHom.IsEmbeddingProjectionPair g p

/-- **Lemma 30's `→` conjunct**, the first conjunct of the lemma to become
type-correct. Unproved. -/
def Lem30Arrow : Prop := IsPRepresentable₂ V Cpo.funSpace

end ScottDomains.Colimit
