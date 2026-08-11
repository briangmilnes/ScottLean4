import ScottDomains.A5Thm29Finite

/-!
# `Theorem29Normal` beyond a finite basis: the maximal points of `A∞`

`Lemma30.Theorem29Normal` asks, for every bifinite domain `E`, for an
order-reflecting map `K(E) → A∞` whose range is normal in `A∞`.
`R49.Agent5.theorem_29_normal_finiteBasis` settles it when `K(E)` is finite. This
file is about the infinite case, and it reports three measurements: what of the
infinite case was already built, which of the two named sufficient conditions
survive (neither), and one infinite class of bases for which the conclusion is
now proved outright.

## 1. The tower and the limit are already built; the step is the whole gap

The plan for this round asked for three things — a tower of finite normal
subposets exhausting `K(E)`, a coherent extension along it, and a limit whose
range is normal. **Two of the three are already in the development**, in
`A2Thm29Universal.lean`, and nothing here rebuilds them:

| # | step | declaration | status |
| - | ---- | ----------- | ------ |
| 1 | the tower `N₀ ⊆ N₁ ⊆ ⋯` of finite normal subposets of a countable Plotkin order, with `⋃ Nᵢ = K(E)` | `R46.Agent2.cover`, `cover_mono`, `cover_isNormalIn_succ`, `exists_mem_cover`, `bot_mem_cover` | proved |
| 2 | the coherent extension `fᵢ ↦ fᵢ₊₁` | `R46.Agent2.exists_extend`, from `HasFiniteExtensions Ainf` | **the gap** |
| 3 | the limit: the `fᵢ` cohere, the union map order-reflects pointwise, and its range — a `◁`-directed union of normal sets — is normal | `R46.Agent2.limitMap`, `stage_stable`, `stageImage_subset`, `isNormalIn_sUnion`, assembled in `theorem_29_normal_of_hasFiniteExtensions` | proved |

Row 3 already contains the lemma the plan asked to isolate: normality of a
directed union of normal subsets is `NormalSubposet.isNormalIn_sUnion`, proved in
r0037 and used at `A2Thm29Universal.lean:762`. The tower's `◁`-directedness is
supplied by `stageImage_subset`. So the whole of `Theorem29Normal`'s residue is
row 2, and row 2 is a property of `A∞` alone.

## 2. Both named sufficient conditions are equivalent, and both are false

`R46.Agent2` states two properties of a poset and proves
`HasNormalRealizations α → HasFiniteExtensions α` (Gunter's Proposition 21) and
`HasFiniteExtensions Ainf → Theorem29Normal` (his Theorem 25).
`R47.Agent1.not_hasNormalRealizations_Ainf` refutes the first at `A∞`. That left
`HasFiniteExtensions Ainf` — the hypothesis actually consumed by the reduction —
formally open, and it is the property row 2 needs.

`hasNormalRealizations_of_hasFiniteExtensions` below closes that: the two
properties are **equivalent** (`hasFiniteExtensions_iff_hasNormalRealizations`),
because a normal type over `A` presented by `(β, T, g, z)` is a finite normal
extension `insert z (g '' A)` of `g '' A` inside `T`, and the map back that the
finite-extension property returns evaluates at `z` to a realization. Hence
`not_hasFiniteExtensions_Ainf`. **No route through either property remains**, and
a future round should not attempt one.

## 3. The obstruction is not one accident at stage 1

`R47.Agent1` refutes `HasNormalRealizations A∞` with a single point,
`β = incl 1 pointB1`: it is maximal in `A∞`, so the normal type of a point
strictly above it — realized in the three-element chain — cannot be realized.
Read narrowly that says one stage of the tower misbehaves, which invites the
repair "start the construction at a later stage".

That repair does not exist. `mkEmpty x = mk ⟨x, ∅⟩` is maximal in `Step α` for
**every** `x` (`mkEmpty_maximal`, generalizing `R47.Agent1.topElt_maximal` from
`x = ⊥`), and the tower's connecting map carries an empty cover to an empty cover
(`stgEmb_mkEmpty`, `liftStg_mkEmpty`), so `incl (n+1) (mkEmpty x)` is maximal in
the colimit for every `n` and every `x : Stg n` (`incl_mkEmpty_maximal`).
Iterating that from `⊥` gives `maxPt : ℕ → Ainf`, an injective sequence of
maximal points (`maxPt_injective`), so the maximal points of `A∞` other than `⊥`
are **infinite** (`infinite_maximal_Ainf`). Each one on its own refutes
`HasNormalRealizations A∞`.

## 4. The same fact discharges the first infinite case of `Theorem29Normal`

Infinitely many maximal points is an obstruction to the *extension* route and, at
the same time, exactly the room needed for one infinite class of bases. Distinct
maximal points have no common upper bound, so `{⊥} ∪ M` is normal in `A∞`
whenever every member of `M` is maximal (`isNormalIn_of_bot_or_maximal`) — no
directedness ever has to be checked, because two maximal points below a common
`x` are equal.

A **flat** basis — one in which `a ⊑ b` forces `a = ⊥` or `a = b` — is exactly a
`⊥` with an antichain over it, so `theorem_29_normal_flatBasis` sends `⊥ ↦ ⊥` and
the rest injectively into `maxPt`. That is `Theorem29Normal`'s conclusion for
every bifinite domain whose basis is flat — the countable flat domains — and it
is the first case with an **infinite** basis discharged in this development.
`exists_normal_antichain_Ainf` records the closed instance.

As with `theorem_29_normal_finiteBasis`, this is a *discharged-at*, not a
discharge: `theorem_29_normal_flatBasis_of_thm29Normal` checks that the added
hypothesis only weakens. `IsBifinite E` is carried to line the statement up with
`Theorem29Normal` and is not used.

## 5. What remains, stated exactly

`Theorem29Normal` is open for a basis that is neither finite nor flat. The
smallest open instance is a basis with an infinite ascending chain: for
`K(E) = ω` the normality half is free (a chain containing `⊥` meets every
principal ideal in a chain, which is directed), so the residue there is the
purely order-theoretic question

> does `A∞` contain a strictly increasing sequence `⊥ = c₀ ⊏ c₁ ⊏ c₂ ⊏ ⋯`?

Nothing in this development answers it. `A∞` has chains of every finite length —
`incl n` is an order embedding and the stages' heights grow — but the tower's
connecting map is `M(f)`, not `η` (`Colimit.stgEmb_ne_mk_eta`), and `M(f)` maps
an empty cover to an empty cover, so the top of a chain lifted along the tower is
maximal from the next stage on. Whether some other family of chains coheres
through the tower is the question a next round should settle; a negative answer
would **refute** `Theorem29Normal` at this `A∞`, since an order-reflecting map
of an `ω`-chain basis into `A∞` is exactly such a sequence.
-/

namespace ScottDomains.R53.Agent3

open ScottDomains ScottDomains.BifiniteUniversal ScottDomains.Colimit

/-! ## Normality is free above `⊥` and the maximal points

Normality of `N` in a poset asks that `N ∩ ↓x` be nonempty and directed for every
`x`. If every member of `N` is `⊥` or maximal, both are automatic: `⊥` supplies
nonemptiness, and two maximal points below the same `x` are both equal to `x`. -/

section BotAndMaximal

variable {α : Type*} [PartialOrder α] [OrderBot α]

/-- **A set of `⊥` and maximal points is normal.** No hypothesis on the poset
beyond a least element, and no directedness is ever checked: a maximal `a ⊑ x`
forces `x = a`, so `N ∩ ↓x` has at most the two members `⊥` and `x`. -/
theorem isNormalIn_of_bot_or_maximal {N : Set α} (hbot : (⊥ : α) ∈ N)
    (hmax : ∀ a ∈ N, a = ⊥ ∨ ∀ w : α, a ≤ w → w = a) :
    N ◁ (Set.univ : Set α) := by
  refine ⟨Set.subset_univ _, fun x _ => ⟨⟨⊥, hbot, Set.mem_Iic.mpr bot_le⟩, ?_⟩⟩
  rintro c ⟨hc, hcx⟩ d ⟨hd, hdx⟩
  rcases hmax c hc with rfl | hcmax
  · exact ⟨d, ⟨hd, hdx⟩, bot_le, le_rfl⟩
  · rcases hmax d hd with rfl | hdmax
    · exact ⟨c, ⟨hc, hcx⟩, le_rfl, bot_le⟩
    · have hxc : x = c := hcmax x (Set.mem_Iic.mp hcx)
      have hxd : x = d := hdmax x (Set.mem_Iic.mp hdx)
      exact ⟨c, ⟨hc, hcx⟩, le_rfl, le_of_eq (hxd.symm.trans hxc)⟩

/-- `{⊥, a}` is normal whenever `a` is maximal. This discharges the second
hypothesis of `R47.Agent1.not_hasNormalRealizations_of_maximal` from the third,
so a non-`⊥` maximal point alone refutes the realization property. -/
theorem pair_bot_isNormalIn_of_maximal {a : α} (hmax : ∀ w : α, a ≤ w → w = a) :
    ({⊥, a} : Set α) ◁ (Set.univ : Set α) :=
  isNormalIn_of_bot_or_maximal (Set.mem_insert _ _)
    (by
      rintro c (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr hmax)

end BotAndMaximal

/-! ## The two named sufficient conditions are the same condition -/

section Equivalence

variable {α : Type} [PartialOrder α]

/-- **The finite-extension property implies the realization property.** The
converse is `R46.Agent2.hasFiniteExtensions_of_hasNormalRealizations` (Gunter's
Proposition 21); this direction is the cheap one and had not been recorded.

A normal type over `A`, presented by a poset `β`, a finite `T ⊆ β`, an embedding
`g` of `A` and a point `z` with `insert z (g '' A) ◁ T`, is already a finite
normal extension of `g '' A`: take `T' := insert z (g '' A)`, which is finite,
nonempty and satisfies `g '' A ◁ T'` by Lemma 4.2
(`IsNormalIn.mono_right`). `HasFiniteExtensions` returns a map `h : β → α` that
inverts `g` on `A` and order-reflects on `T'`, and `h z` is then a realization:
`a ⊑ h z ↔ g a ⊑ z` is order reflection at the pair `(g a, z)` after rewriting
`h (g a) = a`. Its image `h '' T' = insert (h z) A` is normal by the same call. -/
theorem hasNormalRealizations_of_hasFiniteExtensions
    (H : R46.Agent2.HasFiniteExtensions α) : R46.Agent2.HasNormalRealizations α := by
  intro A hAfin hAnorm β _ T hTfin g z hg hgA hzA
  have hgA' : g '' A ◁ insert z (g '' A) :=
    IsNormalIn.mono_right (Set.subset_insert _ _) hzA.subset hgA
  obtain ⟨h, hrefl, hagree, hn⟩ :=
    H A hAfin hAnorm β (insert z (g '' A)) ((hAfin.image g).insert z)
      ⟨z, Set.mem_insert _ _⟩ g hg hgA'
  have hzmem : z ∈ insert z (g '' A) := Set.mem_insert _ _
  refine ⟨h z, ?_, ?_⟩
  · intro a ha
    have hgmem : g a ∈ insert z (g '' A) := Set.mem_insert_of_mem _ ⟨a, ha, rfl⟩
    have h₁ : h (g a) ≤ h z ↔ g a ≤ z := hrefl (g a) hgmem z hzmem
    have h₂ : h z ≤ h (g a) ↔ z ≤ g a := hrefl z hzmem (g a) hgmem
    rw [hagree a ha] at h₁ h₂
    exact ⟨h₁, h₂⟩
  · have himg : h '' insert z (g '' A) = insert (h z) A := by
      rw [Set.image_insert_eq]
      refine congrArg (insert (h z)) (Set.Subset.antisymm ?_ ?_)
      · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
        rw [hagree a ha]
        exact ha
      · exact fun a ha => ⟨g a, ⟨a, ha, rfl⟩, hagree a ha⟩
    rwa [himg] at hn

/-- **Gunter's two hypotheses are one hypothesis.** Proposition 21 turns
one-point realization into finite extension; the display above turns finite
extension back into one-point realization. -/
theorem hasFiniteExtensions_iff_hasNormalRealizations :
    R46.Agent2.HasFiniteExtensions α ↔ R46.Agent2.HasNormalRealizations α :=
  ⟨hasNormalRealizations_of_hasFiniteExtensions,
    R46.Agent2.hasFiniteExtensions_of_hasNormalRealizations⟩

end Equivalence

/-- **The route through `HasFiniteExtensions A∞` is closed.**
`R46.Agent2.theorem_29_normal_of_hasFiniteExtensions` is the reduction the tower
argument actually consumes, and its hypothesis is false: by the equivalence above
it would give `HasNormalRealizations A∞`, refuted in
`R47.Agent1.not_hasNormalRealizations_Ainf`.

Until now only the *stronger* property was known to fail, which left open the
reading that the weaker one might still be provable. It cannot. -/
theorem not_hasFiniteExtensions_Ainf : ¬ R46.Agent2.HasFiniteExtensions Ainf :=
  fun H =>
    R47.Agent1.not_hasNormalRealizations_Ainf (hasNormalRealizations_of_hasFiniteExtensions H)

/-! ## The maximal points of `A∞`

`R47.Agent1` exhibits one maximal point of `A∞`, §7.4's `b = (⊥, ∅)`. The empty
cover is what makes it maximal, and nothing in that argument mentions `⊥`: the
pair `(x, ∅)` is maximal over any base `x`. -/

section MaximalPoints

/-- `(x, ∅)`, the pair with base `x` and empty cover, as a point of the next
stage. `mkEmpty ⊥` is `R47.Agent1.topElt`. -/
def mkEmpty {α : Type u} [PartialOrder α] (x : α) : Step α :=
  mk ⟨x, ∅, by simp⟩

theorem mkEmpty_bot_eq_topElt (k : ℕ) : mkEmpty (⊥ : Stg k) = R47.Agent1.topElt k := rfl

/-- **`(x, ∅)` is maximal in `M(A)`, for every base `x`.** `⟨x, ∅⟩ ⊑ n` cannot
hold by the printed relation — that would need a member of the empty cover — so
it holds by §7.4's identification, which forces `n` to have base `x` and empty
up-set, hence to be the same point. This is `R47.Agent1.topElt_maximal` with the
base freed from `⊥`. -/
theorem mkEmpty_maximal {α : Type u} [PartialOrder α] {x : α} {y : Step α}
    (h : mkEmpty x ≤ y) : y = mkEmpty x := by
  obtain ⟨n, rfl⟩ := mk_surjective y
  rcases h with ⟨w, hw, -⟩ | ⟨hb, hu⟩
  · exact absurd hw (Finset.notMem_empty w)
  · exact le_antisymm (mk_le_mk.mpr (Or.inr ⟨hb.symm, hu.symm⟩))
      (mk_le_mk.mpr (Or.inr ⟨hb, hu⟩))

/-- Distinct bases give distinct empty-cover points: the printed relation is
unavailable, so `⟨x, ∅⟩ ⊑ ⟨y, ∅⟩` can only be the identification, which equates
the bases. -/
theorem mkEmpty_injective {α : Type u} [PartialOrder α] :
    Function.Injective (mkEmpty : α → Step α) := by
  intro x y hxy
  rcases le_of_eq hxy with ⟨z, hz, -⟩ | ⟨hb, -⟩
  · exact absurd hz (Finset.notMem_empty z)
  · exact hb

/-- An empty-cover point is never the least element: `⊥ = (⊥, {⊥})` generates a
nonempty up-set and `(x, ∅)` generates the empty one. -/
theorem mkEmpty_ne_bot {α : Type u} [PartialOrder α] [OrderBot α] (x : α) :
    mkEmpty x ≠ (⊥ : Step α) := by
  intro hEq
  rcases le_of_eq hEq with ⟨z, hz, -⟩ | ⟨-, hu⟩
  · exact absurd hz (Finset.notMem_empty z)
  · obtain ⟨z, hz, -⟩ :=
      (Set.ext_iff.mp hu (⊥ : α)).mpr (mem_upper_eta.mpr (le_refl (⊥ : α)))
    exact absurd hz (Finset.notMem_empty z)

/-- **The tower carries an empty cover to an empty cover.** `M(f)` maps the cover
by `f`, and the image of `∅` is `∅`; the base moves to `stgEmb n x`. This is
`R47.Agent1.stgEmb_topElt` with the base freed from `⊥` — and it is why
maximality, destroyed at once by `eta` (`R47.Agent1.exists_gt_mk_eta_pointB1`),
survives every stage of *this* tower. -/
theorem stgEmb_mkEmpty (k : ℕ) (x : Stg k) :
    stgEmb (k + 1) (mkEmpty x) = mkEmpty (stgEmb k x) :=
  congrArg mk (MPair.ext rfl (Finset.map_empty _))

/-- The same, along an arbitrary hop of the tower. -/
theorem liftStg_mkEmpty : ∀ {n m : ℕ} (h : n ≤ m) (x : Stg n) (h' : n + 1 ≤ m + 1),
    liftStg h' (mkEmpty x) = mkEmpty (liftStg h x) := by
  intro n m h
  induction m, h using Nat.le_induction with
  | base =>
    intro x h'
    rw [Subsingleton.elim h' (le_refl (n + 1)), liftStg_self, liftStg_self]
    rfl
  | succ m hm ih =>
    intro x h'
    have hm1 : n + 1 ≤ m + 1 := Nat.add_le_add_right hm 1
    have e1 : liftStg h' (mkEmpty x) = stgEmb (m + 1) (liftStg hm1 (mkEmpty x)) :=
      liftStg_succ hm1 (mkEmpty x) h'
    have e2 : liftStg hm1 (mkEmpty x) = mkEmpty (liftStg hm x) := ih x hm1
    have e3 : stgEmb (m + 1) (mkEmpty (liftStg hm x)) = mkEmpty (stgEmb m (liftStg hm x)) :=
      stgEmb_mkEmpty m (liftStg hm x)
    have e4 : liftStg (hm.trans (Nat.le_add_right m 1)) x = stgEmb m (liftStg hm x) :=
      liftStg_succ hm x (hm.trans (Nat.le_add_right m 1))
    have e5 : stgEmb (m + 1) (liftStg hm1 (mkEmpty x))
        = stgEmb (m + 1) (mkEmpty (liftStg hm x)) :=
      congrArg (fun y : Stg (m + 1) => (stgEmb (m + 1) y : Stg (m + 2))) e2
    exact e1.trans (e5.trans (e3.trans (congrArg mkEmpty e4.symm)))

/-- **`(x, ∅)` is maximal in the colimit.** Any `w` above it lives in some stage;
compare at a stage above both, where `liftStg_mkEmpty` presents the lifted point
again as an empty-cover pair and `mkEmpty_maximal` identifies the two. -/
theorem incl_mkEmpty_maximal {n : ℕ} (x : Stg n) {w : Ainf}
    (h : incl (n + 1) (mkEmpty x) ≤ w) : w = incl (n + 1) (mkEmpty x) := by
  obtain ⟨m, y, rfl⟩ := incl_surjective w
  have hnm : n ≤ max n m := le_max_left n m
  have h1 : n + 1 ≤ max n m + 1 := Nat.succ_le_succ hnm
  have hm : m ≤ max n m + 1 := (le_max_right n m).trans (Nat.le_succ _)
  rw [incl_le_incl_iff _ _ h1 hm, liftStg_mkEmpty hnm x h1] at h
  rw [← incl_lift hm y, mkEmpty_maximal h, ← liftStg_mkEmpty hnm x h1, incl_lift h1]

end MaximalPoints

/-! ## Infinitely many maximal points

Iterating `mkEmpty` from `⊥ : Stg 0` gives one point at every stage. Along the
tower the iterate is *not* the lift of its predecessor — the lift of
`mkEmpty x` is `mkEmpty (stgEmb x)`, not `mkEmpty (mkEmpty x)` — and that
mismatch is exactly what makes the images in `A∞` pairwise distinct. -/

section Antichain

/-- The iterate: `bpt 0 = ⊥` and `bpt (n+1) = (bpt n, ∅)`. -/
def bpt : (n : ℕ) → Stg n
  | 0 => (⊥ : Stg 0)
  | n + 1 => mkEmpty (bpt n)

theorem bpt_zero : bpt 0 = (⊥ : Stg 0) := rfl

theorem bpt_succ (n : ℕ) : bpt (n + 1) = mkEmpty (bpt n) := rfl

/-- The `n`-th maximal point of `A∞`. -/
def maxPt (n : ℕ) : Ainf := incl (n + 1) (bpt (n + 1))

theorem maxPt_maximal (n : ℕ) {w : Ainf} (h : maxPt n ≤ w) : w = maxPt n :=
  incl_mkEmpty_maximal (bpt n) h

theorem maxPt_ne_bot (n : ℕ) : maxPt n ≠ (⊥ : Ainf) := by
  intro h
  exact mkEmpty_ne_bot (bpt n) (incl_injective (n + 1) (h.trans (incl_bot (n + 1)).symm))

/-- **The iterate is never the lift of an earlier iterate.** Induction on the
smaller index: at the base, the lift of `⊥` is `⊥` and `bpt (m+1)` is an
empty-cover point; at the step, `liftStg_mkEmpty` peels one `mkEmpty` off each
side and `mkEmpty_injective` cancels it. -/
theorem liftStg_bpt_ne : ∀ (n m : ℕ) (h : n ≤ m), n < m → liftStg h (bpt n) ≠ bpt m := by
  intro n
  induction n with
  | zero =>
    intro m h hlt
    cases m with
    | zero => exact absurd hlt (lt_irrefl 0)
    | succ m' =>
      rw [bpt_zero, liftStg_bot, bpt_succ]
      exact fun hEq => mkEmpty_ne_bot (bpt m') hEq.symm
  | succ n ih =>
    intro m h hlt
    cases m with
    | zero => exact absurd hlt (Nat.not_lt_zero _)
    | succ m' =>
      have h' : n ≤ m' := Nat.le_of_succ_le_succ h
      have hlt' : n < m' := Nat.lt_of_succ_lt_succ hlt
      intro hEq
      have e1 : liftStg h (bpt (n + 1)) = mkEmpty (liftStg h' (bpt n)) :=
        liftStg_mkEmpty h' (bpt n) h
      have e2 : mkEmpty (liftStg h' (bpt n)) = mkEmpty (bpt m') := e1.symm.trans hEq
      exact ih m' h' hlt' (mkEmpty_injective e2)

theorem maxPt_injective : Function.Injective maxPt := by
  have key : ∀ n m : ℕ, n < m → maxPt n ≠ maxPt m := by
    intro n m hlt hEq
    have h : n + 1 ≤ m + 1 := Nat.succ_le_succ hlt.le
    have hstep : incl (m + 1) (liftStg h (bpt (n + 1))) = incl (m + 1) (bpt (m + 1)) := by
      rw [incl_lift h (bpt (n + 1))]
      exact hEq
    exact liftStg_bpt_ne (n + 1) (m + 1) h (Nat.succ_lt_succ hlt)
      (incl_injective (m + 1) hstep)
  intro n m hEq
  rcases lt_trichotomy n m with h | h | h
  · exact absurd hEq (key n m h)
  · exact h
  · exact absurd hEq.symm (key m n h)

theorem maxPt_le_iff (i j : ℕ) : maxPt i ≤ maxPt j ↔ i = j := by
  refine ⟨fun h => (maxPt_injective (maxPt_maximal i h)).symm, fun h => le_of_eq (h ▸ rfl)⟩

/-- **`A∞` has infinitely many maximal points other than `⊥`.**

This is the sharpest form of r0047's obstruction. `R47.Agent1` refutes
`HasNormalRealizations A∞` from a single maximal point at stage 1, which reads as
a defect of one stage; in fact every point of every stage produces one
(`incl_mkEmpty_maximal`), so no repair of the form "start the construction at a
later stage" exists. With `pair_bot_isNormalIn_of_maximal`, each of these points
independently refutes the realization property, and hence — by
`hasFiniteExtensions_iff_hasNormalRealizations` — the finite-extension property
as well. -/
theorem infinite_maximal_Ainf :
    {q : Ainf | q ≠ ⊥ ∧ ∀ w : Ainf, q ≤ w → w = q}.Infinite :=
  Set.infinite_of_injective_forall_mem (f := maxPt) maxPt_injective
    (fun n => ⟨maxPt_ne_bot n, fun _ h => maxPt_maximal n h⟩)

/-- **A closed instance of the conclusion at an infinite basis.** `⊥` together
with the maximal points `maxPt` is a normal copy of the countably infinite flat
poset inside `A∞`: order-reflection is `maxPt_le_iff` and normality is
`isNormalIn_of_bot_or_maximal`, with no directedness check anywhere. -/
theorem exists_normal_antichain_Ainf :
    ∃ g : ℕ → Ainf, Function.Injective g ∧ (∀ i j, g i ≤ g j ↔ i = j) ∧
      insert (⊥ : Ainf) (Set.range g) ◁ (Set.univ : Set Ainf) := by
  refine ⟨maxPt, maxPt_injective, maxPt_le_iff, ?_⟩
  refine isNormalIn_of_bot_or_maximal (Set.mem_insert _ _) ?_
  rintro a (rfl | ⟨n, rfl⟩)
  · exact Or.inl rfl
  · exact Or.inr (fun _ h => maxPt_maximal n h)

end Antichain

/-! ## `Theorem29Normal` at a flat basis -/

section FlatBasis

/-- **`Lemma30.Theorem29Normal` at flat bases.** Word for word `Theorem29Normal`,
with the hypothesis that `K(E)` is flat added — every `a ⊑ b` forces `a = ⊥` or
`a = b`. That is a `⊥` with an antichain over it, and it is the basis of every
flat domain.

The map is `⊥ ↦ ⊥` and, on the rest, an injection into `maxPt` supplied by
`[Domain E]`'s countability of `K(E)`. Order reflection: below `⊥` on both sides
nothing but `⊥` sits, and two distinct maximal points of `A∞` are incomparable
(`maxPt_le_iff`), matching the flat order exactly. Normality is
`isNormalIn_of_bot_or_maximal`.

`IsBifinite E` is carried so the statement lines up with `Theorem29Normal` and is
**not used** — a flat basis is a Plotkin order whatever `E` is. This is a
*discharged-at*, not a discharge, and
`theorem_29_normal_flatBasis_of_thm29Normal` records the direction. It is
nevertheless the first case of `Theorem29Normal` with an **infinite** basis that
this development proves: `R49.Agent5.theorem_29_normal_finiteBasis` needs
`Finite ↥(compacts E)`, and nothing else did. -/
theorem theorem_29_normal_flatBasis :
    ∀ (E : Type) [CompletePartialOrder E] [Domain E],
      (∀ a b : ↥(compacts E), a ≤ b → a = ⊥ ∨ a = b) → IsBifinite E →
      ∃ f : ↥(compacts E) → Ainf,
        (∀ a b, f a ≤ f b ↔ a ≤ b) ∧ Set.range f ◁ (Set.univ : Set Ainf) := by
  classical
  intro E _ _ hflat _
  obtain ⟨enc, henc⟩ := Countable.exists_injective_nat ↥(compacts E)
  refine ⟨fun a => if a = ⊥ then (⊥ : Ainf) else maxPt (enc a), ?_, ?_⟩
  · intro a b
    dsimp only
    by_cases ha : a = ⊥
    · rw [if_pos ha]
      exact iff_of_true bot_le (ha ▸ bot_le)
    · by_cases hb : b = ⊥
      · rw [if_neg ha, if_pos hb]
        refine iff_of_false (fun hle => maxPt_ne_bot (enc a) (le_bot_iff.mp hle)) ?_
        intro hle
        exact ha (le_bot_iff.mp (hb ▸ hle))
      · rw [if_neg ha, if_neg hb]
        constructor
        · intro hle
          exact le_of_eq (henc ((maxPt_le_iff (enc a) (enc b)).mp hle))
        · intro hle
          rcases hflat a b hle with h | h
          · exact absurd h ha
          · exact le_of_eq (congrArg (fun c => maxPt (enc c)) h)
  · refine isNormalIn_of_bot_or_maximal ⟨⊥, by simp⟩ ?_
    rintro y ⟨a, rfl⟩
    dsimp only
    by_cases ha : a = ⊥
    · exact Or.inl (if_pos ha)
    · rw [if_neg ha]
      exact Or.inr (fun _ h => maxPt_maximal (enc a) h)

/-- **The direction of the change, recorded.** `Lemma30.Theorem29Normal` implies
the statement above, so the added flatness hypothesis only ever *weakens*: what
is discharged is a consequence of the open claim, not a different sentence. Same
pattern as `R49.Agent5.theorem_29_normal_finiteBasis_of_thm29Normal`. -/
theorem theorem_29_normal_flatBasis_of_thm29Normal (H : Lemma30.Theorem29Normal) :
    ∀ (E : Type) [CompletePartialOrder E] [Domain E],
      (∀ a b : ↥(compacts E), a ≤ b → a = ⊥ ∨ a = b) → IsBifinite E →
      ∃ f : ↥(compacts E) → Ainf,
        (∀ a b, f a ≤ f b ↔ a ≤ b) ∧ Set.range f ◁ (Set.univ : Set Ainf) :=
  fun E _ _ _ hE => H E hE

end FlatBasis

/-! ## What the `ω`-chain case still needs

For a basis that is a chain, normality costs nothing: `N ∩ ↓x` is a chain, hence
directed, and `⊥ ∈ N` makes it nonempty. The lemma below isolates that, so the
open `ω`-chain instance of `Theorem29Normal` is a pure embedding question about
`A∞` with the normality conjunct already discharged. -/

section ChainBasis

variable {α : Type*} [PartialOrder α] [OrderBot α]

/-- **A chain through `⊥` is normal.** Directedness of `N ∩ ↓x` is comparability,
which the chain supplies; nonemptiness is `⊥`. -/
theorem isNormalIn_of_isChain {N : Set α} (hbot : (⊥ : α) ∈ N)
    (hchain : ∀ a ∈ N, ∀ b ∈ N, a ≤ b ∨ b ≤ a) : N ◁ (Set.univ : Set α) := by
  refine ⟨Set.subset_univ _, fun x _ => ⟨⟨⊥, hbot, Set.mem_Iic.mpr bot_le⟩, ?_⟩⟩
  rintro c ⟨hc, hcx⟩ d ⟨hd, hdx⟩
  rcases hchain c hc d hd with h | h
  · exact ⟨d, ⟨hd, hdx⟩, h, le_rfl⟩
  · exact ⟨c, ⟨hc, hcx⟩, le_rfl, h⟩

/-- **The chain case of `Theorem29Normal` is an embedding question.** If `K(E)`
is linearly ordered, any order-reflecting `f : K(E) → A∞` sending `⊥` to `⊥`
already has normal range, so the conclusion of `Theorem29Normal` holds. Nothing
about bifiniteness or countability is used. -/
theorem theorem_29_normal_of_chainBasis {E : Type} [CompletePartialOrder E]
    (hchain : ∀ a b : ↥(compacts E), a ≤ b ∨ b ≤ a) (f : ↥(compacts E) → Ainf)
    (hf : ∀ a b, f a ≤ f b ↔ a ≤ b) (hbot : f ⊥ = (⊥ : Ainf)) :
    (∀ a b, f a ≤ f b ↔ a ≤ b) ∧ Set.range f ◁ (Set.univ : Set Ainf) := by
  refine ⟨hf, isNormalIn_of_isChain ⟨⊥, hbot⟩ ?_⟩
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rcases hchain a b with h | h
  · exact Or.inl ((hf a b).mpr h)
  · exact Or.inr ((hf b a).mpr h)

end ChainBasis

end ScottDomains.R53.Agent3
