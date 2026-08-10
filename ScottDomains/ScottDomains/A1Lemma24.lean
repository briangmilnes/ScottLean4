import ScottDomains.A2Thm29Universal
-- `SFP.exists_greatest_of_finite`: a nonempty finite directed set contains its
-- own greatest element. That element is Gunter's base `X`; nothing else in the
-- import closure of `A2Thm29Universal` supplies it.
import ScottDomains.SFP

/-!
# Gunter's Lemma 24 at `M(A)`, and what it does *not* give this tower

Two results, one positive and one negative, and the negative one is the round's
main finding.

## 1. Lemma 24 at `A⁺ = M(A)`, proved

Gunter, *Universal Profinite Domains*, Information and Computation **72** (1987)
1–30, p. 20 (`papers/Gunter 1987 Universal Profinite Domains.pdf`):

> **Lemma 24** Let `A` be a finite poset. Then there is a finite poset `A⁺` such
> that `A ◁ A⁺` and, for every substructure `B ◁ A` and normal type `Γ` over `B`,
> there is a `Z ∈ A⁺` such that `Z` realizes `Γ` and `B ∪ {Z} ◁ A⁺`.

and p. 23, the identification of `A⁺` with `M(A)` this development formalizes:

> There is an even more explicit way of describing this operation which was
> remarked to the author by Dana Scott. Given a finite poset `A`, let `A⁺` be the
> set of pairs `⟨X, u⟩` such that `X ∈ A` and `u` is an upwards closed set of
> points from `A` such that `X ⊑ Y` for each `Y ∈ u`. Say that `⟨X, u⟩ ⊑ ⟨Y, v⟩`
> iff `Y ∈ u`. This more order-theoretic way of doing things helps in picturing
> the universal domain as the limit of the posets `A ⊴ A⁺ ⊴ A⁺⁺ ⊴ ⋯`.

**Gunter does not prove Lemma 24 of `M(A)`.** His proof (p. 21) iterates Lemma 23
over an enumeration `Γ₁, …, Γₙ` of the normal types and produces *some* finite
`A⁺`; the explicit pair form is then introduced by the sentence above, as a way
of *picturing* the construction, with no theorem, no proof, and no claim that the
two agree. `gunter87_lemma_24_MPair` below is therefore not a transcription — it is the
first proof that Scott's pair construction satisfies Gunter's Lemma 24.

The proof is short once the two order characterizations are separated:
`eta_le_iff` (`η X ⊑ ⟨x, u⟩ ↔ X ⊑ x`) and `le_eta_iff` (`⟨x, u⟩ ⊑ η X ↔ X ∈ ↑u`).
The realization is `⟨X₀, U⟩` with `X₀` the greatest element of `B ∩ ↓Z` — which
exists because `B ◁ T` makes that set directed, and it is finite — and `U` the
set `B ∩ ↑Z`. Normality of `η''B ∪ {⟨X₀, U⟩}` needs only that the cover lies in
`B`; neither `A` nor `B` need be finite for it, and `T` need not be finite at
all.

## 2. The same lemma does **not** discharge `HasNormalRealizations A∞`

`R46.Agent2.HasNormalRealizations` is Gunter's Theorem 25 hypothesis at `A∞`, and
r0046 proved `HasNormalRealizations A∞ → Lemma30.Theorem29Normal`. That reduction
is sound; its target is **false**.

`not_hasNormalRealizations_Ainf` refutes it, and the mechanism is exactly the
divergence `Colimit.lean` already documents and kernel-checks in
`stgEmb_ne_mk_eta`. §7.4 and Gunter p. 23 both take the connecting map of the
tower to be `η : x ↦ (x, {x})`. `Colimit.lean` cannot: the colimit along `η` is
not a fixed point of `M`, so `stgEmb (n+1)` is `M(stgEmb n)` instead. The two
readings differ on what happens to a pair with an **empty cover**:

| # | element | image under `η` | image under `M(f)` |
| - | ------- | --------------- | ------------------ |
| 1 | `(x, ∅)` | `((x, ∅), {(x, ∅)})` | `(f x, ∅)` |

`(x, ∅)` is maximal in `M(A)` for every `A` — `(x, ∅) ⊑ (y, v)` forces `y = x`
and `↑v = ∅`. Under `η` that maximality is destroyed at the next stage
(`exists_gt_mk_eta_pointB1`); under `M(f)` the empty cover is carried along
unchanged, so maximality **persists forever** (`topElt_maximal`,
`incl_pointB1_maximal`). §7.4's own `b = (⊥, ∅)` is such an element, and its
image `β = incl 1 pointB1` is a maximal point of `A∞` whose down-set is `{⊥, β}`.

Take `A = {⊥, β} = im(incl 1)`, which is normal in `A∞`, and the type of a new
point strictly above `β`. It is normal — `Fin 3` realizes it with
`{0, 1} ◁ {0, 1, 2}` — and `A∞` cannot realize it, because nothing is strictly
above `β`. So `HasNormalRealizations A∞` fails, and with it the hypothesis of
`hasNormalRealizations_of_stages` (`not_stagewise_realizations`).

**What this does and does not settle.** It refutes r0046's *sufficient condition*,
not `Lemma30.Theorem29Normal` itself: nothing here forces a normal embedding
`K(E) → A∞` to have `β` in its range. `Theorem29Normal` stays open, and the route to
it through Theorem 25 is now closed at this tower. What Lemma 24 at `M(A)` buys
is a proof for the `η`-tower, which this development does not build.
-/

namespace ScottDomains.R47.Agent1

open ScottDomains ScottDomains.BifiniteUniversal ScottDomains.Colimit

universe u

/-! ## The two order characterizations against the embedded copy -/

section Characterize

variable {α : Type u} [PartialOrder α]

/-- `η X ⊑ ⟨x, u⟩ ↔ X ⊑ x`. The printed relation gives it directly; the
identification disjunct gives `X = x`, which is stronger. -/
theorem eta_le_iff {x : α} {m : MPair α} : eta x ≤ m ↔ x ≤ m.base := by
  constructor
  · rintro (h | ⟨hb, -⟩)
    · exact mem_upper_eta.mp h
    · exact le_of_eq hb
  · exact fun h => Or.inl (mem_upper_eta.mpr h)

/-- `⟨x, u⟩ ⊑ η X ↔ X ∈ ↑u`. The identification disjunct is absorbed: it makes
`↑u` equal to `↑X`, which contains `X`. -/
theorem le_eta_iff {x : α} {m : MPair α} : m ≤ eta x ↔ x ∈ m.upper := by
  constructor
  · rintro (h | ⟨-, hu⟩)
    · exact h
    · rw [hu]
      exact mem_upper_eta.mpr le_rfl
  · exact fun h => Or.inl h

end Characterize

/-! ## `A ◁ A⁺`, and the normality of a one-point extension -/

section Normality

variable {α : Type u} [PartialOrder α]

/-- **The embedded copy of a normal subposet is normal in `M(A)`.** `η` is an
order embedding and `η''B ∩ ↓⟨y, v⟩ = η''(B ∩ ↓y)` by `eta_le_iff`, so
directedness transports unchanged. At `B = A` this is Gunter's `A ◁ A⁺`. -/
theorem isNormalIn_eta_image {B : Set α} (hB : B ◁ (Set.univ : Set α)) :
    eta '' B ◁ (Set.univ : Set (MPair α)) := by
  refine ⟨Set.subset_univ _, fun n _ => ⟨?_, ?_⟩⟩
  · obtain ⟨b, hb, hbn⟩ := hB.nonempty (Set.mem_univ n.base)
    exact ⟨eta b, ⟨b, hb, rfl⟩, eta_le_iff.mpr hbn⟩
  · rintro _ ⟨⟨b₁, hb₁, rfl⟩, h₁⟩ _ ⟨⟨b₂, hb₂, rfl⟩, h₂⟩
    obtain ⟨c, ⟨hcB, hcn⟩, hc₁, hc₂⟩ :=
      hB.directedOn (Set.mem_univ n.base) b₁ ⟨hb₁, eta_le_iff.mp h₁⟩
        b₂ ⟨hb₂, eta_le_iff.mp h₂⟩
    exact ⟨eta c, ⟨⟨c, hcB, rfl⟩, eta_le_iff.mpr hcn⟩,
      eta_le_eta_iff.mpr hc₁, eta_le_eta_iff.mpr hc₂⟩

/-- **`A ◁ A⁺`** (Gunter, Lemma 24's first clause) at `A⁺ = M(A)`: the copy of
`A` embedded by §7.4's `x ↦ (x, {x})` is normal in `M(A)`. -/
theorem isNormalIn_eta_image_univ :
    eta '' (Set.univ : Set α) ◁ (Set.univ : Set (MPair α)) :=
  isNormalIn_eta_image (IsNormalIn.refl _)

/-- The step that makes a one-point extension normal. Given `⟨x, u⟩ ⊑ n` and
`η c ⊑ n` with `c ∈ B`, an upper bound of both is found **inside** `η''B ∪ {⟨x,u⟩}`
and below `n`.

Two cases. If `⟨x, u⟩ ⊑ n` holds by the printed relation there is `z ∈ u` with
`z ⊑ n.base`; `z` lies in `B` by hypothesis, so directedness of `B ∩ ↓n.base`
joins `z` and `c` to a single `d ∈ B`, and `η d` is the bound — `⟨x,u⟩ ⊑ η d`
because `z ∈ u` and `z ⊑ d`. If it holds by the identification disjunct then
`n ⊑ ⟨x, u⟩` as well, and `⟨x, u⟩` is itself the bound. -/
theorem exists_upper_bound_insert {B : Set α} (hB : B ◁ (Set.univ : Set α))
    {m : MPair α} (hcov : (↑m.cover : Set α) ⊆ B) {n : MPair α} (hmn : m ≤ n)
    {c : α} (hcB : c ∈ B) (hcn : eta c ≤ n) :
    ∃ t ∈ insert m (eta '' B), t ≤ n ∧ eta c ≤ t ∧ m ≤ t := by
  rcases hmn with ⟨z, hz, hzn⟩ | ⟨hb, hu⟩
  · obtain ⟨d, ⟨hdB, hdn⟩, hzd, hcd⟩ :=
      hB.directedOn (Set.mem_univ n.base)
        z ⟨hcov (Finset.mem_coe.mpr hz), hzn⟩ c ⟨hcB, eta_le_iff.mp hcn⟩
    exact ⟨eta d, Set.mem_insert_of_mem _ ⟨d, hdB, rfl⟩, eta_le_iff.mpr hdn,
      eta_le_eta_iff.mpr hcd, le_eta_iff.mpr ⟨z, hz, hzd⟩⟩
  · exact ⟨m, Set.mem_insert _ _, Or.inr ⟨hb, hu⟩,
      hcn.trans (Or.inr ⟨hb.symm, hu.symm⟩), le_rfl⟩

/-- **`B ∪ {Z} ◁ M(A)`** — Gunter, Lemma 24's second clause, normality half.
The only hypothesis on `Z = ⟨x, u⟩` is that its cover lies in `B`; its base is
unconstrained, and neither `A` nor `B` need be finite. -/
theorem isNormalIn_insert_eta_image {B : Set α} (hB : B ◁ (Set.univ : Set α))
    {m : MPair α} (hcov : (↑m.cover : Set α) ⊆ B) :
    insert m (eta '' B) ◁ (Set.univ : Set (MPair α)) := by
  refine ⟨Set.subset_univ _, fun n _ => ⟨?_, ?_⟩⟩
  · obtain ⟨b, hb, hbn⟩ := hB.nonempty (Set.mem_univ n.base)
    exact ⟨eta b, Set.mem_insert_of_mem _ ⟨b, hb, rfl⟩, eta_le_iff.mpr hbn⟩
  · rintro a ⟨ha, han⟩ b ⟨hb, hbn⟩
    rcases ha with rfl | ⟨c₁, hc₁, rfl⟩
    · rcases hb with rfl | ⟨c₂, hc₂, rfl⟩
      · exact ⟨_, ⟨Set.mem_insert _ _, han⟩, le_rfl, le_rfl⟩
      · obtain ⟨t, ht, htn, hct, hmt⟩ :=
          exists_upper_bound_insert hB hcov han hc₂ hbn
        exact ⟨t, ⟨ht, htn⟩, hmt, hct⟩
    · rcases hb with rfl | ⟨c₂, hc₂, rfl⟩
      · obtain ⟨t, ht, htn, hct, hmt⟩ :=
          exists_upper_bound_insert hB hcov hbn hc₁ han
        exact ⟨t, ⟨ht, htn⟩, hct, hmt⟩
      · obtain ⟨d, ⟨hdB, hdn⟩, hd₁, hd₂⟩ :=
          hB.directedOn (Set.mem_univ n.base) c₁ ⟨hc₁, eta_le_iff.mp han⟩
            c₂ ⟨hc₂, eta_le_iff.mp hbn⟩
        exact ⟨eta d, ⟨Set.mem_insert_of_mem _ ⟨d, hdB, rfl⟩, eta_le_iff.mpr hdn⟩,
          eta_le_eta_iff.mpr hd₁, eta_le_eta_iff.mpr hd₂⟩

end Normality

/-! ## Gunter's Lemma 24 at `M(A)` -/

section Lemma24

variable {α : Type u} [PartialOrder α]

/-- **Gunter's Lemma 24 at `A⁺ = M(A)`.**

`B ◁ A` finite and a normal type over `B` — presented, as in
`R46.Agent2.HasNormalRealizations`, by a witnessing poset `γ`, a finite `T ⊆ γ`
with `g''B ◁ T` and `insert z (g''B) ◁ T`, and an order-reflecting `g` — yield a
pair `Z ∈ M(A)` that realizes the type over the embedded copy `η''B` and
satisfies `η''B ∪ {Z} ◁ M(A)`.

The witness is Gunter's own: `Z = ⟨X₀, U⟩` with `X₀` the greatest element of
`B ∩ ↓z` and `U = B ∩ ↑z`. `X₀` exists because `g''B ◁ T` makes `g''B ∩ ↓z`
directed and `B` is finite; it lies below every member of `U` because `z` does.

Three hypotheses of `HasNormalRealizations` are **not used** and are carried only
so the statement matches it: `T.Finite`, and `insert z (g''B) ◁ T` beyond its
consequence `z ∈ T`. Finiteness of `B` is used exactly once, for the greatest
element. -/
theorem gunter87_lemma_24_MPair {B : Set α} (hBfin : B.Finite) (hB : B ◁ (Set.univ : Set α))
    (γ : Type*) [PartialOrder γ] (T : Set γ) (g : α → γ) (z : γ)
    (hg : ∀ a ∈ B, ∀ b ∈ B, (g a ≤ g b ↔ a ≤ b))
    (hgB : g '' B ◁ T) (hzB : insert z (g '' B) ◁ T) :
    ∃ m : MPair α,
      (∀ b ∈ B, (eta b ≤ m ↔ g b ≤ z) ∧ (m ≤ eta b ↔ z ≤ g b)) ∧
      insert m (eta '' B) ◁ (Set.univ : Set (MPair α)) := by
  classical
  have hzT : z ∈ T := hzB.subset (Set.mem_insert _ _)
  -- `L = B ∩ ↓z`, pulled back along `g`.
  set L : Set α := {b | b ∈ B ∧ g b ≤ z} with hLdef
  have hLsub : L ⊆ B := fun b hb => hb.1
  have hLne : L.Nonempty := by
    obtain ⟨w, ⟨b, hbB, rfl⟩, hwz⟩ := hgB.nonempty hzT
    exact ⟨b, hbB, hwz⟩
  have hLdir : DirectedOn (· ≤ ·) L := by
    rintro b₁ ⟨hb₁, hz₁⟩ b₂ ⟨hb₂, hz₂⟩
    obtain ⟨w, ⟨⟨d, hdB, rfl⟩, hdz⟩, h₁, h₂⟩ :=
      hgB.directedOn hzT (g b₁) ⟨⟨b₁, hb₁, rfl⟩, hz₁⟩ (g b₂) ⟨⟨b₂, hb₂, rfl⟩, hz₂⟩
    exact ⟨d, ⟨hdB, hdz⟩, (hg b₁ hb₁ d hdB).mp h₁, (hg b₂ hb₂ d hdB).mp h₂⟩
  obtain ⟨x₀, hx₀, hx₀max⟩ :=
    SFP.exists_greatest_of_finite (hBfin.subset hLsub) hLne hLdir
  -- `U = B ∩ ↑z`, the cover.
  set U : Set α := {b | b ∈ B ∧ z ≤ g b} with hUdef
  have hUfin : U.Finite := hBfin.subset fun b hb => hb.1
  have hbase : ∀ w ∈ hUfin.toFinset, x₀ ≤ w := by
    intro w hw
    obtain ⟨hwB, hzw⟩ := hUfin.mem_toFinset.mp hw
    exact (hg x₀ (hLsub hx₀) w hwB).mp (hx₀.2.trans hzw)
  refine ⟨⟨x₀, hUfin.toFinset, hbase⟩, fun b hb => ⟨?_, ?_⟩, ?_⟩
  · rw [eta_le_iff]
    exact ⟨fun h => ((hg b hb x₀ (hLsub hx₀)).mpr h).trans hx₀.2,
      fun h => hx₀max b ⟨hb, h⟩⟩
  · rw [le_eta_iff]
    constructor
    · rintro ⟨w, hw, hwb⟩
      obtain ⟨hwB, hzw⟩ := hUfin.mem_toFinset.mp hw
      exact hzw.trans ((hg w hwB b hb).mpr hwb)
    · exact fun h => ⟨b, hUfin.mem_toFinset.mpr ⟨hb, h⟩, le_rfl⟩
  · refine isNormalIn_insert_eta_image hB ?_
    intro w hw
    exact (hUfin.mem_toFinset.mp (Finset.mem_coe.mp hw)).1

/-- **Lemma 24 after §7.4's identification.** `Step α = M(α)/≈` is the type the
tower actually uses, and `mk` is a monotone order-reflecting surjection, so the
realization and the normality both transport verbatim.

This is the exact shape `R46.Agent2.HasNormalRealizations` asks of one stage of
the tower — **with `mk ∘ eta` as the connecting map**. That the tower's connecting
map is `stgEmb`, not `mk ∘ eta` (`Colimit.stgEmb_ne_mk_eta`), is precisely why
this does not discharge it; see `not_hasNormalRealizations_Ainf`. -/
theorem gunter87_lemma_24_Step {B : Set α} (hBfin : B.Finite) (hB : B ◁ (Set.univ : Set α))
    (γ : Type*) [PartialOrder γ] (T : Set γ) (g : α → γ) (z : γ)
    (hg : ∀ a ∈ B, ∀ b ∈ B, (g a ≤ g b ↔ a ≤ b))
    (hgB : g '' B ◁ T) (hzB : insert z (g '' B) ◁ T) :
    ∃ q : Step α,
      (∀ b ∈ B, ((mk (eta b) : Step α) ≤ q ↔ g b ≤ z) ∧ (q ≤ mk (eta b) ↔ z ≤ g b)) ∧
      insert q ((fun b => (mk (eta b) : Step α)) '' B) ◁ (Set.univ : Set (Step α)) := by
  obtain ⟨m, hreal, hnorm⟩ := gunter87_lemma_24_MPair hBfin hB γ T g z hg hgB hzB
  refine ⟨mk m, hreal, ?_⟩
  have himg : (mk : MPair α → Step α) '' insert m (eta '' B)
      = insert (mk m) ((fun b => (mk (eta b) : Step α)) '' B) := by
    rw [Set.image_insert_eq, Set.image_image]
  rw [← himg]
  exact isNormalIn_image_univ (f := (mk : MPair α → Step α)) (fun _ _ => Iff.rfl)
    mk_surjective hnorm

end Lemma24

/-! ## `(x, ∅)` is maximal, and the tower keeps it that way -/

section Maximal

/-- §7.4's `b = (⊥, ∅)` read at stage `k + 1`: the pair over `Stg k` with least
base and empty cover. `topElt 0` is `Colimit.pointB1`. -/
def topElt (k : ℕ) : Stg (k + 1) := mk (⟨(⊥ : Stg k), ∅, by simp⟩ : MPair (Stg k))

theorem topElt_zero : topElt 0 = pointB1 := rfl

/-- **The connecting map carries the empty cover along unchanged.** `M(f)` maps
the cover by `f`, and the image of `∅` is `∅`; the base goes to `⊥` because
`stgEmb` preserves it. This is the step at which the two readings of §7.4's tower
part company: `η` would send `(⊥, ∅)` to `((⊥, ∅), {(⊥, ∅)})`, whose cover is not
empty. -/
theorem stgEmb_topElt (k : ℕ) : stgEmb (k + 1) (topElt k) = topElt (k + 1) :=
  congrArg mk (MPair.ext (stgEmb_bot k) (Finset.map_empty _))

/-- `pointB1` lifted to any later stage is that stage's `topElt`. -/
theorem liftStg_pointB1 : ∀ (k : ℕ) (h : 1 ≤ k + 1), liftStg h pointB1 = topElt k
  | 0, h => by
    rw [Subsingleton.elim h (le_refl 1), liftStg_self]
    exact topElt_zero.symm
  | k + 1, h => by
    rw [liftStg_succ (Nat.le_add_left 1 k) pointB1 h, liftStg_pointB1 k _, stgEmb_topElt]

/-- **`(⊥, ∅)` is maximal at every stage.** `⟨⊥, ∅⟩ ⊑ n` cannot hold by the
printed relation — that needs a member of the empty cover — so it holds by the
identification, which forces `n` to have base `⊥` and empty up-set, i.e. to be the
same point after §7.4's identification. -/
theorem topElt_maximal {k : ℕ} {y : Stg (k + 1)} (h : topElt k ≤ y) : y = topElt k := by
  obtain ⟨n, rfl⟩ := mk_surjective (α := Stg k) y
  rcases h with ⟨w, hw, -⟩ | ⟨hb, hu⟩
  · exact absurd hw (Finset.notMem_empty w)
  · exact le_antisymm (mk_le_mk.mpr (Or.inr ⟨hb.symm, hu.symm⟩))
      (mk_le_mk.mpr (Or.inr ⟨hb, hu⟩))

/-- **`β = incl 1 pointB1` is a maximal point of `A∞`.** Any `w` above it lives in
some stage `m`; comparing at stage `m + 1` puts `topElt m` below `w`'s
representative, and `topElt_maximal` identifies them. -/
theorem incl_pointB1_maximal {w : Ainf} (h : incl 1 pointB1 ≤ w) :
    w = incl 1 pointB1 := by
  obtain ⟨m, x, rfl⟩ := incl_surjective w
  have h1 : 1 ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le m)
  have hm : m ≤ m + 1 := Nat.le_succ m
  rw [incl_le_incl_iff pointB1 x h1 hm, liftStg_pointB1 m h1] at h
  rw [← incl_lift hm x, topElt_maximal h, ← liftStg_pointB1 m h1, incl_lift h1]

/-- **Under `η` the maximality is destroyed at the very next stage.** `(b, ∅)` is
strictly above `η b = (b, {b})` in `M(Stg 1)`, so §7.4's own connecting map does
*not* preserve maximality — which is why Gunter's Lemma 24 holds of the `η`-tower
and fails of this one. Contrast `stgEmb_topElt`. -/
theorem exists_gt_mk_eta_pointB1 :
    ∃ y : Stg 2, (mk (eta pointB1) : Stg 2) ≤ y ∧ ¬ (y ≤ mk (eta pointB1)) := by
  refine ⟨mk (⟨pointB1, ∅, by simp⟩ : MPair (Stg 1)), mk_le_mk.mpr (eta_le_iff.mpr le_rfl), ?_⟩
  intro hle
  obtain ⟨w, hw, -⟩ := le_eta_iff.mp (mk_le_mk.mp hle)
  exact absurd hw (Finset.notMem_empty w)

end Maximal

/-! ## The mechanism: a normal maximal point refutes the property -/

section Mechanism

variable {α : Type} [PartialOrder α] [OrderBot α]

-- The map into the witnessing poset: the three-element chain `Fin 3`, with
-- `0 = wit ⊥`, `1 = wit a` and `2` the point of the type.
open scoped Classical in
private noncomputable def wit (a x : α) : Fin 3 := if a ≤ x then 1 else 0

omit [OrderBot α] in
private theorem wit_self (a : α) : wit a a = 1 := by
  unfold wit
  exact if_pos le_rfl

private theorem wit_bot {a : α} (hne : a ≠ ⊥) : wit a (⊥ : α) = 0 := by
  unfold wit
  exact if_neg fun h => hne (le_bot_iff.mp h)

private theorem wit_image {a : α} (hne : a ≠ ⊥) :
    wit a '' ({⊥, a} : Set α) = ({0, 1} : Set (Fin 3)) := by
  rw [Set.image_insert_eq, Set.image_singleton, wit_bot hne, wit_self]

/-- Any subset of a linear order is directed, and `0` is below everything in
`Fin 3`, so `{0, 1} ◁ Fin 3`. This is what makes the type below **normal** — the
hypothesis the refutation would be worthless without. -/
private theorem pair_isNormalIn : ({0, 1} : Set (Fin 3)) ◁ (Set.univ : Set (Fin 3)) := by
  refine ⟨Set.subset_univ _, fun x _ => ⟨⟨0, Or.inl rfl, Fin.zero_le x⟩, ?_⟩⟩
  rintro c ⟨hc, hcx⟩ d ⟨hd, hdx⟩
  rcases le_total c d with h | h
  · exact ⟨d, ⟨hd, hdx⟩, h, le_rfl⟩
  · exact ⟨c, ⟨hc, hcx⟩, le_rfl, h⟩

private theorem triple_eq_univ : (insert 2 ({0, 1} : Set (Fin 3))) = Set.univ := by
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  fin_cases x <;> simp

/-- **A poset with a normal maximal point other than `⊥` has no normal
realizations.**

If `a ≠ ⊥` is maximal and `{⊥, a} ◁ α`, then the type of a point strictly above
`a` is normal — the three-element chain `Fin 3` realizes it, with
`{0, 1} ◁ Fin 3` and `{0, 1, 2} ◁ Fin 3` — and `α` cannot realize it, because a
realization would satisfy `a ⊑ y` and `y ⋢ a` while maximality forces `y = a`.

This is Gunter's Theorem 25 hypothesis failing for a structural reason, not for a
contrived one: **the property forbids normal maximal points outright.** -/
theorem not_hasNormalRealizations_of_maximal {a : α} (hne : a ≠ ⊥)
    (hA : ({⊥, a} : Set α) ◁ (Set.univ : Set α)) (hmax : ∀ w : α, a ≤ w → w = a) :
    ¬ R46.Agent2.HasNormalRealizations α := by
  intro H
  have hmem : ∀ x ∈ ({⊥, a} : Set α), x = ⊥ ∨ x = a := fun _ hx => hx
  obtain ⟨y, hy, -⟩ :=
    H ({⊥, a} : Set α) ((Set.finite_singleton a).insert _) hA
      (Fin 3) (Set.univ : Set (Fin 3)) Set.finite_univ (wit a) 2
      (by
        intro c hc d hd
        rcases hmem c hc with rfl | rfl <;> rcases hmem d hd with rfl | rfl
        · simp [wit_bot hne]
        · simp only [wit_bot hne, wit_self]
          exact iff_of_true (by decide) bot_le
        · simp only [wit_bot hne, wit_self]
          exact iff_of_false (by decide) fun h => hne (le_bot_iff.mp h)
        · simp [wit_self])
      (by rw [wit_image hne]; exact pair_isNormalIn)
      (by rw [wit_image hne, triple_eq_univ]; exact IsNormalIn.refl _)
  obtain ⟨hup, hdown⟩ := hy a (Set.mem_insert_of_mem _ rfl)
  rw [wit_self] at hup hdown
  exact absurd (hdown.mp (le_of_eq (hmax y (hup.mpr (by decide))))) (by decide)

end Mechanism

/-! ## The refutation of `HasNormalRealizations A∞` -/

section Refutation

/-- `im(incl 1)` is `{⊥, β}`: `Stg 1` has exactly §7.4's two points `a` and `b`. -/
theorem range_incl_one : Set.range (incl 1) = ({⊥, incl 1 pointB1} : Set Ainf) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    rcases stg_one_eq x with rfl | rfl
    · exact Or.inl (incl_bot 1)
    · exact Or.inr rfl
  · rintro _ (rfl | rfl)
    · exact ⟨(⊥ : Stg 1), incl_bot 1⟩
    · exact ⟨pointB1, rfl⟩

/-- **`HasNormalRealizations A∞` is false.**

`β = incl 1 pointB1` is §7.4's own `b = (⊥, ∅)` sitting in the colimit. It is not
`⊥` (`incl_pointB1_ne_bot`), it is maximal (`incl_pointB1_maximal`), and `{⊥, β}`
is `im(incl 1)`, normal in `A∞` (`isNormalIn_range_incl`). So
`not_hasNormalRealizations_of_maximal` applies.

This refutes the target of r0046's reduction
`theorem_29_normal_of_hasNormalRealizations`. The implication stands; its hypothesis
cannot be met at this `A∞`. It does **not** refute `Lemma30.Theorem29Normal`, which
does not require `β` to lie in the range of the embedding it asks for. -/
theorem not_hasNormalRealizations_Ainf : ¬ R46.Agent2.HasNormalRealizations Ainf :=
  not_hasNormalRealizations_of_maximal incl_pointB1_ne_bot
    (range_incl_one ▸ isNormalIn_range_incl 1)
    (fun _ h => incl_pointB1_maximal h)

/-- **The stagewise residue is false too.** `hasNormalRealizations_of_stages`
derives `HasNormalRealizations A∞` from the property asked of a single step of the
tower — the sentence `Lemma30.lean:426` names as missing — so that sentence is
refuted along with it. What r0046 identified as "the whole of what remains" is
not provable at this tower. -/
theorem not_stagewise_realizations :
    ¬ (∀ (n : ℕ) (A : Set Ainf), A.Finite → A ◁ Set.range (incl n) →
        ∀ (β : Type) [PartialOrder β] (T : Set β), T.Finite → ∀ (g : Ainf → β) (z : β),
          (∀ a ∈ A, ∀ b ∈ A, (g a ≤ g b ↔ a ≤ b)) →
          g '' A ◁ T → insert z (g '' A) ◁ T →
          ∃ y : Ainf, R46.Agent2.SameTypeOver A g z y ∧
            ∃ m : ℕ, insert y A ◁ Set.range (incl m)) :=
  fun h => not_hasNormalRealizations_Ainf (R46.Agent2.hasNormalRealizations_of_stages h)

end Refutation

end ScottDomains.R47.Agent1
