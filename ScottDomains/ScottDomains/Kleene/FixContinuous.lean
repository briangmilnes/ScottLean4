import ScottDomains.FixedPoint
import ScottDomains.ScottHom

/-!
# `fix` is a continuous function of `f`

Gunter & Scott, *Semantic Domains*, §2.3 (printed p. 7):

> Indeed, it is possible to show that, given a cpo `D`, the function
> `fix_D : (D → D) → D` given by `fix_D(f) = ⨆ₙ fⁿ(⊥)` is actually *continuous*.

`FixedPoint.lean` proves Theorem 1 — that `⨆ₙ fⁿ(⊥)` is the least fixed point of
a continuous `f` — but says nothing about how `fix` varies with `f`. `kleeneFix`
there is a bare `(α → α) → α`, never bundled, and the r0040 property audit
recorded this sentence as having no Lean statement in any form.

The sentence matters beyond bookkeeping: the definition of a *fixed point
operator* in the next paragraph (`UniformFixedPoint.lean`) asks each `F_D` to be
continuous, so without this result `kleeneOperator` is not known to satisfy the
paper's own definition of the object Theorem 3 is about.

## The proof

Monotonicity is an induction on the iterate index: `f ⊑ g` gives
`fⁿ(⊥) ⊑ gⁿ(⊥)` because `f (fⁿ ⊥) ⊑ g (fⁿ ⊥) ⊑ g (gⁿ ⊥)`.

Continuity is the two-sided argument. Write `S = {fix(f) | f ∈ M}` for a directed
`M ⊆ D → D` with least upper bound `F`. `S` is directed (image of a directed set
under a monotone map), so `⨆S` exists, and `⨆S ⊑ fix(F)` by monotonicity. The
content is the converse, `fix(F) ⊑ ⨆S`, and it goes through one intermediate
fact:

* **`⨆S` is a pre-fixed point of every `f ∈ M`.** Continuity of `f` reduces
  `f(⨆S) ⊑ ⨆S` to `f(fix(g)) ⊑ ⨆S` for `g ∈ M`; directedness of `M` supplies a
  `k ∈ M` above both `f` and `g`, and then
  `f(fix g) ⊑ k(fix k) = fix k ⊑ ⨆S`.

With that, `Fⁿ(⊥) ⊑ ⨆S` by induction: `F` is the *pointwise* supremum of `M`
(`ScottHom.isLUB_eval_image_of_isLUB`), so `F(Fⁿ ⊥) ⊑ ⨆S` follows from
`f(Fⁿ ⊥) ⊑ f(⨆S) ⊑ ⨆S` for each `f ∈ M`.
-/

namespace ScottDomains.Kleene

variable {α : Type*} [CompletePartialOrder α]

/-- The Kleene iterates ascend with the function: `f ⊑ g` pointwise implies
`fⁿ(⊥) ⊑ gⁿ(⊥)` for every `n`. -/
theorem iterate_bot_le_iterate_bot {f g : α → α} (hg : Monotone g) (hfg : ∀ x, f x ≤ g x) :
    ∀ n : ℕ, f^[n] ⊥ ≤ g^[n] ⊥ := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply' f k, Function.iterate_succ_apply' g k]
    exact (hfg _).trans (hg ih)

/-- `fix` is monotone in `f`, on the underlying functions. -/
theorem kleeneFix_mono {f g : α → α} (hf : Monotone f) (hg : Monotone g)
    (hfg : ∀ x, f x ≤ g x) : kleeneFix f ≤ kleeneFix g := by
  refine (directedOn_kleeneChain hf).sSup_le ?_
  rintro _ ⟨n, rfl⟩
  exact (iterate_bot_le_iterate_bot hg hfg n).trans (le_kleeneFix hg n)

/-- `fix_D : (D → D) → D` is monotone. -/
theorem monotone_kleeneFix : Monotone fun f : ScottHom α α => kleeneFix ⇑f :=
  fun _ _ h => kleeneFix_mono (by exact ScottHom.monotone _) (by exact ScottHom.monotone _) h

/-- The image of a directed set of continuous functions under `fix` is directed. -/
theorem directedOn_kleeneFix_image {d : Set (ScottHom α α)} (hd : DirectedOn (· ≤ ·) d) :
    DirectedOn (· ≤ ·) ((fun f : ScottHom α α => kleeneFix ⇑f) '' d) := by
  rintro _ ⟨f, hf, rfl⟩ _ ⟨g, hg, rfl⟩
  obtain ⟨k, hk, hfk, hgk⟩ := hd f hf g hg
  exact ⟨kleeneFix ⇑k, ⟨k, hk, rfl⟩, monotone_kleeneFix hfk, monotone_kleeneFix hgk⟩

/-- The supremum of `{fix(g) | g ∈ M}` is a pre-fixed point of every `f ∈ M`,
when `M` is directed. This is the one step of the continuity proof that uses
directedness of `M` rather than of the image. -/
theorem apply_sSup_kleeneFix_image_le {d : Set (ScottHom α α)} (hne : d.Nonempty)
    (hd : DirectedOn (· ≤ ·) d) {f : ScottHom α α} (hf : f ∈ d) :
    ⇑f (sSup ((fun g : ScottHom α α => kleeneFix ⇑g) '' d)) ≤
      sSup ((fun g : ScottHom α α => kleeneFix ⇑g) '' d) := by
  have hSdir := directedOn_kleeneFix_image hd
  refine (f.scottContinuous (hne.image _) hSdir hSdir.isLUB_sSup).2 ?_
  rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
  obtain ⟨k, hk, hfk, hgk⟩ := hd f hf g hg
  calc ⇑f (kleeneFix ⇑g) ≤ ⇑k (kleeneFix ⇑k) :=
        (f.monotone (monotone_kleeneFix hgk)).trans (hfk _)
    _ = kleeneFix ⇑k := map_kleeneFix k.scottContinuous
    _ ≤ sSup _ := hSdir.le_sSup ⟨k, hk, rfl⟩

/-- `fix(F) ⊑ ⨆{fix(g) | g ∈ M}` when `F` is the least upper bound of the
directed set `M`. Every Kleene iterate of `F` is below the right-hand side, by
induction through the pointwise description of `F`. -/
theorem kleeneFix_le_sSup_kleeneFix_image {d : Set (ScottHom α α)} (hne : d.Nonempty)
    (hd : DirectedOn (· ≤ ·) d) {F : ScottHom α α} (hF : IsLUB d F) :
    kleeneFix ⇑F ≤ sSup ((fun g : ScottHom α α => kleeneFix ⇑g) '' d) := by
  refine (directedOn_kleeneChain F.monotone).sSup_le ?_
  rintro _ ⟨n, rfl⟩
  show (⇑F)^[n] ⊥ ≤ sSup ((fun g : ScottHom α α => kleeneFix ⇑g) '' d)
  induction n with
  | zero => exact bot_le
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    refine (ScottHom.isLUB_eval_image_of_isLUB hd hF ((⇑F)^[m] ⊥)).2 ?_
    rintro _ ⟨f, hf, rfl⟩
    exact (f.monotone ih).trans (apply_sSup_kleeneFix_image_le hne hd hf)

/-- **`fix_D : (D → D) → D` is continuous.** §2.3's sentence, in full. -/
theorem scottContinuous_kleeneFix :
    ScottContinuous fun f : ScottHom α α => kleeneFix ⇑f := by
  intro d hne hd F hF
  have hSdir := directedOn_kleeneFix_image hd
  have hle : sSup ((fun g : ScottHom α α => kleeneFix ⇑g) '' d) ≤ kleeneFix ⇑F := by
    refine hSdir.sSup_le ?_
    rintro _ ⟨f, hf, rfl⟩
    exact monotone_kleeneFix (hF.1 hf)
  have heq : sSup ((fun g : ScottHom α α => kleeneFix ⇑g) '' d) = kleeneFix ⇑F :=
    le_antisymm hle (kleeneFix_le_sSup_kleeneFix_image hne hd hF)
  show IsLUB ((fun g : ScottHom α α => kleeneFix ⇑g) '' d) (kleeneFix ⇑F)
  rw [← heq]
  exact hSdir.isLUB_sSup

/-- **`fix` as an element of `(D → D) → D`.** The paper writes `fix_D` as a
member of the continuous function space, and this is that bundling. -/
noncomputable def fixHom (α : Type*) [CompletePartialOrder α] : ScottHom (ScottHom α α) α :=
  ⟨fun f => kleeneFix ⇑f, scottContinuous_kleeneFix⟩

@[simp] theorem fixHom_apply (f : ScottHom α α) : fixHom α f = kleeneFix ⇑f := rfl

/-- Theorem 1 restated for the bundled operator: `fix(f)` is the least fixed
point of `f`. -/
theorem isLeast_fixHom (f : ScottHom α α) : IsLeast {a | ⇑f a = a} (fixHom α f) :=
  theorem_1 f.scottContinuous

end ScottDomains.Kleene
