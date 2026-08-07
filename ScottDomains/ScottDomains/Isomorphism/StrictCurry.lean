import ScottDomains.Currying
import ScottDomains.Smash
import ScottDomains.StrictHom

/-!
# Lemma 9, part 4: strict currying

Gunter & Scott, *Semantic Domains*, Lemma 9.4:

> `D ◦→ (E ◦→ F) ≅ (D ⊗ E) ◦→ F`.

This is Lemma 8.4 (`scottHomCurry`, `Currying.lean`) with `×` replaced by `⊗`
and `→` by `◦→`: the smash product is the tensor for which the strict function
space is the internal hom. The paper introduces the two maps by name on the
preceding page, as *strict apply* and *strict curry*.

## The strategy: factor through the product, do not redo it

Nothing here re-proves the joint-versus-separate continuity argument. That is
`ScottHom.curry` / `ScottHom.uncurry`, already checked over `D × E`. Two
transport maps carry it to `D ⊗ E`:

* `smashVal : D ⊗ E → D × E` sends the adjoined bottom to `(⊥, ⊥)` and every
  other element to the pair it names;
* `smashPair : D × E → D ⊗ E` sends a pair with a `⊥` coordinate to the adjoined
  bottom and every other pair to itself.

Both are Scott continuous, and each direction of the isomorphism is a
composition: `uncurryStrict g = uncurry (…) ∘ smashVal`, and
`curryStrict f = curry (⇑f ∘ smashPair)`.

`scottContinuous_smashPair` is the one argument with content. On a directed `s`
whose least upper bound `c` has **both** coordinates non-`⊥`, some member of `s`
already has both coordinates non-`⊥`. That is not immediate — a member may be
`(x, ⊥)` and another `(⊥, y)` — and it is exactly where directedness is spent:
take a member with non-`⊥` first coordinate (one exists, or `(⊥, c.2)` would
bound `s` and force `c.1 = ⊥`), a member with non-`⊥` second coordinate, and the
member of `s` above both.

## Strictness bookkeeping

`StrictHom` is a subtype of `ScottHom`, so a least upper bound in it is a least
upper bound in `ScottHom` whose value happens to be strict
(`isLUB_strictHom_of_isLUB_val`), and the coercion `Subtype.val` is itself Scott
continuous (`scottContinuous_subtypeVal`). Those two lemmas are the whole of the
subtype bookkeeping; every remaining strictness obligation is a one-line
computation at `⊥`.
-/

namespace ScottDomains.Isomorphism

open ScottDomains

variable {α β γ : Type*}
variable [CompletePartialOrder α] [CompletePartialOrder β] [CompletePartialOrder γ]

/-! ### Subtype bookkeeping for `StrictHom` -/

/-- A least upper bound in `D → E` whose value is strict is a least upper bound
in `D ◦→ E`: the order is inherited, and a strict upper bound is in particular an
upper bound in the ambient function space. -/
theorem isLUB_strictHom_of_isLUB_val {S : Set (StrictHom β γ)} {F : StrictHom β γ}
    (h : IsLUB (Subtype.val '' S) F.val) : IsLUB S F :=
  ⟨fun f hf => h.1 ⟨f, hf, rfl⟩, fun u hu => h.2 (by rintro _ ⟨f, hf, rfl⟩; exact hu hf)⟩

/-- **The inclusion `D ◦→ E ↪ D → E` is Scott continuous.** `StrictHom`'s own
`sSup` is the ambient one, so the least upper bound transfers by uniqueness. -/
theorem scottContinuous_subtypeVal :
    ScottContinuous (Subtype.val : StrictHom β γ → ScottHom β γ) := by
  intro S hne hS F hF
  have hdir : DirectedOn (· ≤ ·) (Subtype.val '' S) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨c, hc, hac, hbc⟩ := hS a ha b hb
    exact ⟨c.val, ⟨c, hc, rfl⟩, hac, hbc⟩
  have hFs : F = sSup S := hF.unique (DirectedOn.isLUB_sSup hS)
  have hval : F.val = sSup (Subtype.val '' S) := by
    rw [hFs]
    rfl
  rw [hval]
  exact hdir.isLUB_sSup

/-! ### The two transport maps between `D ⊗ E` and `D × E` -/

/-- `D ⊗ E → D × E`: the adjoined bottom goes to `(⊥, ⊥)`. -/
def smashVal : Smash α β → α × β :=
  fun z => WithBot.recBotCoe (C := fun _ => α × β) ⊥ Subtype.val z

@[simp] theorem smashVal_bot : smashVal (⊥ : Smash α β) = (⊥ : α × β) := rfl

@[simp] theorem smashVal_coe (p : NonBotPair α β) :
    smashVal (↑p : Smash α β) = p.val := rfl

theorem scottContinuous_smashVal : ScottContinuous (smashVal : Smash α β → α × β) := by
  intro s hne hs w hw
  induction w using WithBot.recBotCoe with
  | bot =>
    have hall : ∀ z ∈ s, z = (⊥ : Smash α β) := fun z hz => le_bot_iff.mp (hw.1 hz)
    constructor
    · rintro _ ⟨z, hz, rfl⟩
      exact le_of_eq (congrArg smashVal (hall z hz))
    · intro u hu
      obtain ⟨z₀, hz₀⟩ := hne
      have h := hu ⟨z₀, hz₀, rfl⟩
      rwa [hall z₀ hz₀] at h
  | coe q =>
    obtain ⟨p₀, hp₀⟩ : (smashBase s).Nonempty := by
      by_contra hempty
      have hub : (⊥ : Smash α β) ∈ upperBounds s := by
        intro z hz
        induction z using WithBot.recBotCoe with
        | bot => exact le_rfl
        | coe p => exact absurd ⟨p, hz⟩ hempty
      exact WithBot.not_coe_le_bot q (hw.2 hub)
    constructor
    · rintro _ ⟨z, hz, rfl⟩
      induction z using WithBot.recBotCoe with
      | bot => exact bot_le
      | coe p => exact (WithBot.coe_le_coe (α := NonBotPair α β)).mp (hw.1 hz)
    · intro c hc
      have hp₀c : p₀.val ≤ c := hc ⟨(↑p₀ : Smash α β), coe_mem_of_mem_smashBase hp₀, rfl⟩
      have hc1 : c.1 ≠ ⊥ := fun hb => p₀.2.1 (le_bot_iff.mp (hp₀c.1.trans (le_of_eq hb)))
      have hc2 : c.2 ≠ ⊥ := fun hb => p₀.2.2 (le_bot_iff.mp (hp₀c.2.trans (le_of_eq hb)))
      have hub : (↑(⟨c, hc1, hc2⟩ : NonBotPair α β) : Smash α β) ∈ upperBounds s := by
        intro z hz
        induction z using WithBot.recBotCoe with
        | bot => exact bot_le
        | coe p =>
          exact (WithBot.coe_le_coe (α := NonBotPair α β)).mpr (hc ⟨(↑p : Smash α β), hz, rfl⟩)
      exact (WithBot.coe_le_coe (α := NonBotPair α β)).mp (hw.2 hub)

open Classical in
/-- `D × E → D ⊗ E`: a pair with a `⊥` coordinate is collapsed to the adjoined
bottom. -/
noncomputable def smashPair (p : α × β) : Smash α β :=
  if h : p.1 ≠ ⊥ ∧ p.2 ≠ ⊥ then ↑(⟨p, h⟩ : NonBotPair α β) else ⊥

theorem smashPair_of_ne {p : α × β} (h : p.1 ≠ ⊥ ∧ p.2 ≠ ⊥) :
    smashPair p = ↑(⟨p, h⟩ : NonBotPair α β) := dif_pos h

theorem smashPair_of_bot {p : α × β} (h : ¬(p.1 ≠ ⊥ ∧ p.2 ≠ ⊥)) :
    smashPair p = (⊥ : Smash α β) := dif_neg h

theorem smashPair_mono : Monotone (smashPair : α × β → Smash α β) := by
  intro p q hpq
  by_cases h : p.1 ≠ ⊥ ∧ p.2 ≠ ⊥
  · have h' : q.1 ≠ ⊥ ∧ q.2 ≠ ⊥ :=
      ⟨fun hb => h.1 (le_bot_iff.mp (hpq.1.trans (le_of_eq hb))),
        fun hb => h.2 (le_bot_iff.mp (hpq.2.trans (le_of_eq hb)))⟩
    rw [smashPair_of_ne h, smashPair_of_ne h']
    exact (WithBot.coe_le_coe (α := NonBotPair α β)).mpr hpq
  · rw [smashPair_of_bot h]
    exact bot_le

/-- **`smashPair` is Scott continuous.** The case split is on whether the least
upper bound has both coordinates non-`⊥`. On the branch where it does,
directedness supplies a *single* member of the set with both coordinates
non-`⊥`, which is what makes the collapsed elements harmless. -/
theorem scottContinuous_smashPair : ScottContinuous (smashPair : α × β → Smash α β) := by
  intro s hne hs c hc
  by_cases hcb : c.1 ≠ ⊥ ∧ c.2 ≠ ⊥
  · obtain ⟨p₀, hp₀, hp₀1, hp₀2⟩ : ∃ p ∈ s, p.1 ≠ (⊥ : α) ∧ p.2 ≠ (⊥ : β) := by
      obtain ⟨p₁, hp₁, hp₁1⟩ : ∃ p ∈ s, p.1 ≠ (⊥ : α) := by
        by_contra hcon
        have hub : ((⊥ : α), c.2) ∈ upperBounds s := by
          intro p hp
          refine ⟨?_, (hc.1 hp).2⟩
          by_cases hb : p.1 = ⊥
          · exact le_of_eq hb
          · exact absurd ⟨p, hp, hb⟩ hcon
        exact hcb.1 (le_bot_iff.mp (hc.2 hub).1)
      obtain ⟨p₂, hp₂, hp₂2⟩ : ∃ p ∈ s, p.2 ≠ (⊥ : β) := by
        by_contra hcon
        have hub : (c.1, (⊥ : β)) ∈ upperBounds s := by
          intro p hp
          refine ⟨(hc.1 hp).1, ?_⟩
          by_cases hb : p.2 = ⊥
          · exact le_of_eq hb
          · exact absurd ⟨p, hp, hb⟩ hcon
        exact hcb.2 (le_bot_iff.mp (hc.2 hub).2)
      obtain ⟨p₃, hp₃, hle₁, hle₂⟩ := hs p₁ hp₁ p₂ hp₂
      exact ⟨p₃, hp₃, fun hb => hp₁1 (le_bot_iff.mp (hle₁.1.trans (le_of_eq hb))),
        fun hb => hp₂2 (le_bot_iff.mp (hle₂.2.trans (le_of_eq hb)))⟩
    constructor
    · rintro _ ⟨p, hp, rfl⟩
      exact smashPair_mono (hc.1 hp)
    · intro u hu
      have h₀ : smashPair p₀ ≤ u := hu ⟨p₀, hp₀, rfl⟩
      rw [smashPair_of_ne ⟨hp₀1, hp₀2⟩] at h₀
      induction u using WithBot.recBotCoe with
      | bot => exact absurd h₀ (WithBot.not_coe_le_bot _)
      | coe r =>
        rw [smashPair_of_ne hcb]
        refine (WithBot.coe_le_coe (α := NonBotPair α β)).mpr ?_
        show c ≤ r.val
        refine hc.2 ?_
        intro p hp
        obtain ⟨p₃, hp₃, hle₁, hle₂⟩ := hs p hp p₀ hp₀
        have h1 : p₃.1 ≠ (⊥ : α) := fun hb => hp₀1 (le_bot_iff.mp (hle₂.1.trans (le_of_eq hb)))
        have h2 : p₃.2 ≠ (⊥ : β) := fun hb => hp₀2 (le_bot_iff.mp (hle₂.2.trans (le_of_eq hb)))
        have h₃ : smashPair p₃ ≤ (↑r : Smash α β) := hu ⟨p₃, hp₃, rfl⟩
        rw [smashPair_of_ne ⟨h1, h2⟩] at h₃
        exact hle₁.trans ((WithBot.coe_le_coe (α := NonBotPair α β)).mp h₃)
  · have hall : ∀ p ∈ s, smashPair p = (⊥ : Smash α β) := by
      intro p hp
      refine smashPair_of_bot ?_
      rintro ⟨h1, h2⟩
      exact hcb ⟨fun hb => h1 (le_bot_iff.mp ((hc.1 hp).1.trans (le_of_eq hb))),
        fun hb => h2 (le_bot_iff.mp ((hc.1 hp).2.trans (le_of_eq hb)))⟩
    rw [smashPair_of_bot hcb]
    constructor
    · rintro _ ⟨p, hp, rfl⟩
      exact le_of_eq (hall p hp)
    · intro _ _
      exact bot_le

/-! ### Strict uncurrying -/

/-- Forgetting strictness in the codomain of `g : D ◦→ (E ◦→ F)`. -/
noncomputable def strictToScottHom (g : StrictHom α (StrictHom β γ)) :
    ScottHom α (ScottHom β γ) :=
  ⟨fun x => (g.val x).val, g.val.scottContinuous.comp scottContinuous_subtypeVal⟩

/-- A doubly strict map is `⊥` as soon as its **first** argument is `⊥`: `g ⊥` is
the least element of `E ◦→ F`, which is the constant-`⊥` function. -/
theorem strictHom_apply_bot_left (g : StrictHom α (StrictHom β γ)) (y : β) :
    (g.val (⊥ : α)).val y = ⊥ :=
  congrArg (fun k : StrictHom β γ => k.val y) g.2

/-- **Strict apply.** `(D ⊗ E) ◦→ F` from `D ◦→ (E ◦→ F)`. -/
noncomputable def uncurryStrict (g : StrictHom α (StrictHom β γ)) :
    StrictHom (Smash α β) γ :=
  ⟨⟨fun z => (ScottHom.uncurry (strictToScottHom g)) (smashVal z),
      scottContinuous_smashVal.comp (ScottHom.uncurry (strictToScottHom g)).scottContinuous⟩, by
    show (g.val (⊥ : α)).val (⊥ : β) = ⊥
    rw [g.2]
    rfl⟩

/-! ### Strict currying -/

/-- `f : (D ⊗ E) ◦→ F` read as a jointly continuous map on `D × E`. -/
noncomputable def curryStrictInner (f : StrictHom (Smash α β) γ) : ScottHom (α × β) γ :=
  ⟨fun p => f.val (smashPair p), scottContinuous_smashPair.comp f.val.scottContinuous⟩

/-- Fixing the first argument. Strict, because `smashPair (x, ⊥) = ⊥`. -/
noncomputable def curryStrictApply (f : StrictHom (Smash α β) γ) (x : α) : StrictHom β γ :=
  ⟨(ScottHom.curry (curryStrictInner f)) x, by
    show f.val (smashPair (x, (⊥ : β))) = ⊥
    rw [smashPair_of_bot fun h => h.2 rfl]
    exact f.2⟩

/-- **Strict curry.** `D ◦→ (E ◦→ F)` from `(D ⊗ E) ◦→ F`. -/
noncomputable def curryStrict (f : StrictHom (Smash α β) γ) :
    StrictHom α (StrictHom β γ) :=
  ⟨⟨curryStrictApply f, by
      intro s hne hs a ha
      refine isLUB_strictHom_of_isLUB_val ?_
      have himg : Subtype.val '' ((curryStrictApply f) '' s)
          = (⇑(ScottHom.curry (curryStrictInner f))) '' s := by
        rw [Set.image_image]
        rfl
      rw [himg]
      exact (ScottHom.curry (curryStrictInner f)).scottContinuous hne hs ha⟩, by
    show curryStrictApply f (⊥ : α) = (⊥ : StrictHom β γ)
    refine Subtype.ext (ScottHom.ext ?_)
    intro y
    show f.val (smashPair ((⊥ : α), y)) = ⊥
    rw [smashPair_of_bot fun h => h.1 rfl]
    exact f.2⟩

/-- **Lemma 9.4**, as a named map: `D ◦→ (E ◦→ F) ≅ (D ⊗ E) ◦→ F`. -/
noncomputable def smashCurry :
    StrictHom α (StrictHom β γ) ≃o StrictHom (Smash α β) γ where
  toFun := uncurryStrict
  invFun := curryStrict
  left_inv g := by
    refine Subtype.ext (ScottHom.ext ?_)
    intro x
    refine Subtype.ext (ScottHom.ext ?_)
    intro y
    show (uncurryStrict g).val (smashPair (x, y)) = (g.val x).val y
    by_cases hb : x ≠ ⊥ ∧ y ≠ ⊥
    · rw [smashPair_of_ne hb]
      rfl
    · have hxy : x = ⊥ ∨ y = ⊥ := by
        by_contra hcon
        exact hb ⟨fun hbx => hcon (Or.inl hbx), fun hby => hcon (Or.inr hby)⟩
      rw [smashPair_of_bot hb, (uncurryStrict g).2]
      rcases hxy with hx | hy
      · rw [hx, g.2]
        rfl
      · rw [hy]
        exact ((g.val x).2).symm
  right_inv f := by
    refine Subtype.ext (ScottHom.ext ?_)
    intro z
    induction z using WithBot.recBotCoe with
    | bot => exact ((uncurryStrict (curryStrict f)).2).trans f.2.symm
    | coe p =>
      show f.val (smashPair p.val) = f.val (↑p : Smash α β)
      rw [smashPair_of_ne p.2]
  map_rel_iff' := by
    intro g h
    constructor
    · intro hle x y
      by_cases hb : x ≠ ⊥ ∧ y ≠ ⊥
      · have hz := hle (smashPair (x, y))
        rw [smashPair_of_ne hb] at hz
        exact hz
      · have hxy : x = ⊥ ∨ y = ⊥ := by
          by_contra hcon
          exact hb ⟨fun hbx => hcon (Or.inl hbx), fun hby => hcon (Or.inr hby)⟩
        rcases hxy with hx | hy
        · rw [hx]
          exact (strictHom_apply_bot_left g y).trans_le bot_le
        · rw [hy]
          exact ((g.val x).2).trans_le bot_le
    · intro hle z
      induction z using WithBot.recBotCoe with
      | bot => exact le_of_eq ((uncurryStrict g).2.trans (uncurryStrict h).2.symm)
      | coe p => exact hle p.val.1 p.val.2

end ScottDomains.Isomorphism
