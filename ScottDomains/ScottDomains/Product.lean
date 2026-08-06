import ScottDomains.ScottHom
import Mathlib.Order.CompleteLattice.Basic

/-!
# Products of cpos, and Lemma 8 (parts 1–3)

Gunter & Scott, *Semantic Domains*, §4.5:

> **Lemma 8** Let `D`, `E` and `F` be cpo's, then
> 1. `D × E ≅ E × D`,
> 2. `(D × E) × F ≅ D × (E × F)`,
> 3. `D → (E × F) ≅ (D → E) × (D → F)`,
> 4. `D → (E → F) ≅ (D × E) → F`.

This file supplies the product cpo and parts 1–3. Part 4 — currying — needs the
equivalence between joint and separate Scott continuity and is separate work.

## The product cpo costs no case split

Mathlib supplies `Prod.supSet` (`Order/CompleteLattice/Basic.lean:913`), which
takes suprema coordinatewise, and `isLUB_prod`, which says a least upper bound in
a product is a pair of least upper bounds. Together these make
`CompletePartialOrder (α × β)` immediate: each coordinate image of a directed set
is directed, so each coordinate supremum is a least upper bound.

Unlike `ScottHom` and `↓a`, no `dite` is needed — the coordinatewise supremum is
defined for *every* set, and on directed sets it is automatically the least upper
bound. `Prod` is the one construction in this development that Mathlib hands over
essentially complete.

## Isomorphism means order isomorphism

The paper's `≅` between cpos is an isomorphism of cpos. An order isomorphism
between cpos automatically preserves directed suprema — least upper bounds are
defined by the order — so `≃o` is the right rendering and no separate continuity
obligation appears.
-/

namespace ScottDomains

variable {α β γ : Type*}

section ProdCpo

variable [CompletePartialOrder α] [CompletePartialOrder β]

theorem directedOn_fst_image {s : Set (α × β)} (hs : DirectedOn (· ≤ ·) s) :
    DirectedOn (· ≤ ·) (Prod.fst '' s) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  obtain ⟨c, hc, hac, hbc⟩ := hs a ha b hb
  exact ⟨c.1, ⟨c, hc, rfl⟩, hac.1, hbc.1⟩

theorem directedOn_snd_image {s : Set (α × β)} (hs : DirectedOn (· ≤ ·) s) :
    DirectedOn (· ≤ ·) (Prod.snd '' s) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  obtain ⟨c, hc, hac, hbc⟩ := hs a ha b hb
  exact ⟨c.2, ⟨c, hc, rfl⟩, hac.2, hbc.2⟩

/-- **`D × E` is a cpo**, with suprema taken coordinatewise. -/
instance : CompletePartialOrder (α × β) :=
  { (inferInstance : PartialOrder (α × β)), (inferInstance : SupSet (α × β)),
    (inferInstance : OrderBot (α × β)) with
    lubOfDirected := fun s hs => by
      rw [isLUB_prod]
      exact ⟨(directedOn_fst_image hs).isLUB_sSup, (directedOn_snd_image hs).isLUB_sSup⟩ }

end ProdCpo

section Lemma8

variable [CompletePartialOrder α] [CompletePartialOrder β] [CompletePartialOrder γ]

/-- **Lemma 8.1.** `D × E ≅ E × D`. -/
def prodComm : α × β ≃o β × α where
  toFun p := (p.2, p.1)
  invFun p := (p.2, p.1)
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- **Lemma 8.2.** `(D × E) × F ≅ D × (E × F)`. -/
def prodAssoc : (α × β) × γ ≃o α × β × γ where
  toFun p := (p.1.1, p.1.2, p.2)
  invFun p := ((p.1, p.2.1), p.2.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩

/-- The first component of a continuous map into a product. -/
def ScottHom.fstComp (f : ScottHom α (β × γ)) : ScottHom α β :=
  ⟨fun x => (f x).1, f.scottContinuous.comp ScottContinuous.fst⟩

/-- The second component. -/
def ScottHom.sndComp (f : ScottHom α (β × γ)) : ScottHom α γ :=
  ⟨fun x => (f x).2, f.scottContinuous.comp ScottContinuous.snd⟩

/-- Pairing two continuous maps. -/
def ScottHom.pair (g : ScottHom α β) (h : ScottHom α γ) : ScottHom α (β × γ) :=
  ⟨fun x => (g x, h x), g.scottContinuous.prodMk h.scottContinuous⟩

/-- **Lemma 8.3.** `D → (E × F) ≅ (D → E) × (D → F)`: a continuous map into a
product is exactly a pair of continuous maps, and the pointwise order on either
side is the same relation. -/
def scottHomProd : ScottHom α (β × γ) ≃o ScottHom α β × ScottHom α γ where
  toFun f := (f.fstComp, f.sndComp)
  invFun p := p.1.pair p.2
  left_inv _ := by ext x <;> rfl
  right_inv _ := rfl
  map_rel_iff' := by
    intro f g
    constructor
    · rintro ⟨h₁, h₂⟩ x
      exact ⟨h₁ x, h₂ x⟩
    · intro h
      exact ⟨fun x => (h x).1, fun x => (h x).2⟩

end Lemma8

end ScottDomains
