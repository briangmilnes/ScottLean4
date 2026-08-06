import ScottDomains.Product

/-!
# Lemma 8, part 4: currying

Gunter & Scott, *Semantic Domains*, §4.5, Lemma 8.4:

> `D → (E → F) ≅ (D × E) → F`

This is the one part of Lemma 8 that is not a rearrangement of the same data. It
turns on the equivalence between **joint** and **separate** Scott continuity, and
that equivalence is where the work is.

## Why joint continuity is not free

Currying a jointly continuous `f : D × E → F` is easy in each direction
separately: fixing `x`, the map `y ↦ f (x, y)` is continuous because
`y ↦ (x, y)` carries a directed set to a directed set with the expected least
upper bound.

Going the other way is the hard direction. Given `g : D → (E → F)` continuous
into the function space, uncurrying needs
`g (⨆ fst s) (⨆ snd s) ⊑ u` from `u` bounding `{g q.1 q.2 | q ∈ s}` — and the two
suprema are taken over *different* projections of the same directed set. The
argument peels them one at a time (continuity of `g`, then of `g x`), reaching a
goal about `g x y` for `x` and `y` drawn from different members of `s`; the
directedness of `s` in the **product** is what supplies a single member above
both.

`isLUB_eval_image_of_isLUB` is the bridge that makes the first peel possible: a
least upper bound in `D → E` is a least upper bound pointwise.
-/

namespace ScottDomains

variable {α β γ : Type*}

section Curry

variable [CompletePartialOrder α] [CompletePartialOrder β] [CompletePartialOrder γ]

/-- For fixed `x`, pairing with `x` carries directed sets to directed sets with
the expected least upper bound. -/
theorem scottContinuous_pairLeft (x : α) : ScottContinuous fun y : β => (x, y) := by
  intro s hne _ b hb
  have hfst : Prod.fst '' ((fun y : β => (x, y)) '' s) = {x} := by
    obtain ⟨y₀, hy₀⟩ := hne
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨(x, y₀), ⟨y₀, hy₀, rfl⟩, rfl⟩, ?_⟩
    rintro _ ⟨_, ⟨y, _, rfl⟩, rfl⟩
    rfl
  have hsnd : Prod.snd '' ((fun y : β => (x, y)) '' s) = s := by
    ext z
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact hy
    · intro hz
      exact ⟨(x, z), ⟨z, hz, rfl⟩, rfl⟩
  rw [isLUB_prod, hfst, hsnd]
  exact ⟨isLUB_singleton, hb⟩

/-- Fixing the first argument of a jointly continuous map. -/
def ScottHom.curryApply (f : ScottHom (α × β) γ) (x : α) : ScottHom β γ :=
  ⟨fun y => f (x, y), (scottContinuous_pairLeft x).comp f.scottContinuous⟩

/-- **Currying**: a jointly continuous map curries to a continuous map into the
function space. The outer continuity is the pointwise one, and its
least-upper-bound half comes from joint continuity applied at each fixed `y`. -/
def ScottHom.curry (f : ScottHom (α × β) γ) : ScottHom α (ScottHom β γ) :=
  ⟨f.curryApply, by
    intro s hne hs a ha
    constructor
    · rintro _ ⟨x, hx, rfl⟩ y
      exact f.monotone ⟨ha.1 hx, le_rfl⟩
    · intro u hu y
      have hfst : Prod.fst '' ((fun x : α => (x, y)) '' s) = s := by
        ext z
        constructor
        · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
          exact hx
        · intro hz
          exact ⟨(z, y), ⟨z, hz, rfl⟩, rfl⟩
      have hsnd : Prod.snd '' ((fun x : α => (x, y)) '' s) = {y} := by
        obtain ⟨x₀, hx₀⟩ := hne
        refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨(x₀, y), ⟨x₀, hx₀, rfl⟩, rfl⟩, ?_⟩
        rintro _ ⟨_, ⟨x, _, rfl⟩, rfl⟩
        rfl
      have hpair : IsLUB ((fun x : α => (x, y)) '' s) (a, y) := by
        rw [isLUB_prod, hfst, hsnd]
        exact ⟨ha, isLUB_singleton⟩
      have hdir : DirectedOn (· ≤ ·) ((fun x : α => (x, y)) '' s) := by
        rintro _ ⟨x₁, h₁, rfl⟩ _ ⟨x₂, h₂, rfl⟩
        obtain ⟨x₃, h₃, hle₁, hle₂⟩ := hs x₁ h₁ x₂ h₂
        exact ⟨(x₃, y), ⟨x₃, h₃, rfl⟩, ⟨hle₁, le_rfl⟩, ⟨hle₂, le_rfl⟩⟩
      obtain ⟨x₀, hx₀⟩ := hne
      have hnepair : ((fun x : α => (x, y)) '' s).Nonempty := ⟨(x₀, y), ⟨x₀, hx₀, rfl⟩⟩
      refine (f.scottContinuous hnepair hdir hpair).2 ?_
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact hu ⟨x, hx, rfl⟩ y⟩

/-- **Uncurrying**: a continuous map into the function space uncurries to a
jointly continuous map. This is the direction that needs directedness of `s` in
the *product*. -/
def ScottHom.uncurry (g : ScottHom α (ScottHom β γ)) : ScottHom (α × β) γ :=
  ⟨fun p => g p.1 p.2, by
    intro s hne hs p hp
    rw [isLUB_prod] at hp
    obtain ⟨hfst, hsnd⟩ := hp
    have hdfst := directedOn_fst_image hs
    have hdsnd := directedOn_snd_image hs
    constructor
    · rintro _ ⟨q, hq, rfl⟩
      exact le_trans (g.monotone (hfst.1 ⟨q, hq, rfl⟩) q.2)
        ((g p.1).monotone (hsnd.1 ⟨q, hq, rfl⟩))
    · intro u hu
      -- Peel the first coordinate: a least upper bound in `D → E` is one pointwise.
      have hg : IsLUB (⇑g '' (Prod.fst '' s)) (g p.1) :=
        g.scottContinuous (hne.image _) hdfst hfst
      have hdg : DirectedOn (· ≤ ·) (⇑g '' (Prod.fst '' s)) := by
        rintro _ ⟨x₁, h₁, rfl⟩ _ ⟨x₂, h₂, rfl⟩
        obtain ⟨x₃, h₃, hle₁, hle₂⟩ := hdfst x₁ h₁ x₂ h₂
        exact ⟨g x₃, ⟨x₃, h₃, rfl⟩, g.monotone hle₁, g.monotone hle₂⟩
      refine (ScottHom.isLUB_eval_image_of_isLUB hdg hg p.2).2 ?_
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      -- Peel the second: `g x` is continuous.
      refine ((g x).scottContinuous (hne.image _) hdsnd hsnd).2 ?_
      rintro _ ⟨y, hy, rfl⟩
      -- `x` and `y` come from different members of `s`; directedness merges them.
      obtain ⟨q₁, hq₁, rfl⟩ := hx
      obtain ⟨q₂, hq₂, rfl⟩ := hy
      obtain ⟨q₃, hq₃, hle₁, hle₂⟩ := hs q₁ hq₁ q₂ hq₂
      exact le_trans (le_trans (g.monotone hle₁.1 q₂.2)
        ((g q₃.1).monotone hle₂.2)) (hu ⟨q₃, hq₃, rfl⟩)⟩

/-- **Lemma 8.4.** `D → (E → F) ≅ (D × E) → F`. -/
def scottHomCurry : ScottHom α (ScottHom β γ) ≃o ScottHom (α × β) γ where
  toFun := ScottHom.uncurry
  invFun := ScottHom.curry
  left_inv _ := by ext x y; rfl
  right_inv _ := by ext p; rfl
  map_rel_iff' := by
    intro g h
    constructor
    · intro hle x y
      exact hle (x, y)
    · intro hle p
      exact hle p.1 p.2

end Curry

end ScottDomains
