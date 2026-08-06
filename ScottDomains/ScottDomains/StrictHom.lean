import ScottDomains.ScottHom

/-!
# The strict function space `D →⊥ E`

Gunter & Scott, *Semantic Domains*, §2.1:

> A function `f : D → E` is said to be **strict** if `f(⊥) = ⊥`. … the set of
> strict continuous functions `D →⊥ E` is also a cpo.

Lemma 9 quantifies over this space throughout, and §3.1's `strict` operator is a
projection onto it.

## It needs no case split

Every other subtype-of-a-cpo in this development had to branch, because the
obvious supremum could leave the subtype. Strictness does not have that problem:
for **any** set `s` of strict functions, `sSup s` is strict, whichever branch
`ScottHom`'s own `sSup` takes.

* If the pointwise supremum is continuous, then `(sSup s) ⊥` is the supremum of
  `{f ⊥ | f ∈ s}`, a subset of `{⊥}`, which is `⊥`.
* Otherwise `sSup s` is the constant-`⊥` function, which is strict outright.

So `D →⊥ E` joins `im(p)` and `D × E` as a construction whose supremum is
correct by construction rather than by hypothesis.
-/

namespace ScottDomains

variable {α β : Type*}

section Bot

variable [CompletePartialOrder β]

/-- A set whose members are all `⊥` has supremum `⊥` — including the empty set,
whose supremum is a least element. -/
theorem sSup_eq_bot_of_forall_eq_bot {t : Set β} (h : ∀ b ∈ t, b = ⊥) : sSup t = ⊥ := by
  have hdir : DirectedOn (· ≤ ·) t := by
    intro a ha b hb
    exact ⟨a, ha, le_rfl, le_of_eq ((h b hb).trans (h a ha).symm)⟩
  refine hdir.isLUB_sSup.unique ⟨fun b hb => le_of_eq (h b hb), fun _ _ => bot_le⟩

end Bot

section StrictHom

variable [Preorder α] [OrderBot α] [CompletePartialOrder β]

/-- `f` is **strict**: it preserves `⊥`. -/
def IsStrict (f : ScottHom α β) : Prop := f ⊥ = ⊥

/-- The strict continuous functions `D →⊥ E`. An `abbrev` rather than a `def` so
that the subtype's own order instance and `.val` projection remain available. -/
abbrev StrictHom (α β : Type*) [Preorder α] [OrderBot α] [CompletePartialOrder β] :=
  {f : ScottHom α β // IsStrict f}

/-- The constant-`⊥` function is strict. -/
theorem isStrict_const_bot : IsStrict (ScottHom.const ⊥ : ScottHom α β) := rfl

/-- **Suprema of strict functions are strict**, for every set — the two branches
of `ScottHom`'s `sSup` are both strict, so no hypothesis is needed. -/
theorem isStrict_sSup {s : Set (ScottHom α β)} (hs : ∀ f ∈ s, IsStrict f) :
    IsStrict (sSup s) := by
  classical
  by_cases h : ScottContinuous fun x => sSup ((fun f : ScottHom α β => f x) '' s)
  · show (sSup s) ⊥ = ⊥
    rw [ScottHom.coe_sSup_of_continuous h ⊥]
    refine sSup_eq_bot_of_forall_eq_bot ?_
    rintro _ ⟨f, hf, rfl⟩
    exact hs f hf
  · show (sSup s) ⊥ = ⊥
    rw [ScottHom.sSup_eq_const_bot h]
    rfl

/-- **`D →⊥ E` is a cpo.** Suprema are those of `D → E`, which stay strict by
`isStrict_sSup`, so the construction needs no case split of its own. -/
@[reducible] noncomputable def strictHomCpo : CompletePartialOrder (StrictHom α β) :=
  { (inferInstance : PartialOrder (StrictHom α β)) with
    sSup := fun s => ⟨sSup (Subtype.val '' s), isStrict_sSup (by rintro _ ⟨f, _, rfl⟩; exact f.2)⟩
    bot := ⟨ScottHom.const ⊥, isStrict_const_bot⟩
    bot_le := fun f x => by
      show (ScottHom.const ⊥ : ScottHom α β) x ≤ f.val x
      exact bot_le
    lubOfDirected := fun s hs => by
      have hdir : DirectedOn (· ≤ ·) (Subtype.val '' s) := by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        obtain ⟨c, hc, hac, hbc⟩ := hs a ha b hb
        exact ⟨c.val, ⟨c, hc, rfl⟩, hac, hbc⟩
      constructor
      · intro f hf
        show f.val ≤ sSup (Subtype.val '' s)
        exact hdir.le_sSup ⟨f, hf, rfl⟩
      · intro u hu
        show sSup (Subtype.val '' s) ≤ u.val
        refine hdir.sSup_le ?_
        rintro _ ⟨f, hf, rfl⟩
        exact hu hf }

end StrictHom

end ScottDomains
