import ScottDomains.StrictHom
import ScottDomains.Lift

/-!
# Lemma 9, part 6: lifting is left adjoint to the forgetful functor

Gunter & Scott, *Semantic Domains*, Lemma 9.6:

> `D⊥ ◦→ E ≅ D → E`.

Read categorically this is an adjunction: `(·)⊥` is left adjoint to the functor
that forgets strictness, from pointed cpo's and strict continuous maps to cpo's
and continuous maps. The unit is `up : D → D⊥` — Mathlib's coercion
`(↑) : α → WithBot α` — and the counit direction is the *strict extension* `g†`
of §4.4, which sends the adjoined bottom to `⊥` and agrees with `g` elsewhere.

## The two maps and what each costs

`restrictToBase f = f ∘ up` needs the coercion to be Scott continuous
(`scottContinuous_coe`). That is one argument: an upper bound of a nonempty set
of coercions cannot be the adjoined bottom, so it is again a coercion, and
`WithBot.coe_le_coe` transports the least-upper-bound condition.

`liftExtendFun g = g†` is the direction with content
(`scottContinuous_liftExtendFun`). A directed `s ⊆ D⊥` splits on its least upper
bound. If that bound is `⊥` then `s ⊆ {⊥}` and both sides are `⊥`. Otherwise the
bound is `↑a`, and `liftBase s` — the part of `s` above the adjoined bottom,
already shown directed in `Lift.lean` — is **nonempty**, because an empty base
would make `⊥` an upper bound of `s` and contradict `WithBot.not_coe_le_bot`.
Nonemptiness is what lets `g`'s own continuity be applied, and the adjoined
bottom contributes only `⊥` to the image, which no least upper bound notices.

`left_inv` is where strictness is spent: `g†` agrees with `f` at `↑a` by
construction and at `⊥` only because `f ⊥ = ⊥`. Dropping strictness from the
left-hand side would break exactly this equation — which is the content of the
adjunction.
-/

namespace ScottDomains.Isomorphism

open ScottDomains

variable {α β : Type*} [CompletePartialOrder α] [CompletePartialOrder β]

/-- **`up : D → D⊥` is Scott continuous.** An upper bound of a nonempty set of
coercions is not the adjoined bottom, so it is a coercion and
`WithBot.coe_le_coe` applies. -/
theorem scottContinuous_coe : ScottContinuous ((↑) : α → WithBot α) := by
  intro s hne hs a ha
  constructor
  · rintro _ ⟨x, hx, rfl⟩
    exact WithBot.coe_le_coe.mpr (ha.1 hx)
  · intro u hu
    obtain ⟨x₀, hx₀⟩ := hne
    induction u using WithBot.recBotCoe with
    | bot => exact absurd (hu ⟨x₀, hx₀, rfl⟩) (WithBot.not_coe_le_bot x₀)
    | coe b =>
      refine WithBot.coe_le_coe.mpr (ha.2 ?_)
      intro x hx
      exact WithBot.coe_le_coe.mp (hu ⟨x, hx, rfl⟩)

/-- The **strict extension** `g†` of `g : D → E`: `⊥` at the adjoined bottom and
`g` on the coercions. -/
def liftExtendFun (g : ScottHom α β) : WithBot α → β :=
  fun x => WithBot.recBotCoe (C := fun _ => β) ⊥ (fun a => g a) x

@[simp] theorem liftExtendFun_bot (g : ScottHom α β) : liftExtendFun g ⊥ = ⊥ := rfl

@[simp] theorem liftExtendFun_coe (g : ScottHom α β) (a : α) :
    liftExtendFun g (↑a : WithBot α) = g a := rfl

/-- **`g†` is Scott continuous.** The case split is on the least upper bound of
the directed set: `⊥` forces the set into `{⊥}`, and a coercion `↑a` forces
`liftBase s` to be nonempty, which is what `g`'s continuity needs. -/
theorem scottContinuous_liftExtendFun (g : ScottHom α β) :
    ScottContinuous (liftExtendFun g) := by
  intro s hne hs x hx
  induction x using WithBot.recBotCoe with
  | bot =>
    have hall : ∀ z ∈ s, z = (⊥ : WithBot α) := fun z hz => le_bot_iff.mp (hx.1 hz)
    constructor
    · rintro _ ⟨z, hz, rfl⟩
      exact le_of_eq (congrArg (liftExtendFun g) (hall z hz))
    · intro u hu
      obtain ⟨z₀, hz₀⟩ := hne
      have h := hu ⟨z₀, hz₀, rfl⟩
      rwa [hall z₀ hz₀] at h
  | coe a =>
    have hdir : DirectedOn (· ≤ ·) (liftBase s) := directedOn_liftBase hs
    have hne' : (liftBase s).Nonempty := by
      by_contra hempty
      have hub : (⊥ : WithBot α) ∈ upperBounds s := by
        intro z hz
        induction z using WithBot.recBotCoe with
        | bot => exact le_rfl
        | coe b => exact absurd ⟨b, hz⟩ hempty
      exact WithBot.not_coe_le_bot a (hx.2 hub)
    have hlub : IsLUB (liftBase s) a := by
      constructor
      · intro b hb
        exact WithBot.coe_le_coe.mp (hx.1 (coe_mem_of_mem_liftBase hb))
      · intro c hc
        refine WithBot.coe_le_coe.mp (hx.2 ?_)
        intro z hz
        induction z using WithBot.recBotCoe with
        | bot => exact bot_le
        | coe b => exact WithBot.coe_le_coe.mpr (hc hz)
    have hg := g.scottContinuous hne' hdir hlub
    constructor
    · rintro _ ⟨z, hz, rfl⟩
      induction z using WithBot.recBotCoe with
      | bot => exact bot_le
      | coe b => exact hg.1 ⟨b, hz, rfl⟩
    · intro u hu
      refine hg.2 ?_
      rintro _ ⟨b, hb, rfl⟩
      exact hu ⟨(↑b : WithBot α), coe_mem_of_mem_liftBase hb, rfl⟩

/-- `g†` bundled as a strict continuous map `D⊥ ◦→ E`. -/
def liftExtend (g : ScottHom α β) : StrictHom (WithBot α) β :=
  ⟨⟨liftExtendFun g, scottContinuous_liftExtendFun g⟩, rfl⟩

/-- Restriction along the unit `up : D → D⊥`. -/
def liftRestrict (f : StrictHom (WithBot α) β) : ScottHom α β :=
  ⟨fun a => f.val (↑a : WithBot α), scottContinuous_coe.comp f.val.scottContinuous⟩

/-- **Lemma 9.6**, as a named map: `D⊥ ◦→ E ≅ D → E`. -/
def liftStrictHomIso : StrictHom (WithBot α) β ≃o ScottHom α β where
  toFun := liftRestrict
  invFun := liftExtend
  left_inv f := by
    refine Subtype.ext (ScottHom.ext ?_)
    intro x
    induction x using WithBot.recBotCoe with
    | bot => exact f.2.symm
    | coe a => rfl
  right_inv g := by
    refine ScottHom.ext ?_
    intro a
    rfl
  map_rel_iff' := by
    intro f g
    constructor
    · intro h x
      induction x using WithBot.recBotCoe with
      | bot => exact le_of_eq (f.2.trans g.2.symm)
      | coe a => exact h a
    · intro h a
      exact h (↑a : WithBot α)

end ScottDomains.Isomorphism
