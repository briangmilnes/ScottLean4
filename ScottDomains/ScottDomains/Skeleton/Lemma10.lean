import ScottDomains.Smash
import ScottDomains.Lift
import ScottDomains.StrictHom
import ScottDomains.Product
import ScottDomains.FunctionSpaceCountable

/-!
# Lemma 10: bounded completeness is closed under the operators

Gunter & Scott, *Semantic Domains*, §4.5:

> **Lemma 10** If `D` and `E` are bounded complete domains then so are the cpo's
> `D → E`, `D →⊥ E`, `D × E`, `D ⊗ E`, `D + E`, `D⊥`.

The `D → E` conjunct is **already proved** — it is Theorem 7's bounded-complete
half (`ScottHom`'s `BoundedComplete` instance, r0007) — so it is not restated
here. The remaining conjuncts are one statement each so they can be discharged
independently.

## Status

`lem10_prod`, `lem10_lift` and `lem10_strict` are proved. `lem10_smash` is
**refutable as stated**, and `lem10_smash_refuted` at the end of this file proves
it: `smashSup` (in `Smash.lean`) branches its `dite` on *directedness* of the
base, so on a bounded but non-directed set `sSup` returns the adjoined bottom
instead of the least upper bound. The paper's mathematics is fine — `D ⊗ E` is
bounded complete — but the Lean rendering of `sSup` has to branch on the
condition that makes the coordinatewise supremum correct, which is that it lands
in `NonBotPair`, not on directedness. `ScottHom.lean`'s module docstring records
having hit and fixed the identical defect in the function space. The repair is a
change to the shared module `Smash.lean` and is written out in `lem10_smash`'s
docstring below.

**Owned by agent1.** No other file's declarations are edited when these are
proved.
-/

namespace ScottDomains

variable {α β : Type*} [CompletePartialOrder α] [CompletePartialOrder β]

section Prod

/-- The first-coordinate image of a set bounded above is bounded above. -/
theorem bddAbove_fst_image {s : Set (α × β)} (hs : BddAbove s) : BddAbove (Prod.fst '' s) := by
  obtain ⟨u, hu⟩ := hs
  exact ⟨u.1, by rintro _ ⟨p, hp, rfl⟩; exact (hu hp).1⟩

/-- The second-coordinate image of a set bounded above is bounded above. -/
theorem bddAbove_snd_image {s : Set (α × β)} (hs : BddAbove s) : BddAbove (Prod.snd '' s) := by
  obtain ⟨u, hu⟩ := hs
  exact ⟨u.2, by rintro _ ⟨p, hp, rfl⟩; exact (hu hp).2⟩

/-- **Lemma 10, `D × E`.** Suprema in the product cpo are coordinatewise
(`Prod.supSet`), and `isLUB_prod` says a least upper bound in a product is a pair
of least upper bounds. Boundedness passes to each coordinate image, so each
coordinate supremum is a least upper bound by bounded completeness of the factor.
No case split — unlike `ScottHom`, `WithBot` and `Smash`, the product's `sSup` is
correct on every set on which the factors' `sSup` is. -/
theorem lem10_prod [Domain α] [BoundedComplete α] [Domain β] [BoundedComplete β] :
    BoundedComplete (α × β) where
  isLUB_sSup_of_bddAbove s hs := by
    have hsup : (sSup s : α × β) = (sSup (Prod.fst '' s), sSup (Prod.snd '' s)) := rfl
    rw [isLUB_prod, hsup]
    exact ⟨isLUB_sSup_of_bddAbove (bddAbove_fst_image hs),
      isLUB_sSup_of_bddAbove (bddAbove_snd_image hs)⟩

end Prod

section Smash

/-- `smashSup` returns the adjoined bottom on **every** set whose base is not
directed, bounded or not — its `dite` guard is
`(smashBase s).Nonempty ∧ DirectedOn (· ≤ ·) (smashBase s)`. -/
theorem smashSup_of_not_directedOn {s : Set (Smash α β)}
    (h : ¬ DirectedOn (· ≤ ·) (smashBase s)) : smashSup s = ⊥ := by
  classical
  have hneg : ¬ ((smashBase s).Nonempty ∧ DirectedOn (· ≤ ·) (smashBase s)) := fun hc => h hc.2
  simp only [smashSup, dif_neg hneg]

/-- **The obstacle to `lem10_smash`, stated and checked.** For a set with a
nonempty, non-directed base, `sSup` is the adjoined bottom, which is not even an
upper bound of the set — so `IsLUB s (sSup s)` is refutable. Nothing here assumes
`s` is bounded above, so `BoundedComplete (Smash α β)` holds only if every
bounded subset of `D ⊗ E` has directed base, which fails as soon as `D` has two
incomparable elements with a common upper bound.

Concretely: take `D = 𝒫{0,1}` ordered by inclusion (a finite lattice, hence a
bounded complete domain — every element compact) and `E = Prop`. Then
`s = {↑({0}, True), ↑({1}, True)} ⊆ D ⊗ E` is bounded above by `↑({0,1}, True)`
and its base is not directed, so `sSup s = ⊥` while the least upper bound is
`↑({0,1}, True)`. -/
theorem not_isLUB_sSup_of_not_directedOn_smashBase {s : Set (Smash α β)}
    (hne : (smashBase s).Nonempty) (h : ¬ DirectedOn (· ≤ ·) (smashBase s)) :
    ¬ IsLUB s (sSup s) := by
  obtain ⟨q, hq⟩ := hne
  intro hlub
  have hle : (↑q : Smash α β) ≤ sSup s := hlub.1 (coe_mem_of_mem_smashBase hq)
  rw [show (sSup s : Smash α β) = smashSup s from rfl, smashSup_of_not_directedOn h] at hle
  exact WithBot.not_coe_le_bot q hle

/-- **Lemma 10, `D ⊗ E`.** Not proved: false as stated against the current
`smashSup`, by `not_isLUB_sSup_of_not_directedOn_smashBase` above.

`ScottHom`'s module docstring already names the defect and avoids it there:
"Branching on directedness instead — as an earlier version of this file did —
makes `BoundedComplete (ScottHom α β)` false as stated, because a bounded set of
functions need not be directed and `sSup` would return the junk value on it."
`smashSup` branches on directedness, so it has exactly that defect.

The repair is in `Smash.lean` (a shared module, so it is reported rather than
made): branch on the condition that actually makes the coordinatewise supremum
the right answer — that it lies in `NonBotPair` — instead of on directedness,

    noncomputable def smashSup (s : Set (Smash α β)) : Smash α β :=
      if h : (sSup (Subtype.val '' smashBase s)).1 ≠ ⊥ ∧
             (sSup (Subtype.val '' smashBase s)).2 ≠ ⊥ then ↑(⟨_, h⟩ : NonBotPair α β) else ⊥

which is strictly more permissive and agrees with the present definition on
nonempty directed bases (`sSup_ne_bot_of_nonempty` discharges the new guard) and
on empty bases (`sSup ∅ = (⊥, ⊥)`, so the new guard fails and the value is still
`⊥`). With that definition the bounded case goes through: `lem10_prod` above makes
`sSup (Subtype.val '' smashBase s)` the least upper bound of the base's image, and
a member of a nonempty base has both coordinates non-`⊥` below it. -/
theorem lem10_smash [Domain α] [BoundedComplete α] [Domain β] [BoundedComplete β] :
    BoundedComplete (Smash α β) := by
  sorry

end Smash

/-!
## The refutation, checked by the kernel

`lem10_smash_refuted` below derives `False` from the *statement* of `lem10_smash`
(taken as a hypothesis, at universe `Type`), so the `sorry` above is not merely
unfinished — it cannot be finished while `smashSup` branches on directedness.

The witness is `D = Prop × Prop`, `E = Prop`. `Prop × Prop` is a bounded complete
domain: every element is compact (`isCompactElement_prod` over
`isCompactElement_prop`), and `BoundedComplete (Prop × Prop)` is `lem10_prod`.
Unlike `Prop` itself it is not a chain — `(True, False)` and `(False, True)` are
incomparable with common upper bound `(True, True)` — which is exactly what the
smash product's `sSup` mishandles.
-/

section Refutation

/-- A pair is compact when both coordinates are: take a witness in each coordinate
image of the directed set, then spend directedness once to merge the two
witnesses into a single member above both. -/
theorem isCompactElement_prod {x : α × β} (h₁ : IsCompactElement x.1)
    (h₂ : IsCompactElement x.2) : IsCompactElement x := by
  intro s u hne hd hlub hxu
  rw [isLUB_prod] at hlub
  obtain ⟨_, ⟨p, hp, rfl⟩, hxp⟩ :=
    h₁ (Prod.fst '' s) u.1 (hne.image _) (directedOn_fst_image hd) hlub.1 hxu.1
  obtain ⟨_, ⟨r, hr, rfl⟩, hxr⟩ :=
    h₂ (Prod.snd '' s) u.2 (hne.image _) (directedOn_snd_image hd) hlub.2 hxu.2
  obtain ⟨c, hc, hpc, hrc⟩ := hd p hp r hr
  exact ⟨c, hc, hxp.trans hpc.1, hxr.trans hrc.2⟩

/-- `Prop × Prop` is a domain: all four elements are compact, so algebraicity is
`isAlgebraic_of_forall_isCompactElement`, and the type is countable. -/
theorem domain_prop_prod : Domain (Prop × Prop) where
  __ := isAlgebraic_of_forall_isCompactElement fun x =>
    isCompactElement_prod (isCompactElement_prop x.1) (isCompactElement_prop x.2)
  countable_compacts := (compacts (Prop × Prop)).to_countable

/-- `((True, False), True)` — a non-bottom pair of `(Prop × Prop) ⊗ Prop`. -/
def cex₁ : NonBotPair (Prop × Prop) Prop :=
  ⟨((True, False), True), by simp [Prod.ext_iff], by simp⟩

/-- `((False, True), True)` — incomparable with `cex₁`. -/
def cex₂ : NonBotPair (Prop × Prop) Prop :=
  ⟨((False, True), True), by simp [Prod.ext_iff], by simp⟩

/-- `((True, True), True)` — an upper bound of both. -/
def cex₃ : NonBotPair (Prop × Prop) Prop :=
  ⟨((True, True), True), by simp [Prod.ext_iff], by simp⟩

/-- The two-element set that is bounded above but whose base is not directed. -/
def cexSet : Set (Smash (Prop × Prop) Prop) := {(↑cex₁ : Smash (Prop × Prop) Prop), ↑cex₂}

theorem cex₁_mem_smashBase : cex₁ ∈ smashBase cexSet := Or.inl rfl

theorem cex₂_mem_smashBase : cex₂ ∈ smashBase cexSet := Or.inr rfl

theorem bddAbove_cexSet : BddAbove cexSet := by
  refine ⟨↑cex₃, ?_⟩
  -- every component of `cex₃` is `True`, so each obligation is `_ → True`.
  rintro x (rfl | rfl) <;>
    exact WithBot.coe_le_coe.mpr ⟨⟨fun _ => trivial, fun _ => trivial⟩, fun _ => trivial⟩

/-- The base of `cexSet` is `{cex₁, cex₂}`, and neither is above the other, so no
member of the base bounds both. -/
theorem not_directedOn_smashBase_cexSet : ¬ DirectedOn (· ≤ ·) (smashBase cexSet) := by
  intro hd
  obtain ⟨c, hc, h₁, h₂⟩ := hd cex₁ cex₁_mem_smashBase cex₂ cex₂_mem_smashBase
  have hcc : c = cex₁ ∨ c = cex₂ := by
    rcases hc with hc | hc
    · exact Or.inl (WithBot.coe_inj.mp hc)
    · exact Or.inr (WithBot.coe_inj.mp (Set.mem_singleton_iff.mp hc))
  rcases hcc with rfl | rfl
  · exact h₂.1.2 trivial
  · exact h₁.1.1 trivial

/-- **`D ⊗ E` is not bounded complete as `smashSup` currently stands**, for the
bounded complete domains `D = Prop × Prop` and `E = Prop`. -/
theorem not_boundedComplete_smash_cex : ¬ BoundedComplete (Smash (Prop × Prop) Prop) := by
  intro hbc
  exact not_isLUB_sSup_of_not_directedOn_smashBase ⟨cex₁, cex₁_mem_smashBase⟩
    not_directedOn_smashBase_cexSet
    (hbc.isLUB_sSup_of_bddAbove cexSet bddAbove_cexSet)

/-- **`lem10_smash` is refutable, not merely open.** Its statement, assumed as the
hypothesis `h`, instantiates at `D = Prop × Prop`, `E = Prop` — both bounded
complete domains — and contradicts `not_boundedComplete_smash_cex`. -/
theorem lem10_smash_refuted
    (h : ∀ {α β : Type} [CompletePartialOrder α] [CompletePartialOrder β] [Domain α]
      [BoundedComplete α] [Domain β] [BoundedComplete β], BoundedComplete (Smash α β)) :
    False := by
  haveI : Domain (Prop × Prop) := domain_prop_prod
  haveI : BoundedComplete (Prop × Prop) := lem10_prod
  exact not_boundedComplete_smash_cex (h (α := Prop × Prop) (β := Prop))

/- The hypothesis of `lem10_smash_refuted` is `lem10_smash`'s statement verbatim,
specialized to `Type`. Checked by elaborating

    example : False := lem10_smash_refuted (fun {_ _} _ _ _ _ _ _ => lem10_smash)

which typechecks. It is not kept in the file: it is a proof of `False` that leans
on the `sorry` in `lem10_smash`, so committing it would put a sorry-backed `False`
into the environment for any later file to pick up. -/

end Refutation

section Lift

/-- The base of a set bounded above by a *coercion* is bounded above. The
hypothesis has to name the bound in `D`, not merely in `D⊥`: an upper bound of `s`
that is the adjoined bottom bounds nothing in the base. -/
theorem bddAbove_liftBase {s : Set (WithBot α)} {b : α} (hb : (↑b : WithBot α) ∈ upperBounds s) :
    BddAbove (liftBase s) :=
  ⟨b, fun _a ha => WithBot.coe_le_coe.mp (hb (coe_mem_of_mem_liftBase ha))⟩

/-- An upper bound of a set whose base is nonempty is a coercion, never the
adjoined bottom — `WithBot.not_coe_le_bot`. -/
theorem exists_coe_of_mem_upperBounds {s : Set (WithBot α)} (hne : (liftBase s).Nonempty)
    {u : WithBot α} (hu : u ∈ upperBounds s) : ∃ b : α, u = ↑b := by
  obtain ⟨a₀, ha₀⟩ := hne
  induction u using WithBot.recBotCoe with
  | bot => exact absurd (hu (coe_mem_of_mem_liftBase ha₀)) (WithBot.not_coe_le_bot a₀)
  | coe b => exact ⟨b, rfl⟩

/-- **Lemma 10, `D⊥`.** `liftSup` branches on nonemptiness of the base, not on
directedness, so the branch a *bounded* set takes is already the correct one — the
point `ScottHom`'s module docstring makes about splitting on continuity rather
than directedness. On the nonempty branch the value is `↑(sSup (liftBase s))`, and
bounded completeness of `D` makes that inner supremum a least upper bound; on the
empty branch `s ⊆ {⊥}` and the value is `⊥`. -/
theorem lem10_lift [Domain α] [BoundedComplete α] : BoundedComplete (WithBot α) where
  isLUB_sSup_of_bddAbove s hs := by
    show IsLUB s (liftSup s)
    by_cases hne : (liftBase s).Nonempty
    · obtain ⟨u, hu⟩ := hs
      obtain ⟨b, rfl⟩ := exists_coe_of_mem_upperBounds hne hu
      have hlub : IsLUB (liftBase s) (sSup (liftBase s)) :=
        isLUB_sSup_of_bddAbove (bddAbove_liftBase hu)
      rw [liftSup_of_nonempty hne]
      constructor
      · intro x hx
        induction x using WithBot.recBotCoe with
        | bot => exact bot_le
        | coe a => exact WithBot.coe_le_coe.mpr (hlub.1 hx)
      · intro v hv
        obtain ⟨c, rfl⟩ := exists_coe_of_mem_upperBounds hne hv
        exact WithBot.coe_le_coe.mpr
          (hlub.2 fun a ha => WithBot.coe_le_coe.mp (hv (coe_mem_of_mem_liftBase ha)))
    · rw [liftSup_of_empty hne]
      constructor
      · intro x hx
        induction x using WithBot.recBotCoe with
        | bot => exact le_rfl
        | coe a => exact absurd ⟨a, hx⟩ hne
      · intro _ _
        exact bot_le

end Lift

section Strict

/-- **Lemma 10, `D →⊥ E`.** `StrictHom α β` is a subtype of `ScottHom α β` whose
`sSup` is the ambient one — `isStrict_sSup` shows strictness survives *every*
supremum, so there is no branch to get wrong. Bounded completeness therefore
transports along the subtype: a bound in `D →⊥ E` gives a bound on the image in
`D → E`, `ScottHom`'s own `BoundedComplete` instance (Theorem 7's first sentence)
supplies the least upper bound there, and the order on the subtype is the ambient
order restricted, so the same element is least upper bound of `s`. -/
theorem lem10_strict [Domain α] [BoundedComplete α] [Domain β] [BoundedComplete β] :
    BoundedComplete (StrictHom α β) where
  isLUB_sSup_of_bddAbove s hs := by
    obtain ⟨u, hu⟩ := hs
    have hb : BddAbove (Subtype.val '' s) := ⟨u.val, by rintro _ ⟨f, hf, rfl⟩; exact hu hf⟩
    have hlub : IsLUB (Subtype.val '' s) (sSup (Subtype.val '' s)) :=
      isLUB_sSup_of_bddAbove hb
    constructor
    · intro f hf
      show f.val ≤ sSup (Subtype.val '' s)
      exact hlub.1 ⟨f, hf, rfl⟩
    · intro v hv
      show sSup (Subtype.val '' s) ≤ v.val
      exact hlub.2 (by rintro _ ⟨f, hf, rfl⟩; exact hv hf)

end Strict

/- Axiom audit, by `#print axioms` (run, then removed so the build emits no `info`
lines): `lem10_prod` depends on `[propext, Quot.sound]`; `lem10_lift`,
`lem10_strict` and `lem10_smash_refuted` on `[propext, Classical.choice,
Quot.sound]` — `Classical.choice` entering through the `dite` in `liftSup` and in
`ScottHom`'s `sSup`. None depends on `sorryAx`. -/

end ScottDomains
