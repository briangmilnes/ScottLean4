import ScottDomains.Flat
import ScottDomains.Powerdomain.Plotkin
import ScottDomains.Powerdomain.Universal
import ScottDomains.Skeleton.Lemma10
import ScottDomains.Skeleton.Lemma17

/-!
# §6's opening: `(T × T)♮` is not bounded complete

Gunter & Scott, *Semantic Domains*, §6, first paragraph, quoted from a 170 dpi
rendering of the physical page (printed p. 29 — **not** p. 30; p. 30 is §6.1,
Plotkin orders):

> Of the operators that we have discussed so far, only the convex powerdomain
> `(·)♮` does not take bounded complete domains to bounded complete domains. To
> see this in a simple example, consider the finite poset `T × T` and the
> following elements of `P*f(T × T)`:
>
>     u  = {⟨⊥, true⟩, ⟨⊥, false⟩}
>     v  = {⟨true, ⊥⟩, ⟨false, ⊥⟩}
>     u′ = {⟨true, true⟩, ⟨false, false⟩}
>     v′ = {⟨true, false⟩, ⟨false, true⟩}
>
> It is not hard to see that `u′` and `v′` are *minimal* upper bounds for
> `{u, v}` with respect to the ordering `⊢♮`. Hence no *least* upper bound for
> `{u, u′}` exists and `(T × T)♮` is therefore not bounded complete.

This is the negative counterpart of Lemma 13, which `Powerdomain/BoundedComplete.lean`
proves for `D♯` and `D♭`. It had no Lean statement before r0041 for one reason:
`T` did not exist. `ScottDomains.Flat` supplies it as `Flat Bool`.

## Two departures from the printed text, both recorded

1. **`{u, u′}` is a typo for `{u, v}`.** If `u′` is an upper bound of `{u, v}`
   then it is trivially the *least* upper bound of `{u, u′}`, so the printed
   sentence cannot be what is meant; the preceding sentence, about minimal upper
   bounds of `{u, v}`, fixes the intended pair. `not_exists_isLUB` below is
   stated for `{u, v}`.
2. **Minimality is not what the refutation needs.** Two distinct minimal upper
   bounds do rule out a least one *in the pre-order*, but bounded completeness is
   a property of the *ideal completion* `(T × T)♮`, and a least upper bound there
   is an ideal, not a finite set. The argument that transfers is:
   a least upper bound `I` of `{↓u, ↓v}` would contain `u` and `v`, hence — being
   directed — a single `w` above both, and `w` would lie in both `↓u′` and `↓v′`.
   `no_common_refinement` shows no such `w` exists, and it needs no minimality
   claim at all: **one** element of `w` already carries the contradiction.
   `setU'_minimal` proves the paper's minimality claim separately, since it is a
   property the paper asserts.

## The contradiction in one line

Let `b` be any member of such a `w`. Sitting above `u` forces `b`'s second
coordinate to be `true` or `false` — not `⊥`; sitting above `v` forces the same
of the first. Sitting below `u′` forces the two coordinates *equal*; sitting
below `v′` forces them *different*.
-/

namespace ScottDomains.Flat

open ScottDomains

noncomputable section

/-! ## `T × T` and its compact elements -/

/-- `T × T`, the finite poset of §6's counterexample: nine points. -/
abbrev TT : Type := Truth × Truth

/-- `true : T`. -/
def tru : Truth := up true

/-- `false : T`. -/
def fls : Truth := up false

/-- A pair of truth values as a compact element of `T × T`. Total, because both
factors are flat and `K(D × E) = K(D) × K(E)` (`isCompactElement_prod_iff`). -/
def kp (a b : Truth) : ↥(compacts TT) :=
  ⟨(a, b), isCompactElement_prod_iff.mpr ⟨isCompactElement a, isCompactElement b⟩⟩

@[simp] theorem kp_fst (a b : Truth) : ((kp a b : TT)).1 = a := rfl

@[simp] theorem kp_snd (a b : Truth) : ((kp a b : TT)).2 = b := rfl

theorem kp_le {a b c d : Truth} (h₁ : a ≤ c) (h₂ : b ≤ d) : kp a b ≤ kp c d := ⟨h₁, h₂⟩

/-- The order on `K(T × T)` unfolded to its two coordinates. -/
theorem le_coords {k l : ↥(compacts TT)} (h : k ≤ l) :
    (k : TT).1 ≤ (l : TT).1 ∧ (k : TT).2 ≤ (l : TT).2 := h

/-! ## The paper's four sets -/

open Plotkin.FinCompacts in
/-- `u = {⟨⊥, true⟩, ⟨⊥, false⟩}`. -/
def setU : Plotkin.FinCompacts TT := pair (kp ⊥ tru) (kp ⊥ fls)

open Plotkin.FinCompacts in
/-- `v = {⟨true, ⊥⟩, ⟨false, ⊥⟩}`. -/
def setV : Plotkin.FinCompacts TT := pair (kp tru ⊥) (kp fls ⊥)

open Plotkin.FinCompacts in
/-- `u′ = {⟨true, true⟩, ⟨false, false⟩}`. -/
def setU' : Plotkin.FinCompacts TT := pair (kp tru tru) (kp fls fls)

open Plotkin.FinCompacts in
/-- `v′ = {⟨true, false⟩, ⟨false, true⟩}`. -/
def setV' : Plotkin.FinCompacts TT := pair (kp tru fls) (kp fls tru)

/-! ## `u′` and `v′` are upper bounds of `{u, v}`

Four Egli–Milner checks, each a pair of one-element witnesses. In Mathlib's
orientation the paper's `u′ ⊢♮ u` is `u ≤ u′`. -/

theorem setU_le_setU' : setU ≤ setU' := by
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · rcases Plotkin.FinCompacts.mem_pair.mp ha with rfl | rfl
    · exact ⟨kp tru tru, Plotkin.FinCompacts.mem_pair.mpr (Or.inl rfl), kp_le bot_le le_rfl⟩
    · exact ⟨kp fls fls, Plotkin.FinCompacts.mem_pair.mpr (Or.inr rfl), kp_le bot_le le_rfl⟩
  · rcases Plotkin.FinCompacts.mem_pair.mp hb with rfl | rfl
    · exact ⟨kp ⊥ tru, Plotkin.FinCompacts.mem_pair.mpr (Or.inl rfl), kp_le bot_le le_rfl⟩
    · exact ⟨kp ⊥ fls, Plotkin.FinCompacts.mem_pair.mpr (Or.inr rfl), kp_le bot_le le_rfl⟩

theorem setV_le_setU' : setV ≤ setU' := by
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · rcases Plotkin.FinCompacts.mem_pair.mp ha with rfl | rfl
    · exact ⟨kp tru tru, Plotkin.FinCompacts.mem_pair.mpr (Or.inl rfl), kp_le le_rfl bot_le⟩
    · exact ⟨kp fls fls, Plotkin.FinCompacts.mem_pair.mpr (Or.inr rfl), kp_le le_rfl bot_le⟩
  · rcases Plotkin.FinCompacts.mem_pair.mp hb with rfl | rfl
    · exact ⟨kp tru ⊥, Plotkin.FinCompacts.mem_pair.mpr (Or.inl rfl), kp_le le_rfl bot_le⟩
    · exact ⟨kp fls ⊥, Plotkin.FinCompacts.mem_pair.mpr (Or.inr rfl), kp_le le_rfl bot_le⟩

theorem setU_le_setV' : setU ≤ setV' := by
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · rcases Plotkin.FinCompacts.mem_pair.mp ha with rfl | rfl
    · exact ⟨kp fls tru, Plotkin.FinCompacts.mem_pair.mpr (Or.inr rfl), kp_le bot_le le_rfl⟩
    · exact ⟨kp tru fls, Plotkin.FinCompacts.mem_pair.mpr (Or.inl rfl), kp_le bot_le le_rfl⟩
  · rcases Plotkin.FinCompacts.mem_pair.mp hb with rfl | rfl
    · exact ⟨kp ⊥ fls, Plotkin.FinCompacts.mem_pair.mpr (Or.inr rfl), kp_le bot_le le_rfl⟩
    · exact ⟨kp ⊥ tru, Plotkin.FinCompacts.mem_pair.mpr (Or.inl rfl), kp_le bot_le le_rfl⟩

theorem setV_le_setV' : setV ≤ setV' := by
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · rcases Plotkin.FinCompacts.mem_pair.mp ha with rfl | rfl
    · exact ⟨kp tru fls, Plotkin.FinCompacts.mem_pair.mpr (Or.inl rfl), kp_le le_rfl bot_le⟩
    · exact ⟨kp fls tru, Plotkin.FinCompacts.mem_pair.mpr (Or.inr rfl), kp_le le_rfl bot_le⟩
  · rcases Plotkin.FinCompacts.mem_pair.mp hb with rfl | rfl
    · exact ⟨kp tru ⊥, Plotkin.FinCompacts.mem_pair.mpr (Or.inl rfl), kp_le le_rfl bot_le⟩
    · exact ⟨kp fls ⊥, Plotkin.FinCompacts.mem_pair.mpr (Or.inr rfl), kp_le le_rfl bot_le⟩

/-! ## The shape of any common upper bound -/

/-- **Every member of a set above both `u` and `v` has both coordinates
defined.** The Smyth conjunct of `u ≤ w` puts a member of `u` below each member
of `w`, and both members of `u` have second coordinate `true` or `false`; in a
flat order nothing is strictly above those, so the second coordinate of the
member of `w` is that very value. `v` does the same for the first coordinate. -/
theorem exists_up_of_mem {w : Plotkin.FinCompacts TT} (huw : setU ≤ w) (hvw : setV ≤ w)
    {b : ↥(compacts TT)} (hb : b ∈ w) : ∃ p q : Bool, b = kp (up p) (up q) := by
  obtain ⟨a, ha, hab⟩ := huw.2 b hb
  obtain ⟨c, hc, hcb⟩ := hvw.2 b hb
  have hq : ∃ q : Bool, (b : TT).2 = up q := by
    rcases Plotkin.FinCompacts.mem_pair.mp ha with rfl | rfl
    · exact ⟨true, eq_of_up_le (le_coords hab).2⟩
    · exact ⟨false, eq_of_up_le (le_coords hab).2⟩
  have hp : ∃ p : Bool, (b : TT).1 = up p := by
    rcases Plotkin.FinCompacts.mem_pair.mp hc with rfl | rfl
    · exact ⟨true, eq_of_up_le (le_coords hcb).1⟩
    · exact ⟨false, eq_of_up_le (le_coords hcb).1⟩
  obtain ⟨p, hp⟩ := hp
  obtain ⟨q, hq⟩ := hq
  exact ⟨p, q, Subtype.ext (Prod.ext_iff.mpr ⟨hp, hq⟩)⟩

/-- Dominated by a member of `u′`, the two coordinates agree. -/
theorem eq_of_le_mem_setU' {p q : Bool} (h : ∃ d ∈ setU', kp (up p) (up q) ≤ d) : p = q := by
  obtain ⟨d, hd, hbd⟩ := h
  rcases Plotkin.FinCompacts.mem_pair.mp hd with rfl | rfl
  · rw [up_le_up_iff.mp (le_coords hbd).1, up_le_up_iff.mp (le_coords hbd).2]
  · rw [up_le_up_iff.mp (le_coords hbd).1, up_le_up_iff.mp (le_coords hbd).2]

/-- Dominated by a member of `v′`, the two coordinates differ. -/
theorem ne_of_le_mem_setV' {p q : Bool} (h : ∃ e ∈ setV', kp (up p) (up q) ≤ e) : p ≠ q := by
  obtain ⟨e, he, hbe⟩ := h
  rcases Plotkin.FinCompacts.mem_pair.mp he with rfl | rfl
  · rw [up_le_up_iff.mp (le_coords hbe).1, up_le_up_iff.mp (le_coords hbe).2]
    decide
  · rw [up_le_up_iff.mp (le_coords hbe).1, up_le_up_iff.mp (le_coords hbe).2]
    decide

/-- **No finite set refines both `u′` and `v′` while dominating `u` and `v`.**
This is the whole content of §6's counterexample: a single member `b` of such a
`w` has both coordinates defined, equal (from `w ⊑ u′`) and unequal (from
`w ⊑ v′`). -/
theorem no_common_refinement {w : Plotkin.FinCompacts TT}
    (huw : setU ≤ w) (hvw : setV ≤ w) (hwu : w ≤ setU') (hwv : w ≤ setV') : False := by
  obtain ⟨b, hb⟩ := w.nonempty
  obtain ⟨p, q, rfl⟩ := exists_up_of_mem huw hvw hb
  exact ne_of_le_mem_setV' (hwv.1 _ hb) (eq_of_le_mem_setU' (hwu.1 _ hb))

/-! ## The paper's minimality claim

> It is not hard to see that `u′` and `v′` are *minimal* upper bounds for
> `{u, v}` with respect to the ordering `⊢♮`.

Minimality is not what the refutation above consumes (see the module docstring),
but it is a property the paper asserts, so it is proved. `u′` and `v′` are also
incomparable, which is what makes them *two* minimal upper bounds rather than
one. -/

/-- **`u′` is a minimal upper bound of `{u, v}`.** Any upper bound `w` of
`{u, v}` below `u′` has every member of the shape `⟨up p, up p⟩`, hence is
contained in `u′`; and dominating `u` forces both members of `u′` to occur in
`w`, so `u′ ⊑ w`. -/
theorem setU'_minimal {w : Plotkin.FinCompacts TT} (huw : setU ≤ w) (hvw : setV ≤ w)
    (hwu : w ≤ setU') : setU' ≤ w := by
  have shape : ∀ b ∈ w, b = kp tru tru ∨ b = kp fls fls := by
    intro b hb
    obtain ⟨p, q, rfl⟩ := exists_up_of_mem huw hvw hb
    have hpq : p = q := eq_of_le_mem_setU' (hwu.1 _ hb)
    subst hpq
    cases p with
    | true => exact Or.inl rfl
    | false => exact Or.inr rfl
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · rcases Plotkin.FinCompacts.mem_pair.mp ha with rfl | rfl
    · obtain ⟨c, hc, hle⟩ := huw.1 (kp ⊥ tru) (Plotkin.FinCompacts.mem_pair.mpr (Or.inl rfl))
      rcases shape c hc with rfl | rfl
      · exact ⟨kp tru tru, hc, le_rfl⟩
      · exact absurd (up_le_up_iff.mp (le_coords hle).2) (by decide)
    · obtain ⟨c, hc, hle⟩ := huw.1 (kp ⊥ fls) (Plotkin.FinCompacts.mem_pair.mpr (Or.inr rfl))
      rcases shape c hc with rfl | rfl
      · exact absurd (up_le_up_iff.mp (le_coords hle).2) (by decide)
      · exact ⟨kp fls fls, hc, le_rfl⟩
  · rcases shape b hb with rfl | rfl
    · exact ⟨kp tru tru, Plotkin.FinCompacts.mem_pair.mpr (Or.inl rfl), le_rfl⟩
    · exact ⟨kp fls fls, Plotkin.FinCompacts.mem_pair.mpr (Or.inr rfl), le_rfl⟩

/-- **`v′` is a minimal upper bound of `{u, v}`**, by the same argument with
"equal coordinates" replaced by "different coordinates". -/
theorem setV'_minimal {w : Plotkin.FinCompacts TT} (huw : setU ≤ w) (hvw : setV ≤ w)
    (hwv : w ≤ setV') : setV' ≤ w := by
  have shape : ∀ b ∈ w, b = kp tru fls ∨ b = kp fls tru := by
    intro b hb
    obtain ⟨p, q, rfl⟩ := exists_up_of_mem huw hvw hb
    have hpq : p ≠ q := ne_of_le_mem_setV' (hwv.1 _ hb)
    cases p with
    | true => cases q with
      | true => exact absurd rfl hpq
      | false => exact Or.inl rfl
    | false => cases q with
      | true => exact Or.inr rfl
      | false => exact absurd rfl hpq
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · rcases Plotkin.FinCompacts.mem_pair.mp ha with rfl | rfl
    · obtain ⟨c, hc, hle⟩ := huw.1 (kp ⊥ fls) (Plotkin.FinCompacts.mem_pair.mpr (Or.inr rfl))
      rcases shape c hc with rfl | rfl
      · exact ⟨kp tru fls, hc, le_rfl⟩
      · exact absurd (up_le_up_iff.mp (le_coords hle).2) (by decide)
    · obtain ⟨c, hc, hle⟩ := huw.1 (kp ⊥ tru) (Plotkin.FinCompacts.mem_pair.mpr (Or.inl rfl))
      rcases shape c hc with rfl | rfl
      · exact absurd (up_le_up_iff.mp (le_coords hle).2) (by decide)
      · exact ⟨kp fls tru, hc, le_rfl⟩
  · rcases shape b hb with rfl | rfl
    · exact ⟨kp tru fls, Plotkin.FinCompacts.mem_pair.mpr (Or.inl rfl), le_rfl⟩
    · exact ⟨kp fls tru, Plotkin.FinCompacts.mem_pair.mpr (Or.inr rfl), le_rfl⟩

/-- `u′` and `v′` are incomparable, so they are genuinely two minimal upper
bounds and not one. -/
theorem not_setU'_le_setV' : ¬ setU' ≤ setV' := by
  intro h
  obtain ⟨e, he, hle⟩ := h.1 (kp tru tru) (Plotkin.FinCompacts.mem_pair.mpr (Or.inl rfl))
  rcases Plotkin.FinCompacts.mem_pair.mp he with rfl | rfl
  · exact absurd (up_le_up_iff.mp (le_coords hle).2) (by decide)
  · exact absurd (up_le_up_iff.mp (le_coords hle).1) (by decide)

/-! ## `(T × T)♮` is not bounded complete -/

instance instDomainTT : Domain TT := PowerdomainRep.domain_prod

instance instBoundedCompleteTT : BoundedComplete TT := lem10_prod

/-- `{↓u, ↓v}` is bounded above in `(T × T)♮` — by `↓u′`. -/
theorem bddAbove_pair :
    BddAbove ({Plotkin.principal setU, Plotkin.principal setV} : Set (Plotkin.Powerdomain TT)) := by
  refine ⟨Plotkin.principal setU', ?_⟩
  rintro x (rfl | rfl)
  · exact Plotkin.principal_le_principal.mpr setU_le_setU'
  · exact Plotkin.principal_le_principal.mpr setV_le_setU'

/-- **`{↓u, ↓v}` has no least upper bound in `(T × T)♮`.** A least upper bound
`I` would contain `u` and `v`; being an ideal it is directed, so it would contain
a single `w` above both; and `I` lies below `↓u′` and below `↓v′`, so `w` would
refine both — which `no_common_refinement` forbids. -/
theorem not_exists_isLUB :
    ¬ ∃ I : Plotkin.Powerdomain TT,
        IsLUB ({Plotkin.principal setU, Plotkin.principal setV} : Set (Plotkin.Powerdomain TT)) I := by
  rintro ⟨I, hI⟩
  have hu : setU ∈ I := IdealCompletion.principal_le_iff.mp (hI.1 (Set.mem_insert _ _))
  have hv : setV ∈ I :=
    IdealCompletion.principal_le_iff.mp (hI.1 (Set.mem_insert_of_mem _ rfl))
  have hIu' : I ≤ Plotkin.principal setU' := by
    refine hI.2 ?_
    rintro x (rfl | rfl)
    · exact Plotkin.principal_le_principal.mpr setU_le_setU'
    · exact Plotkin.principal_le_principal.mpr setV_le_setU'
  have hIv' : I ≤ Plotkin.principal setV' := by
    refine hI.2 ?_
    rintro x (rfl | rfl)
    · exact Plotkin.principal_le_principal.mpr setU_le_setV'
    · exact Plotkin.principal_le_principal.mpr setV_le_setV'
  obtain ⟨w, hw, huw, hvw⟩ := I.directed setU hu setV hv
  exact no_common_refinement huw hvw
    (IdealCompletion.mem_principal.mp (hIu' hw)) (IdealCompletion.mem_principal.mp (hIv' hw))

/-- **`(T × T)♮` is not bounded complete.** `BoundedComplete` asserts that every
bounded set has a least upper bound (`exists_isLUB_of_bddAbove`); `{↓u, ↓v}` is
bounded and has none. -/
theorem not_boundedComplete_plotkin_TT : ¬ BoundedComplete (Plotkin.Powerdomain TT) := by
  intro h
  haveI := h
  exact not_exists_isLUB (exists_isLUB_of_bddAbove bddAbove_pair)

/-- **§6's opening sentence, at the paper's own witness.** `T × T` is a bounded
complete domain and its convex powerdomain is not bounded complete — so `(·)♮`
does not preserve bounded completeness, which is exactly the conjunct Lemma 13
omits for `♮` and states for `♯` and `♭`. -/
theorem convex_does_not_preserve_boundedComplete :
    Domain TT ∧ BoundedComplete TT ∧ ¬ BoundedComplete (Plotkin.Powerdomain TT) :=
  ⟨inferInstance, inferInstance, not_boundedComplete_plotkin_TT⟩

end

end ScottDomains.Flat
