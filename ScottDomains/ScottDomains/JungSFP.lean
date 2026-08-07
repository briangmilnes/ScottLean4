import ScottDomains.MinimalUpperBounds
import ScottDomains.StepFunction

/-!
# Jung's step 2: the bifurcation "bifinite or algebraic L-domain"

This file formalizes **Lemma 2.13** and **Theorem 2.14** of A. Jung,
*Cartesian Closed Categories of Domains*, CWI Tract 66 (1989) — the step that
`ScottDomains/Section62.lean` identifies as the missing prerequisite of
Theorem 18 and that rounds r0029–r0031 each failed for want of.

Everything here is read off the PDF in `ScottDomains/papers/Jung 1989 Cartesian
Closed Categories of Domains.pdf`, quoted rather than paraphrased:

> **Lemma 2.13** Let `D` and `E` be algebraic dcpo's with least element and with
> property m. If `E` is not an L-domain and if `B(D)` does not have property M
> then `[D → E]` is not continuous.

> **Theorem 2.14** If `D` is a pointed dcpo with an algebraic function space then
> `D` is a bifinite domain or `D` is an algebraic L-domain.

## Terminology map

Jung's *property m* is `HasCompleteMub`; *property M* is property m together with
finiteness of `minimalUpperBounds`; `U ⁿ` and `U ^∞` are `mubIter` and
`mubClosure`. All four are already in `MinimalUpperBounds.lean`. `B(D)` is
`compacts α`. `mub(A)` taken in the basis is `minimalUpperBounds (compacts α) A`.

## What is proved, and in which form

Three groups of results, in dependency order.

1. **Jung's Proposition 1.9 and its converse** —
   `isCompactElement_of_minimal_upperBounds`,
   `minimal_upperBounds_of_mem_minimalUpperBounds`,
   `mem_minimalUpperBounds_of_minimal`. In an algebraic dcpo, minimality of an
   upper bound of a finite set of compacts *inside `K(D)`* and minimality *in all
   of `D`* are the same condition, and both force compactness. The development
   states minimal upper bounds relative to a subset (that is what §6 needs), so
   this bridge has to exist before any of Jung's arguments can run — every one of
   them applies minimality to a bound that is not known to be compact.

2. **The four-region function `jungFun` and its continuity criterion** —
   `IsJungPatch`, `IsJungPatch.monotone`, `IsJungPatch.scottContinuous`,
   `jungHom`. Jung writes down three functions `D → E` (called `g`, `f_A` and,
   in Lemma 2.17, `f_S`) that differ only in the value they take on
   `↑x₁ ∩ ↑x₂`; the other three regions carry `⊥`, `a₁`, `a₂` in all of them.
   `jungFun x₁ x₂ a₁ a₂ t` is that shape with the top region abstracted as `t`,
   and `IsJungPatch` is exactly the four conditions on `t` that make the result
   monotone and Scott continuous. Both later families are instances, so the case
   analysis is paid for once.

3. **Lemma 2.13 and Theorem 2.14** — `lemma213`, `thm214`.

## Two deviations from the source, both weakenings

* Jung concludes `[D → E]` is **not continuous**; this file concludes it is not
  **algebraic**. Algebraic implies continuous, so our statement is the weaker
  one, and it is the one Theorem 2.14 and Theorem 18 consume. The change costs
  nothing in the proof: the single use of continuity is Proposition 1.9, which
  item 1 above proves for `IsAlgebraic` directly.
* Jung's "`E` is not an L-domain" is used through Theorem 2.10 (vii) — "for each
  upper bound `x` of a pair of compact elements there is a unique minimal upper
  bound below `x`" — and through nothing else. `HasAtMostOneMubBelow` is the
  uniqueness half of that condition, stated directly. This is deliberate and is
  what makes the file free of `sorry`; see the obstruction note below.

## Precisely-located obstruction: Theorem 2.10 is not formalized

`HasAtMostOneMubBelow D` is Jung's condition (vii) minus its existence clause, not
the definition "every principal ideal `↓x` is a complete lattice". Jung's
Theorem 2.10 proves (i) ⟺ (iv) ⟺ (v) ⟺ (vi) ⟺ (vii) ⟺ (viii) for algebraic
dcpo's; none of those six implications is formalized here. The consequence is
bounded and is worth stating exactly:

* **Nothing downstream needs the missing equivalences.** The only use Jung makes
  of "`D` is an algebraic L-domain" after Theorem 2.14 is in the proof of
  Lemma 2.17, where he writes "so any element above both `a₁` and `a₂` is above
  exactly one element of `mub(A)`" — which *is* condition (vii), and is implied
  by `HasAtMostOneMubBelow` together with property m. So the route to Theorem 18
  passes through this file's predicate and never through the lattice definition.
* **What is therefore missing is a name, not a step.** To call the second
  disjunct of `thm214` "`D` is an algebraic L-domain" in the literature's sense
  one must add the existence clause (Jung's property m for pairs, his
  Theorem 1.37, absent from the development) and then Theorem 2.10 (v) ⟹ (iv).
  Until that is done `thm214`'s second disjunct is the strictly weaker,
  formally-checked statement it says it is.

## Where countability is *not* spent

Neither `lemma213` nor `thm214` uses `Domain.countable_compacts`, and neither
should: Jung's Theorem 2.14 is the purely algebraic bifurcation, and it is true
without any cardinality hypothesis. `Section62.lean` records that Theorem 18 is
**false** without countability — the algebraic L-domains are the counterexamples
(Abramsky & Jung Theorem 4.3.4 against 4.3.5). Countability is spent in Jung's
Lemma 2.17, the *next* step, which kills the L-domain disjunct by building
`2 ^ #mub(A)` compact elements of `[D → D]`. That step is not in this file.
-/

namespace ScottDomains.JungSFP

open ScottDomains

/-! ## Jung's Proposition 1.9, and minimality inside `K(D)` versus in `D` -/

section Algebraic

variable {α : Type*} [CompletePartialOrder α] [IsAlgebraic α] {u : Set α} {m : α}

/-- **Jung 1989, Proposition 1.9.** In an algebraic dcpo a minimal upper bound of
a finite set of compact elements is itself compact.

Jung's proof verbatim, with `compactsBelow m` for his "`↓x` is directed": the
finitely many members of `u` all lie in `compactsBelow m`, so directedness
collapses them to a single compact `z ⊑ m` that still bounds `u`; minimality of
`m` gives `m ⊑ z`, and antisymmetry makes `m` the compact `z`. -/
theorem isCompactElement_of_minimal_upperBounds (hu : u.Finite) (huc : u ⊆ compacts α)
    (hm : Minimal (· ∈ upperBounds u) m) : IsCompactElement m := by
  obtain ⟨z, hz, hzub⟩ :=
    exists_mem_upperBounds_of_directedOn (IsAlgebraic.directedOn_compactsBelow m)
      (compactsBelow_nonempty m) hu fun y hy => ⟨y, ⟨huc hy, hm.1 hy⟩, le_rfl⟩
  have hmz : m ≤ z := hm.2 (fun y hy => hzub y hy) hz.2
  have : m = z := le_antisymm hmz hz.2
  rw [this]
  exact hz.1

/-- Minimality among the *compact* upper bounds upgrades to minimality among
**all** upper bounds, for a finite set of compact elements in an algebraic dcpo.

This is the bridge the development did not have. Every one of Jung's minimality
arguments applies the minimality of some `b ∈ mub(A)` to a bound that is not
known to be compact — a value `h d` of an arbitrary continuous function, or an
arbitrary element of a directed set. The proof is the same collapse as
Proposition 1.9: any upper bound `y ⊑ m` dominates a *compact* upper bound `z`,
and minimality in `K(D)` gives `m ⊑ z ⊑ y`. -/
theorem minimal_upperBounds_of_mem_minimalUpperBounds (hu : u.Finite) (huc : u ⊆ compacts α)
    (hm : m ∈ minimalUpperBounds (compacts α) u) : Minimal (· ∈ upperBounds u) m := by
  refine ⟨hm.1.2, fun y hy hym => ?_⟩
  obtain ⟨z, hz, hzub⟩ :=
    exists_mem_upperBounds_of_directedOn (IsAlgebraic.directedOn_compactsBelow y)
      (compactsBelow_nonempty y) hu fun w hw => ⟨w, ⟨huc hw, hy hw⟩, le_rfl⟩
  exact (hm.2 ⟨hz.1, fun w hw => hzub w hw⟩ (hz.2.trans hym)).trans hz.2

/-- The converse direction: a minimal upper bound in `D` is a minimal upper bound
in `K(D)`. Together with the previous two results the two notions coincide on
finite sets of compacts. -/
theorem mem_minimalUpperBounds_of_minimal (hu : u.Finite) (huc : u ⊆ compacts α)
    (hm : Minimal (· ∈ upperBounds u) m) : m ∈ minimalUpperBounds (compacts α) u :=
  ⟨⟨isCompactElement_of_minimal_upperBounds hu huc hm, hm.1⟩, fun _ hy hym => hm.2 hy.2 hym⟩

end Algebraic

/-! ## The four-region function

Jung's `g`, `f_A` (Lemma 2.13) and `f_S` (Lemma 2.17) are the same function on
three of their four regions. `jungFun` is that common shape. -/

section JungFun

variable {D E : Type*} [CompletePartialOrder D] [CompletePartialOrder E]
variable {x₁ x₂ : D} {a₁ a₂ : E} {t : D → E} {d : D}

open Classical in
/-- Jung's four-region function: `⊥` off `↑x₁ ∪ ↑x₂`, `a₁` on `↑x₁ \ ↑x₂`, `a₂`
on `↑x₂ \ ↑x₁`, and the abstracted value `t d` on `↑x₁ ∩ ↑x₂`. `x₁ ≤ d` is not
decidable, so the branches are classical, exactly as in `stepFun`. -/
noncomputable def jungFun (x₁ x₂ : D) (a₁ a₂ : E) (t : D → E) : D → E := fun d =>
  if x₁ ≤ d then (if x₂ ≤ d then t d else a₁) else (if x₂ ≤ d then a₂ else ⊥)

theorem jungFun_of_both (h₁ : x₁ ≤ d) (h₂ : x₂ ≤ d) :
    jungFun x₁ x₂ a₁ a₂ t d = t d := by
  classical simp only [jungFun, if_pos h₁, if_pos h₂]

theorem jungFun_of_left (h₁ : x₁ ≤ d) (h₂ : ¬ x₂ ≤ d) :
    jungFun x₁ x₂ a₁ a₂ t d = a₁ := by
  classical simp only [jungFun, if_pos h₁, if_neg h₂]

theorem jungFun_of_right (h₁ : ¬ x₁ ≤ d) (h₂ : x₂ ≤ d) :
    jungFun x₁ x₂ a₁ a₂ t d = a₂ := by
  classical simp only [jungFun, if_neg h₁, if_pos h₂]

theorem jungFun_of_neither (h₁ : ¬ x₁ ≤ d) (h₂ : ¬ x₂ ≤ d) :
    jungFun x₁ x₂ a₁ a₂ t d = (⊥ : E) := by
  classical simp only [jungFun, if_neg h₁, if_neg h₂]

/-- Two four-region functions agreeing at `d` on the top region agree at `d`. -/
theorem jungFun_congr {t' : D → E} (h : x₁ ≤ d → x₂ ≤ d → t d = t' d) :
    jungFun x₁ x₂ a₁ a₂ t d = jungFun x₁ x₂ a₁ a₂ t' d := by
  by_cases h₁ : x₁ ≤ d
  · by_cases h₂ : x₂ ≤ d
    · rw [jungFun_of_both h₁ h₂, jungFun_of_both h₁ h₂, h h₁ h₂]
    · rw [jungFun_of_left h₁ h₂, jungFun_of_left h₁ h₂]
  · by_cases h₂ : x₂ ≤ d
    · rw [jungFun_of_right h₁ h₂, jungFun_of_right h₁ h₂]
    · rw [jungFun_of_neither h₁ h₂, jungFun_of_neither h₁ h₂]

/-- Compactness of `x₁` and `x₂` puts a single member of a directed set above
both, whenever their least upper bound is above both. -/
theorem exists_mem_of_isLUB_pair (hx₁ : IsCompactElement x₁) (hx₂ : IsCompactElement x₂)
    {s : Set D} (hne : s.Nonempty) (hsd : DirectedOn (· ≤ ·) s) {b : D} (hb : IsLUB s b)
    (h₁ : x₁ ≤ b) (h₂ : x₂ ≤ b) : ∃ d ∈ s, x₁ ≤ d ∧ x₂ ≤ d := by
  obtain ⟨d₁, hd₁, hle₁⟩ := hx₁ s b hne hsd hb h₁
  obtain ⟨d₂, hd₂, hle₂⟩ := hx₂ s b hne hsd hb h₂
  obtain ⟨d, hds, hdd₁, hdd₂⟩ := hsd d₁ hd₁ d₂ hd₂
  exact ⟨d, hds, hle₁.trans hdd₁, hle₂.trans hdd₂⟩

/-- The four conditions on the top-region value `t` that make
`jungFun x₁ x₂ a₁ a₂ t` monotone and Scott continuous.

`attained` is the only one that is not routine, and it is where each instance
does its real work: at a directed least upper bound `b` lying in the top region,
the value `t b` must already be dominated by `t d` for some member `d` of the
directed set that itself lies in the top region. -/
structure IsJungPatch (x₁ x₂ : D) (a₁ a₂ : E) (t : D → E) : Prop where
  /-- `t` is monotone on the top region. -/
  monotone_top : ∀ d d' : D, x₁ ≤ d → x₂ ≤ d → d ≤ d' → t d ≤ t d'
  /-- `t` dominates `a₁` on the top region. -/
  left_le : ∀ d : D, x₁ ≤ d → x₂ ≤ d → a₁ ≤ t d
  /-- `t` dominates `a₂` on the top region. -/
  right_le : ∀ d : D, x₁ ≤ d → x₂ ≤ d → a₂ ≤ t d
  /-- The value at a directed least upper bound in the top region is already
  attained, up to `⊑`, inside the directed set. -/
  attained : ∀ s : Set D, s.Nonempty → DirectedOn (· ≤ ·) s → ∀ b : D, IsLUB s b →
    x₁ ≤ b → x₂ ≤ b → ∃ d ∈ s, x₁ ≤ d ∧ x₂ ≤ d ∧ t b ≤ t d

theorem IsJungPatch.monotone (h : IsJungPatch x₁ x₂ a₁ a₂ t) :
    Monotone (jungFun x₁ x₂ a₁ a₂ t) := by
  intro d d' hdd'
  by_cases h₁ : x₁ ≤ d
  · by_cases h₂ : x₂ ≤ d
    · rw [jungFun_of_both h₁ h₂, jungFun_of_both (h₁.trans hdd') (h₂.trans hdd')]
      exact h.monotone_top d d' h₁ h₂ hdd'
    · rw [jungFun_of_left h₁ h₂]
      by_cases h₂' : x₂ ≤ d'
      · rw [jungFun_of_both (h₁.trans hdd') h₂']
        exact h.left_le d' (h₁.trans hdd') h₂'
      · exact le_of_eq (jungFun_of_left (h₁.trans hdd') h₂').symm
  · by_cases h₂ : x₂ ≤ d
    · rw [jungFun_of_right h₁ h₂]
      by_cases h₁' : x₁ ≤ d'
      · rw [jungFun_of_both h₁' (h₂.trans hdd')]
        exact h.right_le d' h₁' (h₂.trans hdd')
      · exact le_of_eq (jungFun_of_right h₁' (h₂.trans hdd')).symm
    · rw [jungFun_of_neither h₁ h₂]
      exact bot_le

/-- Scott continuity of the four-region function. Monotonicity gives the
upper-bound half; for the least half the four regions are treated separately, and
in three of them compactness of `x₁` or of `x₂` produces the member of the
directed set at which the value is already attained. The fourth is `attained`. -/
theorem IsJungPatch.scottContinuous (h : IsJungPatch x₁ x₂ a₁ a₂ t)
    (hx₁ : IsCompactElement x₁) (hx₂ : IsCompactElement x₂) :
    ScottContinuous (jungFun x₁ x₂ a₁ a₂ t) := by
  intro s hne hsd b hb
  refine ⟨?_, ?_⟩
  · rintro _ ⟨d, hds, rfl⟩
    exact h.monotone (hb.1 hds)
  · intro w hw
    by_cases h₁ : x₁ ≤ b
    · by_cases h₂ : x₂ ≤ b
      · obtain ⟨d, hds, hd₁, hd₂, hle⟩ := h.attained s hne hsd b hb h₁ h₂
        rw [jungFun_of_both h₁ h₂]
        refine hle.trans ?_
        rw [← jungFun_of_both (a₁ := a₁) (a₂ := a₂) (t := t) hd₁ hd₂]
        exact hw ⟨d, hds, rfl⟩
      · obtain ⟨d, hds, hd₁⟩ := hx₁ s b hne hsd hb h₁
        have hd₂ : ¬ x₂ ≤ d := fun hc => h₂ (hc.trans (hb.1 hds))
        rw [jungFun_of_left h₁ h₂,
          ← jungFun_of_left (a₁ := a₁) (a₂ := a₂) (t := t) hd₁ hd₂]
        exact hw ⟨d, hds, rfl⟩
    · by_cases h₂ : x₂ ≤ b
      · obtain ⟨d, hds, hd₂⟩ := hx₂ s b hne hsd hb h₂
        have hd₁ : ¬ x₁ ≤ d := fun hc => h₁ (hc.trans (hb.1 hds))
        rw [jungFun_of_right h₁ h₂,
          ← jungFun_of_right (a₁ := a₁) (a₂ := a₂) (t := t) hd₁ hd₂]
        exact hw ⟨d, hds, rfl⟩
      · rw [jungFun_of_neither h₁ h₂]
        exact bot_le

/-- The four-region function as an element of the function space. -/
noncomputable def jungHom (hx₁ : IsCompactElement x₁) (hx₂ : IsCompactElement x₂)
    (a₁ a₂ : E) (t : D → E) (h : IsJungPatch x₁ x₂ a₁ a₂ t) : ScottHom D E :=
  ⟨jungFun x₁ x₂ a₁ a₂ t, h.scottContinuous hx₁ hx₂⟩

@[simp] theorem coe_jungHom (hx₁ : IsCompactElement x₁) (hx₂ : IsCompactElement x₂)
    (h : IsJungPatch x₁ x₂ a₁ a₂ t) :
    ⇑(jungHom hx₁ hx₂ a₁ a₂ t h) = jungFun x₁ x₂ a₁ a₂ t := rfl

/-- The four-region function is an upper bound of the two compact step functions
`x₁ ↘ a₁` and `x₂ ↘ a₂`. -/
theorem step_le_jungHom (hx₁ : IsCompactElement x₁) (hx₂ : IsCompactElement x₂)
    (h : IsJungPatch x₁ x₂ a₁ a₂ t) :
    ScottHom.step hx₁ a₁ ≤ jungHom hx₁ hx₂ a₁ a₂ t h ∧
      ScottHom.step hx₂ a₂ ≤ jungHom hx₁ hx₂ a₁ a₂ t h := by
  constructor
  · refine (ScottHom.step_le_iff hx₁).mpr ?_
    show a₁ ≤ jungFun x₁ x₂ a₁ a₂ t x₁
    by_cases h₂ : x₂ ≤ x₁
    · rw [jungFun_of_both le_rfl h₂]
      exact h.left_le x₁ le_rfl h₂
    · exact le_of_eq (jungFun_of_left (t := t) le_rfl h₂).symm
  · refine (ScottHom.step_le_iff hx₂).mpr ?_
    show a₂ ≤ jungFun x₁ x₂ a₁ a₂ t x₂
    by_cases h₁ : x₁ ≤ x₂
    · rw [jungFun_of_both h₁ le_rfl]
      exact h.right_le x₂ h₁ le_rfl
    · exact le_of_eq (jungFun_of_right (t := t) h₁ le_rfl).symm

/-- **The four-region function is a *minimal* upper bound of the two step
functions**, as soon as its top-region value is everywhere a minimal upper bound
of `{a₁, a₂}`.

This is the step Jung states as "`g` — as a minimal upper bound of the compact
functions `x₁ ↘ a₁` and `x₂ ↘ a₂`". Below `g` an upper bound `f` is forced: `⊥`
where `g` is `⊥`, and `a₁` (resp. `a₂`) on the one-sided regions because
`x₁ ↘ a₁ ⊑ f` already puts `a₁` under `f x₁ ⊑ f d`. On the top region `f d` is
squeezed between `{a₁, a₂}` and the minimal upper bound `t d`, so it equals
it. -/
theorem minimal_upperBounds_jungHom (hx₁ : IsCompactElement x₁) (hx₂ : IsCompactElement x₂)
    (h : IsJungPatch x₁ x₂ a₁ a₂ t)
    (hmin : ∀ d : D, x₁ ≤ d → x₂ ≤ d → Minimal (· ∈ upperBounds ({a₁, a₂} : Set E)) (t d)) :
    Minimal (· ∈ upperBounds ({ScottHom.step hx₁ a₁, ScottHom.step hx₂ a₂} : Set (ScottHom D E)))
      (jungHom hx₁ hx₂ a₁ a₂ t h) := by
  obtain ⟨hub₁, hub₂⟩ := step_le_jungHom hx₁ hx₂ h
  refine ⟨?_, ?_⟩
  · rintro f (rfl | rfl)
    · exact hub₁
    · exact hub₂
  · intro f hf hfg d
    have hf₁ : ScottHom.step hx₁ a₁ ≤ f := hf (Set.mem_insert _ _)
    have hf₂ : ScottHom.step hx₂ a₂ ≤ f := hf (Set.mem_insert_of_mem _ rfl)
    have ha₁ : ∀ e : D, x₁ ≤ e → a₁ ≤ f e := fun e he =>
      ((ScottHom.step_le_iff hx₁).mp hf₁).trans (f.monotone he)
    have ha₂ : ∀ e : D, x₂ ≤ e → a₂ ≤ f e := fun e he =>
      ((ScottHom.step_le_iff hx₂).mp hf₂).trans (f.monotone he)
    show jungFun x₁ x₂ a₁ a₂ t d ≤ f d
    by_cases h₁ : x₁ ≤ d
    · by_cases h₂ : x₂ ≤ d
      · rw [jungFun_of_both h₁ h₂]
        refine (hmin d h₁ h₂).2 ?_ ?_
        · rintro y (rfl | rfl)
          · exact ha₁ d h₁
          · exact ha₂ d h₂
        · have hfd : f d ≤ jungFun x₁ x₂ a₁ a₂ t d := hfg d
          rwa [jungFun_of_both h₁ h₂] at hfd
      · rw [jungFun_of_left h₁ h₂]
        exact ha₁ d h₁
    · by_cases h₂ : x₂ ≤ d
      · rw [jungFun_of_right h₁ h₂]
        exact ha₂ d h₂
      · rw [jungFun_of_neither h₁ h₂]
        exact bot_le

end JungFun

/-! ## Lemma 2.13 -/

section FVal

variable {D E : Type*}

open Classical in
/-- The top-region value of Jung's approximating family: `b₂` on the minimal
upper bounds of `{x₁, x₂}` not yet in the finite set `A`, and `c` everywhere
else. -/
noncomputable def fVal (M A : Set D) (b₂ c : E) : D → E := fun d => if d ∈ M \ A then b₂ else c

theorem fVal_pos {M A : Set D} {b₂ c : E} {d : D} (h : d ∈ M \ A) :
    fVal M A b₂ c d = b₂ := by
  classical simp only [fVal, if_pos h]

theorem fVal_neg {M A : Set D} {b₂ c : E} {d : D} (h : d ∉ M \ A) :
    fVal M A b₂ c d = c := by
  classical simp only [fVal, if_neg h]

end FVal

section Lemma213

variable {D E : Type*} [CompletePartialOrder D] [CompletePartialOrder E]

/-- If every member of a directed set that lies above `x₁` and `x₂` is a minimal
upper bound of `{x₁, x₂}`, the least upper bound is one of those members.

Two minimal upper bounds that are comparable are equal, so the part of the
directed set lying above `x₁` and `x₂` is a single element; and that part is
cofinal, because directedness lifts any member of the set into it. This is the
step Jung compresses into "the supremum of the directed family maps all of
`mub({x₁, x₂})` onto `c`". -/
theorem exists_eq_of_forall_minimal {x₁ x₂ : D} (hx₁ : IsCompactElement x₁)
    (hx₂ : IsCompactElement x₂) {s : Set D} (hne : s.Nonempty) (hsd : DirectedOn (· ≤ ·) s)
    {b : D} (hb : IsLUB s b) (h₁ : x₁ ≤ b) (h₂ : x₂ ≤ b)
    (hall : ∀ d ∈ s, x₁ ≤ d → x₂ ≤ d → Minimal (· ∈ upperBounds ({x₁, x₂} : Set D)) d) :
    ∃ d ∈ s, x₁ ≤ d ∧ x₂ ≤ d ∧ b = d := by
  obtain ⟨d, hds, hd₁, hd₂⟩ := exists_mem_of_isLUB_pair hx₁ hx₂ hne hsd hb h₁ h₂
  have hdub : d ∈ upperBounds ({x₁, x₂} : Set D) := by
    rintro y (rfl | rfl) <;> assumption
  refine ⟨d, hds, hd₁, hd₂, le_antisymm (hb.2 fun e hes => ?_) (hb.1 hds)⟩
  obtain ⟨e', he's, hde', hee'⟩ := hsd d hds e hes
  exact hee'.trans ((hall e' he's (hd₁.trans hde') (hd₂.trans hde')).2 hdub hde')

variable [IsAlgebraic D]

/-- **Jung 1989, Lemma 2.13.** If `E` carries a pair of compact elements with two
distinct minimal upper bounds under a common bound `c` (the failure of Jung's
condition (vii) of Theorem 2.10 — "`E` is not an L-domain"), and if `K(D)`
carries a pair of compact elements with infinitely many minimal upper bounds
(the failure of property M — "`B(D)` does not have property M"), then the
function space `[D → E]` is not algebraic.

The proof is Jung's. Write `M = mub{x₁, x₂}` in `K(D)`.

* `g = jungFun x₁ x₂ a₁ a₂ (fun _ => b₁)` is a minimal upper bound of the two
  compact step functions `x₁ ↘ a₁` and `x₂ ↘ a₂`, hence compact by
  Proposition 1.9 applied *in the function space* — this is the one place
  algebraicity of `[D → E]` is used, and the only place.
* `f_A = jungFun x₁ x₂ a₁ a₂ (fVal M A b₂ c)`, for `A` ranging over the finite
  subsets of `D`, is a directed family whose least upper bound is the function
  taking the constant value `c` on `↑x₁ ∩ ↑x₂`, which dominates `g` because
  `b₁ ⊑ c`.
* No single `f_A` dominates `g`: `M \ A` is nonempty because `M` is infinite and
  `A` finite, and at any `d ∈ M \ A` we have `g d = b₁` and `f_A d = b₂`, with
  `b₁ ⋢ b₂` because they are distinct minimal upper bounds of `{a₁, a₂}`.

That contradicts compactness of `g`.

Monotonicity of `f_A` is exactly where the development's missing bridge lemma is
spent: the top region splits on membership in `M`, and the split is monotone only
because a member of `M` is minimal among **all** upper bounds of `{x₁, x₂}`, not
merely among the compact ones. `minimal_upperBounds_of_mem_minimalUpperBounds`
supplies that. -/
theorem lemma213 {x₁ x₂ : D} (hx₁ : IsCompactElement x₁) (hx₂ : IsCompactElement x₂)
    (hMinf : (minimalUpperBounds (compacts D) ({x₁, x₂} : Set D)).Infinite)
    [IsAlgebraic E] {a₁ a₂ b₁ b₂ c : E} (ha₁ : IsCompactElement a₁) (ha₂ : IsCompactElement a₂)
    (hb₁ : b₁ ∈ minimalUpperBounds (compacts E) ({a₁, a₂} : Set E))
    (hb₂ : b₂ ∈ minimalUpperBounds (compacts E) ({a₁, a₂} : Set E))
    (hne : b₁ ≠ b₂) (hc₁ : b₁ ≤ c) (hc₂ : b₂ ≤ c) :
    ¬ IsAlgebraic (ScottHom D E) := by
  intro hAlg
  haveI := hAlg
  classical
  set M : Set D := minimalUpperBounds (compacts D) ({x₁, x₂} : Set D) with hM
  -- the two finite sets of compacts the argument runs over
  have hxfin : ({x₁, x₂} : Set D).Finite := Set.toFinite _
  have hxc : ({x₁, x₂} : Set D) ⊆ compacts D := by rintro y (rfl | rfl) <;> assumption
  have hafin : ({a₁, a₂} : Set E).Finite := Set.toFinite _
  have hac : ({a₁, a₂} : Set E) ⊆ compacts E := by rintro y (rfl | rfl) <;> assumption
  -- every minimal upper bound in `K(D)` is minimal among all upper bounds
  have hMmin : ∀ m ∈ M, Minimal (· ∈ upperBounds ({x₁, x₂} : Set D)) m := fun m hm =>
    minimal_upperBounds_of_mem_minimalUpperBounds hxfin hxc hm
  have hMub : ∀ m ∈ M, x₁ ≤ m ∧ x₂ ≤ m := fun m hm =>
    ⟨(hMmin m hm).1 (Set.mem_insert _ _), (hMmin m hm).1 (Set.mem_insert_of_mem _ rfl)⟩
  -- `a₁ ⊑ b₁`, `a₂ ⊑ b₁`, and likewise for `b₂`
  have hab₁ : a₁ ≤ b₁ := hb₁.1.2 (Set.mem_insert _ _)
  have hab₁' : a₂ ≤ b₁ := hb₁.1.2 (Set.mem_insert_of_mem _ rfl)
  have hab₂ : a₁ ≤ b₂ := hb₂.1.2 (Set.mem_insert _ _)
  have hab₂' : a₂ ≤ b₂ := hb₂.1.2 (Set.mem_insert_of_mem _ rfl)
  -- Jung's `g`
  have hpatchG : IsJungPatch x₁ x₂ a₁ a₂ (fun _ : D => b₁) := by
    refine ⟨fun _ _ _ _ _ => le_rfl, fun _ _ _ => hab₁, fun _ _ _ => hab₁', ?_⟩
    intro s hs hsd b hb h₁ h₂
    obtain ⟨d, hds, hd₁, hd₂⟩ := exists_mem_of_isLUB_pair hx₁ hx₂ hs hsd hb h₁ h₂
    exact ⟨d, hds, hd₁, hd₂, le_rfl⟩
  set g : ScottHom D E := jungHom hx₁ hx₂ a₁ a₂ (fun _ : D => b₁) hpatchG with hg
  -- `g` is compact, by Proposition 1.9 in the function space
  have hgmin : Minimal
      (· ∈ upperBounds ({ScottHom.step hx₁ a₁, ScottHom.step hx₂ a₂} : Set (ScottHom D E))) g :=
    minimal_upperBounds_jungHom hx₁ hx₂ hpatchG fun _ _ _ =>
      minimal_upperBounds_of_mem_minimalUpperBounds hafin hac hb₁
  have hstepc : ({ScottHom.step hx₁ a₁, ScottHom.step hx₂ a₂} : Set (ScottHom D E))
      ⊆ compacts (ScottHom D E) := by
    rintro f (rfl | rfl)
    · exact ScottHom.isCompactElement_step hx₁ ha₁
    · exact ScottHom.isCompactElement_step hx₂ ha₂
  have hgc : IsCompactElement g :=
    isCompactElement_of_minimal_upperBounds (Set.toFinite _) hstepc hgmin
  -- Jung's `f_A`, for every finite `A`
  have hpatchF : ∀ A : Set D, IsJungPatch x₁ x₂ a₁ a₂ (fVal M A b₂ c) := by
    intro A
    have hval : ∀ d : D, fVal M A b₂ c d = b₂ ∨ fVal M A b₂ c d = c := by
      intro d
      by_cases hd : d ∈ M \ A
      · exact Or.inl (fVal_pos hd)
      · exact Or.inr (fVal_neg hd)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro d d' hd₁ hd₂ hdd'
      by_cases hd : d ∈ M \ A
      · rw [fVal_pos hd]
        rcases hval d' with h | h
        · rw [h]
        · rw [h]; exact hc₂
      · rw [fVal_neg hd]
        by_cases hd' : d' ∈ M \ A
        · exfalso
          have hdub : d ∈ upperBounds ({x₁, x₂} : Set D) := by
            rintro y (rfl | rfl) <;> assumption
          exact hd (le_antisymm hdd' ((hMmin d' hd'.1).2 hdub hdd') ▸ hd')
        · rw [fVal_neg hd']
    · intro d _ _
      rcases hval d with h | h
      · rw [h]; exact hab₂
      · rw [h]; exact hab₁.trans hc₁
    · intro d _ _
      rcases hval d with h | h
      · rw [h]; exact hab₂'
      · rw [h]; exact hab₁'.trans hc₁
    · intro s hs hsd b hb h₁ h₂
      by_cases hbm : b ∈ M \ A
      · obtain ⟨d, hds, hd₁, hd₂⟩ := exists_mem_of_isLUB_pair hx₁ hx₂ hs hsd hb h₁ h₂
        have hdb : b = d :=
          le_antisymm ((hMmin b hbm.1).2 (by rintro y (rfl | rfl) <;> assumption) (hb.1 hds))
            (hb.1 hds)
        exact ⟨d, hds, hd₁, hd₂, le_of_eq (congrArg (fVal M A b₂ c) hdb)⟩
      · by_contra hcon
        have hallM : ∀ d ∈ s, x₁ ≤ d → x₂ ≤ d → d ∈ M \ A := by
          intro d hds hd₁ hd₂
          by_contra hdn
          exact hcon ⟨d, hds, hd₁, hd₂,
            le_of_eq ((fVal_neg hbm).trans (fVal_neg hdn).symm)⟩
        obtain ⟨d, hds, hd₁, hd₂, hbd⟩ :=
          exists_eq_of_forall_minimal hx₁ hx₂ hs hsd hb h₁ h₂ fun d hds hd₁ hd₂ =>
            hMmin d (hallM d hds hd₁ hd₂).1
        exact hbm (hbd ▸ hallM d hds hd₁ hd₂)
  set F : Set D → ScottHom D E := fun A => jungHom hx₁ hx₂ a₁ a₂ (fVal M A b₂ c) (hpatchF A)
    with hF
  set 𝓕 : Set (ScottHom D E) := {f | ∃ A : Set D, A.Finite ∧ f = F A} with h𝓕
  -- the family is directed: `A ⊆ A'` makes `f_A ⊑ f_{A'}`
  have hmono : ∀ A A' : Set D, A ⊆ A' → F A ≤ F A' := by
    intro A A' hAA' d
    show jungFun x₁ x₂ a₁ a₂ (fVal M A b₂ c) d ≤ jungFun x₁ x₂ a₁ a₂ (fVal M A' b₂ c) d
    by_cases h₁ : x₁ ≤ d
    · by_cases h₂ : x₂ ≤ d
      · rw [jungFun_of_both h₁ h₂, jungFun_of_both h₁ h₂]
        by_cases hd' : d ∈ M \ A'
        · rw [fVal_pos hd', fVal_pos ⟨hd'.1, fun hc => hd'.2 (hAA' hc)⟩]
        · rw [fVal_neg hd']
          by_cases hd : d ∈ M \ A
          · rw [fVal_pos hd]; exact hc₂
          · rw [fVal_neg hd]
      · rw [jungFun_of_left h₁ h₂, jungFun_of_left h₁ h₂]
    · by_cases h₂ : x₂ ≤ d
      · rw [jungFun_of_right h₁ h₂, jungFun_of_right h₁ h₂]
      · rw [jungFun_of_neither h₁ h₂, jungFun_of_neither h₁ h₂]
  have hdir : DirectedOn (· ≤ ·) 𝓕 := by
    rintro _ ⟨A, hA, rfl⟩ _ ⟨A', hA', rfl⟩
    exact ⟨F (A ∪ A'), ⟨A ∪ A', hA.union hA', rfl⟩,
      hmono A (A ∪ A') Set.subset_union_left, hmono A' (A ∪ A') Set.subset_union_right⟩
  have hFne : 𝓕.Nonempty := ⟨F ∅, ∅, Set.finite_empty, rfl⟩
  -- the least upper bound of the family is the constant-`c` patch
  have hpatchH : IsJungPatch x₁ x₂ a₁ a₂ (fun _ : D => c) := by
    refine ⟨fun _ _ _ _ _ => le_rfl, fun _ _ _ => hab₁.trans hc₁,
      fun _ _ _ => hab₁'.trans hc₁, ?_⟩
    intro s hs hsd b hb h₁ h₂
    obtain ⟨d, hds, hd₁, hd₂⟩ := exists_mem_of_isLUB_pair hx₁ hx₂ hs hsd hb h₁ h₂
    exact ⟨d, hds, hd₁, hd₂, le_rfl⟩
  set H : ScottHom D E := jungHom hx₁ hx₂ a₁ a₂ (fun _ : D => c) hpatchH with hH
  have hHlub : IsLUB 𝓕 H := by
    constructor
    · rintro _ ⟨A, _, rfl⟩ d
      show jungFun x₁ x₂ a₁ a₂ (fVal M A b₂ c) d ≤ jungFun x₁ x₂ a₁ a₂ (fun _ : D => c) d
      by_cases h₁ : x₁ ≤ d
      · by_cases h₂ : x₂ ≤ d
        · rw [jungFun_of_both h₁ h₂, jungFun_of_both h₁ h₂]
          by_cases hd : d ∈ M \ A
          · rw [fVal_pos hd]; exact hc₂
          · rw [fVal_neg hd]
        · rw [jungFun_of_left h₁ h₂, jungFun_of_left h₁ h₂]
      · by_cases h₂ : x₂ ≤ d
        · rw [jungFun_of_right h₁ h₂, jungFun_of_right h₁ h₂]
        · rw [jungFun_of_neither h₁ h₂, jungFun_of_neither h₁ h₂]
    · intro w hw d
      have hle := hw (show F {d} ∈ 𝓕 from ⟨{d}, Set.finite_singleton d, rfl⟩) d
      show jungFun x₁ x₂ a₁ a₂ (fun _ : D => c) d ≤ w d
      refine le_trans (le_of_eq ?_) hle
      exact jungFun_congr fun _ _ => (fVal_neg (fun hc => hc.2 rfl)).symm
  -- `g ⊑ H`, so compactness of `g` puts `g` under some `f_A`
  have hgH : g ≤ H := by
    intro d
    show jungFun x₁ x₂ a₁ a₂ (fun _ : D => b₁) d ≤ jungFun x₁ x₂ a₁ a₂ (fun _ : D => c) d
    by_cases h₁ : x₁ ≤ d
    · by_cases h₂ : x₂ ≤ d
      · rw [jungFun_of_both h₁ h₂, jungFun_of_both h₁ h₂]; exact hc₁
      · rw [jungFun_of_left h₁ h₂, jungFun_of_left h₁ h₂]
    · by_cases h₂ : x₂ ≤ d
      · rw [jungFun_of_right h₁ h₂, jungFun_of_right h₁ h₂]
      · rw [jungFun_of_neither h₁ h₂, jungFun_of_neither h₁ h₂]
  obtain ⟨f, hf𝓕, hgf⟩ := hgc 𝓕 H hFne hdir hHlub hgH
  obtain ⟨A, hAfin, rfl⟩ := hf𝓕
  -- but no `f_A` is above `g`
  obtain ⟨d, hd⟩ := (hMinf.sdiff hAfin).nonempty
  obtain ⟨hd₁, hd₂⟩ := hMub d hd.1
  have hb₁b₂ : b₁ ≤ b₂ := by
    have hgd : jungFun x₁ x₂ a₁ a₂ (fun _ : D => b₁) d
        ≤ jungFun x₁ x₂ a₁ a₂ (fVal M A b₂ c) d := hgf d
    simp only [jungFun_of_both hd₁ hd₂, fVal_pos hd] at hgd
    exact hgd
  exact hne (le_antisymm hb₁b₂ (hb₂.2 hb₁.1 hb₁b₂))

end Lemma213

/-! ## Theorem 2.14 -/

section Thm214

variable {D : Type*} [CompletePartialOrder D] [IsAlgebraic D]

/-- The failure of Jung's condition (vii) of Theorem 2.10: some pair of compact
elements has **two distinct** minimal upper bounds under one common bound. This
is what Jung's proof of Lemma 2.13 extracts from "`E` is not an L-domain", and it
is the exact shape `lemma213` consumes. -/
def HasTwoMubBelow (D : Type*) [CompletePartialOrder D] : Prop :=
  ∃ a₁ a₂ : D, IsCompactElement a₁ ∧ IsCompactElement a₂ ∧ ∃ x m₁ m₂ : D,
    m₁ ∈ minimalUpperBounds (compacts D) ({a₁, a₂} : Set D) ∧
      m₂ ∈ minimalUpperBounds (compacts D) ({a₁, a₂} : Set D) ∧
        m₁ ≤ x ∧ m₂ ≤ x ∧ m₁ ≠ m₂

/-- The uniqueness half of Jung's condition (vii) of Theorem 2.10: a pair of
compact elements has **at most one** minimal upper bound below any given bound.

Jung's Theorem 2.10 shows that (vii) — this together with the corresponding
existence clause, which is property m for pairs — characterizes the algebraic
L-domains. That equivalence is not formalized here; see the module docstring for
exactly what that leaves open. What matters downstream is that this is the only
consequence of "algebraic L-domain" that Jung's Lemmas 2.13 and 2.17 ever use. -/
def HasAtMostOneMubBelow (D : Type*) [CompletePartialOrder D] : Prop :=
  ¬ HasTwoMubBelow D

/-- **Jung 1989, Theorem 2.14 — the bifurcation.** If the function space
`[D → D]` is algebraic then either `K(D)` has property M at every pair of compact
elements, or `D` satisfies the uniqueness condition (vii) that characterizes the
algebraic L-domains.

The proof is Jung's contraposition of Lemma 2.13 with `E = D`: negating both
disjuncts supplies simultaneously a pair `{x₁, x₂}` with infinitely many minimal
upper bounds and a pair `{a₁, a₂}` with two distinct minimal upper bounds under a
common bound, which is precisely Lemma 2.13's input.

**What this is and is not.** Jung's own statement reads "`D` is a bifinite domain
or `D` is an algebraic L-domain". Two conversions separate that from what is
proved here, and both live outside step 2:

* first disjunct — property M at pairs becomes property M outright by Jung's
  Lemma 1.29, and property M becomes bifiniteness by his Lemma 2.2 together with
  Theorem 1.32 (`isBifinite_iff_mubClosure`, already in the development). Jung's
  Lemma 2.2 is step 4 and is only partly proved (`Section62.lean`);
* second disjunct — `HasAtMostOneMubBelow` becomes "algebraic L-domain" by his
  Theorem 2.10, adding the existence clause his Theorem 1.37 supplies. Neither
  is formalized.

No `sorry` stands in for either: the statement below is what the kernel checks,
and it is weaker than Jung's in exactly the two named ways. -/
theorem thm214 (hAlg : IsAlgebraic (ScottHom D D)) :
    (∀ x₁ x₂ : D, IsCompactElement x₁ → IsCompactElement x₂ →
        (minimalUpperBounds (compacts D) ({x₁, x₂} : Set D)).Finite) ∨
      HasAtMostOneMubBelow D := by
  by_cases hL : HasTwoMubBelow D
  · refine Or.inl fun x₁ x₂ hx₁ hx₂ => ?_
    by_contra hinf
    obtain ⟨a₁, a₂, ha₁, ha₂, x, m₁, m₂, hm₁, hm₂, hx1, hx2, hne⟩ := hL
    exact lemma213 hx₁ hx₂ hinf ha₁ ha₂ hm₁ hm₂ hne hx1 hx2 hAlg
  · exact Or.inr hL

end Thm214

end ScottDomains.JungSFP
