import ScottDomains.A1Lemma24

/-!
# `Thm29Normal` at finite bases: `A∞` is universal for the finite bifinite domains

Round r0047 left `LemThirty.Thm29Normal` open with three named routes and none
attempted. This file takes route 1 — *prove `Thm29Normal` by a route that does
not pass through Theorem 25* — and carries it as far as it goes: **every finite
poset with a least element sits normally inside `A∞`**, hence `Thm29Normal`'s
conclusion holds for every bifinite domain with a finite basis.

## Why route 1, and why it was not closed by the r0047 refutation

r0047 measured a real obstruction and drew a conclusion one step too strong. The
kernel-checked facts are

| # | fact | declaration |
| - | ---- | ----------- |
| 1 | Gunter's Lemma 24 holds at `A⁺ = M(A)`, against the connecting map `η` | `R47.Agent1.lemma24_MPair`, `lemma24_Step` |
| 2 | the tower's connecting map is `M(f)`, not `η` | `Colimit.stgEmb_ne_mk_eta` |
| 3 | Theorem 25's hypothesis is **false** at `A∞` | `R47.Agent1.not_hasNormalRealizations_Ainf` |
| 4 | so is its stagewise residue | `R47.Agent1.not_stagewise_realizations` |

Row 3 refutes `R46.Agent2.HasNormalRealizations A∞`, whose one use is as the
hypothesis of `R46.Agent2.thm29Normal_of_hasNormalRealizations`. That closes one
*sufficient condition*. It does not close `Thm29Normal`, and the reason is worth
stating precisely, because the recorded blocker — "the route to it through
Theorem 25 is now closed at this tower" — is **narrower than it reads**.

`HasNormalRealizations A∞` quantifies over **every** finite normal `A ◁ A∞`,
including `A = im(incl 1) = {⊥, β}`, and asks `A∞` to realize every normal type
over each. `Thm29Normal` asks only that **some** normal embedding
`K(E) → A∞` exist. A construction is free to choose where its copies sit, and
row 1 already supplies realizations over the `η`-copy of a stage inside the next
stage. The `η`-copy is not the tower's inclusion, so it is useless for
*extending* an embedding already fixed in `A∞` — but for *building* one copy of a
finite poset it is exactly what is needed, because a finite poset is finished
after finitely many steps and only the final stage is mapped into `A∞`.

That is the whole of the argument below: run Gunter's induction **inside the
tower's stages, along `mk ∘ η`**, and map into `A∞` once, at the end, by `incl`.
Nothing here contradicts rows 3 and 4; both quantify over subposets that the
construction never produces.

## The three steps

| # | step | declaration | what it costs |
| - | ---- | ----------- | ------------- |
| 1 | one point more, one stage later | `exists_stage_succ` | `R47.Agent1.lemma24_Step` at `α := Stg k` |
| 2 | Gunter's Proposition 21, iterated | `exists_stage_embedding` | `R46.Agent2.exists_singleton_step`, on `Set.ncard` |
| 3 | one stage into the colimit | `exists_normal_embedding_Ainf` | `Colimit.isNormalIn_range_incl`, `IsNormalIn.trans` |

Step 1 is the only new mathematics. Given a copy `h '' S ◁ Stg k` of a normal
subposet `S` of the finite poset `P`, and a point `X ∉ S` with
`insert X S ◁ P`, the pair `(P, X)` presents a **normal type over `h '' S`** in
exactly the shape `lemma24_Step` consumes: the witnessing poset is `P` itself,
the order-reflecting map is the partial inverse `Function.invFunOn h S`, and the
two normality hypotheses are `S ◁ P` and `insert X S ◁ P`. Lemma 24 returns a
point `q` of `Step (Stg k) = Stg (k+1)` realizing that type over `mk '' η '' (h '' S)`,
together with the normality of the one-point extension. The updated map is
`Function.update` in spirit — written as an `if` because the old map changes
stage as well as value.

Step 2 needs a chain `{⊥} = S₀ ⊊ S₁ ⊊ ⋯ ⊊ Sₙ = P` with every `Sᵢ ◁ P` and every
step a singleton. That is Gunter's Proposition 21, already proved in r0046 as
`R46.Agent2.exists_singleton_step`: adjoining a point **maximal in `P ∖ S`**
preserves normality. Nothing about `P` beyond finiteness is used, and the
hypothesis `P ◁ P` that Gunter's "Plotkin order" would ask for is
`IsNormalIn.refl` — `N ∩ ↓x` at `N = univ` has `x` itself as greatest element, so
**every finite poset is a Plotkin order** and the finite bifinite domains are
exactly the finite pointed posets.

## What this settles, and what it does not

`thm29Normal_finiteBasis` is `LemThirty.Thm29Normal` **with one hypothesis
added**: `Finite ↥(compacts E)`. By this development's own accounting that is a
*discharged-at*, not a discharge, and it is reported as such. `IsBifinite E` is
carried in the statement to match `Thm29Normal` and is **never used** — see the
paragraph above.

The residue is exactly the infinite case, and the obstruction in it is precisely
located: for `K(E)` infinite the construction must produce a *nested* chain of
copies inside `A∞`, so step `i+1` has to realize a normal type over
`incl kᵢ '' Aᵢ` — the **tower's** image — whereas `lemma24_Step` realizes it over
the `η`-image, and `Colimit.stgEmb_ne_mk_eta` says those differ. This is the
universal property `LemThirty.lean:479–485` names as deferred to [Gun87], and
`R47.Agent1.not_stagewise_realizations` refutes its unrestricted form. What is
*not* known, and is not asserted anywhere in this development, is whether it
holds when the subposet is required to contain no maximal point of `A∞` — the
only mechanism by which `not_hasNormalRealizations_of_maximal` refutes it. That
is stated here in prose rather than as a `Prop` nobody attempts.
-/

namespace ScottDomains.R49.Agent5

open ScottDomains ScottDomains.BifiniteUniversal ScottDomains.Colimit

/-! ## Step 1: one point more, one stage later -/

section StageStep

variable {P : Type} [PartialOrder P]

/-- **One point more, one stage later.** A normal copy of `S ⊆ P` inside `Stg k`
extends to a normal copy of `insert X S` inside `Stg (k+1)`.

The normal type of `X` over `S` is presented to `R47.Agent1.lemma24_Step` with
`P` itself as the witnessing poset and `Function.invFunOn h S` as the
order-reflecting map back; its two normality hypotheses become `S ◁ P` and
`insert X S ◁ P`. Nothing is asked of `X` beyond `X ∉ S` and that hypothesis.

The new map is an `if`, not a `Function.update`: `h` and the extension land in
different types, so the old values must be moved by `mk ∘ η` as well. -/
theorem exists_stage_succ {S : Set P} (hSfin : S.Finite) {X : P} (hXS : X ∉ S)
    (hSnorm : S ◁ (Set.univ : Set P)) (hXnorm : insert X S ◁ (Set.univ : Set P))
    {k : ℕ} (h : P → Stg k)
    (href : ∀ a ∈ S, ∀ b ∈ S, (h a ≤ h b ↔ a ≤ b))
    (hnorm : h '' S ◁ (Set.univ : Set (Stg k))) :
    ∃ h' : P → Step (Stg k),
      (∀ a ∈ insert X S, ∀ b ∈ insert X S, (h' a ≤ h' b ↔ a ≤ b)) ∧
      h' '' insert X S ◁ (Set.univ : Set (Step (Stg k))) := by
  classical
  haveI : Nonempty P := ⟨X⟩
  have hbne : ∀ a ∈ S, a ≠ X := fun a ha hax => hXS (hax ▸ ha)
  have hinj : Set.InjOn h S := fun a ha b hb hab =>
    le_antisymm ((href a ha b hb).mp hab.le) ((href b hb a ha).mp hab.ge)
  have hgh : ∀ a ∈ S, Function.invFunOn h S (h a) = a := hinj.leftInvOn_invFunOn
  have himg : Function.invFunOn h S '' (h '' S) = S := by
    ext a
    constructor
    · rintro ⟨_, ⟨a', ha', rfl⟩, rfl⟩
      rw [hgh a' ha']
      exact ha'
    · exact fun ha => ⟨h a, ⟨a, ha, rfl⟩, hgh a ha⟩
  obtain ⟨q, hreal, hqnorm⟩ :=
    R47.Agent1.lemma24_Step (α := Stg k) (hSfin.image h) hnorm P (Set.univ : Set P)
      (Function.invFunOn h S) X
      (by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        rw [hgh a ha, hgh b hb]
        exact (href a ha b hb).symm)
      (by rw [himg]; exact hSnorm)
      (by rw [himg]; exact hXnorm)
  have hupd : ∀ a ∈ S,
      Function.update (fun x => (mk (eta (h x)) : Step (Stg k))) X q a = mk (eta (h a)) :=
    fun a ha => Function.update_of_ne (hbne a ha) _ _
  have hupdX : Function.update (fun x => (mk (eta (h x)) : Step (Stg k))) X q X = q :=
    Function.update_self _ _ _
  refine ⟨Function.update (fun x => (mk (eta (h x)) : Step (Stg k))) X q, ?_, ?_⟩
  · rintro a (rfl | ha) b (rfl | hb)
    · simp
    · rw [hupdX, hupd b hb]
      have hty := (hreal (h b) ⟨b, hb, rfl⟩).2
      rwa [hgh b hb] at hty
    · rw [hupdX, hupd a ha]
      have hty := (hreal (h a) ⟨a, ha, rfl⟩).1
      rwa [hgh a ha] at hty
    · rw [hupd a ha, hupd b hb]
      exact mk_le_mk.trans (eta_le_eta_iff.trans (href a ha b hb))
  · have himg' :
        Function.update (fun x => (mk (eta (h x)) : Step (Stg k))) X q '' insert X S
          = insert q ((fun b => (mk (eta b) : Step (Stg k))) '' (h '' S)) := by
      rw [Set.image_insert_eq, hupdX, Set.image_image]
      exact congrArg (insert q) (Set.image_congr hupd)
    rw [himg']
    exact hqnorm

end StageStep

/-! ## Step 2: Gunter's Proposition 21, iterated through the tower -/

section Iterate

variable {P : Type} [PartialOrder P] [Finite P]

/-- **Every finite poset with `⊥` has a normal copy in some stage.**

The induction is Gunter's Proposition 21 run on `Set.ncard (univ ∖ S)`, exactly
as `R46.Agent2.hasFiniteExtensions_of_hasNormalRealizations` runs it — with the
appeal to the refuted realization property replaced by `exists_stage_succ`, which
pays for the point by moving one stage up the tower.

Stated in the `∀ n` form so the recursion has a decreasing measure; the caller
supplies `n := Set.ncard (univ ∖ {⊥})`. -/
theorem exists_stage_embedding :
    ∀ n : ℕ, ∀ S : Set P, Set.ncard (Set.univ \ S) ≤ n → S ◁ (Set.univ : Set P) →
      ∀ (k : ℕ) (h : P → Stg k),
        (∀ a ∈ S, ∀ b ∈ S, (h a ≤ h b ↔ a ≤ b)) → h '' S ◁ (Set.univ : Set (Stg k)) →
        ∃ (k' : ℕ) (h' : P → Stg k'),
          (∀ a b : P, (h' a ≤ h' b ↔ a ≤ b)) ∧ Set.range h' ◁ (Set.univ : Set (Stg k')) := by
  have finish : ∀ S : Set P, Set.univ \ S = ∅ → ∀ (k : ℕ) (h : P → Stg k),
      (∀ a ∈ S, ∀ b ∈ S, (h a ≤ h b ↔ a ≤ b)) → h '' S ◁ (Set.univ : Set (Stg k)) →
      ∃ (k' : ℕ) (h' : P → Stg k'),
        (∀ a b : P, (h' a ≤ h' b ↔ a ≤ b)) ∧ Set.range h' ◁ (Set.univ : Set (Stg k')) := by
    intro S hempty k h href hnorm
    have hS : S = Set.univ :=
      Set.Subset.antisymm (Set.subset_univ _) (Set.sdiff_eq_empty.mp hempty)
    subst hS
    exact ⟨k, h, fun a b => href a (Set.mem_univ a) b (Set.mem_univ b),
      by rwa [Set.image_univ] at hnorm⟩
  intro n
  induction n with
  | zero =>
    intro S hcard hSnorm k h href hnorm
    exact finish S ((Set.ncard_eq_zero (Set.toFinite _)).mp (Nat.le_zero.mp hcard))
      k h href hnorm
  | succ n ih =>
    intro S hcard hSnorm k h href hnorm
    rcases Set.eq_empty_or_nonempty (Set.univ \ S) with hempty | hne
    · exact finish S hempty k h href hnorm
    · obtain ⟨X, hXmem, -, hXnorm⟩ :=
        R46.Agent2.exists_singleton_step hSnorm (Set.toFinite _) hne
      obtain ⟨h', href', hnorm'⟩ :=
        exists_stage_succ (Set.toFinite S) hXmem.2 hSnorm hXnorm h href hnorm
      have hsub : (Set.univ \ insert X S) ⊆ (Set.univ \ S) :=
        fun z hz => ⟨hz.1, fun hzS => hz.2 (Set.mem_insert_of_mem _ hzS)⟩
      have hlt : Set.ncard (Set.univ \ insert X S) < Set.ncard (Set.univ \ S) :=
        Set.ncard_lt_ncard
          ((Set.ssubset_iff_of_subset hsub).mpr
            ⟨X, hXmem, fun hz => hz.2 (Set.mem_insert _ _)⟩)
          (Set.toFinite _)
      exact ih (insert X S) (by omega) hXnorm (k + 1) h' href' hnorm'

end Iterate

/-! ## Step 3: one stage into the colimit -/

/-- **`A∞` is universal for the finite pointed posets.** Every finite poset with a
least element admits an order-reflecting map into `A∞` whose range is normal in
`A∞` — `LemThirty.Thm29Normal`'s conclusion, at a finite basis.

The chain starts at `S := {⊥}` inside `Stg 0`, which is `PUnit`, and
`singleton_bot_isNormalIn` discharges normality at both ends of the base case.
The last stage is carried into `A∞` by `incl k`, which is order-reflecting
(`Colimit.incl_le_incl`) and has normal range (`Colimit.isNormalIn_range_incl`),
so `IsNormalIn.trans` finishes.

No hypothesis of bifiniteness appears: a finite poset is a Plotkin order for
free, `Set.univ ◁ Set.univ` being `IsNormalIn.refl`. -/
theorem exists_normal_embedding_Ainf (P : Type) [PartialOrder P] [Finite P] [OrderBot P] :
    ∃ f : P → Ainf, (∀ a b, f a ≤ f b ↔ a ≤ b) ∧ Set.range f ◁ (Set.univ : Set Ainf) := by
  obtain ⟨k, h, href, hnorm⟩ :=
    exists_stage_embedding (Set.ncard (Set.univ \ ({⊥} : Set P))) ({⊥} : Set P) le_rfl
      (singleton_bot_isNormalIn (Set.mem_univ _)) 0 (fun _ => (⊥ : Stg 0))
      (fun a ha b hb => by
        rw [show a = ⊥ from ha, show b = ⊥ from hb]
        exact iff_of_true le_rfl le_rfl)
      (by
        rw [show (fun _ : P => (⊥ : Stg 0)) '' ({⊥} : Set P) = ({⊥} : Set (Stg 0)) by simp]
        exact singleton_bot_isNormalIn (Set.mem_univ _))
  refine ⟨fun x => incl k (h x), fun a b => (incl_le_incl _ _).trans (href a b), ?_⟩
  have hr : Set.range (fun x => incl k (h x)) = incl k '' Set.range h := by
    rw [← Set.image_univ, ← Set.image_univ, Set.image_image]
  rw [hr]
  exact (isNormalIn_image_range (fun a b => incl_le_incl a b) hnorm).trans
    (isNormalIn_range_incl k)

/-- **`LemThirty.Thm29Normal` at finite bases.** Word for word `Thm29Normal`,
with `Finite ↥(compacts E)` added — a *discharged-at*, not a discharge.

`IsBifinite E` is carried so the statement lines up with `Thm29Normal` and is
**not used**: a finite basis is a Plotkin order whatever `E` is. `[Domain E]` is
likewise not used here; it is load-bearing only in the infinite case, where
`LemThirty.countable_compacts_of_reflects` and
`R45.Agent3.not_thm29NormalWithoutDomain` show its removal makes the statement
false. -/
theorem thm29Normal_finiteBasis :
    ∀ (E : Type) [CompletePartialOrder E] [Domain E], Finite ↥(compacts E) → IsBifinite E →
      ∃ f : ↥(compacts E) → Ainf,
        (∀ a b, f a ≤ f b ↔ a ≤ b) ∧ Set.range f ◁ (Set.univ : Set Ainf) := by
  intro E _ _ hfin _
  exact exists_normal_embedding_Ainf _

/-- **The direction of the change, recorded.** `LemThirty.Thm29Normal` implies the
statement `thm29Normal_finiteBasis` proves, so the added `Finite ↥(compacts E)`
binder only ever *weakens*: what is discharged above is a consequence of the open
claim and not a different sentence.

This is r0046's `stepFunctionsDecidable_of_unconditional` pattern, and it runs the
same way round as that one — from the claim to the restriction — unlike r0047's
`freeCarrier_of_preservesRecursivePresentation`, which runs the other way. It is
the artifact that makes "discharged-at, not discharged" checkable rather than
asserted. -/
theorem thm29Normal_finiteBasis_of_thm29Normal (H : LemThirty.Thm29Normal) :
    ∀ (E : Type) [CompletePartialOrder E] [Domain E], Finite ↥(compacts E) → IsBifinite E →
      ∃ f : ↥(compacts E) → Ainf,
        (∀ a b, f a ≤ f b ↔ a ≤ b) ∧ Set.range f ◁ (Set.univ : Set Ainf) :=
  fun E _ _ _ hE => H E hE

/-- **A four-element chain sits normally in `A∞`.** A closed instance, so the
statement above is on record as inhabited rather than only quantified.

`Fin 4` is used because Mathlib already supplies its `PartialOrder`, `Finite` and
`OrderBot` instances; no property of `Fin 4` beyond those three is asked for, and
`exists_normal_embedding_Ainf` applies verbatim to any finite pointed poset —
including the ones with non-trivial normality constraints, such as the four-point
diamond `⊥ ⊏ a, b ⊏ ⊤`, where dropping either of `a`, `b` makes `↓⊤` fail to be
directed. -/
theorem exists_normal_embedding_chain :
    ∃ f : Fin 4 → Ainf, (∀ a b, f a ≤ f b ↔ a ≤ b) ∧ Set.range f ◁ (Set.univ : Set Ainf) :=
  exists_normal_embedding_Ainf (Fin 4)

end ScottDomains.R49.Agent5
