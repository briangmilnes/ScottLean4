import ScottDomains.Bifinite
import ScottDomains.FunctionSpaceCountable
import ScottDomains.Projection
-- `Set.Finite.finite_subsets`, used to bound the witness set of Proposition 15.
import Mathlib.Data.Set.Finite.Powerset

/-!
# §6: Proposition 15, Theorem 18, Lemma 19

Gunter & Scott, *Semantic Domains*, §6:

> **Proposition 15** Every bounded-complete domain is bifinite.

> **Theorem 18** If `D` and `D → D` are domains, then `D` is bifinite.

> **Lemma 19** `r : D → D` closure (`r ∘ r = r ⊒ id`) ⟹ `im(r)` is a domain.

**Owned by agent2.** No other file's declarations are edited when these are
proved.

## What is proved here

`prop15` and `lem19` are proved. `thm18` is not: the paper states it without
proof — "The theorem is due to Smyth and its proof may be found in [Smy83a]" —
and the argument it points at is a case analysis of the three configurations of
Figure 3, several pages long. See the comment on `thm18`.

`prop15` follows the paper's own proof. The witness set is `lubClosure u`, the
paper's `N = {x | x is the least upper bound of a finite subset of u}`, and the
three steps are `isCompactElement_of_isLUB_finite` (`N ⊆ K(D)`), the closure of
`N` under bounded least upper bounds, and the observation that `N ∩ ↓x` has a
greatest element and is therefore directed.

`lem19` is stated as the *existence* of a cpo structure on `im(r)`, and the
structure exhibited is `IsClosure.rangeCompletePartialOrder`. It costs less than
the projection analogue `IsProjection.rangeCompletePartialOrder` (r0013): for a
closure the inflationary law `x ⊑ r(x)` gives the upper-bound half of
`lubOfDirected` outright, and idempotence gives the least half, so neither the
continuity of `r` nor a case split on emptiness of the directed set is needed.
-/

namespace ScottDomains

variable {α : Type*}

section Closure

variable [Preorder α] {r : ScottHom α α}

/-- A **closure**: idempotent and *above* the identity — the order dual of
`IsProjection`. Lemma 19 is about these. -/
def IsClosure (r : ScottHom α α) : Prop :=
  (∀ x, r (r x) = r x) ∧ ∀ x, x ≤ r x

theorem IsClosure.idem (h : IsClosure r) (x : α) : r (r x) = r x := h.1 x

theorem IsClosure.le_apply (h : IsClosure r) (x : α) : x ≤ r x := h.2 x

/-- A closure fixes its own image — the dual of `IsProjection.apply_of_mem_range`,
and the half of idempotence that the cpo structure on `im(r)` consumes. -/
theorem IsClosure.apply_of_mem_range (h : IsClosure r) {y : α}
    (hy : y ∈ Set.range ⇑r) : r y = y := by
  obtain ⟨x, rfl⟩ := hy
  exact h.idem x

end Closure

section FiniteUpperBound

variable [Preorder α]

/-- A finite set each of whose members is dominated by a nonempty directed set `s`
has a *single* dominating element inside `s`.

Induction on the finite set: the empty case takes any member of `s`, and the
insertion step feeds the two witnesses — one for the new element, one from the
induction hypothesis — to directedness. This is the step Gunter & Scott write as
"Since `M` is directed, there is some `z ∈ M` which is an upper bound for `v`". -/
theorem exists_upperBound_mem_of_finite {s t : Set α} (hd : DirectedOn (· ≤ ·) s)
    (hne : s.Nonempty) (ht : t.Finite) :
    (∀ y ∈ t, ∃ z ∈ s, y ≤ z) → ∃ z ∈ s, ∀ y ∈ t, y ≤ z := by
  induction t, ht using Set.Finite.induction_on with
  | empty =>
    intro _
    obtain ⟨z, hz⟩ := hne
    exact ⟨z, hz, fun y hy => absurd hy (Set.notMem_empty y)⟩
  | @insert a t _ _ ih =>
    intro h
    obtain ⟨z₁, hz₁, hz₁le⟩ := h a (Set.mem_insert a t)
    obtain ⟨z₂, hz₂, hz₂le⟩ := ih fun y hy => h y (Set.mem_insert_of_mem a hy)
    obtain ⟨z, hz, h₁, h₂⟩ := hd z₁ hz₁ z₂ hz₂
    refine ⟨z, hz, ?_⟩
    rintro y (rfl | hy)
    · exact hz₁le.trans h₁
    · exact (hz₂le y hy).trans h₂

/-- `N` in the proof of Proposition 15: the least upper bounds of those subsets of
`u` that have one. Over a bounded complete cpo and a finite `u` this is the
paper's "least upper bound of a finite subset of `u`", the boundedness condition
being carried by the existence of the least upper bound rather than stated
separately. -/
def lubClosure (u : Set α) : Set α := {c | ∃ v, v ⊆ u ∧ IsLUB v c}

@[simp] theorem mem_lubClosure {u : Set α} {c : α} :
    c ∈ lubClosure u ↔ ∃ v, v ⊆ u ∧ IsLUB v c := Iff.rfl

end FiniteUpperBound

section Statements

variable [CompletePartialOrder α]

/-- The least upper bound of a *finite* set of compact elements is compact. This is
the first paragraph of Gunter & Scott's proof of Proposition 15, and it spends
algebraicity, not bounded completeness: `x = ⨆ M` for the directed set
`M = K(D) ∩ ↓x`, each member of `v` is compact hence dominated by some member of
`M`, `exists_upperBound_mem_of_finite` collapses those witnesses to a single
`z ∈ M`, and `x ⊑ z ⊑ x` forces `x = z ∈ K(D)`. -/
theorem isCompactElement_of_isLUB_finite [IsAlgebraic α] {v : Set α} (hv : v.Finite)
    (hvc : ∀ y ∈ v, IsCompactElement y) {x : α} (hx : IsLUB v x) : IsCompactElement x := by
  have hdir := IsAlgebraic.directedOn_compactsBelow x
  have hMlub := IsAlgebraic.isLUB_compactsBelow x
  have hne := compactsBelow_nonempty x
  obtain ⟨z, hz, hzub⟩ :=
    exists_upperBound_mem_of_finite hdir hne hv fun y hy =>
      hvc y hy (compactsBelow x) x hne hdir hMlub (hx.1 hy)
  exact le_antisymm (hx.2 hzub) hz.2 ▸ hz.1

/-- **Proposition 15.** Every bounded complete domain is bifinite.

Gunter & Scott's proof, verbatim in structure. For a finite `u ⊆ K(D)` the
witness is `N = lubClosure u`:

* `N` is finite, because each of its members is the ambient `sSup` of a subset of
  the finite set `u`;
* `u ⊆ N`, taking singletons;
* `N ⊆ K(D)` by `isCompactElement_of_isLUB_finite`;
* `N ◁ K(D)`: for `x ∈ K(D)` the set `S = N ∩ ↓x` is bounded by `x`, so it has a
  least upper bound; that bound is again in `N`, being the least upper bound of
  `{y ∈ u | y ⊑ z for some z ∈ S}`; and it is `⊑ x`. So `S` has a greatest
  element, which makes it nonempty and directed. -/
theorem prop15 [Domain α] [BoundedComplete α] : IsBifinite α := by
  intro u hu husub
  have hNfin : (lubClosure u).Finite := by
    refine Set.Finite.subset (hu.finite_subsets.image sSup) ?_
    rintro c ⟨v, hvu, hlub⟩
    exact ⟨v, hvu, (isLUB_sSup_of_bddAbove ⟨c, hlub.1⟩).unique hlub⟩
  have huN : u ⊆ lubClosure u := fun k hk =>
    ⟨{k}, Set.singleton_subset_iff.mpr hk, isLUB_singleton⟩
  have hNc : lubClosure u ⊆ compacts α := by
    rintro c ⟨v, hvu, hlub⟩
    exact isCompactElement_of_isLUB_finite (hu.subset hvu)
      (fun y hy => (husub (hvu hy) : IsCompactElement y)) hlub
  refine ⟨lubClosure u, hNfin, ⟨hNc, fun x _ => ?_⟩, huN⟩
  set S : Set α := lubClosure u ∩ Set.Iic x
  have hlub : IsLUB S (sSup S) := isLUB_sSup_of_bddAbove ⟨x, fun _ hy => hy.2⟩
  -- the least upper bound of `S` is again a least upper bound of a subset of `u`
  have hmemN : sSup S ∈ lubClosure u := by
    refine ⟨{y ∈ u | ∃ z ∈ S, y ≤ z}, fun _ hy => hy.1, ⟨?_, ?_⟩⟩
    · rintro y ⟨-, z, hz, hyz⟩
      exact hyz.trans (hlub.1 hz)
    · intro b hb
      refine hlub.2 fun z hz => ?_
      obtain ⟨v, hvu, hvlub⟩ := hz.1
      exact hvlub.2 fun y hy => hb ⟨hvu hy, z, hz, hvlub.1 hy⟩
  have hmemS : sSup S ∈ S := ⟨hmemN, hlub.2 fun _ hy => hy.2⟩
  exact ⟨⟨sSup S, hmemS⟩, fun a ha b hb => ⟨sSup S, hmemS, hlub.1 ha, hlub.1 hb⟩⟩

/-- **Theorem 18.** If `D` and `D → D` are domains, then `D` is bifinite.

The hypothesis is on the *function space* being a domain, which is what
Theorem 7 supplies under bounded completeness — so this is the converse
direction and does not follow from it.

**Not proved.** Gunter & Scott state the theorem with no proof at all: "The
theorem is due to Smyth and its proof may be found in [Smy83a]. It is carried out
by analyzing each of the cases pictured in Figure 3 and showing that if `D → D`
is not a domain, then `D` cannot be bifinite." The three configurations of
Figure 3 are (a) a finite set with no complete set of minimal upper bounds,
(b) one whose complete set of minimal upper bounds is infinite, and (c) one whose
iterated minimal-upper-bound closure `U^∞(u)` is infinite; the argument
constructs, from each, a continuous `D → D` witnessing failure of algebraicity of
the function space. None of the three constructions is in this development:
`MUB(u)`, completeness of a set of minimal upper bounds, and `U^∞` are not
defined anywhere in `ScottDomains/`, and the contrapositive needs a compact
element of `ScottHom α α` exhibited for each configuration. -/
theorem thm18 [Domain α] [Domain (ScottHom α α)] : IsBifinite α := by
  sorry

section RangeCpo

variable {r : ScottHom α α}

/-- The defining property of the cpo structure on `im(r)`: for a directed `s` in
the image, `r (⨆ s)` is the least upper bound of `s` *in the image*.

Both halves are cheap, and neither uses continuity of `r`:

* upper bound — `a ⊑ ⨆ s` in the ambient order, and `⨆ s ⊑ r(⨆ s)` because a
  closure is inflationary;
* least — if `b` bounds `s` then `⨆ s ⊑ b`, so `r(⨆ s) ⊑ r(b) = b`, the last
  equation because `b` lies in the image and `r` is idempotent.

The empty directed set needs no separate treatment: both halves are vacuous or
go through `DirectedOn.sSup_le` on `∅`. This is where the closure case is
cheaper than `IsProjection.apply_sSup_of_directed`, which must handle `s = ∅` by
hand because `p ⊥ = ⊥` while `r ⊥` is in general *not* `⊥`. -/
theorem IsClosure.isLUB_range (hr : IsClosure r) {s : Set ↥(Set.range ⇑r)}
    (hs : DirectedOn (· ≤ ·) s) :
    IsLUB s (⟨r (sSup (Subtype.val '' s)), Set.mem_range_self _⟩ : ↥(Set.range ⇑r)) := by
  have hdir := ScottHom.directedOn_val_image (p := r) hs
  constructor
  · intro a ha
    show a.val ≤ r (sSup (Subtype.val '' s))
    exact (hdir.le_sSup ⟨a, ha, rfl⟩).trans (hr.le_apply _)
  · intro b hb
    show r (sSup (Subtype.val '' s)) ≤ b.val
    calc r (sSup (Subtype.val '' s))
        ≤ r b.val := r.monotone (hdir.sSup_le (by rintro _ ⟨a, ha, rfl⟩; exact hb ha))
      _ = b.val := hr.apply_of_mem_range b.2

/-- **The image of a closure is a cpo.** Suprema are computed in the ambient order
and pushed through `r`, which lands in the range by construction; the least
element is `r ⊥`, not `⊥`. -/
@[reducible] def IsClosure.rangeCompletePartialOrder (hr : IsClosure r) :
    CompletePartialOrder ↥(Set.range ⇑r) :=
  { (inferInstance : PartialOrder ↥(Set.range ⇑r)) with
    sSup := fun s => ⟨r (sSup (Subtype.val '' s)), Set.mem_range_self _⟩
    bot := ⟨r ⊥, Set.mem_range_self ⊥⟩
    bot_le := fun b => by
      show r ⊥ ≤ b.val
      calc r ⊥ ≤ r b.val := r.monotone bot_le
        _ = b.val := hr.apply_of_mem_range b.2
    lubOfDirected := fun _ hs => hr.isLUB_range hs }

end RangeCpo

/-- **Lemma 19.** If `r : D → D` is a closure, then `im(r)` is a domain.

Stated as the existence of the cpo structure on the image rather than by first
building it — that construction is part of the proof, and fixing it here would
prejudge how it is done. Compare `IsProjection.rangeCompletePartialOrder`
(r0013), which is the projection analogue and a likely model. -/
theorem lem19 (r : ScottHom α α) (_hr : IsClosure r) :
    ∃ _ : CompletePartialOrder ↥(Set.range ⇑r), True :=
  ⟨_hr.rangeCompletePartialOrder, trivial⟩

end Statements

end ScottDomains
