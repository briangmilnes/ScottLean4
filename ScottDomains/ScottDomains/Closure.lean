-- `ScottHom.directedOn_val_image`, used by `IsClosure.isLUB_range`, lives in
-- `Projection.lean` (it is stated for an arbitrary endomorphism's range, not only
-- a projection's); that import subsumes `ScottDomains.ScottHom`.
import ScottDomains.Projection

/-!
# Closures on a cpo: the shared `IsClosure` API

Gunter & Scott, *Semantic Domains*, §7.1 defines a **finitary closure** as a
continuous `r : D → D` with `r ∘ r = r ⊒ id` whose image is a domain, and §6.2's
Lemma 19 says the image condition is automatic over a domain. This file carries
the order-theoretic API for `r ∘ r = r ⊒ id` — the definition, the cpo structure
on `im(r)`, and the two facts about ambient suprema that the closure-poset
constructions need.

## Why it is its own module

These declarations lived in `Skeleton/Section6.lean` until r0042. That placement
put `Skeleton.Section6` inside the import cone of `ScottDomains.JungFinite` —

    JungFinite → Section62 → FinitaryProjectionEmbedding
               → Skeleton.Section6b → FinitaryProjectionPoset → Skeleton.Section6

— because `FinitaryProjectionPoset.lean` imports the skeleton file solely for
`IsClosure`. `Skeleton/Section6.lean` states Theorem 18, whose proof is
`ScottDomains.Thm18.theorem_18_of_jung_theorem_1_37_and_jung_corollary_1_36` in `ScottDomains/Thm18.lean`,
which imports `JungFinite`; so as long as the skeleton file owned this API,
citing that proof from Theorem 18 was an import cycle and `lake` rejected it.
Measured by `scripts/a5-import-cone.sh`: before the move, `Skeleton.Section6` was
one of the 22 modules in `JungFinite`'s cone.

Moving the API out also restores the `Skeleton/` convention the rest of the
development follows — a skeleton module states the paper's numbered results and
names the declaration discharging each, and owns no shared API. What stays in
`Skeleton/Section6.lean` is Proposition 15, Theorem 18, Lemma 19 and Proposition
15's own proof helpers.

The declarations are unchanged: same names, same `ScottDomains` namespace, same
proofs. `Skeleton/Section6.lean` imports this file, so every module that reached
these names through the skeleton still does.
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

section RangeCpo

variable [CompletePartialOrder α] {r : ScottHom α α}

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

/-! ## Shared closure API

Two lemmas that `FinitaryProjectionPoset.lean` (Theorem 16, Lemma 20) and
`UniversalDomain.lean` (Theorem 22, Lemma 23) both need. They were written twice
in round r0028, once in each of those modules, under the same names — a clash
invisible to `lake build`, because no module imported both, and one that surfaced
the moment anything did. `IsClosure` is defined here, so this is their home; both
modules import this file and reach them unqualified. -/

section SharedClosureApi

variable [CompletePartialOrder α] {r : ScottHom α α}

/-- A continuous closure fixes the ambient supremum of a nonempty directed subset
of its image. Contrast `IsProjection.apply_sSup_of_directed`, which needs no
nonemptiness because `p ⊥ = ⊥` while `r ⊥` in general is not `⊥`. -/
theorem IsClosure.apply_sSup_of_directed (hr : IsClosure r) {D : Set α}
    (hne : D.Nonempty) (hD : DirectedOn (· ≤ ·) D) (hsub : D ⊆ Set.range ⇑r) :
    r (sSup D) = sSup D := by
  have hlub : IsLUB (⇑r '' D) (r (sSup D)) := r.scottContinuous hne hD hD.isLUB_sSup
  have himg : ⇑r '' D = D := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hr.apply_of_mem_range (hsub hx)]
      exact hx
    · exact fun hy => ⟨y, hy, hr.apply_of_mem_range (hsub hy)⟩
  rw [himg] at hlub
  exact hlub.unique hD.isLUB_sSup

/-- The pointwise supremum of a nonempty directed set of closures is a closure.

Only idempotence needs an argument. Continuity of `r` turns `r ((⨆d) x)` into
`⨆_{r' ∈ d} r (r' x)`, and directedness collapses each term: choosing `r'' ∈ d`
above both `r` and `r'` gives `r (r' x) ⊑ r'' (r'' x) = r'' x ⊑ (⨆d) x`. -/
theorem isClosure_sSup {d : Set (ScottHom α α)} (hne : d.Nonempty)
    (hd : DirectedOn (· ≤ ·) d) (hcl : ∀ r ∈ d, IsClosure r) : IsClosure (sSup d) := by
  have hev : ∀ x : α, DirectedOn (· ≤ ·) ((fun f : ScottHom α α => f x) '' d) :=
    fun x => ScottHom.directedOn_eval_image hd x
  have hle : ∀ x : α, x ≤ (sSup d) x := by
    intro x
    obtain ⟨r, hr⟩ := hne
    rw [ScottHom.coe_sSup_of_directed hd x]
    exact ((hcl r hr).le_apply x).trans ((hev x).le_sSup ⟨r, hr, rfl⟩)
  refine ⟨fun x => le_antisymm ?_ (hle _), hle⟩
  rw [ScottHom.coe_sSup_of_directed hd ((sSup d) x)]
  refine (hev _).sSup_le ?_
  rintro _ ⟨r, hr, rfl⟩
  have hcont : IsLUB (⇑r '' ((fun f : ScottHom α α => f x) '' d)) (r ((sSup d) x)) := by
    have h := r.scottContinuous (hne.image _) (hev x) (hev x).isLUB_sSup
    rwa [← ScottHom.coe_sSup_of_directed hd x] at h
  refine hcont.2 ?_
  rintro _ ⟨_, ⟨r', hr', rfl⟩, rfl⟩
  obtain ⟨r'', hr'', hrr, hr'r⟩ := hd r hr r' hr'
  calc r (r' x) ≤ r'' (r' x) := hrr (r' x)
    _ ≤ r'' (r'' x) := r''.monotone (hr'r x)
    _ = r'' x := (hcl r'' hr'').idem x
    _ ≤ (sSup d) x := by
        rw [ScottHom.coe_sSup_of_directed hd x]
        exact (hev x).le_sSup ⟨r'', hr'', rfl⟩

end SharedClosureApi

end ScottDomains
