import ScottDomains.Lemma28AtU

/-!
# r0038 audit: the duplicate pairs of §7, converted from resemblance to evidence

Round r0038 classifies every theorem of the §7 representability stack
(`UniversalDomain`, `Universality`, `RecursiveDomain`, `Combinator`,
`CombinatorRep`, `Dyadic`, `Atomless`, `PRepresentable`, `PRep`, `PRepFun`,
`PRepSum`, `Lemma28AtU`) and labels each `P`/`S`/`A`/`U`/`D`/`W`. The report is
`reports/r0038-report-from-agent5-to-orchestrator-audit-section-seven.md`.

A `D` label is a claim that two declarations state the same proposition, and a
claim of that kind read off two docstrings is exactly the kind that r0028 got
wrong — it shipped a duplicate declaration that survived 971 green jobs because
nothing ever imported both halves. This module is the check. Each theorem below
is an equality of two *proof terms*; it elaborates only if the two propositions
are definitionally equal, so the kernel, not a reader's eye, decides whether the
pair is a duplicate.

The proofs are all `rfl`, and that is the point: proof irrelevance makes the
proof-term equality trivial **once the two statements are the same type**, so the
whole content of each theorem is in whether it typechecks at all.

This module adds no mathematics. It proves nothing that was not already proved,
introduces no definition, and nothing imports it.

| # | Pair | Verdict |
| - | ---- | ------- |
| 1 | `PRepSum.orderIso_apply_bot` vs Mathlib's `OrderIso.map_bot` | duplicate of a Mathlib lemma |
| 2 | `PRepFun.val_ne_bot_of_ne_bot` vs `PRepSum.val_ne_bot_of_ne_bot` | duplicate, one an instance of the other |
| 3 | `Combinator.liftRangeMap_le_iff` vs `PRep.liftRangeMap_le_iff` | duplicate, `PRep`'s is the general one |
| 4 | `Combinator.liftRangeMap_surjective` vs `PRep.liftRangeMap_surjective` | duplicate, same |
| 5 | `Combinator.liftRange_mem` vs `PRep.liftRange_mem` | duplicate, same |
-/

namespace ScottDomains.Audit.SectionSeven

open ScottDomains

universe u

/-! ## 1. An order isomorphism preserves `⊥` — twice

`PRepSum.orderIso_apply_bot` proves `e ⊥ = ⊥` for `e : A.carrier ≃o A'.carrier`
in five lines. Mathlib v4.32.2 proves it as `OrderIso.map_bot`
(`Mathlib/Order/Hom/Basic.lean`), under `[LE α] [PartialOrder β] [OrderBot α]
[OrderBot β]` — hypotheses a `Cpo` supplies. The development's copy has three
uses, all inside `PRepSum`. -/

theorem orderIso_apply_bot_is_mathlib_map_bot (A A' : Cpo.{u})
    (e : A.carrier ≃o A'.carrier) :
    PRepSum.orderIso_apply_bot A A' e = e.map_bot := rfl

/-! ## 2. "a non-`⊥` point of `im(p)` has a non-`⊥` value" — twice

`PRepSum.val_ne_bot_of_ne_bot` is stated at `projCpo hp` for a bare projection
`p`; `PRepFun.val_ne_bot_of_ne_bot` is stated at `FpImage a` for `a : Fp(U)`.
The two carriers are the same construction — `FpImage a` unfolds to
`projCpo (mem_Fp.mp a.2).isProjection` — so `PRepFun`'s statement is `PRepSum`'s
at that projection, and the two files each built it because r0037 ran them in
worktrees that could not see each other. -/

theorem val_ne_bot_of_ne_bot_pair {U : Type u} [CompletePartialOrder U]
    {a : ↥(Fp U)} {x : (BifiniteUniversal.FpImage a).carrier}
    (h : x ≠ ⊥) :
    PRepFun.val_ne_bot_of_ne_bot h
      = PRepSum.val_ne_bot_of_ne_bot (mem_Fp.mp a.2).isProjection h := rfl

/-! ## 3–5. `im(r⊥) ≅ (im r)⊥`, built twice

`CombinatorRep.lean` (r0034) derives the isomorphism with the index type
`ClosurePoset U`; `PRep.lean` (r0036) re-derives it at a bare `r : ScottHom U U`,
its docstring recording the re-derivation as necessary "since the index type
changes". Measured, it is not: `Combinator.liftFamily r` is by definition
`Combinator.liftMap r.val`, so the closure-indexed statements are the
`ScottHom`-indexed ones at `r.val`, and each of the three theorems below
elaborates by `rfl`.

`PRep`'s versions are the general ones, so this is a `D` pair to be resolved by
deleting the specialization rather than the generalization. -/

section LiftRange

variable {U : Type u} [CompletePartialOrder U] (r : ClosurePoset U)

theorem liftRange_mem_pair (z : WithBot ↥(Set.range ⇑r.val)) :
    Combinator.liftRange_mem r z = PRep.liftRange_mem r.val z := rfl

theorem liftRangeMap_le_iff_pair (z w : WithBot ↥(Set.range ⇑r.val)) :
    Combinator.liftRangeMap_le_iff r z w = PRep.liftRangeMap_le_iff r.val z w := rfl

theorem liftRangeMap_surjective_pair :
    Combinator.liftRangeMap_surjective r = PRep.liftRangeMap_surjective r.val := rfl

end LiftRange

end ScottDomains.Audit.SectionSeven
