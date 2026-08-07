import ScottDomains.FinitaryProjectionPoset

/-!
# §6.2 and §7.1: Theorem 16 and Lemma 20

Gunter & Scott, *Semantic Domains*, quoted from the source PDF:

> **Theorem 16** If `D` is bifinite, then the poset `Fp(D)` of finitary
> projections on `D` is an algebraic lattice and the inclusion map
> `i : Fp(D) ↪ (D → D)` is an embedding.

> **Lemma 20** If `D` is a domain, then `Fc(D)` is a cpo.

**Owned by agent3.** The constructions both statements quantify over are in
`ScottDomains/FinitaryProjectionPoset.lean`; this file holds only the two
numbered statements, so that the round's other agents can edit their own skeleton
files without touching this one.

## What is proved

Both are proved, with no `sorry`.

`thm16` is Theorem 16's **first** conjunct, "`Fp(D)` is an algebraic lattice".
Mathlib's name for that concept is a `CompleteLattice` that is
`IsCompactlyGenerated`, and it fits without adjustment: Mathlib's
`IsCompactElement` is the very predicate this development already uses for
`K(D)` — `ScottDomains.WayBelow` is built from it — so "compactly generated"
here means exactly "every finitary projection is the least upper bound of the
finitary projections with a finite basis". The `CompleteLattice` cannot be an
`instance`, because `IsBifinite` is a `def`-level proposition and not a class, so
the statement is existential, with a conjunct pinning the lattice order to the
pointwise order of `D → D`; without that conjunct the existential would be
satisfied by any complete lattice structure whatever and would say nothing.

The **second** conjunct of the paper's sentence — that the inclusion
`i : Fp(D) ↪ (D → D)` is an embedding — is *not* stated here. It is a separate
claim about an embedding–projection pair, and the paper's sketch of it ("Let
`S_f = {x ∈ K(D) | x ⊑ f(x)}` … there is a least set `N_f` with
`S_f ⊆ N_f ◁ K(D)`") does not obviously produce the projection half `i ∘ s ⊑ id`:
`S_f` is in general **not** normal, so `N_f` is strictly larger, and a minimal
upper bound `m` of `a, b ∈ S_f` lies in `N_f` without satisfying `m ⊑ f(m)`.
Recording the claim with a guessed proof strategy would be worse than recording
the gap, so it is recorded here.

`lem20` is Lemma 20 in full. Note that its content is the *existence* of the cpo
structure on `Fc(D)`, not a particular one, so — as with `lem19` — the statement
is existential and `Fc.completePartialOrder` is the witness.
-/

namespace ScottDomains

variable {α : Type*} [CompletePartialOrder α]

/-- **Theorem 16 (first conjunct).** If `D` is bifinite, then `Fp(D)`, the
finitary projections on `D` under the pointwise order, is an algebraic lattice —
a complete lattice in which every element is the supremum of the compact elements
below it.

The two components of the witness are `Fp.completeLattice` (meets are
intersections of bases, normal by `isNormalIn_sInter`, which is where
bifiniteness is spent) and `Fp.isCompactlyGenerated` (the compact elements are
the projections `p_N` with `N` finite, and `normalClosure` produces enough of
them). The middle conjunct says the lattice order is the pointwise order, and
holds by `Iff.rfl` because `completeLatticeOfInf` splices in the ambient
`PartialOrder` rather than deriving a new one. -/
theorem thm16 [Domain α] (h : IsBifinite α) :
    ∃ L : CompleteLattice ↥(Fp α),
      (∀ p q : ↥(Fp α), (letI := L; p ≤ q) ↔ ∀ x, p.val x ≤ q.val x) ∧
      @IsCompactlyGenerated _ L :=
  ⟨Fp.completeLattice h, fun _ _ => Iff.rfl, Fp.isCompactlyGenerated h⟩

/-- **Lemma 20.** If `D` is a domain, then `Fc(D)`, the finitary closures on `D`
under the pointwise order, is a cpo.

The least element is `id`, and the least upper bound of a directed family is the
pointwise supremum — a closure by `isClosure_sSup`, and a *finitary* closure
because Lemma 19 at full strength (`IsClosure.domain_range`) makes the image of
every closure over a domain a domain. The second conjunct records that the cpo
order is the pointwise order. -/
theorem lem20 [Domain α] :
    ∃ C : CompletePartialOrder ↥(Fc α),
      ∀ r s : ↥(Fc α), (letI := C; r ≤ s) ↔ ∀ x, r.val x ≤ s.val x :=
  ⟨Fc.completePartialOrder, fun _ _ => Iff.rfl⟩

end ScottDomains
