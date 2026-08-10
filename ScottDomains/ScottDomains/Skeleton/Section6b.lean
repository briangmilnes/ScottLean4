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

`theorem_16` is Theorem 16's **first** conjunct, "`Fp(D)` is an algebraic lattice".
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
`i : Fp(D) ↪ (D → D)` is an embedding — is *not* stated here, and r0032 settled
why: **it is false.** `FinitaryProjectionEmbedding.lean` refutes it by the kernel
for the embedding–projection reading (`ScottHom.IsEmbeddingProjectionPair`, the
reading the paper's own sketch names when it asks one to "verify that `f ↦ N_f`
is a projection"). The witness is a five-element bifinite domain with two
incomparable minimal upper bounds `m₁, m₂` over an incomparable pair `a, b`; for
`f = λx. m₁` there are two incomparable maximal finitary projections below `f`
and no greatest one, while any monotone section would have to produce one. The
refutation is proved against a `D` that satisfies `theorem_16` above, so it isolates
the second conjunct.

The sketch's error is exact, and is recorded as
`Fp.le_iff_fpBasis_subset_stableCompacts`: `p ⊑ f ⟺ im(p) ∩ K(D) ⊆ S_f`. The
paper takes `N_f` to be the least normal set **containing** `S_f`, but what is
needed is a normal set **contained in** it; the two agree only when `S_f` is
itself normal, which holds exactly when `f` is already a finitary projection. So
no choice of `N_f` repairs the argument — the earlier note here, that this was an
unclosed gap in the proof, understated it.

A positive statement is still available and is not proved here: the conjunct
holds whenever every `S_f` contains a greatest normal subposet, which bounded
complete domains satisfy.

`lemma_20` is Lemma 20 in full. Note that its content is the *existence* of the cpo
structure on `Fc(D)`, not a particular one, so — as with `lemma_19` — the statement
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
theorem theorem_16 [Domain α] (h : IsBifinite α) :
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
theorem lemma_20 [Domain α] :
    ∃ C : CompletePartialOrder ↥(Fc α),
      ∀ r s : ↥(Fc α), (letI := C; r ≤ s) ↔ ∀ x, r.val x ≤ s.val x :=
  ⟨Fc.completePartialOrder, fun _ _ => Iff.rfl⟩

end ScottDomains
