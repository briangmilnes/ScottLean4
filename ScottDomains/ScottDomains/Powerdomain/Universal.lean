import ScottDomains.UniversalDomain
-- `theorem_21`, `IsRepresentable₂.diag` and `IsSolvable`, for the corollary `D ≅ D × D`
-- at the end of the file. Not reachable from `UniversalDomain`.
import ScottDomains.RecursiveDomain

/-!
# §7.1: the product operator is representable over `P N`

Gunter & Scott, *Semantic Domains*, §7.1, quoted from the source PDF:

> A similar construction can be carried out for the product operator. Suppose
>
> > `×⁻ : P N → (P N × P N)`
> > `×⁺ : (P N × P N) → P N`
>
> such that `×⁻ ∘ ×⁺ = id` and `×⁺ ∘ ×⁻ ⊒ id`. For `r, s ∈ Fc(P N)` define
>
> > `R×(r, s) = ×⁺ ∘ (r × s) ∘ ×⁻`
>
> We leave for the reader the demonstration that this makes sense and `R×`
> represents the product operator.

`isRepresentable_prod` is that demonstration. It is the second of the two
hypotheses of **Lemma 24** — "Let `U` be a non-trivial cpo. If the product and
function space operators can be represented over `U`, then there are non-trivial
domains `D` and `E` such that `E ≅ E × E` and `D ≅ D → E`" — whose first
hypothesis is `ScottDomains.lemma_23`.

## The generic representation scheme

The paper's `R→` (Lemma 23, `UniversalDomain.lean`) and its `R×` are the same
construction with two parameters changed: the cpo `V` that the closure pair
`(→⁻, →⁺)` / `(×⁻, ×⁺)` lands in, and the operator `V → V` conjugated by that
pair. `repOf`, `isClosure_repOf`, `scottContinuous_repOf` and `repRangeOrderIso`
below are that construction stated once, for an arbitrary `V` and an arbitrary
continuous family `C : Fc(U) × Fc(U) → (V → V)` of closures. `UniversalDomain.lean`
is not edited: `lemma_23` keeps its own specialized copies, and the generic versions
are used only from here.

## What Lemma 28 and Lemma 30 actually say

The plan for this round described Lemma 28 as "the operators `→, ×, ⊗, +, ()⊥,
()], ()[` are representable over the universal domain `U`" with `U = P N`, and
Lemma 30 as a universal/closure property of the powerdomains from §5.3. Neither
description matches the paper. Quoting §7.3 and §7.4:

> **Lemma 28** The following operators are representable over `U`: `→`, `⇸`, `×`,
> `⊗`, `+`, `⊕`, `()⊥`, `()♯`, `()♭`.

> **Lemma 30** The following operators are p-representable over `V`: `→`, `⇸`,
> `×`, `⊗`, `+`, `⊕`, `()⊥`, `()♯`, `()♭`, `()♮`.

Three differences from the plan's reading, each of which changes what has to be
built:

* Neither lemma is about `P N`. Lemma 28's `U` is §7.3's domain of ideals over
  the finite non-empty unions of half-open intervals `[r, t)` of dyadic rationals
  in `[0, 1)`, ordered by superset; Lemma 30's `V` is §7.4's bifinite universal
  domain, the fixed point of `D ↦ D⁺` supplied by Theorem 29. The development
  constructs neither.
* Both lemmas are about **p-representability** — the diagram is drawn with
  `Fp(U)`, the poset of finitary *projections*, not `Fc(U)`, the finitary
  *closures*. §7.3 defines the notion afresh: "let us say that an operator `F` on
  cpo's is p-representable over a cpo `U` if and only if there is a continuous
  function `R_F` which completes the following diagram (up to isomorphism)", with
  `Fp(U)` on the bottom row. `IsRepresentable` and `IsRepresentable₂`
  (`UniversalDomain.lean`) are the `Fc(U)` notion, so they state Lemma 28 for no
  value of `U`.
* Consequently Lemma 23 is *not* Lemma 28's function-space conjunct. The paper
  says only that the two proofs resemble each other: "The proof that `→` is
  representable over `U` is almost identical to the proof we gave above that it
  is representable over `P N`."

§5.3 ("Universal and closure properties") is a section of §5 on powerdomains and
contains no lemma numbered 30.

The result proved here is therefore *not* a conjunct of Lemma 28. It is §7.1's
own product remark over `P N`, which is what Lemma 24 consumes.

## Why `+` is not on this list

Over `P N` it cannot be. §7.1: "Unfortunately, there is no representation for the
operator `F(X) = X + X` over `P N`", and §7.3 opens by naming that failure as the
reason the paper builds a second universal domain at all. So of the plan's
`×, ⊗, +, ()⊥`, the `+` conjunct is false over `P N` as the paper states it, and
is one of the two motivations for §7.3.
-/

namespace ScottDomains.PowerdomainRep

universe u

/-! ## A representation scheme for one conjugating pair

Everything in this section is `UniversalDomain.lean`'s `repFun`,
`isClosure_repFun`, `scottContinuous_repClosure` and `repRangeOrderIso` with
`ScottHom U U` generalized to an arbitrary cpo `V` and `compHom r s` generalized
to an arbitrary closure `C : V → V`. The proofs are unchanged; only the types
are wider. -/

section Generic

variable {U V : Type u} [CompletePartialOrder U] [CompletePartialOrder V]

/-- `R(C) = gr ∘ C ∘ fn`, continuous as a composite of three continuous maps.
At `V = U → U`, `fn = →⁻`, `gr = →⁺` and `C = (s, r)` this is Lemma 23's
`repFun`; at `V = U × U`, `fn = ×⁻`, `gr = ×⁺` and `C = r × s` it is `R×`. -/
def repOf (fn : ScottHom U V) (gr : ScottHom V U) (C : ScottHom V V) : ScottHom U U :=
  ⟨⇑gr ∘ ⇑C ∘ ⇑fn,
    ScottContinuous.comp (ScottContinuous.comp fn.scottContinuous C.scottContinuous)
      gr.scottContinuous⟩

@[simp] theorem repOf_apply (fn : ScottHom U V) (gr : ScottHom V U) (C : ScottHom V V) (x : U) :
    repOf fn gr C x = gr (C (fn x)) := rfl

variable {fn : ScottHom U V} {gr : ScottHom V U}

/-- `R(C)` is a closure whenever `C` is: `fn ∘ gr = id` deletes the inner pair and
idempotence of `C` collapses the rest, exactly as in the paper's displayed
computation for `R→`. -/
theorem isClosure_repOf (hfg : ∀ y, fn (gr y) = y) (hgf : ∀ x, x ≤ gr (fn x))
    {C : ScottHom V V} (hC : IsClosure C) : IsClosure (repOf fn gr C) := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · show gr (C (fn (gr (C (fn x))))) = gr (C (fn x))
    rw [hfg, hC.idem]
  · exact (hgf x).trans (gr.monotone (hC.le_apply (fn x)))

/-- `fn` carries `im(R(C))` into `im(C)`. -/
theorem fn_mem_range_of_mem_range_repOf (hfg : ∀ y, fn (gr y) = y) {C : ScottHom V V} {x : U}
    (hx : x ∈ Set.range ⇑(repOf fn gr C)) : fn x ∈ Set.range ⇑C := by
  obtain ⟨y, rfl⟩ := hx
  refine Set.mem_range.mpr ⟨fn y, ?_⟩
  show C (fn y) = fn (gr (C (fn y)))
  rw [hfg]

/-- `gr` carries `im(C)` into `im(R(C))`. -/
theorem gr_mem_range_repOf (hfg : ∀ y, fn (gr y) = y) {C : ScottHom V V} {F : V}
    (hF : F ∈ Set.range ⇑C) : gr F ∈ Set.range ⇑(repOf fn gr C) := by
  obtain ⟨G, rfl⟩ := hF
  refine Set.mem_range.mpr ⟨gr G, ?_⟩
  show gr (C (fn (gr G))) = gr (C G)
  rw [hfg]

/-- The paper's "we need only show that `(→⁺ ∘ →⁻)(x) = x` for each
`x = R→(r,s)(x)`", at this generality. -/
theorem gr_fn_of_mem_range_repOf (hfg : ∀ y, fn (gr y) = y) {C : ScottHom V V} {x : U}
    (hx : x ∈ Set.range ⇑(repOf fn gr C)) : gr (fn x) = x := by
  obtain ⟨y, rfl⟩ := hx
  show gr (fn (gr (C (fn y)))) = gr (C (fn y))
  rw [hfg]

/-- `im(R(C)) ≅ im(C)`, by `fn` and `gr` restricted. -/
def repRangeOrderIso (hfg : ∀ y, fn (gr y) = y) (C : ScottHom V V) :
    ↥(Set.range ⇑(repOf fn gr C)) ≃o ↥(Set.range ⇑C) :=
  Equiv.toOrderIso
    { toFun := fun x => ⟨fn x.val, fn_mem_range_of_mem_range_repOf hfg x.2⟩
      invFun := fun F => ⟨gr F.val, gr_mem_range_repOf hfg F.2⟩
      left_inv := fun x => Subtype.ext (gr_fn_of_mem_range_repOf hfg x.2)
      right_inv := fun F => Subtype.ext (hfg F.val) }
    (fun _ _ h => fn.monotone h) (fun _ _ h => gr.monotone h)

/-- **`(r, s) ↦ R(C(r,s))` is continuous.** The upper-bound half is monotonicity
of `C` followed by monotonicity of `gr`; the least half feeds the pointwise least
upper bound of `C` at the argument `fn x` into the continuity of `gr`.

The two hypotheses on `C` are exactly what the argument spends: `hCmono` for the
upper-bound half and `hCeval` — pointwise Scott continuity of `C`, which is how
`isLUB_compHom_of_isLUB` states the same fact for `R→` — for the least half. -/
theorem scottContinuous_repOf (hfg : ∀ y, fn (gr y) = y) (hgf : ∀ x, x ≤ gr (fn x))
    {C : ClosurePoset U × ClosurePoset U → ScottHom V V}
    (hCcl : ∀ p, IsClosure (C p))
    (hCmono : ∀ {p q : ClosurePoset U × ClosurePoset U}, p ≤ q → C p ≤ C q)
    (hCeval : ∀ {d : Set (ClosurePoset U × ClosurePoset U)}, d.Nonempty →
      DirectedOn (· ≤ ·) d → ∀ {a : ClosurePoset U × ClosurePoset U}, IsLUB d a →
      ∀ y : V, IsLUB ((fun p => C p y) '' d) (C a y)) :
    ScottContinuous (fun p : ClosurePoset U × ClosurePoset U =>
      (⟨repOf fn gr (C p), isClosure_repOf hfg hgf (hCcl p)⟩ : ClosurePoset U)) := by
  intro d hne hd a ha
  refine ⟨?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩ x
    exact gr.monotone (hCmono (ha.1 hp) (fn x))
  · intro u hu x
    have hE := hCeval hne hd ha (fn x)
    have hEdir : DirectedOn (· ≤ ·) ((fun p : ClosurePoset U × ClosurePoset U =>
        C p (fn x)) '' d) := by
      rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
      obtain ⟨c, hc, hpc, hqc⟩ := hd p hp q hq
      exact ⟨_, ⟨c, hc, rfl⟩, hCmono hpc (fn x), hCmono hqc (fn x)⟩
    refine (gr.scottContinuous (hne.image _) hEdir hE).2 ?_
    rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact hu ⟨p, hp, rfl⟩ x

end Generic

/-! ## `P N × P N` is a countably based algebraic lattice

Theorem 22 is applied at `L = P N × P N`, so its three hypotheses have to be
discharged there. Algebraicity and countability of the basis both reduce to
`isCompactElement_prod_iff` (`Skeleton/Lemma17.lean`), which says `K(D × E) =
K(D) × K(E)`; lattice completeness is coordinatewise, because `Prod.supSet` takes
suprema coordinatewise and `P N` is a complete lattice. -/

section ProductDomain

variable {α β : Type*} [CompletePartialOrder α] [CompletePartialOrder β]

/-- `K(D × E) = K(D) × K(E)`, in set form. -/
theorem compacts_prod : compacts (α × β) = compacts α ×ˢ compacts β :=
  Set.ext fun _ => isCompactElement_prod_iff

/-- The compact approximants of a pair are the pairs of compact approximants. -/
theorem compactsBelow_prod (x : α × β) :
    compactsBelow x = compactsBelow x.1 ×ˢ compactsBelow x.2 := by
  ext p
  simp only [mem_compactsBelow, Set.mem_prod, isCompactElement_prod_iff, Prod.le_def]
  tauto

/-- **`D × E` is algebraic when `D` and `E` are.** Directedness is coordinatewise;
the least upper bound is `isLUB_prod` after `Set.fst_image_prod` and
`Set.snd_image_prod` strip the rectangle, whose two nonemptiness side conditions
are `⊥ ∈ compactsBelow`. -/
theorem isAlgebraic_prod [IsAlgebraic α] [IsAlgebraic β] : IsAlgebraic (α × β) where
  directedOn_compactsBelow x := by
    rw [compactsBelow_prod]
    rintro p hp q hq
    obtain ⟨a, ha, hpa, hqa⟩ := IsAlgebraic.directedOn_compactsBelow x.1 p.1 hp.1 q.1 hq.1
    obtain ⟨b, hb, hpb, hqb⟩ := IsAlgebraic.directedOn_compactsBelow x.2 p.2 hp.2 q.2 hq.2
    exact ⟨(a, b), ⟨ha, hb⟩, ⟨hpa, hpb⟩, ⟨hqa, hqb⟩⟩
  isLUB_compactsBelow x := by
    have hne₁ : (compactsBelow x.1).Nonempty := ⟨⊥, isCompactElement_bot, bot_le⟩
    have hne₂ : (compactsBelow x.2).Nonempty := ⟨⊥, isCompactElement_bot, bot_le⟩
    rw [compactsBelow_prod, isLUB_prod, Set.fst_image_prod _ hne₂, Set.snd_image_prod hne₁]
    exact ⟨IsAlgebraic.isLUB_compactsBelow x.1, IsAlgebraic.isLUB_compactsBelow x.2⟩

/-- **`D × E` is a domain when `D` and `E` are.** Countability of the basis is
`Set.Countable.prod` against `compacts_prod`. Stated as a theorem, not an
instance: it is needed only to instantiate Theorem 22 at `P N × P N`, and a
`Domain` instance on every product would be resolved on every product goal in the
development. -/
theorem domain_prod [Domain α] [Domain β] : Domain (α × β) :=
  { __ := isAlgebraic_prod
    countable_compacts := by
      rw [compacts_prod]
      exact (Domain.countable_compacts (α := α)).prod (Domain.countable_compacts (α := β)) }

end ProductDomain

/-- `P N × P N` is a complete lattice: `sSup` in the product cpo is coordinatewise
(`Prod.supSet`), and in `P X` every set has a least upper bound. This is the
`hsup` hypothesis of `theorem_22`. -/
theorem isLUB_sSup_prod_set {X Y : Type*} (t : Set (Set X × Set Y)) : IsLUB t (sSup t) :=
  isLUB_prod.mpr ⟨isLUB_sSup _, isLUB_sSup _⟩

/-! ## `r × s`, the operator conjugated by `(×⁻, ×⁺)` -/

section ProdMap

variable {U : Type*} [CompletePartialOrder U]

/-- `(r × s)(x, y) = (r x, s y)`, Gunter & Scott's `r × s`. -/
def prodMap (r s : ScottHom U U) : ScottHom (U × U) (U × U) :=
  ⟨fun p => (r p.1, s p.2),
    ScottContinuous.prodMk (ScottContinuous.comp ScottContinuous.fst r.scottContinuous)
      (ScottContinuous.comp ScottContinuous.snd s.scottContinuous)⟩

@[simp] theorem prodMap_apply (r s : ScottHom U U) (p : U × U) :
    prodMap r s p = (r p.1, s p.2) := rfl

/-- `r × s` is a closure on `D × D` whenever `r` and `s` are closures on `D` —
both laws hold coordinatewise, which is the whole content of the paper's "we
leave for the reader the demonstration that this makes sense". -/
theorem isClosure_prodMap {r s : ScottHom U U} (hr : IsClosure r) (hs : IsClosure s) :
    IsClosure (prodMap r s) := by
  refine ⟨fun p => ?_, fun p => ⟨hr.le_apply p.1, hs.le_apply p.2⟩⟩
  show (r (r p.1), s (s p.2)) = (r p.1, s p.2)
  rw [hr.idem, hs.idem]

/-- `r × s` is monotone in `(r, s)`, pointwise and coordinatewise. -/
theorem prodMap_mono {r r' s s' : ScottHom U U} (hr : r ≤ r') (hs : s ≤ s') :
    prodMap r s ≤ prodMap r' s' :=
  fun p => ⟨hr p.1, hs p.2⟩

/-- The exchange step behind continuity of `R×`: `r × s` applied to a fixed
argument carries a least upper bound in `Fc(U) × Fc(U)` to one in `U × U`.

Unlike the function-space case (`isLUB_compHom_of_isLUB`), directedness is not
spent on putting the two coordinates back on the diagonal: `r × s` uses `r` and
`s` on *separate* coordinates, so `isLUB_prod` splits the goal into two
independent evaluations. Directedness is still needed, but only to move the least
upper bound out of the subtype `Fc(U)` and into `U → U`
(`isLUB_val_image_of_isLUB`). -/
theorem isLUB_prodMap_of_isLUB {d : Set (ClosurePoset U × ClosurePoset U)}
    (hne : d.Nonempty) (hd : DirectedOn (· ≤ ·) d) {a : ClosurePoset U × ClosurePoset U}
    (ha : IsLUB d a) (y : U × U) :
    IsLUB ((fun p : ClosurePoset U × ClosurePoset U => prodMap p.1.val p.2.val y) '' d)
      (prodMap a.1.val a.2.val y) := by
  have hdfst : DirectedOn (· ≤ ·) (Prod.fst '' d) := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    obtain ⟨c, hc, hpc, hqc⟩ := hd p hp q hq
    exact ⟨c.1, ⟨c, hc, rfl⟩, hpc.1, hqc.1⟩
  have hdsnd : DirectedOn (· ≤ ·) (Prod.snd '' d) := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    obtain ⟨c, hc, hpc, hqc⟩ := hd p hp q hq
    exact ⟨c.2, ⟨c, hc, rfl⟩, hpc.2, hqc.2⟩
  have h₁ : IsLUB ((fun p : ClosurePoset U × ClosurePoset U => p.1.val) '' d) a.1.val := by
    have := isLUB_val_image_of_isLUB (hne.image _) hdfst (isLUB_prod.mp ha).1
    rwa [Set.image_image] at this
  have h₂ : IsLUB ((fun p : ClosurePoset U × ClosurePoset U => p.2.val) '' d) a.2.val := by
    have := isLUB_val_image_of_isLUB (hne.image _) hdsnd (isLUB_prod.mp ha).2
    rwa [Set.image_image] at this
  have hd₁ : DirectedOn (· ≤ ·)
      ((fun p : ClosurePoset U × ClosurePoset U => p.1.val) '' d) := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    obtain ⟨c, hc, hpc, hqc⟩ := hd p hp q hq
    exact ⟨c.1.val, ⟨c, hc, rfl⟩, hpc.1, hqc.1⟩
  have hd₂ : DirectedOn (· ≤ ·)
      ((fun p : ClosurePoset U × ClosurePoset U => p.2.val) '' d) := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    obtain ⟨c, hc, hpc, hqc⟩ := hd p hp q hq
    exact ⟨c.2.val, ⟨c, hc, rfl⟩, hpc.2, hqc.2⟩
  refine isLUB_prod.mpr ⟨?_, ?_⟩
  · have := ScottHom.isLUB_eval_image_of_isLUB hd₁ h₁ y.1
    rw [Set.image_image] at this
    simpa [Set.image_image] using this
  · have := ScottHom.isLUB_eval_image_of_isLUB hd₂ h₂ y.2
    rw [Set.image_image] at this
    simpa [Set.image_image] using this

/-! ### `im(r × s) ≅ im(r) × im(s)`

The range of `r × s` is the rectangle `im(r) × im(s)`, so the isomorphism is the
subtype-of-a-product / product-of-subtypes shuffle and every one of its four
equations is `rfl`. -/

/-- The first coordinate of a point of `im(r × s)` lies in `im(r)`. -/
theorem fst_mem_range_of_mem_range_prodMap {r s : ScottHom U U} {p : U × U}
    (hp : p ∈ Set.range ⇑(prodMap r s)) : p.1 ∈ Set.range ⇑r := by
  obtain ⟨q, rfl⟩ := hp
  exact ⟨q.1, rfl⟩

/-- The second coordinate of a point of `im(r × s)` lies in `im(s)`. -/
theorem snd_mem_range_of_mem_range_prodMap {r s : ScottHom U U} {p : U × U}
    (hp : p ∈ Set.range ⇑(prodMap r s)) : p.2 ∈ Set.range ⇑s := by
  obtain ⟨q, rfl⟩ := hp
  exact ⟨q.2, rfl⟩

/-- A pair drawn from `im(r)` and `im(s)` lies in `im(r × s)`. -/
theorem mk_mem_range_prodMap {r s : ScottHom U U} {x y : U}
    (hx : x ∈ Set.range ⇑r) (hy : y ∈ Set.range ⇑s) :
    (x, y) ∈ Set.range ⇑(prodMap r s) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨(a, b), rfl⟩

/-- `im(r × s) ≅ im(r) × im(s)`. -/
def prodRangeOrderIso (r s : ScottHom U U) :
    ↥(Set.range ⇑(prodMap r s)) ≃o ↥(Set.range ⇑r) × ↥(Set.range ⇑s) :=
  Equiv.toOrderIso
    { toFun := fun p => (⟨p.val.1, fst_mem_range_of_mem_range_prodMap p.2⟩,
        ⟨p.val.2, snd_mem_range_of_mem_range_prodMap p.2⟩)
      invFun := fun q => ⟨(q.1.val, q.2.val), mk_mem_range_prodMap q.1.2 q.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    (fun _ _ h => ⟨h.1, h.2⟩) (fun _ _ h => ⟨h.1, h.2⟩)

end ProdMap

/-! ## The product operator, and its representability over `P N` -/

/-- The product operator `· × ·` as an operator on cpos, the companion of
`ScottDomains.Cpo.funSpace`. -/
def prodCpo (D E : Cpo.{u}) : Cpo.{u} := ⟨D.carrier × E.carrier, inferInstance⟩

/-- **The product operator is representable over `P N`** (Gunter & Scott, §7.1,
the paragraph after Lemma 23).

The representing map is the paper's `R×(r, s) = ×⁺ ∘ (r × s) ∘ ×⁻`, with
`×⁻, ×⁺` the closure pair **Theorem 22** supplies at `L = P N × P N` — a countably
based algebraic lattice by `domain_prod` (algebraicity and a countable basis, both
from `K(D × E) = K(D) × K(E)`) and `isLUB_sSup_prod_set` (completeness of the
lattice).

The three obligations of `IsRepresentable₂` are discharged by `isClosure_repOf`
against `isClosure_prodMap` (`R×(r,s) ∈ Fc(P N)`), `scottContinuous_repOf` against
`prodMap_mono` and `isLUB_prodMap_of_isLUB` (continuity of `R×`), and the
composite `repRangeOrderIso ≫ prodRangeOrderIso` (the isomorphism
`im(R×(r,s)) ≅ im(r) × im(s)`).

Together with `ScottDomains.lemma_23` this supplies both hypotheses of **Lemma 24**.

This is *not* a conjunct of Lemma 28; see the module docstring for what Lemma 28
actually states and over which domain. -/
theorem isRepresentable_prod : IsRepresentable₂ (Set ℕ) prodCpo := by
  haveI : Domain (Set ℕ × Set ℕ) := domain_prod
  obtain ⟨fn, gr, hfg, hgf⟩ := theorem_22 (Set ℕ × Set ℕ) isLUB_sSup_prod_set
  refine ⟨fun p => ⟨repOf fn gr (prodMap p.1.val p.2.val),
      isClosure_repOf hfg hgf (isClosure_prodMap p.1.2 p.2.2)⟩,
    scottContinuous_repOf hfg hgf (fun p => isClosure_prodMap p.1.2 p.2.2)
      (fun h => prodMap_mono h.1 h.2) isLUB_prodMap_of_isLUB,
    fun p => ⟨?_⟩⟩
  exact (repRangeOrderIso hfg _).trans (prodRangeOrderIso p.1.val p.2.val)

/-- **`D ≅ D × D` has a solution**, the companion of `recursiveDomain_funSpace`
(`RecursiveDomain.lean`) and the first step of Lemma 24's proof — "we can
represent `F(X) = U × X × X` over `U`, so there is a closure `A` of `U` such that
`A ≅ U × A × A`".

One line, and it is the end-to-end check that `isRepresentable_prod` has the shape
the §7 pipeline consumes: `IsRepresentable₂.diag` turns it into a unary
representable operator and **Theorem 21** turns that into a domain. -/
theorem recursiveDomain_prod : Recursive.IsSolvable.{0} fun X => prodCpo X X :=
  Recursive.theorem_21 (Recursive.IsRepresentable₂.diag isRepresentable_prod)

end ScottDomains.PowerdomainRep

/- Axiom audit, by `#print axioms` (run, then removed so the build emits no
`info` lines). All 20 declarations depend only on the three standard axioms; none
depends on `sorryAx`.

  repOf                                 [propext, Classical.choice, Quot.sound]
  isClosure_repOf                       [propext, Classical.choice, Quot.sound]
  fn_mem_range_of_mem_range_repOf       [propext, Classical.choice, Quot.sound]
  gr_mem_range_repOf                    [propext, Classical.choice, Quot.sound]
  gr_fn_of_mem_range_repOf              [propext, Classical.choice, Quot.sound]
  repRangeOrderIso                      [propext, Classical.choice, Quot.sound]
  scottContinuous_repOf                 [propext, Classical.choice, Quot.sound]
  compacts_prod                         [propext, Quot.sound]
  compactsBelow_prod                    [propext, Quot.sound]
  isAlgebraic_prod                      [propext, Classical.choice, Quot.sound]
  domain_prod                           [propext, Classical.choice, Quot.sound]
  isLUB_sSup_prod_set                   [propext, Classical.choice, Quot.sound]
  prodMap                               [propext, Classical.choice, Quot.sound]
  isClosure_prodMap                     [propext, Classical.choice, Quot.sound]
  prodMap_mono                          [propext, Classical.choice, Quot.sound]
  isLUB_prodMap_of_isLUB                [propext, Classical.choice, Quot.sound]
  prodRangeOrderIso                     [propext, Classical.choice, Quot.sound]
  prodCpo                               [propext, Quot.sound]
  isRepresentable_prod                  [propext, Classical.choice, Quot.sound]
  recursiveDomain_prod                  [propext, Classical.choice, Quot.sound]

`compacts_prod`, `compactsBelow_prod` and `prodCpo` are choice-free; the two set
identities are `Set.ext` over `isCompactElement_prod_iff`, and `prodCpo` only
pairs two carriers. Everywhere else `Classical.choice` enters through the same
door it enters `ScottDomains.lemma_23` by — `ScottHom`'s `SupSet` instance is a
`dite` on an undecidable continuity predicate — plus, in `isRepresentable_prod`
itself, `Set.Countable.exists_eq_range` inside `theorem_22`, which chooses the
enumeration `l₀, l₁, l₂, …` of the basis of `P N × P N`. -/
