import ScottDomains.UniversalDomain
import ScottDomains.FinitaryProjectionPoset
import ScottDomains.FixedPoint

/-!
# §7: recursive domain equations, the universal domain, and Theorem 21

Gunter & Scott, *Semantic Domains*, §7 (*Recursive definitions of domains*),
quoted from the source PDF:

> Many of the data types that arise in the semantics of computer programming
> languages may be seen as solutions of **recursive domain equations**. Consider,
> for example, the equation `T ≅ T + T` (of course, this is an isomorphism rather
> than an equality …).

> We will say that a domain `E` is a **closure of `D`** if it is isomorphic to
> `im(r)` for some finitary closure `r` on `D`.

> **Theorem 21** If an operator `F` is representable over a cpo `U`, then there is
> a domain `D` such that `D ≅ F(D)`.
>
> *Proof:* Suppose `R_F` represents `F`. By the Fixed Point Theorem, there is an
> `r ∈ Fc(U)` such that `r = R_F(r)`. Thus `im(r) = im(R_F(r)) ≅ F(im(r))` so
> `im(r)` is the desired domain. ∎

> Structures such as `P N` are often referred to as **universal domains** because
> they have a rich collection of domains as **retracts**.

`UniversalDomain.lean` (round r0028) supplies everything this file consumes:
`Cpo`, `ClosurePoset U = Fc(U)`, `ClosurePoset.image = im`, `IsClosurePair`,
`IsRepresentable`, `IsRepresentable₂`, **Theorem 22** and **Lemma 23**.

## There is no inverse limit in §7

The section opens with the informal `T₀ → T₁ → T₂ → ⋯` chain of embeddings and
then says: "This is all very informal, however; how are we to make this idea
mathematically precise and, at the same time, sufficiently general?" The answer
the paper gives is §7.1, *Solving domain equations with closures* — the route
formalized here. `D∞` as an inverse limit of embedding–projection pairs is **not
constructed anywhere in §7**; the paper reaches `D ≅ D → D` (§7.2) from
Theorem 21 plus Lemma 23, and `Fc(U)` is where the limit is actually taken. So
`recursiveDomain_funSpace` below, not an inverse limit, is this development's
reflexive domain.

## What is proved and what the numbers cost

| # | Statement | Hypotheses |
| -- | --------- | ---------- |
| 1 | `closureCpo` — `Fc(U)` is a cpo with `⊥ = id` | `U` a cpo (**not** a domain) |
| 2 | `thm21` — representable ⟹ solvable | `U` a cpo |
| 3 | `recursiveDomain_funSpace` — `∃ D, D ≅ (D → D)` | Lemma 23, i.e. `U = P N` |
| 4 | `powersetCpo_isUniversal` — `P N` is universal | Theorem 22 |

Item 1 is **Lemma 20's content**, restated for `ClosurePoset U`.
`FinitaryProjectionPoset.lean` already proves `Fc.completePartialOrder` for
`↥(Fc α) = {r // IsFinitaryClosure r}`, but that subtype is not
`ClosurePoset α = {r // IsClosure r}`, and collapsing the two (`mem_Fc_iff`)
spends `[Domain α]` — a hypothesis Theorem 21 does not have and the paper does
not use ("representable over a **cpo** `U`"). The construction is therefore
repeated here over the weaker hypothesis rather than transported.
-/

namespace ScottDomains.Recursive

universe u

/-! ### The recursive domain equation

The paper writes the equation as `X ≅ F(X)` and stresses that `≅` is an
isomorphism, not an equality — which is exactly why `Cpo` is a bundled carrier
and `≅` is `≃o` between carriers. An operator on cpos is a function
`Cpo → Cpo`, so a recursive domain equation is nothing more than such a function,
and *solving* it is inhabiting the isomorphism type at some `D`. -/

/-- **`D` solves the recursive domain equation `X ≅ F(X)`.**

`Nonempty` rather than a chosen isomorphism: the paper asserts `D ≅ F(D)`, and
every use downstream needs only that some isomorphism exists. -/
def Solves (F : Cpo.{u} → Cpo.{u}) (D : Cpo.{u}) : Prop :=
  Nonempty (D.carrier ≃o (F D).carrier)

/-- **The recursive domain equation `X ≅ F(X)` is solvable.** This is the
conclusion of Theorem 21. -/
def IsSolvable (F : Cpo.{u} → Cpo.{u}) : Prop := ∃ D : Cpo.{u}, Solves F D

/-! ### Universal domains

The paper gives the notion twice, in two sentences that are not the same
statement, and both are formalized:

* the **retract** phrasing, which is the one the paper actually names —
  "Structures such as `P N` are often referred to as universal domains because
  they have a rich collection of domains as retracts" — where "retract" is §7's
  closure `r : U → D` with a section `s : D → U`, `r ∘ s = id` and `s ∘ r ⊒ id`
  (`IsClosurePair`), which is the literal conclusion of Theorem 22;
* the **image-of-a-closure** phrasing, from the definition two paragraphs
  earlier: "a domain `E` is a closure of `D` if it is isomorphic to `im(r)` for
  some finitary closure `r` on `D`". This is the form Theorem 21 consumes, since
  the fixed point it produces is an element of `Fc(U)` and the domain is its
  image.

`IsUniversal.of_retract` proves that the first implies the second, which is the
step the r0028 docstring recorded as "related … but not needed here". -/

/-- **`E` is a closure of `D`**: `E ≅ im(r)` for some `r ∈ Fc(D)`.

The paper's `Fc(D)` carries the extra requirement that `im(r)` be a domain;
`ClosurePoset` drops it because Lemma 19 makes it automatic over a domain, which
is the sentence the paper states immediately before Lemma 19 and which
`FinitaryProjectionPoset.mem_Fc_iff` records. -/
def IsClosureOf (E D : Cpo.{u}) : Prop :=
  ∃ r : ClosurePoset D.carrier, Nonempty (E.carrier ≃o r.image.carrier)

/-- **`U` is a universal domain for the class `C`**, image-of-a-closure
phrasing: every member of `C` is a closure of `U`. -/
def IsUniversal (U : Cpo.{u}) (C : Cpo.{u} → Prop) : Prop := ∀ D, C D → IsClosureOf D U

/-- **`U` is a universal domain for the class `C`**, retract phrasing: every
member of `C` is a retract of `U` in §7's sense — the target of a closure
`r : U → D` with section `s`. This is the phrasing the paper attaches the term
"universal domain" to, and the literal shape of Theorem 22's conclusion. -/
def IsUniversalRetract (U : Cpo.{u}) (C : Cpo.{u} → Prop) : Prop :=
  ∀ D, C D → ∃ (r : ScottHom U.carrier D.carrier) (s : ScottHom D.carrier U.carrier),
    IsClosurePair r s

/-! #### A retract of `U` is the image of a closure on `U`

`UniversalDomain.lean` records this as known and unproved: "`s ∘ r : D → D` is an
`IsClosure` whose image is order-isomorphic to `E` — but the relation is not
needed here and would require a composition operation on `ScottHom`, which the
development does not have." The composite is built pointwise below, exactly as
`repFun` builds its three-fold composite, so no such operation is needed. -/

section RetractToClosure

variable {α β : Type u} [CompletePartialOrder α] [CompletePartialOrder β]
  {r : ScottHom α β} {s : ScottHom β α}

/-- `s ∘ r : α → α`, the endomorphism a closure pair `(r, s)` determines on its
source. Continuous as a composite of two continuous maps. -/
noncomputable def pairComp (r : ScottHom α β) (s : ScottHom β α) : ScottHom α α :=
  ⟨⇑s ∘ ⇑r, ScottContinuous.comp r.scottContinuous s.scottContinuous⟩

@[simp] theorem pairComp_apply (x : α) : pairComp r s x = s (r x) := rfl

/-- `s ∘ r` is a closure on `α`. Idempotence is one rewrite by `r ∘ s = id`,
which deletes the inner pair; inflation is the pair's second law verbatim. -/
theorem isClosure_pairComp (h : IsClosurePair r s) : IsClosure (pairComp r s) := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · show s (r (s (r x))) = s (r x)
    rw [h.1]
  · exact h.2 x

/-- `im(s ∘ r) = im(s)`: the inclusion `⊆` is immediate, and `s y = s (r (s y))`
gives `⊇`. Only the `⊇` half is stated, because it is the one the isomorphism
needs. -/
theorem mem_range_pairComp (h : IsClosurePair r s) (y : β) :
    s y ∈ Set.range ⇑(pairComp r s) :=
  ⟨s y, by show s (r (s y)) = s y; rw [h.1]⟩

/-- **`β ≅ im(s ∘ r)`.** The maps are `s` corestricted and `r` restricted. The
round trip `r ∘ s = id` is the pair's first law; the other round trip is
`s (r z) = z` for `z ∈ im(s ∘ r)`, which is idempotence of `s ∘ r` at a point of
its own image. Monotonicity in both directions is monotonicity of `s` and of
`r`, so `Equiv.toOrderIso` upgrades the bijection to an order isomorphism — and
an order isomorphism between cpos preserves directed suprema automatically. -/
noncomputable def pairCompOrderIso (h : IsClosurePair r s) :
    β ≃o ↥(Set.range ⇑(pairComp r s)) :=
  Equiv.toOrderIso
    { toFun := fun y => ⟨s y, mem_range_pairComp h y⟩
      invFun := fun z => r z.val
      left_inv := fun y => h.1 y
      right_inv := fun z => Subtype.ext (by
        obtain ⟨x, hx⟩ := z.2
        show s (r z.val) = z.val
        rw [← hx]
        show s (r (s (r x))) = s (r x)
        rw [h.1]) }
    (fun _ _ hy => s.monotone hy) (fun _ _ hz => r.monotone hz)

end RetractToClosure

/-- A retract of `D` in §7's sense is a closure of `D`. -/
theorem IsClosureOf.of_isClosurePair {D E : Cpo.{u}}
    (r : ScottHom D.carrier E.carrier) (s : ScottHom E.carrier D.carrier)
    (h : IsClosurePair r s) : IsClosureOf E D :=
  ⟨⟨pairComp r s, isClosure_pairComp h⟩, ⟨pairCompOrderIso h⟩⟩

/-- The paper's two phrasings of "universal domain", in the only direction that
needs an argument. -/
theorem IsUniversal.of_retract {U : Cpo.{u}} {C : Cpo.{u} → Prop}
    (h : IsUniversalRetract U C) : IsUniversal U C := by
  intro D hD
  obtain ⟨r, s, hrs⟩ := h D hD
  exact IsClosureOf.of_isClosurePair r s hrs

/-! #### `P N` is a universal domain

Theorem 22 is exactly the retract phrasing at `U = P N` and `C` = the countably
based algebraic lattices, so the only work is packaging. -/

/-- `P N` as a bundled cpo. -/
def powersetCpo : Cpo.{0} := ⟨Set ℕ, inferInstance⟩

/-- The paper's "(countably based) algebraic lattice", as a predicate on `Cpo`.

`Domain D.carrier` is `IsAlgebraic` with `K(D)` countable — the countably based
algebraic half — and it is a `Prop`-valued class, so it may be conjoined
directly. Lattice completeness is carried as the proposition
`∀ t, IsLUB t (sSup t)` against the cpo's own `sSup`, for the instance-diamond
reason `UniversalDomain.lean` records: a second `CompletePartialOrder` on a type
that already has one broke an `Iff.rfl` in r0004. -/
def IsCountablyBasedAlgebraicLattice (D : Cpo.{u}) : Prop :=
  Domain D.carrier ∧ ∀ t : Set D.carrier, IsLUB t (sSup t)

/-- **`P N` is a universal domain, retract phrasing** — this is Theorem 22. -/
theorem powersetCpo_isUniversalRetract :
    IsUniversalRetract powersetCpo IsCountablyBasedAlgebraicLattice := by
  rintro D ⟨hdom, hsup⟩
  letI := hdom
  exact thm22 D.carrier hsup

/-- **`P N` is a universal domain, image-of-a-closure phrasing.** Every countably
based algebraic lattice is `im(r)` for some `r ∈ Fc(P N)`. -/
theorem powersetCpo_isUniversal :
    IsUniversal powersetCpo IsCountablyBasedAlgebraicLattice :=
  IsUniversal.of_retract powersetCpo_isUniversalRetract

/-! ### Lemma 20's content for `Fc(U)`: it is a cpo

> **Lemma 20** If `D` is a domain, then `Fc(D)` is a cpo.

Theorem 21 applies the Fixed Point Theorem inside `Fc(U)`, so `Fc(U)` must be a
cpo *with a least element*, and `⊥` is `id` — the least closure, since every
closure is inflationary.

The `SupSet` case split follows the rule this development already fixed: `sSup`
branches on **the proposition the subtype constructor needs**, here
`IsClosure (⨆ …)`, not on directedness, which is merely sufficient. The candidate
is the ambient supremum of `insert id (val '' S)`; adjoining `id` changes no
supremum of a nonempty family and makes the family nonempty and directed even
when `S = ∅`, so one argument covers the empty case. -/

section FcCpo

variable {U : Type u} [CompletePartialOrder U]

/-- `id`, the least element of `Fc(U)`. -/
def idClosure (U : Type u) [CompletePartialOrder U] : ClosurePoset U :=
  ⟨ScottHom.id, isClosure_id⟩

/-- `id ⊑ r` for every closure `r`, which is the inflationary law read as an
order fact about `Fc(U)`. -/
theorem idClosure_le (r : ClosurePoset U) : idClosure U ≤ r := fun x => r.2.le_apply x

/-- `insert id (val '' S)` is nonempty and directed whenever `S` is directed. -/
theorem directedOn_insert_id {S : Set (ClosurePoset U)} (hS : DirectedOn (· ≤ ·) S) :
    DirectedOn (· ≤ ·)
      (insert (ScottHom.id : ScottHom U U) ((fun c : ClosurePoset U => c.val) '' S)) := by
  have hid : ∀ f ∈ insert (ScottHom.id : ScottHom U U)
      ((fun c : ClosurePoset U => c.val) '' S), (ScottHom.id : ScottHom U U) ≤ f := by
    rintro _ (rfl | ⟨a, _, rfl⟩)
    · exact le_rfl
    · exact fun x => a.2.le_apply x
  rintro u hu v hv
  rcases hu with rfl | ⟨a, ha, rfl⟩
  · exact ⟨v, hv, hid v hv, le_rfl⟩
  rcases hv with rfl | ⟨b, hb, rfl⟩
  · exact ⟨a.val, Set.mem_insert_of_mem _ ⟨a, ha, rfl⟩, le_rfl,
      hid _ (Set.mem_insert_of_mem _ ⟨a, ha, rfl⟩)⟩
  obtain ⟨c, hc, hac, hbc⟩ := hS a ha b hb
  exact ⟨c.val, Set.mem_insert_of_mem _ ⟨c, hc, rfl⟩, hac, hbc⟩

open Classical in
/-- **`Fc(U)` is a cpo**, with `⊥ = id` and directed suprema computed pointwise
in `U → U`. Stated for `ClosurePoset U` and over a bare cpo `U`; see the module
docstring for why `FinitaryProjectionPoset.Fc.completePartialOrder` cannot be
reused.

Not an instance: `IsRepresentable` states `ScottContinuous R` against the
`PartialOrder (ClosurePoset U)` instance already in scope, and this structure is
spliced from that same instance so the two agree definitionally. Installing a
second route to `Preorder (ClosurePoset U)` globally is the diamond the
development avoids elsewhere; `letI` at the two use sites costs nothing. -/
@[reducible] noncomputable def closureCpo (U : Type u) [CompletePartialOrder U] :
    CompletePartialOrder (ClosurePoset U) :=
  { (inferInstance : PartialOrder (ClosurePoset U)) with
    sSup := fun S =>
      if h : IsClosure (sSup (insert (ScottHom.id : ScottHom U U)
          ((fun c : ClosurePoset U => c.val) '' S))) then ⟨_, h⟩ else idClosure U
    bot := idClosure U
    bot_le := idClosure_le
    lubOfDirected := fun S hS => by
      have hdir := directedOn_insert_id hS
      have hcl : ∀ f ∈ insert (ScottHom.id : ScottHom U U)
          ((fun c : ClosurePoset U => c.val) '' S), IsClosure f := by
        rintro _ (rfl | ⟨a, _, rfl⟩)
        · exact isClosure_id
        · exact a.2
      have hmem : IsClosure (sSup (insert (ScottHom.id : ScottHom U U)
          ((fun c : ClosurePoset U => c.val) '' S))) :=
        isClosure_sSup ⟨_, Set.mem_insert _ _⟩ hdir hcl
      rw [dif_pos hmem]
      constructor
      · intro a ha
        exact hdir.le_sSup (Set.mem_insert_of_mem _ ⟨a, ha, rfl⟩)
      · intro b hb
        refine hdir.sSup_le ?_
        rintro _ (rfl | ⟨a, ha, rfl⟩)
        · exact idClosure_le b
        · exact hb ha }

/-- **The Fixed Point Theorem inside `Fc(U)`** — the step the proof of Theorem 21
cites by name. `Fc(U)` is a cpo with `⊥ = id`, so Theorem 1 applies to a
continuous `R : Fc(U) → Fc(U)` and returns `⨆ₙ Rⁿ(id)`, the least closure fixed
by `R`. -/
theorem exists_fixedPoint {R : ClosurePoset U → ClosurePoset U} (hR : ScottContinuous R) :
    ∃ r : ClosurePoset U, R r = r := by
  letI : CompletePartialOrder (ClosurePoset U) := closureCpo U
  exact ⟨kleeneFix R, map_kleeneFix hR⟩

end FcCpo

/-! ### Theorem 21 -/

/-- **Theorem 21.** If an operator `F` is representable over a cpo `U`, then the
recursive domain equation `X ≅ F(X)` has a solution.

The paper's proof, unchanged: `R_F` is continuous on `Fc(U)`, which is a cpo
(`closureCpo`), so the Fixed Point Theorem gives `r ∈ Fc(U)` with `R_F(r) = r`;
representability gives `im(R_F(r)) ≅ F(im(r))`; substituting the fixed-point
equation turns the left side into `im(r)`.

The hypothesis is `U` a **cpo**, exactly as stated — no algebraicity, no
countable basis, and no `Domain U`. -/
theorem thm21 {U : Type u} [CompletePartialOrder U] {F : Cpo.{u} → Cpo.{u}}
    (hF : IsRepresentable U F) : IsSolvable F := by
  obtain ⟨R, hR, hiso⟩ := hF
  obtain ⟨r, hr⟩ := exists_fixedPoint hR
  refine ⟨r.image, ?_⟩
  have h := hiso r
  rwa [hr] at h

/-! ### Diagonalizing a binary representable operator

Lemma 23 is stated for the **binary** function-space operator
(`IsRepresentable₂`), because that is the form the paper displays; Theorem 21
consumes a unary operator. The diagonal `X ↦ F(X, X)` is representable by
`r ↦ R(r, r)`, and the only thing to check is that `r ↦ (r, r)` is continuous
into the product order. -/

/-- The diagonal `a ↦ (a, a)` is Scott continuous: in the product order both
halves of `IsLUB` are the corresponding halves for `a`, taken twice. -/
theorem scottContinuous_diag {α : Type*} [Preorder α] :
    ScottContinuous (fun a : α => (a, a)) := by
  intro d _ _ a ha
  constructor
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨ha.1 hx, ha.1 hx⟩
  · rintro ⟨u₁, u₂⟩ hu
    exact ⟨ha.2 fun x hx => (hu ⟨x, hx, rfl⟩).1, ha.2 fun x hx => (hu ⟨x, hx, rfl⟩).2⟩

/-- A binary operator representable over `U` has a representable diagonal, by
`R'(r) = R(r, r)`. -/
theorem IsRepresentable₂.diag {U : Type u} [CompletePartialOrder U]
    {F : Cpo.{u} → Cpo.{u} → Cpo.{u}} (h : IsRepresentable₂ U F) :
    IsRepresentable U fun X => F X X := by
  obtain ⟨R, hR, hiso⟩ := h
  exact ⟨fun r => R (r, r), ScottContinuous.comp scottContinuous_diag hR,
    fun r => hiso (r, r)⟩

/-- **The reflexive domain.** There is a cpo `D` with `D ≅ (D → D)`.

This is §7.2's opening claim, and it is where the paper's route actually lands:
Lemma 23 (the function space is representable over `P N`), diagonalized, fed to
Theorem 21. No inverse limit is taken anywhere; the limit is the one
`exists_fixedPoint` takes inside `Fc(P N)`.

What is **not** claimed: that `D` is nontrivial. The paper is explicit that this
statement alone does not give an interesting model — "the equation `I ≅ I → I`
… shows that there is no guarantee that the result will be at all interesting" —
and nontriviality is Lemma 24 and Theorem 25, which additionally need the product
operator represented over `U`. Those are not stated here. -/
theorem recursiveDomain_funSpace : IsSolvable.{0} fun X => Cpo.funSpace X X :=
  thm21 (IsRepresentable₂.diag lem23)

end ScottDomains.Recursive
