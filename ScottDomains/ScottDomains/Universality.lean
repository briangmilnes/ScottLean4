import ScottDomains.Powerdomain.Universal
import ScottDomains.Currying
import Mathlib.Order.Bounds.OrderIso

/-!
# §7.2: Lemma 24 and Theorem 25 — a non-trivial reflexive domain

Gunter & Scott, *Semantic Domains*, §7.2 (*Modelling the untyped λ-calculus*),
quoted verbatim from the source PDF:

> It is tempting to try to solve the domain equation `D ≅ D → D` by the methods
> just discussed. Unfortunately, the equation `I ≅ I → I` (corresponding to the
> fact that on a one-point set there is only one possible self-map) shows that
> there is no guarantee that the result will be at all interesting. There has to
> be a way to build in some nontrivial structure that is not wiped out by the
> fixed-point process.

> **Lemma 24** Let `U` be a non-trivial cpo. If the product and function space
> operators can be represented over `U`, then there are non-trivial domains `D`
> and `E` such that `E ≅ E × E` and `D ≅ D → E`.
>
> *Proof:* We can represent `F(X) = U × X × X` over `U`, so there is a closure
> `A` of `U` such that `A ≅ U × A × A`. Thus
> `U × A ≅ U × (U × A × A) ≅ (U × A) × (U × A)`. So `E = U × A` is non-trivial
> and `E ≅ E × E`. Now, `E` is a closure of `U` so `G(X) = X → E` is
> representable over `U`. Hence there is a cpo `D ≅ D → E`. This cpo is
> non-trivial because `E` is. ∎

> **Theorem 25** If `U` is a non-trivial domain which represents products and
> function spaces, then there is a non-trivial domain `D` such that
> `D ≅ D × D ≅ D → D` and `D` is the image of a closure on `U`.
>
> *Proof:* Let `D` and `E` be the domains given by Lemma 24. Then
> `D × D ≅ (D → E) × (D → E) ≅ D → (E × E) ≅ D → E ≅ D`
> and
> `D → D ≅ D → (D → E) ≅ (D × D) → E ≅ D → E ≅ D`. ∎

> We note, in fact, that `D` will have `P N` itself represented by a closure on
> `U`. Hence, to get a non-trivial solution for `D ≅ D → D ≅ D × D`, take `U` in
> the theorem to be `P N`.

Both hypotheses are already available at `U = P N`: `ScottDomains.lem23`
(`UniversalDomain.lean`, r0028) and
`ScottDomains.PowerdomainRep.isRepresentable_prod` (`Powerdomain/Universal.lean`,
r0031). `thm25_powerset` is the paper's last sentence.

## What "non-trivial" is

The paper fixes the meaning by its own counterexample: the obstruction is the
one-point cpo `I`, for which `I ≅ I → I` holds vacuously. So *non-trivial* is
"has at least two elements", which is Mathlib's `Nontrivial`. It is **not** a
condition the development cannot express, and it is carried as an explicit
hypothesis `[Nontrivial U]` on Lemma 24 and Theorem 25, exactly where the paper
states it. At `U = P N` it is discharged by `Set.nontrivial_of_nonempty`.

## Where the statements here are stronger than the paper's prose

Two conjuncts are added, and both are read off the paper's own proof rather than
invented:

1. Lemma 24 also concludes that `D` and `E` are **closures of `U`**
   (`Recursive.IsClosureOf`). The proof needs this — "Now, `E` is a closure of
   `U` so `G(X) = X → E` is representable over `U`" — and Theorem 25's
   conclusion "`D` is the image of a closure on `U`" is nothing else.
2. Theorem 25's `D` is delivered together with `IsClosureOf D U`, which is
   precisely the relation `Recursive.IsUniversal` quantifies over. No third
   formalization of universality is introduced: `thm25_isUniversal` states the
   corollary with `Recursive.IsUniversal` itself.

## Where the statements here are weaker than the paper's prose

The paper says "non-trivial **domains** `D` and `E`", but its own proof produces
cpos: "Hence there is a **cpo** `D ≅ D → E`". Lemma 24's hypothesis is a
non-trivial *cpo* `U`, and Theorem 21 — which the proof invokes — is stated over
a cpo and returns `im(r)` for a closure `r`, which `Skeleton/Section6.lean`'s
`lem19` shows carries a `CompletePartialOrder` and **not** that it is algebraic
with a countable basis (the note `UniversalDomain.lean` records against
`ClosurePoset`). So `D` and `E` are `Cpo`, not `Domain`, and that is what the
proof supports. Theorem 25's hypothesis is `U` a *domain*, but no step of its
proof spends algebraicity or countability of `K(U)`, so `thm25` is stated over a
cpo — a strictly stronger theorem, and the one the proof establishes.

## What had to be built

Lemma 8 (`Product.lean`, `Currying.lean`) supplies the four isomorphisms the two
proofs shuffle, but only for bare carrier types. Both proofs also need `≅` to be
a **congruence** — `D ≅ D'` and `E ≅ E'` must give `D × E ≅ D' × E'` and
`(D → E) ≅ (D' → E')` — and Mathlib has no `OrderIso.prodCongr`. The function
space case spends the fact that an order isomorphism between cpos is Scott
continuous (`scottContinuous_orderIso`, one line from `OrderIso.isLUB_image'`),
which is the same observation `Product.lean`'s docstring makes when it says `≃o`
needs no separate continuity obligation.
-/

namespace ScottDomains.Universality

open ScottDomains.Recursive ScottDomains.PowerdomainRep

universe u

/-! ## Order-isomorphism toolkit

Four facts, none of them in Mathlib in this form, all consumed by the two proofs
below. -/

section Toolkit

variable {α β γ δ : Type*}

/-- **An order isomorphism is Scott continuous.** Least upper bounds are defined
by the order alone, so an order isomorphism carries them to least upper bounds;
`OrderIso.isLUB_image'` is exactly that, and neither directedness nor
nonemptiness of the set is used. -/
theorem scottContinuous_orderIso [Preorder α] [Preorder β] (e : α ≃o β) :
    ScottContinuous ⇑e := fun _ _ _ _ ha => (OrderIso.isLUB_image' e).mpr ha

/-- Pairing with a fixed value on the left is Scott continuous, over bare
preorders. `Currying.scottContinuous_pairLeft` proves the same statement but
demands `CompletePartialOrder` on both factors, and the use below is at
`Fc(U) = ClosurePoset U`, which carries only a `PartialOrder` instance — its cpo
structure `closureCpo` is deliberately not an instance. -/
theorem scottContinuous_pairConst [Preorder α] [Preorder β] (c : α) :
    ScottContinuous (fun y : β => (c, y)) := by
  intro d hne _ a ha
  refine ⟨?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨le_rfl, ha.1 hy⟩
  · rintro ⟨u₁, u₂⟩ hu
    obtain ⟨y₀, hy₀⟩ := hne
    exact ⟨(hu ⟨y₀, hy₀, rfl⟩).1, ha.2 fun y hy => (hu ⟨y, hy, rfl⟩).2⟩

/-- Pairing with a fixed value on the right, the mirror image. -/
theorem scottContinuous_pairConstRight [Preorder α] [Preorder β] (c : β) :
    ScottContinuous (fun y : α => (y, c)) := by
  intro d hne _ a ha
  refine ⟨?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨ha.1 hy, le_rfl⟩
  · rintro ⟨u₁, u₂⟩ hu
    obtain ⟨y₀, hy₀⟩ := hne
    exact ⟨ha.2 fun y hy => (hu ⟨y, hy, rfl⟩).1, (hu ⟨y₀, hy₀, rfl⟩).2⟩

/-- **The product is a congruence for `≃o`.** Mathlib has `OrderIso.prodComm` but
no `OrderIso.prodCongr`; both `Prod.le` obligations are coordinatewise. -/
def prodOrderIso [Preorder α] [Preorder β] [Preorder γ] [Preorder δ]
    (e : α ≃o β) (f : γ ≃o δ) : α × γ ≃o β × δ where
  toFun p := (e p.1, f p.2)
  invFun q := (e.symm q.1, f.symm q.2)
  left_inv p := by simp
  right_inv q := by simp
  map_rel_iff' := ⟨fun h => ⟨e.le_iff_le.mp h.1, f.le_iff_le.mp h.2⟩,
    fun h => ⟨e.le_iff_le.mpr h.1, f.le_iff_le.mpr h.2⟩⟩

/-- **The function space is a congruence for `≃o`.** Transport is
`g ↦ f ∘ g ∘ e⁻¹`, continuous because `scottContinuous_orderIso` makes both
isomorphisms continuous; the order condition is the pointwise order on either
side, tested at `e x` in one direction and at `e⁻¹ y` in the other. -/
def scottHomOrderIso [CompletePartialOrder α] [CompletePartialOrder β]
    [CompletePartialOrder γ] [CompletePartialOrder δ] (e : α ≃o β) (f : γ ≃o δ) :
    ScottHom α γ ≃o ScottHom β δ where
  toFun g := ⟨⇑f ∘ ⇑g ∘ ⇑e.symm,
    ScottContinuous.comp
      (ScottContinuous.comp (scottContinuous_orderIso e.symm) g.scottContinuous)
      (scottContinuous_orderIso f)⟩
  invFun h := ⟨⇑f.symm ∘ ⇑h ∘ ⇑e,
    ScottContinuous.comp
      (ScottContinuous.comp (scottContinuous_orderIso e) h.scottContinuous)
      (scottContinuous_orderIso f.symm)⟩
  left_inv g := by
    ext x
    show f.symm (f (g (e.symm (e x)))) = g x
    simp
  right_inv h := by
    ext y
    show f (f.symm (h (e (e.symm y)))) = h y
    simp
  map_rel_iff' := by
    refine fun {g₁ g₂} => ⟨fun h x => ?_, fun h y => f.monotone (h (e.symm y))⟩
    have hx := h (e x)
    simpa using f.le_iff_le.mp hx

/-- Nontriviality transports backwards along an order isomorphism. -/
theorem nontrivial_of_orderIso [Preorder α] [Preorder β] (e : α ≃o β)
    (h : Nontrivial β) : Nontrivial α := by
  obtain ⟨x, y, hxy⟩ := h
  refine ⟨e.symm x, e.symm y, fun hs => hxy ?_⟩
  rw [← e.apply_symm_apply x, ← e.apply_symm_apply y, hs]

/-- **`D → E` is non-trivial when `E` is**, witnessed by two constant maps, which
differ already at `⊥`. This is the step that carries the paper's "This cpo is
non-trivial because `E` is" — nothing about `D` is used beyond its having a
least element. -/
theorem nontrivial_scottHom [CompletePartialOrder α] [CompletePartialOrder β]
    (h : Nontrivial β) : Nontrivial (ScottHom α β) := by
  obtain ⟨b₁, b₂, hb⟩ := h
  refine ⟨(ScottHom.const b₁ : ScottHom α β), ScottHom.const b₂, fun he => hb ?_⟩
  exact congrArg (fun g : ScottHom α β => g ⊥) he

/-- The rearrangement `((u₁, a₁), (u₂, a₂)) ↦ (u₁, (u₂, (a₁, a₂)))`, which is the
paper's `(U × A) × (U × A) ≅ U × (U × A × A)` read right to left. Stated as one
isomorphism rather than assembled from `prodComm` and `prodAssoc` because the
assembly is four steps and every equation here is `rfl`. -/
def prodShuffle [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] :
    (α × β) × (γ × δ) ≃o α × (γ × (β × δ)) where
  toFun p := (p.1.1, (p.2.1, (p.1.2, p.2.2)))
  invFun q := ((q.1, q.2.2.1), (q.2.1, q.2.2.2))
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := ⟨fun h => ⟨⟨h.1, h.2.2.1⟩, ⟨h.2.1, h.2.2.2⟩⟩,
    fun h => ⟨h.1.1, ⟨h.2.1, ⟨h.1.2, h.2.2⟩⟩⟩⟩

end Toolkit

/-! ## Isomorphism of bundled cpos

`Cpo` is the bundled carrier `UniversalDomain.lean` introduces so that "an
operator on cpo's" is a function `Cpo → Cpo`; `Iso` is the paper's `≅` on those
values. It is definitionally `Recursive.Solves` with the operator applied
(`solves_iff_iso`), so nothing new is being defined — only named, because §7.2's
two proofs are chains of a dozen isomorphisms each and are unreadable otherwise. -/

/-- **`D ≅ E`** for bundled cpos. An order isomorphism between cpos preserves
directed suprema automatically (`scottContinuous_orderIso`), so `≃o` between
carriers is the full content of the paper's `≅`. -/
def Iso (D E : Cpo.{u}) : Prop := Nonempty (D.carrier ≃o E.carrier)

/-- `Recursive.Solves F D` *is* `Iso D (F D)`; the two are the same proposition,
so no conversion is ever needed between §7.1's vocabulary and this file's. -/
theorem solves_iff_iso {F : Cpo.{u} → Cpo.{u}} {D : Cpo.{u}} : Solves F D ↔ Iso D (F D) :=
  Iff.rfl

namespace Iso

variable {D D' E E' : Cpo.{u}}

@[refl] theorem refl (D : Cpo.{u}) : Iso D D := ⟨OrderIso.refl _⟩

theorem symm (h : Iso D E) : Iso E D := h.map OrderIso.symm

theorem trans (h₁ : Iso D E) (h₂ : Iso E E') : Iso D E' :=
  h₁.elim fun e₁ => h₂.elim fun e₂ => ⟨e₁.trans e₂⟩

/-- `≅` is a congruence for `×`. -/
theorem prodCongr (h : Iso D D') (h' : Iso E E') : Iso (prodCpo D E) (prodCpo D' E') :=
  h.elim fun e => h'.elim fun e' => ⟨prodOrderIso e e'⟩

/-- `≅` is a congruence for `→`. -/
theorem funSpaceCongr (h : Iso D D') (h' : Iso E E') :
    Iso (Cpo.funSpace D E) (Cpo.funSpace D' E') :=
  h.elim fun e => h'.elim fun e' => ⟨scottHomOrderIso e e'⟩

/-- Nontriviality is an isomorphism invariant. -/
theorem nontrivial (h : Iso D E) (hE : Nontrivial E.carrier) : Nontrivial D.carrier :=
  h.elim fun e => nontrivial_of_orderIso e hE

end Iso

/-- Being the image of a closure on `U` is an isomorphism invariant of the
first argument. This is what makes Theorem 25's conclusion a `Recursive.IsUniversal`
statement about an isomorphism class rather than about one chosen carrier. -/
theorem IsClosureOf.of_iso {D E W : Cpo.{u}} (h : Iso D E) (hE : IsClosureOf E W) :
    IsClosureOf D W := by
  obtain ⟨r, hr⟩ := hE
  exact ⟨r, h.trans hr⟩

/-! ### Lemma 8, lifted to `Cpo`

`Product.lean` and `Currying.lean` prove parts 1–4 for carrier types. Only the
two parts §7.2 actually consumes are lifted. -/

/-- **Lemma 8.3** at the level of `Cpo`: `D → (E × F) ≅ (D → E) × (D → F)`. -/
theorem iso_funSpace_prod (D E F : Cpo.{u}) :
    Iso (Cpo.funSpace D (prodCpo E F)) (prodCpo (Cpo.funSpace D E) (Cpo.funSpace D F)) :=
  ⟨scottHomProd⟩

/-- **Lemma 8.4** at the level of `Cpo`: `D → (E → F) ≅ (D × E) → F`. -/
theorem iso_curry (D E F : Cpo.{u}) :
    Iso (Cpo.funSpace D (Cpo.funSpace E F)) (Cpo.funSpace (prodCpo D E) F) :=
  ⟨scottHomCurry⟩

/-! ## `U` itself is a closure of `U`

The paper's remark that "a constant operator `X ↦ D` is representable over a
domain `U` if and only if `D` is a closure of `U`" is used below only in the
direction it is needed, and only at two closures: `id`, whose image is `U`, and
the one representing `E`. -/

/-- `U` as a bundled cpo. -/
def cpoOf (U : Type u) [CompletePartialOrder U] : Cpo.{u} := ⟨U, inferInstance⟩

/-- **`im(id) ≅ U`.** `⊥` of `Fc(U)` is `id` (`Recursive.idClosure`), whose range
is all of `U`, and the order on the range subtype is the induced one — so every
equation is `rfl`. -/
def idClosureImageIso (U : Type u) [CompletePartialOrder U] :
    (idClosure U).image.carrier ≃o U where
  toFun x := x.val
  invFun x := ⟨x, ⟨x, rfl⟩⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-! ## Theorem 21, retaining the closure it fixes

`Recursive.thm21` returns `IsSolvable F` — a cpo and an isomorphism, with the
closure discarded. Lemma 24 needs the closure back: its `A` is "a **closure** of
`U` such that `A ≅ U × A × A`", and Theorem 25's conclusion is that `D` is the
image of a closure on `U`. The proof is `thm21`'s, unchanged; only the
existential is wider. -/

/-- **Theorem 21, with the fixed closure retained.** The Fixed Point Theorem
inside `Fc(U)` (`Recursive.exists_fixedPoint`, which is Lemma 20 plus Theorem 1)
gives `r` with `R_F(r) = r`; representability gives `im(R_F(r)) ≅ F(im(r))`; the
fixed-point equation rewrites the left side to `im(r)`. -/
theorem theorem_21_image {U : Type u} [CompletePartialOrder U] {F : Cpo.{u} → Cpo.{u}}
    (hF : IsRepresentable U F) : ∃ r : ClosurePoset U, Iso r.image (F r.image) := by
  obtain ⟨R, hR, hiso⟩ := hF
  obtain ⟨r, hr⟩ := exists_fixedPoint hR
  refine ⟨r, ?_⟩
  have h := hiso r
  rwa [hr] at h

alias thm21_image := theorem_21_image

/-! ## The two derived operators Lemma 24 represents -/

section Derived

variable {U : Type u} [CompletePartialOrder U]

/-- **`F(X) = U × (X × X)` is representable over `U`** whenever `×` is.

The representing map is `R_F(r) = R×(id, R×(r, r))`: the constant `id` supplies
the `U` factor, since `im(id) ≅ U`. Continuity is the composite of the diagonal
(`Recursive.scottContinuous_diag`), `R×`, pairing with the constant `id`
(`scottContinuous_pairConst`) and `R×` again. The isomorphism is `R×`'s own,
applied twice and rewritten in the first coordinate by `idClosureImageIso`.

This is the paper's "We can represent `F(X) = U × X × X` over `U`", with the
paper's unparenthesized triple product read as `U × (X × X)`; which bracketing is
chosen is immaterial, because the only use of `A ≅ F(A)` is inside the shuffle
`prodShuffle`, which reassociates anyway. -/
theorem isRepresentable_selfProdSquare (hprod : IsRepresentable₂ U prodCpo) :
    IsRepresentable U (fun X => prodCpo (cpoOf U) (prodCpo X X)) := by
  obtain ⟨R, hR, hiso⟩ := hprod
  refine ⟨fun r => R (idClosure U, R (r, r)),
    ScottContinuous.comp
      (ScottContinuous.comp (ScottContinuous.comp scottContinuous_diag hR)
        (scottContinuous_pairConst (idClosure U))) hR,
    fun r => ?_⟩
  obtain ⟨e₁⟩ := hiso (idClosure U, R (r, r))
  obtain ⟨e₂⟩ := hiso (r, r)
  exact ⟨e₁.trans (prodOrderIso (idClosureImageIso U) e₂)⟩

/-- **`G(X) = X → E` is representable over `U`** whenever `→` is and `E` is a
closure of `U`, which is the paper's "Now, `E` is a closure of `U` so
`G(X) = X → E` is representable over `U`".

The representing map is `R_G(r) = R→(r, c)` for the closure `c` with
`im(c) ≅ E`; continuity is pairing with a constant on the right followed by
`R→`, and the isomorphism is `R→`'s own with the codomain rewritten by
`scottHomOrderIso` along `im(c) ≅ E`. -/
theorem isRepresentable_funSpaceConst (hfun : IsRepresentable₂ U Cpo.funSpace)
    {E : Cpo.{u}} {c : ClosurePoset U} (hc : Iso c.image E) :
    IsRepresentable U (fun X => Cpo.funSpace X E) := by
  obtain ⟨R, hR, hiso⟩ := hfun
  obtain ⟨ec⟩ := hc
  refine ⟨fun r => R (r, c),
    ScottContinuous.comp (scottContinuous_pairConstRight c) hR, fun r => ?_⟩
  obtain ⟨e⟩ := hiso (r, c)
  exact ⟨e.trans (scottHomOrderIso (OrderIso.refl r.image.carrier) ec)⟩

end Derived

/-! ## Lemma 24 -/

/-- **Lemma 24.** Let `U` be a non-trivial cpo. If the product and function space
operators are representable over `U`, then there are non-trivial cpos `D` and `E`,
both closures of `U`, with `E ≅ E × E` and `D ≅ D → E`.

The proof is the paper's, in its four steps.

| # | Step | Instrument |
| -- | ---- | ---------- |
| 1 | a closure `A` of `U` with `A ≅ U × (A × A)` | `isRepresentable_selfProdSquare`, `thm21_image` |
| 2 | `E := U × A` satisfies `E ≅ E × E` | `prodOrderIso` then `prodShuffle` |
| 3 | `E` is a closure of `U` | `R×(id, A)`, whose image is `im(id) × im(A) ≅ U × A` |
| 4 | a closure `D` of `U` with `D ≅ D → E` | `isRepresentable_funSpaceConst`, `thm21_image` |

Non-triviality of `E` is `Nontrivial U` plus `im(A) ∋ A(⊥)`; non-triviality of
`D` is `nontrivial_scottHom` transported back along `D ≅ D → E`, which is the
paper's "This cpo is non-trivial because `E` is".

Stated over a cpo and concluding about `Cpo`, not `Domain` — see the module
docstring for why the paper's word "domains" is not what its own proof
delivers. -/
theorem lemma_24 (U : Type u) [CompletePartialOrder U] [Nontrivial U]
    (hprod : IsRepresentable₂ U prodCpo) (hfun : IsRepresentable₂ U Cpo.funSpace) :
    ∃ D E : Cpo.{u}, Nontrivial D.carrier ∧ Nontrivial E.carrier ∧
      IsClosureOf D (cpoOf U) ∧ IsClosureOf E (cpoOf U) ∧
      Iso E (prodCpo E E) ∧ Iso D (Cpo.funSpace D E) := by
  -- Step 1: `A` is a closure of `U` with `A ≅ U × (A × A)`.
  obtain ⟨A, hA⟩ := thm21_image (isRepresentable_selfProdSquare hprod)
  obtain ⟨eA⟩ := hA
  set E : Cpo.{u} := prodCpo (cpoOf U) A.image with hE
  -- `im(A)` is nonempty, which is all `E`'s non-triviality needs beyond `U`'s.
  have hAne : Nonempty A.image.carrier := ⟨⟨A.val ⊥, Set.mem_range_self ⊥⟩⟩
  have hEnt : Nontrivial E.carrier := by
    haveI := hAne
    exact inferInstanceAs (Nontrivial (U × A.image.carrier))
  -- Step 2: `E ≅ E × E`.
  have hEiso : Iso E (prodCpo E E) :=
    ⟨(prodOrderIso (OrderIso.refl U) eA).trans prodShuffle.symm⟩
  -- Step 3: `E` is a closure of `U`, via `R×(id, A)`.
  obtain ⟨Rp, _, hpiso⟩ := hprod
  obtain ⟨ep⟩ := hpiso (idClosure U, A)
  have hEcl : IsClosureOf E (cpoOf U) :=
    ⟨Rp (idClosure U, A),
      ⟨(prodOrderIso (idClosureImageIso U) (OrderIso.refl A.image.carrier)).symm.trans ep.symm⟩⟩
  have hcE : Iso (Rp (idClosure U, A)).image E :=
    ⟨ep.trans (prodOrderIso (idClosureImageIso U) (OrderIso.refl A.image.carrier))⟩
  -- Step 4: `D` is a closure of `U` with `D ≅ D → E`.
  obtain ⟨Dcl, hD⟩ := thm21_image (isRepresentable_funSpaceConst hfun hcE)
  refine ⟨Dcl.image, E, hD.nontrivial (nontrivial_scottHom hEnt), hEnt,
    ⟨Dcl, Iso.refl _⟩, hEcl, hEiso, hD⟩

alias lem24 := lemma_24

/-! ## Theorem 25 -/

/-- **Theorem 25.** If `U` is a non-trivial cpo representing products and function
spaces, then there is a non-trivial cpo `D` which is the image of a closure on
`U` and satisfies `D ≅ D × D` and `D ≅ D → D`.

The paper's two displayed chains, unchanged:

`D × D ≅ (D → E) × (D → E) ≅ D → (E × E) ≅ D → E ≅ D`

`D → D ≅ D → (D → E) ≅ (D × D) → E ≅ D → E ≅ D`

with `Iso.prodCongr` and `Iso.funSpaceCongr` supplying every "≅" that rewrites
under an operator, `iso_funSpace_prod` (Lemma 8.3) the second step of the first
chain, and `iso_curry` (Lemma 8.4) the second step of the second. The second
chain consumes the first at its third step, which is why they are proved in this
order.

The hypothesis is `U` a **cpo**, weaker than the paper's "non-trivial domain":
no step spends algebraicity or countability of `K(U)`. `IsClosureOf D (cpoOf U)`
is the paper's "`D` is the image of a closure on `U`", and it is the relation
`Recursive.IsUniversal` is defined by. -/
theorem theorem_25 (U : Type u) [CompletePartialOrder U] [Nontrivial U]
    (hprod : IsRepresentable₂ U prodCpo) (hfun : IsRepresentable₂ U Cpo.funSpace) :
    ∃ D : Cpo.{u}, Nontrivial D.carrier ∧ IsClosureOf D (cpoOf U) ∧
      Iso D (prodCpo D D) ∧ Iso D (Cpo.funSpace D D) := by
  obtain ⟨D, E, hDnt, _, hDcl, _, hEiso, hDiso⟩ := lem24 U hprod hfun
  -- `D × D ≅ (D → E) × (D → E) ≅ D → (E × E) ≅ D → E ≅ D`.
  have hprodD : Iso (prodCpo D D) D :=
    ((((Iso.prodCongr hDiso hDiso).trans (iso_funSpace_prod D E E).symm).trans
      (Iso.funSpaceCongr (Iso.refl D) hEiso.symm)).trans hDiso.symm)
  -- `D → D ≅ D → (D → E) ≅ (D × D) → E ≅ D → E ≅ D`.
  have hfunD : Iso (Cpo.funSpace D D) D :=
    ((((Iso.funSpaceCongr (Iso.refl D) hDiso).trans (iso_curry D D E)).trans
      (Iso.funSpaceCongr hprodD (Iso.refl E))).trans hDiso.symm)
  exact ⟨D, hDnt, hDcl, hprodD.symm, hfunD.symm⟩

alias thm25 := theorem_25

/-! ## The instance at `U = P N`

> We note, in fact, that `D` will have `P N` itself represented by a closure on
> `U`. Hence, to get a non-trivial solution for `D ≅ D → D ≅ D × D`, take `U` in
> the theorem to be `P N`.

Both representability hypotheses are already proved at `P N`, and non-triviality
is `∅ ≠ N`. -/

/-- **Theorem 25 at `U = P N`.** There is a non-trivial cpo `D`, the image of a
closure on `P N`, with `D ≅ D × D` and `D ≅ D → D`.

`Recursive.powersetCpo` is `cpoOf (Set ℕ)`; the hypotheses are
`ScottDomains.PowerdomainRep.isRepresentable_prod` (r0031) and
`ScottDomains.lem23` (r0028), and `Nontrivial (Set ℕ)` is
`Set.nontrivial_of_nonempty`. -/
theorem theorem_25_powerset :
    ∃ D : Cpo.{0}, Nontrivial D.carrier ∧ IsClosureOf D powersetCpo ∧
      Iso D (prodCpo D D) ∧ Iso D (Cpo.funSpace D D) :=
  thm25 (Set ℕ) isRepresentable_prod lem23

alias thm25_powerset := theorem_25_powerset

/-- **`P N` is universal for the isomorphism class of the domain Theorem 25
produces.**

`Recursive.IsUniversal U C` is `∀ D, C D → IsClosureOf D U` — the
image-of-a-closure phrasing of *universal domain* that `RecursiveDomain.lean`
already fixes. Theorem 25 delivers `IsClosureOf D powersetCpo` for one `D`, and
`IsClosureOf.of_iso` spreads it over `D`'s whole isomorphism class, which is the
largest class the theorem supports: it is an **existence** statement about one
domain, not a claim that every cpo satisfying `X ≅ X × X ≅ X → X` is a closure
of `P N`.

This is deliberately not a new definition of universality. The other universal
statement about `P N` in the development, `Recursive.powersetCpo_isUniversal`,
is Theorem 22's — universality for the countably based algebraic lattices — and
uses the same predicate. -/
theorem theorem_25_isUniversal :
    ∃ D : Cpo.{0}, Nontrivial D.carrier ∧ Iso D (prodCpo D D) ∧
      Iso D (Cpo.funSpace D D) ∧ IsUniversal powersetCpo (fun X => Iso X D) := by
  obtain ⟨D, hnt, hcl, hp, hf⟩ := thm25_powerset
  exact ⟨D, hnt, hp, hf, fun X hX => IsClosureOf.of_iso hX hcl⟩

alias thm25_isUniversal := theorem_25_isUniversal

end ScottDomains.Universality

/- Axiom audit, by `#print axioms` (run, then removed so the build emits no
`info` lines). All 28 declarations depend only on the three standard axioms; none
depends on `sorryAx`.

  scottContinuous_orderIso              [propext, Quot.sound]
  scottContinuous_pairConst             []
  scottContinuous_pairConstRight        []
  prodOrderIso                          [propext, Quot.sound]
  scottHomOrderIso                      [propext, Classical.choice, Quot.sound]
  nontrivial_of_orderIso                [propext, Quot.sound]
  nontrivial_scottHom                   [propext, Classical.choice, Quot.sound]
  prodShuffle                           [Quot.sound]
  Iso                                   [Quot.sound]
  solves_iff_iso                        [Quot.sound]
  Iso.refl                              [Quot.sound]
  Iso.symm                              [propext, Quot.sound]
  Iso.trans                             [Quot.sound]
  Iso.prodCongr                         [propext, Quot.sound]
  Iso.funSpaceCongr                     [propext, Classical.choice, Quot.sound]
  Iso.nontrivial                        [propext, Quot.sound]
  IsClosureOf.of_iso                    [propext, Quot.sound]
  iso_funSpace_prod                     [propext, Classical.choice, Quot.sound]
  iso_curry                             [propext, Classical.choice, Quot.sound]
  cpoOf                                 []
  idClosureImageIso                     [propext, Quot.sound]
  thm21_image                           [propext, Classical.choice, Quot.sound]
  isRepresentable_selfProdSquare        [propext, Classical.choice, Quot.sound]
  isRepresentable_funSpaceConst         [propext, Classical.choice, Quot.sound]
  lem24                                 [propext, Classical.choice, Quot.sound]
  thm25                                 [propext, Classical.choice, Quot.sound]
  thm25_powerset                        [propext, Classical.choice, Quot.sound]
  thm25_isUniversal                     [propext, Classical.choice, Quot.sound]

Three declarations are axiom-free: the two pairing-continuity lemmas, whose
proofs are `IsLUB` bookkeeping in `Prod`, and `cpoOf`, which only bundles a
carrier with an instance. `Classical.choice` enters exactly where it enters
`ScottDomains.lem23` and `PowerdomainRep.isRepresentable_prod` — through
`ScottHom`'s `SupSet` instance, a `dite` on an undecidable continuity predicate —
which is why every declaration mentioning `ScottHom`'s cpo structure carries it
and none of the pure-`Prod` ones do. `lem24` and `thm25` add no new door: their
choice comes from `thm22`'s enumeration of the basis, inherited through the two
representability hypotheses. -/
