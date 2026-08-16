import ScottDomains.EquilogicalSpaces.PartialEquilogical
import ScottDomains.Currying
import ScottDomains.FunctionSpaceDomain

/-!
# Theorem 3.8 and the currying step of Theorem 3.13

A. Bauer, L. Birkedal and D. S. Scott, *Equilogical Spaces*, TCS **315**(1):35–59,
2004, §3, `ScottDomains/papers/Bauer Birkedal Scott 2004 Equilogical Spaces.pdf`.

The paper's proof of Theorem 3.13 is three sentences:

> We have to show, that for any three structures in `PEqu`, say, `𝒜`, `ℬ`, and
> `𝒞`, there is a one-one correspondence between functions in the two spaces:
> `(𝒜 × ℬ → 𝒞)` and `(𝒜 → (ℬ → 𝒞))`. As we know, there is a particular one-one
> correspondence that is an isomorphism of the underlying algebraic lattices (and
> a homeomorphism of topological spaces). It only remains to show that the
> isomorphism preserves the partial equivalence relation. This is a
> "self-proving" theorem, in the sense that once the question is stated it is
> just a matter of unpacking the definitions.

This module holds the two halves that sentence names, and holds them apart:

| Half | Where it comes from | Status |
| ---- | ------------------- | ------ |
| the isomorphism of algebraic lattices | `ScottDomains.Currying.scottHomCurry` | **already proved in this package** |
| that it preserves the partial equivalence relation | `scottHomCurry_homRel` below | **proved here** |

So the "self-proving" step is now discharged, and it really is self-proving: the
two sides of `scottHomCurry_homRel` are the same quantifier prefix with the pair
`(x, u)` split or joined. The proof is one term.

`ScottDomains.Currying` supplies the first half as an *order* isomorphism
`ScottHom α (ScottHom β γ) ≃o ScottHom (α × β) γ`, with the joint-versus-separate
continuity argument — the genuinely hard part — already done.

## Why the relations are unbundled here

`HomRel` and `ProdRel` below take the relations as plain arguments rather than
reading them off `PartialEquilogicalSpace`s. Bundling would be circular at this
point: `homRel A B` as a relation *on a `PEqu` object* needs the function space
to be an object, i.e. needs `IsAlgebraic (ScottHom α β)`, which
`ScottDomains.FunctionSpaceDomain` supplies only for `β` bounded complete. That
side condition is real and is recorded as `Theorem38ExponentialIsObject` below
rather than assumed. The preservation result does not need it, so it is proved
without it.
-/

universe u

namespace ScottDomains.EquilogicalSpaces

open ScottDomains

/-! ## The product and exponential relations of Definition 3.11 -/

/-- The partial equivalence relation on a **product**: componentwise. -/
def ProdRel {X Y : Type u} (rX : X → X → Prop) (rY : Y → Y → Prop) :
    X × Y → X × Y → Prop :=
  fun p q => rX p.1 q.1 ∧ rY p.2 q.2

/-- The partial equivalence relation on an **exponential**, in Definition
    3.11(2)'s two-point form: `f ≡ g` iff `f` and `g` agree up to `≡` on
    `≡`-related arguments. -/
def HomRel {X Y : Type u} [CompletePartialOrder X] [CompletePartialOrder Y]
    (rX : X → X → Prop) (rY : Y → Y → Prop) (f g : ScottHom X Y) : Prop :=
  ∀ x y : X, rX x y → rY (f x) (g y)

section Preservation

variable {X Y Z : Type u}
  [CompletePartialOrder X] [CompletePartialOrder Y] [CompletePartialOrder Z]
  (rX : X → X → Prop) (rY : Y → Y → Prop) (rZ : Z → Z → Prop)

/-- **The "self-proving" step of Theorem 3.13**: the currying isomorphism
    `scottHomCurry` of `ScottDomains.Currying` preserves the partial equivalence
    relations, in both directions.

    Unpacked, the left side says

        ∀ x y, rX x y → ∀ u v, rY u v → rZ (g₁ x u) (g₂ y v)

    and the right side says

        ∀ p q, (rX p.1 q.1 ∧ rY p.2 q.2) → rZ (g₁ p.1 p.2) (g₂ q.1 q.2)

    which is the same prefix with the pair split or joined. The paper is right
    that nothing else is needed; the whole proof is the term below. -/
theorem scottHomCurry_homRel (g₁ g₂ : ScottHom X (ScottHom Y Z)) :
    HomRel rX (HomRel rY rZ) g₁ g₂ ↔
      HomRel (ProdRel rX rY) rZ (scottHomCurry g₁) (scottHomCurry g₂) :=
  ⟨fun h p q hpq => h p.1 q.1 hpq.1 p.2 q.2 hpq.2,
   fun h x y hxy u v huv => h (x, u) (y, v) ⟨hxy, huv⟩⟩

/-- The same statement read backwards along the isomorphism: currying a jointly
    continuous map preserves the relations. Immediate from
    `scottHomCurry_homRel` and `Equiv.symm_apply_apply`, but stated separately
    because it is the direction Theorem 3.13's transposition actually uses. -/
theorem scottHomCurry_symm_homRel (f₁ f₂ : ScottHom (X × Y) Z) :
    HomRel (ProdRel rX rY) rZ f₁ f₂ ↔
      HomRel rX (HomRel rY rZ) (scottHomCurry.symm f₁) (scottHomCurry.symm f₂) := by
  constructor
  · intro h x y hxy u v huv
    exact h (x, u) (y, v) ⟨hxy, huv⟩
  · intro h p q hpq
    exact h p.1 q.1 hpq.1 p.2 q.2 hpq.2

end Preservation

/-! ## What remains of Theorem 3.8 -/

/-- The exponential of two objects of `PEqu` is again an object: the function
    space of algebraic lattices is an algebraic lattice.

    `ScottDomains.FunctionSpaceDomain` proves `IsAlgebraic (ScottHom α β)` for
    `α` algebraic and `β` algebraic **and bounded complete**. Every complete
    lattice is bounded complete — `sSup` is a least upper bound of every subset,
    bounded or not — so the side condition is discharged for `ALat`; but the
    `BoundedComplete` instance for a `CompleteLattice` is not in the package and
    has to be supplied before `FunctionSpaceDomain`'s result can be applied here.
    That is the remaining obligation, and it is a one-instance job rather than a
    mathematical one. -/
def Theorem38ExponentialIsObject : Prop :=
  ∀ (X Y : Type u) (_ : CompleteLattice X) (_ : CompleteLattice Y),
    ScottDomains.IsAlgebraic X → ScottDomains.IsAlgebraic Y →
      ∀ _ : CompleteLattice (ScottHom X Y), ScottDomains.IsAlgebraic (ScottHom X Y)

/-- The **currying bijection** underlying Theorem 3.8, for algebraic lattices.

    Named for what it is. This is *not* "`ALat` is cartesian closed": it is the
    one-one correspondence the paper points at when it says "there is a
    particular one-one correspondence that is an isomorphism of the underlying
    algebraic lattices". Cartesian closure additionally requires the categorical
    packaging — a bundled `ALat`, its finite products, and the adjunction — none
    of which exists in the package yet, so full Theorem 3.8 cannot presently be
    given a type at all. -/
def Theorem38CurryingBijection : Prop :=
  ∀ (X Y Z : Type u) (_ : CompleteLattice X) (_ : CompleteLattice Y) (_ : CompleteLattice Z),
    ScottDomains.IsAlgebraic X → ScottDomains.IsAlgebraic Y → ScottDomains.IsAlgebraic Z →
      Nonempty (ScottHom X (ScottHom Y Z) ≃o ScottHom (X × Y) Z)

/-- **Proved**, and by `ScottDomains.Currying.scottHomCurry` directly — the
    algebraicity and lattice hypotheses go unused, since the bijection holds for
    arbitrary complete partial orders.

    Recording it separates what this package already establishes (the bijection)
    from what Theorem 3.8 still owes (the categorical packaging, and that the
    exponential is an *object* of `ALat`). Overstating this as cartesian closure
    would be the error the `regular`/`WellPowered` discipline elsewhere in this
    directory exists to prevent. -/
theorem theorem38_curryingBijection : Theorem38CurryingBijection.{u} :=
  fun _ _ _ _ _ _ _ _ _ => ⟨scottHomCurry⟩

end ScottDomains.EquilogicalSpaces
