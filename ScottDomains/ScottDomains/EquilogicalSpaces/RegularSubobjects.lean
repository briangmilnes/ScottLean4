import ScottDomains.EquilogicalSpaces.EquLimits

/-!
# Towards Theorem 3.10's regular well-poweredness halves

The 1998 manuscript's proof sketch is the plan:

> The properties of being regular well-powered and regular co-well-powered follow
> from the corresponding properties of `Top₀` and the category of equivalence
> relations. But, one has to be careful to check that the regular subobjects are
> obtained by selecting some equivalence classes and taking the union of them to
> form a subspace; likewise, forming a regular quotient is just making the
> equivalence relation coarser (putting equivalence classes together). The
> trouble is that there are subobjects and quotients which are not formed in this
> simple way.

"Selecting some equivalence classes and taking the union" is exactly: a regular
subobject is determined by a **`≡`-saturated subset** of `|𝒜|`. Saturated subsets
live in `Set A.carrier`, which is a `Type u`, so `small_of_injective` then gives
`Small.{u}` and the theorem.

## The argument, in full

Let `m : 𝒮 ⟶ 𝒜` be a regular mono, exhibited as the equalizer of
`l, r : 𝒜 ⟶ 𝒵`, and let `T` be the saturated image of `m`. Then

    T = { a | l a ≡ r a }                                          (★)

* `⊆` is `m ≫ l = m ≫ r` read at a point, then transported along `≡`.
* `⊇` needs, for an *abstract* regular mono, the one-point space: a point `a`
  with `l a ≡ r a` gives a map `equTerminal ⟶ 𝒜` equalizing `l` and `r`, which
  the universal property factors through `𝒮`, naming a point of `𝒮` whose image
  is `≡ a`. That is what `pointMap` is for. For the *concrete* equalizer
  `eqObj` it is simpler still and needs no such argument — `a` together with its
  proof **is** a point of the subspace — which is what `equTerminal_detects`
  records.

Now if two regular subobjects have the same `T`, each arrow equalizes the other's
pair — by (★) and equivariance — so each factors through the other, and the two
factorisations compose to identities because the arrows are monic. That iso
commutes with the arrows, so `Subobject.eq_of_comm` makes the subobjects equal.
Injectivity of `S ↦ T`, hence smallness.

## Status

**Proved:** the saturation lemmas, `pointMap`, and `sat_range_eqInc` — which is
(★) for the *concrete* equalizer of `EquLimits.lean`. That last is the
`Equ`-specific content of the argument.

**Not done, and these are the theorems:** (★) for an *abstract* regular mono,
which needs Mathlib's `IsRegularMono` unpacked into a `Fork` and `pointMap` fed
through its universal property; and then the injectivity argument closing with
`Subobject.eq_of_comm`. So `Theorem310RegularWellPowered` and
`Theorem310RegularCoWellPowered` remain `Prop`-valued claims in `Theorems3.lean`
— **statements, not theorems** — and Theorem 3.10 is proved in two of its four
clauses.
-/

universe u

namespace ScottDomains.EquilogicalSpaces

open CategoryTheory CategoryTheory.Limits

/-! ## Saturated subsets -/

/-- The `≡`-saturation of a subset: everything related to something in it.
    "Selecting some equivalence classes and taking the union of them." -/
def EquilogicalSpace.sat (A : EquilogicalSpace.{u}) (T : Set A.carrier) :
    Set A.carrier := { a | ∃ b ∈ T, A.Rel a b }

namespace EquilogicalSpace

theorem subset_sat {A : EquilogicalSpace.{u}} (T : Set A.carrier) : T ⊆ A.sat T :=
  fun a ha => ⟨a, ha, A.setoid.refl a⟩

/-- A saturation is saturated: it absorbs `≡`. -/
theorem sat_saturated {A : EquilogicalSpace.{u}} {T : Set A.carrier} {a b : A.carrier}
    (hab : A.Rel a b) (hb : b ∈ A.sat T) : a ∈ A.sat T := by
  obtain ⟨c, hc, hbc⟩ := hb
  exact ⟨c, hc, A.setoid.trans hab hbc⟩

theorem sat_mono {A : EquilogicalSpace.{u}} {T T' : Set A.carrier} (h : T ⊆ T') :
    A.sat T ⊆ A.sat T' := fun _ ⟨b, hb, hab⟩ => ⟨b, h hb, hab⟩

end EquilogicalSpace

/-! ## The one-point space detects points

    This is the crux of the `⊇` half of (★), and the only step of the argument
    that is genuinely about `Equ` rather than about the subobject API. -/

/-- A point of `𝒜`, as a map out of the terminal object. Equivariance is
    reflexivity of `≡_𝒜` — available because `Equ`'s relations are total, and the
    reason the same trick would need care in `PEqu`. -/
def EquilogicalSpace.pointMap (A : EquilogicalSpace.{u}) (a : A.carrier) :
    Equivariant equTerminal A where
  toFun := fun _ => a
  continuous_toFun := continuous_const
  equivariant := fun _ => A.setoid.refl a

/-- **A point at which `l` and `r` agree lies in the equalizer's saturated
    image.**

    For the *concrete* equalizer this is immediate — `a` paired with its own
    proof is a point of the subspace, and `≡` is reflexive — so `pointMap` is not
    needed here. It is needed for the passage to an arbitrary regular mono, where
    the point has to be produced by the universal property instead. -/
theorem equTerminal_detects {A Z : EquilogicalSpace.{u}} (l r : Equivariant A Z)
    {a : A.carrier} (ha : Z.Rel (l.toFun a) (r.toFun a)) :
    a ∈ A.sat (Set.range (EquilogicalSpace.eqInc l r).toFun) :=
  ⟨a, ⟨⟨a, ha⟩, rfl⟩, A.setoid.refl a⟩

/-- The converse inclusion at the level of the concrete equalizer: every point of
    the equalizer's subspace satisfies `l a ≡ r a`, and so does everything
    `≡`-related to it. -/
theorem sat_range_eqInc_subset {A Z : EquilogicalSpace.{u}} (l r : Equivariant A Z) :
    A.sat (Set.range (EquilogicalSpace.eqInc l r).toFun)
      ⊆ { a | Z.Rel (l.toFun a) (r.toFun a) } := by
  rintro a ⟨_, ⟨x, rfl⟩, hax⟩
  exact Z.setoid.trans (l.equivariant hax)
    (Z.setoid.trans x.2 (Z.setoid.symm (r.equivariant hax)))

/-- **(★) for the concrete equalizer**: its saturated image is exactly the set of
    points where `l` and `r` agree. Both inclusions above, together. -/
theorem sat_range_eqInc {A Z : EquilogicalSpace.{u}} (l r : Equivariant A Z) :
    A.sat (Set.range (EquilogicalSpace.eqInc l r).toFun)
      = { a | Z.Rel (l.toFun a) (r.toFun a) } :=
  Set.Subset.antisymm (sat_range_eqInc_subset l r)
    (fun _ ha => equTerminal_detects l r ha)

end ScottDomains.EquilogicalSpaces
