import ScottDomains.EquilogicalSpaces.EquLimits
import ScottDomains.EquilogicalSpaces.EquProducts
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.Logic.Small.Basic

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

/-! ## Applying a morphism at a point

    A morphism of `Equ` is a class, so "its value at `x`" means the value of a
    chosen representative — `homOut` from `EquLimits.lean`. Different choices
    give `≡`-related values, which is all any statement below needs. -/

/-- Equal morphisms have `≡`-related values at `≡`-related points. -/
theorem hom_apply_rel {A B : EquilogicalSpace.{u}} {f g : A ⟶ B} (h : f = g)
    {x y : A.carrier} (hxy : A.Rel x y) :
    B.Rel ((homOut f).toFun x) ((homOut g).toFun y) :=
  Quotient.exact ((homOut_spec f).trans (h.trans (homOut_spec g).symm)) x y hxy

/-- A representative of a composite agrees, up to `≡`, with the composite of
    representatives. -/
theorem homOut_comp_apply {A B C : EquilogicalSpace.{u}} (f : A ⟶ B) (g : B ⟶ C)
    {x y : A.carrier} (hxy : A.Rel x y) :
    C.Rel ((homOut (f ≫ g)).toFun x) ((homOut g).toFun ((homOut f).toFun y)) := by
  have hfg : (f ≫ g) = Quotient.mk _
      (Equivariant.comp (homOut g) (homOut f)) := by
    conv_lhs => rw [← homOut_spec f, ← homOut_spec g]
    rfl
  exact Quotient.exact ((homOut_spec (f ≫ g)).trans hfg) x y hxy

/-- Two morphisms agreeing (up to `≡`) at `≡`-related points are equal. The
    `calc` goes through representatives because `Quotient.sound` needs both sides
    presented as classes. -/
theorem hom_ext_of_rel {A B : EquilogicalSpace.{u}} {f g : A ⟶ B}
    (h : ∀ x y, A.Rel x y →
      B.Rel ((homOut f).toFun x) ((homOut g).toFun y)) : f = g :=
  calc f = Quotient.mk _ (homOut f) := (homOut_spec f).symm
    _ = Quotient.mk _ (homOut g) := Quotient.sound h
    _ = g := homOut_spec g

/-! ## (★) for an abstract regular mono -/

section Star

variable {A X : EquilogicalSpace.{u}} (m : X ⟶ A) [IsRegularMono m]

/-- The set of points where the exhibiting pair agrees. -/
def agreeSet : Set A.carrier :=
  { a | (IsRegularMono.Z m).Rel
      ((homOut (IsRegularMono.left m)).toFun a)
      ((homOut (IsRegularMono.right m)).toFun a) }

/-- `⊆` of (★): everything in the saturated image satisfies the equation. Uses
    only `m ≫ left = m ≫ right`, not the universal property. -/
theorem sat_range_subset_agreeSet :
    A.sat (Set.range (homOut m).toFun) ⊆ agreeSet m := by
  rintro a ⟨_, ⟨x, rfl⟩, hax⟩
  have hw := IsRegularMono.w m
  have h1 := homOut_comp_apply m (IsRegularMono.left m) (X.setoid.refl x)
  have h2 := homOut_comp_apply m (IsRegularMono.right m) (X.setoid.refl x)
  have hmid := hom_apply_rel hw (X.setoid.refl x)
  have hkey :
      (IsRegularMono.Z m).Rel
        ((homOut (IsRegularMono.left m)).toFun ((homOut m).toFun x))
        ((homOut (IsRegularMono.right m)).toFun ((homOut m).toFun x)) :=
    EquilogicalSpace.Rel.trans (EquilogicalSpace.Rel.symm h1)
      (EquilogicalSpace.Rel.trans hmid h2)
  exact EquilogicalSpace.Rel.trans
    ((homOut (IsRegularMono.left m)).equivariant hax)
    (EquilogicalSpace.Rel.trans hkey
      (EquilogicalSpace.Rel.symm ((homOut (IsRegularMono.right m)).equivariant hax)))

/-- `⊇` of (★). **This is where the universal property is used**: the point map
    at `a` equalizes the pair, so it factors through `m`, and the factorisation
    names a point of `𝒳` whose image is `≡ a`. -/
theorem agreeSet_subset_sat_range :
    agreeSet m ⊆ A.sat (Set.range (homOut m).toFun) := by
  intro a ha
  set p : equTerminal.{u} ⟶ A := Quotient.mk _ (A.pointMap a) with hp
  have hpa : ∀ u : equTerminal.{u}.carrier, A.Rel ((homOut p).toFun u) a := fun u =>
    Quotient.exact ((homOut_spec p).trans hp) u u (equTerminal.setoid.refl u)
  -- the point map at `a` equalizes the pair, since it takes only the value `a`
  have hpeq : p ≫ IsRegularMono.left m = p ≫ IsRegularMono.right m := by
    refine hom_ext_of_rel ?_
    intro u v _
    have s1 := homOut_comp_apply p (IsRegularMono.left m) (equTerminal.setoid.refl u)
    have s2 := homOut_comp_apply p (IsRegularMono.right m) (equTerminal.setoid.refl v)
    have s3 := (homOut (IsRegularMono.left m)).equivariant (hpa u)
    have s4 := (homOut (IsRegularMono.right m)).equivariant (hpa v)
    exact EquilogicalSpace.Rel.trans s1
      (EquilogicalSpace.Rel.trans s3
        (EquilogicalSpace.Rel.trans ha
          (EquilogicalSpace.Rel.trans (EquilogicalSpace.Rel.symm s4)
            (EquilogicalSpace.Rel.symm s2))))
  -- so it factors through `m`, naming a point whose image is `≡ a`
  set k := IsRegularMono.lift m p hpeq with hk
  have hfac : k ≫ m = p := IsRegularMono.fac m p hpeq
  let star : equTerminal.{u}.carrier := PUnit.unit
  refine ⟨(homOut m).toFun ((homOut k).toFun star), ⟨_, rfl⟩, ?_⟩
  refine EquilogicalSpace.Rel.symm
    (EquilogicalSpace.Rel.trans ?_ (hpa star))
  exact EquilogicalSpace.Rel.trans
    (EquilogicalSpace.Rel.symm
      (homOut_comp_apply k m (equTerminal.setoid.refl star)))
    (hom_apply_rel hfac (equTerminal.setoid.refl star))

/-- **(★)**: the saturated image of a regular mono is exactly the set where its
    exhibiting pair agrees. -/
theorem sat_range_eq_agreeSet :
    A.sat (Set.range (homOut m).toFun) = agreeSet m :=
  Set.Subset.antisymm (sat_range_subset_agreeSet m) (agreeSet_subset_sat_range m)

end Star

/-! ## Regular well-poweredness

    With (★) in hand the rest is the manuscript's argument: two regular
    subobjects with the same saturated image each equalize the other's pair, so
    each factors through the other; the composites are identities because the
    arrows are monic; and the resulting iso commutes with the arrows. -/

section WellPowered

variable {A : EquilogicalSpace.{u}}

/-- The saturated image of a regular subobject — the "union of equivalence
    classes" the manuscript describes. -/
noncomputable def satImage (S : { S : Subobject A // IsRegularMono S.arrow }) :
    Set A.carrier :=
  A.sat (Set.range (homOut S.1.arrow).toFun)

/-- If one regular subobject's saturated image is contained in another's, its
    arrow equalizes the other's pair. -/
theorem arrow_equalizes_of_subset
    {S T : { S : Subobject A // IsRegularMono S.arrow }}
    (h : satImage S ⊆ satImage T) :
    haveI := T.2
    S.1.arrow ≫ IsRegularMono.left T.1.arrow
      = S.1.arrow ≫ IsRegularMono.right T.1.arrow := by
  haveI := S.2; haveI := T.2
  refine hom_ext_of_rel ?_
  intro x y hxy
  have hmem : (homOut S.1.arrow).toFun x ∈ agreeSet T.1.arrow := by
    rw [← sat_range_eq_agreeSet]
    exact h ⟨_, ⟨x, rfl⟩, EquilogicalSpace.Rel.refl A _⟩
  have hxy' := (homOut S.1.arrow).equivariant hxy
  have s1 := homOut_comp_apply S.1.arrow (IsRegularMono.left T.1.arrow) hxy
  have s2 := homOut_comp_apply S.1.arrow (IsRegularMono.right T.1.arrow)
    (EquilogicalSpace.Rel.refl _ y)
  have s3 := (homOut (IsRegularMono.right T.1.arrow)).equivariant hxy'
  exact EquilogicalSpace.Rel.trans
    (homOut_comp_apply S.1.arrow (IsRegularMono.left T.1.arrow)
      (EquilogicalSpace.Rel.refl _ x))
    (EquilogicalSpace.Rel.trans hmem
      (EquilogicalSpace.Rel.trans s3 (EquilogicalSpace.Rel.symm s2)))

/-- **Regular subobjects are determined by their saturated image.** -/
theorem satImage_injective : Function.Injective (satImage (A := A)) := by
  rintro S T hST
  haveI := S.2; haveI := T.2
  have hu := arrow_equalizes_of_subset (S := S) (T := T) (le_of_eq hST)
  have hv := arrow_equalizes_of_subset (S := T) (T := S) (le_of_eq hST.symm)
  set u := IsRegularMono.lift T.1.arrow S.1.arrow hu with hudef
  set v := IsRegularMono.lift S.1.arrow T.1.arrow hv with hvdef
  have hufac : u ≫ T.1.arrow = S.1.arrow := IsRegularMono.fac _ _ hu
  have hvfac : v ≫ S.1.arrow = T.1.arrow := IsRegularMono.fac _ _ hv
  haveI : Mono S.1.arrow := inferInstance
  haveI : Mono T.1.arrow := inferInstance
  have huv : u ≫ v = 𝟙 _ := by
    apply (cancel_mono S.1.arrow).mp
    rw [Category.assoc, hvfac, hufac, Category.id_comp]
  have hvu : v ≫ u = 𝟙 _ := by
    apply (cancel_mono T.1.arrow).mp
    rw [Category.assoc, hufac, hvfac, Category.id_comp]
  refine Subtype.ext (Subobject.eq_of_comm ⟨u, v, huv, hvu⟩ ?_)
  exact hufac

/-- **Theorem 3.10, regular well-poweredness**: the regular subobjects of every
    object of `Equ` form a set.

    `satImage` lands in `Set A.carrier`, which is a `Type u`, and is injective —
    so `small_of_injective` finishes. This is the manuscript's "the regular
    subobjects are obtained by selecting some equivalence classes and taking the
    union of them to form a subspace", made precise. -/
theorem regularWellPowered (A : EquilogicalSpace.{u}) :
    Small.{u} { S : Subobject A // IsRegularMono S.arrow } :=
  small_of_injective (satImage_injective (A := A))

end WellPowered

end ScottDomains.EquilogicalSpaces
