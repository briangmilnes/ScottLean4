import ScottDomains.EquilogicalSpaces.EquLimits
import ScottDomains.EquilogicalSpaces.EquProducts
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.Logic.Small.Basic

/-!
# Theorem 3.10's regular well-poweredness halves

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

**All proved.** `sat_range_eq_agreeSet` is (★) for an abstract regular mono;
`regularWellPowered` and `regularCoWellPowered` are Theorem 3.10's two regular
clauses, restated under the paper's number in `Theorems3.lean` as
`bauerBirkedalScott04_theorem_3_10_regularWellPowered` and
`…_regularCoWellPowered`.

The co-well-powered half is **not** a corollary of the well-powered one: it runs
in `Equᵒᵖ`, where the one-point space has no dual, and is carried instead by the
*kernel relation* `{ (x, y) | q x ≡ q y }` — the manuscript's "making the
equivalence relation coarser".
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

/-! ## Regular co-well-poweredness

    Not a corollary of the above. The dual argument runs in `Equᵒᵖ`, where
    regular monos are regular *epis* of `Equ`, and the separator that made (★)
    work — the one-point space — has no dual available. What replaces it is that
    a regular quotient is determined by its **kernel relation**

        K(q) = { (x, y) | q x ≡ q y }

    which is the manuscript's "forming a regular quotient is just making the
    equivalence relation coarser (putting equivalence classes together)". It
    lives in `Set (|𝒜| × |𝒜|)`, again a `Type u`.

    And unlike (★), no universal property is needed to *describe* `K(q)` — only
    to prove injectivity. -/

section CoWellPowered

variable {A : EquilogicalSpace.{u}}

/-- The kernel relation of a morphism out of `𝒜`. -/
def kerRel {Q : EquilogicalSpace.{u}} (q : A ⟶ Q) : Set (A.carrier × A.carrier) :=
  { p | Q.Rel ((homOut q).toFun p.1) ((homOut q).toFun p.2) }

/-- If one regular epi's kernel relation is contained in another's, the other
    coequalizes the first's pair. Dual to `arrow_equalizes_of_subset`. -/
theorem coequalizes_of_kerRel_subset {Q R : EquilogicalSpace.{u}}
    (q : A ⟶ Q) [IsRegularEpi q] (t : A ⟶ R) (h : kerRel q ⊆ kerRel t) :
    IsRegularEpi.left q ≫ t = IsRegularEpi.right q ≫ t := by
  refine hom_ext_of_rel ?_
  intro w w' hww'
  -- `(l w, r w)` is in `K(q)` by the coequalizer condition, hence in `K(t)`
  have hq : ((homOut (IsRegularEpi.left q)).toFun w,
      (homOut (IsRegularEpi.right q)).toFun w) ∈ kerRel q := by
    have hw := IsRegularEpi.w q
    have s1 := homOut_comp_apply (IsRegularEpi.left q) q
      (EquilogicalSpace.Rel.refl _ w)
    have s2 := homOut_comp_apply (IsRegularEpi.right q) q
      (EquilogicalSpace.Rel.refl _ w)
    have hmid := hom_apply_rel hw (EquilogicalSpace.Rel.refl _ w)
    exact EquilogicalSpace.Rel.trans (EquilogicalSpace.Rel.symm s1)
      (EquilogicalSpace.Rel.trans hmid s2)
  have ht := h hq
  -- and `r w ≡ r w'`, so `t` sends them to related points
  have hr := (homOut (IsRegularEpi.right q)).equivariant hww'
  have s3 := homOut_comp_apply (IsRegularEpi.left q) t
    (EquilogicalSpace.Rel.refl _ w)
  have s4 := homOut_comp_apply (IsRegularEpi.right q) t hww'
  exact EquilogicalSpace.Rel.trans s3
    (EquilogicalSpace.Rel.trans ht
      (EquilogicalSpace.Rel.trans
        ((homOut t).equivariant hr) (EquilogicalSpace.Rel.symm
          (homOut_comp_apply (IsRegularEpi.right q) t
            (EquilogicalSpace.Rel.refl _ w')))))

/-- A regular quotient of `𝒜`, as a regular subobject of `op 𝒜`. -/
noncomputable def kerImage
    (S : { S : Subobject (Opposite.op A) // IsRegularMono S.arrow }) :
    Set (A.carrier × A.carrier) :=
  kerRel S.1.arrow.unop

/-- **Regular quotients are determined by their kernel relation.** -/
theorem kerImage_injective : Function.Injective (kerImage (A := A)) := by
  rintro S T hST
  haveI hS : IsRegularEpi S.1.arrow.unop :=
    (isRegularEpi_unop_iff_isRegularMono _).mpr S.2
  haveI hT : IsRegularEpi T.1.arrow.unop :=
    (isRegularEpi_unop_iff_isRegularMono _).mpr T.2
  have hu := coequalizes_of_kerRel_subset S.1.arrow.unop T.1.arrow.unop
    (le_of_eq hST)
  have hv := coequalizes_of_kerRel_subset T.1.arrow.unop S.1.arrow.unop
    (le_of_eq hST.symm)
  set u := IsRegularEpi.desc S.1.arrow.unop T.1.arrow.unop hu with hudef
  set v := IsRegularEpi.desc T.1.arrow.unop S.1.arrow.unop hv with hvdef
  have hufac : S.1.arrow.unop ≫ u = T.1.arrow.unop := IsRegularEpi.fac _ _ hu
  have hvfac : T.1.arrow.unop ≫ v = S.1.arrow.unop := IsRegularEpi.fac _ _ hv
  have huv : u ≫ v = 𝟙 _ := by
    apply (cancel_epi S.1.arrow.unop).mp
    rw [← Category.assoc, hufac, hvfac, Category.comp_id]
  have hvu : v ≫ u = 𝟙 _ := by
    apply (cancel_epi T.1.arrow.unop).mp
    rw [← Category.assoc, hvfac, hufac, Category.comp_id]
  -- Build the iso in `Equ`, then `Iso.op` it: `(S : Equᵒᵖ) ⟶ (T : Equᵒᵖ)` is
  -- `Q_T ⟶ Q_S` in `Equ`, so the *hom* of the opposite iso is `v`, not `u`.
  -- inlined, not bound by `have`: `have` would erase the body and `.hom` would
  -- no longer reduce to `v`
  refine Subtype.ext (Subobject.eq_of_comm
    (Iso.op (⟨v, u, hvu, huv⟩ : (Subobject.underlying.obj T.1).unop
      ≅ (Subobject.underlying.obj S.1).unop)) ?_)
  exact Quiver.Hom.unop_inj (by simpa using hvfac)

/-- **Theorem 3.10, regular co-well-poweredness**: no object of `Equ` has a
    proper class of non-isomorphic regular quotients. -/
theorem regularCoWellPowered (A : EquilogicalSpace.{u}) :
    Small.{u} { S : Subobject (Opposite.op A) // IsRegularMono S.arrow } :=
  small_of_injective (kerImage_injective (A := A))

end CoWellPowered

end ScottDomains.EquilogicalSpaces
