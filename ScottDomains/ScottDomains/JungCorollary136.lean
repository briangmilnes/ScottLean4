import ScottDomains.JungFinite
import ScottDomains.Combinator

/-!
# Jung's Proposition 1.34 and Corollary 1.36

A. Jung, *Cartesian Closed Categories of Domains*, CWI Tract 66 (1989), §1.5
("Directed-complete partial orders with a continuous function space"), printed
pages 46–50. Both statements are quoted from the source PDF in
`ScottDomains/papers/`, not from a secondary summary:

> **Proposition 1.34** Let `D` be a dcpo with a continuous function space and let
> `f : D → D` be way-below `id_D`. Then for all `d ∈ D`, `f(d)` is way-below `d`.

> **Corollary 1.36** If `D` is a dcpo with a continuous function space and if for
> `f, g ∈ [D → D]`, `f` is way-below `g`, then `f(d)` is way-below `g(d)` for all
> `d ∈ D`.

Corollary 1.36 at `f = g` compact says a compact function has compact values; at
`g = id` it says a compact deflation's fixed points are compact, which is what
`JungFinite.jung_lemma_2_2` consumes and what `fixedPointOfCompactDeflationIsCompact`
discharges here.

## The proof given here is not Jung's, and is shorter

Jung proves 1.34 by restricting to the principal ideal `↓e`: he cites Proposition
1.22 (the function space of a retract is continuous) to know `[↓e → ↓e]` is
continuous, then Proposition 1.5(i) (in a *continuous* dcpo, `≪` may be tested
against directed families whose supremum is the element itself) to lift
`f|↓e ≪ id_{↓e}` from families with supremum exactly `id_{↓e}` to all of them,
and only then applies the constant functions `c_{e_j}`, which are available on
`↓e` because `↓e` has a top element. Three prerequisites, one subtype, and one
retraction.

Jung's appeal to Proposition 1.22 is sound but he does not say why `↓e` is a
retract of `D`; it is, via `cap e` below — `x ↦ x` on `↓e` and `x ↦ e` off it —
which is monotone precisely because `↓e` is a lower set, and Scott continuous
because a directed set whose supremum escapes `↓e` already has a member outside
`↓e`. That observation is what makes the shorter route visible.

The route taken here **never forms `↓e`**. Two explicit functions on `D` do all
the work:

| # | Function | Definition | Role |
| -- | -------- | ---------- | ---- |
| 1 | `cap e` | `x ↦ if x ≤ e then x else e` | its compact approximants index the family below |
| 2 | `extend e F` | `x ↦ if x ≤ e then F x else x` | extension of `F` by the identity off `↓e` |

`extend e F` is monotone exactly when `F x ≤ x` on `↓e`, which is what `F ≤ cap e`
says — this is the condition r0037 measured as the obstruction to the restriction
route, and it is met here rather than circumvented. Given `f ≪ id_D` and a
directed `s` with `IsLUB s e` and `d ≤ e`, the argument is:

1. `{extend e F | F ∈ K(D → D), F ⊑ cap e}` is directed with least upper bound
   `id_D` — the least-upper-bound half is `ScottHom.isLUB_eval_image_of_isLUB`
   against `IsAlgebraic.isLUB_compactsBelow (cap e)`, evaluated at points of `↓e`;
2. `f ≪ id_D` therefore yields a **compact** `F ⊑ cap e` with `f ⊑ extend e F`;
3. the constant functions `{c_z | z ∈ s}` are directed with least upper bound
   `c_e`, and `F ⊑ cap e ⊑ c_e`, so **compactness of `F`** gives `z ∈ s` with
   `F ⊑ c_z`;
4. `d ≤ e`, so `f(d) ≤ (extend e F)(d) = F(d) ≤ z`.

Step 3 is where Jung needs `↓e`'s top element; here `c_e` supplies it on all of
`D` because `cap e` is bounded by `e` everywhere. Nothing in the argument uses
algebraicity of `D` itself, only `IsAlgebraic (ScottHom α α)`, and that only to
produce a directed family of compacts with least upper bound `cap e`. Under
Jung's weaker hypothesis — `[D → D]` merely *continuous* — the same script runs
with `{F | F ≪ cap e}` in place of `compactsBelow (cap e)` and `WayBelow F (cap e)`
in place of compactness at step 3; the development carries `IsAlgebraic`, so that
is the form stated.

Corollary 1.36 then follows in four lines, as in Jung: `g` is the least upper
bound of `{p ∘ g | p ≪ id}` by continuity of the function space, so `f ≪ g`
produces a compact `p ⊑ id` with `f ⊑ p ∘ g`, and Proposition 1.34 applied to `p`
gives `f(d) ≤ p(g(d)) ≪ g(d)`.
-/

namespace ScottDomains.JungCorollary136

open ScottDomains ScottDomains.ContinuousConstruction ScottDomains.Combinator

variable {α : Type*} [CompletePartialOrder α] {e : α}

/-! ## `cap e`: the retraction of `D` onto the principal ideal `↓e` -/

section Cap

open Classical in
/-- `cap e` as a bare function: the identity on `↓e`, and `e` everywhere else.
`x ≤ e` is not decidable in general, so the branch is classical, following
`ScottHom.stepFun`. -/
noncomputable def capFun (e : α) : α → α := fun x => if x ≤ e then x else e

theorem capFun_of_le {x : α} (h : x ≤ e) : capFun e x = x := by
  classical simp only [capFun, if_pos h]

theorem capFun_of_not_le {x : α} (h : ¬ x ≤ e) : capFun e x = e := by
  classical simp only [capFun, if_neg h]

/-- Every value of `cap e` lies in `↓e`. This is what lets the constant function
`c_e` dominate `cap e` on all of `D`, which is the step Jung has to move into
`[↓e → ↓e]` to obtain. -/
theorem capFun_le (x : α) : capFun e x ≤ e := by
  by_cases h : x ≤ e
  · exact (capFun_of_le h).le.trans h
  · exact (capFun_of_not_le h).le

/-- `cap e` is monotone. The only case needing an argument is `x ≤ e` and
`¬ y ≤ e`, where the value drops from `x` to `e` and `x ≤ e` is the hypothesis
itself; the case `¬ x ≤ e` with `y ≤ e` cannot occur because `↓e` is a lower
set. -/
theorem monotone_capFun (e : α) : Monotone (capFun e) := by
  intro x y hxy
  by_cases hx : x ≤ e
  · by_cases hy : y ≤ e
    · rw [capFun_of_le hx, capFun_of_le hy]
      exact hxy
    · rw [capFun_of_le hx, capFun_of_not_le hy]
      exact hx
  · have hy : ¬ y ≤ e := fun h => hx (hxy.trans h)
    exact le_of_eq (by rw [capFun_of_not_le hx, capFun_of_not_le hy])

/-- `cap e` is Scott continuous. The one real case: if the least upper bound `a`
of a directed `s` escapes `↓e`, then some member of `s` escapes it too — else `e`
would be an upper bound of `s` and hence above `a` — and that member already takes
the value `e`. -/
theorem scottContinuous_capFun (e : α) : ScottContinuous (capFun e) := by
  intro s hne hs a ha
  by_cases hae : a ≤ e
  · have himg : (capFun e) '' s = s := by
      refine Set.Subset.antisymm ?_ ?_
      · rintro _ ⟨x, hx, rfl⟩
        rwa [capFun_of_le ((ha.1 hx).trans hae)]
      · intro x hx
        exact ⟨x, hx, capFun_of_le ((ha.1 hx).trans hae)⟩
    rw [himg, capFun_of_le hae]
    exact ha
  · obtain ⟨x₀, hx₀, hx₀e⟩ : ∃ x ∈ s, ¬ x ≤ e := by
      by_contra hcon
      exact hae (ha.2 fun x hx => not_not.mp fun hxe => hcon ⟨x, hx, hxe⟩)
    rw [capFun_of_not_le hae]
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact capFun_le x
    · intro u hu
      have h := hu ⟨x₀, hx₀, rfl⟩
      rwa [capFun_of_not_le hx₀e] at h

/-- `cap e` bundled. It is a retraction of `D` onto `↓e`: idempotent, with image
exactly `↓e`. Jung's Proposition 1.22 is applied to this retraction; the proof
below does not need Proposition 1.22, only the function itself. -/
noncomputable def cap (e : α) : ScottHom α α := ⟨capFun e, scottContinuous_capFun e⟩

@[simp] theorem cap_apply (e x : α) : cap e x = capFun e x := rfl

/-- Below `cap e`, a function is a deflation on `↓e`. This is the hypothesis that
makes `extend e F` monotone, and the reason the family of step 1 is indexed by
`compactsBelow (cap e)` rather than by `compactsBelow idHom`. -/
theorem le_self_of_mem_compactsBelow_cap {F : ScottHom α α}
    (hF : F ∈ compactsBelow (cap e)) {x : α} (hx : x ≤ e) : F x ≤ x := by
  have h := hF.2 x
  dsimp only at h
  rwa [cap_apply, capFun_of_le hx] at h

end Cap

/-! ## `extend e F`: extension by the identity off `↓e` -/

section Extend

open Classical in
/-- `extend e F` as a bare function: `F` on `↓e`, the identity elsewhere. -/
noncomputable def extFun (e : α) (F : α → α) : α → α := fun x => if x ≤ e then F x else x

theorem extFun_of_le {F : α → α} {x : α} (h : x ≤ e) : extFun e F x = F x := by
  classical simp only [extFun, if_pos h]

theorem extFun_of_not_le {F : α → α} {x : α} (h : ¬ x ≤ e) : extFun e F x = x := by
  classical simp only [extFun, if_neg h]

/-- Monotonicity, and the exact hypothesis it costs. For `x ≤ e ` and `y` outside
`↓e` above `x` the extension must produce `F x ≤ y`, and `F x ≤ x ≤ y` is the only
route — so `F` must be a deflation *on `↓e`*, which is `hF`. r0037 recorded this
as the obstruction to restricting a compact deflation; it is met here because the
family is indexed below `cap e`, not below `idHom`. -/
theorem monotone_extFun {F : ScottHom α α} (hF : ∀ x, x ≤ e → F x ≤ x) :
    Monotone (extFun e ⇑F) := by
  intro x y hxy
  by_cases hx : x ≤ e
  · by_cases hy : y ≤ e
    · rw [extFun_of_le hx, extFun_of_le hy]
      exact F.monotone hxy
    · rw [extFun_of_le hx, extFun_of_not_le hy]
      exact (hF x hx).trans hxy
  · have hy : ¬ y ≤ e := fun h => hx (hxy.trans h)
    rw [extFun_of_not_le hx, extFun_of_not_le hy]
    exact hxy

/-- Scott continuity. When the least upper bound `a` of a directed `s` lies in
`↓e` the extension agrees with `F` on all of `s`, and `F`'s own continuity
finishes. When `a` escapes `↓e`, the members of `s` outside `↓e` are **cofinal**
in `s` — directedness moves any member above one of them — and on those the
extension is the identity, so the image has least upper bound `a`. -/
theorem scottContinuous_extFun {F : ScottHom α α} (hF : ∀ x, x ≤ e → F x ≤ x) :
    ScottContinuous (extFun e ⇑F) := by
  intro s hne hs a ha
  by_cases hae : a ≤ e
  · have hsub : ∀ x ∈ s, x ≤ e := fun x hx => (ha.1 hx).trans hae
    have himg : (extFun e ⇑F) '' s = (⇑F) '' s := by
      refine Set.Subset.antisymm ?_ ?_
      · rintro _ ⟨x, hx, rfl⟩
        exact ⟨x, hx, (extFun_of_le (hsub x hx)).symm⟩
      · rintro _ ⟨x, hx, rfl⟩
        exact ⟨x, hx, extFun_of_le (hsub x hx)⟩
    rw [himg, extFun_of_le hae]
    exact F.scottContinuous hne hs ha
  · obtain ⟨x₀, hx₀, hx₀e⟩ : ∃ x ∈ s, ¬ x ≤ e := by
      by_contra hcon
      exact hae (ha.2 fun x hx => not_not.mp fun hxe => hcon ⟨x, hx, hxe⟩)
    rw [extFun_of_not_le hae]
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      by_cases hx' : x ≤ e
      · rw [extFun_of_le hx']
        exact (hF x hx').trans (ha.1 hx)
      · rw [extFun_of_not_le hx']
        exact ha.1 hx
    · intro u hu
      refine ha.2 fun x hx => ?_
      by_cases hx' : x ≤ e
      · obtain ⟨w, hw, hxw, hx₀w⟩ := hs x hx x₀ hx₀
        have hwe : ¬ w ≤ e := fun h => hx₀e (hx₀w.trans h)
        have h := hu ⟨w, hw, rfl⟩
        rw [extFun_of_not_le hwe] at h
        exact hxw.trans h
      · have h := hu ⟨x, hx, rfl⟩
        rwa [extFun_of_not_le hx'] at h

/-- `extend e F` bundled, for `F` a deflation on `↓e`. -/
noncomputable def extend (e : α) (F : ScottHom α α) (hF : ∀ x, x ≤ e → F x ≤ x) :
    ScottHom α α :=
  ⟨extFun e ⇑F, scottContinuous_extFun hF⟩

@[simp] theorem extend_apply {F : ScottHom α α} (hF : ∀ x, x ≤ e → F x ≤ x) (x : α) :
    extend e F hF x = extFun e ⇑F x := rfl

/-- The extension attached to a compact approximant of `cap e`; the hypothesis of
`extend` is supplied by `le_self_of_mem_compactsBelow_cap`. -/
noncomputable def extendOf {F : ScottHom α α} (hF : F ∈ compactsBelow (cap e)) :
    ScottHom α α :=
  extend e F fun _ hx => le_self_of_mem_compactsBelow_cap hF hx

@[simp] theorem extendOf_apply {F : ScottHom α α} (hF : F ∈ compactsBelow (cap e)) (x : α) :
    extendOf hF x = extFun e ⇑F x := rfl

/-- Extension is monotone in the function extended: on `↓e` it is `F`, and off
`↓e` both sides are the identity. -/
theorem extFun_le_extFun {F₁ F₂ : ScottHom α α} (h : F₁ ≤ F₂) (x : α) :
    extFun e ⇑F₁ x ≤ extFun e ⇑F₂ x := by
  by_cases hx : x ≤ e
  · rw [extFun_of_le hx, extFun_of_le hx]
    exact h x
  · exact le_of_eq (by rw [extFun_of_not_le hx, extFun_of_not_le hx])

/-- The family of step 1: the extensions by the identity of the compact
approximants of `cap e`. Its members are named by their underlying functions so
that membership carries no proof term. -/
def extSet (e : α) : Set (ScottHom α α) :=
  {G | ∃ F ∈ compactsBelow (cap e), ⇑G = extFun e ⇑F}

theorem extendOf_mem {F : ScottHom α α} (hF : F ∈ compactsBelow (cap e)) :
    extendOf hF ∈ extSet e := ⟨F, hF, rfl⟩

theorem extSet_nonempty (e : α) : (extSet e).Nonempty :=
  ⟨extendOf (bot_mem_compactsBelow (cap e)), extendOf_mem _⟩

end Extend

/-! ## The family of extensions, and Proposition 1.34 -/

section Prop134

variable [IsAlgebraic (ScottHom α α)]

/-- Directed, because `compactsBelow (cap e)` is — that is algebraicity of the
function space — and extension is monotone. -/
theorem directedOn_extSet (e : α) : DirectedOn (· ≤ ·) (extSet e) := by
  rintro G₁ ⟨F₁, hF₁, hG₁⟩ G₂ ⟨F₂, hF₂, hG₂⟩
  obtain ⟨F₃, hF₃, h₁₃, h₂₃⟩ :=
    IsAlgebraic.directedOn_compactsBelow (cap e) F₁ hF₁ F₂ hF₂
  refine ⟨extendOf hF₃, extendOf_mem hF₃, ?_, ?_⟩
  · intro x
    dsimp only
    rw [congrFun hG₁ x]
    exact extFun_le_extFun h₁₃ x
  · intro x
    dsimp only
    rw [congrFun hG₂ x]
    exact extFun_le_extFun h₂₃ x

/-- **The least upper bound of the extension family is the identity.** Off `↓e`
every member already *is* the identity, so a bound there is immediate. On `↓e`
the members are the compact approximants of `cap e`, whose values at a point of
`↓e` have least upper bound `cap e x = x`; that is
`ScottHom.isLUB_eval_image_of_isLUB` applied to
`IsAlgebraic.isLUB_compactsBelow (cap e)`. -/
theorem isLUB_extSet (e : α) : IsLUB (extSet e) (idHom : ScottHom α α) := by
  refine ⟨?_, ?_⟩
  · rintro G ⟨F, hF, hG⟩ x
    dsimp only
    rw [congrFun hG x]
    by_cases hx : x ≤ e
    · rw [extFun_of_le hx]
      exact le_self_of_mem_compactsBelow_cap hF hx
    · exact le_of_eq (extFun_of_not_le hx)
  · intro U hU x
    dsimp only
    by_cases hx : x ≤ e
    · have hlub := ScottHom.isLUB_eval_image_of_isLUB
        (IsAlgebraic.directedOn_compactsBelow (cap e))
        (IsAlgebraic.isLUB_compactsBelow (cap e)) x
      have hub : U x ∈
          upperBounds ((fun f : ScottHom α α => f x) '' compactsBelow (cap e)) := by
        rintro _ ⟨F, hF, rfl⟩
        have h := hU (extendOf_mem hF) x
        dsimp only at h
        rwa [extendOf_apply, extFun_of_le hx] at h
      have h := hlub.2 hub
      rwa [cap_apply, capFun_of_le hx] at h
    · have h := hU (extendOf_mem (bot_mem_compactsBelow (cap e))) x
      dsimp only at h
      rwa [extendOf_apply, extFun_of_not_le hx] at h

/-- **Jung 1989, Proposition 1.34.** If `f` is way below `id_D` in `[D → D]` then
`f(d)` is way below `d` for every `d`.

The four steps of the module docstring. Note where each hypothesis is spent:
`IsAlgebraic (ScottHom α α)` supplies the directed family of compacts below
`cap u` (steps 1 and 2), and **compactness of that approximant** — not
compactness of `f` — is what step 3 consumes against the constant functions.
`IsAlgebraic α` is never used. -/
theorem apply_wayBelow_of_wayBelow_idHom {f : ScottHom α α}
    (hf : f ≪ (idHom : ScottHom α α)) (d : α) : f d ≪ d := by
  intro s u hne hs hlub hdu
  -- Step 2: `f ≪ id` against the extension family gives a compact `F ⊑ cap u`.
  obtain ⟨G, hG, hfG⟩ :=
    hf (extSet u) idHom (extSet_nonempty u) (directedOn_extSet u) (isLUB_extSet u) le_rfl
  obtain ⟨F, hF, hGF⟩ := hG
  -- Step 3: the constant functions on `s`, directed with least upper bound `c_u`.
  have hCdir : DirectedOn (· ≤ ·)
      ((fun z : α => (ScottHom.const z : ScottHom α α)) '' s) := by
    rintro _ ⟨z₁, hz₁, rfl⟩ _ ⟨z₂, hz₂, rfl⟩
    obtain ⟨z₃, hz₃, h₁, h₂⟩ := hs z₁ hz₁ z₂ hz₂
    exact ⟨ScottHom.const z₃, ⟨z₃, hz₃, rfl⟩, fun _ => h₁, fun _ => h₂⟩
  have hClub : IsLUB ((fun z : α => (ScottHom.const z : ScottHom α α)) '' s)
      (ScottHom.const u) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩ _
      exact hlub.1 hz
    · intro V hV x
      exact hlub.2 fun z hz => hV ⟨z, hz, rfl⟩ x
  have hFu : F ≤ (ScottHom.const u : ScottHom α α) := fun x => (hF.2 x).trans (capFun_le x)
  obtain ⟨_, ⟨z, hz, rfl⟩, hFz⟩ :=
    hF.1 _ (ScottHom.const u) (hne.image _) hCdir hClub hFu
  -- Step 4: evaluate at `d`, which lies in `↓u`.
  refine ⟨z, hz, ?_⟩
  have h := hfG d
  dsimp only at h
  rw [congrFun hGF d, extFun_of_le hdu] at h
  exact h.trans (hFz d)

end Prop134

/-! ## Corollary 1.36 and the predicate it discharges -/

section Cor136

variable [IsAlgebraic (ScottHom α α)]

/-- **Jung 1989, Corollary 1.36.** `f ≪ g` in `[D → D]` implies `f(d) ≪ g(d)` for
every `d`.

Jung's own four lines: by continuity of the function space `g` is the least upper
bound of `{p ∘ g | p ≪ id_D}`, so `f ≪ g` produces such a `p` with `p ∘ g ⊒ f`,
and Proposition 1.34 gives `f(d) ≤ p(g(d)) ≪ g(d)`. Here the family is indexed by
`compactsBelow idHom`, which algebraicity of the function space makes directed
with least upper bound `idHom`; that the composites then have least upper bound
`g` is `ScottHom.isLUB_eval_image_of_isLUB` evaluated at `g x`. -/
theorem apply_wayBelow_apply {f g : ScottHom α α} (h : f ≪ g) (d : α) : f d ≪ g d := by
  have hCdir : DirectedOn (· ≤ ·)
      ((fun p : ScottHom α α => comp p g) '' compactsBelow (idHom : ScottHom α α)) := by
    rintro _ ⟨p₁, hp₁, rfl⟩ _ ⟨p₂, hp₂, rfl⟩
    obtain ⟨p₃, hp₃, h₁, h₂⟩ :=
      IsAlgebraic.directedOn_compactsBelow (idHom : ScottHom α α) p₁ hp₁ p₂ hp₂
    exact ⟨comp p₃ g, ⟨p₃, hp₃, rfl⟩, fun x => h₁ (g x), fun x => h₂ (g x)⟩
  have hClub : IsLUB
      ((fun p : ScottHom α α => comp p g) '' compactsBelow (idHom : ScottHom α α)) g := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨p, hp, rfl⟩ x
      exact hp.2 (g x)
    · intro V hV x
      have hlub := ScottHom.isLUB_eval_image_of_isLUB
        (IsAlgebraic.directedOn_compactsBelow (idHom : ScottHom α α))
        (IsAlgebraic.isLUB_compactsBelow (idHom : ScottHom α α)) (g x)
      refine hlub.2 ?_
      rintro _ ⟨p, hp, rfl⟩
      exact hV ⟨p, hp, rfl⟩ x
  obtain ⟨_, ⟨p, hp, rfl⟩, hfp⟩ :=
    h _ g ((compactsBelow_nonempty (idHom : ScottHom α α)).image _) hCdir hClub le_rfl
  have hpid : p ≪ (idHom : ScottHom α α) :=
    WayBelow.trans_le ((wayBelow_self_iff_isCompactElement p).mpr hp.1) hp.2
  exact LE.le.trans_wayBelow (hfp d) (apply_wayBelow_of_wayBelow_idHom hpid (g d))

/-- **A compact function has compact values.** Corollary 1.36 at `f = g`: a
compact `g` is way below itself, so `g(d) ≪ g(d)`, which on the diagonal *is*
`IsCompactElement (g d)` (`wayBelow_self_iff_isCompactElement`, an `Iff.rfl`). -/
theorem isCompactElement_apply {g : ScottHom α α} (hg : IsCompactElement g) (d : α) :
    IsCompactElement (g d) :=
  (wayBelow_self_iff_isCompactElement (g d)).mp
    (apply_wayBelow_apply ((wayBelow_self_iff_isCompactElement g).mpr hg) d)

/-- **The remaining hypothesis of `JungFinite.jung_lemma_2_2`, discharged.**

`JungFinite.FixedPointOfCompactDeflationIsCompact α` asks that a fixed point of a
compact deflation be compact. A compact `f` is way below itself, hence way below
`idHom` once `f ⊑ id`; Proposition 1.34 then gives `f(d) ≪ d`, and `f d = d`
turns that into `d ≪ d`, which is `IsCompactElement d`.

The predicate is stated at `[CompletePartialOrder α]`; this proof adds
`[IsAlgebraic (ScottHom α α)]`, which both `JungFinite.jung_lemma_2_2` and
`JungFinite.theorem_18_of_propertyM` already carry. -/
theorem fixedPointOfCompactDeflationIsCompact :
    JungFinite.FixedPointOfCompactDeflationIsCompact α := by
  intro f hf hfle d hfd
  have hfid : f ≪ (idHom : ScottHom α α) :=
    WayBelow.trans_le ((wayBelow_self_iff_isCompactElement f).mpr hf) fun z => hfle z
  have hd := apply_wayBelow_of_wayBelow_idHom hfid d
  rw [hfd] at hd
  exact (wayBelow_self_iff_isCompactElement d).mp hd

end Cor136

end ScottDomains.JungCorollary136
