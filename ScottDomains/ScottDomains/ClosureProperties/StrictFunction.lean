import ScottDomains.Skeleton.Lemma17
import ScottDomains.StrictHom
import ScottDomains.CompactFunction

/-!
# Lemma 17, the strict function space conjunct `D →⊥ E`

Gunter & Scott, *Semantic Domains*, §6.2, quoted from the source PDF:

> **Lemma 17** If `D` and `E` are bifinite domains, then so are the cpo's
> `D → E`, `D →⊥ E`, `D × E`, `D ⊗ E`, `D + E`, `D ⊕ E`, `D⊥`, `D♮`, `D♯` and
> `D♭`.
>
> **Proof:** … Suppose `p : D → D` and `q : E → E` are finitary projections.
> Given a continuous function `f : D → E`, define `(q, p)(f) = q ∘ f ∘ p`. The
> function `(q, p)` defines a finitary projection on `D → E`. Moreover, if `p`
> and `q` have finite images, then so does `(q, p)`.

The strict function space is proved with the **same** operator `(q, p)`, and this
file spends its length on the one fact that makes that legitimate: the basis of
`D →⊥ E` is the basis of `D → E` intersected with the strict functions, in *both*
directions.

* The easy direction (`isCompactElement_of_isCompactElement_val`): a strict `f`
  that is compact in `D → E` is compact in `D →⊥ E`, because the suprema of
  `D →⊥ E` are those of `D → E` (`StrictHom.lean` — strictness survives every
  supremum, so the subtype needs no case split).
* The direction with content (`isCompactElement_val_of_isCompactElement`): a
  compact of `D →⊥ E` is compact in `D → E`. A directed family in `D → E` need
  not consist of strict functions, so compactness in the subtype says nothing
  about it directly. The repair is the **strictification** `σ`, sending
  `g` to `x ↦ if x = ⊥ then ⊥ else g x`. It is continuous, it is below `g`, it
  fixes the strict functions, and — the step that does the work — it carries the
  least upper bound of a directed family to the least upper bound of the
  strictified family. So a directed family with a large enough supremum can be
  replaced by its strictification, at which point compactness in the subtype
  applies and `σ g ≤ g` transports the witness back.

With that, `(q, p)` transfers verbatim: `p_{N₁}` and `p_{N₂}` are strict, hence
`(q, p) f` is strict whenever `f` is, hence `(q, p)` restricts to a projection of
`D →⊥ E` with finite image, and `im((q,p)) ∩ (D →⊥ E)` is the finite normal
subposet the Plotkin condition asks for. `(q, p) f = f` for each compact `f` of
`u` is the step-function argument of `lem17_fun`, factored out here as
`exists_finite_projection_fixing` so that neither proof restates it.
-/

namespace ScottDomains.ClosureProperties

open ScottDomains

variable {α β : Type*} [CompletePartialOrder α] [CompletePartialOrder β]

/-! ### Strictification

`σ g = g` off the bottom and `⊥` at the bottom. Its continuity is where the
non-triviality sits: on a directed `d` whose least upper bound is not `⊥`, some
member of `d` is not `⊥`, and monotonicity of `g` pushes `g ⊥` under `σ` of that
member — which is why the value at `⊥` can be discarded without lowering the
supremum. -/

open Classical in
/-- `σ g`, as a bare function. -/
noncomputable def strictFun (g : ScottHom α β) : α → β := fun x => if x = ⊥ then ⊥ else g x

@[simp] theorem strictFun_bot (g : ScottHom α β) : strictFun g (⊥ : α) = ⊥ := by
  classical simp [strictFun]

theorem strictFun_of_ne_bot (g : ScottHom α β) {x : α} (h : x ≠ ⊥) : strictFun g x = g x := by
  classical simp [strictFun, h]

theorem strictFun_le (g : ScottHom α β) (x : α) : strictFun g x ≤ g x := by
  by_cases h : x = ⊥
  · subst h
    rw [strictFun_bot]
    exact bot_le
  · rw [strictFun_of_ne_bot g h]

theorem monotone_strictFun (g : ScottHom α β) : Monotone (strictFun g) := by
  intro x y hxy
  by_cases hx : x = ⊥
  · subst hx
    rw [strictFun_bot]
    exact bot_le
  · have hy : y ≠ ⊥ := fun h => hx (le_bot_iff.mp (h ▸ hxy))
    rw [strictFun_of_ne_bot g hx, strictFun_of_ne_bot g hy]
    exact g.monotone hxy

/-- **`σ g` is Scott continuous.** On a directed `d` with `⨆d = ⊥` every member
is `⊥` and both sides are `⊥`. Otherwise some `x₀ ∈ d` is not `⊥`, and the only
member whose value `σ` lowers is `⊥` itself, whose `g`-value is already below
`g x₀ = σ g x₀`. -/
theorem scottContinuous_strictFun (g : ScottHom α β) : ScottContinuous (strictFun g) := by
  intro d hne hd a hlub
  by_cases ha : a = ⊥
  · subst ha
    have hall : ∀ x ∈ d, x = ⊥ := fun x hx => le_bot_iff.mp (hlub.1 hx)
    constructor
    · rintro _ ⟨x, hx, rfl⟩
      rw [hall x hx]
    · intro v _
      rw [strictFun_bot]
      exact bot_le
  · constructor
    · rintro _ ⟨x, hx, rfl⟩
      exact monotone_strictFun g (hlub.1 hx)
    · intro v hv
      obtain ⟨x₀, hx₀, hx₀ne⟩ : ∃ x ∈ d, x ≠ ⊥ := by
        by_contra hcon
        refine ha (le_bot_iff.mp (hlub.2 fun x hx => le_of_eq ?_))
        by_contra hxne
        exact hcon ⟨x, hx, hxne⟩
      rw [strictFun_of_ne_bot g ha]
      refine (g.scottContinuous hne hd hlub).2 ?_
      rintro _ ⟨x, hx, rfl⟩
      by_cases hxb : x = ⊥
      · subst hxb
        calc g ⊥ ≤ g x₀ := g.monotone bot_le
          _ = strictFun g x₀ := (strictFun_of_ne_bot g hx₀ne).symm
          _ ≤ v := hv ⟨x₀, hx₀, rfl⟩
      · calc g x = strictFun g x := (strictFun_of_ne_bot g hxb).symm
          _ ≤ v := hv ⟨x, hx, rfl⟩

/-- `σ`, as a map into `D →⊥ E`. -/
noncomputable def strictHom (g : ScottHom α β) : StrictHom α β :=
  ⟨⟨strictFun g, scottContinuous_strictFun g⟩, strictFun_bot g⟩

@[simp] theorem strictHom_apply (g : ScottHom α β) (x : α) :
    (strictHom g).val x = strictFun g x := rfl

theorem strictHom_val_le (g : ScottHom α β) : (strictHom g).val ≤ g := fun x => strictFun_le g x

theorem monotone_strictHom : Monotone (strictHom : ScottHom α β → StrictHom α β) := by
  intro g h hgh x
  show strictFun g x ≤ strictFun h x
  by_cases hx : x = ⊥
  · subst hx
    rw [strictFun_bot]
    exact bot_le
  · rw [strictFun_of_ne_bot g hx, strictFun_of_ne_bot h hx]
    exact hgh x

/-- `σ` fixes the strict functions: that is what makes it a retraction onto
`D →⊥ E` and not merely a monotone map into it. -/
theorem strictHom_val_of_isStrict {g : ScottHom α β} (hg : IsStrict g) :
    (strictHom g).val = g := by
  refine ScottHom.ext fun x => ?_
  by_cases hx : x = ⊥
  · subst hx
    rw [strictHom_apply, strictFun_bot]
    exact hg.symm
  · rw [strictHom_apply, strictFun_of_ne_bot g hx]

/-! ### The basis of `D →⊥ E` is the basis of `D → E`, cut down -/

/-- Suprema in `D →⊥ E` are those of `D → E`: a least upper bound in the subtype
is a least upper bound of the image, provided the family is directed (which is
what puts the ambient supremum back inside the subtype). -/
theorem isLUB_val_image_of_isLUB {s : Set (StrictHom α β)}
    (hd : DirectedOn (· ≤ ·) s) {u : StrictHom α β} (h : IsLUB s u) :
    IsLUB (Subtype.val '' s) (u.val : ScottHom α β) := by
  have hdv : DirectedOn (· ≤ ·) (Subtype.val '' s) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨c, hc, hac, hbc⟩ := hd a ha b hb
    exact ⟨c.val, ⟨c, hc, rfl⟩, hac, hbc⟩
  have hu : u = sSup s := h.unique hd.isLUB_sSup
  rw [hu]
  exact hdv.isLUB_sSup

/-- **A strict function compact in `D → E` is compact in `D →⊥ E`.** The directed
families of the subtype are directed families of the ambient space with the same
least upper bounds, so the ambient witness is already a member of the subtype
family. -/
theorem isCompactElement_of_isCompactElement_val {f : StrictHom α β}
    (h : IsCompactElement (f.val : ScottHom α β)) : IsCompactElement f := by
  intro s u hne hd hlub hfu
  obtain ⟨_, ⟨g, hg, rfl⟩, hle⟩ :=
    h (Subtype.val '' s) u.val (hne.image _)
      (by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        obtain ⟨c, hc, hac, hbc⟩ := hd a ha b hb
        exact ⟨c.val, ⟨c, hc, rfl⟩, hac, hbc⟩)
      (isLUB_val_image_of_isLUB hd hlub) hfu
  exact ⟨g, hg, hle⟩

/-- **A compact of `D →⊥ E` is compact in `D → E`.** This is the direction that
needs strictification: replace the ambient directed family `s` by `σ '' s`, which
lies in `D →⊥ E`, is directed, and has `σ F` as its least upper bound *there*.
Compactness in the subtype then produces `g ∈ s` with `f ≤ σ g`, and `σ g ≤ g`
finishes. The least-upper-bound step is where `σ` earns its keep: off `⊥` the
value of `σ F` is `F`'s, which is the supremum of the values of the family by
`isLUB_eval_image_of_isLUB`. -/
theorem isCompactElement_val_of_isCompactElement {f : StrictHom α β}
    (h : IsCompactElement f) : IsCompactElement (f.val : ScottHom α β) := by
  intro s F hne hd hlub hfF
  have hdir : DirectedOn (· ≤ ·) ((strictHom : ScottHom α β → StrictHom α β) '' s) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨c, hc, hac, hbc⟩ := hd a ha b hb
    exact ⟨strictHom c, ⟨c, hc, rfl⟩, monotone_strictHom hac, monotone_strictHom hbc⟩
  have hlub' : IsLUB ((strictHom : ScottHom α β → StrictHom α β) '' s) (strictHom F) := by
    constructor
    · rintro _ ⟨g, hg, rfl⟩
      exact monotone_strictHom (hlub.1 hg)
    · intro v hv x
      show strictFun F x ≤ v.val x
      by_cases hx : x = ⊥
      · subst hx
        rw [strictFun_bot]
        exact bot_le
      · rw [strictFun_of_ne_bot F hx]
        refine (ScottHom.isLUB_eval_image_of_isLUB hd hlub x).2 ?_
        rintro _ ⟨g, hg, rfl⟩
        calc g x = strictFun g x := (strictFun_of_ne_bot g hx).symm
          _ ≤ v.val x := hv ⟨g, hg, rfl⟩ x
  have hfstrict : f ≤ strictHom F := by
    intro x
    show f.val x ≤ strictFun F x
    by_cases hx : x = ⊥
    · subst hx
      rw [strictFun_bot]
      exact le_of_eq f.2
    · rw [strictFun_of_ne_bot F hx]
      exact hfF x
  obtain ⟨_, ⟨g, hg, rfl⟩, hle⟩ :=
    h _ (strictHom F) (hne.image _) hdir hlub' hfstrict
  exact ⟨g, hg, le_trans hle (strictHom_val_le g)⟩

/-! ### `(q, p)` and the two projections it is built from -/

/-- `p_N` is strict: `⊥ ∈ N` (Lemma 4.3) and `p_N` fixes every member of `N`. -/
theorem normalHom_bot [IsAlgebraic α] {N : Set α} (hN : N ◁ compacts α) :
    (normalHom hN) (⊥ : α) = ⊥ :=
  normalFun_of_mem hN (hN.bot_mem isCompactElement_bot)

/-- `(q, p) f` is strict whenever `p`, `q` and `f` are: `q (f (p ⊥))` unwinds to
`q (f ⊥) = q ⊥ = ⊥`. -/
theorem isStrict_compHom {p : ScottHom α α} {q : ScottHom β β} (hp : p (⊥ : α) = ⊥)
    (hq : q (⊥ : β) = ⊥) {f : ScottHom α β} (hf : IsStrict f) : IsStrict (compHom p q f) := by
  show q (f (p ⊥)) = ⊥
  rw [hp, hf, hq]

open ScottHom in
/-- **The projection `(q, p)` of `lem17_fun`, with its two ingredients exposed.**
`lem17_fun` needs only that the image of `(q, p)` is a finite normal subposet
containing `u`; the strict function space needs the two projections themselves,
because it must know they are strict. The proof is `lem17_fun`'s, up to the final
packaging: every `f ∈ u` is a finite join of step functions, the compacts those
step functions mention are expanded to finite normal `N₁ ◁ K(D)` and
`N₂ ◁ K(E)`, and `(p_{N₂}, p_{N₁})` fixes each `f ∈ u`. -/
theorem exists_finite_projection_fixing [Domain α] [Domain β] [BoundedComplete β]
    (h₁ : IsBifinite α) (h₂ : IsBifinite β) {u : Set (ScottHom α β)} (hu : u.Finite)
    (husub : u ⊆ compacts (ScottHom α β)) :
    ∃ (p : ScottHom α α) (q : ScottHom β β), IsProjection p ∧ IsProjection q ∧
      p (⊥ : α) = ⊥ ∧ q (⊥ : β) = ⊥ ∧ (Set.range ⇑(compHom p q)).Finite ∧
      ∀ f ∈ u, compHom p q f = f := by
  classical
  have hstep : ∀ f : ScottHom α β, f ∈ u →
      ∃ S : Set (ScottHom α β), S.Finite ∧ S ⊆ stepsBelow f ∧ IsLUB S f :=
    fun f hf => exists_finite_isLUB_of_isCompactElement (husub hf)
  choose! S hSfin hSsub hSlub using hstep
  have hTfin : (⋃ f ∈ u, S f).Finite := hu.biUnion hSfin
  have hTstep : ∀ g ∈ ⋃ f ∈ u, S f, ∃ pr : α × β, IsStepPair g pr := by
    intro g hg
    obtain ⟨f, hf, hgS⟩ := Set.mem_iUnion₂.mp hg
    exact (hSsub f hf hgS).1
  choose! π hπ using hTstep
  have hK : (fun g => (π g).1) '' (⋃ f ∈ u, S f) ⊆ compacts α := by
    rintro _ ⟨g, hg, rfl⟩
    exact (hπ g hg).1
  have hE : (fun g => (π g).2) '' (⋃ f ∈ u, S f) ⊆ compacts β := by
    rintro _ ⟨g, hg, rfl⟩
    exact (hπ g hg).2.1
  obtain ⟨N₁, hN₁fin, hN₁, hN₁sub⟩ := h₁ _ (hTfin.image _) hK
  obtain ⟨N₂, hN₂fin, hN₂, hN₂sub⟩ := h₂ _ (hTfin.image _) hE
  have hp : IsProjection (normalHom hN₁) := isProjection_normalHom hN₁
  have hq : IsProjection (normalHom hN₂) := isProjection_normalHom hN₂
  have hP : IsProjection (compHom (normalHom hN₁) (normalHom hN₂)) := isProjection_compHom hp hq
  refine ⟨normalHom hN₁, normalHom hN₂, hp, hq, normalHom_bot hN₁, normalHom_bot hN₂,
    finite_range_compHom hp hq (finite_range_normalHom hN₁ hN₁fin)
      (finite_range_normalHom hN₂ hN₂fin), ?_⟩
  intro f hf
  refine le_antisymm (hP.le f) ?_
  refine (hSlub f hf).2 ?_
  intro g hg
  have hgT : g ∈ ⋃ f ∈ u, S f := Set.mem_biUnion hf hg
  obtain ⟨_, _, hgfun⟩ := hπ g hgT
  intro x
  show g x ≤ normalFun N₂ (f (normalFun N₁ x))
  by_cases hkx : (π g).1 ≤ x
  · have hkp : (π g).1 ≤ normalFun N₁ x :=
      le_normalFun hN₁ (hN₁sub ⟨g, hgT, rfl⟩) hkx
    have hle : (π g).2 ≤ f (normalFun N₁ x) := by
      have hgf := ScottHom.le_def.mp (hSsub f hf hg).2 (normalFun N₁ x)
      rwa [hgfun, stepFun_of_le hkp] at hgf
    calc g x = (π g).2 := by rw [hgfun]; exact stepFun_of_le hkx
      _ = normalFun N₂ ((π g).2) := (normalFun_of_mem hN₂ (hN₂sub ⟨g, hgT, rfl⟩)).symm
      _ ≤ normalFun N₂ (f (normalFun N₁ x)) := monotone_normalFun hN₂ hle
  · rw [hgfun, stepFun_of_not_le hkx]
    exact bot_le

/-! ### Lemma 17, the strict function-space conjunct -/

open ScottHom in
/-- **Lemma 17, `D →⊥ E`.** `(q, p)` restricted to the strict functions is a
projection of `D →⊥ E` with finite image, and its image is a finite normal
subposet of `K(D →⊥ E)` containing `u`:

* finite, because `f ↦ f.val` is injective and the ambient image is finite;
* inside `K(D →⊥ E)`, by `isCompactElement_of_mem_range_of_finite` in the ambient
  space followed by `isCompactElement_of_isCompactElement_val`;
* normal, because `(q,p) x` is the **greatest** member of the image below `x` —
  a member `a` of the image satisfies `a = (q,p) a ≤ (q,p) x`;
* containing `u`, because each `f ∈ u` is compact in `D → E`
  (`isCompactElement_val_of_isCompactElement`) and `(q, p)` fixes it.

`[BoundedComplete β]` is inherited from the step-function decomposition, exactly
as in `lem17_fun`. -/
theorem lem17_strictFun [Domain α] [Domain β] [BoundedComplete β]
    (h₁ : IsBifinite α) (h₂ : IsBifinite β) : IsBifinite (StrictHom α β) := by
  intro u hu husub
  have huvfin : (Subtype.val '' u : Set (ScottHom α β)).Finite := hu.image _
  have huvsub : (Subtype.val '' u : Set (ScottHom α β)) ⊆ compacts (ScottHom α β) := by
    rintro _ ⟨f, hf, rfl⟩
    exact isCompactElement_val_of_isCompactElement (husub hf)
  obtain ⟨p, q, hp, hq, hpbot, hqbot, hPfin, hfix⟩ :=
    exists_finite_projection_fixing h₁ h₂ huvfin huvsub
  have hP : IsProjection (compHom p q) := isProjection_compHom hp hq
  refine ⟨Subtype.val ⁻¹' Set.range ⇑(compHom p q), hPfin.preimage Subtype.val_injective.injOn,
    ⟨?_, ?_⟩, ?_⟩
  · intro y hy
    exact isCompactElement_of_isCompactElement_val
      (isCompactElement_of_mem_range_of_finite hP hPfin hy)
  · intro x _
    refine ⟨⟨⟨compHom p q x.val, isStrict_compHom hpbot hqbot x.2⟩,
      Set.mem_range_self _, Set.mem_Iic.mpr (hP.le x.val)⟩, ?_⟩
    rintro a ⟨ha, hax⟩ b ⟨hb, hbx⟩
    refine ⟨⟨compHom p q x.val, isStrict_compHom hpbot hqbot x.2⟩,
      ⟨Set.mem_range_self _, Set.mem_Iic.mpr (hP.le x.val)⟩, ?_, ?_⟩
    · exact (hP.apply_of_mem_range ha).symm.trans_le ((compHom p q).monotone hax)
    · exact (hP.apply_of_mem_range hb).symm.trans_le ((compHom p q).monotone hbx)
  · intro f hf
    exact ⟨f.val, hfix f.val ⟨f, hf, rfl⟩⟩

end ScottDomains.ClosureProperties
