import ScottDomains.Combinator
import ScottDomains.ClosureProperties.SeparatedSum
import ScottDomains.Isomorphism.StrictCurry
import ScottDomains.Isomorphism.Counterexample

/-!
# §4's algebra of *maps*: `f × g`, `f ⊗ g`, `f ⊕ g`, `f⊥`, `f + g`

Gunter & Scott, *Semantic Domains*, §4 defines each of its operators twice — once
on domains and once on continuous functions — and says so explicitly (printed
p. 14):

> Note that we have "overloaded" the symbol `×` so that it works both on pairs of
> *domains* and pairs of *functions*. … In this case (and others to follow) we
> have an example of what mathematicians call a **functor**.

r0040 measured that the development had every object §4 defines and every closure
property it asserts, but **none of the five functorial actions on morphisms in
general** — only `U`-specialised versions built for §7's representability work.
This file is the general action, and the properties §4 states about it.

## What is stated here, and where the paper states it

| # | Property | Printed page |
| -- | -------- | ----: |
| 1 | `f : D × E → F` is continuous **iff** continuous in each argument separately | 13 |
| 2 | `id_D × id_E = id_{D×E}` | 14 |
| 3 | `(f × g) ∘ (f' × g') = (f ∘ f') × (g ∘ g')` | 14 |
| 4 | the multiary product's universal property | 15 |
| 5 | `smash` is a surjection | 17 |
| 6 | `smash` is a projection whose corresponding embedding is `unsmash` | 18 |
| 7 | a bistrict continuous `f` factors uniquely through `smash` | 18 |
| 8 | `f ⊗ g` is the unique strict map completing §4.3's square | 18 |
| 9 | the multiary `[f₁, …, fₙ]` and its universal property | 19 |
| 10 | `up ∘ down ⊒ id_{D⊥}` | 20 |
| 11 | `h = [f†, g†]` may **not** be the only *continuous* completion | 21 |

Row 11 is the section's one negative claim and the one that separates `+` from
`⊕`: without it §4.4's universal property reads as a coproduct in the category of
continuous maps, which it is not.

## Three printed defects found while checking these against the PDF

Each was read off a 200 dpi render of the page, not from `pdftotext`.

1. **Printed p. 18, the `f ⊗ g` square.** The prose reads `f : D → D'` and
   `g : E → E'`, but *both* right-hand corners of the diagram are printed
   `D × E` and `D ⊗ E` where they must be `D' × E'` and `D' ⊗ E'`.
2. **Printed p. 19, the multiary coalesced sum.** The page prints
   `inᵢ = inr ∘ inl^{n-i}`, which is ill-typed under the composition order the
   same paper uses two pages earlier for `onᵢ = snd ∘ fst^{n-i}`: `inr` lands in
   `⊕(D₁,…,Dᵢ)` and `inl` must be applied `n-i` times *after* it. The correct
   form is `inᵢ = inl^{n-i} ∘ inr`, which is what `multiIn` below is.
3. **Printed p. 19, `f ⊕ g`.** The prose says "given continuous functions", but
   the displayed types are `f : D ⊸ D'` and `g : E ⊸ E'` — the *strict* arrow.
   The strict reading is the correct one: `[·,·]` is defined for strict maps, and
   `coalSumMap` below takes `StrictHom`s accordingly.

## Which of several duplicate definitions this file builds on

r0040 recorded three maps each defined twice in the development. Checking the
names against the whole package while writing this file raised one of those to
**three** copies and added a fourth pair, both recorded here:

| # | Concept | Copies | Used here |
| -- | ------- | ------ | --------- |
| 1 | pairing `⟨f, g⟩` | `ScottHom.pair` (`Product.lean`), `Combinator.prodMkHom` | `ScottHom.pair` |
| 2 | `smash` | `Isomorphism.smashPair` (`StrictCurry.lean`), **`ScottDomains.smashPair` (`Skeleton/Sum.lean`)**, `PRepFun.smashCollapse` | `Isomorphism.smashPair` |
| 3 | `unsmash` | `Isomorphism.smashVal`, `PRepFun.smashEmbed` | `Isomorphism.smashVal` |
| 4 | `inl`, `inr` | **`Isomorphism.sumInl`/`sumInr` (bundled `StrictHom`s) and `ScottDomains.sumInl`/`sumInr` (raw functions, `Skeleton/Sum.lean`)** | `Isomorphism.sumInl`/`sumInr` |

Rows 2 and 4 are not a stylistic remark: `ScottDomains.smashPair` and
`ScottDomains.sumInl` live in the *enclosing* namespace of this file, so an
unqualified `smashPair` inside `ScottDomains.Morphism` silently resolves to the
`Skeleton` copy and no `Isomorphism` lemma applies to it. Every reference below is
therefore written `Isomorphism.…` explicitly, which both fixes the resolution and
records which copy was chosen.

The one place a §7 module is named is composition.
`ScottDomains.Combinator.comp` is the development's *only* bundled composition of
`ScottHom`s and `ScottHom.id` its only bundled identity; both are stated at
`Preorder` and are perfectly general, so this file imports them rather than
declaring a second `comp` and a second `id`.
-/

namespace ScottDomains.Morphism

open ScottDomains
open ScottDomains.Combinator (comp comp_apply)

universe u

/-! ## §4.1 The product on maps

> Given continuous functions `f : D → D'` and `g : E → E'`, we may define a
> continuous function `f × g` which takes `(x, y)` to `(f(x), g(y))` by setting
> `f × g = ⟨f ∘ fst, g ∘ snd⟩ : D × E → D' × E'`.
-/

section Projections

variable {α β : Type*} [CompletePartialOrder α] [CompletePartialOrder β]

/-- `fst : D × E → D`, bundled. `Product.lean` names the *component* operation
`ScottHom.fstComp`, which takes a map into a product to its first component; the
projection itself is that operation at the identity, so no new function is
introduced here. -/
def prodFst : ScottHom (α × β) α := ScottHom.fstComp ScottHom.id

@[simp] theorem prodFst_apply (p : α × β) : (prodFst : ScottHom (α × β) α) p = p.1 := rfl

/-- `snd : D × E → E`, bundled. -/
def prodSnd : ScottHom (α × β) β := ScottHom.sndComp ScottHom.id

@[simp] theorem prodSnd_apply (p : α × β) : (prodSnd : ScottHom (α × β) β) p = p.2 := rfl

end Projections

section ProductFunctor

variable {α₁ α₂ β₁ β₂ γ₁ γ₂ : Type*}
variable [CompletePartialOrder α₁] [CompletePartialOrder α₂]
variable [CompletePartialOrder β₁] [CompletePartialOrder β₂]
variable [CompletePartialOrder γ₁] [CompletePartialOrder γ₂]

/-- **`f × g`** (Gunter & Scott §4.1, printed p. 14), as the paper defines it:
`⟨f ∘ fst, g ∘ snd⟩`. -/
def prodMap (f : ScottHom α₁ β₁) (g : ScottHom α₂ β₂) : ScottHom (α₁ × α₂) (β₁ × β₂) :=
  ScottHom.pair (comp f prodFst) (comp g prodSnd)

@[simp] theorem prodMap_apply (f : ScottHom α₁ β₁) (g : ScottHom α₂ β₂) (p : α₁ × α₂) :
    prodMap f g p = (f p.1, g p.2) := rfl

/-- **`id_D × id_E = id_{D×E}`** — the first functor law, printed p. 14. -/
theorem prodMap_id :
    prodMap (ScottHom.id : ScottHom α₁ α₁) (ScottHom.id : ScottHom α₂ α₂)
      = (ScottHom.id : ScottHom (α₁ × α₂) (α₁ × α₂)) :=
  ScottHom.ext fun _ => rfl

/-- **`(f × g) ∘ (f' × g') = (f ∘ f') × (g ∘ g')`** — the second functor law,
printed p. 14. Together with `prodMap_id` this is the statement that `×` is a
functor, which is exactly what the paper's remark on that page claims. -/
theorem prodMap_comp (f : ScottHom β₁ γ₁) (g : ScottHom β₂ γ₂)
    (f' : ScottHom α₁ β₁) (g' : ScottHom α₂ β₂) :
    comp (prodMap f g) (prodMap f' g') = prodMap (comp f f') (comp g g') :=
  ScottHom.ext fun _ => rfl

end ProductFunctor

/-! ## §4.1 Joint versus separate continuity

> Given cpos `D, E, F`, one can show that a function `f : D × E → F` is
> continuous if and only if it is continuous in each of its arguments
> individually. … We leave the proof of this equivalence as an exercise for the
> reader.

r0040 measured `ScottHom.uncurry` as *not* this statement: its hypothesis is
continuity into the function space `D → (E → F)`, which is strictly stronger than
separate continuity. The direction with content is separate ⟹ joint, and it is
where directedness of the set **in the product** is spent: the two suprema are
taken over different projections of one directed set, and a single member of that
set above both is what merges them.
-/

section Separate

variable {α β γ : Type*}
variable [CompletePartialOrder α] [CompletePartialOrder β] [CompletePartialOrder γ]

/-- For fixed `y`, pairing on the right is Scott continuous. The mirror image of
`ScottDomains.scottContinuous_pairLeft`. -/
theorem scottContinuous_pairRight (y : β) : ScottContinuous fun x : α => (x, y) := by
  intro s hne _ a ha
  have hfst : Prod.fst '' ((fun x : α => (x, y)) '' s) = s := by
    ext z
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact hx
    · intro hz
      exact ⟨(z, y), ⟨z, hz, rfl⟩, rfl⟩
  have hsnd : Prod.snd '' ((fun x : α => (x, y)) '' s) = {y} := by
    obtain ⟨x₀, hx₀⟩ := hne
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨(x₀, y), ⟨x₀, hx₀, rfl⟩, rfl⟩, ?_⟩
    rintro _ ⟨_, ⟨x, _, rfl⟩, rfl⟩
    rfl
  rw [isLUB_prod, hfst, hsnd]
  exact ⟨ha, isLUB_singleton⟩

/-- §4.1's two numbered conditions: `f` is continuous in each of its arguments
individually. -/
def SeparatelyScottContinuous (f : α × β → γ) : Prop :=
  (∀ e : β, ScottContinuous fun x : α => f (x, e)) ∧
    (∀ d : α, ScottContinuous fun y : β => f (d, y))

/-- Separate continuity implies joint monotonicity: change one coordinate at a
time. -/
theorem SeparatelyScottContinuous.monotone {f : α × β → γ}
    (h : SeparatelyScottContinuous f) : Monotone f := by
  intro p q hpq
  exact le_trans ((h.1 p.2).monotone hpq.1) ((h.2 q.1).monotone hpq.2)

/-- **A function on a product is Scott continuous exactly when it is Scott
continuous in each argument separately** (Gunter & Scott §4.1, printed p. 13 —
the equivalence the paper leaves as an exercise for the reader).

Forward: compose with `scottContinuous_pairRight` / `scottContinuous_pairLeft`.

Backward: monotonicity gives the upper-bound half. For the least half, peel the
first coordinate with the hypothesis at `c.2` and the second with the hypothesis
at `x`, reaching a goal about `f (q₁.1, q₂.2)` for `q₁, q₂` drawn from different
members of the directed set; `hs q₁ _ q₂ _` supplies a single member above both,
and monotonicity finishes. -/
theorem scottContinuous_iff_separately {f : α × β → γ} :
    ScottContinuous f ↔ SeparatelyScottContinuous f := by
  constructor
  · intro hf
    exact ⟨fun e => (scottContinuous_pairRight e).comp hf,
      fun d => (scottContinuous_pairLeft d).comp hf⟩
  · intro h
    have hmono : Monotone f := h.monotone
    intro s hne hs c hc
    have hc2 := hc
    rw [isLUB_prod] at hc2
    obtain ⟨hM, hN⟩ := hc2
    have hMne : (Prod.fst '' s).Nonempty := hne.image _
    have hNne : (Prod.snd '' s).Nonempty := hne.image _
    have hMdir : DirectedOn (· ≤ ·) (Prod.fst '' s) := directedOn_fst_image hs
    have hNdir : DirectedOn (· ≤ ·) (Prod.snd '' s) := directedOn_snd_image hs
    constructor
    · rintro _ ⟨q, hq, rfl⟩
      exact hmono (hc.1 hq)
    · intro u hu
      have hkey := (h.1 c.2) hMne hMdir hM
      refine hkey.2 ?_
      rintro _ ⟨x, hx, rfl⟩
      have hkey2 := (h.2 x) hNne hNdir hN
      refine hkey2.2 ?_
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨q₁, hq₁, rfl⟩ := hx
      obtain ⟨q₂, hq₂, rfl⟩ := hy
      obtain ⟨q₃, hq₃, hle₁, hle₂⟩ := hs q₁ hq₁ q₂ hq₂
      exact le_trans (hmono (show (q₁.1, q₂.2) ≤ q₃ from ⟨hle₁.1, hle₂.2⟩))
        (hu ⟨q₃, hq₃, rfl⟩)

end Separate

/-! ## §4.3 `smash`, `unsmash`, and the smash product on maps

> There is a continuous **surjection** `smash : D × E → D ⊗ E` … In fact, it is a
> **projection** whose corresponding embedding is the function
> `unsmash : D ⊗ E → D × E`.

`Isomorphism.smashPair` is the paper's `smash` and `Isomorphism.smashVal` its
`unsmash`; both are proved Scott continuous in `Isomorphism/StrictCurry.lean`.
What was never stated is the surjectivity and the two round-trip relations, which
is what makes the pair a projection–embedding pair.
-/

section Smash

variable {α β γ : Type*}
variable [CompletePartialOrder α] [CompletePartialOrder β] [CompletePartialOrder γ]

/-- **`smash` is a surjection** (printed p. 17). The adjoined bottom is hit by
`(⊥, ⊥)` and every other element is a non-bottom pair, hit by itself. -/
theorem smashPair_surjective :
    Function.Surjective (Isomorphism.smashPair : α × β → Smash α β) := by
  intro z
  induction z using WithBot.recBotCoe with
  | bot => exact ⟨((⊥ : α), (⊥ : β)), Isomorphism.smashPair_of_bot fun h => h.1 rfl⟩
  | coe p => exact ⟨p.val, Isomorphism.smashPair_of_ne p.2⟩

/-- **`smash ∘ unsmash = id_{D⊗E}`** — the projection half of the pair
(printed p. 18). -/
theorem smashPair_smashVal (z : Smash α β) :
    Isomorphism.smashPair (Isomorphism.smashVal z) = z := by
  induction z using WithBot.recBotCoe with
  | bot => exact Isomorphism.smashPair_of_bot fun h => h.1 rfl
  | coe p => exact Isomorphism.smashPair_of_ne p.2

/-- **`unsmash ∘ smash ⊑ id_{D×E}`** — the embedding half of the pair
(printed p. 18). The inequality is strict exactly at the pairs one of whose
coordinates is `⊥`, which are the pairs `smash` collapses. -/
theorem smashVal_smashPair_le (p : α × β) :
    Isomorphism.smashVal (Isomorphism.smashPair p) ≤ p := by
  by_cases h : p.1 ≠ ⊥ ∧ p.2 ≠ ⊥
  · rw [Isomorphism.smashPair_of_ne h]
    exact le_rfl
  · rw [Isomorphism.smashPair_of_bot h, Isomorphism.smashVal_bot]
    exact bot_le

/-- **`smash` is a projection whose corresponding embedding is `unsmash`**
(printed p. 18), as the conjunction of the two round-trip relations. The paper
compares this with `up`/`down` on the lift, where the second relation runs the
other way (`up_comp_down_ge` below) — so the two constructions are *not* the same
kind of pair, and that difference is the point of the remark on printed p. 20. -/
theorem isProjectionEmbeddingPair_smash :
    (∀ z : Smash α β, Isomorphism.smashPair (Isomorphism.smashVal z) = z) ∧
      (∀ p : α × β, Isomorphism.smashVal (Isomorphism.smashPair p) ≤ p) :=
  ⟨smashPair_smashVal, smashVal_smashPair_le⟩

/-- §4.3's **bistrict**: `f (x, y) = ⊥` whenever `x = ⊥` or `y = ⊥`. The
development had no predicate for separate strictness; this is it. It is strictly
stronger than `IsStrict` on `D × E`, which constrains `f` only at `(⊥, ⊥)`. -/
def IsBistrict (f : α × β → γ) : Prop := ∀ p : α × β, p.1 = ⊥ ∨ p.2 = ⊥ → f p = ⊥

/-- A pair failing the `smash` guard has a `⊥` coordinate. -/
theorem eq_bot_or_of_not_ne {p : α × β} (h : ¬(p.1 ≠ ⊥ ∧ p.2 ≠ ⊥)) :
    p.1 = ⊥ ∨ p.2 = ⊥ := by
  by_contra hcon
  exact h ⟨fun hb => hcon (Or.inl hb), fun hb => hcon (Or.inr hb)⟩

/-- `g = f ∘ unsmash`, the factorisation of a bistrict continuous `f` through the
smash product (printed p. 18). Strictness is `f (⊥, ⊥) = ⊥`, one instance of
bistrictness. -/
noncomputable def bistrictFactor (f : ScottHom (α × β) γ) (hf : IsBistrict ⇑f) :
    StrictHom (Smash α β) γ :=
  ⟨⟨fun z => f (Isomorphism.smashVal z),
      Isomorphism.scottContinuous_smashVal.comp f.scottContinuous⟩, by
    show f (Isomorphism.smashVal (⊥ : Smash α β)) = ⊥
    rw [Isomorphism.smashVal_bot]
    exact hf _ (Or.inl rfl)⟩

/-- **`(f ∘ unsmash) ∘ smash = f`** — the triangle of printed p. 18 commutes. -/
theorem bistrictFactor_comp_smash (f : ScottHom (α × β) γ) (hf : IsBistrict ⇑f)
    (p : α × β) :
    (bistrictFactor f hf).val (Isomorphism.smashPair p) = f p := by
  show f (Isomorphism.smashVal (Isomorphism.smashPair p)) = f p
  by_cases h : p.1 ≠ ⊥ ∧ p.2 ≠ ⊥
  · rw [Isomorphism.smashPair_of_ne h]
    rfl
  · rw [Isomorphism.smashPair_of_bot h, Isomorphism.smashVal_bot, hf _ (Or.inl rfl),
      hf p (eq_bot_or_of_not_ne h)]

/-- **`f ∘ unsmash` is the *unique* strict continuous map completing the
triangle** (printed p. 18). `smash` is surjective, so any two completions agree
off the adjoined bottom, and strictness settles them there. -/
theorem bistrictFactor_unique (f : ScottHom (α × β) γ) (hf : IsBistrict ⇑f)
    (g : StrictHom (Smash α β) γ)
    (hg : ∀ p : α × β, g.val (Isomorphism.smashPair p) = f p) :
    g = bistrictFactor f hf := by
  refine Subtype.ext (ScottHom.ext ?_)
  intro z
  induction z using WithBot.recBotCoe with
  | bot =>
    show g.val (⊥ : Smash α β) = f (Isomorphism.smashVal (⊥ : Smash α β))
    rw [g.2, Isomorphism.smashVal_bot, hf _ (Or.inl rfl)]
  | coe p =>
    have hp := hg p.val
    rw [Isomorphism.smashPair_of_ne p.2] at hp
    exact hp

end Smash

section SmashFunctor

variable {α₁ α₂ β₁ β₂ : Type*}
variable [CompletePartialOrder α₁] [CompletePartialOrder α₂]
variable [CompletePartialOrder β₁] [CompletePartialOrder β₂]

/-- `smash ∘ (f × g)` for strict `f`, `g`, as a continuous map on the plain
product. -/
noncomputable def smashProdMap (f : StrictHom α₁ β₁) (g : StrictHom α₂ β₂) :
    ScottHom (α₁ × α₂) (Smash β₁ β₂) :=
  comp ⟨Isomorphism.smashPair, Isomorphism.scottContinuous_smashPair⟩ (prodMap f.val g.val)

@[simp] theorem smashProdMap_apply (f : StrictHom α₁ β₁) (g : StrictHom α₂ β₂)
    (p : α₁ × α₂) :
    smashProdMap f g p = Isomorphism.smashPair (f.val p.1, g.val p.2) := rfl

/-- **`smash ∘ (f × g)` is bistrict when `f` and `g` are strict.** This is the
only place the strictness hypothesis of printed p. 18 is used, and it is what
makes `f ⊗ g` an instance of the bistrict factorisation rather than a separate
construction. -/
theorem isBistrict_smashProdMap (f : StrictHom α₁ β₁) (g : StrictHom α₂ β₂) :
    IsBistrict ⇑(smashProdMap f g) := by
  rintro p (h | h)
  · show Isomorphism.smashPair (f.val p.1, g.val p.2) = ⊥
    refine Isomorphism.smashPair_of_bot ?_
    rintro ⟨h1, -⟩
    refine h1 ?_
    show f.val p.1 = ⊥
    rw [h]
    exact f.2
  · show Isomorphism.smashPair (f.val p.1, g.val p.2) = ⊥
    refine Isomorphism.smashPair_of_bot ?_
    rintro ⟨-, h2⟩
    refine h2 ?_
    show g.val p.2 = ⊥
    rw [h]
    exact g.2

/-- **`f ⊗ g = smash ∘ (f × g) ∘ unsmash`** (Gunter & Scott §4.3, printed p. 18),
for strict continuous `f` and `g`, exactly as the paper writes it. The formula was
recited in a docstring at `CombinatorRep.lean:506–507` and never put under the
kernel; this is that formula as a definition. -/
noncomputable def smashMap (f : StrictHom α₁ β₁) (g : StrictHom α₂ β₂) :
    StrictHom (Smash α₁ α₂) (Smash β₁ β₂) :=
  bistrictFactor (smashProdMap f g) (isBistrict_smashProdMap f g)

/-- **§4.3's square commutes**: `(f ⊗ g) ∘ smash = smash ∘ (f × g)`.

The paper's diagram prints both right-hand corners as `D × E` and `D ⊗ E`; the
prose types `f : D → D'` and `g : E → E'` make them `D' × E'` and `D' ⊗ E'`, and
that is the reading formalized here. -/
theorem smashMap_comp_smash (f : StrictHom α₁ β₁) (g : StrictHom α₂ β₂)
    (p : α₁ × α₂) :
    (smashMap f g).val (Isomorphism.smashPair p)
      = Isomorphism.smashPair (f.val p.1, g.val p.2) :=
  bistrictFactor_comp_smash _ _ p

/-- **`f ⊗ g` is the unique strict continuous map completing the square**
(printed p. 18). -/
theorem smashMap_unique (f : StrictHom α₁ β₁) (g : StrictHom α₂ β₂)
    (h : StrictHom (Smash α₁ α₂) (Smash β₁ β₂))
    (hh : ∀ p : α₁ × α₂, h.val (Isomorphism.smashPair p)
      = Isomorphism.smashPair (f.val p.1, g.val p.2)) :
    h = smashMap f g :=
  bistrictFactor_unique _ _ h hh

end SmashFunctor

/-! ## §4.4 The lift, the coalesced sum and the separated sum, on maps -/

section Strict

variable {α β γ : Type*}
variable [CompletePartialOrder α] [CompletePartialOrder β] [CompletePartialOrder γ]

/-- Composition of strict continuous maps. `Combinator.comp` composes the
underlying `ScottHom`s; strictness is `g (f ⊥) = g ⊥ = ⊥`. -/
def strictComp (g : StrictHom β γ) (f : StrictHom α β) : StrictHom α γ :=
  ⟨comp g.val f.val, by
    show g.val (f.val ⊥) = ⊥
    rw [f.2, g.2]⟩

@[simp] theorem strictComp_apply (g : StrictHom β γ) (f : StrictHom α β) (x : α) :
    (strictComp g f).val x = g.val (f.val x) := rfl

/-- **`[f, g] ∘ inl = f`** — one of §4.4's two triangle equations (printed p. 19).
Read off `Isomorphism.coalescedSumCopair` rather than re-proved: that isomorphism's
forward map *is* restriction along the two injections and its inverse *is*
`copair`, so `apply_symm_apply` at `(f, g)` is exactly the pair of triangles. -/
theorem copair_comp_sumInl (g : StrictHom β α) (h : StrictHom γ α) :
    strictComp (Isomorphism.copair g h) Isomorphism.sumInl = g :=
  congrArg Prod.fst (Isomorphism.coalescedSumCopair.apply_symm_apply (g, h))

/-- **`[f, g] ∘ inr = g`** — the other triangle equation. -/
theorem copair_comp_sumInr (g : StrictHom β α) (h : StrictHom γ α) :
    strictComp (Isomorphism.copair g h) Isomorphism.sumInr = h :=
  congrArg Prod.snd (Isomorphism.coalescedSumCopair.apply_symm_apply (g, h))

end Strict

section Lift

variable {α β : Type*} [CompletePartialOrder α] [CompletePartialOrder β]

/-- `up : D → D⊥`, bundled. Mathlib's `WithBot` coercion, Scott continuous by
`Isomorphism.scottContinuous_coe`. -/
noncomputable def up : ScottHom α (WithBot α) := ⟨(↑), Isomorphism.scottContinuous_coe⟩

@[simp] theorem up_apply (a : α) : (up : ScottHom α (WithBot α)) a = (↑a : WithBot α) := rfl

/-- `down : D⊥ → D`, the paper's **total** function `down(z) = x` on `(x, 0)` and
`⊥_D` otherwise. It is `Isomorphism.liftExtendFun` at the identity — r0040
recorded that no declaration named it, and that Mathlib's `WithBot.unbot` is *not*
it, being partial (it takes a proof `z ≠ ⊥`). -/
noncomputable def down : ScottHom (WithBot α) α :=
  (Isomorphism.liftExtend (ScottHom.id : ScottHom α α)).val

@[simp] theorem down_coe (a : α) : (down : ScottHom (WithBot α) α) (↑a : WithBot α) = a := rfl

@[simp] theorem down_bot : (down : ScottHom (WithBot α) α) ⊥ = ⊥ := rfl

/-- **`down ∘ up = id_D`** (printed p. 20). -/
theorem down_comp_up : comp (down : ScottHom (WithBot α) α) up = ScottHom.id :=
  ScottHom.ext fun _ => rfl

/-- **`up ∘ down ⊒ id_{D⊥}`** (printed p. 20).

The direction of this inequality is the whole content of the paper's remark:

> These inequations are reminiscent of those which we gave for
> embedding-projection pairs, but the second inequation has `⊒` rather than `⊑`.

Compare `smashVal_smashPair_le`, which has `⊑`: `smash`/`unsmash` **is** a
projection–embedding pair and `up`/`down` is not. The inequality is strict exactly
at the adjoined bottom, where `up (down ⊥) = ↑⊥ ⊐ ⊥`. -/
theorem up_comp_down_ge :
    (ScottHom.id : ScottHom (WithBot α) (WithBot α)) ≤ comp up down := by
  refine ScottHom.le_def.mpr ?_
  intro z
  induction z using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe a => exact le_rfl

/-- **The inequality does not run the other way.** `up ∘ down ⊑ id` is *false*,
which is what makes the paper's `⊒` a genuine distinction from an
embedding–projection pair rather than a slip of the pen. At `D = I` the lift has
two elements and `up (down ⊥) = ↑⊥ ⊐ ⊥`. Without this the previous theorem would
be compatible with `up ∘ down = id`, and the remark it formalizes would be
empty. -/
theorem not_up_comp_down_le :
    ¬ (comp (up : ScottHom PUnit (WithBot PUnit)) down
        ≤ (ScottHom.id : ScottHom (WithBot PUnit) (WithBot PUnit))) := by
  intro h
  exact WithBot.not_coe_le_bot (⊥ : PUnit) (ScottHom.le_def.mp h ⊥)

/-- **`f⊥ = (up ∘ f)†`** (printed p. 20): the lift on maps, always strict. -/
noncomputable def liftMap (f : ScottHom α β) : StrictHom (WithBot α) (WithBot β) :=
  Isomorphism.liftExtend (comp up f)

@[simp] theorem liftMap_coe (f : ScottHom α β) (a : α) :
    (liftMap f).val (↑a : WithBot α) = (↑(f a) : WithBot β) := rfl

@[simp] theorem liftMap_bot (f : ScottHom α β) :
    (liftMap f).val (⊥ : WithBot α) = (⊥ : WithBot β) := rfl

end Lift

section SumFunctor

variable {α₁ α₂ β₁ β₂ : Type*}
variable [CompletePartialOrder α₁] [CompletePartialOrder α₂]
variable [CompletePartialOrder β₁] [CompletePartialOrder β₂]

/-- **`f ⊕ g = [inl ∘ f, inr ∘ g]`** (printed p. 19). The page's prose says
"continuous functions", but the displayed types carry the *strict* arrow
`D ⊸ D'`, and the strict reading is the one that makes `[·,·]` applicable — so
the arguments here are `StrictHom`s. -/
noncomputable def coalSumMap (f : StrictHom α₁ β₁) (g : StrictHom α₂ β₂) :
    StrictHom (CoalescedSum α₁ α₂) (CoalescedSum β₁ β₂) :=
  Isomorphism.copair (strictComp Isomorphism.sumInl f) (strictComp Isomorphism.sumInr g)

/-- **`f + g = f⊥ ⊕ g⊥`** (printed p. 21). Unlike `⊕`, this is defined for
*arbitrary* continuous `f` and `g`: `f⊥` is strict whatever `f` is, which is
precisely why the separated sum's universal property relaxes each factor to a
continuous map (`ClosureProperties.separatedSumCopair`). -/
noncomputable def sepSumMap (f : ScottHom α₁ β₁) (g : ScottHom α₂ β₂) :
    StrictHom (ClosureProperties.SeparatedSum α₁ α₂)
      (ClosureProperties.SeparatedSum β₁ β₂) :=
  coalSumMap (liftMap f) (liftMap g)

end SumFunctor

/-! ## §4.4 The separated sum's completion is not unique among *continuous* maps

> However, `h` may not be the only continuous function which completes the
> diagram.

This is §4's one negative claim, and the one that distinguishes `+` from `⊕`.
`ClosureProperties.separatedSumCopair` states that the **strict** completion is
unique; without the present witness that universal property reads as a coproduct
in the category of continuous maps, which it is not.
-/

section Completion

variable {α β γ : Type*}
variable [CompletePartialOrder α] [CompletePartialOrder β] [CompletePartialOrder γ]

/-- `h` **completes §4.4's diagram** for `D + E`: it agrees with `f` along
`inl ∘ up` and with `g` along `inr ∘ up`. Nothing constrains `h` at the sum's
adjoined bottom, which is the whole reason a continuous completion is not
unique. -/
def CompletesSepSum (f : ScottHom α γ) (g : ScottHom β γ)
    (h : ScottHom (ClosureProperties.SeparatedSum α β) γ) : Prop :=
  (∀ x : α, h (Isomorphism.sumInlFun (γ := WithBot β) (↑x : WithBot α)) = f x) ∧
    (∀ y : β, h (Isomorphism.sumInrFun (β := WithBot α) (↑y : WithBot β)) = g y)

/-- **`h = [f†, g†]`** (printed p. 21): the inverse of `separatedSumCopair` is
literally the copair of the two strict extensions. -/
theorem separatedSumCopair_symm_apply (f : ScottHom α γ) (g : ScottHom β γ) :
    (ClosureProperties.separatedSumCopair (α := α) (β := β) (γ := γ)).symm (f, g)
      = Isomorphism.copair (Isomorphism.liftExtend f) (Isomorphism.liftExtend g) := rfl

/-- The strict completion `h = [f†, g†]` does complete the diagram. -/
theorem completesSepSum_separatedSumCopair (f : ScottHom α γ) (g : ScottHom β γ) :
    CompletesSepSum f g
      ((ClosureProperties.separatedSumCopair (α := α) (β := β) (γ := γ)).symm (f, g)).val := by
  constructor
  · intro x
    show Isomorphism.copairFun (Isomorphism.liftExtend f) (Isomorphism.liftExtend g)
      (Isomorphism.sumInlFun (↑x : WithBot α)) = f x
    rw [Isomorphism.sumInlFun_of_ne (WithBot.coe_ne_bot)]
    rfl
  · intro y
    show Isomorphism.copairFun (Isomorphism.liftExtend f) (Isomorphism.liftExtend g)
      (Isomorphism.sumInrFun (↑y : WithBot β)) = g y
    rw [Isomorphism.sumInrFun_of_ne (WithBot.coe_ne_bot)]
    rfl

/-- **`h` may not be the only *continuous* function which completes the diagram**
(printed p. 21) — stated as an explicit witness, since the claim is negative.

Take `D = E = I` (the one-point cpo `PUnit`), `F = Prop` and `f = g = λ_. True`.
The strict completion sends the sum's adjoined bottom to `⊥ = False`; the constant
map `λ_. True` sends it to `True`. Both are Scott continuous and both agree with
`f` and `g` along the two injections, and they differ at exactly one point — the
adjoined bottom, which is in the image of neither injection. -/
theorem exists_ne_continuous_completions :
    ∃ h₁ h₂ : ScottHom (ClosureProperties.SeparatedSum PUnit PUnit) Prop,
      CompletesSepSum (ScottHom.const True) (ScottHom.const True) h₁ ∧
        CompletesSepSum (ScottHom.const True) (ScottHom.const True) h₂ ∧ h₁ ≠ h₂ := by
  refine ⟨(ClosureProperties.separatedSumCopair.symm
      ((ScottHom.const True : ScottHom PUnit Prop),
        (ScottHom.const True : ScottHom PUnit Prop))).val,
    ScottHom.const True, completesSepSum_separatedSumCopair _ _,
    ⟨fun _ => rfl, fun _ => rfl⟩, ?_⟩
  intro hEq
  have hbot := (ClosureProperties.separatedSumCopair.symm
    ((ScottHom.const True : ScottHom PUnit Prop),
      (ScottHom.const True : ScottHom PUnit Prop))).2
  rw [hEq] at hbot
  exact Isomorphism.true_ne_bot hbot

end Completion

/-! ## §4.1 The multiary product

> It is often useful to have a multiary notation for products. We write
> `×() = I`, `×(D₁,…,Dₙ) = ×(D₁,…,Dₙ₋₁) × Dₙ` and define projections
> `onᵢ : ×(D₁,…,Dₙ) → Dᵢ` by `onᵢ = snd ∘ fst^{n-i}`. Similarly, one defines a
> multiary version of the pairing operation by taking `⟨⟩` to be the identity on
> the one point domain and defining `⟨f₁,…,fₙ⟩ = ⟨⟨f₁,…,fₙ₋₁⟩, fₙ⟩`. These
> multiary versions of projection and pairing satisfy a universal property similar
> to the one for the binary product.

Indices are zero-based: `MultiProd D n` is the paper's `×(D 0, …, D (n-1))`, and
`I` is `PUnit`. `Fin.lastCases` is the eliminator the paper's recursion asks for —
it splits an index of `Fin (n+1)` into the last one and an index of `Fin n`,
which is exactly `snd` versus `· ∘ fst`.
-/

section MultiProduct

/-- `×() = I` and `×(D₁,…,Dₙ) = ×(D₁,…,Dₙ₋₁) × Dₙ`. -/
def MultiProd (D : ℕ → Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => MultiProd D n × D n

/-- `×(D₁,…,Dₙ)` is a cpo, by the same recursion: `PUnit` is one, and the binary
product of two cpos is one (`Product.lean`). -/
instance instMultiProdCpo (D : ℕ → Type u) [∀ i, CompletePartialOrder (D i)] :
    ∀ n, CompletePartialOrder (MultiProd D n)
  | 0 => inferInstanceAs (CompletePartialOrder PUnit)
  | n + 1 =>
      letI := instMultiProdCpo D n
      inferInstanceAs (CompletePartialOrder (MultiProd D n × D n))

variable {D : ℕ → Type u} [∀ i, CompletePartialOrder (D i)]
variable {γ : Type*} [CompletePartialOrder γ]

omit [∀ i, CompletePartialOrder (D i)] in
/-- The shape of the recursion, made checkable: `×(D₀, D₁)` is `(I × D₀) × D₁`.
The leading `I` is the paper's own convention (`×() = I`), not an artefact — the
paper's `×(D₁)` is `I × D₁`, isomorphic to but not equal to `D₁`. -/
theorem multiProd_two : MultiProd D 2 = ((PUnit × D 0) × D 1) := rfl

/-- **`onᵢ = snd ∘ fst^{n-i}`**, the multiary projection. -/
def multiProj : (n : ℕ) → (i : Fin n) → ScottHom (MultiProd D n) (D i.val)
  | 0, i => i.elim0
  | n + 1, i =>
      Fin.lastCases
        (motive := fun j : Fin (n + 1) => ScottHom (MultiProd D (n + 1)) (D j.val))
        prodSnd (fun j => comp (multiProj n j) prodFst) i

@[simp] theorem multiProj_last (n : ℕ) :
    (multiProj (D := D) (n + 1) (Fin.last n)) = prodSnd := by
  simp only [multiProj, Fin.lastCases_last]

@[simp] theorem multiProj_castSucc (n : ℕ) (j : Fin n) :
    (multiProj (D := D) (n + 1) j.castSucc) = comp (multiProj n j) prodFst := by
  simp only [multiProj, Fin.lastCases_castSucc]
  rfl

/-- **`⟨f₁,…,fₙ⟩ = ⟨⟨f₁,…,fₙ₋₁⟩, fₙ⟩`**, with `⟨⟩` the unique map into `I`. -/
def multiPair : (n : ℕ) → ((i : Fin n) → ScottHom γ (D i.val)) → ScottHom γ (MultiProd D n)
  | 0, _ => ScottHom.const ⊥
  | n + 1, f => ScottHom.pair (multiPair n fun j => f j.castSucc) (f (Fin.last n))

/-- **`onᵢ ∘ ⟨f₁,…,fₙ⟩ = fᵢ`** — the existence half of the multiary universal
property (printed p. 15). -/
theorem multiProj_comp_multiPair :
    ∀ (n : ℕ) (f : (i : Fin n) → ScottHom γ (D i.val)) (i : Fin n),
      comp (multiProj n i) (multiPair n f) = f i := by
  intro n
  induction n with
  | zero => intro _ i; exact i.elim0
  | succ n ih =>
    intro f i
    induction i using Fin.lastCases with
    | last =>
      rw [multiProj_last]
      exact ScottHom.ext fun _ => rfl
    | cast j =>
      rw [multiProj_castSucc]
      exact ScottHom.ext fun x =>
        congrArg (fun k : ScottHom γ (D j.val) => k x) (ih (fun j => f j.castSucc) j)

/-- **`⟨on₁ ∘ h, …, onₙ ∘ h⟩ = h`** — the uniqueness half, in the form the paper
writes for the binary product (printed p. 13). Together with
`multiProj_comp_multiPair` this is "a universal property similar to the one for
the binary product". -/
theorem multiPair_unique :
    ∀ (n : ℕ) (f : (i : Fin n) → ScottHom γ (D i.val)) (k : ScottHom γ (MultiProd D n)),
      (∀ i : Fin n, comp (multiProj n i) k = f i) → k = multiPair n f := by
  intro n
  induction n with
  | zero =>
    intro _ k _
    haveI : Subsingleton (MultiProd D 0) := inferInstanceAs (Subsingleton PUnit)
    exact ScottHom.ext fun x => Subsingleton.elim _ _
  | succ n ih =>
    intro f k h
    have hsnd : k.sndComp = f (Fin.last n) := by
      have hlast := h (Fin.last n)
      rw [multiProj_last] at hlast
      exact hlast
    have hfst : k.fstComp = multiPair n (fun j => f j.castSucc) := by
      refine ih _ _ ?_
      intro j
      have hj := h j.castSucc
      rw [multiProj_castSucc] at hj
      exact hj
    refine ScottHom.ext fun x => ?_
    show k x = (multiPair n (fun j => f j.castSucc) x, f (Fin.last n) x)
    rw [← hfst, ← hsnd]
    rfl

end MultiProduct

/-! ## §4.4 The multiary coalesced sum

> As with the product, it is useful to have a multiary notation for the coalesced
> sum. We define `⊕() = I`, `⊕(D₁,…,Dₙ) = ⊕(D₁,…,Dₙ₋₁) ⊕ Dₙ` and
> `inᵢ = inr ∘ inl^{n-i}`. One may also define `[f₁,…,fₙ]` and prove a universal
> property.

The printed `inᵢ = inr ∘ inl^{n-i}` has its composition order transposed — see the
module docstring. `multiIn` is the well-typed form `inl^{n-i} ∘ inr`.

`CoalescedSum` needs its arguments' orders to state the next type, so the type and
its cpo instance are built simultaneously by a `Sigma`-valued recursion — the
idiom `Colimit.lean`'s `stage` already uses for the same reason. The product above
needs no such thing, because `α × β` is a type before either factor is ordered.
-/

section MultiSum

/-- The stage tower for `⊕(D₁,…,Dₙ)`, carrying each stage's cpo structure. -/
noncomputable def multiSumStage (D : ℕ → Type u) [∀ i, CompletePartialOrder (D i)] :
    ℕ → Σ T : Type u, CompletePartialOrder T
  | 0 => ⟨PUnit, inferInstance⟩
  | n + 1 =>
      ⟨@CoalescedSum (multiSumStage D n).1 (D n) (multiSumStage D n).2 inferInstance,
        @sumCpo (multiSumStage D n).1 (D n) (multiSumStage D n).2 inferInstance⟩

/-- `⊕() = I` and `⊕(D₁,…,Dₙ) = ⊕(D₁,…,Dₙ₋₁) ⊕ Dₙ`. -/
def MultiSum (D : ℕ → Type u) [∀ i, CompletePartialOrder (D i)] (n : ℕ) : Type u :=
  (multiSumStage D n).1

noncomputable instance instMultiSumCpo (D : ℕ → Type u) [∀ i, CompletePartialOrder (D i)]
    (n : ℕ) : CompletePartialOrder (MultiSum D n) := (multiSumStage D n).2

/-- The same instance keyed on `(multiSumStage D n).1` rather than on
`MultiSum D n`. Typeclass resolution indexes on the head symbol, so a goal left in
`Sigma.fst` form after unfolding the recursion does not see the instance above;
the two are definitionally the same term, so no diamond is created. This is the
same pairing `Colimit.lean` needs for `Stg`. -/
noncomputable instance instMultiSumStageCpo (D : ℕ → Type u)
    [∀ i, CompletePartialOrder (D i)] (n : ℕ) :
    CompletePartialOrder (multiSumStage D n).1 := (multiSumStage D n).2

theorem multiSum_succ (D : ℕ → Type u) [∀ i, CompletePartialOrder (D i)] (n : ℕ) :
    MultiSum D (n + 1) = CoalescedSum (MultiSum D n) (D n) := rfl

variable {D : ℕ → Type u} [∀ i, CompletePartialOrder (D i)]
variable {γ : Type*} [CompletePartialOrder γ]

/-- **`inᵢ = inl^{n-i} ∘ inr`**, the multiary injection. The page prints
`inr ∘ inl^{n-i}`, which is ill-typed; this is the repaired form. -/
noncomputable def multiIn :
    (n : ℕ) → (i : Fin n) → StrictHom (D i.val) (MultiSum D n)
  | 0, i => i.elim0
  | n + 1, i =>
      Fin.lastCases
        (motive := fun j : Fin (n + 1) => StrictHom (D j.val) (MultiSum D (n + 1)))
        Isomorphism.sumInr
        (fun j => strictComp Isomorphism.sumInl (multiIn n j)) i

@[simp] theorem multiIn_last (n : ℕ) :
    (multiIn (D := D) (n + 1) (Fin.last n)) = Isomorphism.sumInr := by
  simp only [multiIn, Fin.lastCases_last]

@[simp] theorem multiIn_castSucc (n : ℕ) (j : Fin n) :
    (multiIn (D := D) (n + 1) j.castSucc)
      = strictComp Isomorphism.sumInl (multiIn n j) := by
  simp only [multiIn, Fin.lastCases_castSucc]
  rfl

/-- **`[f₁,…,fₙ]`**, with `[]` the unique strict map out of `I`. -/
noncomputable def multiCopair :
    (n : ℕ) → ((i : Fin n) → StrictHom (D i.val) γ) → StrictHom (MultiSum D n) γ
  | 0, _ => ⊥
  | n + 1, f =>
      Isomorphism.copair (multiCopair n fun j => f j.castSucc) (f (Fin.last n))

/-- **`[f₁,…,fₙ] ∘ inᵢ = fᵢ`** — the existence half of the multiary universal
property (printed p. 19). -/
theorem multiCopair_comp_multiIn :
    ∀ (n : ℕ) (f : (i : Fin n) → StrictHom (D i.val) γ) (i : Fin n),
      strictComp (multiCopair n f) (multiIn n i) = f i := by
  intro n
  induction n with
  | zero => intro _ i; exact i.elim0
  | succ n ih =>
    intro f i
    induction i using Fin.lastCases with
    | last =>
      rw [multiIn_last]
      exact copair_comp_sumInr _ _
    | cast j =>
      rw [multiIn_castSucc]
      have hleft := copair_comp_sumInl
        (multiCopair (D := D) (γ := γ) n fun jj => f jj.castSucc) (f (Fin.last n))
      have hih := ih (fun jj => f jj.castSucc) j
      refine Subtype.ext (ScottHom.ext fun x => ?_)
      have h1 := congrArg
        (fun k : StrictHom (MultiSum D n) γ => k.val ((multiIn (D := D) n j).val x)) hleft
      have h2 := congrArg (fun k : StrictHom (D j.val) γ => k.val x) hih
      exact h1.trans h2

/-- **`[f₁,…,fₙ]` is the unique strict continuous map with `h ∘ inᵢ = fᵢ`** — the
uniqueness half (printed p. 19). -/
theorem multiCopair_unique :
    ∀ (n : ℕ) (f : (i : Fin n) → StrictHom (D i.val) γ) (k : StrictHom (MultiSum D n) γ),
      (∀ i : Fin n, strictComp k (multiIn n i) = f i) → k = multiCopair n f := by
  intro n
  induction n with
  | zero =>
    intro f k _
    haveI : Subsingleton (MultiSum D 0) := inferInstanceAs (Subsingleton PUnit)
    refine Subtype.ext (ScottHom.ext fun x => ?_)
    rw [Subsingleton.elim x (⊥ : MultiSum D 0)]
    exact k.2.trans (multiCopair (D := D) (γ := γ) 0 f).2.symm
  | succ n ih =>
    intro f k h
    have hright : Isomorphism.restrictRight k = f (Fin.last n) := by
      have hlast := h (Fin.last n)
      rw [multiIn_last] at hlast
      exact hlast
    have hleft : Isomorphism.restrictLeft k = multiCopair n (fun j => f j.castSucc) := by
      refine ih _ _ ?_
      intro j
      have hj := h j.castSucc
      rw [multiIn_castSucc] at hj
      exact hj
    have hk := Isomorphism.coalescedSumCopair.symm_apply_apply k
    rw [show (Isomorphism.coalescedSumCopair k)
        = (Isomorphism.restrictLeft k, Isomorphism.restrictRight k) from rfl,
      hleft, hright] at hk
    exact hk.symm

end MultiSum

end ScottDomains.Morphism
