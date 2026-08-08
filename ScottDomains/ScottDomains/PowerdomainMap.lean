import ScottDomains.ContinuousAlgebra
-- `ScottHom.IsProjection`, the bundled form §7.3's `Fp(U)` machinery takes. Not
-- reachable from `ScottDomains.ContinuousAlgebra`, which stops at `IdealCompletion`.
import ScottDomains.Projection

/-!
# §5.3's `f♮`, `f♯`, `f♭`: the action of a continuous map on a powerdomain

Gunter & Scott, *Semantic Domains* (Handbook of Theoretical Computer Science
Vol. B, 1990), §5.3, the sentence immediately after Theorem 12's proof and the
two axiom paragraphs, read off the rendered page (printed p. 28–29):

> If `f : D → E` is a continuous function, then there is a unique homomorphism
> `f♮ : D♮ → E♮` which makes the following diagram commute … namely
> `f♮ = ext({|·|} ∘ f)`. Of course, there are functions `f♯` and `f♭` with
> similar definitions.

r0040 measured this sentence as `N` — **no Lean statement at all**. Nine name
variants (`fSharp`, `powerdomainMap`, `Powerdomain.map`, `hoareMap`, `smythMap`,
`plotkinMap`, `mapPowerdomain`, `fFlat`, `fNatural`) returned zero hits, and the
only `ext(` in the development is Theorem 12's `ext(f) : D♮ → E`, which is a map
**out of** a powerdomain into an algebra, not a map `D♮ → E♮`. Two other modules
had recorded the same absence for their own purposes: `PRepFun.lean:98` and
`docs/PaperInventory.md` row 554, the latter naming it as the obstruction to
Lemma 28's `()♯` and `()♭` conjuncts.

## The construction needs nothing new

`ext` is already general enough. `E♮` is itself a continuous algebra satisfying
`T♮` (`ContinuousAlgebra.instIsSemilatticeIdealCompletion`, the paper's "*each of
the algebras `D♮`, `D♯` and `D♭` satisfies `T♮`*"), and `{|·|} ∘ f : D → E♮` is
continuous as a composite of two continuous maps. So Theorem 12 applies **with
`E♮` as the target algebra**, and its `ext` is the paper's `f♮`:

    map f  :=  ext ({|·|} ∘ f)  :  D♮ → E♮.

The `∃!` of `thm12` then delivers, in one step, the paper's whole sentence: `f♮`
exists, it is a homomorphism, it satisfies the naturality equation
`f♮ ∘ {|·|} = {|·|} ∘ f`, and it is the **only** map with those two properties.
`exists_unique_map` below is that statement; the three named corollaries
`thm_map_hoare`, `thm_map_smyth`, `thm_map_plotkin` are it at the three carriers.

### This settles the obstruction r0038 named, by dissolving it

r0038 and `Lemma28AtU.lean`'s docstring record the blocker as: *"the natural
construction acts on finite sets of compacts and so wants `p(K(D)) ⊆ K(D)` for a
finitary projection `p`; whether that holds is the step to settle first."*

Two measurements, and they point in opposite directions:

1. **`p(K(D)) ⊆ K(D)` is false**, already for a finitary projection.
   `ScottDomains.PowerdomainCompacts` exhibits a domain, a finitary projection on
   it and a compact element whose image is not compact
   (`Compacts.finitaryProjection_not_maps_compacts`). So the construction *by
   transport of finite sets of compacts* cannot be carried out, and no amount of
   further work would have made it work. That module is separate from this one
   deliberately: it imports `ScottDomains.PRep` for `domain_orderIso`, and this
   module must stay importable *by* `PRep`.
2. **The paper's construction never asks for it.** `ext` factors through the
   ideal completion's universal property, which quantifies over *ideals*, not
   over a transported basis. The map `f♮` is defined for **every** continuous
   `f`, with no hypothesis relating `f` to `K(D)` at all.

So the r0038 obstruction was an artefact of picking the wrong construction. What
Lemma 28 needs from this file is `isProjection_map`: the action of a projection
is a projection, proved not from any property of compacts but from the two
functor laws — `map (p ∘ p) = map p ∘ map p` gives idempotence and
`map p ≤ map id = id` gives `map p ⊑ id`.

## What is proved here

| # | Statement | Content |
| - | --------- | ------- |
| 1 | `map` | `f♮ = ext({\|·\|} ∘ f)`, generically in the presentation `A` of `K(D)` |
| 2 | `map_unit` | the naturality square, `f♮({\|x\|}) = {\|f x\|}` |
| 3 | `isHom_map`, `scottContinuous_map` | `f♮` is a homomorphism of continuous algebras, hence continuous |
| 4 | `exists_unique_map` | the paper's sentence: existence **and** uniqueness |
| 5 | `map_id` | `(id)♮ = id` — the first functor law |
| 6 | `map_comp` | `(g ∘ f)♮ = g♮ ∘ f♮` — the second functor law |
| 7 | `map_le_map` | local monotonicity: `f ⊑ g` implies `f♮ ⊑ g♮` |
| 8 | `isProjection_map` | `p` a projection implies `p♮` a projection |
| 9 | `PowerdomainCompacts` (separate module) | `p(K(D)) ⊆ K(D)` fails for a finitary projection |

Rows 1–8 are generic in the pre-order `A` presenting `Pf(K(D))`, so each holds at
all three powerdomains at once; the three `hoare`/`smyth`/`plotkin` sections
discharge the single ordering-specific obligation `hmono`, exactly as
`thm12_hoare`, `thm12_smyth` and `thm12_plotkin` do for Theorem 12.

## The one obligation that is not generic

`thm12` leaves open `Monotone (foldGen ({|·|} ∘ f))` — that the fold
`{|f x₁|} ⋓ ⋯ ⋓ {|f xₙ|}` is monotone for the pre-order `A`. It is discharged by
`fold_le_fold_of_hoare` under `T♭`, `fold_le_fold_of_smyth` under `T♯`, and
`fold_le_fold_of_convex` under `T♮`, and the model conditions
`instIsLowerHoare`, `instIsUpperSmyth` and `instIsSemilatticeIdealCompletion` are
what make each available at the *target* powerdomain. This is the same three-way
split as Theorem 12 and for the same reason: the theory is what relates `⋓` to
the domain order, and the convex case has the least of it.
-/

namespace ScottDomains.PowerdomainMap

open ScottDomains ScottDomains.ContinuousAlgebra ScottDomains.IdealCompletion

universe u

/-! ## 1. Homomorphisms compose

Two facts about `IsHom` that `ContinuousAlgebra.lean` never needed, because
Theorem 12 produces a single homomorphism and never composes two. Both functor
laws below are uniqueness arguments and both need one of these. -/

section HomAlgebra

variable {F G H : Type u}
variable [CompletePartialOrder F] [CompletePartialOrder G] [CompletePartialOrder H]
variable [Binop F] [Binop G] [Binop H]

/-- The identity is a homomorphism of continuous algebras. -/
theorem isHom_id : IsHom (id : F → F) :=
  ⟨ScottContinuous.id, fun _ _ => rfl⟩

/-- A composite of homomorphisms is a homomorphism: continuity composes by
`ScottContinuous.comp`, and `map_op` composes by rewriting twice. -/
theorem isHom_comp {h₁ : F → G} {h₂ : G → H} (H₁ : IsHom h₁) (H₂ : IsHom h₂) :
    IsHom (h₂ ∘ h₁) :=
  ⟨H₁.scottContinuous.comp H₂.scottContinuous, fun s t => by
    show h₂ (h₁ (s ⋓ t)) = h₂ (h₁ s) ⋓ h₂ (h₁ t)
    rw [H₁.map_op, H₂.map_op]⟩

end HomAlgebra

/-! ## 2. `f♮`, generically in the presentation of `Pf(K(D))`

`A` presents `Pf(K(D))` and `B` presents `Pf(K(E))`; the three powerdomains
differ only in which pre-order is put on that carrier, and nothing below inspects
the ordering except through the hypothesis `hmono`. -/

section Generic

variable {D E F : Type u}
variable [CompletePartialOrder D] [IsAlgebraic D]
variable [CompletePartialOrder E] [IsAlgebraic E]
variable [CompletePartialOrder F] [IsAlgebraic F]
variable {A : Type u} [Preorder A] [OrderBot A] [FinSets ↥(compacts D) A]
variable {B : Type u} [Preorder B] [OrderBot B] [FinSets ↥(compacts E) B]
variable {C : Type u} [Preorder C] [OrderBot C] [FinSets ↥(compacts F) C]

/-- `{|·|} ∘ f : D → E♮`, the diagonal of the paper's naturality square. Named
rather than written inline so that `foldGen` applications match syntactically in
every statement below. -/
noncomputable def unitComp (f : D → E) (x : D) : IdealCompletion B := unit (f x)

omit [CompletePartialOrder D] [IsAlgebraic D] in
@[simp] theorem unitComp_apply (f : D → E) (x : D) :
    unitComp (B := B) f x = unit (f x) := rfl

omit [IsAlgebraic D] in
/-- `{|·|} ∘ f` is continuous: `scottContinuous_unit` after `hf`. -/
theorem scottContinuous_unitComp {f : D → E} (hf : ScottContinuous f) :
    ScottContinuous (unitComp (B := B) f) :=
  hf.comp scottContinuous_unit

/-- **The paper's `f♮ = ext({|·|} ∘ f)`.** Theorem 12 applied with the target
algebra taken to be the powerdomain `E♮` itself, which satisfies `T♮` by
`instIsSemilatticeIdealCompletion`. -/
noncomputable def map (f : D → E) : IdealCompletion A → IdealCompletion B :=
  ext (A := A) (unitComp (B := B) f)

omit [IsAlgebraic D] [OrderBot A] in
theorem map_apply (f : D → E) (I : IdealCompletion A) :
    map (A := A) (B := B) f I = idealExtend (foldGen (unitComp (B := B) f)) I := rfl

/-- **The naturality square commutes**: `f♮({|x|}) = {|f x|}`. -/
theorem map_unit {f : D → E}
    (hmono : Monotone (foldGen (A := A) (unitComp (B := B) f)))
    (hf : ScottContinuous f) (x : D) :
    map (A := A) (B := B) f (unit x) = unit (f x) :=
  ext_unit hmono (scottContinuous_unitComp hf) x

omit [IsAlgebraic D] [OrderBot A] in
/-- On a principal ideal `↓u`, `f♮` is the fold `{|f x₁|} ⋓ ⋯ ⋓ {|f xₙ|}` — the
paper's own hint for `ext`. -/
theorem map_principal {f : D → E}
    (hmono : Monotone (foldGen (A := A) (unitComp (B := B) f))) (u : A) :
    map (A := A) (B := B) f (principal u) = foldGen (unitComp (B := B) f) u :=
  ext_principal hmono u

omit [IsAlgebraic D] in
/-- **`f♮` is a homomorphism of continuous algebras.** -/
theorem isHom_map {f : D → E}
    (hmono : Monotone (foldGen (A := A) (unitComp (B := B) f))) :
    IsHom (map (A := A) (B := B) f) :=
  isHom_ext hmono

omit [IsAlgebraic D] in
/-- **`f♮` is Scott continuous** — the first component of `isHom_map`, named
because the bundled `ScottHom` needs it on its own. -/
theorem scottContinuous_map {f : D → E}
    (hmono : Monotone (foldGen (A := A) (unitComp (B := B) f))) :
    ScottContinuous (map (A := A) (B := B) f) :=
  scottContinuous_ext hmono

/-- **§5.3's sentence, in full.** *If `f : D → E` is a continuous function, then
there is a unique homomorphism `f♮ : D♮ → E♮` which makes the diagram commute.*

Existence and uniqueness both, and the predicate carries both conjuncts: `h` is a
homomorphism of continuous algebras, and `h ∘ {|·|} = {|·|} ∘ f`. This is
`thm12` with the free algebra `E♮` as target. -/
theorem exists_unique_map {f : D → E} (hf : ScottContinuous f)
    (hmono : Monotone (foldGen (A := A) (unitComp (B := B) f))) :
    ∃! h : IdealCompletion A → IdealCompletion B,
      IsHom h ∧ ∀ x : D, h (unit x) = unit (f x) :=
  thm12 (scottContinuous_unitComp hf) hmono

/-! ### The functor laws

Both are uniqueness arguments against `exists_unique_map`, and neither inspects
the construction: the candidate is shown to be a homomorphism completing the same
square, and uniqueness identifies it with `map`. -/

/-- **`(id)♮ = id`.** The identity is a homomorphism and completes the square
`id ∘ {|·|} = {|·|} ∘ id` on the nose, so uniqueness identifies it with
`map id`. -/
theorem map_id
    (hmono : Monotone (foldGen (A := A) (unitComp (B := A) (id : D → D)))) :
    map (A := A) (B := A) (id : D → D) = id := by
  obtain ⟨_h₀, -, huniq⟩ :=
    exists_unique_map (A := A) (B := A) (f := (id : D → D)) ScottContinuous.id hmono
  exact (huniq _ ⟨isHom_map hmono, fun x => map_unit hmono ScottContinuous.id x⟩).trans
    (huniq _ ⟨isHom_id, fun _ => rfl⟩).symm

/-- **`(g ∘ f)♮ = g♮ ∘ f♮`.** `g♮ ∘ f♮` is a homomorphism by `isHom_comp` and
completes the square by two applications of `map_unit`, so uniqueness identifies
it with `map (g ∘ f)`. -/
theorem map_comp {f : D → E} {g : E → F} (hf : ScottContinuous f) (hg : ScottContinuous g)
    (hmf : Monotone (foldGen (A := A) (unitComp (B := B) f)))
    (hmg : Monotone (foldGen (A := B) (unitComp (B := C) g)))
    (hmgf : Monotone (foldGen (A := A) (unitComp (B := C) (g ∘ f)))) :
    map (A := A) (B := C) (g ∘ f)
      = map (A := B) (B := C) g ∘ map (A := A) (B := B) f := by
  obtain ⟨_h₀, -, huniq⟩ :=
    exists_unique_map (A := A) (B := C) (f := g ∘ f) (hf.comp hg) hmgf
  refine (huniq _ ⟨isHom_map hmgf, fun x => map_unit hmgf (hf.comp hg) x⟩).trans
    (huniq _ ⟨isHom_comp (isHom_map hmf) (isHom_map hmg), fun x => ?_⟩).symm
  show map (A := B) (B := C) g (map (A := A) (B := B) f (unit x)) = unit (g (f x))
  rw [map_unit hmf hf, map_unit hmg hg]

omit [IsAlgebraic D] [OrderBot A] in
/-- **Local monotonicity**: `f ⊑ g` pointwise implies `f♮ ⊑ g♮` pointwise.

Not a functor law, and not derivable from the two that are: it is the statement
that the action is monotone on the *hom-set*, which is what makes `map p ⊑ map id`
available in `isProjection_map`. The proof is `fold_le_fold` under the least upper
bounds that define `idealExtend`; the only fact used about `{|·|}` is
`monotone_unit`. -/
theorem map_le_map {f g : D → E} (hfg : ∀ x, f x ≤ g x)
    (hmf : Monotone (foldGen (A := A) (unitComp (B := B) f)))
    (hmg : Monotone (foldGen (A := A) (unitComp (B := B) g))) (I : IdealCompletion A) :
    map (A := A) (B := B) f I ≤ map (A := A) (B := B) g I := by
  refine (isLUB_idealExtend hmf I).2 ?_
  rintro _ ⟨u, hu, rfl⟩
  refine le_trans ?_ ((isLUB_idealExtend hmg I).1 ⟨u, hu, rfl⟩)
  exact fold_le_fold _ fun k _ => monotone_unit (hfg (k : D))

/-- **The action of a projection is a projection.**

This is what Lemma 28's `()♯` and `()♭` conjuncts need, and it is proved from the
two functor laws and local monotonicity, with no appeal to compact elements at
all: `p ∘ p = p` gives `p♮ ∘ p♮ = p♮` through `map_comp`, and `p ⊑ id` gives
`p♮ ⊑ (id)♮ = id` through `map_le_map` and `map_id`. -/
theorem isProjection_map {p : D → D} (hcont : ScottContinuous p)
    (hidem : ∀ x, p (p x) = p x) (hle : ∀ x, p x ≤ x)
    (hmp : Monotone (foldGen (A := A) (unitComp (B := A) p)))
    (hmid : Monotone (foldGen (A := A) (unitComp (B := A) (id : D → D)))) :
    (∀ I : IdealCompletion A, map (A := A) (B := A) p (map (A := A) (B := A) p I)
        = map (A := A) (B := A) p I)
      ∧ ∀ I : IdealCompletion A, map (A := A) (B := A) p I ≤ I := by
  have hpp : (p ∘ p) = p := funext hidem
  constructor
  · intro I
    have hcomp := map_comp (A := A) (B := A) (C := A) hcont hcont hmp hmp (by rwa [hpp])
    rw [hpp] at hcomp
    exact congrFun hcomp.symm I
  · intro I
    have h := map_le_map (A := A) (B := A) (f := p) (g := (id : D → D)) hle hmp hmid I
    rwa [map_id hmid, id_eq] at h

/-- The bundled form: `f♮` as a `ScottHom` between the two powerdomains, which is
the shape `ScottHom.IsProjection` and the `Fp(U)` machinery of §7.3 take. -/
noncomputable def scottHom {f : D → E}
    (hmono : Monotone (foldGen (A := A) (unitComp (B := B) f))) :
    ScottHom (IdealCompletion A) (IdealCompletion B) :=
  ⟨map (A := A) (B := B) f, scottContinuous_map hmono⟩

omit [IsAlgebraic D] in
@[simp] theorem scottHom_apply {f : D → E}
    (hmono : Monotone (foldGen (A := A) (unitComp (B := B) f))) (I : IdealCompletion A) :
    scottHom (A := A) (B := B) hmono I = map (A := A) (B := B) f I := rfl

/-- `isProjection_map` in the bundled form `ScottHom.IsProjection` asks for. -/
theorem isProjection_scottHom {p : D → D} (hcont : ScottContinuous p)
    (hidem : ∀ x, p (p x) = p x) (hle : ∀ x, p x ≤ x)
    (hmp : Monotone (foldGen (A := A) (unitComp (B := A) p)))
    (hmid : Monotone (foldGen (A := A) (unitComp (B := A) (id : D → D)))) :
    ScottHom.IsProjection (scottHom (A := A) (B := A) hmp) :=
  isProjection_map hcont hidem hle hmp hmid

end Generic

/-! ## 3. The three powerdomains

Each section discharges `hmono` for its ordering and names the resulting action.
The discharges are the same three lemmas Theorem 12 spends — and in the same
pairing of theory to ordering, which is the kernel's check that the `♯`/`♭`
correspondence has not been inverted. -/

section Hoare

variable {D E : Type u}
variable [CompletePartialOrder D] [IsAlgebraic D] [CompletePartialOrder E] [IsAlgebraic E]

omit [IsAlgebraic D] in
/-- `hmono` at the **Hoare** ordering, from `4♭` in the target `E♭`. -/
theorem foldMono_hoare {f : D → E} (hf : ScottContinuous f) :
    Monotone (foldGen (A := Hoare.Pf ↥(compacts D))
      (unitComp (B := Hoare.Pf ↥(compacts E)) f)) :=
  fun _ _ huv => fold_le_fold_of_hoare _ _
    (fun _ _ h => (scottContinuous_unitComp hf).monotone h)
    fun a ha => Hoare.Pf.le_def.mp huv a ha

/-- **`f♭ : D♭ → E♭`.** -/
noncomputable def hoare (f : D → E) :
    IdealCompletion (Hoare.Pf ↥(compacts D)) → IdealCompletion (Hoare.Pf ↥(compacts E)) :=
  map f

/-- **§5.3's `f♭`, existence and uniqueness.** -/
theorem thm_map_hoare {f : D → E} (hf : ScottContinuous f) :
    ∃! h : IdealCompletion (Hoare.Pf ↥(compacts D)) →
        IdealCompletion (Hoare.Pf ↥(compacts E)),
      IsHom h ∧ ∀ x : D, h (unit x) = unit (f x) :=
  exists_unique_map hf (foldMono_hoare hf)

theorem hoare_unit {f : D → E} (hf : ScottContinuous f) (x : D) :
    hoare f (unit x) = unit (f x) :=
  map_unit (foldMono_hoare hf) hf x

omit [IsAlgebraic D] in
theorem isHom_hoare {f : D → E} (hf : ScottContinuous f) : IsHom (hoare f) :=
  isHom_map (foldMono_hoare hf)

omit [IsAlgebraic D] in
theorem scottContinuous_hoare {f : D → E} (hf : ScottContinuous f) :
    ScottContinuous (hoare f) :=
  scottContinuous_map (foldMono_hoare hf)

/-- **`(id)♭ = id`.** -/
theorem hoare_id : hoare (id : D → D) = id :=
  map_id (foldMono_hoare ScottContinuous.id)

/-- **`(g ∘ f)♭ = g♭ ∘ f♭`.** -/
theorem hoare_comp {F : Type u} [CompletePartialOrder F] [IsAlgebraic F]
    {f : D → E} {g : E → F} (hf : ScottContinuous f) (hg : ScottContinuous g) :
    hoare (g ∘ f) = hoare g ∘ hoare f :=
  map_comp hf hg (foldMono_hoare hf) (foldMono_hoare hg) (foldMono_hoare (hf.comp hg))

/-- **A projection acts as a projection on `D♭`.** -/
theorem isProjection_hoare {p : D → D} (hcont : ScottContinuous p)
    (hidem : ∀ x, p (p x) = p x) (hle : ∀ x, p x ≤ x) :
    ScottHom.IsProjection
      (⟨hoare p, scottContinuous_hoare hcont⟩ :
        ScottHom (IdealCompletion (Hoare.Pf ↥(compacts D)))
          (IdealCompletion (Hoare.Pf ↥(compacts D)))) :=
  isProjection_map hcont hidem hle (foldMono_hoare hcont)
    (foldMono_hoare ScottContinuous.id)

end Hoare

section Smyth

variable {D E : Type u}
variable [CompletePartialOrder D] [IsAlgebraic D] [CompletePartialOrder E] [IsAlgebraic E]

omit [IsAlgebraic D] in
/-- `hmono` at the **Smyth** ordering, from `4♯` in the target `E♯`. -/
theorem foldMono_smyth {f : D → E} (hf : ScottContinuous f) :
    Monotone (foldGen (A := Smyth.Basis D) (unitComp (B := Smyth.Basis E) f)) :=
  fun _ _ huv => fold_le_fold_of_smyth _ _
    (fun _ _ h => (scottContinuous_unitComp hf).monotone h)
    fun b hb => Smyth.Basis.le_def.mp huv b hb

/-- **`f♯ : D♯ → E♯`.** -/
noncomputable def smyth (f : D → E) : Smyth.Powerdomain D → Smyth.Powerdomain E :=
  map f

/-- **§5.3's `f♯`, existence and uniqueness.** -/
theorem thm_map_smyth {f : D → E} (hf : ScottContinuous f) :
    ∃! h : Smyth.Powerdomain D → Smyth.Powerdomain E,
      IsHom h ∧ ∀ x : D, h (unit x) = unit (f x) :=
  exists_unique_map hf (foldMono_smyth hf)

theorem smyth_unit {f : D → E} (hf : ScottContinuous f) (x : D) :
    smyth f (unit x) = unit (f x) :=
  map_unit (foldMono_smyth hf) hf x

omit [IsAlgebraic D] in
theorem isHom_smyth {f : D → E} (hf : ScottContinuous f) : IsHom (smyth f) :=
  isHom_map (foldMono_smyth hf)

omit [IsAlgebraic D] in
theorem scottContinuous_smyth {f : D → E} (hf : ScottContinuous f) :
    ScottContinuous (smyth f) :=
  scottContinuous_map (foldMono_smyth hf)

/-- **`(id)♯ = id`.** -/
theorem smyth_id : smyth (id : D → D) = id :=
  map_id (foldMono_smyth ScottContinuous.id)

/-- **`(g ∘ f)♯ = g♯ ∘ f♯`.** -/
theorem smyth_comp {F : Type u} [CompletePartialOrder F] [IsAlgebraic F]
    {f : D → E} {g : E → F} (hf : ScottContinuous f) (hg : ScottContinuous g) :
    smyth (g ∘ f) = smyth g ∘ smyth f :=
  map_comp hf hg (foldMono_smyth hf) (foldMono_smyth hg) (foldMono_smyth (hf.comp hg))

/-- **A projection acts as a projection on `D♯`.** This is the fact Lemma 28's
`()♯` conjunct needs and that no earlier round had. -/
theorem isProjection_smyth {p : D → D} (hcont : ScottContinuous p)
    (hidem : ∀ x, p (p x) = p x) (hle : ∀ x, p x ≤ x) :
    ScottHom.IsProjection
      (⟨smyth p, scottContinuous_smyth hcont⟩ :
        ScottHom (Smyth.Powerdomain D) (Smyth.Powerdomain D)) :=
  isProjection_map hcont hidem hle (foldMono_smyth hcont)
    (foldMono_smyth ScottContinuous.id)

end Smyth

section Plotkin

variable {D E : Type u}
variable [CompletePartialOrder D] [IsAlgebraic D] [CompletePartialOrder E] [IsAlgebraic E]

omit [IsAlgebraic D] in
/-- `hmono` at the **Egli–Milner** ordering, under `T♮` alone. Both conjuncts of
the ordering are consumed, and `fold_le_fold_of_convex` is where the work is —
under `T♮` the operation `⋓` is unrelated to the domain order. -/
theorem foldMono_plotkin {f : D → E} (hf : ScottContinuous f) :
    Monotone (foldGen (A := Plotkin.FinCompacts D)
      (unitComp (B := Plotkin.FinCompacts E) f)) := by
  intro u v huv
  refine fold_le_fold_of_convex _ _
    (fun _ _ h => (scottContinuous_unitComp (B := Plotkin.FinCompacts E) hf).monotone h) ?_ ?_
  · intro a ha
    obtain ⟨b, hb, hab⟩ := huv.1 a ((Set.Finite.mem_toFinset _).mp ha)
    exact ⟨b, (Set.Finite.mem_toFinset _).mpr hb, hab⟩
  · intro b hb
    obtain ⟨a, ha, hab⟩ := huv.2 b ((Set.Finite.mem_toFinset _).mp hb)
    exact ⟨a, (Set.Finite.mem_toFinset _).mpr ha, hab⟩

/-- **`f♮ : D♮ → E♮`**, the case the paper states. -/
noncomputable def plotkin (f : D → E) : Plotkin.Powerdomain D → Plotkin.Powerdomain E :=
  map f

/-- **§5.3's `f♮`, existence and uniqueness — the paper's own sentence.** -/
theorem thm_map_plotkin {f : D → E} (hf : ScottContinuous f) :
    ∃! h : Plotkin.Powerdomain D → Plotkin.Powerdomain E,
      IsHom h ∧ ∀ x : D, h (unit x) = unit (f x) :=
  exists_unique_map hf (foldMono_plotkin hf)

theorem plotkin_unit {f : D → E} (hf : ScottContinuous f) (x : D) :
    plotkin f (unit x) = unit (f x) :=
  map_unit (foldMono_plotkin hf) hf x

omit [IsAlgebraic D] in
theorem isHom_plotkin {f : D → E} (hf : ScottContinuous f) : IsHom (plotkin f) :=
  isHom_map (foldMono_plotkin hf)

omit [IsAlgebraic D] in
theorem scottContinuous_plotkin {f : D → E} (hf : ScottContinuous f) :
    ScottContinuous (plotkin f) :=
  scottContinuous_map (foldMono_plotkin hf)

/-- **`(id)♮ = id`.** -/
theorem plotkin_id : plotkin (id : D → D) = id :=
  map_id (foldMono_plotkin ScottContinuous.id)

/-- **`(g ∘ f)♮ = g♮ ∘ f♮`.** -/
theorem plotkin_comp {F : Type u} [CompletePartialOrder F] [IsAlgebraic F]
    {f : D → E} {g : E → F} (hf : ScottContinuous f) (hg : ScottContinuous g) :
    plotkin (g ∘ f) = plotkin g ∘ plotkin f :=
  map_comp hf hg (foldMono_plotkin hf) (foldMono_plotkin hg) (foldMono_plotkin (hf.comp hg))

/-- **A projection acts as a projection on `D♮`.** -/
theorem isProjection_plotkin {p : D → D} (hcont : ScottContinuous p)
    (hidem : ∀ x, p (p x) = p x) (hle : ∀ x, p x ≤ x) :
    ScottHom.IsProjection
      (⟨plotkin p, scottContinuous_plotkin hcont⟩ :
        ScottHom (Plotkin.Powerdomain D) (Plotkin.Powerdomain D)) :=
  isProjection_map hcont hidem hle (foldMono_plotkin hcont)
    (foldMono_plotkin ScottContinuous.id)

end Plotkin

/-! ## 4. The instances resolve

An instance chain that is never demanded is never checked. `Prop` is the cheapest
domain in the development, so these force resolution to run the whole chain at
each of the three carriers: the `FinSets` presentation of `Pf(K(Prop))`, the
`Binop` on the target powerdomain, and the theory instance that `hmono` spends. -/

section Witnesses

example : ScottContinuous (hoare (id : Prop → Prop)) := scottContinuous_hoare ScottContinuous.id
example : ScottContinuous (smyth (id : Prop → Prop)) := scottContinuous_smyth ScottContinuous.id
example : ScottContinuous (plotkin (id : Prop → Prop)) :=
  scottContinuous_plotkin ScottContinuous.id

end Witnesses

end ScottDomains.PowerdomainMap

/- Axiom audit, by `scripts/axioms.sh` (run, then recorded here so the build emits
no `info` lines). Every declaration depends only on the three standard axioms;
none depends on `sorryAx`.

  ScottDomains.PowerdomainMap.map               [propext, Classical.choice, Quot.sound]
  ScottDomains.PowerdomainMap.exists_unique_map [propext, Classical.choice, Quot.sound]
  ScottDomains.PowerdomainMap.map_id            [propext, Classical.choice, Quot.sound]
  ScottDomains.PowerdomainMap.map_comp          [propext, Classical.choice, Quot.sound]
  ScottDomains.PowerdomainMap.map_le_map        [propext, Classical.choice, Quot.sound]
  ScottDomains.PowerdomainMap.isProjection_map  [propext, Classical.choice, Quot.sound]
  ScottDomains.PowerdomainMap.thm_map_hoare     [propext, Classical.choice, Quot.sound]
  ScottDomains.PowerdomainMap.thm_map_smyth     [propext, Classical.choice, Quot.sound]
  ScottDomains.PowerdomainMap.thm_map_plotkin   [propext, Classical.choice, Quot.sound]
  ScottDomains.PowerdomainMap.isProjection_smyth [propext, Classical.choice, Quot.sound]
  ScottDomains.PowerdomainMap.isProjection_hoare [propext, Classical.choice, Quot.sound]

`Classical.choice` is inherited entirely from `IdealCompletion`'s `idealSup`, a
`dite` on the undecidable `Order.IsIdeal`, through `idealExtend`; nothing in this
file introduces a new use. -/
