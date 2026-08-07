import ScottDomains.Universality

/-!
# §7.2, Theorem 26: a fixed algebra on `D` containing every continuous algebra on a retract

Gunter & Scott, *Semantic Domains*, §7.2, quoted from the source PDF:

> We will call an expression in the notation of applicative algebra which has no
> variables a **combination**. Any combination `F` defines an `n`-ary operation
> `F(x₁)(x₂)⋯(x_n)`.

> **Theorem 26** Given a signature `(s₁, s₂, …, s_n)`, there are combinations
> `F₁, F₂, …, F_n` defining operations on `D` of these arities such that whenever
> a continuous algebra of this signature is given on a domain `A` that is a
> retract of `D`, then `A` can be made isomorphic to a subalgebra of this fixed
> algebra structure on `D`.

> *Proof:* … We are going to define the representation of `A` as a subalgebra of
> `D` by means of a continuous function `ψ : A → D` defined by means of a
> fixed-point equation:
>
> > `ψ(a) = pair(a)`
> > `      (pair(λx₂…x_{s₁}. ψ(o₁(a, fst(x₂), …, fst(x_{s₁}))))`
> > `      (pair(λx₂…x_{s₂}. ψ(o₂(a, fst(x₂), …, fst(x_{s₂}))))`
> > `             ⋮`
> > `      (pair(λx₂…x_{s_n}. ψ(o_n(a, fst(x₂), …, fst(x_{s_n}))))`
> > `      (K))⋯)`
>
> Consider the following combinations:
>
> > `F₁ = λx. fst(snd(x))`,  `F₂ = λx. fst(snd(snd(x)))`,  …,
> > `F_n = λx. fst(snd(snd(⋯snd(x))))`,
>
> which have to be rewritten in terms of `S`, `K`, `fst`, and `snd`. We then
> calculate that
>
> > `Fᵢ(ψ(a₁))(ψ(a₂))⋯(ψ(a_{sᵢ})) = ψ(oᵢ(a₁, a₂, …, a_{sᵢ}))`.

This file is that proof. `thm26` is the displayed calculation and
`thm26_subalgebra` its reading as "`A` is isomorphic to a subalgebra".

## Where `D` comes from

`D` is the λ-calculus model of §7.2: a cpo with `D ≅ D → D` and `D ≅ D × D`.
`Universality.thm25` produces exactly that, so `LambdaModel` — the applicative
structure the proof consumes — is derived from a pair of order isomorphisms and
nothing else (`LambdaModel.ofOrderIso`), and `exists_thm26_of_thm25` is Theorem 25
feeding it.

## Two design decisions, and the reason for each

**The signature is indexed by `Fin n`, with arities in `ℕ`.** The paper writes
`(s₁, s₂, …, s_n)`, a finite *sequence*: the operations are ordered and the proof
uses the order — `Fᵢ` reads the `i`-th slot of a right-nested tuple by applying
`snd` exactly `i` times, so the index must carry a position, not merely an
identity. `Fin n → ℕ` is that sequence. A general finite index type `ι` with
`[Fintype ι]` carries an identity but not a position, and every use would have to
choose an enumeration of `ι`, reintroducing `Fin n` under an extra layer.

**Arities are required positive** (`hs : ∀ i, 0 < s i`), and this is a correction
to the paper, not a convenience. The paper explicitly admits `0` in a signature
("here, `0` indicates a 0-ary operation, which is just a constant", of the
signature `(2,0,0,0,0,0)`), but **Theorem 26 is false for any signature containing
`0`**, by the following argument, which is stated here and is *not* Lean-checked.
Suppose `sᵢ = 0`. `Fᵢ` is one fixed element of `D`; a subalgebra of
`⟨D, F₁, …, F_n⟩` contains `Fᵢ` and has `Fᵢ` as its own `i`-th constant, so an
isomorphism of `A` onto a subalgebra must send `A`'s constant `oᵢ` to `Fᵢ`. Take
two one-point algebras `A = {a}` and `B = {b}` with `a ≠ b`, both retracts of `D`.
Both embeddings must hit that same `Fᵢ`, and the paper's own `ψ` satisfies
`fst(ψ(x)) = x` (`thm26`'s first conjunct), so `a = fst(Fᵢ) = b` — a contradiction.
The paper's construction breaks down before that: `Fᵢ` reads a slot *out of an
argument*, and a 0-ary operation supplies no argument to read it out of.

## The interior of the tuple

The paper terminates the right-nested tuple with the combination `K`. Nothing ever
reads past the last slot, so any element of `D` serves; `⊥` is used here, which
keeps `K` and `S` out of the data `ψ` depends on. They are still needed for `Fᵢ`
itself, which the paper requires to be a **combination**: `Comb`, `combEval` and
`fComb` exhibit `Fᵢ` as an explicit variable-free term over `S`, `K`, `fst`, `snd`.

## Operations as elements of `D`

An `m`-ary continuous operation on `D` is taken to be an element `o : D` acting by
`x₁, …, x_m ↦ o ⬝ x₁ ⬝ ⋯ ⬝ x_m` (`iterApp`). This costs no generality: `D ≅ D → D`
makes `D` a reflexive object, so `lam` turns any continuous `D → D` into an element
and `ScottHom.curry` followed by `lam` twice turns any jointly continuous
`D × D → D` into one (`elem_of_hom₁`, `elem_of_hom₂`; the induction for general `m`
is the same and no statement here consumes it). The paper works in the same
notation — its `oᵢ(a, fst(x₂), …)` is applicative, not a Lean function.
-/

namespace ScottDomains.Combinator

open ScottDomains.Universality

universe u

/-! ## Toolkit: bundled composition, and continuity into a function space

Every continuity obligation below is discharged by exhibiting a map as a composite
of bundled `ScottHom`s. These are the pieces. -/

section Toolkit

variable {α β γ : Type*}

/-- Composition of bundled Scott-continuous maps. The development has
`ScottContinuous.comp` but no bundled composition, and the fixed-point functional
below is built entirely out of composites. -/
def comp [Preorder α] [Preorder β] [Preorder γ] (g : ScottHom β γ) (f : ScottHom α β) :
    ScottHom α γ :=
  ⟨⇑g ∘ ⇑f, ScottContinuous.comp f.scottContinuous g.scottContinuous⟩

@[simp] theorem comp_apply [Preorder α] [Preorder β] [Preorder γ]
    (g : ScottHom β γ) (f : ScottHom α β) (x : α) : comp g f x = g (f x) := rfl

/-- `(f, g) ↦ fun a => (f a, g a)`, bundled. -/
def prodMkHom [Preorder α] [Preorder β] [Preorder γ] (f : ScottHom α β) (g : ScottHom α γ) :
    ScottHom α (β × γ) :=
  ⟨fun a => (f a, g a), ScottContinuous.prodMk f.scottContinuous g.scottContinuous⟩

@[simp] theorem prodMkHom_apply [Preorder α] [Preorder β] [Preorder γ]
    (f : ScottHom α β) (g : ScottHom α γ) (a : α) : prodMkHom f g a = (f a, g a) := rfl

/-- **A pointwise-continuous family of continuous maps is continuous into the
function space.** Least upper bounds in `ScottHom β γ` are pointwise, so both
halves of `IsLUB` reduce to the corresponding halves at each argument. This is the
lemma that makes each "λ inside a fixed point" below cost nothing. -/
theorem scottContinuous_of_pointwise [Preorder α] [Preorder β] [CompletePartialOrder γ]
    {f : α → ScottHom β γ} (h : ∀ y, ScottContinuous fun a => f a y) : ScottContinuous f := by
  intro d hne hd a ha
  refine ⟨?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩ y
    exact (h y).monotone (ha.1 hp)
  · intro u hu y
    refine ((h y) hne hd ha).2 ?_
    rintro _ ⟨p, hp, rfl⟩
    exact hu ⟨p, hp, rfl⟩ y

/-- Evaluation at a point, bundled: `f ↦ f x`. -/
def evalHom [Preorder α] [CompletePartialOrder β] (x : α) : ScottHom (ScottHom α β) β :=
  ⟨fun f => f x, by
    intro d _ hd F hF
    exact ScottHom.isLUB_eval_image_of_isLUB hd hF x⟩

@[simp] theorem evalHom_apply [Preorder α] [CompletePartialOrder β] (x : α)
    (f : ScottHom α β) : evalHom x f = f x := rfl

/-- The constant family, bundled: `b ↦ (fun _ => b)`. -/
def constHom [Preorder α] [CompletePartialOrder β] : ScottHom β (ScottHom α β) :=
  ⟨ScottHom.const, scottContinuous_of_pointwise fun _ => ScottContinuous.id⟩

@[simp] theorem constHom_apply [Preorder α] [CompletePartialOrder β] (b : β) :
    (constHom (α := α) b) = ScottHom.const b := rfl

/-- Post-composition by a fixed map, bundled: `f ↦ h ∘ f`. -/
def postHom [Preorder α] [CompletePartialOrder β] [CompletePartialOrder γ]
    (h : ScottHom β γ) : ScottHom (ScottHom α β) (ScottHom α γ) :=
  ⟨fun f => comp h f, scottContinuous_of_pointwise fun y =>
    (comp h (evalHom (α := α) (β := β) y)).scottContinuous⟩

@[simp] theorem postHom_apply [Preorder α] [CompletePartialOrder β] [CompletePartialOrder γ]
    (h : ScottHom β γ) (f : ScottHom α β) : postHom h f = comp h f := rfl

/-- Pre-composition by a fixed map, bundled: `f ↦ f ∘ h`. -/
def preHom [Preorder α] [Preorder β] [CompletePartialOrder γ]
    (h : ScottHom α β) : ScottHom (ScottHom β γ) (ScottHom α γ) :=
  ⟨fun f => comp f h, scottContinuous_of_pointwise fun y => (evalHom (h y)).scottContinuous⟩

@[simp] theorem preHom_apply [Preorder α] [Preorder β] [CompletePartialOrder γ]
    (h : ScottHom α β) (f : ScottHom β γ) : preHom h f = comp f h := rfl

/-- Post-composition, bundled *in the map being composed with*: `h ↦ (f ↦ h ∘ f)`.
This is the one that makes the recursion on the arity below a composite. -/
def postHomHom [Preorder α] [CompletePartialOrder β] [CompletePartialOrder γ] :
    ScottHom (ScottHom β γ) (ScottHom (ScottHom α β) (ScottHom α γ)) :=
  ⟨postHom, scottContinuous_of_pointwise fun f => (preHom f).scottContinuous⟩

@[simp] theorem postHomHom_apply [Preorder α] [CompletePartialOrder β] [CompletePartialOrder γ]
    (h : ScottHom β γ) : (postHomHom (α := α) h) = postHom h := rfl

end Toolkit

/-! ## The λ-calculus model

The applicative structure §7.2 works in: application, abstraction with the β-law,
and a pairing with its two projections. -/

/-- **The applicative structure of §7.2.** `app` and `lam` are the two halves of
`D ≅ D → D` and `app_lam` is the β-law; `pairH`, `fstH`, `sndH` come from
`D ≅ D × D`. Nothing else about `D` is used anywhere below. -/
structure LambdaModel (D : Type u) [CompletePartialOrder D] where
  /-- Application, `D → (D → D)`. -/
  app : ScottHom D (ScottHom D D)
  /-- Abstraction, `(D → D) → D`. -/
  lam : ScottHom (ScottHom D D) D
  /-- The β-law. -/
  app_lam : ∀ f, app (lam f) = f
  /-- Pairing. -/
  pairH : ScottHom (D × D) D
  /-- First projection. -/
  fstH : ScottHom D D
  /-- Second projection. -/
  sndH : ScottHom D D
  /-- `fst ∘ pair = π₁`. -/
  fst_pair : ∀ x y, fstH (pairH (x, y)) = x
  /-- `snd ∘ pair = π₂`. -/
  snd_pair : ∀ x y, sndH (pairH (x, y)) = y

namespace LambdaModel

variable {D : Type u} [CompletePartialOrder D]

/-- The applicative structure carried by any cpo with `D ≅ D → D` and `D ≅ D × D`.
An order isomorphism between cpos is Scott continuous
(`Universality.scottContinuous_orderIso`), so nothing further is needed. -/
noncomputable def ofOrderIso (e : D ≃o ScottHom D D) (q : D ≃o D × D) : LambdaModel D where
  app := ⟨⇑e, scottContinuous_orderIso e⟩
  lam := ⟨⇑e.symm, scottContinuous_orderIso e.symm⟩
  app_lam f := e.apply_symm_apply f
  pairH := ⟨⇑q.symm, scottContinuous_orderIso q.symm⟩
  fstH := ⟨fun x => (q x).1,
    ScottContinuous.comp (scottContinuous_orderIso q) ScottContinuous.fst⟩
  sndH := ⟨fun x => (q x).2,
    ScottContinuous.comp (scottContinuous_orderIso q) ScottContinuous.snd⟩
  fst_pair x y := congrArg Prod.fst (q.apply_symm_apply (x, y))
  snd_pair x y := congrArg Prod.snd (q.apply_symm_apply (x, y))

variable (M : LambdaModel D)

/-- Iterated application, `f ⬝ x₁ ⬝ ⋯ ⬝ x_k` — the paper's `F(x₁)(x₂)⋯(x_n)`. -/
def iterApp : D → List D → D
  | f, [] => f
  | f, x :: xs => iterApp (M.app f x) xs

@[simp] theorem iterApp_nil (f : D) : M.iterApp f [] = f := rfl

@[simp] theorem iterApp_cons (f x : D) (xs : List D) :
    M.iterApp f (x :: xs) = M.iterApp (M.app f x) xs := rfl

/-- Every continuous `D → D` is an element of `D`, by `lam`. -/
theorem elem_of_hom₁ (f : ScottHom D D) : ∃ o : D, ∀ x, M.iterApp o [x] = f x :=
  ⟨M.lam f, fun x => by rw [iterApp_cons, iterApp_nil, M.app_lam]⟩

/-- Every jointly continuous `D × D → D` is an element of `D`, by `ScottHom.curry`
and `lam` twice. This is why taking operations to be elements of `D` costs no
generality. -/
theorem elem_of_hom₂ (f : ScottHom (D × D) D) :
    ∃ o : D, ∀ x y, M.iterApp o [x, y] = f (x, y) := by
  refine ⟨M.lam (comp M.lam (ScottHom.curry f)), fun x y => ?_⟩
  rw [iterApp_cons, iterApp_cons, iterApp_nil, M.app_lam, comp_apply, M.app_lam]
  rfl

/-! ### `S` and `K`

Both are needed only to exhibit `Fᵢ` as a combination; neither occurs in `ψ`. -/

/-- Binary application, jointly continuous, via `ScottHom.uncurry`. -/
noncomputable def appU : ScottHom (D × D) D := ScottHom.uncurry M.app

@[simp] theorem appU_apply (x y : D) : M.appU (x, y) = M.app x y := rfl

/-- `a ↦ (f a) ⬝ (g a)`, for continuous `f` and `g`. -/
noncomputable def apHom {α : Type*} [Preorder α] (f g : ScottHom α D) : ScottHom α D :=
  comp M.appU (prodMkHom f g)

@[simp] theorem apHom_apply {α : Type*} [Preorder α] (f g : ScottHom α D) (a : α) :
    M.apHom f g a = M.app (f a) (g a) := rfl

/-- `K = λx. λy. x`, as an element of `D`. -/
noncomputable def kElem : D := M.lam (comp M.lam constHom)

@[simp] theorem kElem_apply (x y : D) : M.app (M.app M.kElem x) y = x := by
  rw [kElem, M.app_lam, comp_apply, constHom_apply, M.app_lam]
  rfl

/-- `λz. x z (y z)`, the body of `S`. -/
noncomputable def sInner (x y : D) : ScottHom D D :=
  M.apHom (M.apHom (ScottHom.const x) ScottHom.id)
    (M.apHom (ScottHom.const y) ScottHom.id)

@[simp] theorem sInner_apply (x y z : D) : M.sInner x y z = M.app (M.app x z) (M.app y z) := rfl

/-- `λy. λz. x z (y z)`. -/
noncomputable def sMid (x : D) : ScottHom D D :=
  ⟨fun y => M.lam (M.sInner x y), by
    refine ScottContinuous.comp (scottContinuous_of_pointwise fun z => ?_) M.lam.scottContinuous
    exact (M.apHom (ScottHom.const (M.app x z))
      (M.apHom ScottHom.id (ScottHom.const z))).scottContinuous⟩

@[simp] theorem sMid_apply (x y : D) : M.sMid x y = M.lam (M.sInner x y) := rfl

/-- `S = λx. λy. λz. x z (y z)`, as an element of `D`. -/
noncomputable def sElem : D :=
  M.lam ⟨fun x => M.lam (M.sMid x), by
    refine ScottContinuous.comp (scottContinuous_of_pointwise fun y => ?_) M.lam.scottContinuous
    refine ScottContinuous.comp (scottContinuous_of_pointwise fun z => ?_) M.lam.scottContinuous
    exact (M.apHom (M.apHom ScottHom.id (ScottHom.const z))
      (ScottHom.const (M.app y z))).scottContinuous⟩

@[simp] theorem sElem_apply (x y z : D) :
    M.app (M.app (M.app M.sElem x) y) z = M.app (M.app x z) (M.app y z) := by
  rw [sElem, M.app_lam]
  show M.app (M.app (M.lam (M.sMid x)) y) z = _
  rw [M.app_lam, sMid_apply, M.app_lam, sInner_apply]

end LambdaModel

/-! ## Combinations

> We will call an expression in the notation of applicative algebra which has no
> variables a **combination**.

`Comb` is that notion of expression, `combEval` its interpretation. `fComb`
exhibits `Fᵢ` as one, which is the part of Theorem 26's statement the word
"combination" carries: `Fᵢ` depends on the signature and on `D`'s applicative
structure, and on nothing whatever about the algebra `A`. -/

/-- A variable-free expression over `S`, `K`, `fst`, `snd` and application. -/
inductive Comb : Type
  | S : Comb
  | K : Comb
  | fstC : Comb
  | sndC : Comb
  | ap : Comb → Comb → Comb

/-- `B = S (K S) K`, the composition combinator. -/
def bComb : Comb := .ap (.ap .S (.ap .K .S)) .K

/-- `fst ∘ snd^k` as a combination: `fstSndPowComb 0 = fst`, and each step composes
another `snd` on the right with `B`. This is the paper's "which have to be
rewritten in terms of `S`, `K`, `fst`, and `snd`". -/
def fstSndPowComb : ℕ → Comb
  | 0 => .fstC
  | k + 1 => .ap (.ap bComb (fstSndPowComb k)) .sndC

namespace LambdaModel

variable {D : Type u} [CompletePartialOrder D]

/-- The interpretation of a combination in the model. -/
noncomputable def combEval (M : LambdaModel D) : Comb → D
  | .S => M.sElem
  | .K => M.kElem
  | .fstC => M.lam M.fstH
  | .sndC => M.lam M.sndH
  | .ap c₁ c₂ => M.app (combEval M c₁) (combEval M c₂)

variable (M : LambdaModel D)

@[simp] theorem combEval_ap (c₁ c₂ : Comb) :
    M.combEval (.ap c₁ c₂) = M.app (M.combEval c₁) (M.combEval c₂) := by rw [combEval]

@[simp] theorem combEval_fstC_apply (x : D) : M.app (M.combEval .fstC) x = M.fstH x := by
  rw [combEval, M.app_lam]

@[simp] theorem combEval_sndC_apply (x : D) : M.app (M.combEval .sndC) x = M.sndH x := by
  rw [combEval, M.app_lam]

@[simp] theorem bComb_apply (f g x : D) :
    M.app (M.app (M.app (M.combEval bComb) f) g) x = M.app f (M.app g x) := by
  simp only [bComb, combEval_ap, combEval, sElem_apply, kElem_apply]

end LambdaModel

/-! ## The construction

Parameterized by a `LambdaModel M` on `D`, a signature `s : Fin n → ℕ` with
positive arities, and a family `o : Fin n → D` of operations. -/

namespace Construction

variable {D : Type u} [CompletePartialOrder D] (M : LambdaModel D)

/-! ### `W ψ k`, the `k`-fold abstraction

`W ψ k c` is the paper's `λx₂…x_{k+1}. ψ(c (fst x₂) ⋯ (fst x_{k+1}))`. It is built
as a bundled map *of `ψ`*, because the whole system is one fixed point in `ψ`. -/

/-- `c ↦ (x ↦ c ⬝ fst x)`, the innermost step of the abstraction. -/
noncomputable def appFst : ScottHom D (ScottHom D D) := comp (preHom M.fstH) M.app

@[simp] theorem appFst_apply (c x : D) : appFst M c x = M.app c (M.fstH x) := rfl

/-- `ψ ↦ (c ↦ λx₂…x_{k+1}. ψ (c (fst x₂) ⋯ (fst x_{k+1})))`, bundled in `ψ`.
`WHom 0` is the identity; each step post-composes with `lam`, pre-composes with
`appFst`, and is therefore a composite of the toolkit's bundled maps — so no
continuity obligation is discharged by hand. -/
noncomputable def WHom : ℕ → ScottHom (ScottHom D D) (ScottHom D D)
  | 0 => ScottHom.id
  | k + 1 =>
    comp (postHom M.lam) (comp (preHom (appFst M)) (comp postHomHom (WHom k)))

@[simp] theorem WHom_zero (ψ : ScottHom D D) : WHom M 0 ψ = ψ := by rw [WHom]; rfl

@[simp] theorem WHom_succ (k : ℕ) (ψ : ScottHom D D) (c : D) :
    WHom M (k + 1) ψ c = M.lam (comp (WHom M k ψ) (appFst M c)) := by rw [WHom]; rfl

/-- **The defining equation of `W`.** `W ψ k c` applied to `ψ b₁, …, ψ b_k` is
`ψ (c ⬝ b₁ ⬝ ⋯ ⬝ b_k)`, provided `ψ` satisfies `fst (ψ b) = b` — which is the only
property of `ψ` this step consumes, and the reason the paper's `ψ` puts `a` in the
first component of the pair. -/
theorem iterApp_WHom {ψ : ScottHom D D} (hψ : ∀ b, M.fstH (ψ b) = b) (k : ℕ) :
    ∀ (c : D) (l : List D), l.length = k →
      M.iterApp (WHom M k ψ c) (l.map ⇑ψ) = ψ (M.iterApp c l) := by
  induction k with
  | zero =>
    rintro c (_ | ⟨b, l⟩) h
    · rw [WHom_zero]; rfl
    · simp at h
  | succ k ih =>
    rintro c (_ | ⟨b, l⟩) h
    · simp at h
    · have hl : l.length = k := by simpa using h
      rw [List.map_cons, LambdaModel.iterApp_cons, WHom_succ, M.app_lam, comp_apply,
        appFst_apply, hψ b, LambdaModel.iterApp_cons]
      exact ih (M.app c b) l hl

/-! ### The right-nested tuple

`tailHom j m` is the tuple of slots `j, j+1, …, j+m-1`, terminated by `⊥`. -/

variable {n : ℕ} (s : Fin n → ℕ) (o : Fin n → D)

/-- The `i`-th slot as a bundled map of `ψ`:
`ψ ↦ (a ↦ λx₂…x_{sᵢ}. ψ(oᵢ ⬝ a ⬝ fst x₂ ⋯ fst x_{sᵢ}))`. -/
noncomputable def slotHom (i : Fin n) : ScottHom (ScottHom D D) (ScottHom D D) :=
  comp (preHom (M.app (o i))) (WHom M (s i - 1))

@[simp] theorem slotHom_apply (i : Fin n) (ψ : ScottHom D D) (a : D) :
    slotHom M s o i ψ a = WHom M (s i - 1) ψ (M.app (o i) a) := rfl

/-- Pairing two continuous families pointwise, bundled jointly. -/
noncomputable def pairHomH : ScottHom (ScottHom D D × ScottHom D D) (ScottHom D D) :=
  ⟨fun p => comp M.pairH (prodMkHom p.1 p.2), scottContinuous_of_pointwise fun a =>
    ScottContinuous.comp
      (ScottContinuous.prodMk
        (ScottContinuous.comp ScottContinuous.fst (evalHom a).scottContinuous)
        (ScottContinuous.comp ScottContinuous.snd (evalHom a).scottContinuous))
      M.pairH.scottContinuous⟩

@[simp] theorem pairHomH_apply (f g : ScottHom D D) (a : D) :
    pairHomH M (f, g) a = M.pairH (f a, g a) := rfl

/-- The tuple of the `m` slots starting at index `j`, terminated by `⊥`, as a
bundled map of `ψ`. The paper terminates with `K`; nothing reads past the last
slot, so `⊥` serves and keeps `S` and `K` out of `ψ`. -/
noncomputable def tailHom : ℕ → ℕ → ScottHom (ScottHom D D) (ScottHom D D)
  | _, 0 => ScottHom.const (ScottHom.const ⊥)
  | j, m + 1 =>
    if h : j < n then
      comp (pairHomH M) (prodMkHom (slotHom M s o ⟨j, h⟩) (tailHom (j + 1) m))
    else ScottHom.const (ScottHom.const ⊥)

theorem tailHom_succ {j : ℕ} (h : j < n) (m : ℕ) (ψ : ScottHom D D) (a : D) :
    tailHom M s o j (m + 1) ψ a =
      M.pairH (slotHom M s o ⟨j, h⟩ ψ a, tailHom M s o (j + 1) m ψ a) := by
  rw [tailHom, dif_pos h]
  rfl

/-- **The fixed-point functional of the paper's displayed equation.**
`Θ ψ = fun a => pair a (tuple of slots at a)`. Every constituent is a bundled map,
so `Θ` is a `ScottHom` on `D → D` and the Fixed Point Theorem applies to it. -/
noncomputable def bigTheta : ScottHom (ScottHom D D) (ScottHom D D) :=
  comp (pairHomH M) (prodMkHom (ScottHom.const ScottHom.id) (tailHom M s o 0 n))

@[simp] theorem bigTheta_apply (ψ : ScottHom D D) (a : D) :
    bigTheta M s o ψ a = M.pairH (a, tailHom M s o 0 n ψ a) := rfl

/-- **`ψ`**, the least solution of the paper's fixed-point equation, by the Fixed
Point Theorem (`kleeneFix`) in the cpo `D → D`. -/
noncomputable def psi : ScottHom D D := kleeneFix ⇑(bigTheta M s o)

theorem psi_eq : bigTheta M s o (psi M s o) = psi M s o :=
  map_kleeneFix (bigTheta M s o).scottContinuous

/-- The first component of `ψ a` is `a` — the paper's reason for pairing `a` in. -/
theorem fst_psi (a : D) : M.fstH (psi M s o a) = a := by
  conv_lhs => rw [← psi_eq M s o]
  rw [bigTheta_apply, M.fst_pair]

/-- `ψ` is injective, which is what "isomorphic to a subalgebra" needs. -/
theorem psi_injective : Function.Injective ⇑(psi M s o) := by
  intro x y h
  rw [← fst_psi M s o x, ← fst_psi M s o y, h]

/-- The second component of `ψ a` is the whole tuple of slots. -/
theorem snd_psi (a : D) : M.sndH (psi M s o a) = tailHom M s o 0 n (psi M s o) a := by
  conv_lhs => rw [← psi_eq M s o]
  rw [bigTheta_apply, M.snd_pair]

/-- Applying `snd` `i` times to the tuple starting at `j` walks `i` slots along. -/
theorem sndIter_tailHom (ψ : ScottHom D D) (a : D) (i : ℕ) :
    ∀ (j m : ℕ), j + i ≤ n →
      (⇑M.sndH)^[i] (tailHom M s o j (i + m) ψ a) = tailHom M s o (j + i) m ψ a := by
  induction i with
  | zero => intro j m _; simp
  | succ i ih =>
    intro j m hjm
    have hj : j < n := by omega
    rw [show i + 1 + m = (i + m) + 1 from by omega, Function.iterate_succ_apply,
      tailHom_succ M s o hj, M.snd_pair, ih (j + 1) m (by omega),
      show j + 1 + i = j + (i + 1) from by omega]

/-- Reading the `i`-th slot: `fst (snd^{i+1} (ψ a))` is exactly the `i`-th slot at
`a`. This is the paper's `Fᵢ(ψ(a₁))`. -/
theorem fst_sndIter_psi (i : Fin n) (a : D) :
    M.fstH ((⇑M.sndH)^[i.val + 1] (psi M s o a)) = slotHom M s o i (psi M s o) a := by
  obtain ⟨m, hm⟩ : ∃ m, n - i.val = m + 1 := ⟨n - i.val - 1, by omega⟩
  have hn : i.val + (m + 1) = n := by omega
  rw [Function.iterate_succ_apply, snd_psi]
  rw [show tailHom M s o 0 n (psi M s o) a
      = tailHom M s o 0 (i.val + (m + 1)) (psi M s o) a by rw [hn]]
  rw [sndIter_tailHom M s o (psi M s o) a i.val 0 (m + 1) (by omega),
    Nat.zero_add, tailHom_succ M s o i.isLt, M.fst_pair]

end Construction

/-! ## Theorem 26 -/

section Theorem26

variable {D : Type u} [CompletePartialOrder D] (M : LambdaModel D)

open LambdaModel Construction

/-- `Fᵢ` acts as `λx. fst(snd^{i}(x))`, and it is a **combination** — a
variable-free term over `S`, `K`, `fst`, `snd`. This is the paper's "which have to
be rewritten in terms of `S`, `K`, `fst`, and `snd`", discharged by `bComb`. -/
theorem app_combEval_fstSndPowComb (k : ℕ) :
    ∀ x : D, M.app (M.combEval (fstSndPowComb k)) x = M.fstH ((⇑M.sndH)^[k] x) := by
  induction k with
  | zero => intro x; rw [fstSndPowComb, combEval_fstC_apply, Function.iterate_zero_apply]
  | succ k ih =>
    intro x
    rw [fstSndPowComb, combEval_ap, combEval_ap, bComb_apply, combEval_sndC_apply, ih,
      Function.iterate_succ_apply]

/-- **Theorem 26.** Given a signature `(s₁, …, s_n)` of positive arities, there are
combinations `F₁, …, F_n` — depending on the signature and on `D`'s applicative
structure alone — such that for *every* family of operations `o₁, …, o_n` on `D` of
those arities there is a continuous injection `ψ : D → D` with

`Fᵢ ⬝ ψ(a₁) ⬝ ⋯ ⬝ ψ(a_{sᵢ}) = ψ(oᵢ ⬝ a₁ ⬝ ⋯ ⬝ a_{sᵢ})`.

The paper's displayed calculation, verbatim. `ψ` is the least fixed point of the
paper's displayed equation (`Construction.psi`), taken by the Fixed Point Theorem
in the cpo `D → D`; injectivity is `fst(ψ(a)) = a`, which is why the paper pairs
`a` into the first component.

Hypotheses: a `LambdaModel` on `D` — that is, `D ≅ D → D` and `D ≅ D × D`, which
is exactly what **Theorem 25** delivers — and `0 < sᵢ`. See the module docstring
for why the positivity is a correction to the paper rather than a convenience. -/
theorem thm26 {n : ℕ} (s : Fin n → ℕ) (hs : ∀ i, 0 < s i) :
    ∃ F : Fin n → Comb, ∀ o : Fin n → D, ∃ ψ : ScottHom D D,
      Function.Injective ⇑ψ ∧ (∀ a, M.fstH (ψ a) = a) ∧
      ∀ (i : Fin n) (l : List D), l.length = s i →
        M.iterApp (M.combEval (F i)) (l.map ⇑ψ) = ψ (M.iterApp (o i) l) := by
  refine ⟨fun i => fstSndPowComb (i.val + 1), fun o =>
    ⟨psi M s o, psi_injective M s o, fst_psi M s o, ?_⟩⟩
  rintro i (_ | ⟨a, l⟩) hl
  · simp only [List.length_nil] at hl
    exact absurd (hs i) (by omega)
  · have hlen : l.length = s i - 1 := by simp only [List.length_cons] at hl; omega
    rw [List.map_cons, iterApp_cons, app_combEval_fstSndPowComb,
      fst_sndIter_psi, slotHom_apply, iterApp_cons]
    exact iterApp_WHom M (fst_psi M s o) (s i - 1) (M.app (o i) a) l hlen

/-- **Theorem 26, subalgebra form.** If a subset `A ⊆ D` is closed under the
operations `o₁, …, o_n`, then `ψ` is injective on `A` and `ψ '' A` is closed under
the fixed operations `F₁, …, F_n` — i.e. `A` is isomorphic to a subalgebra of
`⟨D, F₁, …, F_n⟩`, which is the sentence Theorem 26 states. -/
theorem thm26_subalgebra {n : ℕ} (s : Fin n → ℕ) (hs : ∀ i, 0 < s i) :
    ∃ F : Fin n → Comb, ∀ (A : Set D) (o : Fin n → D),
      (∀ (i : Fin n) (l : List D), l.length = s i → (∀ b ∈ l, b ∈ A) →
        M.iterApp (o i) l ∈ A) →
      ∃ ψ : ScottHom D D, Set.InjOn ⇑ψ A ∧
        ∀ (i : Fin n) (l : List D), l.length = s i → (∀ b ∈ l, b ∈ A) →
          M.iterApp (M.combEval (F i)) (l.map ⇑ψ) ∈ ⇑ψ '' A := by
  obtain ⟨F, hF⟩ := thm26 M s hs
  refine ⟨F, fun A o hA => ?_⟩
  obtain ⟨ψ, hinj, _, heq⟩ := hF o
  exact ⟨ψ, hinj.injOn, fun i l hl hlA => ⟨M.iterApp (o i) l, hA i l hl hlA, (heq i l hl).symm⟩⟩

/-- **Theorem 26 at a retract.** `A` a retract of `D` — the paper's hypothesis —
with operations induced from `D`'s. `φ = ψ ∘ e` is injective and carries the
induced operation `p ∘ oᵢ ∘ e^{s_i}` to `Fᵢ`, which is the isomorphism onto a
subalgebra the theorem asserts. -/
theorem thm26_retract {n : ℕ} (s : Fin n → ℕ) (hs : ∀ i, 0 < s i)
    {A : Type u} [CompletePartialOrder A] (e : ScottHom A D) (p : ScottHom D A)
    (hpe : ∀ a, p (e a) = a) (o : Fin n → D)
    (hclosed : ∀ (i : Fin n) (l : List D), l.length = s i → (∀ b ∈ l, b ∈ Set.range ⇑e) →
      M.iterApp (o i) l ∈ Set.range ⇑e) :
    ∃ (F : Fin n → Comb) (φ : A → D), Function.Injective φ ∧
      ∀ (i : Fin n) (l : List A), l.length = s i →
        M.iterApp (M.combEval (F i)) (l.map φ) = φ (p (M.iterApp (o i) (l.map ⇑e))) := by
  obtain ⟨F, hF⟩ := thm26 M s hs
  obtain ⟨ψ, hinj, _, heq⟩ := hF o
  have hein : Function.Injective ⇑e := fun x y h => by rw [← hpe x, ← hpe y, h]
  refine ⟨F, fun a => ψ (e a), hinj.comp hein, fun i l hl => ?_⟩
  have hmem : M.iterApp (o i) (l.map ⇑e) ∈ Set.range ⇑e := by
    refine hclosed i (l.map ⇑e) (by simpa using hl) ?_
    intro b hb
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hb
    exact ⟨c, rfl⟩
  obtain ⟨c, hc⟩ := hmem
  have hmap : List.map (fun a => ψ (e a)) l = List.map ⇑ψ (List.map ⇑e l) := by
    rw [List.map_map]; rfl
  rw [hmap, heq i (l.map ⇑e) (by simpa using hl)]
  show ψ (M.iterApp (o i) (List.map ⇑e l)) = ψ (e (p (M.iterApp (o i) (List.map ⇑e l))))
  rw [← hc, hpe c]

end Theorem26

/-! ## Theorem 26 over the domain Theorem 25 produces -/

/-- **Theorem 25 supplies the hypothesis of Theorem 26.** There is a non-trivial
cpo `D`, the image of a closure on `P N`, carrying an applicative structure; hence
Theorem 26 holds over it for every signature of positive arities.

This is the sentence §7.2 opens with — "our λ-calculus model can be considered as a
continuous algebra of signature (2,0,0,0,0,0)" — with `D` the model Theorem 25
constructs. -/
theorem exists_lambdaModel_of_thm25 :
    ∃ (D : Cpo.{0}) (_ : LambdaModel D.carrier), Nontrivial D.carrier ∧
      Recursive.IsClosureOf D Recursive.powersetCpo := by
  obtain ⟨D, hnt, hcl, ⟨q⟩, ⟨e⟩⟩ := thm25_powerset
  exact ⟨D, LambdaModel.ofOrderIso e q, hnt, hcl⟩

end ScottDomains.Combinator
