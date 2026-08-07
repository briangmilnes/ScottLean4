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
> > `F₁ = λx. fst(snd(x))`
> > `F₂ = λx. fst(snd(snd(x)))`
> > `      ⋮`
> > `F_n = λx. fst(snd(snd(⋯snd(x))))`,
>
> which have to be rewritten in terms of `S`, `K`, `fst`, and `snd`. We then
> calculate that
>
> > `Fᵢ(ψ(a₁))(ψ(a₂))⋯(ψ(a_{sᵢ})) = ψ(oᵢ(a₁, a₂, …, a_{sᵢ}))`.

This file is that proof. `thm26` is the displayed calculation, `thm26_subalgebra`
its reading as "`A` is isomorphic to a subalgebra", and `lambdaModel_of_thm25`
connects the hypothesis to Theorem 25, which is where the paper's `D` comes from.

## Where `D` comes from

`D` is the λ-calculus model of §7.2: a cpo with `D ≅ D → D` and `D ≅ D × D`.
`Universality.thm25` produces exactly that, so `LambdaModel` — the applicative
structure the proof consumes — is derived from a pair of order isomorphisms and
nothing else. `lambdaModel_of_orderIso` is the derivation and
`exists_lambdaModel_of_thm25` is Theorem 25 feeding it.

## Two design decisions, and the reason for each

**The signature is indexed by `Fin n` with arities in `ℕ`.** The paper writes
`(s₁, s₂, …, s_n)`, a finite *sequence*: the operations are ordered, and the proof
uses the order — `Fᵢ` reads the `i`-th slot of a right-nested tuple by applying
`snd` exactly `i` times, so the index must carry a position, not merely an
identity. `Fin n → ℕ` is that sequence. A general finite index type `ι` with
`[Fintype ι]` would carry an identity but not a position, and every use would have
to choose an enumeration of `ι` — reintroducing `Fin n` with an extra layer. The
rest of §7 reuses `Fin n → ℕ` for the same reason.

**Arities are required positive** (`hs : ∀ i, 0 < s i`), and this is a correction
to the paper, not a convenience. The paper explicitly admits `0` in a signature
("here, `0` indicates a 0-ary operation, which is just a constant", of the
signature `(2,0,0,0,0,0)`), but **Theorem 26 is false for any signature containing
`0`**, by the following argument, which is stated here and is not Lean-checked.
Suppose `sᵢ = 0`. `Fᵢ` is one fixed element of `D`; a subalgebra of `⟨D, …, Fᵢ, …⟩`
contains `Fᵢ` and has `Fᵢ` as its own `i`-th constant, so an isomorphism of `A`
onto a subalgebra must send `A`'s constant `oᵢ` to `Fᵢ`. Take two one-point
algebras `A = {a}` and `B = {b}` with `a ≠ b`, both retracts of `D` (one-point
subsets of a nontrivial `D` are retracts), with constants `oᵢ = a` and `oᵢ = b`.
Both embeddings must hit the same `Fᵢ`, and the paper's own `ψ` satisfies
`fst(ψ(x)) = x`, so `a = fst(Fᵢ) = b` — a contradiction. The paper's construction
also breaks down before this: its `Fᵢ` reads a slot *out of an argument*, and a
0-ary operation supplies no argument to read it out of.

## The interior of the tuple

The paper terminates the right-nested tuple with the combination `K`. Nothing
reads past the last slot, so any element of `D` serves; `⊥` is used here, which
removes `K` and `S` from the data that `ψ` depends on. They are still needed for
`Fᵢ` itself, which the paper requires to be a **combination** — see `Comb` and
`combEval` below, where `Fᵢ` is exhibited as an explicit variable-free term over
`S`, `K`, `fst`, `snd`.

## Operations as elements of `D`

An `m`-ary continuous operation on `D` is taken to be an element `o : D` acting by
`x₁, …, x_m ↦ o ⬝ x₁ ⬝ ⋯ ⬝ x_m` (`iterApp`). This is not a restriction: `D ≅ D → D`
makes `D` a reflexive object, so `lam` turns any continuous `D → D` into an
element, and `ScottHom.curry` turns any jointly continuous `D × D → D` into a
continuous `D → (D → D)` and hence into an element — `elem_of_hom₁` and
`elem_of_hom₂` record the two arities the file uses. The paper works in the same
notation: its `oᵢ(a, fst(x₂), …)` is applicative, not a Lean function.
-/

namespace ScottDomains.Combinator

open ScottDomains.Universality

universe u

/-! ## Toolkit: bundled composition and continuity into a function space

Every continuity obligation of the construction below is discharged by exhibiting
a map as a composite of bundled `ScottHom`s. These are the pieces. -/

section Toolkit

variable {α β γ : Type*}

/-- Composition of bundled Scott-continuous maps. The development has
`ScottContinuous.comp` but no bundled composition; the fixed-point functional
below is built entirely out of composites, so it is worth naming. -/
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
lemma that makes every "λ inside a fixed point" below cost nothing. -/
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

/-- Post-composition by a fixed map, bundled: `f ↦ h ∘ f`. -/
def postHom [Preorder α] [CompletePartialOrder β] [CompletePartialOrder γ]
    (h : ScottHom β γ) : ScottHom (ScottHom α β) (ScottHom α γ) :=
  ⟨fun f => comp h f, scottContinuous_of_pointwise fun y =>
    (comp h (evalHom (β := β) y)).scottContinuous⟩

@[simp] theorem postHom_apply [Preorder α] [CompletePartialOrder β] [CompletePartialOrder γ]
    (h : ScottHom β γ) (f : ScottHom α β) : postHom h f = comp h f := rfl

/-- Pre-composition by a fixed map, bundled: `f ↦ f ∘ h`. -/
def preHom [Preorder α] [Preorder β] [CompletePartialOrder γ]
    (h : ScottHom α β) : ScottHom (ScottHom β γ) (ScottHom α γ) :=
  ⟨fun f => comp f h, scottContinuous_of_pointwise fun y => (evalHom (h y)).scottContinuous⟩

@[simp] theorem preHom_apply [Preorder α] [Preorder β] [CompletePartialOrder γ]
    (h : ScottHom α β) (f : ScottHom β γ) : preHom h f = comp f h := rfl

end Toolkit

/-! ## The λ-calculus model

The applicative structure §7.2 works in: application, abstraction with the β-law,
and a pairing with its two projections. -/

/-- **The applicative structure of §7.2.** `app` and `lam` are the two halves of
`D ≅ D → D` and `app_lam` is the β-law; `pairH`, `fstH`, `sndH` are the three
halves of `D ≅ D × D`. Nothing else about `D` is used anywhere below. -/
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

/-- The applicative structure carried by any cpo with `D ≅ D → D` and
`D ≅ D × D`. An order isomorphism between cpos is Scott continuous
(`Universality.scottContinuous_orderIso`), so no further hypothesis is needed. -/
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

/-- Iterated application, `f ⬝ x₁ ⬝ ⋯ ⬝ x_k`. The paper's `F(x₁)(x₂)⋯(x_n)`. -/
def iterApp : D → List D → D
  | f, [] => f
  | f, x :: xs => iterApp (M.app f x) xs

@[simp] theorem iterApp_nil (f : D) : M.iterApp f [] = f := rfl

@[simp] theorem iterApp_cons (f x : D) (xs : List D) :
    M.iterApp f (x :: xs) = M.iterApp (M.app f x) xs := rfl

/-- Every continuous `D → D` is an element of `D`, by `lam`. -/
theorem elem_of_hom₁ (f : ScottHom D D) : ∃ o : D, ∀ x, M.iterApp o [x] = f x :=
  ⟨M.lam f, fun x => by simp [M.app_lam]⟩

/-- Every jointly continuous `D × D → D` is an element of `D`, by `ScottHom.curry`
followed by `lam` twice. This is why taking operations to be elements of `D`
costs no generality. -/
theorem elem_of_hom₂ (f : ScottHom (D × D) D) :
    ∃ o : D, ∀ x y, M.iterApp o [x, y] = f (x, y) := by
  refine ⟨M.lam (comp M.lam (ScottHom.curry f)), fun x y => ?_⟩
  simp only [iterApp_cons, iterApp_nil, M.app_lam, comp_apply]
  rw [M.app_lam]
  rfl

end LambdaModel

/-! ## Combinations

> We will call an expression in the notation of applicative algebra which has no
> variables a **combination**.

`Comb` is that notion of expression and `combEval` its interpretation in a
`LambdaModel`. `Fᵢ` is exhibited below as an explicit `Comb`, which is the part of
Theorem 26's statement that "combination" carries: `Fᵢ` depends on the signature
and on `D`'s applicative structure, and on nothing about the algebra `A`. -/

/-- A variable-free expression over `S`, `K`, `fst`, `snd` and application. -/
inductive Comb : Type
  | S : Comb
  | K : Comb
  | fstC : Comb
  | sndC : Comb
  | ap : Comb → Comb → Comb

namespace LambdaModel

variable {D : Type u} [CompletePartialOrder D] (M : LambdaModel D)

/-- `K = λx. λy. x`, as an element. -/
noncomputable def kElem : D :=
  M.lam ⟨fun x => M.lam (ScottHom.const x), scottContinuous_of_pointwise
    (fun _ => M.lam.scottContinuous.comp' (by
      exact scottContinuous_of_pointwise fun _ => ScottContinuous.id))⟩

/-- `S = λx. λy. λz. x z (y z)`, as an element. -/
noncomputable def sElem : D :=
  M.lam ⟨fun x => M.lam ⟨fun y => M.lam
      ⟨fun z => M.app (M.app x z) (M.app y z), by
        exact ScottContinuous.comp
          (ScottContinuous.prodMk (M.app x).scottContinuous (M.app y).scottContinuous)
          (ScottHom.uncurry M.app).scottContinuous⟩,
      by
        refine ScottContinuous.comp (scottContinuous_of_pointwise fun z => ?_)
          M.lam.scottContinuous
        exact ScottContinuous.comp
          (ScottContinuous.prodMk (ScottContinuous.const _)
            (ScottContinuous.comp (evalHom z).scottContinuous
              (ScottContinuous.comp M.app.scottContinuous ScottContinuous.id)))
          (ScottHom.uncurry M.app).scottContinuous⟩,
    by
      refine ScottContinuous.comp (scottContinuous_of_pointwise fun y => ?_)
        M.lam.scottContinuous
      refine ScottContinuous.comp (scottContinuous_of_pointwise fun z => ?_)
        M.lam.scottContinuous
      exact ScottContinuous.comp
        (ScottContinuous.prodMk
          (ScottContinuous.comp (ScottContinuous.comp M.app.scottContinuous
            (evalHom z).scottContinuous) ScottContinuous.id)
          (ScottContinuous.const _))
        (ScottHom.uncurry M.app).scottContinuous⟩

/-- The interpretation of a combination. -/
noncomputable def combEval : Comb → D
  | .S => M.sElem
  | .K => M.kElem
  | .fstC => M.lam M.fstH
  | .sndC => M.lam M.sndH
  | .ap c₁ c₂ => M.app (M.combEval c₁) (M.combEval c₂)

@[simp] theorem kElem_apply (x y : D) : M.app (M.app M.kElem x) y = x := by
  simp [kElem, M.app_lam]

@[simp] theorem sElem_apply (x y z : D) :
    M.app (M.app (M.app M.sElem x) y) z = M.app (M.app x z) (M.app y z) := by
  simp [sElem, M.app_lam]

/-- `B = S (K S) K`, the composition combinator: `B f g x = f (g x)`. -/
def bComb : Comb := .ap (.ap .S (.ap .K .S)) .K

@[simp] theorem bComb_apply (f g x : D) :
    M.app (M.app (M.app (M.combEval bComb) f) g) x = M.app f (M.app g x) := by
  simp [bComb, combEval]

end LambdaModel

/-! ## The construction

Everything below is parameterized by a `LambdaModel M` on `D`, a signature
`s : Fin n → ℕ` with positive arities, and a family `o : Fin n → D` of operations.
-/

namespace Construction

variable {D : Type u} [CompletePartialOrder D] (M : LambdaModel D)

/-! ### `W ψ k`, the `k`-fold abstraction

`W ψ k c` is the paper's `λx₂…x_{k+1}. ψ(c (fst x₂) ⋯ (fst x_{k+1}))`. It is built
so that `ψ ↦ W ψ k` is itself a bundled `ScottHom`, which is what the fixed point
of the whole system needs. -/

/-- `ψ ↦ (c ↦ λx. W ψ k c (fst x))`, as a bundled map. `WHom 0` is the identity
and each step is a composite of `lam`, pre- and post-composition, and `app`. -/
noncomputable def WHom : ℕ → ScottHom (ScottHom D D) (ScottHom D D)
  | 0 => ScottHom.id
  | k + 1 =>
    comp (postHom M.lam)
      (comp (preHom (comp (preHom M.fstH) M.app))
        (comp (postHom (α := ScottHom D D) (β := D) (γ := D)
          |>.toFun ∘ id) (WHom k)))

end Construction

end ScottDomains.Combinator
