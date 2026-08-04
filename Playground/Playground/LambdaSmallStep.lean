import Mathlib.Tactic
import Mathlib.Logic.Relation

/-!
# Full-β small-step semantics for the untyped λ-calculus (de Bruijn)

Terms use **de Bruijn indices**: a bound variable is a natural number counting the
number of `lam` binders between its occurrence and the `lam` that binds it. This
makes **α-conversion definitional** — α-equivalent terms have *identical*
representations, so `λx.x` and `λy.y` are literally the same `Term` (see the α
examples). That is the whole reason to pay the index bookkeeping cost.

The reduction relation `Step` (`↝`) is **full β**: a redex may be contracted in
*any* position, including under a `lam`. This is the relation whose conversion
equals the denotation given by a cartesian closed category (Lambek–Scott): the
categorical interpretation is invariant under β anywhere, so only a *full* β
relation can line up with it. We include η as well, giving the **βη** theory that
CCCs model exactly:

* the `beta` rule is the operational shadow of the CCC equation
  `ev ∘ ⟨curry f, 𝟙⟩ = f` (the exponential counit / computation rule);
* the `eta` rule is the shadow of the *uniqueness* of `curry` (the unit).

See `Playground/CartesianClosed.lean` for the categorical side.
-/

namespace Playground.Lambda

/-- Untyped λ-terms with de Bruijn indices. -/
inductive Term where
  | var (n : Nat) : Term
  | app (f a : Term) : Term
  | lam (b : Term) : Term
  deriving DecidableEq, Repr

namespace Term

/-- `lift d c t` shifts every **free** variable of `t` (index `≥` cutoff `c`) up by
`d`. Free variables are those not captured by a `lam` inside `t`; the cutoff rises
by one under each binder. -/
def lift (d c : Nat) : Term → Term
  | var k => if k < c then var k else var (k + d)
  | app f a => app (lift d c f) (lift d c a)
  | lam b => lam (lift d (c + 1) b)

/-- `subst t j s` is `t[j := s]`: replace variable `j` by `s`, and **decrement**
every free variable above `j` (removing the binder that `j` referred to). Going
under a binder shifts the index to `j+1` and lifts `s` to keep its free variables
correct. Single-variable β-substitution is `subst b 0 a`. -/
def subst : Term → Nat → Term → Term
  | var k,   j, s => if k < j then var k else if k = j then s else var (k - 1)
  | app f a, j, s => app (subst f j s) (subst a j s)
  | lam b,   j, s => lam (subst b (j + 1) (lift 1 0 s))

end Term

open Term

/-- **Full-β (with η) small-step reduction**, `t ↝ t'`.

* `beta`  — contract a redex: `(λ b) a ↝ b[0 := a]`.
* `eta`   — η-contract: `λ (f⁺ · 0) ↝ f`, where `f⁺ = lift 1 0 f` (so the bound
            variable cannot occur free in `f`, discharging the usual side condition).
* `appL`, `appR`, `lam` — congruence rules letting a step happen in **any**
            position, *including under a `lam`* (`lam`). That last rule is what
            makes this *full* β rather than a weak/left-to-right strategy. -/
inductive Step : Term → Term → Prop where
  | beta (b a : Term)            : Step (app (lam b) a) (subst b 0 a)
  | eta  (f : Term)              : Step (lam (app (lift 1 0 f) (var 0))) f
  | appL {f f' : Term} (a : Term) : Step f f' → Step (app f a) (app f' a)
  | appR (f : Term) {a a' : Term} : Step a a' → Step (app f a) (app f a')
  | lam  {b b' : Term}            : Step b b' → Step (lam b) (lam b')

@[inherit_doc] scoped infixr:50 " ↝ " => Step

/-- Many-step reduction: the reflexive–transitive closure of `↝`. -/
abbrev MultiStep : Term → Term → Prop := Relation.ReflTransGen Step

@[inherit_doc] scoped infixr:50 " ↝* " => MultiStep

/-! ## Standard combinators -/

/-- Identity `I = λx. x`. -/
def I : Term := lam (var 0)
/-- `K = λx. λy. x` (the constant-function combinator; de Bruijn `var 1` is the outer `x`). -/
def K : Term := lam (lam (var 1))
/-- `S = λx. λy. λz. (x z) (y z)`. -/
def S : Term := lam (lam (lam (app (app (var 2) (var 0)) (app (var 1) (var 0)))))
/-- `Δ = λx. x x` (self-application). -/
def Δ : Term := lam (app (var 0) (var 0))
/-- `Ω = Δ Δ`, the canonical non-terminating term. -/
def Ω : Term := app Δ Δ

/-! ## β-reduction -/

/-- **β**: `I t ↝ t`. The redex `(λ 0) t` contracts to `0[0 := t] = t`. -/
example (t : Term) : app I t ↝ t := by
  simpa [I, subst] using Step.beta (var 0) t

/-- **β under a binder** (this is what "full β" buys): `λ (I 0) ↝ λ 0`. A
left-to-right / call-by-value strategy could *not* take this step. -/
example : lam (app I (var 0)) ↝ lam (var 0) := by
  simpa [I, subst] using Step.lam (Step.beta (var 0) (var 0))

/-- **β can loop**: `Ω ↝ Ω`. Contracting `Δ Δ` reproduces `Δ Δ`, so there is no
normal form — β-reduction need not terminate. -/
example : Ω ↝ Ω := by
  simpa [Ω, Δ, subst] using Step.beta (app (var 0) (var 0)) Δ

/-! ## α-conversion -/

-- In de Bruijn form there is **no α rule**: α-equivalent terms are *equal*.
-- The named terms `λx. x` and `λy. y` both encode to `lam (var 0)`, and
-- `λx. λy. x y` and `λa. λb. a b` both encode to `lam (lam (app (var 1) (var 0)))`.
-- So α-conversion is discharged by `rfl`.

/-- **α**: `λx.x` and `λy.y` are the *same* de Bruijn term. -/
example : (lam (var 0) : Term) = lam (var 0) := rfl

/-- **α**: two α-variants of `λf.λx. f x` are equal, because names are erased. -/
example : (lam (lam (app (var 1) (var 0))) : Term) = lam (lam (app (var 1) (var 0))) := rfl

/-! ## η-reduction -/

/-- **η** (general): `λ (f⁺ · 0) ↝ f`. The lift of `f` guarantees the bound
variable `0` does not occur free in `f`, which is exactly the η side condition. -/
example (f : Term) : lam (app (lift 1 0 f) (var 0)) ↝ f := Step.eta f

/-- **η** (concrete): `λ. (1 0) ↝ 0`, i.e. `λx. y x ↝ y`. Here `lift 1 0 (var 0) = var 1`. -/
example : lam (app (var 1) (var 0)) ↝ var 0 := by
  simpa [lift] using Step.eta (var 0)

/-! ## Many-step reduction -/

/-- Two β-steps: `I (I t) ↝* t`. -/
example (t : Term) : app I (app I t) ↝* t := by
  have s1 : app I (app I t) ↝ app I t := by
    simpa [I, subst] using Step.beta (var 0) (app I t)
  have s2 : app I t ↝ t := by
    simpa [I, subst] using Step.beta (var 0) t
  exact (Relation.ReflTransGen.single s1).tail s2

/-- `K` discards its (divergent) second argument: `K I Ω ↝* I`. -/
example : app (app K I) Ω ↝* I := by
  have s1 : app (app K I) Ω ↝ app (lam I) Ω := by
    simpa [K, I, subst, lift] using Step.appL Ω (Step.beta (lam (var 1)) I)
  have s2 : app (lam I) Ω ↝ I := by
    simpa [I, subst, lift] using Step.beta I Ω
  exact (Relation.ReflTransGen.single s1).tail s2

end Playground.Lambda
