import ScottDomains.EffectivePresentation
-- `REPred`, the recursively enumerable predicates: the notion §3.2 needs and the
-- one `EffectivePresentation.lean` recorded as missing from Mathlib. It is
-- present; the grep that missed it searched for `RePred`.
import Mathlib.Computability.RE

/-!
# §3.2: computable functions between effectively presented domains

Gunter & Scott, *Semantic Domains*, §3.2, the sentence immediately after the
definition of an effective presentation:

> If `⟨D, d⟩` and `⟨E, e⟩` are effectively presented domains, then a continuous
> function `f : D → E` is said to be **computable** (with respect to `d` and `e`)
> if and only if, for every `n ∈ ℕ`, the set `{m | eₘ ⊑ f(dₙ)}` is recursively
> enumerable.

This is the definition `EffectivePresentation.lean` left out. Its stated reason —
"this Mathlib (v4.32.2) has no `RePred` or equivalent" — was wrong about the
spelling: `Mathlib/Computability/RE.lean` defines

    def REPred {α} [Primcodable α] (p : α → Prop) :=
      Partrec fun a => Part.assert (p a) fun _ => Part.some ()

"`p` is the domain of a partial recursive function", which is the standard
characterization of a recursively enumerable predicate and is what the paper's
"recursively enumerable" means. The predicate here lives on `ℕ` (the index `m`),
so the only `Primcodable` instance needed is the one on `ℕ`; nothing has to be
encoded on `K(D)` itself. That is the point of a presentation — it moves
recursion-theoretic questions onto the index set.

## Continuity

`f` is a `ScottHom α β`, so continuity is carried by the type: every `f` for
which `IsComputable d e f` is even stateable is continuous, by
`ScottHom.scottContinuous`. The paper's "a continuous function `f : D → E` is
said to be computable" is therefore rendered without a side condition.

## The paper's quantifier is non-uniform, and that is load-bearing

The definition quantifies `n` *outside* the r.e. claim: for each `n` separately,
`{m | eₘ ⊑ f(dₙ)}` is r.e. It does not ask that an index for that r.e. set be
computable from `n`. `IsComputable` is that literal statement.
`IsUniformlyComputable` is the stronger, uniform reading — the single relation
`{(n, m) | eₘ ⊑ f(dₙ)}` is r.e. — which is what the surrounding literature
usually means and what every closure property below actually needs.
`IsUniformlyComputable.isComputable` proves the implication; the converse is
false in general and is not claimed here.

## What "effectively decidable" has to mean for any of this to be provable

`EffectivePresentation.decidableLE` renders the paper's condition 1 as a Lean
`DecidablePred` instance: a program that decides the ordering. That is not the
same claim as Mathlib's `ComputablePred`, which additionally ties the decision
procedure to `Nat.Partrec`, and there is no route from the first to the second —
a `Decidable` instance may be `Classical.dec`. So no computability theorem here
follows from `EffectivePresentation` alone. `RecursiveLE` is the recursion-
theoretic reading of condition 1, taken as an explicit hypothesis wherever it is
needed. Strengthening `EffectivePresentation` itself is a change to a shared
module and is left to the orchestrator.

## Closure under composition, and why it is absent

If `f : D → E` and `g : E → F` are computable then, expanding `g(f(dₙ))` as the
directed supremum of `{g(eₘ) | eₘ ⊑ f(dₙ)}`,

    c_k ⊑ g(f(dₙ))  ↔  ∃ m, eₘ ⊑ f(dₙ) ∧ c_k ⊑ g(eₘ),

so composition needs r.e. predicates to be closed under conjunction and under
existential quantification over `ℕ`. Mathlib v4.32.2's `REPred` API is five
lemmas — `of_eq`, `Partrec.dom_re`, `ComputablePred.to_re`,
`computable_iff_re_compl_re`, `computable_iff_re_compl_re'` — and has neither.
Conjunction is a short `Partrec.bind`; the projection theorem is a dovetailing
argument over `Nat.Partrec.Code.evaln` and is recursion theory, not domain
theory. Composition is therefore stated nowhere below rather than assumed.
-/

namespace ScottDomains.Computable

variable {α β : Type*} [CompletePartialOrder α] [Domain α]
  [CompletePartialOrder β] [Domain β]

/-- Recursive enumerability is preserved by precomposition with a computable
function: if `p` is r.e. and `g` is computable then `p ∘ g` is r.e.

This is `Partrec.comp` read through the definition of `REPred`: `p ∘ g` is the
domain of `(fun a => Part.assert (p a) …) ∘ g`. Mathlib does not state it, and
both substitution steps below are instances of it. -/
theorem rePred_comp {σ τ : Type*} [Primcodable σ] [Primcodable τ] {p : τ → Prop}
    (hp : REPred p) {g : σ → τ} (hg : Computable g) : REPred fun a => p (g a) :=
  Partrec.comp hp hg

/-- The paper's **computable function**, verbatim: `f` is computable with respect
to `d` and `e` if and only if, for every `n`, the set `{m | eₘ ⊑ f(dₙ)}` is
recursively enumerable. -/
def IsComputable (d : EffectivePresentation α) (e : EffectivePresentation β)
    (f : ScottHom α β) : Prop :=
  ∀ n : ℕ, REPred fun m : ℕ => e.enum m ≤ f (d.enum n)

/-- The uniform strengthening: the single relation `{(n, m) | eₘ ⊑ f(dₙ)}` is
recursively enumerable, with `n` inside the r.e. claim rather than outside it.
This is not the paper's wording — see the module docstring. -/
def IsUniformlyComputable (d : EffectivePresentation α)
    (e : EffectivePresentation β) (f : ScottHom α β) : Prop :=
  REPred fun p : ℕ × ℕ => e.enum p.2 ≤ f (d.enum p.1)

/-- The recursion-theoretic reading of condition 1 of an effective presentation:
the ordering on the basis, read off the indices, is a *computable* predicate in
the sense of `Mathlib/Computability/RE.lean` — not merely `Decidable`. -/
def RecursiveLE (d : EffectivePresentation α) : Prop :=
  ComputablePred fun p : ℕ × ℕ => d.enum p.1 ≤ d.enum p.2

/-- The uniform reading implies the paper's. Fixing `n` is precomposition with
the computable map `m ↦ (n, m)`, so `rePred_comp` applies. -/
theorem IsUniformlyComputable.isComputable {d : EffectivePresentation α}
    {e : EffectivePresentation β} {f : ScottHom α β}
    (h : IsUniformlyComputable d e f) : IsComputable d e f := fun n =>
  rePred_comp h (Computable.pair (Computable.const n) Computable.id)

/-- A continuous function that sends basis elements to basis elements, by a
computable map `t` on indices, is uniformly computable — provided the *target*
presentation's ordering is recursive.

The set to enumerate is `{(n, m) | eₘ ⊑ e_{t n}}`, which is the ordering
relation of `e` precomposed with the computable map `(n, m) ↦ (m, t n)`; the
hypothesis on `f` is what turns `f (dₙ)` into `e_{t n}`. Nothing is asked of `d`
beyond its being a presentation, because `d` enters only through the index `n`.

This is the one place where recursion theory is spent; the identity and the
constants below are instances of it. -/
theorem isUniformlyComputable_of_enumMap {d : EffectivePresentation α}
    {e : EffectivePresentation β} (he : RecursiveLE e) {f : ScottHom α β}
    {t : ℕ → ℕ} (ht : Computable t) (hf : ∀ n, f (d.enum n) = e.enum (t n)) :
    IsUniformlyComputable d e f :=
  (rePred_comp he.to_re
      (Computable.pair Computable.snd (ht.comp Computable.fst))).of_eq fun p => by
    rw [hf p.1]

/-- The identity is computable with respect to any presentation whose ordering is
recursive: take `t = id` in `isUniformlyComputable_of_enumMap`.

Stated for an arbitrary `f : ScottHom α α` that is pointwise the identity rather
than for the bundled `ScottHom.id`, which lives in `FinitaryProjectionPoset` and
would drag `Theorem6` and `Skeleton.Section6` into this module's import closure.
At a call site, `ScottHom.id` discharges `hf` with `fun _ => rfl`. -/
theorem isUniformlyComputable_id {d : EffectivePresentation α}
    (hd : RecursiveLE d) {f : ScottHom α α} (hf : ∀ x, f x = x) :
    IsUniformlyComputable d d f :=
  isUniformlyComputable_of_enumMap hd Computable.id fun n => hf (d.enum n)

/-- A constant function at a basis element is computable, with the same proviso
on the target presentation: take `t` to be the constant index map. -/
theorem isUniformlyComputable_const {d : EffectivePresentation α}
    {e : EffectivePresentation β} (he : RecursiveLE e) (j : ℕ) :
    IsUniformlyComputable d e (ScottHom.const (e.enum j) : ScottHom α β) :=
  isUniformlyComputable_of_enumMap he (Computable.const j) fun _ => rfl

end ScottDomains.Computable
