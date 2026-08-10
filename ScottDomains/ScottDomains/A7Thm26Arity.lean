import ScottDomains.Combinator

/-!
# r0049, agent7 — Theorem 26 at arity 0: the printed statement is false

`Combinator.thm26`, `thm26_subalgebra` and `thm26_retract` all carry
`hs : ∀ i, 0 < s i`. The paper does not assume it. Printed p. 38, verbatim from
`pdftotext -layout -f 39 -l 40` of `papers/Gunter Scott 1990.pdf`
(`scripts/a7-thm26-page.sh` reproduces the extraction):

> By a continuous algebra we mean a domain with various continuous operations
> singled out. In particular, our λ-calculus model can be considered as a
> continuous algebra of signature `(2,0,0,0,0,0)`. The binary operation is the
> operation of functional application. Here, `0` indicates a 0-ary operation,
> which is just a constant.

and printed p. 39:

> **Theorem 26** Given a signature `(s₁, s₂, …, s_n)`, there are combinations
> `F₁, F₂, …, F_n` defining operations on `D` of these arities such that whenever
> a continuous algebra of this signature is given on a domain `A` that is a
> retract of `D`, then `A` can be made isomorphic to a subalgebra of this fixed
> algebra structure on `D`.

So arity 0 is admitted, and the paper's own worked signature has **five** 0-ary
slots.

## What was on record, and why it was not a proof

`Combinator.lean:60–72` justifies `hs` by an argument it states is not
Lean-checked: two one-point algebras `A = {a}`, `B = {b}` must both map their
0-ary constant to the same fixed `Fᵢ`, and "the paper's own `ψ` satisfies
`fst(ψ(x)) = x`, so `a = fst(Fᵢ) = b`". r0044's agent2 and `docs/Status.md`
correctly refused that inference: `fst ∘ ψ = id` is a property of the paper's
*construction*, not of the printed conclusion, which asks only for an
isomorphism onto *some* subalgebra. `isAlgEmbedding_const_of_subsingleton` below
makes the refusal precise — at a one-element carrier the constant map **is** an
isomorphism onto a subalgebra, so the one-point pair yields no contradiction by
itself.

## What this file establishes

The recorded conclusion is nevertheless **right**, and for a different reason.
The one-point algebra does not contradict anything; it *collapses* the 0-ary
combinations. A signature with two distinct 0-ary slots `i ≠ j` forces, from the
printed statement alone:

1. taking `A` with `oᵢ = oⱼ`, an injective homomorphism sends both constants to
   the same element, so `Fᵢ = Fⱼ` — the combinations are fixed before `A` is
   chosen, so this is a statement about `F` alone;
2. taking `A` with `oᵢ ≠ oⱼ`, an injective homomorphism sends the two constants
   to distinct elements, so `Fᵢ ≠ Fⱼ`.

`not_thm26Printed_of_two_zero_arities` is that contradiction, kernel-checked. It
needs only that `D` is a domain with two distinct elements — which is exactly
what Theorem 25 is stated to deliver ("there is a non-trivial domain `D`").
**Theorem 26 as printed is false for every signature with two or more 0-ary
operations, including the paper's own `(2,0,0,0,0,0)`.** `hs` is therefore a
repair of a printed defect, not a defect of ours.

`not_thm26_statement_of_zero_arity` records the weaker, separate fact that
`Combinator.thm26`'s own statement already fails with a **single** 0-ary slot,
because that statement exposes `fst ∘ ψ = id`. The two are different results: one
is about the printed theorem, the other about our transcription of its proof.

## The encoding, and why it is the generous one

A refutation is only as strong as the hypotheses it grants. `Thm26Printed` grants
every hypothesis the printed sentence carries — `A` is a **domain**, `A` is a
**retract** of `D`, and the operations are **continuous** — and asks for the
weakest reading of the conclusion, an injective homomorphism. `isSubalgebraOf_range`
proves that the image of such a homomorphism really is a subalgebra, so nothing
is lost by not carrying the subalgebra as data: "isomorphic to a subalgebra" and
"admits an injective homomorphism" name the same fact, and any order-theoretic
strengthening of "isomorphic" only strengthens what is being refuted.

Arities are carried on `List` arguments, matching `Combinator`'s own `iterApp`
convention; only lists of length `sᵢ` are constrained, exactly as in
`thm26_subalgebra`.
-/

namespace ScottDomains.R49.Agent7

open ScottDomains.Combinator

universe u

section Arity

variable {D : Type u} [CompletePartialOrder D] (M : LambdaModel D)

/-- `S ⊆ D` is a **subalgebra** of the fixed algebra `⟨D, F₁, …, F_n⟩` of the
signature `s`: closed under each `Fᵢ`, read applicatively. At a 0-ary slot the
list is empty and the condition reads `Fᵢ ∈ S` — every subalgebra contains every
constant, which is the fact the refutation turns on. -/
def IsSubalgebraOf {n : ℕ} (s : Fin n → ℕ) (F : Fin n → Comb) (S : Set D) : Prop :=
  ∀ (i : Fin n) (l : List D), l.length = s i → (∀ b ∈ l, b ∈ S) →
    M.iterApp (M.combEval (F i)) l ∈ S

/-- `h : A → D` is an **isomorphism of `⟨A, o⟩` onto a subalgebra of
`⟨D, F₁, …, F_n⟩`**: injective, and carrying each `oᵢ` to `Fᵢ`. The image is a
subalgebra (`isSubalgebraOf_range`) and `h` is a bijection onto it, so this is
the printed "`A` can be made isomorphic to a subalgebra". -/
def IsAlgEmbedding {n : ℕ} (s : Fin n → ℕ) (F : Fin n → Comb)
    {A : Type u} (o : Fin n → List A → A) (h : A → D) : Prop :=
  Function.Injective h ∧
    ∀ (i : Fin n) (l : List A), l.length = s i →
      M.iterApp (M.combEval (F i)) (l.map h) = h (o i l)

omit [CompletePartialOrder D] in
/-- A list of elements of `Set.range h` is the `h`-image of a list. -/
theorem exists_map_eq {A : Type u} {h : A → D} :
    ∀ l : List D, (∀ b ∈ l, b ∈ Set.range h) → ∃ l' : List A, l = l'.map h
  | [], _ => ⟨[], rfl⟩
  | b :: t, hb => by
    obtain ⟨a, rfl⟩ := hb b (by simp)
    obtain ⟨t', rfl⟩ := exists_map_eq t fun c hc => hb c (by simp [hc])
    exact ⟨a :: t', rfl⟩

/-- The image of an isomorphism onto a subalgebra **is** a subalgebra. This is
what licenses `IsAlgEmbedding` as a transcription of the printed conclusion. -/
theorem isSubalgebraOf_range {n : ℕ} {s : Fin n → ℕ} {F : Fin n → Comb}
    {A : Type u} {o : Fin n → List A → A} {h : A → D}
    (hh : IsAlgEmbedding M s F o h) : IsSubalgebraOf M s F (Set.range h) := by
  intro i l hl hmem
  obtain ⟨l', rfl⟩ := exists_map_eq l hmem
  exact ⟨o i l', (hh.2 i l' (by simpa using hl)).symm⟩

/-- **Continuity of the operations, argumentwise.** Fixing every argument but one
of an `sᵢ`-ary operation gives a Scott-continuous map `A → A`. At `sᵢ = 0` the
premise `|pre| + 1 + |post| = 0` is unsatisfiable, so a 0-ary operation is
continuous by default — as it must be, a constant carrying no argument. -/
def ArgwiseContinuous {A : Type u} [CompletePartialOrder A] {n : ℕ} (s : Fin n → ℕ)
    (o : Fin n → List A → A) : Prop :=
  ∀ (i : Fin n) (pre post : List A), pre.length + 1 + post.length = s i →
    ScottContinuous fun a => o i (pre ++ a :: post)

/-- **Theorem 26 exactly as printed.** Combinations `F₁, …, F_n` chosen from the
signature alone, such that every continuous algebra of that signature on a domain
`A` that is a retract of `D` is isomorphic to a subalgebra of `⟨D, F₁, …, F_n⟩`.

Every hypothesis the printed sentence carries is granted: `A` is a `Domain`, the
retraction pair `(e, p)` with `p ∘ e = id` is the paper's "retract of `D`", and
the operations are continuous. The conclusion is the weakest reading. -/
def Thm26Printed {n : ℕ} (s : Fin n → ℕ) : Prop :=
  ∃ F : Fin n → Comb,
    ∀ (A : Type u) [CompletePartialOrder A] [Domain A]
      (e : ScottHom A D) (p : ScottHom D A), (∀ a, p (e a) = a) →
      ∀ o : Fin n → List A → A, ArgwiseContinuous s o →
        ∃ h : A → D, IsAlgEmbedding M s F o h

/-- **The one-point argument on record proves nothing on its own.** With every
arity `0` and every combination interpreting to the same `c`, the constant map
out of a one-element carrier is an isomorphism onto the subalgebra `{c}`. Two
distinct one-point algebras are therefore isomorphic to the *same* subalgebra,
and the contradiction `Combinator.lean:60–72` draws needs the extra property
`fst(ψ(x)) = x`, which the printed statement does not assert. -/
theorem isAlgEmbedding_const_of_subsingleton {n : ℕ} {s : Fin n → ℕ} {F : Fin n → Comb}
    {A : Type u} [Subsingleton A] (o : Fin n → List A → A) {c : D}
    (hs : ∀ i, s i = 0) (hF : ∀ i, M.combEval (F i) = c) :
    IsAlgEmbedding M s F o (fun _ => c) := by
  refine ⟨fun a b _ => Subsingleton.elim a b, fun i l hl => ?_⟩
  have : l = [] := List.eq_nil_of_length_eq_zero (by rw [hl, hs i])
  subst this
  simpa using hF i

/-- Reading a 0-ary slot out of an isomorphism onto a subalgebra: the fixed
element `Fᵢ` **is** the image of `A`'s constant. -/
theorem combEval_eq_of_zero_arity {n : ℕ} {s : Fin n → ℕ} {F : Fin n → Comb}
    {A : Type u} {o : Fin n → List A → A} {h : A → D}
    (hh : IsAlgEmbedding M s F o h) {i : Fin n} (hi : s i = 0) :
    M.combEval (F i) = h (o i []) := by
  simpa using hh.2 i [] (by simp [hi])

/-- **Theorem 26 as printed is false for any signature with two 0-ary slots.**

Only two instances of the printed statement are used, both at the carrier `D`
itself with the identity retraction and constant operations, so both are
continuous algebras of the signature on a domain that is a retract of `D`:

* `o ≡ x` forces `Fᵢ = h₁ x = Fⱼ`;
* `oᵢ = x`, `oⱼ = y` forces `Fᵢ = h₂ x ≠ h₂ y = Fⱼ` by injectivity.

The combinations `F` are quantified **before** the algebra, which is what makes
the two instances speak about the same `Fᵢ`, `Fⱼ`. The paper's own worked
signature `(2,0,0,0,0,0)` has five 0-ary slots and is covered. -/
theorem not_thm26Printed_of_two_zero_arities [Domain D] {n : ℕ} (s : Fin n → ℕ)
    {i j : Fin n} (hij : i ≠ j) (hi : s i = 0) (hj : s j = 0)
    {x y : D} (hxy : x ≠ y) : ¬ Thm26Printed M s := by
  rintro ⟨F, hF⟩
  -- Instance 1: both constants are `x`.
  obtain ⟨h₁, hinj₁, heq₁⟩ :=
    hF D ScottHom.id ScottHom.id (fun _ => rfl) (fun _ _ => x)
      (fun _ _ _ _ => ScottContinuous.const x)
  have e₁ : M.combEval (F i) = h₁ x :=
    combEval_eq_of_zero_arity M ⟨hinj₁, heq₁⟩ hi
  have e₂ : M.combEval (F j) = h₁ x :=
    combEval_eq_of_zero_arity M ⟨hinj₁, heq₁⟩ hj
  -- Instance 2: the constants are `x` and `y`.
  obtain ⟨h₂, hinj₂, heq₂⟩ :=
    hF D ScottHom.id ScottHom.id (fun _ => rfl) (fun k _ => if k = i then x else y)
      (fun k _ _ _ => ScottContinuous.const (if k = i then x else y))
  have e₃ : M.combEval (F i) = h₂ x := by
    have := combEval_eq_of_zero_arity M ⟨hinj₂, heq₂⟩ hi
    simpa using this
  have e₄ : M.combEval (F j) = h₂ y := by
    have := combEval_eq_of_zero_arity M ⟨hinj₂, heq₂⟩ hj
    simpa [Ne.symm hij] using this
  exact hxy (hinj₂ (e₃ ▸ e₁ ▸ e₂ ▸ e₄ : h₂ x = h₂ y))

/-- **`Combinator.thm26`'s own statement fails at a single 0-ary slot.** That
statement carries the conjunct `fst(ψ a) = a`, which the printed theorem does
not, and one 0-ary slot is then already enough: `Fᵢ` is fixed before the
operations are chosen, so `fst(Fᵢ)` would have to equal every constant at once.

This is a statement about our transcription, not about the paper; the printed
theorem is refuted by `not_thm26Printed_of_two_zero_arities`. Both conclude that
`hs : ∀ i, 0 < s i` cannot be dropped. -/
theorem not_thm26_statement_of_zero_arity {n : ℕ} (s : Fin n → ℕ) {i : Fin n}
    (hi : s i = 0) {x y : D} (hxy : x ≠ y) :
    ¬ ∃ F : Fin n → Comb, ∀ o : Fin n → D, ∃ ψ : ScottHom D D,
        Function.Injective ⇑ψ ∧ (∀ a, M.fstH (ψ a) = a) ∧
        ∀ (k : Fin n) (l : List D), l.length = s k →
          M.iterApp (M.combEval (F k)) (l.map ⇑ψ) = ψ (M.iterApp (o k) l) := by
  rintro ⟨F, hF⟩
  obtain ⟨ψx, -, hfx, hex⟩ := hF fun _ => x
  obtain ⟨ψy, -, hfy, hey⟩ := hF fun _ => y
  have ex : M.combEval (F i) = ψx x := by simpa using hex i [] (by simp [hi])
  have ey : M.combEval (F i) = ψy y := by simpa using hey i [] (by simp [hi])
  exact hxy (by rw [← hfx x, ← ex, ey, hfy y])

end Arity

end ScottDomains.R49.Agent7
