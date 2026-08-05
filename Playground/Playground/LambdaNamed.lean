import Mathlib.Tactic

/-!
# The untyped λ-calculus with NAMED variables and EXPLICIT α-equivalence

Dana Scott asked for the λ-calculus done *without* de Bruijn indices. Here terms
carry real names (`lam "x" t`), and α-equivalence — identifying terms that differ
only in their bound names — is defined **explicitly**, as a relation.

## Defining α without renaming or de Bruijn

The subtle choice is how to *state* α on named terms. We avoid both de Bruijn
indices and capture-avoiding renaming by carrying a **name correspondence**
`R : List (String × String)`: entering a pair of binders `lam x t` / `lam y s`
extends `R` with `(x, y)`, recording that these bound names correspond. Two
variables match if the *innermost* correspondence binds them together, or — if
neither is bound here — they are literally equal. This makes α a clean
*structural* relation: no term renaming, no well-founded recursion.

## Status (honest, kernel-checked)

Proved, with **no `sorry`s**: α is **reflexive, symmetric, and transitive** — a
genuine equivalence relation. A `decide`-checked example shows why *naive*
substitution is unsound (it captures), the very reason α-equivalence is needed.
Not yet formalized (future work, and where the named representation's cost really
bites): capture-avoiding substitution, β-reduction, and confluence.
-/

namespace Playground.LambdaNamed

/-- Untyped λ-terms with named variables. -/
inductive Term where
  | var : String → Term
  | app : Term → Term → Term
  | lam : String → Term → Term
deriving DecidableEq, Repr

open Term

/-- Free variables of a term. -/
def fv : Term → List String
  | var x   => [x]
  | app t u => fv t ++ fv u
  | lam x t => (fv t).filter (· != x)

/-! ## Explicit α-equivalence via a name correspondence -/

/-- `related R x y`: under the correspondence `R`, the left name `x` matches the
right name `y`. The innermost binding wins (shadowing); unbound names must be
identical. -/
def related : List (String × String) → String → String → Prop
  | [],          x, y => x = y
  | (a, b) :: R, x, y => (x = a ∧ y = b) ∨ (x ≠ a ∧ y ≠ b ∧ related R x y)

/-- α-equivalence under a name correspondence `R`. -/
inductive AlphaR : List (String × String) → Term → Term → Prop where
  | var  {R x y}         : related R x y → AlphaR R (var x) (var y)
  | app  {R t₁ t₂ s₁ s₂} : AlphaR R t₁ s₁ → AlphaR R t₂ s₂ →
                             AlphaR R (app t₁ t₂) (app s₁ s₂)
  | lam  {R x y t s}     : AlphaR ((x, y) :: R) t s → AlphaR R (lam x t) (lam y s)

/-- Two terms are α-equivalent when related under the empty correspondence. -/
def Alpha (t s : Term) : Prop := AlphaR [] t s

@[inherit_doc] scoped infix:50 " ≡α " => Alpha

/-! ### α is reflexive -/

theorem alphaR_refl (R : List (String × String)) (hR : ∀ w, related R w w) :
    ∀ t, AlphaR R t t
  | var x   => .var (hR x)
  | app t u => .app (alphaR_refl R hR t) (alphaR_refl R hR u)
  | lam x t =>
      have hR' : ∀ w, related ((x, x) :: R) w w := fun w => by
        by_cases h : w = x
        · exact Or.inl ⟨h, h⟩
        · exact Or.inr ⟨h, h, hR w⟩
      .lam (alphaR_refl ((x, x) :: R) hR' t)

theorem alpha_refl (t : Term) : t ≡α t := alphaR_refl [] (fun _ => rfl) t

/-! ### α is symmetric -/

theorem related_swap : ∀ {R : List (String × String)} {x y},
    related R x y → related (R.map Prod.swap) y x := by
  intro R
  induction R with
  | nil => intro x y h; exact h.symm
  | cons hd tl ih =>
      obtain ⟨a, b⟩ := hd
      intro x y h
      rcases h with ⟨hx, hy⟩ | ⟨hx, hy, hr⟩
      · exact Or.inl ⟨hy, hx⟩
      · exact Or.inr ⟨hy, hx, ih hr⟩

theorem alphaR_symm {R t s} (h : AlphaR R t s) : AlphaR (R.map Prod.swap) s t := by
  induction h with
  | var hr           => exact .var (related_swap hr)
  | app _ _ ih₁ ih₂  => exact .app ih₁ ih₂
  | lam _ ih         => exact .lam ih

theorem alpha_symm {t s} (h : t ≡α s) : s ≡α t := by
  have := alphaR_symm h
  simpa [Alpha] using this

/-! ### α is transitive — completing the equivalence relation

Transitivity *composes* two name correspondences. When `AlphaR R₁ t s` and
`AlphaR R₂ s u` descend through the shared middle term `s`, the lists `R₁` and
`R₂` grow in lockstep, so the middle names align (`R₁.map snd = R₂.map fst`);
their composition then pairs `t`'s names directly with `u`'s. -/

/-- Composition of two aligned name correspondences. -/
def compose : List (String × String) → List (String × String) → List (String × String)
  | (a, _) :: R₁, (_, c) :: R₂ => (a, c) :: compose R₁ R₂
  | _, _ => []

/-- Composition lemma for `related`, given the middle names align. -/
theorem related_comp : ∀ {R₁ R₂ : List (String × String)},
    R₁.map Prod.snd = R₂.map Prod.fst →
      ∀ {x y z}, related R₁ x y → related R₂ y z → related (compose R₁ R₂) x z := by
  intro R₁
  induction R₁ with
  | nil =>
      intro R₂ halign x y z h₁ h₂
      cases R₂ with
      | nil => exact h₁.trans h₂
      | cons _ _ => simp at halign
  | cons hd tl ih =>
      intro R₂ halign x y z h₁ h₂
      obtain ⟨a, b⟩ := hd
      cases R₂ with
      | nil => simp at halign
      | cons hd₂ tl₂ =>
          obtain ⟨c, d⟩ := hd₂
          obtain ⟨rfl, htail⟩ : b = c ∧ tl.map Prod.snd = tl₂.map Prod.fst := by
            simpa using halign
          rcases h₁ with ⟨hxa, rfl⟩ | ⟨hxa, hyb, hr₁⟩
          · rcases h₂ with ⟨_, hzd⟩ | ⟨hbb, _, _⟩
            · exact Or.inl ⟨hxa, hzd⟩
            · exact absurd rfl hbb
          · rcases h₂ with ⟨hyb', _⟩ | ⟨_, hzd, hr₂⟩
            · exact absurd hyb' hyb
            · exact Or.inr ⟨hxa, hzd, ih htail hr₁ hr₂⟩

/-- α under composed correspondences — the engine of transitivity. -/
theorem alphaR_trans {R₁ t s} (h₁ : AlphaR R₁ t s) :
    ∀ {R₂ u}, R₁.map Prod.snd = R₂.map Prod.fst → AlphaR R₂ s u →
      AlphaR (compose R₁ R₂) t u := by
  induction h₁ with
  | var hr =>
      intro R₂ u halign h₂
      cases h₂ with
      | var hr₂ => exact .var (related_comp halign hr hr₂)
  | app _ _ ih₁ ih₂ =>
      intro R₂ u halign h₂
      cases h₂ with
      | app h2a h2b => exact .app (ih₁ halign h2a) (ih₂ halign h2b)
  | @lam R x y t' s' _ ih =>
      intro R₂ u halign h₂
      cases h₂ with
      | @lam _ _ z _ u' h2' =>
          refine .lam ?_
          have halign' : ((x, y) :: R).map Prod.snd = ((y, z) :: R₂).map Prod.fst := by
            show y :: R.map Prod.snd = y :: R₂.map Prod.fst
            rw [halign]
          exact ih halign' h2'

/-- **α is transitive** — so, with `alpha_refl` and `alpha_symm`, an equivalence. -/
theorem alpha_trans {t s u} (h₁ : t ≡α s) (h₂ : s ≡α u) : t ≡α u := by
  have h := alphaR_trans h₁ (R₂ := []) rfl h₂
  exact h

/-! ## Why α is unavoidable: naive substitution captures -/

/-- **Naive** substitution — the obvious structural definition, which does *not*
avoid capture, and is shown just below to be unsound. -/
def substNaive (x : String) (s : Term) : Term → Term
  | var y   => if y = x then s else var y
  | app t u => app (substNaive x s t) (substNaive x s u)
  | lam y t => if y = x then lam y t else lam y (substNaive x s t)

/-- Substituting the *free* variable `"y"` for `"x"` in `λy. x` naively yields
`λy. y`: the substituted `y` was **captured** by the binder. The correct,
capture-avoiding result must first α-rename the bound `y`, giving something
α-equivalent to `λy'. y`. This failure is exactly why α-equivalence is needed. -/
example : substNaive "x" (var "y") (lam "y" (var "x")) = lam "y" (var "y") := by
  decide

/-! ## Further work

Capture-avoiding substitution, β-reduction, and confluence for the *named*
calculus are not yet formalized. That is where the named representation's cost
really shows: even *defining* capture-avoiding substitution needs a fresh-name
supply and well-founded recursion — machinery de Bruijn indices make free. -/

end Playground.LambdaNamed
