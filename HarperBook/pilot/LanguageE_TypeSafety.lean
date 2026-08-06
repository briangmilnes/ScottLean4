/-
  Practical Foundations for Programming Languages (PFPL), 2nd ed.
  Robert Harper, Cambridge University Press, 2016.

  Type safety for the language E, Chapters 4–6.

  Source:
  * Ch. 4 "Statics"  — syntax and typing rules (4.1a)–(4.1h).
  * Ch. 5 "Dynamics" — value judgment and the structural (call-by-value)
                        transition judgment `e ↦ e'`.
  * Ch. 6 "Type Safety" — Preservation (Thm. 6.1), Progress (Thm. 6.2),
                        Canonical Forms (Lemma 6.3).

  STATUS: complete, standalone core Lean 4 (NO Mathlib, no project imports).
  The statics are copied from `pilot/LanguageE_Statics.lean`, with ONE
  deliberate modelling change explained below.

  MODELLING CHANGE vs. the pilot (necessary for type safety to HOLD).
  The pilot's variable rule (4.1a) used list membership `(x,τ) ∈ Γ`. Under a
  context with a repeated key — which the `let` rule (4.1h) produces whenever a
  bound variable shadows an outer one — membership is NON-deterministic: a
  single variable admits every type recorded for it. That defeats shadowing and
  makes Preservation FALSE. Concretely, with the membership rule
    ⊢ let x = num[0] in (let x = str["a"] in x) : num
  is derivable (the inner `x` may pick the outer `x:num`), yet it steps to
    let x = str["a"] in x
  whose only type is `str`. So `e ↦ e'` fails to preserve the type.

  PFPL's generic judgment (Ch. 4) uses a hypothetical context whose variables
  are DISTINCT (freshness / α-renaming convention), i.e. deterministic lookup
  with innermost binding winning. We model exactly that with a functional
  `lookup : Ctx → String → Option Ty` (first match wins). This is faithful to
  the book and is what makes rule (4.1h)'s freshness convention precise.
-/

namespace PFPL.Ch4.LanguageE

/-! ## Statics (Chapter 4) -/

/-- Types of E (Section 4.1): `Typ τ ::= num | str`. -/
inductive Ty where
  | num
  | str
  deriving DecidableEq, Repr

/-- Expressions of E (Section 4.1):
    `Exp e ::= x | num[n] | str[s] | plus(e1;e2) | times(e1;e2)
             | cat(e1;e2) | len(e) | let(e1; x.e2)`. -/
inductive Exp where
  | var   (x : String)
  | num   (n : Nat)
  | str   (s : String)
  | plus  (e1 e2 : Exp)
  | times (e1 e2 : Exp)
  | cat   (e1 e2 : Exp)
  | len   (e : Exp)
  | letE  (e1 : Exp) (x : String) (e2 : Exp)
  deriving Repr

/-- A typing context Γ: hypotheses `x : τ`, innermost (leftmost) first. -/
abbrev Ctx := List (String × Ty)

/-- Deterministic context lookup: the innermost (first) binding of `x` wins.
    This realises rule (4.1a)'s hypothetical context with distinct variables. -/
def lookup : Ctx → String → Option Ty
  | [],            _ => none
  | (y, τ) :: Γ,   x => if x = y then some τ else lookup Γ x

/-- The statics of E, rules (4.1a)–(4.1h). Syntax-directed: one rule per form.
    Rule (4.1a) uses `lookup Γ x = some τ` (innermost binding), replacing the
    pilot's `(x,τ) ∈ Γ` so that shadowing is deterministic. -/
inductive HasType : Ctx → Exp → Ty → Prop where
  /-- (4.1a) `Γ ⊢ x : τ` when the innermost binding of `x` in `Γ` is `τ`. -/
  | var   {Γ x τ}      (h : lookup Γ x = some τ) :
      HasType Γ (.var x) τ
  /-- (4.1c) `Γ ⊢ num[n] : num`. -/
  | num   {Γ n} :
      HasType Γ (.num n) .num
  /-- (4.1b) `Γ ⊢ str[s] : str`. -/
  | str   {Γ s} :
      HasType Γ (.str s) .str
  /-- (4.1d) `Γ ⊢ e1 : num   Γ ⊢ e2 : num   ⟹   Γ ⊢ plus(e1;e2) : num`. -/
  | plus  {Γ e1 e2} (h1 : HasType Γ e1 .num) (h2 : HasType Γ e2 .num) :
      HasType Γ (.plus e1 e2) .num
  /-- (4.1e) `Γ ⊢ e1 : num   Γ ⊢ e2 : num   ⟹   Γ ⊢ times(e1;e2) : num`. -/
  | times {Γ e1 e2} (h1 : HasType Γ e1 .num) (h2 : HasType Γ e2 .num) :
      HasType Γ (.times e1 e2) .num
  /-- (4.1f) `Γ ⊢ e1 : str   Γ ⊢ e2 : str   ⟹   Γ ⊢ cat(e1;e2) : str`. -/
  | cat   {Γ e1 e2} (h1 : HasType Γ e1 .str) (h2 : HasType Γ e2 .str) :
      HasType Γ (.cat e1 e2) .str
  /-- (4.1g) `Γ ⊢ e : str   ⟹   Γ ⊢ len(e) : num`. -/
  | len   {Γ e} (h : HasType Γ e .str) :
      HasType Γ (.len e) .num
  /-- (4.1h) `Γ ⊢ e1 : τ1   Γ, x : τ1 ⊢ e2 : τ2   ⟹   Γ ⊢ let(e1;x.e2) : τ2`. -/
  | letE  {Γ e1 x e2 τ1 τ2}
      (h1 : HasType Γ e1 τ1) (h2 : HasType ((x, τ1) :: Γ) e2 τ2) :
      HasType Γ (.letE e1 x e2) τ2

@[inherit_doc] notation:50 Γ " ⊢ " e " : " τ => HasType Γ e τ

/-! ## Dynamics (Chapter 5) -/

/-- Values (Section 5.1): `num[n] val` and `str[s] val` are the only values. -/
inductive Value : Exp → Prop where
  | num (n : Nat) : Value (.num n)
  | str (s : String) : Value (.str s)

/-- Capture-avoiding substitution `[v/x]e`.

    E's values `num[n]`, `str[s]` are CLOSED, so substituting a value never
    captures; no α-renaming is required. For `let(e1;y.e2)` we always substitute
    into `e1`, and into `e2` only when `y ≠ x` (an inner binder `y = x` shadows
    the substituted variable). Total function `Exp → Exp`. -/
def subst (x : String) (v : Exp) : Exp → Exp
  | .var y        => if y = x then v else .var y
  | .num n        => .num n
  | .str s        => .str s
  | .plus e1 e2   => .plus (subst x v e1) (subst x v e2)
  | .times e1 e2  => .times (subst x v e1) (subst x v e2)
  | .cat e1 e2    => .cat (subst x v e1) (subst x v e2)
  | .len e        => .len (subst x v e)
  | .letE e1 y e2 => .letE (subst x v e1) y (if y = x then e2 else subst x v e2)

/-- The structural, call-by-value transition judgment `e ↦ e'` (Chapter 5).
    Congruence rules `(a)`/`(b)` and instruction rules `(c)`/`(d)` per form. -/
inductive Step : Exp → Exp → Prop where
  | plus1  {e1 e1' e2}  (s : Step e1 e1') : Step (.plus e1 e2) (.plus e1' e2)
  | plus2  {e1 e2 e2'}  (hv : Value e1) (s : Step e2 e2') : Step (.plus e1 e2) (.plus e1 e2')
  | plusβ  {m n}        : Step (.plus (.num m) (.num n)) (.num (m + n))
  | times1 {e1 e1' e2}  (s : Step e1 e1') : Step (.times e1 e2) (.times e1' e2)
  | times2 {e1 e2 e2'}  (hv : Value e1) (s : Step e2 e2') : Step (.times e1 e2) (.times e1 e2')
  | timesβ {m n}        : Step (.times (.num m) (.num n)) (.num (m * n))
  | cat1   {e1 e1' e2}  (s : Step e1 e1') : Step (.cat e1 e2) (.cat e1' e2)
  | cat2   {e1 e2 e2'}  (hv : Value e1) (s : Step e2 e2') : Step (.cat e1 e2) (.cat e1 e2')
  | catβ   {s t : String} : Step (.cat (.str s) (.str t)) (.str (s ++ t))
  | len1   {e e'}       (s : Step e e') : Step (.len e) (.len e')
  | lenβ   {s : String} : Step (.len (.str s)) (.num s.length)
  | let1   {e1 e1' x e2} (s : Step e1 e1') : Step (.letE e1 x e2) (.letE e1' x e2)
  | letβ   {e1 x e2}    (hv : Value e1) : Step (.letE e1 x e2) (subst x e1 e2)

/-! ## Structural lemmas on typing -/

/-- A successful lookup survives extending the context on the right (deeper).
    Used to weaken a closed value into any context. -/
theorem lookup_append_some {x : String} {τ : Ty} {Δ : Ctx} :
    ∀ {Γ : Ctx}, lookup Γ x = some τ → lookup (Γ ++ Δ) x = some τ := by
  intro Γ
  induction Γ with
  | nil => intro h; simp [lookup] at h
  | cons p Γ ih =>
    obtain ⟨y, σ⟩ := p
    intro h
    simp only [List.cons_append, lookup] at h ⊢
    by_cases hxy : x = y
    · simp only [if_pos hxy] at h ⊢; exact h
    · simp only [if_neg hxy] at h ⊢; exact ih h

/-- Weakening (§4.3): typing is preserved by appending hypotheses on the right,
    `Γ ⊢ e : τ  ⟹  Γ ++ Δ ⊢ e : τ`. -/
theorem weaken_append {Γ e τ} (h : HasType Γ e τ) :
    ∀ {Δ : Ctx}, HasType (Γ ++ Δ) e τ := by
  induction h with
  | var hlk        => intro Δ; exact .var (lookup_append_some hlk)
  | num            => intro Δ; exact .num
  | str            => intro Δ; exact .str
  | plus _ _ ih1 ih2  => intro Δ; exact .plus ih1 ih2
  | times _ _ ih1 ih2 => intro Δ; exact .times ih1 ih2
  | cat _ _ ih1 ih2   => intro Δ; exact .cat ih1 ih2
  | len _ ih          => intro Δ; exact .len ih
  | letE _ _ ih1 ih2  => intro Δ; exact .letE ih1 ih2

/-- Context congruence: typing depends on the context only through `lookup`, so
    contexts with equal lookups type the same expressions. This packages
    exchange (reordering distinct-key hypotheses) and contraction (dropping a
    shadowed hypothesis), both needed by the substitution lemma. -/
theorem lookup_cong {Γ e τ} (h : HasType Γ e τ) :
    ∀ {Γ'}, (∀ z, lookup Γ z = lookup Γ' z) → HasType Γ' e τ := by
  induction h with
  | var hlk => intro Γ' hc; apply HasType.var; rw [← hc]; exact hlk
  | num => intro Γ' _; exact .num
  | str => intro Γ' _; exact .str
  | plus _ _ ih1 ih2 => intro Γ' hc; exact .plus (ih1 hc) (ih2 hc)
  | times _ _ ih1 ih2 => intro Γ' hc; exact .times (ih1 hc) (ih2 hc)
  | cat _ _ ih1 ih2 => intro Γ' hc; exact .cat (ih1 hc) (ih2 hc)
  | len _ ih => intro Γ' hc; exact .len (ih hc)
  | @letE _ _ xx _ _ _ _ _ ih1 ih2 =>
      intro Γ' hc
      refine .letE (ih1 hc) (ih2 ?_)
      intro z; simp only [lookup]
      by_cases hzx : z = xx
      · simp [hzx]
      · simp [hzx, hc z]

/-- Values are closed: a value typeable in any context is typeable in `[]`
    (with the same type). Bridges the general substitution lemma (which needs a
    closed `v`) with Preservation (where `v` is a value typed in `Γ`). -/
theorem value_typing_empty {Γ v τ} (hval : Value v) (h : HasType Γ v τ) :
    HasType [] v τ := by
  cases hval with
  | num n => cases h; exact .num
  | str s => cases h; exact .str

/-- Substitution lemma (§4.3, Lemma 4.4). If `x:τ1, Γ ⊢ e2 : τ2` and `⊢ v : τ1`
    (v closed) then `Γ ⊢ [v/x]e2 : τ2`. Proved by induction on `e2`, generalising
    the context; the `let` cases use `lookup_cong` for exchange (distinct binder)
    and contraction (shadowing binder), and the variable case uses weakening. -/
theorem subst_pres {x : String} {v : Exp} {τ1 : Ty} (hv : HasType [] v τ1) :
    ∀ {e2 : Exp} {Γ : Ctx} {τ2 : Ty},
      HasType ((x, τ1) :: Γ) e2 τ2 → HasType Γ (subst x v e2) τ2 := by
  intro e2
  induction e2 with
  | var y =>
    intro Γ τ2 hty
    cases hty with
    | var hlk =>
      by_cases hyx : y = x
      · simp only [subst, if_pos hyx]
        simp only [lookup] at hlk
        rw [if_pos hyx] at hlk
        injection hlk with hlk
        subst hlk
        exact weaken_append hv
      · simp only [subst, if_neg hyx]
        apply HasType.var
        simp only [lookup, if_neg hyx] at hlk
        exact hlk
  | num n => intro Γ τ2 hty; cases hty; exact .num
  | str s => intro Γ τ2 hty; cases hty; exact .str
  | plus e1 e2 ih1 ih2 =>
      intro Γ τ2 hty; cases hty with
      | plus h1 h2 => exact .plus (ih1 h1) (ih2 h2)
  | times e1 e2 ih1 ih2 =>
      intro Γ τ2 hty; cases hty with
      | times h1 h2 => exact .times (ih1 h1) (ih2 h2)
  | cat e1 e2 ih1 ih2 =>
      intro Γ τ2 hty; cases hty with
      | cat h1 h2 => exact .cat (ih1 h1) (ih2 h2)
  | len e ih =>
      intro Γ τ2 hty; cases hty with
      | len h => exact .len (ih h)
  | letE e1 y eb ih1 ih2 =>
      intro Γ τ2 hty
      cases hty with
      | letE h1 h2 =>
        by_cases hyx : y = x
        · -- shadowing binder: do not substitute into the body; drop (x,τ1)
          simp only [subst, if_pos hyx]
          refine .letE (ih1 h1) ?_
          refine lookup_cong h2 ?_
          intro z; simp only [lookup]
          by_cases hzy : z = y
          · simp [hzy]
          · have hzx : ¬ z = x := fun hc => hzy (hc.trans hyx.symm)
            simp [hzy, hzx]
        · -- distinct binder: substitute into the body; exchange the hypotheses
          simp only [subst, if_neg hyx]
          refine .letE (ih1 h1) (ih2 (lookup_cong h2 ?_))
          intro z; simp only [lookup]
          by_cases hzy : z = y
          · simp [hzy, hyx]
          · by_cases hzx : z = x
            · simp [hzx, Ne.symm hyx]
            · simp [hzy, hzx]

/-! ## Canonical forms (Chapter 6, Lemma 6.3) -/

/-- Canonical forms for `num`: a closed value of type `num` is a numeral. -/
theorem canonical_num {v} (hty : HasType [] v .num) (hval : Value v) :
    ∃ n, v = .num n := by
  cases hval with
  | num n => exact ⟨n, rfl⟩
  | str s => cases hty

/-- Canonical forms for `str`: a closed value of type `str` is a literal. -/
theorem canonical_str {v} (hty : HasType [] v .str) (hval : Value v) :
    ∃ s, v = .str s := by
  cases hval with
  | num n => cases hty
  | str s => exact ⟨s, rfl⟩

/-! ## Type safety (Chapter 6) -/

/-- Preservation (Theorem 6.1): `Γ ⊢ e : τ` and `e ↦ e'` imply `Γ ⊢ e' : τ`.
    Induction on the transition; congruence cases use the induction hypothesis,
    instruction cases invert the typing, and `let`-β uses `subst_pres`. -/
theorem preservation {Γ e e' τ} (hstep : Step e e') :
    HasType Γ e τ → HasType Γ e' τ := by
  induction hstep generalizing τ with
  | plus1 _s ih  => intro hty; cases hty with | plus h1 h2 => exact .plus (ih h1) h2
  | plus2 _hv _s ih => intro hty; cases hty with | plus h1 h2 => exact .plus h1 (ih h2)
  | plusβ => intro hty; cases hty with | plus _ _ => exact .num
  | times1 _s ih => intro hty; cases hty with | times h1 h2 => exact .times (ih h1) h2
  | times2 _hv _s ih => intro hty; cases hty with | times h1 h2 => exact .times h1 (ih h2)
  | timesβ => intro hty; cases hty with | times _ _ => exact .num
  | cat1 _s ih => intro hty; cases hty with | cat h1 h2 => exact .cat (ih h1) h2
  | cat2 _hv _s ih => intro hty; cases hty with | cat h1 h2 => exact .cat h1 (ih h2)
  | catβ => intro hty; cases hty with | cat _ _ => exact .str
  | len1 _s ih => intro hty; cases hty with | len h => exact .len (ih h)
  | lenβ => intro hty; cases hty with | len _ => exact .num
  | let1 _s ih => intro hty; cases hty with | letE h1 h2 => exact .letE (ih h1) h2
  | letβ hv => intro hty; cases hty with
      | letE h1 h2 => exact subst_pres (value_typing_empty hv h1) h2

/-- Progress (Theorem 6.2): a closed well-typed `e` is a value or steps.
    Induction on `e`; instruction cases use Canonical Forms. -/
theorem progress : ∀ {e τ}, HasType [] e τ → Value e ∨ ∃ e', Step e e' := by
  intro e
  induction e with
  | var _y => intro τ hty; cases hty with | var hlk => simp [lookup] at hlk
  | num n => intro τ _hty; exact Or.inl (.num n)
  | str s => intro τ _hty; exact Or.inl (.str s)
  | plus e1 e2 ih1 ih2 =>
      intro τ hty; cases hty with
      | plus h1 h2 =>
        cases ih1 h1 with
        | inl hv1 =>
          cases ih2 h2 with
          | inl hv2 =>
            cases canonical_num h1 hv1 with
            | intro m hm => cases canonical_num h2 hv2 with
              | intro n hn => subst hm; subst hn; exact Or.inr ⟨_, .plusβ⟩
          | inr hex2 => cases hex2 with
            | intro e2' s2 => exact Or.inr ⟨_, .plus2 hv1 s2⟩
        | inr hex1 => cases hex1 with
          | intro e1' s1 => exact Or.inr ⟨_, .plus1 s1⟩
  | times e1 e2 ih1 ih2 =>
      intro τ hty; cases hty with
      | times h1 h2 =>
        cases ih1 h1 with
        | inl hv1 =>
          cases ih2 h2 with
          | inl hv2 =>
            cases canonical_num h1 hv1 with
            | intro m hm => cases canonical_num h2 hv2 with
              | intro n hn => subst hm; subst hn; exact Or.inr ⟨_, .timesβ⟩
          | inr hex2 => cases hex2 with
            | intro e2' s2 => exact Or.inr ⟨_, .times2 hv1 s2⟩
        | inr hex1 => cases hex1 with
          | intro e1' s1 => exact Or.inr ⟨_, .times1 s1⟩
  | cat e1 e2 ih1 ih2 =>
      intro τ hty; cases hty with
      | cat h1 h2 =>
        cases ih1 h1 with
        | inl hv1 =>
          cases ih2 h2 with
          | inl hv2 =>
            cases canonical_str h1 hv1 with
            | intro s hs => cases canonical_str h2 hv2 with
              | intro t ht => subst hs; subst ht; exact Or.inr ⟨_, .catβ⟩
          | inr hex2 => cases hex2 with
            | intro e2' s2 => exact Or.inr ⟨_, .cat2 hv1 s2⟩
        | inr hex1 => cases hex1 with
          | intro e1' s1 => exact Or.inr ⟨_, .cat1 s1⟩
  | len e ih =>
      intro τ hty; cases hty with
      | len h =>
        cases ih h with
        | inl hv => cases canonical_str h hv with
          | intro s hs => subst hs; exact Or.inr ⟨_, .lenβ⟩
        | inr hex => cases hex with
          | intro e' s => exact Or.inr ⟨_, .len1 s⟩
  | letE e1 x e2 ih1 _ih2 =>
      intro τ hty; cases hty with
      | letE h1 h2 =>
        cases ih1 h1 with
        | inl hv1 => exact Or.inr ⟨_, .letβ hv1⟩
        | inr hex1 => cases hex1 with
          | intro e1' s1 => exact Or.inr ⟨_, .let1 s1⟩

end PFPL.Ch4.LanguageE
