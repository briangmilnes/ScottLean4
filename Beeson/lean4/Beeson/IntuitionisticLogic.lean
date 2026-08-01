/-
  Beeson — Intuitionistic logic (propositional / `Prop` lemmas).
  Ported from the Lean 3 source `Beeson/IntuitionisticLogic.lean`.

  Translation notes (Lean 3 -> Lean 4, CORE only, no Mathlib):
    * `lemma`            -> `theorem`  (`lemma` is a Mathlib extension, absent from core)
    * `assume x, begin … end` -> `by intro x; …`
    * `begin … end`      -> `by`
    * trailing tactic commas removed
    * `cases h with a b` (And)  -> use `h.left` / `h.right`, or `⟨a,b⟩`
    * `cases h with a b` (Or)   -> `cases h with | inl a => … | inr b => …`
    * `split`            -> `constructor`;  `{ … }` focus blocks -> `·` bullets
    * `left` / `right`   -> `Or.inl` / `Or.inr` (or the `left`/`right` tactics)
    * dropped `import mario` and the final `#axioms_all` diagnostic command
      (Lean 3 metaprogramming; only used to print the axiom list — the source
      noted "this file is clean").
  The Lean 3 original contains no `sorry`/`admit` and no abandoned proof paths,
  so there are no `-- FAILED (Beeson):` blocks to preserve.
-/

theorem Heyting1 : ∀ (p : Prop), p → p ∧ p := by
  intro p h
  exact ⟨h, h⟩

theorem Heyting2 : ∀ (p q : Prop), p ∧ q → q ∧ p := by
  intro p q h
  exact ⟨h.right, h.left⟩

theorem Heyting3 : ∀ (p q r : Prop), (p → q) → ((p ∧ r) → (q ∧ r)) := by
  intro p q r h h2
  exact ⟨h h2.left, h2.right⟩

theorem Heyting4 : ∀ (p q r : Prop), ((p → q) ∧ (q → r)) → (p → r) := by
  intro p q r h h2
  exact h.right (h.left h2)

theorem Heyting5 : ∀ (p q : Prop), (q → (p → q)) := by
  intro p q h _
  exact h

theorem Heyting6 : ∀ (p q : Prop), (p ∧ (p → q)) → q := by
  intro p q h
  exact h.right h.left

theorem Heyting7 : ∀ (p q : Prop), p → (p ∨ q) := by
  intro p q h
  exact Or.inl h

theorem Heyting8 : ∀ (p q : Prop), (p ∨ q) → (q ∨ p) := by
  intro p q h
  cases h with
  | inl h2 => exact Or.inr h2
  | inr h3 => exact Or.inl h3

theorem Heyting9 : ∀ (p q r : Prop), ((p → r) ∧ (q → r)) → ((p ∨ q) → r) := by
  intro p q r h h2
  cases h2 with
  | inl h5 => exact h.left h5
  | inr h6 => exact h.right h6

theorem Heyting10 : ∀ (p q : Prop), ¬ p → (p → q) := by
  intro p q h h2
  contradiction

theorem Heyting11 : ∀ (p q : Prop), ((p → q) ∧ (p → ¬ q)) → ¬ p := by
  intro p q h h2
  have h5 := h.left h2
  have h6 := h.right h2
  contradiction

theorem double_negate : ∀ (P : Prop), P → ¬¬ P := by
  intro P hP h
  contradiction

theorem notnotLEM : ∀ (P : Prop), ¬¬ (P ∨ ¬ P) := by
  intro P h
  have h2 : ¬ P := by
    intro hP
    exact h (Or.inl hP)
  exact h (Or.inr h2)

theorem not_orNF : ∀ (A B : Prop), ¬ (A ∨ B) ↔ ¬ A ∧ ¬ B := by
  intro A B
  constructor
  · intro h
    exact ⟨fun h2 => h (Or.inl h2), fun h2 => h (Or.inr h2)⟩
  · intro h h4
    cases h4 with
    | inl h5 => exact h.left h5
    | inr h6 => exact h.right h6

theorem Kleene12 : ∀ (A B : Prop), (A → B) → ¬ B → ¬ A := by
  intro A B h1 h2 h3
  exact h2 (h1 h3)

theorem Kleene3 : ∀ (A B C : Prop), (A → B → C) ↔ (B → A → C) := by
  intro A B C
  constructor
  · intro h h2 h3; exact h h3 h2
  · intro h h2 h3; exact h h3 h2

theorem Kleene4and5 : ∀ (A B C : Prop), (A ∧ B → C) ↔ (A → B → C) := by
  intro A B C
  constructor
  · intro h h2 h3; exact h ⟨h2, h3⟩
  · intro h h2; exact h h2.left h2.right

theorem Kleene13 : ∀ (A B : Prop), (A → ¬ B) → B → ¬ A := by
  intro A B h h2 h3
  exact h h3 h2

theorem triplenegation : ∀ (P : Prop), ¬¬¬ P ↔ ¬ P := by
  intro P
  constructor
  · intro h h2
    exact h (double_negate P h2)
  · intro h
    exact double_negate (¬ P) h

theorem Kleene22 : ∀ (A B C : Prop), (A → B → C) → ¬¬ A → ¬¬ B → ¬¬ C := by
  intro A B C h h2 h3
  have hcopy := h
  rw [Kleene3] at h
  have h4 := Kleene12 B (A → C) h
  have h5 : B → (¬¬ A) → ¬¬ C := by
    intro h6 h7
    have h8 := h h6
    have h9 := Kleene12 A C h8
    have h10 := Kleene12 (¬ C) (¬ A) h9 h7
    exact h10
  have h6 : B → ¬¬ C := by
    intro h7
    exact h5 h7 h2
  have h7 := Kleene13 B (¬ C) h6
  have h8 := Kleene13 (¬ C) (¬¬ B)
  rw [triplenegation] at h8
  exact h8 h7 h3

theorem notnot_imp : ∀ (P Q : Prop), (P → Q) → ¬¬ P → ¬¬ Q := by
  intro P Q h
  have h2 := Kleene12 P Q h
  have h3 := Kleene12 (¬ Q) (¬ P) h2
  exact h3

theorem iffdef : ∀ (P Q : Prop), (P ↔ Q) ↔ ((P → Q) ∧ (Q → P)) := by
  intro P Q
  constructor
  · intro h20
    exact ⟨h20.mp, h20.mpr⟩
  · intro h20
    exact ⟨h20.left, h20.right⟩

theorem push_double_negationNF : ∀ (A B : Prop), (¬¬ (A → B)) → (¬¬ A) → ¬¬ B := by
  intro A B
  have h2 : (A → B) → (A → B) := fun h => h
  exact Kleene22 (A → B) A B h2

theorem notnot_imp2way : ∀ (P Q : Prop), ¬¬(P → Q) ↔ (¬¬ P → ¬¬ Q) := by
  intro P Q
  constructor
  · intro h6
    have h4 := notnot_imp P Q
    have h5 := notnot_imp (P → Q) (¬¬ P → ¬¬ Q) h4
    have h7 := h5 h6
    have h8 := push_double_negationNF (¬¬ P) (¬¬ Q) h7
    rw [triplenegation] at h8
    rw [triplenegation] at h8
    exact h8
  · intro h h4
    apply h
    · intro h5
      apply h4
      intro h6
      contradiction
    · intro h5
      apply h4
      intro h6
      exact h5

theorem notnot_forall {M : Type} :
    ∀ (P : M → Prop), (¬¬ ∀ (x : M), P x) → ∀ (x : M), ¬¬ P x := by
  intro P h t h2
  have h3 : ¬ ∀ (x : M), P x := by
    intro h4
    exact h2 (h4 t)
  contradiction

theorem notnot_and : ∀ (P Q : Prop), (¬¬ (P ∧ Q)) ↔ ((¬¬ P) ∧ ¬¬ Q) := by
  intro P Q
  constructor
  · intro h
    constructor
    · intro h2
      apply h
      intro h3
      exact h2 h3.left
    · intro h2
      apply h
      intro h3
      exact h2 h3.right
  · intro h h4
    have h5 : P → Q → P ∧ Q := fun h6 h7 => ⟨h6, h7⟩
    have h6 := notnot_imp P (Q → P ∧ Q) h5 h.left
    have h7 := push_double_negationNF Q (P ∧ Q) h6 h.right
    contradiction

theorem notnot_iff : ∀ (P Q : Prop), ¬¬ (P ↔ Q) → (¬¬ P ↔ ¬¬ Q) := by
  intro P Q h
  rw [iffdef]
  rw [iffdef] at h
  have h3 := notnot_and (P → Q) (Q → P)
  rw [h3] at h
  constructor
  · exact push_double_negationNF P Q h.left
  · exact push_double_negationNF Q P h.right

theorem notnot_iff_2way : ∀ (P Q : Prop), ¬¬ (P ↔ Q) ↔ (¬¬ P ↔ ¬¬ Q) := by
  intro P Q
  constructor
  · exact notnot_iff P Q
  · intro h
    rw [iffdef]
    rw [iffdef] at h
    have h4 := notnot_and (P → Q) (Q → P)
    rw [h4]
    constructor
    · rw [notnot_imp2way]; exact h.left
    · rw [notnot_imp2way]; exact h.right

-- Lean 3 source used `rw not_exists`; ported without it (core has no `not_exists`).
theorem existsnotnot {M : Type} :
    ∀ (P : M → Prop), (¬¬ ∃ (x : M), ¬¬ P x) → ¬¬ ∃ (x : M), P x := by
  intro P h h2
  apply h
  intro h3
  cases h3 with
  | intro c h4 =>
    apply h4
    intro hpc
    exact h2 ⟨c, hpc⟩

theorem pushnotnot : ∀ (P Q A B : Prop),
    ¬¬(P ∨ Q) → (P → A) → (Q → B) → ¬¬ (A ∨ B) := by
  intro P Q A B h2 h3 h4
  have h5 : P ∨ Q → A ∨ B := by
    intro h6
    cases h6 with
    | inl h7 => exact Or.inl (h3 h7)
    | inr h8 => exact Or.inr (h4 h8)
  have h11 := double_negate (P ∨ Q → A ∨ B) h5
  have h12 := push_double_negationNF (P ∨ Q) (A ∨ B) h11
  exact h12 h2
