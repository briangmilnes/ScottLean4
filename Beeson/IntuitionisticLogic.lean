import mario

-- Intuitionistic logic


lemma Heyting1: ∀ (p:Prop), p → p ∧ p:=
  assume p,
  begin
    intro h,
    exact ⟨ h,h⟩, 
  end

lemma Heyting2: ∀ (p q:Prop), p ∧ q → q ∧ p:=
  assume p q,
  begin
    intro h,
    exact ⟨ h.right, h.left⟩, 
  end

lemma Heyting3: ∀ (p q r:Prop), (p → q) → ((p ∧ r) → (q ∧ r)):=
  assume p q r,
  begin
    intros h h2, 
    cases h2 with h3 h4,
    exact ⟨ h h3, h4⟩, 
  end

lemma Heyting4: ∀ (p q r:Prop), ((p → q) ∧ (q → r)) → (p → r):=
  assume p q r,
  begin
    intros h h2,
    cases h with h3 h4,
    exact h4 (h3 h2), 
  end 

lemma Heyting5: ∀ (p q: Prop), (q → (p → q)):=
  assume p q,
  begin
    intros h h2, 
    exact h, 
  end

lemma Heyting6: ∀ (p q:Prop), ( p ∧ (p → q)) → q:=
  assume p q,
  begin
    intro h,
    cases h with h2 h3,
    exact h3 h2, 
  end

lemma Heyting7: ∀ (p q:Prop), p → (p ∨ q):=
  assume p q,
  begin
    intro h,
    left,
    exact h,
  end

lemma Heyting8: ∀ (p q:Prop), (p ∨ q) → (q ∨ p):=
  assume p q,
  begin
    intro h,
    cases h with h2 h3,
    {
      right, 
      exact h2,
    },
    {
      left,
      exact h3,
    }
  end 

lemma Heyting9: ∀ (p q r:Prop), ((p → r) ∧ (q → r)) → ((p ∨ q) → r):=
  assume p q r,
  begin
    intros h h2,
    cases h with h3 h4,
    cases h2 with h5 h6,
    {
      exact h3 h5,
    },
    {
      exact h4 h6, 
    }
  end

lemma Heyting10: ∀ (p q:Prop), ¬ p → (p → q):=
  assume p q,
  begin
    intros h h2,
    contradiction,
  end

lemma Heyting11: ∀ (p q:Prop), ((p → q) ∧ (p → ¬ q)) → ¬ p:=
  assume p q,
  begin
    intros h h2,
    cases h with h3 h4,
    have h5:= h3 h2,
    have h6:= h4 h2,
    contradiction, 
  end

lemma double_negate: ∀ (P:Prop), P → ¬¬ P:= 
  assume P, 
  begin 
    intros hP h,
    contradiction,  
  end

lemma notnotLEM: ∀ (P:Prop), ¬¬ (P ∨ ¬ P):=
  assume P,
  begin
    intro h,
    have h2: ¬P:=
      begin
        intro hP,
        apply h,
        left,
        exact hP,
      end, 
    apply h,
    right,
    exact h2, 
  end 

lemma not_orNF: ∀ (A B:Prop), ¬ (A ∨ B) ↔ ¬ A ∧ ¬ B:=
  assume A B,
  begin
    split,
    {
      intro h,
      split,
      {
        intro h2,
        apply h,
        left,
        exact h2,
      },
      {
        intro h2,
        apply h,
        right,
        exact h2, 
      }
    },
    {
      intro h,
      cases h with h2 h3,
      intro h4,
      cases h4 with h5 h6,
      {
        contradiction,
      },
      {
        contradiction,
      }
    }
  end

lemma Kleene12: ∀ (A B:Prop), (A → B) → ¬ B → ¬ A:=
  assume A B,
  begin
    intros h1 h2 h3,
    have h4:= h1 h3,
    contradiction, 
  end

lemma Kleene3: ∀ (A B C:Prop), (A → B → C) ↔ (B → A → C):=
  assume A B C,
  begin
    split,
    {
      intros h h2 h3,
      exact  h h3 h2,
    },
    {
      intros h h2 h3,
      exact h h3 h2, 
    }
  end

lemma Kleene4and5: ∀ (A B C:Prop), A ∧ B → C ↔ A → B → C:=
  assume A B C,
  begin
    split,
    {  --Kleene 5
      intros h h2 h3,
      apply h,
      exact ⟨ h2, h3⟩, 
    },
    { -- Kleene 4
      intros h h2,
      cases h2 with h3 h4,
      exact h h3 h4, 
    }
  end

lemma Kleene13: ∀ (A B:Prop), (A → ¬ B) → B → ¬ A:=
  assume A B,
  begin
    intros h h2 h3,
    exact h h3 h2, 
  end


lemma triplenegation: ∀ (P:Prop), ¬¬¬ P ↔ ¬ P:= 
  assume P,
  begin 
    split,
    {
      intros h h2, 
      have h3:= double_negate P h2,
      contradiction,
    },
    {
      intro h,
      exact  double_negate (¬ P) h,
    }
  end 

lemma Kleene22: ∀ (A B C:Prop), (A → B → C) → ¬¬ A → ¬¬ B → ¬¬ C:=
  assume A B C,
  begin
    intros h h2 h3,
    have hcopy:= h, 
    rw Kleene3 at h,
    have h4:= Kleene12 B (A → C) h, 
    have h5: B → (¬¬ A) → ¬¬ C:=
      begin
        intros h6 h7, 
        have h8:= h h6, 
        have h9:= Kleene12 A C h8,
        have h10:= Kleene12 (¬ C) (¬ A) h9 h7,
        exact h10,
      end,
    have h6: B → ¬¬ C:=
      begin
        intro h7,
        exact h5 h7 h2, 
      end,
    have h7:= Kleene13 B (¬C) h6, 
    have h8:= Kleene13 (¬ C)  (¬¬ B),
    rw triplenegation at h8, 
    exact h8 h7 h3, 
  end

lemma notnot_imp: ∀ (P Q:Prop), (P → Q) → ¬¬ P → ¬¬ Q:=
  assume P Q,
  begin
    intro h,
    have h2:= Kleene12 P Q h, 
    have h3:= Kleene12 (¬Q) (¬P)  h2,
    exact h3,
  end

lemma iffdef: ∀ (P Q:Prop),  (P ↔ Q) ↔  (P → Q) ∧ (Q → P):=
  assume P Q,
  begin
    split,
    {
      intro h20,
      rw h20 at *,
      split,
      {
        intro h21,
        exact h21,
      },
      {
        intro h21,
        exact h21, 
      }
    },
    {
      intro h20,
      cases h20 with h21 h22, 
      split,
      {
        exact h21,
      },
      {
        exact h22,
      } 
    }
end 

lemma push_double_negationNF: ∀ (A B: Prop), (¬¬ (A → B)) → (¬¬ A) → ¬¬ B:=
  -- Kleene23  
  assume A B,
  begin 
    have h2: (A → B)→ (A→ B):=
      begin
        intro h,
        exact h, 
      end,
    exact Kleene22 (A → B) A B h2, 
  end 

lemma notnot_imp2way: ∀ (P Q:Prop), ¬¬(P → Q) ↔ ¬¬ P → ¬¬ Q:=
  assume P Q,
  begin
    split,
    {
      have h4:= notnot_imp P Q,
      have h5:= notnot_imp (P → Q) (¬¬ P → ¬¬ Q) h4, 
      intro h6,
      have h7:= h5 h6,
      have h8:= push_double_negationNF (¬¬ P)(¬¬ Q) h7,
      rw triplenegation at h8,
      rw triplenegation at h8,
      exact h8,
    },
    {
      intros h h4,
      apply h,
      {
        intro h5,
        apply h4,
        intro h6,
        contradiction,
      },
      {
        intro h5,
        apply h4,
        intro h6,
        exact h5,
      }
    }
  end

lemma notnot_forall{M:Type}: ∀ (P: M → Prop), (¬¬ ∀ (x:M), P x) → ∀ (x:M), ¬¬ P x:=
  -- credit: Troestra 344, p. 8 
  assume P,
  begin
    intros h t,
    intro h2,
    have h3:  ¬ ∀ (x:M), P x:=
      begin
        intro h4,
        specialize h4 t,
        contradiction,
      end,
    contradiction, 
   end

lemma notnot_and: ∀ (P Q:Prop), (¬¬ (P ∧ Q)) ↔ ((¬¬ P) ∧ ¬¬ Q):=
  assume P Q,
  begin
    split,
    {
      intro h,
      split,
      {
        intro h2,
        apply h,
        intro h3,
        cases h3 with h4 h5,
        contradiction,
      },
      {
        intro h2,
        apply h,
        intro h3,
        cases h3 with h4 h5,
        contradiction,
      }
    },
    {
      intro h,
      cases h with h2 h3,
      intro h4,
      have h5: P → Q → P ∧ Q:=
        begin
          intros h6 h7,
          exact ⟨ h6, h7⟩,
        end,
      have h6:= notnot_imp P (Q → P ∧ Q) h5 h2,
      have h7:= push_double_negationNF Q (P ∧ Q) h6 h3,
      contradiction, 
    }
  end

lemma notnot_iff: ∀ (P Q:Prop), ¬¬ (P ↔ Q) → (¬¬ P ↔ ¬¬ Q):=
  assume P Q, 
  begin
    intros h,
    rw iffdef, 
    rw iffdef at h,
    have h3:= notnot_and (P → Q) (Q → P),
    rw h3 at h, 
    cases h with h4 h5,
    split,
    {
      have h6:= notnot_imp P Q, 
      have h7:= double_negate ((P → Q) → ¬¬P → ¬¬Q) h6,
      have h8:= push_double_negationNF P Q h4,
      exact h8,
    },
    {
      have h6:= notnot_imp Q P, 
      have h7:= double_negate ((Q → P) → ¬¬Q → ¬¬P) h6,
      have h8:= push_double_negationNF Q P h5,
      exact h8,
    }
  end

lemma notnot_iff_2way: ∀ (P Q:Prop), ¬¬ (P ↔ Q) ↔ (¬¬ P ↔ ¬¬ Q):=
  assume P Q, 
  begin
    split,
    { exact notnot_iff P Q,
    },
    {
      intro h,
      rw iffdef,
      rw iffdef at h,
      cases h with h2 h3,
      have h4:= notnot_and (P → Q) (Q → P),
      rw h4,
      split,
      {
        rw notnot_imp2way,
        exact h2,
      },
      {
        rw notnot_imp2way,
        exact h3,
      }
    }
  end

lemma existsnotnot{M:Type}: ∀ (P: M → Prop), (¬¬ ∃ (x:M),¬¬ P x) → ¬¬ ∃ (x:M), P x:=
  assume P,
  begin
   intros h h2,
   apply h,
   intros h3,
   cases h3 with c h4,
   rw not_exists at h2,
   have h5:= h2 c,
   contradiction,
  end

lemma pushnotnot: ∀ (P Q A B: Prop),
¬¬(P ∨ Q)→ (P → A) → (Q → B) → ¬¬ (A ∨ B):=
  begin
    intros P Q A B h2 h3 h4,
    have h5: P ∨ Q → A ∨ B:=
      begin
        intros h6,
        cases h6 with h7 h8,
        {
          have h9:= h3 h7,
          left,
          exact h9,
        },
        {
          have h10:= h4 h8,
          right,
          exact h10,
        },
      end,
    have h11:= double_negate (P ∨ Q → A ∨ B) h5,
    have h12:= push_double_negationNF (P ∨ Q)(A ∨ B) h11,
    apply h12,
    exact h2,
  end
 
 
#axioms_all    -- this file is clean