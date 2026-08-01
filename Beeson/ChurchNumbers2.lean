import Dedekind2

variables (M:Type) [Model M] (a b x y z u v w X R W κ μ ℓ : M)
-- using ℓ where the source text has λ because you can't use λ for a variable.

open Model 

lemma issuccessor: ∀ (x y:M), x ∈ ℕℕ → y ∈ ℕℕ → x <ℕ y → ∃(z:M), z ∈ ℕℕ ∧ y = S z:=
  assume x y,
  begin
    intros hx hy h3,
    have h4:= ChurchOrder x y, 
    rw h4 at h3,
    cases h3 with n h5,
    cases h5 with h6 h7,
    have h8:= ChurchAddition_equation x n hx h6,
    rw h8 at h7,
    use x ⊕ n,
    split,
    {
      exact ChurchAdditionMaps M n h6 x hx,
    },
    symmetry,
    exact h7,
  end 

lemma notless0: ∀ (x:M), x ∈ ℕℕ → ¬ x <ℕ ChurchZero:=
  assume x,
  begin
    intros h h3,
    have h4:= issuccessor M x ChurchZero h (zeroN M) h3,
    cases h4 with z h5,
    cases h5 with h6 h7,
    have h8:= successoromitszero M z h6,
    rw sym at h7,
    contradiction,
  end
  
lemma order1: ∀(x y:M), x ∈ ℕℕ → y ∈ ℕℕ → (x = y ∨ x <ℕ y) → x <ℕ S y:=
  assume x y,
  begin
    intros hx hy hor,
    cases hor with h4 h5,
    {
      rw h4,
      have h6:= ChurchOrder y (S y),
      rw h6,
      use ChurchZero,
      rw ChurchAddition_equation y ChurchZero hy (zeroN M),
      rw ChurchZero_equation y hy,
      simp,
      exact zeroN M,
    },
    {
      rw ChurchOrder x y at h5,
      cases h5 with n h6,
      cases h6 with h7 h8,
      rw ChurchOrder x (S y), 
      use (S n),
      rw ChurchAddition_equation x (S n) hx (successorN M n h7),
      rw h8,
      simp,
      exact successorN M n h7,
    }
  end

lemma xlessthansx: ∀ (x:M), x ∈ ℕℕ → x <ℕ S x:=  
  begin
    intros x h,
    have h2: x = x ∨ x <ℕ x:=
      begin
        left,
        refl,
      end,
    exact order1 M x x h h h2, 
  end

lemma zerosmall: ∀(x:M), x ∈ ℕℕ → ¬ x = ChurchZero → ChurchZero <ℕ x:=
  begin
    have base: ChurchZero ∈ Z_zerosmall M:=
      begin
        rw Z_zerosmall_members,
        split,
        {
          exact zeroN M,
        },
        {
          intros h3,
          contradiction,
        }
      end,
    have step: ∀ (x:M), x ∈ Z_zerosmall M → S x ∈ Z_zerosmall M:=
      assume x,
      begin
        intro h,
        rw Z_zerosmall_members,
        rw Z_zerosmall_members at h,
        cases h with h2 h3,
        split,
        {
          exact successorN M x h2,
        },
        {
          intro h4,
          have h5:= order1 M ChurchZero x (zeroN M) h2,
          apply h5,
          have h6:= decidable0 M x h2,
          cases h6 with h7 h8,
          {
            rw h7,
            left, 
            refl,
          },
          {
            right, 
            exact h3 h8,
          }
        }
      end,
    intros n hn,
    rw N_members at hn,
    specialize hn (Z_zerosmall  M),
    have h3:= hn (and.intro base step),
    rw Z_zerosmall_members at h3,
    exact h3.right, 
  end 

lemma nonzeroisChurchSuccessor: ∀ (n:M), n ∈ ℕℕ → ¬ n = ChurchZero → ∃ (m:M), m ∈ ℕℕ ∧ n = S m:=
  assume n,
  begin
    intros hn h3,
    have h4:= zerosmall M n hn h3,
    have h5:= issuccessor M ChurchZero n (zeroN M) hn h4,
    exact h5,
  end

lemma order2: ∀ (x y:M), x ∈ ℕℕ → y ∈ ℕℕ → x <ℕ y → S x <ℕ y ∨ S x = y:=
  assume x y,
  begin
    intros hx hy h3,
    rw ChurchOrder x y at h3,
    cases h3 with p h4,
    cases h4 with h5 h6,
    rw ChurchSuccessorShift M p h5 x hx at h6,
    have h7:= decidable0 M p h5,
    cases h7 with h8 h9,
    { 
      rw h8 at *,
      rw ChurchZero_equation (S x) (successorN M x hx) at h6,
      right,
      exact h6,
    },
    {
      have h10:= issuccessor M,
      have h11:= nonzeroisChurchSuccessor M p h5 h9,
      cases h11 with m h12,
      cases h12 with h13 h14,
      rw h14 at *,
      left,
      rw ChurchOrder (S x) y,
      use m,
      exact ⟨ h13, h6⟩, 
    }
  end

lemma transitivity: ∀ (x y z:M), x ∈ ℕℕ → y ∈ ℕℕ → z ∈ ℕℕ → x <ℕ y → y <ℕ z → x <ℕ z:=
  assume x y z,
  begin
    intros hx hy hz hxy hyz,
    rw ChurchOrder x y at hxy,
    rw ChurchOrder y z at hyz,
    cases hxy with p h3,
    cases hyz with q h4,
    cases h3 with h5 h6,
    cases h4 with h7 h8,
    rw ChurchOrder x z,
    use S p ⊕ q,
    split,
    { 
      have h9:= ChurchAdditionMaps M q h7  (S p) (successorN M p h5),
      exact h9,
    },
    {
      rw← h8,
      rw← h6,
      rw← ChurchAddition_equation (S p) q (successorN M p h5) h7,
      rw ChurchAdditionAssociative M (S p) (successorN M p h5) x (S q) hx (successorN M q h7),
    }
  end

lemma trichotomy1: ∀ (x:M), x ∈ ℕℕ → ∀(y:M), y ∈ ℕℕ → x <ℕ y ∨ x = y ∨ y <ℕ x:=
  begin
    have base: ChurchZero ∈ Z_trichotomy1 M:=
      begin
        rw Z_trichotomy1_members,
        split,
        {
          exact zeroN M,
        },
        {
          intros y hy,
          have h3:= zerosmall M y hy,
          have h4:= decidable0 M y hy,
          cases h4 with h5 h6,
          {
            right, left,
            symmetry,
            exact h5,
          },
          {
            have h7:= h3 h6,
            left,
            exact h7,
          }
        }
      end,
    have step: ∀ (x:M), x ∈ Z_trichotomy1 M → S x ∈ Z_trichotomy1 M:=
      assume x,
      begin
        rw Z_trichotomy1_members,
        rw Z_trichotomy1_members,
        intro h,
        cases h with hx h3,
        split,
        {
          exact successorN M x hx,
        },
        {
          intros y hy,
          have h4:= h3 y hy,
          cases h4 with h5 h6,
          {
            have h7:= order2 M x y hx hy h5,
            cases h7 with h8 h9,
            {
              left,
              exact h8,
            },
            {
              right,left,
              exact h9,
            }
          },
          {
            cases h6 with h7 h8,
            { 
              rw h7 at *,
              have h9:= xlessthansx M y hx, 
              right,
              right,
              exact h9,
            },
            { 
              have h13:= xlessthansx M x hx,
              have h14:= transitivity M y x (S x) hy hx (successorN M x hx) h8 h13,
              right,
              right,
              exact h14,
            } 
          }
        }
      end,
    intros n hn,
    rw N_members at hn,
    specialize hn (Z_trichotomy1  M),
    have h3:= hn (and.intro base step),
    rw Z_trichotomy1_members at h3,
    exact h3.right, 
  end 

lemma lessthansuccessorN: ∀(x y:M),x ∈ ℕℕ → y ∈ ℕℕ → (∀ (u:M), u ∈ ℕℕ →  S u = S x →  u=x) →
  (y <ℕ S x ↔ y <ℕ x ∨ y = x):=
  assume x y,
  begin
    intros hx hy hnds,
    split,
    {
      intro h3,
      rw ChurchOrder y (S x) at h3,
      cases h3 with p h4,
      cases h4 with h5 h6,
      rw ChurchAddition_equation y p hy h5 at h6,
      have h7:= ChurchAdditionMaps M p h5 y hy,
      have h8:= hnds (y ⊕ p) h7 h6,
      have h9:= decidable0 M p h5,
      cases h9 with h10 h11,
      {
        rw h10 at *,
        rw ChurchZero_equation y  hy at h8,
        rw h8 at *,
        right,
        refl, 
      },
      {
        left,
        have h12:= nonzeroisChurchSuccessor M p h5 h11,
        cases h12 with m h13,
        cases h13 with h14 h15,
        rw ChurchOrder y x,
        use m,
        rw h15 at *,
        exact ⟨ h14, h8⟩, 
      }
    },
    {
      intros h3,
      cases h3 with h4 h5,
      {
        have h6:= xlessthansx M x hx,
        have h7:= transitivity M y x (S x) hy hx (successorN M x hx) h4 h6,
        exact h7,
      },
      {
        rw h5 at *,
        exact xlessthansx M x hx,
      }
    }
  end

lemma markov: ∀ (X:M), X ∈ FINITE M → (¬¬ ∃ (u:M), u ∈ X) → ∃ (u:M), u ∈ X:=
  assume X,
  begin
    intros hX,
    have h:= empty_or_inhabited M X hX, 
    cases h with h3 h4,
    {
      rw h3 at *,
      intros h2,
      have h5: ¬ ∃ (u:M), u ∈ Λ:=
        begin
          intros h6,
          cases h6 with u h7,
          have h8:= emptyset_axiom u,
          contradiction,
        end,
      contradiction,
    },
    {
      intros h9,
      exact h4,
    }
  end

lemma trichotomyonS: ∀ (P:M), P ⊆ ℕℕ → 
 (∀ (x:M), x ∈ ℕℕ → S x ∈ P  → x ∈ P) →
 (∀ (x y:M), (x ∈ P → y ∈ P → (y <ℕ S x ↔ y <ℕ  x ∨ y = x))) →
 (∀ (y:M), y∈ P → ∀(x:M), x ∈ P → ¬ (x <ℕ y ∧ y <ℕ x) ∧ ¬ (y <ℕ y)):=
  assume P,
  begin
    intros hp h1 h2,
    have  base: ChurchZero ∈ Z_trichotomyonS M P:=
      begin
        rw Z_trichotomyonS_members,
        split,
        {
          exact zeroN M,
        },
        {
          intros h20 x hx,
          split,
          {
            intro h4,
            cases h4 with h5 h6,
            have h7:= member_subset M P ℕℕ x hp hx,
            have h8:= notless0 M x h7,
            contradiction,
          },
          {
            intro h4,
            have h5:= notless0 M ChurchZero (zeroN M),
            contradiction, 
          }
        }
      end,
    have step: ∀ (y:M), y ∈ Z_trichotomyonS M P → S y ∈ Z_trichotomyonS M P:=
      begin
        intros y h4,
        rw Z_trichotomyonS_members at h4,
        rw Z_trichotomyonS_members,
        cases h4 with hy h5,
        split,
        {
          exact successorN M y hy,
        },
        {
          intros hsy x h6,
          have hx:= member_subset M P ℕℕ x hp h6,
          have h7:= h1 y hy hsy,
          split,
          { 
            intro h8,
            cases h8 with h9 h10,
            have h11:= (h2 y x h7 h6).mp h9,
            have h12:∃ (j:M), j ∈ ℕℕ ∧ x ⊕ j = y:=
              begin
                cases h11 with h13 h14,
                { 
                  rw ChurchOrder x y at h13,
                  cases h13 with n h15,
                  use S n,
                  exact ⟨ successorN M n h15.left, h15.right⟩, 
                },
                {
                  rw h14,
                  use ChurchZero,
                  rw ChurchZero_equation y hy,
                  simp,
                  exact zeroN M, 
                }
              end,
            cases h12 with j h13,
            cases h13 with h14 h15,
            rw ChurchOrder (S y) x at h10,
            cases h10 with ℓ h16,
            cases h16 with h17 h18,
            rw← h18 at h15,
            rw ChurchAdditionAssociative M (S ℓ) (successorN M ℓ h17) (S y) j (successorN M y hy) h14 at h15,
            rw← ChurchSuccessorShift M (S ℓ ⊕ j) at h15,
            {
              have h19: y <ℕ y:=
                begin
                  rw ChurchOrder y y,
                  use (S ℓ) ⊕ j,
                  split,
                  {
                   have h20:= ChurchAdditionMaps M j h14 (S ℓ) (successorN M ℓ h17),
                   exact h20,
                  },
                  {
                    exact h15,
                  }
                end,
              have h20:= h5 h7 x h6,
              cases h20 with h21 h22,
              contradiction,
            },
            {
              have h23:= ChurchAdditionMaps M j h14 (S ℓ) (successorN M ℓ h17), 
              exact h23,
            },
            {
              exact hy,
            }
          },
          {
            have h8:= h2 y (S y) h7 hsy,
            intro h9,
            rw h8 at h9,
            have h10:= xlessthansx M y hy,
            have h11:= h5 h7 (S y) hsy,
            cases h11 with h12 h13,
            apply h12,
            split,
            {
              cases h9 with h14 h15,
              {
                exact h14,
              },
              {
                rw h15 at *,
                simp at h12,
                contradiction,
              }
            },
            {
              have h15:= xlessthansx M y hy,
              exact h15,
            }
          }
        }
      end,
    intros n hnp,
    have hn:= member_subset M P ℕℕ n hp hnp,
    rw N_members at hn,
    specialize hn (Z_trichotomyonS  M P),
    have h30:= hn (and.intro base step),
    rw Z_trichotomyonS_members at h30,
    exact h30.right hnp, 
  end

lemma S1: ChurchZero ∈ (STEM:M) ∧ ∀(u:M), u ∈ ℕℕ → u ∈ STEM → (∀ (v:M), v ∈ ℕℕ → S u = S v → u = v)→ S u ∈ STEM:=
  begin
    split,
    { 
      rw StemDefinition,
      split,
      { 
        exact zeroN M,
      },
      { 
        intros w h2 h3,
        exact h2,
      }
    },
    {
      intros u hu h2 h3,
      rw StemDefinition,
      rw StemDefinition at h2,
      split,
      {
        exact successorN M u h2.left,
      },
      { intros w h4 h5,
        have h7:= h2.right w h4 h5,
        have h6:= h5 u hu h7 h3,
        exact h6,
      }
    }
  end

lemma SN: (STEM:M) ⊆ ℕℕ:=
  begin
    rw subset_definition,
    intros t h,
    rw StemDefinition at h,
    exact h.left,
  end

lemma Soneone: ∀(u v:M), u ∈ STEM  → S u ∈ STEM → v ∈ ℕℕ  → S u = S v → u = v:=
  assume u v,
  begin 
    have h3:= S1 M,
    cases h3 with h4 h5,
    intros hu hsu hv huv,
    have h6:= member_subset M STEM ℕℕ u (SN M) hu,
    have h8:= h5 u h6 hu,
    have h9:= member_subset M STEM ℕℕ u (SN M) hu,
    have h10: ChurchZero ∈ Z_Soneone M:=
      begin
        rw Z_Soneone_members,
        split,
        {
          exact zeroN M,
        },
        {
          intros p q hp hq h,
          have h2:= successoromitszero M p hp,
          rw sym at h2,
          contradiction,
        }
      end,
    have h11: Z_Soneone M ⊆ ℕℕ:=
      begin
        rw subset_definition,
        intros t h,
        rw Z_Soneone_members at h,
        exact h.left,
      end,
    have h12: ∀ (a:M), a ∈ ℕℕ → a ∈ Z_Soneone M → (∀ (b:M), b ∈ ℕℕ → S a = S b → a = b) → S a ∈ Z_Soneone M:=
      begin
        intros a h100 ha h,
        rw Z_Soneone_members,
        split,
        {
          have h30:= member_subset M (Z_Soneone M) ℕℕ a h11 ha,
          have h31:= successorN M a h30,
          exact h31,
        },
        { 
          intros p q hp h34 h35 h36,
          have h37:= h p hp h35,
          rw← h37 at h36,
          have h38:= h q h34 h36,
          rw← h38,
          rw← h37,
        }
      end,
    have h13: STEM ⊆ Z_Soneone M:=
      begin
        rw subset_definition,
        intros t h22,
        rw StemDefinition at h22,
        cases h22 with h23 h24,
        have h25:= h24 (Z_Soneone M) h10,
        apply h25, 
        exact h12, 
      end,
    have h40:= member_subset M STEM (Z_Soneone M) (S u) h13 hsu,
    rw Z_Soneone_members at h40,
    cases h40 with h41 h42,
    have h43:= h42 u v h6 hv (refl (S u)) huv,
    exact h43,
  end

lemma Spred: ∀ (y:M), y ∈ ℕℕ → S y ∈ STEM → y ∈ STEM:=
  begin
    set X:= Z_Spred M  with h50,
    have h: STEM ⊆ X:=
      begin
        rw subset_definition,
        intros x h3,
        rw StemDefinition at h3,
        cases h3 with h7 h8,
        specialize h8 X,
        have h9:= (S1 M).left,
        have h10: ChurchZero ∈ X:=
          begin
            rw h50,
            rw Z_Spred_members,
            split,
            {
              exact h9,
            },
            {
              left,
              refl,
            }
          end,
        apply h8,
        {
          exact h10,
        },
        {
          intros z hz hzx h11,
          rw h50 at hzx,
          rw Z_Spred_members at hzx,
          cases hzx with h12 h13,
          rw h50,
          rw Z_Spred_members,
          rw and_comm,
          split,
          {
            right,
            use z,
            simp,
            exact h12,
          },
          {
            have h14:= S1 M,
            cases h14 with h15 h16,
            have h20:= h16 z hz h12 h11,
            exact h20,
          }
        }
      end, 
    intros x hx hsx,
    have h60:= member_subset M STEM X (S x) h hsx,
    rw h50 at h60,
    rw Z_Spred_members at h60,
    cases h60 with h61 h62,
    cases h62 with h63 h64,
    { 
      have h65:= successoromitszero M x hx,
      contradiction,
    },
    {
      cases h64 with y h65,
      cases h65 with h66 h67,
      rw← h66 at h61,
      have h68:= Soneone M y x h67 h61 hx h66,
      rw h68 at *,
      exact h67,
    }
  end 

lemma Sdecidable: ∀ (x:M), x ∈ ℕℕ → ∀ (y:M), y ∈ ℕℕ →  x ∈ STEM → (x = y ∨ ¬ x=y):=
  begin
    have base: ChurchZero ∈ Z_Sdecidable M:=
      begin
        rw Z_Sdecidable_members, 
        split,
        {
          exact zeroN M,
        },
        {
          intros y hy h3,
          have h4:= decidable0 M y hy,
          rw sym at h4,
          exact h4,
        }
      end,
    have step: ∀ (x:M), x ∈ Z_Sdecidable M → S x ∈ Z_Sdecidable M:=
      begin
        intros x h,
        rw Z_Sdecidable_members at h,
        rw Z_Sdecidable_members,
        cases h with h10 h11,
        split,
        {
          exact successorN M x h10,
        },
        {
          intros y hy hsx,
          have hycopy:= hy,
          have h14:= decidable0 M y hy,
          cases h14 with h15 h16,
          {
            rw h15 at *, 
            rw StemDefinition at hsx,
            cases hsx with h17 h18,
            have h16:= decidable0 M (S x) h17,
            exact h16,
          },
          { 
            have h17:= nonzeroisChurchSuccessor M y hy h16,
            cases h17 with q h18,
            cases h18 with h19 h20,
            rw h20 at *,
            have h21:= Spred M x h10 hsx,
            have h23:= Soneone M x q h21 hsx h19,
            have h24:= h11 q h19 h21,
            cases h24 with h25 h26,
            {
              rw h25,
              left,
              refl,
            },
            {
              right,
              intro h27,
              have h28:= h23 h27,
              contradiction,
            }
          }
        }
      end,
    intros n hn,
    rw N_members at hn,
    specialize hn (Z_Sdecidable  M),
    have h3:= hn (and.intro base step),
    rw Z_Sdecidable_members at h3,
    exact h3.right, 
  end 

lemma Sinit: ∀ (y:M), y ∈ ℕℕ → ∀ (x:M), x ∈ ℕℕ → y ∈ STEM → x <ℕ y → x ∈ STEM:=
   begin
    have base: ChurchZero ∈ Z_Sinit M:=
      begin
        rw Z_Sinit_members,
        split,
        {
          exact zeroN M,
        },
        {
          have h3:= S1 M,
          cases h3 with h4 h5,
          intros x hx h4 h7,
          have h6:= notless0 M x hx,
          contradiction,
        }
      end,
    have step: ∀ (y:M), y ∈ Z_Sinit M → S y ∈ Z_Sinit M:=
      begin
        intros y h,
        rw Z_Sinit_members at h,
        rw Z_Sinit_members,
        cases h with h3 h4,
        split,
        {
          exact successorN M y h3, 
        },
        {
          intros x hx h5 h6,
          have h7:= Spred M y h3 h5,
          have h8: ∀ (u : M), u ∈ ℕℕ → S u = S y → u = y:=
            begin
              intros u hu,
              have h30:= Soneone M y u h7 h5 hu,
              intro h31,
              rw sym,
              rw sym at h31,
              exact h30 h31,
            end,
          have h9:= h4 x hx h7,
          have h10:= lessthansuccessorN M y x h3 hx h8,
          rw h10 at h6,
          cases h6 with h20 h21,
          {
            exact h9 h20,
          },
          {
            rw h21,
            exact h7,
          }
        }
      end,
    intros n hn,
    rw N_members at hn,
    specialize hn (Z_Sinit  M),
    have h3:= hn (and.intro base step),
    rw Z_Sinit_members at h3,
    exact h3.right, 
  end

lemma Smax: ∀(k n:M), k ∈ STEM → n ∈ ℕℕ → ¬ k = n →  S k = S n → ∀ (x:M), x ∈ STEM ↔ x ∈ ℕℕ ∧ (x <ℕ k ∨ x = k):=
  begin
    intros k n hk hn hkn h49,
    set Z:= Z_Smax M k with h50,
    have base: ChurchZero ∈ Z:=
      begin
        have h3:= (S1 M).left,
        have h4:= member_subset M STEM ℕℕ k (SN M) hk,
        have h5:= decidable0 M k h4,
        rw h50,
        rw Z_Smax_members M k,
        split,
        {
          exact h3,
        },
        {
          cases h5 with h6 h7,
          {
            right,
            symmetry,
            exact h6,
          },
          {
            left,
            have h8:= nonzeroisChurchSuccessor M k h4 h7,
            cases h8 with m h9,
            cases h9 with h10 h11,
            rw h11,
            have h12:= ChurchOrder ChurchZero (S m),
            rw  h12, 
            use m,
            split,
            {
              exact h10,
            },
            {
              rw zeroplusx,
              exact successorN M m h10,
            }
          }
        }
      end,
    have step: ∀ (x:M), x ∈ Z_Smax M k → (∀ (u:M), u ∈ ℕℕ → S x = S u → x = u) → S x ∈ Z_Smax M k:=
      begin
        intros x h4 h5,
        rw Z_Smax_members M k at h4,
        cases h4 with h6 h7,
        rw or_comm at h7,
        have h41:= member_subset M STEM ℕℕ x (SN M) h6,
        have h42:= member_subset M STEM ℕℕ k (SN M) hk,
        cases h7 with h8 h9,
        {
          rw h8 at *,
          have h9:= h5 n hn h49,
          contradiction,
        },
        {
          have h10 := order2 M x k h41 h42 h9,
          rw Z_Smax_members M k,
          rw and_comm,
          split,
          {
            exact h10,
          },
          {
            have h11:= (S1 M).right x h41 h6 h5,
            exact h11,
          }
        }
      end,
    have h60: STEM ⊆ Z:=
      begin
        rw subset_definition,
        intros t h61,
        rw StemDefinition at h61,
        cases h61 with h62 h63,
        specialize h63 Z,
        apply h63,
        {
          exact base,
        },
        {
          intros u hu h64 h65,
          rw← h50 at step,
          have h66:= step u h64 h65,
          exact h66,
        }
      end,
    intro x,
    split,
    {
      intro h,
      have  h30:= member_subset M STEM ℕℕ x (SN M) h,
      have h31:= member_subset M STEM Z x h60 h,
      rw h50 at h31,
      rw Z_Smax_members M x at h31,
      exact ⟨ h30, h31.right⟩,
    },
    {
      intros h,
      cases h with h30 h31,
      have h40:= member_subset M STEM ℕℕ k (SN M) hk,
      cases h31 with h32 h33,
      {
        have h34:= Sinit M k h40 x h30 hk h32,
        exact h34,
      },
      {
        rw h33 at *,
        exact hk,
      }
    }
  end

lemma knotlessthank:  ∀(k n:M), k ∈ STEM → n ∈ ℕℕ → ¬ k = n →  S k = S n → ¬ k <ℕ k:=
  assume k n,
  begin
    intros hk hn hnk hsnk,
    have hkn := member_subset M STEM ℕℕ k (SN M) hk,
    set X:= STEM - Z_knotlessthank M k with h50,
    have h3: STEM ⊆ X:=
      begin
        rw subset_definition,
        intros x hx,
        rw StemDefinition at hx,
        cases hx with h3 h4,
        specialize h4 X,
        apply h4,
        {
          rw h50,
          rw minus_members,
          split,
          {
            exact (S1 M).left,
          },
          {
            intros h5,
            rw Z_knotlessthank_members M k at h5,
            cases h5 with h6 h7,
            have h8:= notless0 M k hkn,
            contradiction,
          }
        },
        {
          intros u hu h20 h21,
          rw h50,
          rw minus_members,
          rw h50 at h20,
          rw minus_members at h20,
          cases h20 with h23 h22,
          split,
          {
            have h25:= (S1 M).right,
            have h24:= h25 u hu h23 h21,
            exact h24,
          },
          {
            intro h25,
            rw Z_knotlessthank_members M k at h25,
            rw Z_knotlessthank_members M k at h22,
            cases h25 with h26 h27,
            have h28:= lessthansuccessorN M u k hu hkn,
            have h29:k <ℕ S u ↔ k <ℕ u ∨ k = u:=
              begin
                apply h28,
                intros t h30,
                have h31:= h21 t h30,
                intro h32,
                rw sym,
                rw sym at h32,
                exact h31 h32,
              end,
            rw h29 at h27,
            cases h27 with h33 h34,
            {
              exact h22 ⟨ hu, h33⟩, 
            },
            {
              rw← h34 at *,
              have h40:= h21 n hn hsnk,
              contradiction,
            }
          }
        }
      end,
    have h41:= member_subset M STEM X k h3 hk,
    rw h50 at h41,
    rw minus_members at h41,
    cases h41 with h42 h43,
    rw Z_knotlessthank_members M k at h43,
    intros h44,
    exact h43 ⟨ hkn, h44⟩, 
  end

lemma kisunique:  ∀(k n:M), k ∈ STEM → n ∈ ℕℕ → ¬ k = n →  S k = S n →
∀ (x:M), x ∈ STEM → ¬ (x = k) → ∀ (u:M), u ∈ ℕℕ → S u = S x → u = x :=
  assume k n,
  begin
    intros hk hn hkn h4 x h5 h6,
    have h60:= member_subset M STEM ℕℕ k (SN M) hk,
    have h10:= Smax M k n hk hn hkn h4 x,
    have h11:= h10.mp h5,
    cases h11 with h12 h13,
    rw or_comm at h13,
    cases h13 with h14 h15,
    {
      contradiction,
    },
    {
      have h20: ¬ ∃(u:M), u ∈ ℕℕ  ∧ S u = S x ∧ ¬ u = x:=
        begin 
          intro h21,
          cases h21 with u h22,
          rcases h22 with ⟨ h23, h24, h25⟩, 
          rw sym at h25 h24,
          have h16:= Smax M x u h5 h23 h25 h24 k,
          have h17:= h16.mp hk,
          cases h17 with h18 h19,
          rw or_comm at h19,
          cases h19 with h26 h27,
          {
            rw sym at h26,
            contradiction,
          },
          {
            have h28:= transitivity M k x k h18 h12 h18 h27 h15,
            have h29:= knotlessthank M k n hk hn hkn h4,
            contradiction,
          }
        end,
      have h21: ∀ (u:M),(u ∈ ℕℕ → S u = S x → ¬¬ u = x):=
        begin
          intros u hu h22 h23,
          have h24: ∃ (u : M), u ∈ ℕℕ ∧ S u = S x ∧ ¬u = x :=
            begin
              use u,
              exact ⟨ hu, h22, h23⟩, 
            end,
          contradiction,
        end,
      have h30: ∀ (u:M),(u ∈ ℕℕ → S u = S x →  u = x):=
        begin
          intros u hu h22,
          have h24:= h21 u hu h22,
          have h25:= Sdecidable M x h12 u hu h5,
          cases h25 with h26 h27,
          {
            symmetry,
            exact h26,
          },
          {
            rw sym at h27,
            contradiction,
          }
        end,
      exact h30,
    }
  end

lemma Strichotomy:  ∀(k n:M), k ∈ STEM → n ∈ ℕℕ → ¬ k = n →  S k = S n →
∀ (x y:M), x ∈ STEM → y ∈ STEM →  ¬ (x <ℕ y ∧ y <ℕ x) ∧ ¬ (y <ℕ y):=
  begin
    intros k n  hk hn hkn h40,
    intros x y hx hy,
    have h3:= trichotomyonS M STEM (SN M),
    apply h3,
    { 
      intros p hp, 
      have h4:= Spred M p hp,
      exact h4,
    },
    { 
      intros p q hp hq,
      have hpN:= member_subset M STEM ℕℕ p (SN M) hp,
      have hqN:= member_subset M STEM ℕℕ q (SN M) hq,
      have h6:= member_subset M STEM ℕℕ k (SN M) hk,
      have h3:= Sdecidable M p hpN k h6 hp,
      cases h3 with h10 h11,
      {
         rw h10 at *,
        split,
        {      
          have h12:= (Smax M k n hk hn hkn h40 q).mp hq,
          cases h12 with h13 h14,
          intro h15,
          exact h14, 
        },
        {
          have h12:= xlessthansx M k h6,
          intro h13,
          cases h13 with h14 h15,
          {
            have h16:= transitivity M q k (S k) hqN h6 (successorN M k h6) h14 h12,
            exact h16,
          },
          {
            rw h15 at *,
            exact h12,
          }
        }
      },
      {
        have h20:= kisunique M k n hk hn hkn h40 p hp h11,
        have h21:= lessthansuccessorN M p q hpN hqN h20,
        exact h21,
      }
    },
    {
      exact hy,
    },
    {
      exact hx,
    }
  end


lemma nneqzero: ∀(k n:M), k ∈ STEM → n ∈ ℕℕ → ¬ k = n →  S k = S n → ¬ (n = ChurchZero):=
  begin
    intros k n hks hn hkn h4 h5,
    rw h5 at *,
    have h6:= (S1 M).left,
    have h20:= member_subset M STEM ℕℕ k (SN M) hks,
    rw sym at hkn h4,
    have h7:= (Smax M ChurchZero k h6 h20 hkn h4 k).mp hks,
    cases h7 with h8 h9,
    cases h9 with h10 h11,
    {
      have h12:= notless0 M k h8,
      contradiction,
    },
    {
      rw sym at h11,
      contradiction,
    }
  end

lemma L1:  ∀(k n:M), k ∈ STEM → n ∈ ℕℕ → ¬ k = n →  S k = S n → ( n ∈ LOOP n ∧ ∀ (x:M),x ∈ LOOP n → S x ∈ LOOP n):=
  assume  k n hk hn hkn h4,
  begin
    split,
    {
      rw LoopDefinition,
      split,
      {
        exact hn,
      },
      {
        intros w h5 h6,
        exact h5,
      }
    },
    {
      intros x h5,
      rw LoopDefinition at h5,
      rw LoopDefinition,
      cases h5 with h6 h7,
      split,
      {
        exact successorN M x h6,
      },
      {
        intros w h8 h9,
        have h10:= h7 w h8 h9,
        exact h9 x h10,
      }
    }
  end

lemma LN:  ∀(k n:M), k ∈ STEM → n ∈ ℕℕ → ¬ k = n →  S k = S n →   LOOP n ⊆ ℕℕ :=
  assume k n hk hn hkn h40,
  begin
    rw subset_definition,
    intros t h3,
    rw LoopDefinition at h3,
    cases h3 with h4 h5,
    have h6:= h5 ℕℕ hn,
    apply h6,
    intros u h7,
    exact successorN M u h7,
  end

lemma LcapS1: ∀(k n:M), k ∈ STEM → n ∈ ℕℕ → ¬ k = n →  S k = S n → ∀ (j:M), j ∈ STEM → ¬ j ∈ LOOP n:=
  assume k n hk hn hkn h40,
  begin
    have h30:= nneqzero M k n hk hn hkn h40, 
    have h7:= L1 M k n hk hn hkn h40,
    cases h7 with h8 h9,
    have base: ChurchZero ∈ Z_LcapS1 M k n:=
      begin
        rw Z_LcapS1_members M k n,
        split,
        {
          exact zeroN M,
        },
        {
          intros h h3,
          have h4:= LoopDefinition ChurchZero n,
          rw h4 at h3,
          cases h3 with h4 h5,
          specialize h5 (LOOP n - single ChurchZero),
          have h6: n ∈ LOOP n - single ChurchZero:=
            begin
              rw minus_members,
              rw singleton1,
              exact ⟨ h8, h30 ⟩, 
            end,
          have h10:= h5 h6,
          have h11: ∀ (u : M), u ∈ LOOP n - single ChurchZero → S u ∈ LOOP n - single ChurchZero:=
            begin
              intros u h12,
              rw minus_members,
              rw minus_members at h12,
              cases h12 with h13 h14,
              split,
              {
                exact h9 u h13,
              },
              {
                rw singleton1,
                have h15:= successoromitszero M u,
                have h17:= (LN M) k n hk hn hkn h40,
                have h16:=  member_subset M (LOOP n)  ℕℕ u h17 h13,
                exact h15 h16,
              }
            end,
          have h12:= h10 h11,
          rw minus_members at h12,
          cases h12 with h13 h14,
          rw singleton1 at h14,
          contradiction,
        }
      end,
    have step: ∀ (j:M), j ∈ Z_LcapS1 M k n → S j ∈ Z_LcapS1 M k n:=
      assume j,
      begin
        rw Z_LcapS1_members M k n,
        rw Z_LcapS1_members M k n,
        intro h,
        cases h with h20 h21,
        split,
        {
          exact successorN M j h20,
        },
        {
          intro h210,
          have h22:= Spred M j h20 h210,
          have h23:= Soneone M j n h22 h210 hn,
          have h24:= h21 h22,
          have h25: ¬ j = n:=
            begin
              intro h26,
              rw h26 at *,
              contradiction,
            end,
          have h26: ¬ S j = S n:=
            begin
              intro h27,
              exact h25 (h23 h27),
            end,
          set Z:= LOOP n - single (S j) with h50,
          have h27: LOOP n ⊆ Z:=
            begin
              rw subset_definition,
              intro t,
              intro h28,
              rw LoopDefinition at h28,
              cases h28 with h29 h30,
              specialize h30 Z,
              apply h30,
              {
                rw h50,
                rw minus_members,
                split,
                {
                  exact h8,
                },
                {
                  rw singleton1,
                  intro h31,
                  rw← h31 at h210,
                  have h32:= kisunique M k n hk hn hkn h40 n h210,
                  rw sym at hkn,
                  have h34:= member_subset M STEM ℕℕ k (SN M) hk,
                  have h33:= h32 hkn k h34 h40,
                  rw sym at h33,
                  contradiction,
                }
              },
              {
                intros x h60,
                rw h50,
                rw h50 at h60,
                rw minus_members,
                rw minus_members at h60,
                rw singleton1 at h60,
                rw singleton1,
                cases h60 with h61 h62,
                have h63:= L1 M k n hk hn hkn h40,
                cases h63 with h64 h65,
                split,
                {
                  exact h65 x h61,
                },
                {
                  have h66: ¬ x = j:=
                    begin
                      intro h67,
                      rw h67 at *,
                      contradiction,
                    end,
                  intro h68,
                  have h69:= Soneone M j x h22 h210,
                  have h70: x ∈ ℕℕ := member_subset M (LOOP n) ℕℕ x (LN M k n hk hn hkn h40) h61,
                  rw sym at h68,
                  rw sym at h66,
                  exact h66 (h69 h70 h68),
                }
              }
            end,
          
          intros h28,
          have h29:= member_subset M (LOOP n) Z (S j) h27 h28,
          rw h50 at h29,
          rw minus_members at h29,
          cases h29 with h30 h31,
          rw singleton1 at h31,
          contradiction,
        }
      end,
    have h70:∀ (j:M), j ∈ ℕℕ → j ∈ Z_LcapS1 M k n:=
      begin
        intros j hj,
        rw N_members at hj,
        specialize hj (Z_LcapS1 M k n),
        have h3:= hj (and.intro base step),
        exact h3, 
      end, 
    intros j h h71,
    have h72:= member_subset M STEM ℕℕ j (SN M) h,
    have h73:= h70 j h72,
    rw Z_LcapS1_members M k n at h73,
    cases h73 with h74 h75,
    exact h75 h h71, 
  end 


lemma LcapS: ∀(k n:M), k ∈ STEM → n ∈ ℕℕ → ¬ k = n →  S k = S n → LOOP n ∩ STEM = Λ:=
  assume k n hk hn hkn h40,
  begin
    rw full_extensionality,
    intro x,
    rw intersection_axiom,
    split,
    {
      intro h3,
      cases h3 with h4 h5,
      have h6:= LcapS1 M k n hk hn hkn h40 x h5,
      contradiction,
    },
    {
      intro h4,
      have h5:=emptyset_axiom x,
      contradiction,
    }
  end

lemma LcupS:∀(k n:M), k ∈ STEM → n ∈ ℕℕ → ¬ k = n →  S k = S n → ℕℕ = (LOOP n ∪ STEM):=
  assume k n hk hn hkn h40,
  begin
    have base: ChurchZero ∈ Z_LcupS M k n:=
      begin
        rw Z_LcupS_members M k n,
        split,
        {
          exact zeroN M,
        },
        {
          rw binary_union_axiom,
          right,
          exact (S1 M).left,
        }
      end,
    have step: ∀(x:M), x ∈ Z_LcupS M k n → S x ∈ Z_LcupS M k n:=
      begin
        intros x h,
        rw Z_LcupS_members M k n at h,
        rw Z_LcupS_members M k n,
        cases h with h3 h4,
        rw binary_union_axiom at h4,
        split,
        {
          exact successorN M x h3,
        },
        {
          rw binary_union_axiom,
          have h20:= LN M k n hk hn hkn h40,
          have h21:= member_subset M (LOOP n) ℕℕ x h20,
          have h12:= L1 M k n hk hn hkn h40,
          cases h12 with h13 h14,
          cases h4 with h5 h6,
          {
            left, 
            exact h14 x h5,
          },
          {
            have h7:= member_subset M STEM ℕℕ k (SN M) hk,
            have h8:= Sdecidable M x h3 k h7 h6,
            cases h8 with h9 h10,
            {
              rw h9 at *,
              left,
              rw h40,
              exact h14 n h13,
            },
            {
              right,
              have h22:= kisunique M k n hk hn hkn h40 x h6 h10,
              simp_rw sym at h22,
              have h23:= (S1 M).right x h3 h6 h22, 
              exact h23,
            }
          }
        }
      end,
    have h30: ℕℕ ⊆ Z_LcupS M k n:=
      begin
        rw subset_definition, 
        intros x hx,
        rw N_members at hx,
        specialize hx (Z_LcupS  M k n),
        have h3:= hx (and.intro base step),
        rw Z_LcupS_members M k n at h3,
        rw Z_LcupS_members M k n,
        exact h3,
      end,
    rw full_extensionality,
    intro x,
    split,
    {
      intro h31,
      have h32:= member_subset M ℕℕ (Z_LcupS M k n) x h30 h31,
      rw Z_LcupS_members M k n at h32,
      exact h32.right,
    },
    {
      intro h31,
      rw binary_union_axiom at h31,
      cases h31 with h32 h33,
      {
        have h34:= LN M k n hk hn hkn h40,
        have h35:= member_subset M (LOOP n) ℕℕ x h34 h32,
        exact h35,
      },
      {
        have h34:= SN M,
        have h35:= member_subset M STEM ℕℕ x h34 h33,
        exact h35,
      }
    }
  end
 
lemma Tail1: ∀(n:M), n ∈ Tail M n:=
  assume n,
  begin
    rw Tail_members,
    right,
    refl,
  end

lemma Tail2: ∀ (n x:M), n ∈ ℕℕ → x ∈ ℕℕ → x ∈ Tail M n → S x ∈ Tail M n:=
  assume n x,
  begin
    intros hn hx h3,
    rw Tail_members M n at h3,
    rw Tail_members M n,
    cases h3 with h4 h5,
    {
      left,
      have h6:= xlessthansx M x hx,
      have h7:= transitivity M n x (S x) hn hx (successorN M x hx) h4 h6,
      exact h7,
    },
    {
      rw h5 at *,
      left,
      exact xlessthansx M n hn,
    }
  end

lemma TailN: ∀ (x n:M), n ∈ ℕℕ → x ∈ Tail M n → x ∈ ℕℕ :=
  assume x n,
  begin
    intros hn h,
    rw Tail_members at h,
    cases h with h3 h4,
    {
      rw ChurchOrder at h3,
      cases h3 with m h5,
      cases h5 with h6 h7,
      have h8:= successorN M m h6,
      have h9:= ChurchAdditionMaps M (S m)  h8 n hn ,
      rw h7 at h9,
      exact h9,
    },
    {
      rw h4,
      exact hn,
    }
  end

lemma Lindependent:  ∀(k n:M), k ∈ STEM → n ∈ ℕℕ → ¬ k = n →  S k = S n → LOOP n = ℕℕ - STEM:=
  assume k n hk hn hkn h40,
  begin
    have h3:= LcupS M k n hk hn hkn h40,
    rw h3,
    rw full_extensionality,
    intro t,
    rw minus_members,
    rw binary_union_axiom,
    split,
    {
      intro h4,
      split,
      {
        left,
        exact h4,
      },
      {
        have h5:= LcapS M k n hk hn hkn h40,
        rw full_extensionality at h5,
        specialize h5 t,
        rw intersection_axiom at h5,
        have h6:= emptyset_axiom t,
        cases h5 with h7 h8,
        intro h9,
        exact h6 (h7 ⟨ h4, h9⟩ ),
      }  
    },
    {
      intro h10,
      cases h10 with h11 h12,
      cases h11 with h13 h14,
      {
        exact h13,
      },
      {
        contradiction,
      }
    }
  end

theorem annihilation: ∀ (u m:M), u ∈ ℕℕ → m ∈ ℕℕ → u ⊕ m = u → ∀ (X f:M), injection M f X →
  ∀ (x:M), x ∈ X → Ap (Ap m f) x = x:=
  assume u m,
  begin
    intros hu hm hum X f hperm x hx,
    unfold injection at hperm,
    rcases hperm with ⟨honeone, hrel, hf, hdom, hrange⟩,
    have h3: Ap (Ap u f) x = Ap( Ap (u ⊕ m) f) x :=
      begin
        rw hum,
      end,
    have honeonecopy:= honeone,
    unfold oneone at honeonecopy,
    cases honeonecopy with hmaps h10,
    have h4:= doubleiteration M u hu X f m x hf hmaps hm hx,
    rw← h3 at h4,
    have h5:= oneoneiteration M u hu X f hf hrel hdom hrange hmaps honeone,
    rcases h5 with ⟨ h6, h7, h8⟩,
    have h20:= nfFUNC M u hu f hf hrel,
    cases h20 with h21 h22,
    have h9:= Apmaps M X (Ap u f) x h6 h21 hx,
    have h30: Ap (Ap m f) x ∈ X:= 
      begin
         have h40:= oneoneiteration M m hm X f hf hrel hdom hrange hmaps honeone,
         rcases h40 with ⟨ h41, h42, h43⟩,
         have h41copy:= h41,
         unfold maps at h41, 
         rcases h41 with ⟨ h44, h45, h46, h47⟩,
         have h48:= h47 x hx,
         cases h48 with y h49,
         cases h49 with h50 h51,
         have h52:= nfFUNC M m hm f hf hrel,
         cases h52 with h53 h54,
         have h55:= Apmaps M X (Ap m f) x h41copy h53 hx,
         rw FUNC_members at h53,
         have h56:= h53 x y (Ap (Ap m f) x) h51 h55,
         rw← h56,
         exact h50,
      end,
    have h10:= Apmaps M X (Ap u f) ( Ap (Ap m f) x) h6 h21 h30,
    rw h4 at h10,
    -- now use h7 with h9 and h10  to finish 
    unfold oneone at h7,
    rcases h7 with ⟨ h31, h32, h33⟩, 
    have h34:= h32 (Ap (Ap m f) x) x (Ap (Ap u f) x) ⟨ h10, h9, h30⟩,
    exact h34,
  end

lemma mbig1: ∀ (x:M), x ∈ ℕℕ → ¬  x = x ⊕ S ChurchZero  :=
  begin
    intros x hx h,
    rw sym at h,
    have h5:= annihilation M x (S ChurchZero) hx (successorN M ChurchZero (zeroN M)) h,
    set X:= pair (ChurchZero:M)  (S ChurchZero) with h50,
    set f:= pair ‹ (ChurchZero:M), S ChurchZero›  ‹ S ChurchZero, ChurchZero › with h51,
    have h40:= successoromitszero M ChurchZero (zeroN M),
    have hrel: Rel f:=
      begin
        rw Rel_definition,
        intros z h10,
        rw h51 at h10,
        rw pairing_axiom at h10,
        cases h10 with h11 h12,
        {
          use ChurchZero, use S ChurchZero,
          exact h11,
        },
        {
          use S ChurchZero, use ChurchZero,
          exact h12, 
        }
      end,
    have hf: f ∈ FUNC:=
      begin
        rw FUNC_members,
        intros x y z h10 h11,
        rw h51 at h10 h11,
        rw pairing_axiom at h10 h11,
        cases h10 with h12 h13,
        {
          rw ordered_pair_equality at h12,
          rw h12.left at *,
          rw h12.right at *,
          cases h11 with h14 h15,
          {
            rw ordered_pair_equality at h14,
            symmetry,
            exact h14.right,
          },
          {
            rw ordered_pair_equality at h15,
            cases h15 with h16 h17,
            rw sym at h16,
            contradiction,
          }
        },
        {
          rw ordered_pair_equality at h13,
          rw h13.left at *,
          rw h13.right at *,
          cases h11 with h14 h15,
          {
            rw ordered_pair_equality at h14,
            cases h14 with h16 h17,
            contradiction,
          },
          {
            rw ordered_pair_equality at h15,
            symmetry,
            exact h15.right,
          }
        }
      end,
    have h6: injection M f X:=
      begin
        unfold injection,
        repeat{split},
        {
          rw Rel_definition,
          intros z h10,
          rw h51 at h10,
          rw pairing_axiom at h10,
          cases h10 with h11 h12,
          {
            use ChurchZero, use (S ChurchZero),
            exact h11,
          },
          {
            use (S ChurchZero),use ChurchZero,
            exact h12,
          }
        },
        {
          intros x y h10,
          cases h10 with h11 h12,
          rw h51 at h12,
          rw pairing_axiom at h12,
          cases h12 with h13 h14,
          {
            rw ordered_pair_equality at h13,
            rw h13.right,
            rw h50,
            rw pairing_axiom,
            right,
            refl,
          },
          {
            rw ordered_pair_equality at h14,
            rw h14.right,
            rw h50,
            rw pairing_axiom,
            left,
            refl,
          }
        },
        {
          intros x y z h10,
          rcases h10 with ⟨ h11, h12, h13⟩, 
          rw h51 at h12 h13,
          rw pairing_axiom at h12 h13,
          rw ordered_pair_equality at h12 h13,
          rw ordered_pair_equality at h12 h13,
          cases h13 with h14 h15,
          {
            rw h14.left at *,
            rw h14.right at *,
            cases h12 with h16 h17,
            {
              exact h16.right,
            },
            {
              cases h17 with h18 h19,
              rw sym at h18,
              contradiction,
            }
          },
          { rw h15.left at *,
            rw h15.right at *,
            cases h12 with h16 h17,
            {
              cases h16 with h18 h19,
              contradiction,
            },
            {
              exact h17.right,
            }
          }
        },
        {
          intros x hx,
          rw h50 at hx,
          rw pairing_axiom at hx,
          cases hx with h10 h11,
          {
            use S ChurchZero,
            rw h10,
            rw h50,
            rw h51,
            repeat{rw pairing_axiom},
            split,
            {
              right,
              refl,
            },
            {
              left,
              refl,
            } 
          },
          {
            use ChurchZero,
            rw h11,
            rw h50,
            rw h51,
            repeat{rw pairing_axiom},
            split,
            {
              left,
              refl,
            },
            {
              right,
              refl,
            }
          }
        },
        {
          intros x u y h10,
          rcases h10 with ⟨ h11, h12, h13⟩,
          rw h51 at h11 h12,
          rw h50 at h13,
          rw pairing_axiom at h11 h12 h13,
          cases h13 with h14 h15,
          {
            rw h14 at *,
            cases h11 with h16 h17,
            {
              rw ordered_pair_equality at h16,
              simp at h16,
              rw h16 at *,
              cases h12 with h17 h18,
              {
                rw ordered_pair_equality at h17,
                symmetry,
                exact h17.left,
              },
              {
                rw ordered_pair_equality at h18,
                cases h18 with h19 h20,
                contradiction,
              }
            },
            {
              rw ordered_pair_equality at h17,
              cases h17 with h18 h19,
              rw sym at h18,
              contradiction,
            }
          },
          {
            rw h15 at *,
            cases h11 with h16 h17,
            {
              rw ordered_pair_equality at h16,
              cases h16 with h18 h19,
              contradiction,
            },
            {
              rw ordered_pair_equality at h17,
              rw h17.right at *,
              cases h12 with h18 h19,
              {
                rw ordered_pair_equality at h18,
                cases h18 with h20 h21,
                rw sym at h21,
                contradiction,
              },
              {
                rw ordered_pair_equality at h19,
                cases h19 with h20 h21,
                symmetry,
                exact h20,
              }
            }
          }
        },
        {
          intros x y h10,
          cases h10 with h11 h12,
          rw h51 at h11,
          rw h50 at h12,
          rw pairing_axiom at h11 h12,
          cases h12 with h13 h14,
          {
            rw h13 at *, 
            rw h50,
            rw pairing_axiom,
            cases h11 with h15 h16,
            {
              rw ordered_pair_equality at h15,
              left,
              exact h15.left,
            },
            {
              rw ordered_pair_equality at h16,
              right,
              exact h16.left,
            }
          },
          {
            rw h14 at *,
            rw h50,
            rw pairing_axiom,
            cases h11 with h12 h13,
            {
              rw ordered_pair_equality at h12,
              left,
              exact h12.left,
            },
            {
              rw ordered_pair_equality at h13,
              right,
              exact h13.left,
            }
          }
        },
        {
          exact hrel,
        },
        { 
          exact hf,        
        },
        { 
          rw subset_definition,
          intros x h10,
          rw domain_axiom f hrel at h10,
          cases h10 with y h11,
          rw h51 at h11,
          rw pairing_axiom at h11,
          cases h11 with h12 h13,
          {
            rw ordered_pair_equality at h12,
            rw h50,
            rw pairing_axiom,
            left,
            exact h12.left,
          },
          {
            rw ordered_pair_equality at h13,
            rw h50,
            rw pairing_axiom,
            right,
            exact h13.left,
          }
        },
        {
          rw subset_definition,
          intros y h10,
          rw range_axiom f hrel at h10,
          cases h10 with x h11,
          rw h51 at h11,
          rw pairing_axiom at h11,
          cases h11 with h12 h13,
          {
            rw ordered_pair_equality at h12,
            rw h12.right,
            rw h50,
            rw pairing_axiom,
            right,
            refl,
          },
          {
            rw ordered_pair_equality at h13,
            rw h13.right,
            rw h50,
            rw pairing_axiom,
            left,
            refl,
          }
        }
      end,
    have h20: ChurchZero ∈ X:=
      begin
        rw h50,
        rw pairing_axiom,
        left,
        refl,
      end,
    have h21:= h5 X f h6 ChurchZero h20, 
    have h22:= ApOne M f hf hrel,
    rw h22 at *,
    have h23: Ap f ChurchZero = S ChurchZero:=
      begin
        rw full_extensionality,
        intro t,
        have h10:= Ap_members M f ChurchZero t,
        rw h10,
        split,
        {
          intro h11,
          cases h11 with y h12,
          cases h12 with h13 h14,
          rw h51 at h13,
          rw pairing_axiom at h13,
          cases h13 with h15 h16,
          { 
            rw ordered_pair_equality at h15,
            rw h15.right at *,
            exact h14, 
          },
          {
            rw ordered_pair_equality at h16,
            cases h16 with h17 h18,
            rw sym at h17,
            contradiction, 
          }
        },
        {
          intros h11,
          use S ChurchZero,
          split,
          {
            rw h51,
            rw pairing_axiom,
            left,
            refl, 
          },
          {
            exact h11,
          }
        }
      end, 
    have h24: ChurchZero = S ChurchZero:=
      begin
        rw h21 at h23,
        exact h23,
      end,
    have h25:= Church1notequal0 M,
    rw sym at h25, 
    contradiction,
  end

lemma snneqn: ∀ (x:M), x ∈ ℕℕ → ¬ S x = x:=
  assume x hx,
  begin
    have h3: S x = x ⊕ S ChurchZero:=
      begin
        rw ChurchSuccessorShift M ChurchZero (zeroN M) x hx,
        rw ChurchZero_equation,
        exact successorN M x hx,
      end,
    intro h4,
    rw h4 at h3,
    rw sym at h3,
    have h4:= mbig1 M x hx,
    rw sym at h3,
    contradiction,  
  end

lemma mbig2: ∀ (x:M), x ∈ ℕℕ → ¬  x = x ⊕ S (S ChurchZero)  :=
  begin
    intros x hx h,
    rw sym at h,
    set a:= ChurchZero with hadef,
    set b:= S ChurchZero with hbdef,
    set c:= S (S ChurchZero) with hcdef, 
    have ha:= zeroN M,
    have hb:= successorN M a ha,
    have hc:= successorN M b hb,
    have h5:= annihilation M x (S b) hx hc h,
    set X:= (pair a b)  ∪  single c with h50,
    set f:= pair ‹ a,b ›  ‹ b,c › ∪ single ‹ c,a›  with h51,
    have h40:= successoromitszero M a ha,
    rw← hbdef at h40,
    have h41:= successoromitszero M b hb,
    rw hbdef at h41,
    rw← hcdef at h41,
    rw← hadef at h40 h41,
    have h42:=snneqn M b hb,
    rw hbdef at h42,
    rw← hcdef at h42,
    rw← hbdef at h42,
    -- now a,b,c are distinct elements of ℕℕ
    -- We will show they are elements of X
    have haX: a ∈ X:=
      begin
        rw h50,
        rw binary_union_axiom,
        left,
        rw pairing_axiom,
        simp,
      end,
    have hbX: b ∈ X:=
      begin
        rw h50,
        rw binary_union_axiom,
        left,
        rw pairing_axiom,
        simp,
      end,
    have hcX: c ∈ X:=
      begin
        rw h50,
        rw binary_union_axiom,
        right,
        rw singleton1,
      end,
    have hsubset: X ⊆ ℕℕ :=
      begin
        rw subset_definition,
        intros t ht,
        rw h50 at ht,
        rw binary_union_axiom at ht,
        rw singleton1 at ht,
        cases ht with h3 h4,
        {
          rw pairing_axiom at h3,
          cases h3 with h5 h6,
          {
            rw h5,
            exact ha,
          },
          {
            rw h6,
            exact hb,
          }
        },
        {
          rw h4,
          exact hc,
        }
      end,
    have hFUNC: f ∈ FUNC:=
      begin
        rw FUNC_members,
        intros x y z hx hz,
        rw h51 at hx hz,
        rw binary_union_axiom at hx hz,
        rw singleton1 at hx hz,
        rw pairing_axiom at hx hz,
        cases hx with h20 h21,
        {
          cases h20 with h22 h23,
          {
            cases hz with h24 h25,
            {
              cases h24 with h26 h27,
              {
                rw ordered_pair_equality at h26 h22,
                rw h22.right,
                rw h26.right,
              },
              {
                rw ordered_pair_equality at h27 h22,
                cases h27 with h28 h29,
                cases h22 with h30 h31,
                rw h28 at *,
                contradiction,
              }
            },
            {
              rw ordered_pair_equality at h22 h25,
              cases h25 with h26 h27,
              cases h22 with h28 h29,
              rw h26 at *,
              contradiction,
            }
          },
          { 
            cases hz with h30 h31,
            { 
              cases h30 with h32 h33,
              {
                rw ordered_pair_equality at h23 h32,
                cases h32 with h33 h34,
                cases h23 with h35 h36,
                rw h35 at h33,
                contradiction,
              },
              {
                rw ordered_pair_equality at h23 h33,
                rw h33.right,
                rw h23.right,
              }
            },
            {
              rw ordered_pair_equality at h23 h31,
              cases h23 with h34 h35,
              cases h31 with h36 h37,
              rw h36 at h34,
              contradiction,
            }
          }
        },
        {
          cases hz with h38 h39,
          {
            cases h38 with h40 h41,
            {
              rw ordered_pair_equality at h21 h40,
              cases h40 with h41 h42,
              cases h21 with h43 h44,
              rw h43 at h41,
              contradiction,
            },
            {
              rw ordered_pair_equality at h21 h41,
              cases h41 with h42 h43,
              cases h21 with h44 h45,
              rw h44 at h42,
              contradiction,
            }
          },
          {
            rw ordered_pair_equality at h21 h39,
            rw h21.right,
            rw h39.right,
          }
        }
      end,
    -- now the application structure of f on X
    have h10:= Apdef M f hFUNC,
    have hab: Ap f a = b:=
      begin
        symmetry,
        apply h10,
        rw h51, 
        rw binary_union_axiom,
        left,
        rw pairing_axiom,
        simp,
      end,
    have hbc: Ap f b = c:=
      begin
        symmetry,
        apply h10,
        rw h51,
        rw binary_union_axiom,
        left,
        rw pairing_axiom,
        simp,
      end,
    have hca: Ap f c = a:=
      begin
        symmetry,
        apply h10,
        rw h51,
        rw binary_union_axiom,
        right,
        rw singleton1,
      end,
    have hRel: Rel f:=
      begin
        rw Rel_definition,
        intros z h20,
        rw h51 at h20,
        rw binary_union_axiom at h20,
        rw singleton1 at h20,
        rw pairing_axiom at h20,
        cases h20 with h60 h61,
        {
          cases h60 with h62 h63,
          {
            use a, use b, 
            exact h62,
          },
          {
            use b, use c,
            exact h63,
          }
        },
        {
          use c, use a,
          exact h61,
        }
      end,
    have hmaps: maps M f X X:=
      begin
        unfold maps,
        split,
        {
          exact hRel,
        },
        {
          repeat{split},
          {
            intros x y h31,
            cases h31 with h32 h33,
            rw h50 at h32,
            rw binary_union_axiom at h32,
            rw singleton1 at h32,
            rw pairing_axiom at h32,
            rw or_assoc at h32,
            rw h50,
            rw binary_union_axiom,
            rw singleton1,
            rw pairing_axiom,
            rw or_assoc,
            rw h51 at h33,
            rw binary_union_axiom at h33,
            rw singleton1 at h33,
            rw pairing_axiom at h33,
            rw or_assoc at h33,
            cases h32 with h34 h35,
            {  
              rw h34 at *,
              repeat{rw ordered_pair_equality at h33},
              simp at h33,
              cases h33 with h36 h37,
              { 
                rw h36 at *,
                simp,
              },
              { 
                cases h37 with h38 h39,
                { 
                  right,
                  right,
                  exact h38.right,
                },
                {
                  rw h39.right at *,
                  simp,
                }
              }
            },
            {
              cases h35 with h60 h61,
              {
                rw h60 at *,
                repeat{rw ordered_pair_equality at h33},
                simp at h33,
                cases h33 with h62 h63,
                {
                  cases h62 with h64 h65,
                  contradiction, 
                },
                {
                  cases h63 with h66 h67,
                  {
                    rw h66,
                    simp,
                  },
                  {
                    left,
                    exact h67.right,
                  }
                }
              },
              {
                rw h61 at *,
                repeat{rw ordered_pair_equality at h33},
                simp at h33,
                cases h33 with h68 h69,
                {
                  cases h68 with h70 h71,
                  contradiction,
                },
                {
                  cases h69 with  h72 h73,
                  {
                    rw h72.right,
                    simp,
                  },
                  {
                    left,
                    exact h73,
                  }
                } 
              }
            }
          },
          {
            intros x y z h20,
            rcases h20 with ⟨ h21, h22, h23⟩,
            rw h51 at h22 h23,
            rw binary_union_axiom at h22 h23,
            rw singleton1 at h22 h23,
            rw pairing_axiom at h22 h23,
            repeat{rw ordered_pair_equality at h22 h23},
            cases h22 with h24 h25,
            {
              cases h24 with h26 h27,
              {
                cases h26 with h28 h29,
                rw h28 at *,
                rw h29 at *,
                simp at h23,
                cases h23 with h30 h31,
                {
                  cases h30 with h32 h33,
                  {
                    rw h32,
                  },
                  {
                    cases h33 with h34 h35, 
                    rw sym at h34,
                    contradiction,
                  }
                },
                {
                  cases h31 with h36 h37,
                  rw sym at h36,
                  contradiction,
                }
              },
              {
                cases h27 with h38 h39,
                rw h38 at *,
                rw h39 at *,
                simp at h23,
                cases h23 with h45 h46,
                {
                  cases h45 with h47 h48,
                  {
                    cases h47 with h49 h52,
                    contradiction,
                  },
                  { 
                    rw h48,
                  }
                },
                {
                  cases h46 with h53 h54,
                  rw sym at h53,
                  contradiction, 
                }
              }
            },
            {
              cases h25 with h55 h56,
              rw h55 at *,
              rw h56 at *,
              simp at h23,
              cases h23 with h57 h58,
              {
                cases h57 with h59 h60,
                {
                  cases h59 with h61 h62,
                  contradiction,
                },
                {
                  cases h60 with h63 h64,
                  contradiction,
                }
              },
              {
                rw h58,
              }
            }
          },
          {
            intros x h20,
            rw h50 at h20,
            rw binary_union_axiom at h20,
            rw singleton1 at h20,
            rw pairing_axiom at h20,
            cases h20 with h21 h22,
            {
              cases h21 with h23 h24,
              {
                use b,
                split,
                {
                  exact hbX,
                },
                {
                  rw h51,
                  rw h23 at *,
                  rw binary_union_axiom,
                  left,
                  rw pairing_axiom,
                  simp,
                }
              },
              {
                use c,
                split,
                {
                  exact hcX,
                },
                {
                  rw h24,
                  rw h51,
                  rw binary_union_axiom,
                  left,
                  rw pairing_axiom,
                  simp,
                }
              }
            },
            {
              use a,
              rw h22 at *,
              split,
              {
                exact haX,
              },
              {
                rw h51,
                rw binary_union_axiom,
                right,
                rw singleton1,
              }
            }
          }
        }
      end,
    have honeone: oneone M f X X:=
      begin
        unfold oneone,
        split,
        {
          exact hmaps,
        },
        {
          split,
          {
            intros x u y h15,
            rcases h15 with ⟨ h16, h17, h18⟩,
            rw h51 at h16 h17,
            rw h50 at h18,
            rw binary_union_axiom at h16 h17 h18,
            rw singleton1 at h16 h17 h18,
            rw pairing_axiom at h16 h17 h18,
            cases h16 with h19 h20,
            {
              cases h19 with h21 h22,
              {
                rw ordered_pair_equality at h21,
                cases h21 with h23 h24,
                rw h23 at *,
                rw h24 at *,
                cases h17 with h25 h26,
                {
                  cases h25 with h27 h28,
                  {
                    rw ordered_pair_equality at h27,
                    symmetry,
                    exact h27.left,
                  },
                  {
                    rw ordered_pair_equality at h28,
                    cases h28 with h29 h30,
                    rw sym at h30,
                    contradiction,
                  } 
                },
                {
                  rw ordered_pair_equality at h26,
                  cases h26 with h31 h32,
                  contradiction,
                }
              },
              {
                rw ordered_pair_equality at h22,
                cases h22 with h33 h34,
                rw h33 at *,
                rw h34 at *,
                cases h17 with h35 h36,
                {
                  rw ordered_pair_equality at h35,
                  cases h35 with h37 h38,
                  {
                    cases h37 with h39 h52,
                    contradiction,
                  },
                  {
                    rw ordered_pair_equality at h38,
                    rw h38.left,
                  }
                },
                {
                  rw ordered_pair_equality at h36,
                  cases h36 with h53 h54,
                  contradiction,
                }
              }
            },
            {
              rw ordered_pair_equality at h20,
              rw h20.left at *,
              rw h20.right at *,
              cases h17 with h55 h56,
              {
                cases h55 with h57 h58,
                {
                  rw ordered_pair_equality at h57,
                  cases h57 with h59 h60,
                  rw sym at h60,
                  contradiction,
                },
                {
                  rw ordered_pair_equality at h58,
                  cases h58 with h61 h62,
                  rw sym at h62,
                  contradiction,
                }
              },
              {
                rw ordered_pair_equality at h56,
                rw h56.left,
              },
            }
          },
          {
            intros x y h11,
            cases h11 with h12 h13,
            rw h51 at h12,
            rw h50 at h13,
            rw binary_union_axiom at h12 h13,
            rw singleton1 at h12 h13,
            rw pairing_axiom at h12 h13,
            repeat{rw ordered_pair_equality at h12},
            cases h13 with h14 h15,
            {
              cases h14 with h16 h17,
              {
                rw h16 at *,
                simp at h12,
                cases h12 with h18 h19,
                {
                  cases h18 with h20 h21,
                  {
                    cases h20 with h22 h23,
                    rw sym at h23,
                    contradiction,
                  },
                  {
                    cases h21 with h24 h25,
                    rw sym at h25,
                    contradiction,
                  }
                },
                {
                  rw h19,
                  exact hcX,
                }
              },
              {
                cases h12 with h26 h27,
                {
                  cases h26 with h28 h29,
                  {
                    rw h28.left,
                    exact haX,
                  },
                  {
                    rw h29.left,
                    exact hbX,
                  }
                },
                {
                  rw h27.left,
                  exact hcX,
                }
              }
            },
            {
              rw h15 at *,
              simp at h12,
              cases h12 with h30 h31,
              {
                cases h30 with h32 h33,
                {
                  cases h32 with h34 h35,
                  contradiction,
                },
                {
                  rw h33,
                  exact hbX,
                }
              },
              {
                cases h31 with h36 h37,
                contradiction,
              }
            }
          }
        }
      end,
    have hdom: dom f ⊆ X :=
      begin
        rw subset_definition,
        intros t h11,
        rw domain_axiom f hRel at h11,
        cases h11 with y h12,
        rw h51 at h12,
        rw binary_union_axiom at h12,
        rw singleton1 at h12,
        rw pairing_axiom at h12,
        cases h12 with h13 h14,
        {
          cases h13 with h15 h16,
          {
            rw ordered_pair_equality at h15,
            rw h15.left,
            exact haX,
          },
          {
            rw ordered_pair_equality at h16,
            rw h16.left,
            exact hbX,
          }
        },
        {
          rw ordered_pair_equality at h14,
          rw h14.left,
          exact hcX,
        }
      end,
    have hrange: range f ⊆ X:=
      begin
        rw subset_definition,
        intros t h11,
        rw range_axiom f hRel at h11,
        cases h11 with x h12,
        rw h51 at h12,
        rw binary_union_axiom at h12,
        rw singleton1 at h12,
        rw pairing_axiom at h12,
        cases h12 with h13 h14,
        {
          cases h13 with h15 h16,
          {
            rw ordered_pair_equality at h15,
            rw h15.right,
            exact hbX,
          },
          {
            rw ordered_pair_equality at h16,
            rw h16.right,
            exact hcX,
          }
        },
        {
          rw ordered_pair_equality at h14,
          rw h14.right,
          exact haX,
        }
      end,
    have hinjection: injection M  f X:=
      begin
        unfold injection,
        exact ⟨ honeone, hRel, hFUNC, hdom, hrange⟩,
      end,
    have h21:= h5 X f hinjection a haX, 
    have h22:= successorequation M X f   hFUNC hRel  hmaps b a hb haX,
    rw h22 at h21,
    rw hbdef at h21,
    rw ApOne at h21,
    rw hab at h21,
    rw hbc at h21,
    contradiction,
    exact hFUNC,
    exact hRel,
  end

lemma ssnneqn: ∀ (x:M), x ∈ ℕℕ → ¬ S (S x) = x:=
  assume x hx h2,
  begin
    have h4:= mbig2 M x hx,
    have h3: x = x ⊕ S (S ChurchZero):=
      begin
        rw ChurchSuccessorShift M (S ChurchZero) (successorN M ChurchZero (zeroN M)) x hx,
        rw ChurchSuccessorShift M ChurchZero (zeroN M) (S x) (successorN M x hx),
        rw ChurchZero_equation (S (S x)) (successorN M (S x) (successorN M x hx)),
        symmetry,
        exact h2,
      end,
    contradiction,
  end 

lemma Churchletolessthan: ∀ (x y:M), x ∈ ℕℕ → y ∈ ℕℕ → x ≤ℕ y → ¬ x = y → x <ℕ y:=
  assume x y,
  begin
    intros hx hy h3 h4,
    rw ChurchOrder2 x y at h3,
    cases h3 with m h5,
    cases h5 with h6 h7,
    have h8: ¬ m = ChurchZero:=
      begin
        intro h9,
        rw h9 at *,
        rw ChurchZero_equation x hx at h7,
        contradiction, 
      end,
    have h9:= nonzeroisChurchSuccessor M m h6 h8,
    cases h9 with r h10,
    cases h10 with h11 h12,
    rw ChurchOrder x y,
    use r,
    rw← h12,
    exact ⟨ h11, h7⟩,
  end

lemma Churchle: ∀ (x y:M), x ∈ ℕℕ → y ∈ ℕℕ → (x ≤ℕ y ↔  x <ℕ y ∨ x = y):=
  assume x y,
  begin
    intros hx hy,
    split,
    {
      intro h,
      rw ChurchOrder2 x y at h,
      cases h with n h2,
      cases h2 with hn h4,
      have h5:= decidable0 M n hn,
      cases h5 with h6 h7,
      {
        right,
        rw h6 at h4,
        rw ChurchZero_equation x hx at h4,
        exact h4,
      },
      {
        left,
        rw ChurchOrder,
        have h8:= nonzeroisChurchSuccessor M n hn h7,
        cases h8 with m h9,
        use m,
        rw h9.right at h4,
        exact ⟨ h9.left, h4⟩, 
      }
    },
    {
      intros h,
      cases h with h2 h3,
      {
        rw ChurchOrder   x y at h2,
        cases h2 with n h4,
        cases h4 with hn h6,
        rw ChurchOrder2 x y,
        use (S n),
        exact ⟨ (successorN M n hn), h6⟩,
      },
      {
        rw h3 at *,
        rw ChurchOrder2,
        use ChurchZero,
        rw ChurchZero_equation y hy,
        simp,
        exact zeroN M,
      }
    }
  end
  
lemma klessthann: ∀(k n:M), k ∈ STEM → n ∈ ℕℕ → ¬ k = n →  S k = S n → k <ℕ n:=
  assume k n,
  begin
    set X:= Z_klessthann M k n with h50,
    intros hk hn hkn h3,
    have h4: STEM ⊆ X:=
      begin
        have h51:ChurchZero ∈ X:=
          begin
            rw h50,
            rw Z_klessthann_members M k n,
            have h6:= (S1 M).left,
            have h7:= zeroplusx M n hn,
            split,
            {
              exact h6,
            },
            {
              rw ChurchOrder2 ChurchZero n, 
              use n,
              exact ⟨ hn, h7⟩, 
            }
          end,
        
        rw subset_definition,
        intros z h5,
        rw StemDefinition at h5,
        cases h5 with h6 h7,
        have h8:= h7 X h51,
        apply h8, 
        intros x hx h9 h10,
        rw h50 at h9,
        rw Z_klessthann_members M k n at h9,
        cases h9 with h11 h12,
        have h13:= (S1 M).right x hx h11 h10,
        have h14: ¬ x = n:=
          begin
            intros h15,
            rw h15 at *,
            have h16:= kisunique M k n hk hn hkn h3 n h11,
            rw sym at hkn,
            have h17:= member_subset M STEM ℕℕ k (SN M) hk,
            have h18:= h16 hkn k h17 h3,
            rw sym at h18,
            contradiction,
          end,
        have h15:= Churchletolessthan M x n hx hn h12 h14,
        have h16:= order2 M x n hx hn h15,
        rw h50,
        rw Z_klessthann_members M k n,
        split,
        {
          exact h13,
        },
        {
          rw Churchle M (S x) n (successorN M x hx) hn,
          exact h16,
        }
      end,
    have h5:= member_subset M STEM X k h4 hk,
    rw h50 at h5,
    rw Z_klessthann_members M k n at h5,
    cases h5 with h6 h7,
    have h8:= member_subset M STEM ℕℕ k (SN M) hk,
    have h9:= Churchletolessthan M k n h8 hn h7 hkn,
    exact h9,
  end

lemma nissuccessor:  ∀(k n:M), k ∈ STEM → n ∈ ℕℕ → ¬ k = n →  S k = S n → ∃ (p:M),p ∈ LOOP n ∧ S p = n:=
  assume k n hk hn hkn h,
  begin
     have h106:= member_subset M STEM ℕℕ k (SN M) hk,
    have h2: ¬ n ∈ STEM:=
      begin
        intro h4,
        have h5:= hkn,
        rw sym at h5,       
        have h3:= kisunique M k n hk hn hkn h n h4 h5 k h106 h,
        contradiction,
      end,
    have h3:= (S1 M).left,
    have h4: ¬ n = ChurchZero:=
      begin
        intro h5,
        rw← h5 at h3,
        contradiction,
      end,
    have h5:= predecessor M n hn h4,
    cases h5 with p h6,
    cases h6 with hp h8,
    have h9:= LcupS M k n hk hn hkn h,
    rw full_extensionality at h9,
    have h10:= (h9 p).mp hp,
    rw binary_union_axiom at h10,
    cases h10 with h11 h12,
    { 
      use p,
      exact ⟨ h11, h8⟩,
    },
    {
      have h12:= Sdecidable M p hp k h106 h12,
      cases h12 with h13 h14,
      {
        rw h13 at *,
        rw h at h8,
        use n,
        rw h8,
        simp,
        have h15:= L1 M k n hk hn hkn h,
        exact h15.left,
      },
      {
        
        have h115:= Smax M k n hk hn hkn h,
        have h15:= (h115 p).mp h12,
        cases h15 with h16 h17,
        have h18:= (S1 M).right p hp h12,
        have h30: S p ∈ STEM:=
          begin
            have h116:= (h115 (S p)).mpr,
            apply h116,
            split,
            {
              exact successorN M p hp,
            },
            {
              cases h17 with h20 h21,
              {
                have h22:= order2 M p k hp h106 h20,
                exact h22,
              },
              {
                contradiction,
              }
            }
          end,
        have h31:= LcapS M k n hk hn hkn h,
        have h32:= (L1 M k n hk hn hkn h).left,
        have h33: S p ∈ LOOP n:=
          begin
            rw h8,
            exact h32,
          end,
        have h34:= LcapS M k n hk hn hkn h,
        rw full_extensionality at h34,
        have h35: ¬ S p ∈ STEM:=
          begin
            intros h36,
            specialize h34 (S p),
            have h37: S p ∈ LOOP n ∩ STEM:=
              begin
                rw intersection_axiom,
                exact ⟨ h33, h36⟩, 
              end,
            rw h34 at h37,
            have h38:= emptyset_axiom (S p),
            contradiction,
          end,
        contradiction,
      }
    }
  end

theorem looponto: ∀(k n:M), k ∈ STEM → n ∈ ℕℕ → ¬ k = n →  S k = S n → ∀ (x:M), x ∈ LOOP n → ∃(y:M), y ∈ LOOP n ∧ S y = x:=
  assume k n hk hn hkn h,
  begin
    have h2:=  L1 M k n hk hn hkn h,
    cases h2 with h5 h4,
    have base: n ∈ Z_looponto M k n:= 
      begin
        have h3:= nissuccessor M k n hk hn hkn h,
        rw Z_looponto_members M k n,
        exact ⟨ h5, h3⟩,
      end,
    have step: ∀ (x:M), x ∈ Z_looponto M k n → S x ∈ Z_looponto M k n:=
      begin
        intros x hx,
        rw Z_looponto_members M k n at hx,
        cases hx with h6 h7,
        have h8:= h4 x h6,
        rw Z_looponto_members M k n,
        split,
        {
          exact h8,
        },
        {
          use x,
          simp,
          exact h6,
        }
      end,
    intros x hx,
    rw LoopDefinition at hx,
    cases hx with h20 h21,
    specialize h21 (Z_looponto M k n),
    have h22:= h21 base step,
    rw Z_looponto_members M k n at h22,
    cases h22 with h23 h24,
    exact h24,
  end 

lemma loopfinite:  ℕℕ ∈ FINITE M → 
∀(k n:M), k ∈ STEM → n ∈ ℕℕ → ¬ k = n →  S k = S n →
LOOP n ∈ FINITE M:=
  begin
    intros hfinite k n hk hn hkn h3,
    have h6:= LcupS M k n hk hn hkn h3,
    have h6copy:= h6, 
    have h90:= LcapS M k n hk hn hkn h3,
    have h5: LOOP n ⊆ ℕℕ :=
      begin
        rw subset_definition,
        intros z h7,
        rw h6,
        rw binary_union_axiom,
        left,
        exact h7,
      end,
    have h4:=  separablefinite M ℕℕ hfinite (LOOP n) h5,
    apply h4,
    unfold separable_subset,
    split,
    {
      exact h5,
    },
    {
      rw full_extensionality,
      intro x,
      rw full_extensionality at h6,
      specialize h6 x,
      rw binary_union_axiom at h6,
      rw binary_union_axiom,
      split,
      {
        intro hx,
        rw h6 at hx,
        cases hx with h7 h8,
        {
          left,
          exact h7,
        },
        {
          right,
          rw minus_members,
          split,
          {
            rw h6copy,
            rw binary_union_axiom,
            right,
            exact h8,
          },
          {
            intro h9,
            have h10: x ∈ (LOOP n) ∩ STEM:=
              begin
                rw intersection_axiom,
                exact ⟨ h9, h8⟩, 
              end,
            rw h90 at h10,
            have h91:= emptyset_axiom x,
            contradiction,
          }
        }
      },
      {
        intro h7,
        cases h7 with h8 h9,
        {
          exact member_subset M (LOOP n) ℕℕ x h5 h8,
        },
        {
          rw minus_members at h9,
          exact h9.left,
        }
      }
    }
  end

theorem looppermutation:ℕℕ ∈ FINITE M → 
∀(k n:M), k ∈ STEM → n ∈ ℕℕ → ¬ k = n →  S k = S n →
permutation M (CSG M n) (LOOP n):=
  assume hfinite k n hk hn hkn h3,
  begin
    unfold permutation,
    unfold injection,
    have hrel: Rel (CSG M n):=
      begin
        rw Rel_definition,
        intros z h5,
        rw CSG_members at h5,
        cases h5 with x h6,
        cases h6 with h7 h8,
        use x, use S x,
        exact h7,
      end,
    have hf: CSG M n ∈ FUNC:=
      begin
        rw FUNC_members,
        intros x y z h4 h5,
        rw CSG_members at h4 h5,
        cases h5 with p h6,
        cases h4 with q h7,
        cases h6 with h8 h9,
        cases h7 with h10 h11,
        rw ordered_pair_equality at h8 h10,
        cases h10 with h12 h13,
        cases h8 with h14 h15,
        rw← h12 at *,
        rw← h14 at *,
        rw h13,
        rw h15,
      end,
    have h4:= looponto M k n hk hn hkn h3,
    have h5: onto M (CSG M n)(LOOP n)(LOOP n):=
      begin
        unfold onto,
        intros y hy,
        have h6:= h4 y hy,
        cases h6 with x h7,
        use x,
        cases h7 with h8 h9,
        split,
        {
          exact h8,
        },
        {
          rw CSG_members,
          use x,
          rw h9,
          simp,
          exact h8,
        }
      end,
    have h6: dom (CSG M n) ⊆ LOOP n:=
      begin
        rw subset_definition,
        intros t h,
        rw domain_axiom (CSG M n) hrel at h,
        cases h with y h7,
        rw CSG_members at h7,
        cases h7 with x h8,
        cases h8 with h9 h10,
        rw ordered_pair_equality at h9,
        rw h9.left at *,
        exact h10,
      end,
    have h9:= loopfinite M hfinite k n hk hn hkn h3,
    have h10: maps M (CSG M n) (LOOP n) (LOOP n):=
      begin
        unfold maps,
        split,
        {
          exact hrel,
        },
        {
          split,
          {
            intros x y h,
            cases h with h20 h21,
            rw CSG_members at h21,
            cases h21 with p h22,
            cases h22 with h23 h24,
            rw ordered_pair_equality at h23,
            rw h23.left at *,
            rw h23.right at *,
            have h24:= L1 M k n hk hn hkn h3,
            cases h24 with h25 h26,
            exact h26 p h20,
          },
          {
            split,
            {
              intros x y z h,
              rcases h with ⟨ h10,h11, h12⟩,
              rw CSG_members at h11 h12,
              cases h12 with p h13,
              cases h11 with q h14,
              cases h14 with h15 h16,
              cases h13 with h17 h18,
              rw ordered_pair_equality at h15 h17,
              cases h17 with h19 h20,
              cases h15 with h21 h22,
              rw← h19 at *,
              rw← h21 at *,
              rw h20,
              rw h22,
            },
            {
              intros x h,
              use S x,
              have h24:= L1 M k n hk hn hkn h3,
              split,
              {
                exact h24.right x h,
              },
              {
                rw CSG_members,
                use x,
                simp,
                exact h,
              }
            }
          }
        }
      end,
    have h11: oneone M (CSG M n) (LOOP n)(LOOP n):=
      begin
        have h12:= dedekind2 M (LOOP n) (CSG M n) h9 hf hrel h6 h10 h5,
        exact h12,
      end,
    have h12: range(CSG M n) ⊆ LOOP n:=
      begin
        rw subset_definition,
        intros t h,
        rw range_axiom (CSG M n) hrel at h,
        cases h with x h13,
        rw CSG_members at h13,
        cases h13 with p h14,
        cases h14 with h15 h16,
        rw ordered_pair_equality at h15,
        rw h15.right,
        have h24:= L1 M k n hk hn hkn h3,
        exact h24.right p h16,
      end,
    split,
    {
      exact ⟨ h11, hrel, hf, h6, h12⟩,
    },
    {
      exact h5,
    }
  end  

theorem looponeone: ℕℕ ∈ FINITE M → 
∀(k n:M), k ∈ STEM → n ∈ ℕℕ → ¬ k = n →  S k = S n →
∀ (x z:M), x ∈ LOOP n → z ∈ LOOP n → S x = S z → x = z:=
  assume hfinite k n hk hn hkn h3,
  begin
    set f:= CSG M n with h50,
    have h4:= looppermutation M hfinite k n hk hn hkn h3,
    unfold permutation at h4,
    cases h4 with h5 h6,
    unfold injection at h5,
    cases h5 with h7 h8,
    unfold oneone at h7,
    rcases h7 with ⟨ h9, h10, h11⟩,
    intros x z hx hz h20,
    specialize h10 x z (S x),
    apply h10,
    rw CSG_members,
    rw CSG_members,
    split,
    {
      use x,
      simp,
      exact hx,
    },
    {
      use x,
      split,
      {
        rw ordered_pair_equality,
        simp,
        rw h20 at *,
        symmetry,
        apply h10,
        split,
        {
          rw← h20,
          rw CSG_members,
          use x,
          simp,
          exact hx,
        },
        {
          rw CSG_members,
          split,
          {
            use z,
            simp,
            exact hz,
          },
          {
            exact hx,
          }
        }
      },
      {
        exact hx,
      },
      {
        exact hx,
      }
    }
  end

#axioms_all 

 