-- The order of the loop 

import ChurchNumbers4

variables (M:Type) [Model M] (a b x y z u v w X R W κ μ ℓ : M)
-- using ℓ where the source text has λ because you can't use λ for a variable.

open Model 

lemma SGRel: Rel (SG M):=
  begin
    rw Rel_definition,
    intros z h,
    rw SG_members at h,
    cases h with x h2,
    cases h2 with h3 h4,
    use x, use (S x),
    exact h3,
  end

lemma SGFUNC: SG M ∈ FUNC:=
  begin
    rw FUNC_members,
    intros x y z h1 h2,
    rw SG_members at h1 h2,
    cases h2 with p h3,
    cases h1 with q h4,
    cases h3 with h5 h6,
    cases h4 with h7 h8,
    rw ordered_pair_equality at h5 h7,
    cases h7 with h10 h9,
    cases h5 with h12 h11,
    rw← h12 at *,
    rw← h10 at *,
    rw [h11, h9],
  end

lemma SGMaps: maps M (SG M) ℕℕ ℕℕ:=
  begin
    unfold maps,
    split,
    {
      exact SGRel M,
    },
    repeat{split},
    {
      intros x y h,
      cases h with h3 h4,
      rw SG_members at h4,
      cases h4 with p h5,
      cases h5 with h6 h7,
      rw ordered_pair_equality at h6,
      cases h6 with h8 h9,
      rw← h8 at *,
      rw h9 at *,
      exact successorN M x h7,
    },
    {
      intros x y z h,
      rcases h with ⟨ h2,h3, h4⟩,
      rw SG_members at h3 h4,
      cases h4 with p h5,
      cases h3 with q h6,
      cases h5 with h7 hp,
      cases h6 with h8 hq,
      rw ordered_pair_equality at h7 h8,
      cases h8 with h9 h10,
      cases h7 with h11 h12,
      rw← h9 at *,
      rw← h11 at *,
      rw [h10, h12],
    },
    {
      intros x hx,
      use (S x),
      split,
      {
        exact successorN M x hx,
      },
      {
        rw SG_members,
        use x,
        simp,
        exact hx,
      }
    }
  end

lemma counting1: ∀ (x:M), x ∈ ℕℕ → ∃ (j:M), j ∈ ℕℕ ∧ Ap (Ap j (SG M)) ChurchZero = x:=
  begin
    have base: ChurchZero ∈ Z_counting1 M:=
      begin
        rw Z_counting1_members,
        split,
        { 
          exact zeroN M,
        },
        {
          use ChurchZero,
          split,
          {
            exact zeroN M,
          },
          {
            have h3:= zeroAp M (SG M) ChurchZero,
            exact h3,
          }
        }
      end,
    have step: ∀ (x:M), x ∈ Z_counting1 M → S x ∈ Z_counting1 M:=
      begin
        intros x h,
        rw Z_counting1_members at h,
        cases h with h2 h3,
        cases h3 with j h4,
        cases h4 with h5 h6,
        rw Z_counting1_members,
        split,
        {
          exact successorN M x h2,
        },
        {
          use ( S j),
          split,
          {
            exact successorN M j h5,
          },
          {
            have h7:= successorequation M ℕℕ (SG M) (SGFUNC M) (SGRel M) (SGMaps M) j ChurchZero h5 (zeroN M),
            rw h6 at h7,
            rw h7,
            have h8:= Apdef M (SG M) (SGFUNC M) x (S x),
            symmetry,
            apply h8,
            rw SG_members,
            use x,
            simp,
            exact h2,
          }
        }
      end,
    intros x h,
    rw N_members at h,
    have h4:= h (Z_counting1 M) ⟨ base, step⟩, 
    rw Z_counting1_members at h4,
    exact h4.right,
  end

lemma counting3: ∀ (j:M), j ∈ ℕℕ → Ap (Ap j (SG M)) ChurchZero ∈ ℕℕ :=
  assume j hj,
  begin
    have h3:= nfFUNC M j hj (SG M) (SGFUNC M) (SGRel M),
    cases h3 with h20 h21,
    have h4:= iteration M j hj ℕℕ (SG M) (SGFUNC M) (SGRel M) (SGMaps M),
    cases h4 with h5 h6,
    unfold maps at h5, 
    rcases h5 with ⟨ h6, h7, h8, h9⟩,
    have h10:= h9 ChurchZero (zeroN M),
    cases h10 with y h11,
    cases h11 with h12 h13,
    have h14:= Apdef M (Ap j (SG M)) h20 ChurchZero y h13,
    rw← h14,
    exact h12,
  end

lemma counting2: ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n →  ∀ (x:M), x ∈ ℕℕ → 
∃(j:M), j ∈ ℕℕ ∧ Ap (Ap j (SG M)) ChurchZero = x ∧  
 ∀ (l:M), l ∈ ℕℕ → Ap (Ap l (SG M)) ChurchZero = x → j≼l :=
  assume hfinite k n hk hn hkn hskn x hx,
  begin
    set Z:= Z_counting2 M x with h50,
    have h80:= finitedecidable M ℕℕ hfinite,
    rw decidable_members at h80,
    have h2: Z ⊆ ℕℕ :=
      begin
        rw subset_definition,
        intro t,
        rw h50,
        rw Z_counting2_members,
        intro h,
        exact h.left,
      end, 
    have h3: Z ∈ FINITE M:=
      begin
        have h5:= separablefinite M ℕℕ hfinite Z h2,
        apply h5,
        unfold separable_subset,
        split,
        {
          exact h2,
        },
        {
          rw full_extensionality,
          intro t,
          rw binary_union_axiom,
          rw minus_members,
          split,
          {
            intro ht,
            rw h50,
            rw Z_counting2_members,
            have h18:= counting3 M t ht,
            have h19:= h80  (Ap (Ap t (SG M)) ChurchZero) x ⟨ h18, hx⟩, 
            cases h19 with h20 h21,
            {
              left,
              exact ⟨ ht, h20 ⟩,
            },
            {
              right,
              split,
              {
                exact ht,
              },
              {
                intro h,
                cases h with h22 h23,
                contradiction,
              }
            }
          },  
          {
            intro h,
            cases h with h30 h31,
            {
              rw h50 at h30,
              rw Z_counting2_members M x at h30,
              cases h30 with h32 h33,
              exact h32,
            },
            {
              exact h31.left,
            }
          }
        }
      end,
    have h5: ∃(u:M), u ∈ Z:=
      begin
        have h6:= counting1 M x hx,
        cases h6 with j h7,
        cases h7 with hj h8,
        use j,
        rw h50,
        rw Z_counting2_members,
        exact ⟨ hj, h8⟩, 
      end,
    have h6: ¬ (Z = Λ):=
      begin
        intro h,
        cases h5 with u h7,
        rw h at h7,
        have h8:= emptyset_axiom u,
        contradiction,
      end,
    have h4:= leastelement M hfinite k n hk hn hkn hskn Z h3 h2 h6,
    cases h4 with j h20,
    cases h20 with hj h21,
    use j,
    split,
    { 
      have h23:= member_subset M Z ℕℕ j h2 hj,
      exact h23,
    },
    {
      rw h50 at hj,
      rw Z_counting2_members M x at hj,
      cases hj with h24 h25,
      split,
      {
        exact h25,
      },
      {
        intros l hl h26,
        specialize h21 l,
        apply h21,
        rw h50,
        rw Z_counting2_members M x,
        exact ⟨ hl, h26⟩, 
      }
    }
  end



lemma kspreceq_helper: ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n → 
∀ (l:M), l ∈ ℕℕ → ∀ (j:M), j ∈ ℕℕ → j ≼ l → ¬ l = n → S j ≼ S l:=
  assume hfinite k n hk hn hkn hskn,
  begin
    have base: ChurchZero ∈ Z_kspreceq_helper M n:=
      begin
        rw Z_kspreceq_helper_members,
        split,
        {
          exact zeroN M,
        },
        {
          intros j hj h3 hjn,
          have h4:= preceqzero M hfinite k n hk hn hkn hskn j hj h3,
          rw h4,
          exact preceqreflexive M hfinite k n hk hn hkn hskn (S ChurchZero) (successorN M ChurchZero (zeroN M)),
        }
      end,
    have step: ∀(l:M), l ∈ Z_kspreceq_helper M n → ¬ l = n → S l ∈ Z_kspreceq_helper M n:=
      begin
        intros l h hln,
        rw Z_kspreceq_helper_members M n at h,
        rw Z_kspreceq_helper_members M n,
        cases h with hl h4,
        split,
        {
          exact successorN M l hl,
        },
        {
          intros j hj hjl hln2,
          have h80:= finitedecidable M ℕℕ hfinite,
          rw decidable_members at h80,
          have h81:= h80 (S j) (S l)⟨ successorN M j hj, successorN M l hl⟩, 
          cases h81 with h82 h83,
          {
            rw h82 at *,
            have h5:= preceqreflexive M hfinite k n hk hn hkn hskn (S l) (successorN M l hl),
            have h6:= preceqsuccessor M hfinite k n hk hn hkn hskn (S l) (S l)(successorN M l hl)(successorN M l hl) hln2,
            rw h6,
            left,
            exact h5,
          },
          {
            have h8:= preceqsuccessor M hfinite k n hk hn hkn hskn (S j) (S l) (successorN M j hj) (successorN M l hl) hln2,
            rw h8,
            have h9:=preceqsuccessor M hfinite k n hk hn hkn hskn j l hj hl hln,
            rw h9 at hjl,
            cases hjl with h10 h11,
            { 
              left,
              have h12:= preceqsuccessor M hfinite k n hk hn hkn hskn (S j) l (successorN M j hj) hl hln,
              rw h12,
              have h84:= h80 j l ⟨ hj, hl⟩, 
              cases h84 with h13 h14,
              {
                rw h13 at *,
                contradiction,
              },
              {
                left,
                have h15:=leftpreceqsuccessor M hfinite k n hk hn hkn hskn j l hj hl,
                have h16: j ≺  l:=
                  begin
                    rw prec_definition,
                    exact ⟨ h10, h14⟩,
                  end,
                exact  h15 h16,
              }
            },
            {
              rw h11 at *,
              right,
              refl, 
            }
          }
        }
      end,
    have h4:= finiteinduction M hfinite k n hk hn hkn hskn (Z_kspreceq_helper M n) ⟨ base, step⟩,
    intros l hl,
    have h5:= member_subset M ℕℕ (Z_kspreceq_helper M n) l h4 hl,
    rw Z_kspreceq_helper_members M n at h5,
    exact h5.right,
  end 
 

lemma ApSG: ∀ (x:M), x ∈ ℕℕ → Ap (SG M) x = S x:=
  assume x hx,
  begin
    have h4:= Apdef M (SG M) (SGFUNC M) x (S x),
    symmetry,
    apply h4,
    rw SG_members,
    use x,
    simp,
    exact hx,
  end

lemma xsmapsloop: ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n →  
∀ (x:M), x ∈ ℕℕ → ∀ (y:M), y ∈ LOOP n → Ap (Ap x (SG M)) y ∈ LOOP n:=
  assume hfinite k n hk hn hkn hskn,
  begin
    have base: ChurchZero ∈ Z_xsmapsloop M n:=
      begin
        rw Z_xsmapsloop_members M n,
        split,
        {
          exact zeroN M,
        },
        {
          intros y hyloop,
          have hy:= member_subset M (LOOP n) ℕℕ y (LN M k n hk hn hkn hskn) hyloop,
          rw ApZero,
          rw ApId,
          exact hyloop,
        }
      end,
    have step: ∀ (x:M), x ∈ Z_xsmapsloop M n → ¬ x = n → S x ∈ Z_xsmapsloop M n:=
      begin
        intros x h hxn,
        rw Z_xsmapsloop_members at h,
        rw Z_xsmapsloop_members,
        cases h with hx h4,
        split,
        {
          exact successorN M x hx,
        },
        {
          intros y hyloop,
          rw successorequation M ℕℕ (SG M) (SGFUNC M) (SGRel M) (SGMaps M),
          {
            have h20:  Ap (Ap x (SG M)) y ∈ ℕℕ:=
              begin
                have h22: x ∈ FUNC:= Churchnumbersarefunctions M x hx,
                have h21:= h4 y hyloop,
                have h22:= member_subset M (LOOP n) ℕℕ (Ap (Ap x (SG M)) y ) (LN M k n hk hn hkn hskn) h21,
                exact h22,
              end,
            have h30:  Ap (Ap x (SG M)) y ∈ LOOP n:=
              begin
                have h22: x ∈ FUNC:= Churchnumbersarefunctions M x hx,
                have h21:= h4 y hyloop,
                exact h21,
              end,
            rw ApSG,
            {
              have h31:= L1 M k n hk hn hkn hskn,
              apply h31.right,
              exact h30,
            },
            {
              exact h20,
            }
          },
          {
            exact hx,
          },
          {
            have h34:= member_subset M (LOOP n) ℕℕ y (LN M k n hk hn hkn hskn) hyloop,
            exact h34,
          }
        }
      end,
    intros x h,
    have h5:= finiteinduction M hfinite k n hk hn hkn hskn (Z_xsmapsloop M n) ⟨ base, step⟩,
    rw subset_definition at h5,
    intros y hyloop,
    have h35:=  h5 x h, 
    rw Z_xsmapsloop_members M n at h35, 
    cases h35 with h36 h37,
    exact h37 y hyloop,
  end

lemma xsmapsN: ∀ (x:M), x ∈ ℕℕ → ∀ (y:M), y ∈ ℕℕ  → Ap (Ap x (SG M)) y ∈ ℕℕ :=
  begin
    have base: ChurchZero ∈ Z_xsmapsN M:=
      begin
        rw Z_xsmapsN_members M,
        split,
        {
          exact zeroN M,
        },
        {
          intros y hy,
          have h4:= zeroAp M (SG M) y,
          rw h4,
          exact hy,
        }
      end,
    have step: ∀ (x:M), x ∈ Z_xsmapsN M  → S x ∈ Z_xsmapsN M:=
      begin
        intros x h,
        rw Z_xsmapsN_members at h,
        rw Z_xsmapsN_members,
        cases h with hx h4,
        split,
        {
          exact successorN M x hx,
        },
        {
          intros y hy,
          rw successorequation M ℕℕ (SG M) (SGFUNC M) (SGRel M) (SGMaps M),
          {
            have h20:  Ap (Ap x (SG M)) y ∈ ℕℕ:=
              begin
                have h22: x ∈ FUNC:= Churchnumbersarefunctions M x hx,
                have h21:= h4 y hy,
                exact h21,
              end,
            rw ApSG,
            {
              exact (successorN M (Ap (Ap x (SG M)) y ) h20),
            },
            { 
              exact h20,
            }
          },
          {
            exact hx,
          },
          {
            exact hy,
          }
        }
      end,
    intros x hx y hy,
    rw N_members at hx,
    specialize hx (Z_xsmapsN M),
    have h5:= hx ⟨ base, step⟩, 
    rw Z_xsmapsN_members at h5,
    cases h5 with h6 h7,
    exact h7 y hy,
  end

lemma mexists_helper:ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n → 
∃ (m:M), m ∈ ℕℕ ∧ k ⊕ m = n:=
  assume hfinite k n hk hn hkn hskn,
  begin
    have hk2:= member_subset M STEM ℕℕ k (SN M) hk,
    set X:= Z_mexists_helper M k n  with h50,
    have h3: n ∈ X:=
        begin
          rw h50,
          rw Z_mexists_helper_members,
          split,
          {
            exact hn,
          },
          {
            use ChurchZero,
            split,
            {
              exact zeroN M,
            },
            {
              rw ChurchZero_equation n hn,
            }
          }
        end,
    have h4: LOOP n ⊆ X:=
      begin
        rw subset_definition,
        intros t h5,
        rw LoopDefinition at h5,
        cases h5 with ht h6,
        have h7:= h6 X h3,
        apply h7,
        intros u h8,
        rw h50 at h8,
        rw Z_mexists_helper_members at h8,
        cases h8 with hu h9,
        cases h9 with p h10,
        cases h10 with hp h11,
        rw h50,
        rw Z_mexists_helper_members,
        split,
        {
          exact successorN M u hu,
        },
        {
          use S p,
          split,
          {
            exact successorN M p hp,
          },
          {
            rw h11,
            rw ChurchAddition_equation,
            exact hn,
            exact hp,
          }
        }
      end,
    rw subset_definition at h4,
    have hnloop:= (L1 M k n hk hn hkn hskn).left,
    have h5:= looponto M k n hk hn hkn hskn n hnloop,
    cases h5 with p h6,
    cases h6 with h7 h8,
    have h9:= h4 p h7,
    rw h50 at h9,
    rw Z_mexists_helper_members at h9,
    cases h9 with hp h10,
    cases h10 with m h11,
    cases h11 with hm h12,
    use S m,
    split,
    {
      exact successorN M m hm,
    },
    {
      rw h12 at h8,
      rw←  ChurchAddition_equation n m hn hm  at h8,
      rw ChurchSuccessorShift M m hm n hn at h8,
      rw← hskn at h8,
      rw ChurchSuccessorShift,
      exact h8,
      exact hm,
      exact hk2,
    }
  end

lemma mexists: ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n → 
∃ (m:M), m ∈ ℕℕ ∧ k ⊕ m = n ∧ ∀(l:M), l ∈ ℕℕ → k ⊕ l = n → m ≼ l:=
  assume hfinite k n hk hn hkn hskn,
  begin
    have hk2:= member_subset M STEM ℕℕ k (SN M) hk,
    set X:= Z_mexists M k n with h50,
    have h10: X ⊆ ℕℕ:=
      begin
        rw subset_definition,
        intros t h11,
        rw h50 at h11,
        rw Z_mexists_members at h11,
        cases h11 with ht h12,
        exact ht,
      end,
    have h80:= finitedecidable M ℕℕ hfinite,
    rw decidable_members at h80,
    have h5:= separablefinite M ℕℕ hfinite X h10,
    have h11: X ∈ FINITE M:=
      begin
        apply h5,
        unfold separable_subset,
        split,
        {
          exact h10,
        },
        {
          rw full_extensionality,
          intro t,
          rw binary_union_axiom,
          rw minus_members,
          split,
          {
            intro ht,
            rw h50,
            rw Z_mexists_members,
            have h81:= h80 n (k ⊕ t) ⟨ hn, ChurchAdditionMaps M t ht k hk2⟩, 
            cases h81 with h20 h21,
            {
              left,
              exact ⟨ ht, h20⟩,
            },
            {
              right,
              split,
              {
                exact ht,
              },
              {
                intro h,
                cases h with h22 h23,
                contradiction,
              }
            }
          },
          {
            intro h,
            cases h with h30 h31,
            {
              rw h50 at h30,
              rw Z_mexists_members at h30,
              cases h30 with h32 h33,
              exact h32,
            },
            {
              cases h31 with h32 h33,
              exact h32,
            }
          }
        }
      end,
    have h25:= mexists_helper M hfinite k n hk hn hkn hskn,
    cases h25 with m h26,
    cases h26 with h27 h28,
    have h29: m ∈ X:=
      begin
        rw h50,
        rw Z_mexists_members,
        rw sym at h28,
        exact ⟨ h27, h28⟩, 
      end,
    have h30: ¬ (X = Λ):=
      begin
        intro h,
        have h2:= emptyset_axiom m,
        rw h at *,
        contradiction,
      end,
    have h4:= leastelement M hfinite k n hk hn hkn hskn X h11 h10 h30,
    cases h4 with p h40,
    cases h40 with hp h42,
    use p,
    rw h50 at hp,
    rw Z_mexists_members at hp,
    cases hp with h43 h44,
    split,
    {
      exact h43,
    },
    {
      rw sym at h44,
      split,
      {
        exact h44,
      },
      {
        intros l hl hkl,
        specialize h42 l,
        apply h42,
        rw Z_mexists_members,
        rw sym at hkl,
        exact ⟨ hl, hkl⟩, 
      }
    }
  end

 
lemma E24:  ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n → ∀ (a:M), a ∈ USC(LOOP n)→ 
∀ (p q:M), p ∈ USC(LOOP n) → q ∈ LOOP n → 
‹ p, q › = ‹ a, n › ∨ ¬ (‹ p, q › = ‹ a, n ›):=
  assume hfinite k n hk hn hkn hskn a ha p q hp hq,
  begin
    have h100:= L1 M  k n hk hn hkn hskn,
    have h20:= loopfinite M hfinite k n hk hn hkn hskn,
    have h21:= (uscfinite M (LOOP n)).mpr h20,
    have h81:= finitedecidable M (LOOP n) h20,
    rw decidable_members at h81,
    have h82:= finitedecidable M (USC (LOOP n)) h21,
    rw decidable_members at h82,
    have h83:= h81 q n ⟨hq,h100.left⟩,
    have h84:= h82 p a ⟨ hp, ha⟩, 
    cases h83 with h85 h86,
    {
      rw h85 at *,
      cases h84 with h87 h88,
      {
        rw h87 at *,
        simp,
      },
      {
        right,
        rw ordered_pair_equality,
        simp,
        exact h88,
      }
    },
    {
      right,
      rw ordered_pair_equality,
      intro h,
      cases h with h2 h3,
      contradiction,
    }
  end

 
lemma SGMapsLoop: ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n → 
maps M (SG M) (LOOP n)(LOOP n):=
  assume hfinite k n hk hn hkn hskn,
  begin
    unfold maps,
    repeat{split},
    {
      exact SGRel M,
    },
    {
      intros x y h,
      cases h with h2 h3,
      rw SG_members at h3,
      cases h3 with p h4,
      cases h4 with h5 h6,
      rw ordered_pair_equality at h5,
      cases h5 with h6 h8,
      rw h6 at *,
      rw h8 at *, 
      have h7:= L1 M k n hk hn hkn hskn,
      exact h7.right p h2,
    },
    {
      intros x y z h4,
      rcases h4 with ⟨ h5, h6, h7⟩, 
      have h8:= SGFUNC M,
      rw FUNC_members at h8,
      exact h8 x y z h6 h7,
    },
    {
      intros x hxloop,
      use (S x),
      split,
      {
        have h7:= L1 M k n hk hn hkn hskn,
        exact h7.right x hxloop,
      },
      {
        rw SG_members,
        use x,
        simp,
        have h3:= LN M k n hk hn hkn hskn,
        exact member_subset M (LOOP n) ℕℕ x h3 hxloop,
      }
    }
  end

lemma qsx: ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n → 
∀ (q:M), q ∈ ℕℕ  → ∀ (x:M), x ∈ LOOP n → Ap (Ap q (SG M)) x ∈ LOOP n:=
  assume hfinite k n hk hn hkn hskn,
  begin
    have  base: ChurchZero ∈ Z_qsx M n:=
      begin
        rw Z_qsx_members,
        split,
        {
          exact zeroN M,
        },
        {
          intros x hloopx,
          have h3:= ApZero M (SG M),
          rw h3,
          have h4:= ApId M x,
          rw h4,
          exact hloopx,
        }
      end,
    have step: ∀ (q:M), q ∈ Z_qsx M n → ¬ q = n → S q ∈ Z_qsx M n:=
      begin
        intros q h3 hqn,
        rw Z_qsx_members at h3,
        rw Z_qsx_members,
        cases h3 with hq h5,
        split,
        {
          exact successorN M q hq,
        },
        {
          intros x hxloop,
          have h7:= SGMapsLoop M hfinite k n hk hn hkn hskn,
          have h6:= successorequation M (LOOP n) (SG M) (SGFUNC M) (SGRel M) h7 q x hq hxloop,
          rw h6,
          have h8:= h5 x hxloop,
          unfold maps at h7,
          rcases h7 with ⟨ h10, h11, h12, h13⟩,
          have h14:= h11 (Ap (Ap q (SG M)) x) (Ap (SG M) (Ap (Ap q (SG M)) x) ),
          apply h14,
          split,
          {
            exact h8,
          },
          {
            rw SG_members,
            have h20:= LN M  k n hk hn hkn hskn,
            have h21:= member_subset M (LOOP n) ℕℕ (Ap (Ap q (SG M)) x ) h20 h8,
            have h9:= ApSG M (Ap (Ap q (SG M)) x) h21,
            simp_rw h9,
            use Ap (Ap q (SG M)) x,
            simp,
            exact h21,
          }
        }
      end,
    intros q hq,
    have h:= finiteinduction M hfinite k n hk hn hkn hskn (Z_qsx M n) ⟨ base, step⟩,
    rw subset_definition at h,
    intros x hxloop,
    have h3:= h q hq,
    rw Z_qsx_members at h3,
    exact h3.right x hxloop,
  end

lemma loopaddition:  ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n → 
∀ (z:M), z ∈ LOOP n → ∃ (x:M), x ∈ ℕℕ ∧ z = n ⊕ x:=
  assume hfinite k n hk hn hkn hskn,
  begin
    have base: n ∈ Z_loopaddition M n:=
      begin
        rw Z_loopaddition_members,
        split,
        {
          have h3:= L1 M k n hk hn hkn hskn,
          exact h3.left,
        },
        {
          use ChurchZero,
          split,
          {
            exact zeroN M,
          },
          {
            rw ChurchZero_equation,
            exact hn,
          }
        }
      end,
    have step: ∀ (z:M), z ∈ Z_loopaddition M n → S z ∈ Z_loopaddition M n:=
      assume z h,
      begin
        rw Z_loopaddition_members at h,
        cases h with h2 h3,
        cases h3 with x h4,
        cases h4 with h5 h6,
        rw Z_loopaddition_members,
        split,
        {
          exact (L1 M k n hk hn hkn hskn).right z h2,
        },
        {
          use S x,
          split,
          {
            exact successorN M x h5,
          },
          {
            rw ChurchAddition_equation,
            rw h6,
            exact hn,
            exact h5,
          }
        }
      end,
    intros z hzloop,
    rw LoopDefinition at hzloop,
    cases hzloop with h4 h5,
    have h6:= h5 (Z_loopaddition M n) base step,
    rw Z_loopaddition_members at h6,
    exact h6.right,
  end

lemma orderq_helper: ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n → 
∀ (q:M), q ∈ ℕℕ → ¬ q = ChurchZero →  Ap (Ap q (SG M)) n = n →
∀ (x:M), x ∈ LOOP n → Ap (Ap q (SG M)) x = x :=
  assume hfinite k n hk hn hkn hskn q hq hqn h1,
  begin
    have h3:= L1 M k n hk hn hkn hskn,
    cases h3 with h4 h5,
    have base: n ∈ Z_orderq_helper M n q:=
      begin
        rw Z_orderq_helper_members M n q,
        split,
        {
          exact h4,
        },
        {
          exact h1,
        }
      end,
    have step: ∀ (x:M), x ∈ Z_orderq_helper M n q → S x ∈ Z_orderq_helper M n q:=
      assume x,
      begin
        intro h,
        rw Z_orderq_helper_members M n q at h,
        rw Z_orderq_helper_members M n q,
        cases h with h6 h7,
        split,
        {
          exact h5 x h6,
        },
        {
          have h9:= SGMapsLoop M hfinite k n hk hn hkn hskn,
          have h8:= successorequation M (LOOP n) (SG M) (SGFUNC M)(SGRel M) h9 q x hq h6,
          have h12:= LN M k n hk hn hkn hskn,
          have hx:= member_subset M (LOOP n) ℕℕ x h12 h6,
          have h11:= ApSG M x hx,
          rw h11 at *,
          have h13:= ApSG M q hq,
          rw h13 at *,
          have h20:= doubleiteration M q hq (LOOP n) (SG M) (S ChurchZero) x (SGFUNC M) h9 (successorN M ChurchZero (zeroN M)) h6,
          rw ChurchSuccessorShift M ChurchZero (zeroN M) q hq at h20,
          rw ChurchZero_equation (S q)(successorN M q hq) at h20,
          have h21: Ap (Ap (S ChurchZero) (SG M)) x = S x :=
            begin
               have h30:= successorequation M (LOOP n) (SG M) (SGFUNC M)(SGRel M) h9 ChurchZero x (zeroN M) h6,
               rw h30,
               have h31:= zeroAp M (SG M) x,
               rw h31,
               have h32:= ApSG M x hx,
               exact h32,
            end,
          rw h21 at h20,
          rw h20,
          rw h7 at h8,
          rw h11 at h8,
          exact h8,
        }
      end,
    intros x h,
    rw LoopDefinition at h,
    cases h with h40 h41,
    have h42:=  h41 (Z_orderq_helper M n q) base step,
    rw Z_orderq_helper_members at h42,
    exact h42.right,
  end

lemma loopcounting: ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n → 
( ∀ (x:M), x ∈ ℕℕ →  Ap ( Ap x (SG M)) ChurchZero = x) →
∀ (q:M), q ∈ ℕℕ → Ap ( Ap q (SG M)) n = n ⊕ q:=
  assume hfinite k n hk hn hkn hskn ChurchCountingAxiom q hq,
  begin
    have h1:= ChurchCountingAxiom n hn,
    have h2: Ap ( Ap q (SG M)) (Ap (Ap n (SG M)) ChurchZero) = Ap ( Ap q (SG M))n :=
      begin
        rw h1, 
      end,
    have h3:= doubleiteration M q hq ℕℕ (SG M) n ChurchZero (SGFUNC M) (SGMaps M) hn (zeroN M),
    rw h2 at h3,
    have h4:=ChurchAdditionMaps M q hq n hn,
    rw ChurchAdditionCommutative M n hn q hq at h3,
    rw ChurchCountingAxiom (n ⊕ q) h4 at h3,
    exact h3,
  end

lemma additionmapsloop:ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n → 
∀ (x:M), x ∈ LOOP n → ∀ (y:M), y ∈ ℕℕ  → x ⊕ y ∈ LOOP n:=
  assume hfinite k n hk hn hkn hskn x hxloop,
  begin
    have hxn: x ∈ ℕℕ :=
      begin
        have h20:= LN M k n hk hn hkn hskn,
        exact member_subset M (LOOP n) ℕℕ x h20 hxloop,
      end,
    have base: ChurchZero ∈ Z_additionmapsloop M n x:=
      begin
        rw Z_additionmapsloop_members,
        split,
        {
          exact zeroN M,
        },
        { 
          have h3:= ChurchZero_equation  x hxn,
          rw h3,
          exact hxloop,
        }
      end,
    have step: ∀ (y:M), y ∈ Z_additionmapsloop M n x → S y ∈ Z_additionmapsloop M n x:=
      begin
        intros y h,
        rw Z_additionmapsloop_members at h,
        cases h with hy h3,
        rw Z_additionmapsloop_members,
        split,
        {
          exact successorN M y hy,
        },
        {
          rw ChurchAddition_equation x y hxn hy,
          have h4:= L1 M k n hk hn hkn hskn,
          cases h4 with h5 h6,
          exact h6 (x ⊕ y) h3,
        }
      end,
    intros y hy,
    rw N_members at hy,
    have h30:= hy (Z_additionmapsloop M n x)⟨base, step⟩, 
    rw Z_additionmapsloop_members at h30,
    exact h30.right,
  end


lemma knm: ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n → 
∀ (m:M), m ∈ ℕℕ → k ⊕ m = n → n ⊕ m = n:=
  assume hfinite k n hk hn hkn hskn m hm hkm,
  begin
    have h2: S (k ⊕ m) = S n:=
      begin
        rw hkm,
      end,
    have h3:= (StemDefinition k).mp hk, 
    have h4:= h3.left,
    have h5:= ChurchAddition_equation k m h4 hm,
    rw← h5 at h2,
    have h6:=  ChurchSuccessorShift M m hm k h4,
    rw h6 at h2,
    rw hskn at h2,
    rw← ChurchSuccessorShift M m hm n hn at h2,
    rw ChurchAddition_equation n m hn hm at h2,
    have hnloop:= (L1 M k n hk hn hkn hskn).left,
    have h7:= additionmapsloop M hfinite k n hk hn hkn hskn n hnloop m hm,
    have h8:= looponeone M hfinite k n hk hn hkn hskn (n ⊕ m) n h7 hnloop h2,
    exact h8,
  end

lemma predecessornotn:  ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n → 
∀ (x:M), x ∈ ℕℕ → ¬ x = ChurchZero → 
∃ (r:M), r ∈ ℕℕ ∧ S r = x ∧ ¬ r = n:=
  assume hfinite k n hk hn hkn hskn x hx h2,
  begin
    have h3:= predecessor M x hx h2,
    cases h3 with u h4,
    cases h4 with hu h6,
    have h80:= finitedecidable M ℕℕ hfinite,
    rw decidable_members at h80,
    have h81:= h80 u n ⟨ hu, hn⟩, 
    cases h81 with h20 h21,
    { 
      use k,
      have hk2:= member_subset M STEM ℕℕ k (SN M) hk,
      split,
      {
        exact hk2, 
      },
      {
        rw h20 at *,
        rw← hskn at h6,
        exact ⟨ h6, hkn⟩, 
      }
    },
    { 
      use u,
      split,
      {
        exact hu,
      },
      {
        exact ⟨ h6, h21⟩, 
      }
    }
  end

 
lemma xfmaps: ∀ (X f x:M), f ∈ FUNC → Rel f → maps M f X X → x ∈ X → 
∀ (q:M), q ∈ ℕℕ  → Ap (Ap q f) x ∈ X:=
  assume X f x hFUNC hRel hmaps hx,
  begin
    have base: ChurchZero ∈ Z_xfmaps M f X x:=
      begin
        rw Z_xfmaps_members,
        split,
        {
          exact zeroN M,
        },
        {
          rw zeroAp,
          exact hx,
        }
      end,
    have step: ∀ (q:M), q ∈ Z_xfmaps M f X x → S q ∈ Z_xfmaps M f X x:=
      begin
        intros q h4,
        rw Z_xfmaps_members M f X x at h4,
        rw Z_xfmaps_members M f X x,
        cases h4 with hq hIH, 
        have h3:= successorequation M X f hFUNC hRel hmaps q x hq hx,
        split,
        {
          exact successorN M q hq,
        },
        {
          rw h3,
          set p:= Ap (Ap q f) x with h50,
          have h5:= Apmaps M X f p hmaps hFUNC hIH,
          unfold maps at hmaps,
          rcases hmaps with ⟨ hRel, h6, h7, h8⟩,
          have h9:= h6 p (Ap f p),
          apply h9,
          exact ⟨ hIH, h5⟩, 
        }
      end,
    intros q hq,
    rw N_members at hq,
    specialize hq (Z_xfmaps M f X x),
    have h5:= hq ⟨base,step⟩,
    rw Z_xfmaps_members  at h5,
    exact h5.right,
  end

lemma nplusm: ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n → 
∀ (x:M), x ∈ ℕℕ → ¬ x = ChurchZero → n = k ⊕  x → n = n ⊕  x:=
  assume hfinite k n hk hn hkn hskn x hx hxn h2,
  begin 
    have h3: S n = S (k ⊕ x):=
      begin
        rw h2,
      end,
    have hk2:= member_subset M  STEM ℕℕ k (SN M) hk,
    rw←  ChurchAddition_equation k x hk2 hx at h3,
    rw ChurchSuccessorShift M x hx k hk2  at h3,
    rw hskn at h3,
    rw← ChurchSuccessorShift M x hx n hn  at h3,
    rw ChurchAddition_equation n x hn hx at h3,
    have h10:= L1 M k n hk hn hkn hskn,
    cases h10  with hloopn h11,
    have h12:= additionmapsloop M hfinite k n hk hn hkn hskn n hloopn x hx,
    have h4:= looponeone M hfinite k n hk hn hkn hskn n (n ⊕ x) hloopn h12 h3,
    exact h4,
  end

lemma smloop: ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n → 
∀ (m:M), m ∈ ℕℕ → k ⊕  m = n → 
∀ (x:M), x ∈ LOOP n → Ap (Ap m (SG M)) x = x:=
  assume hfinite k n hk hn hkn hskn m hm hkplusm,
  begin
    have hk2: k ∈ ℕℕ := member_subset M STEM ℕℕ k (SN M) hk, 
    have h1: ¬ m = ChurchZero:=
      begin
        intro h,
        rw h at *,
        rw ChurchZero_equation k hk2 at hkplusm,
        contradiction,
      end,
    set f:= restrict (SG M) (LOOP n) with h50,
    have hRel: Rel f:=
      begin
        rw Rel_definition,
        intros t hf,
        rw h50 at hf,
        have h10:= restrict_definition (SG M)(LOOP n),
        rw h10 at hf,
        rw intersection_axiom at hf,
        cases hf with h11 h12,
        rw product_axiom at h12,
        cases h12 with a h13,
        cases h13 with b h14,
        use a, use b,
        exact h14.right.right,
      end,
    have hFUNC: f ∈ FUNC:=
      begin
        rw FUNC_members,
        intros x y z h2 h3,
        rw h50 at h2 h3,
        rw restriction at h2 h3,
        cases h2 with h4 h5,
        cases h3 with h6 h7,
        rw SG_members at h4 h6,
        cases h6 with a h8,
        cases h4 with b h9,
        rw ordered_pair_equality at h8 h9,
        cases h9 with h10 h11,
        cases h8 with h12 h13,
        cases h10 with h14 h15,
        cases h12 with h16 h17,
        rw← h14 at *,
        rw← h16 at *,
        rw h15,
        rw h17,
      end,
    have hdom: dom f ⊆ LOOP n:=
      begin
        rw subset_definition,
        intros t ht,
        rw domain_axiom f hRel  at ht,
        cases ht with y h10,
        rw h50 at h10,
        rw restriction at h10,
        exact h10.right,
      end,
    have hmaps: maps M f (LOOP n)(LOOP n):=
      begin
        unfold maps,
        split,
        {
          exact hRel,
        },
        {
          repeat{split},
          {
            intros x y h10,
            cases h10 with h11 h12,
            rw h50 at h12,
            rw restriction at h12,
            cases h12 with h13 h14,
            rw SG_members at h13,
            cases h13 with a h15,
            cases h15 with h16 h17,
            rw ordered_pair_equality at h16,
            cases h16 with h18 h19,
            rw← h18 at *,
            have h20:= L1 M k n hk hn hkn hskn,
            rw h19,
            exact h20.right x h11,
          },
          {
            intros x y z h,
            rcases h with ⟨h10, h11, h12⟩,
            have h13:= hFUNC,
            rw FUNC_members at h13,
            exact h13 x y z h11 h12,
          },
          {
            intros x hx,
            use S x,
            have h20:= L1 M k n hk hn hkn hskn,
            cases h20 with h21 h22,
            split,
            {
              exact h22 x hx,
            },
            {
              rw h50,
              rw restriction,
              rw SG_members,
              split,
              {
                use x,
                simp,
                have h23:= LN M  k n hk hn hkn hskn,
                exact member_subset M (LOOP n) ℕℕ x h23 hx,
              },
              {
                exact hx,
              }
            }
          }
        }
      end,
    have honeone: oneone M f (LOOP n)(LOOP n):=
      begin
        unfold oneone,
        split,
        {
          exact hmaps,
        },
        {
          split,
          {
            intros x u y,
            rw h50,
            rw restriction,
            rw restriction,
            rw SG_members,
            rw SG_members,
            intro h,
            rcases h with ⟨ h10, h11, h12⟩, 
            cases h10 with h13 h14,
            cases h11 with h15 h16,
            cases h13 with a h17,
            cases h15 with b h18,
            cases h17 with h19 h20,
            cases h18 with h21 h22,
            rw ordered_pair_equality at h19 h21,
            cases h21 with h26 h23,
            cases h19 with h24 h25,
            rw← h26 at *,
            rw← h24 at *,
            rw h25 at h23,
            have h27:= looponeone M hfinite k n hk hn hkn hskn x u h12 h16 h23,
            exact h27,
          },
          {
            intros x y h10,
            cases h10 with h11 h12,
            rw h50 at h11,
            rw restriction at h11,
            cases h11 with h13 h14,
            exact h14,
          }
        }
      end,
    have hrange: range f ⊆ LOOP n:=
      begin
        rw subset_definition,
        intros t h,
        rw range_axiom f hRel at h,
        cases h with x h2,
        rw h50 at h2,
        rw restriction at h2,
        cases h2 with h3 h4,
        rw SG_members at h3,
        cases h3 with a h5,
        cases h5 with h6 h7,
        rw ordered_pair_equality at h6,
        cases h6 with h8 h9,
        rw← h8 at *,
        have h20:= L1 M k n hk hn hkn hskn,
        rw h9 at *,
        exact h20.right x h4,
      end,
    have hinjection: injection M f (LOOP n):=
      begin
        unfold injection,
        exact ⟨ honeone, hRel, hFUNC, hdom, hrange⟩,
      end,
    have E4672: ∀ (q:M), q ∈ ℕℕ → ∀(x:M), x ∈ LOOP n → Ap (Ap q f) x = Ap (Ap q (SG M)) x:=
      begin
        have base: ChurchZero ∈ Z_E4672 M n f:=
          begin
            rw Z_E4672_members,
            split,
            {
              exact zeroN M,
            },
            {
              intros x hxloop,
              rw ApZero,
              rw ApZero,
            }
          end,
        have step: ∀ (q:M), q ∈ Z_E4672 M n f → S q ∈ Z_E4672 M n f:=
          begin
            intros q h,
            rw Z_E4672_members at h,
            rw Z_E4672_members,
            cases h with hq h3,
            split,
            {
              exact successorN M q hq,
            },
            {
              intros x hxloop,
              have h4:= successorequation M (LOOP n) f hFUNC hRel hmaps q x hq hxloop,
              rw h4,
              have h5:= successorequation M (LOOP n) (SG M) (SGFUNC M) (SGRel M) (SGMapsLoop M hfinite k n hk hn hkn hskn) q x hq hxloop,
              rw h5,
              have h6:= h3 x hxloop,
              rw h6,
              have h7:= xsmapsloop M hfinite k n hk hn hkn hskn q hq x hxloop,
              have h8:= Apdef M f hFUNC (Ap (Ap q (SG M)) x) (Ap (SG M) (Ap (Ap q (SG M)) x)),
              symmetry,
              apply h8,
              rw h50,
              rw ApSG,
              rw restriction,
              rw and_comm,
              split,
              {
                exact h7,
              },
              { 
                rw SG_members,
                use Ap (Ap q (SG M)) x,
                simp,
                have h9:= LN M k n hk hn hkn hskn,
                exact member_subset M (LOOP n) ℕℕ (Ap (Ap q (SG M)) x) h9 h7, 
              },
              {
                have h9:= LN M k n hk hn hkn hskn,
                exact member_subset M (LOOP n) ℕℕ (Ap (Ap q (SG M)) x) h9 h7, 
              }
            }
          end,
        intros q hq,
        rw N_members at hq,
        specialize hq (Z_E4672 M n f),
        have h3:= hq ⟨ base, step⟩,
        rw Z_E4672_members M n f at h3,
        exact h3.right,
      end,
    rw sym at hkplusm,
    have h10:= nplusm M hfinite k n hk hn hkn hskn m hm h1 hkplusm,
    rw sym at h10,
    have h2:= annihilation M n m hn hm h10 (LOOP n) f hinjection,
    intros x hxloop,
    have h3:= h2 x hxloop,
    have h4:= E4672 m hm x hxloop,
    rw h4 at h3,
    exact h3,
  end

lemma successorflip: ∀ (t q:M), t ∈ ℕℕ → q ∈ ℕℕ → Ap (Ap q (SG M)) (S t) = S (Ap (Ap q (SG M)) t):=
  assume t q ht hq,
  begin
    have h1: Ap (Ap ChurchZero (SG M)) t  = t:=
      begin
        rw ApZero,
        rw ApId,
      end,
    have h2: S(Ap (Ap ChurchZero (SG M)) t) = S t:=
      begin
        rw h1,
      end,
    have h3: Ap( Ap q (SG M)) t ∈ ℕℕ :=
      begin
        have h4:= xsmapsN M q hq t ht,
        exact h4,
      end,
    have h9:= doubleiteration M q hq ℕℕ (SG M) (S ChurchZero) t (SGFUNC M) (SGMaps M) (successorN M ChurchZero (zeroN M)) ht,
    rw ApOne M (SG M)(SGFUNC M) (SGRel M)  at h9,
    rw ApSG at h9,
    rw ChurchSuccessorShift M ChurchZero (zeroN M) q hq at h9,
    rw ChurchZero_equation (S q)(successorN M q hq) at h9,
    have h10:= successorequation M ℕℕ (SG M) (SGFUNC M)(SGRel M) (SGMaps M) q t hq ht,
    rw h10 at h9,
    rw ApSG at h9,
    exact h9,
    exact h3,
    exact ht,
  end

lemma orderq_helper2: ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n → 
∀ (q:M), q ∈ ℕℕ → ¬ q = ChurchZero → 
∀ (t:M), t ∈ LOOP n → Ap (Ap q (SG M)) t = t →
∀ (x:M), x ∈ LOOP n → Ap (Ap q (SG M)) x = x:=
  assume hfinite k n hk hn hkn hskn q hq hqn,
  begin
    have h80:=decidable0 M q hq,
    have h81:= nneqzero M k n hk hn hkn hskn,
    have h2:= L1 M k n hk hn hkn hskn,
    cases h2 with hnloop h1,
    have h30:= LN M k n hk hn hkn hskn,
   
    have base: n ∈ Z_orderq_helper2 M n q:=
      begin
        rw Z_orderq_helper2_members M n q,
        have h3:= orderq_helper M hfinite k n hk hn hkn hskn q hq hqn,
        exact ⟨ hnloop, h3⟩, 
      end,
    have step: ∀ (t:M), t ∈ Z_orderq_helper2 M n q → S t ∈ Z_orderq_helper2 M n q:=
      begin
        intros t h,
        rw Z_orderq_helper2_members M n q at h,
        rw Z_orderq_helper2_members M n q,
        cases h with htloop h2,
        have ht:= member_subset M (LOOP n) ℕℕ t h30 htloop,
        have hstloop:= h1 t htloop,
        split,
        { 
          exact hstloop,
        },
        {
          have h5:= successorflip M t q ht hq,
          intro h,
          rw h at h5,
          have h6: Ap (Ap q (SG M)) t ∈ LOOP n:=
            begin
              have h23:= xsmapsloop M hfinite k n hk hn hkn hskn q hq t htloop,
              exact h23,
            end,
          have h7:= looponeone M hfinite k n hk hn hkn hskn t ( Ap  (Ap q (SG M)) t) htloop h6 h5,
          rw sym at h7,
          have h8:= h2 h7,
          exact h8,
        }
      end,
    intros t h34,
    rw LoopDefinition at h34,
    cases h34 with ht h5,
    have h6:= h5 (Z_orderq_helper2 M n q) base step,
    rw Z_orderq_helper2_members at h6,
    exact h6.right, 
  end




#axioms_all 