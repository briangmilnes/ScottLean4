-- Theory of ≺ and ≼ 

import ChurchNumbers2

variables (M:Type) [Model M] (a b x y z u v w X R W κ μ ℓ : M)
-- using ℓ where the source text has λ because you can't use λ for a variable.

open Model 

lemma kinN:   ∀ (k n:M), k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n → k ∈ ℕℕ :=
  begin
    intros  k n hk hn hkn hskn,
    have h191:= LcupS M k n hk hn hkn hskn,
    rw full_extensionality at h191,
    specialize h191 k,
    rw h191,
    rw binary_union_axiom,
    right,
    exact hk,
  end

lemma nnotinstem:  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k=n → S k = S n → ¬ n ∈ STEM:=
  begin
    intros k n hk hn hkn hskn h3,
    have h19:= kinN M k n hk hn hkn hskn,
    have hkncopy:= hkn,
    have hskncopy:= hskn,
    rw sym at hkn hskn,
    have h20:= Smax M n k h3 h19 hkn hskn k,
    have hkcopy:= hk,
    rw h20 at hk,
    cases hk with h21 h22,
    have h23:= Smax M k n hkcopy hn hkncopy hskncopy n,
    rw h23 at h3,
    cases h3 with h24 h25,
    cases h22 with h26 h27,
    {
      cases h25 with h28 h29,
      {
        have h30:= transitivity M k n k h21 h24 h21 h26 h28,
        have h31:= knotlessthank M k n hkcopy h24 hkncopy hskncopy,
        contradiction,
      },
      {
        have h31:= knotlessthank M k n hkcopy h24 hkncopy hskncopy,
        rw h29 at *,
        contradiction,
      }
    },
    {
      have h31:= knotlessthank M k n hkcopy h24 hkncopy hskncopy,
      rw← h27 at *,
      contradiction,
    }  
  end

theorem rho: ℕℕ ∈ FINITE M →  ∀ (k n j l:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n →
 j ∈ ℕℕ → l ∈ ℕℕ → ¬ j = l → S j = S l → j <ℕ  l → j=k ∧ l=n:=
  begin
    intros hfinite k n j l hk hn hkn hskn hj hl hjl hsjl hjlessl,
    have h3: ¬ l ∈ STEM:=
      begin
        intro h4,
        have h5:= Sinit M l hl j hj h4 hjlessl,
        have h7: S j ∈ STEM:=
          begin
            have h30:= (S1 M).right j hj h5,
            apply h30,
            intros v hv hjv,
            have h32: ¬ j = k:= 
              begin
                intro h,
                rw h at *,
                have h33:=Smax M k n hk hn hkn hskn l,
                rw h33 at h4,
                cases h4 with h34 h35,
                cases h35 with h36 h37,
                {
                  have h38:= transitivity M k l k hj h34 hj hjlessl h36,
                  have h39:= knotlessthank M k n hk hn hkn hskn,
                  contradiction,
                },
                { 
                  rw sym at h37,
                  contradiction,
                }
              end,
            have h31:= kisunique M k n hk hn hkn hskn j h5 h32 v hv,
            rw sym at hjv,
            symmetry,
            exact h31 hjv,
          end,
        have h8:= Soneone M j l h5 h7 hl hsjl,
        contradiction,
      end,
    have h5:j ∈ STEM :=
      begin
        have h6:= LcupS M k n hk hn hkn hskn,
        rw full_extensionality at h6,
        specialize h6 l,
        rw h6 at hl,
        rw binary_union_axiom at hl,
        cases hl with h7 h8,
        { have h9: ¬ j ∈ LOOP n:=
            begin
              intro h,
              rw sym at hsjl,
              have h10:= looponeone M hfinite k n hk hn hkn hskn l j h7 h hsjl,
              rw sym at h10,
              contradiction,
            end,
          have h10:= LcapS M k n hk hn hkn hskn,
          have h11:= LcupS M k n hk hn hkn hskn,
          rw full_extensionality at h11,
          specialize h11 j,
          rw h11 at hj,
          rw binary_union_axiom at hj,
          cases hj with h12 h13,
          {
            contradiction,
          },
          {
            exact h13,
          }
        },
        {
          contradiction,
        }
      end, 
    have h6:= Smax M k n hk hn hkn hskn,
    have h7: ¬ S k ∈ STEM:=
      begin
        intro h,
        have h8:= Soneone M k n hk h hn hskn,
        contradiction, 
      end,
    have h8: ¬ k = S k:=
      begin
        intro h,
        rw h at hk,
        contradiction,  
      end,
    have h190: k ∈ ℕℕ:= kinN M k n hk hn hkn hskn,
    have h9: j = k ∨ ¬ j = k:=
      begin
        have h200:= finitedecidable M ℕℕ hfinite,
        rw decidable_members at h200,
        have h201:= h200 j k ⟨ hj, h190⟩,
        exact h201,
      end,
    cases h9 with h10 h11,
    {
      split,
      {
        exact h10,
      },
      {
        rw h10 at *,
        have h12: S n = S l:=
          begin
            rw← hskn,
            rw hsjl,
          end,
        have h13:= LcupS M k n hk hn hkn hskn,
        rw full_extensionality at h13,
        have h14:= (h13 l).mp hl,
        rw binary_union_axiom at h14,
        have h24:= (h13 n).mp hn,
        rw binary_union_axiom at h24,
        cases h14 with h15 h16,
        {
          have h17:= (L1 M k n hk hn hkn hskn).right l h15,
          have h18:= looponeone M hfinite k n hk hn hkn hskn l n h15,
          have h123:=   (L1 M k n hk hn hkn hskn).left,
          rw sym at h12,
          exact h18 h123 h12,
        },
        {
          contradiction,
        }  
      }
    },
    { 
      have h9:= kisunique M k n hk hn hkn hskn j h5 h11,
      have h10:= (S1 M).right j hj h5,
      have h11: S j ∈ STEM:=
        begin
          apply h10,
          intros v hv hjv,
          rw sym at hjv,
          have h12:= h9 v hv hjv,
          symmetry,
          exact h12,
        end,
      have h13:=Soneone M j l h5 h11 hl hsjl,
      contradiction, 
    }
  end
    
lemma preceq_helper:  ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n →
∀ (X:M),X ⊆ ℕℕ →  
((∀ (u:M), u ∈ X → (∀ (v:M),v ∈ ℕℕ → v<ℕ u → S u = S v → u = v) → S u ∈ X)
 ↔ (∀ (u:M), u ∈ X → ¬ u = n → S u ∈ X)):=
  begin
    intros hfinite k n hk hn hkn hskn X hX,
    have h20:= finitedecidable  M ℕℕ hfinite,
    rw decidable_members at h20, 
    split,
    { --left to right
      intros h u hu hun,
      have h3:= h u hu,
      apply h3,
      intros v hv hvu,
      have h5:= member_subset M X ℕℕ u hX hu,

      have h7:= h20 u v ⟨ h5, hv⟩, 
      cases h7 with h8 h9,
      {
        rw h8 at *,
        simp,
      },
      {
        rw sym at h9,
        intro h10,
        rw sym at h10, 
        have h6:= rho M hfinite k n v u hk hn hkn hskn hv h5 h9 h10 hvu,
        rw h6.left at *,
        rw h6.right at *,
        contradiction,
      }
    },
    { --right to left
      intros h2793 u hu h3,
      have h4: ¬ u = n:=
        begin
          intro h,
          rw h at *,
          have h6:= kinN M k n hk hn hkn hskn,
          have h7:= klessthann M k n hk hn hkn hskn,
          have h8:= h3 k h6 h7,
          rw sym at hskn,
          rw sym at hkn,
          exact hkn (h8 hskn),
        end,
      exact h2793 u hu h4, 
    }
  end

lemma preceq:  ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n →
∀ (x y:M), x ≼ y ↔ 
(∀ (w:M),  ℕℕ = (w ∪ (ℕℕ -w)) → x ∈ w → ( ∀ (u:M), u ∈ w → ¬ u = n → S u ∈ w)  → y ∈ w) :=
  begin
    intros hfinite k n hk hn hkn hskn x y,
    split,
    {
      intros h w hw hx hclosure,
      rw preceq_definition at h,
      have h4:= h w hw,
      apply h4,
      { 
        intros  u hu h5,
        apply hclosure,
        {
          exact hu,
        },
        {
          intro h6,
          rw h6 at *,
          have h7:= kinN M k n hk hn hkn hskn,
          have h8:= klessthann M k n hk hn hkn hskn,
          have h9:= h5 k h7 h8,
          rw sym at h9,
          have h10:= h9 hskn,
          rw sym at h10, 
          contradiction, 
        }
      },
      {
        exact hx,
      } 
    },
    {
      intro h,
      have h10:= preceq_helper M hfinite k n hk hn hkn hskn, 
      rw preceq_definition,
      intros w hw,
      have h11:= h w hw,
      have h34: w ⊆ ℕℕ:=
        begin
          rw subset_definition,
          intro t,
          rw full_extensionality at hw,
          specialize hw t,
          intro h,
          rw hw,
          rw binary_union_axiom,
          left,
          exact h,
        end,
      have h12:= h10 w h34,
      rw← h12 at h11,
      intros  h33 hx,
      have h33:= h11 hx h33,
      exact h33,
    }
  end 

lemma preceqtrans: ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n →
∀ (x y z:M), x ≼ y → y ≼ z → x ≼ z:=
  begin
     intros hfinite k n hk hn hkn hskn x y z hxy hyz,
     have h3:= preceq M hfinite k n hk hn hkn hskn,
     rw (h3 x z),
     intros w hw hxw hclosure,
     have h5:= (h3 x y).mp hxy w hw hxw,
     have h7:= (h3 y z).mp hyz w hw (h5 hclosure) hclosure,
     exact h7,
  end

lemma preceqreflexive: ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n → ∀ (x:M),
x ∈ ℕℕ → x ≼ x:=
  begin
    intros hfinite k n hk hn hkn hskn x hx,
    have h3:= preceq M hfinite k n hk hn hkn hskn,
    have h4:= h3 x x,
    rw h4,
    intros w hw hx hclosure,
    exact hx, 
  end

lemma preceqzero: ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n → ∀ (x:M),
x ∈ ℕℕ → x ≼ ChurchZero → x = ChurchZero :=
  begin
    intros hfinite k n hk hn hkn hskn x hxn hx,
    have h3:= preceq M hfinite k n hk hn hkn hskn,
    have h4:= h3 x ChurchZero,
    rw h4 at hx,
    set Z:= ℕℕ  - (single ChurchZero) with h50,
    have h5: ∀ (u:M), u ∈ Z → ¬ u = n → S u ∈ Z:=
      begin
        intros u hu h6,
        rw h50,
        rw minus_members,
        rw singleton1,
        rw h50 at hu,
        rw minus_members at hu,
        rw singleton1 at hu,
        cases hu with h7 h8,
        have h9:= successorN M u h7,
        split,
        {
          exact h9,
        },
        {
          exact successoromitszero M u h7,
        }
      end,
    have h6: Z ⊆ ℕℕ :=
      begin
        rw subset_definition,
        intro t,
        intro h,
        rw h50 at h,
        rw minus_members at h,
        exact h.left,
      end,
    have h34: ℕℕ = (Z ∪ (ℕℕ - Z)):=
      begin
        rw full_extensionality,
        intro t,
        rw h50,
        rw binary_union_axiom,
        rw minus_members,
        rw minus_members,
        rw singleton1,
        rw minus_members,
        rw singleton1,
        have h60:= finitedecidable M ℕℕ hfinite,
        rw decidable_members at h60,
        split,
        {
          intro h,
          have h61:= h60 t ChurchZero ⟨ h, zeroN M⟩, 
          cases h61 with h62 h63,
          {
            rw h62 at *, 
            right,
            split,
            {
              exact h,
            },
            {
              intro h63,
              cases h63 with h64 h65,
              contradiction, 
            }
          },
          {
            left,
            exact ⟨ h, h63⟩, 
          }
        },
        {
          intro h,
          cases h with h65 h66,
          {
            exact h65.left,
          },
          {
            exact h66.left, 
          }
        }
      end,
    have h8:= hx Z h34,
    have h9:= finitedecidable M ℕℕ hfinite,
    rw decidable_members at h9,
    have h10:= h9 x ChurchZero ⟨ hxn, zeroN M ⟩,
    cases h10 with h11 h12,
    {
      exact h11,
    },
    {
      have h13: ¬ x ∈ Z:=
        begin
          intro h,
          have h14:= h8 h h5,
          rw h50 at h14,
          rw minus_members at h14,
          rw singleton1 at h14,
          cases h14 with h15 h16,
          contradiction,
        end,
      rw h50 at h13,
      rw minus_members at h13,
      rw singleton1 at h13,
      have h14: x ∈ ℕℕ ∧ ¬ x = ChurchZero:=
        begin
          exact ⟨ hxn, h12⟩, 
        end,
      contradiction,
    }
  end

lemma preceqsuccessor: ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n →
∀ (x y:M), x ∈ ℕℕ → y ∈ ℕℕ → ¬ y = n →
( x ≼ S y ↔ x ≼ y ∨ x = S y):=
  begin
    intros hfinite k n hk hn hkn hskn x y hx hy hyn,
    have h3:= preceq M hfinite k n hk hn hkn hskn,
    have h4:= finitedecidable M ℕℕ hfinite,
    rw decidable_members at h4,
    have h5:= h4 x (S y) ⟨ hx, (successorN M y hy)⟩ ,
    split,
    { --left to right,
      intro h,
      cases h5 with h6 h7,
      {
        right,
        exact h6,
      },
      {
        left,
        have h8:= h3 x y,
        rw h8,
        intros X hX hxw hclosure,
        have h20: y ∈ X ∨ ¬ y ∈ X:=
          begin
            rw full_extensionality at hX,
            specialize hX y,
            rw hX at hy,
            rw binary_union_axiom at hy,
            cases hy with h21 h22,
            {
              left, 
              exact h21,
            },
            {
              rw minus_members at h22,
              right,
              exact h22.right,
            }
          end,
        cases h20 with h21 h22,
        {
          exact h21,
        },
        { 
          set Z:= X - single (S y) with h50,
          have h23: ℕℕ = (Z ∪ (ℕℕ -Z)):=
            begin
              rw full_extensionality,
              intro t,
              rw binary_union_axiom,
              rw minus_members,
              rw singleton1,
              rw minus_members,
              rw h50,
              rw minus_members,
              rw singleton1,
              split,
              {
                intro ht,
                have h24: t ∈ X ∨ ¬ t ∈ X:=
                  begin
                    rw full_extensionality at hX,
                    specialize hX t,
                    rw hX at ht,
                    rw binary_union_axiom at ht,
                    cases ht with h25 h26,
                    {
                      left,
                      exact h25,
                    },
                    {
                      right,
                      rw minus_members at h26,
                      exact h26.right,
                    }
                  end,
                have h27:= h4 t (S y) ⟨ ht, successorN M y hy⟩,
                cases h24 with h25 h26,
                {
                  cases h27 with h28 h29,
                  {
                    right,
                    split,
                    {
                      exact ht,
                    },
                    {
                      intro h29,
                      cases h29 with h30 h31,
                      contradiction,
                    }
                  },
                  {
                    left,
                    exact ⟨ h25, h29⟩,
                  }
                },
                {
                  right,
                  split,
                  {
                    exact ht,
                  },
                  {
                    intro h28,
                    cases h28 with h29 h30,
                    contradiction,
                  }
                }
              },
              {
                intro h23,
                cases h23 with h24 h25,
                {
                  cases h24 with h26 h27,
                  rw full_extensionality at hX,
                  specialize hX t,
                  apply hX.mpr,
                  rw binary_union_axiom,
                  left,
                  exact h26,
                },
                {
                  exact h25.left, 
                }
              }
            end,
          have h24: x ∈ Z:=
            begin
              rw h50,
              rw minus_members,
              rw singleton1,
              exact ⟨ hxw, h7⟩, 
            end,
          have h10: ∀ (u : M), u ∈ Z → ¬u = n → S u ∈ Z:=
            begin
              intros u hu hun,
              have hucopy := hu,
              rw minus_members at hucopy,
              rw singleton1 at hucopy, 
              have h11:= hclosure u hucopy.left hun,
              rw h50,
              rw minus_members,
              split,
              {
                exact h11,
              },
              { 
                intro h,
                rw singleton1 at h, 
                cases hucopy with h13 h14,
                rw h50 at hu,
                rw minus_members at hu,
                cases hu with h16 h17,
                have hun: u ∈ ℕℕ :=
                  begin
                    rw hX,
                    rw binary_union_axiom,
                    left,
                    exact h16, 
                  end,
                have h18:= trichotomy1 M u hun y hy,
                have h40:= h4 u y ⟨ hun, hy⟩,
                cases h40 with h41 h42,
                {
                  rw h41 at *,
                  contradiction,
                },
                {
                  cases h18 with h19 h20,
                  {
                    have h30:= rho M hfinite k n u y hk hn hkn hskn hun hy h42 h h19,
                    cases h30 with h31 h32,
                    contradiction, 
                  },
                  {
                    rw sym at h42 h,
                    cases h20 with h32 h33,
                    {
                      rw sym at h32,
                      contradiction,
                    },
                    {
                      have h30:= rho M hfinite k n y u hk hn hkn hskn hy hun h42 h h33,
                      cases h30 with h32 h33,
                      contradiction, 
                    }
                  }
                }
              }
            end,
          have h30:= preceq M hfinite k n hk hn hkn hskn x (S y),
          have h31:= h30.mp h Z h23 h24 h10,
          rw h50 at h31,
          rw minus_members at h31,
          cases h31 with h32 h33,
          rw singleton1 at h33,
          contradiction,
        }
      }
    },
    { --right to left,
      intro h,
      cases h with h20 h21,
      {
        have h22:= preceq M hfinite k n hk hn hkn hskn x (S y),
        rw h22,
        have h23:= preceq M hfinite k n hk hn hkn hskn x y,
        rw h23 at h20,
        intros X h100 h101 h102,
        have h103:= h20 X h100 h101 h102,
        have h104:= h102 y h103 hyn,
        exact h104,
      },
      {
        rw h21,
        have h22:= preceqreflexive M hfinite k n hk hn hkn hskn (S y) (successorN M y hy),
        exact h22,
      }
    }
  end 

lemma precmin_helper: ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n →   ChurchZero ≼ k:=
  begin
    intros hfinite k n hk hn hkn hskn,
    have h4:= preceq_definition ChurchZero k,
    rw h4,
    intros X hX hclosed hzero,
    rw StemDefinition k at hk,
    cases hk with h5 h6,
    have h7:= h6 X hzero,
    apply h7,
    intros u hun huX h8,
    have h9:= hclosed u huX,
    apply h9,
    intros v hv h10 huv,
    exact h8 v hv huv,
  end

lemma precmin: ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n → ∀ (x:M), x ∈ ℕℕ → ChurchZero ≼ x:=
  begin
    intros hfinite k n hk hn hkn hskn,
    have base: ChurchZero ∈ Z_precmin M:=
      begin
        rw Z_precmin_members,
        split,
        {
          exact zeroN M,
        },
        {
          have h3:= preceqreflexive M hfinite k n hk hn hkn hskn ChurchZero (zeroN M),
          exact h3,
        }
      end,
    have step: ∀ (x:M), x ∈ Z_precmin M → S x ∈ Z_precmin M:=
      begin
        intros x h,
        rw Z_precmin_members at h,
        cases h with hx h3,
        rw Z_precmin_members,
        have h20:= finitedecidable M ℕℕ hfinite,
        rw decidable_members M at h20,
        have h21:= h20 x n ⟨ hx, hn⟩,
        cases h21 with h22 h23,
        {
          rw h22 at *,
          split,
          {
            exact successorN M n hx,
          },
          {
            rw← hskn,
            have h4:= precmin_helper M hfinite k n hk hn hkn hskn,
            have h23:k ∈ ℕℕ :=
              begin
                have h24:= LcupS M k n hk hn hkn hskn,
                rw h24,
                rw binary_union_axiom,
                right,
                exact hk,
              end,
            have h5:=  preceqsuccessor M hfinite k n hk hn hkn hskn ChurchZero k (zeroN M) h23 hkn,
            rw h5,
            left,
            exact h4, 
          }
        },
        { 
          split,
          {
            exact successorN M x hx,
          },
          {
            have h4:= preceqsuccessor  M hfinite k n hk hn hkn hskn ChurchZero x (zeroN M) hx h23,
            rw h4,
            left,
            exact h3,
          }
        }
      end,
    intros n h,
    rw N_members at h,
    specialize h (Z_precmin M),
    have h3:= h (and.intro base step), 
    rw Z_precmin_members at h3,
    exact h3.right, 
  end

lemma precmin2:  ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n →
∀ (x:M), x ∈ ℕℕ → ¬ (x ≺ ChurchZero):=
  begin
    intros hfinite k n hk hn hkn hskn x hx,
    have h40:= finitedecidable M ℕℕ,
    rw decidable_members at h40,
    have hdecidable:= h40 hfinite,
    have h3:= prec_definition x ChurchZero,
    rw h3,
    intros h,
    cases h with h4 h5,
    set Z:= ℕℕ - (single (ChurchZero:M)) with h50,
    have h6:= preceq M hfinite k n hk hn hkn hskn x ChurchZero,
    rw h6 at h4,
    specialize h4 Z,
    have h7: ¬ ChurchZero ∈ Z:=
      begin
        rw h50,
        intro h,
        rw minus_members at h,
        rw singleton1 at h,
        cases h with h8 h9,
        contradiction, 
      end,
    apply h7,
    apply h4,
    { 
      rw full_extensionality,
      intro t,
      rw binary_union_axiom,
      rw minus_members,
      rw singleton1,
      rw minus_members,
      rw h50,
      rw minus_members,
      rw singleton1, 
      split,
      {
        intro ht,
        have h8:= hdecidable t ChurchZero ⟨ ht, zeroN M⟩,
        cases h8 with h9 h10,
        {
          right,
          split,
          {
            exact ht,
          },
          {
            intro h10,
            cases h10 with h11 h12,
            contradiction,
          }
        },
        {
          left,
          exact ⟨ ht, h10⟩,
        }
      },
      {
        intro h11,
        cases h11 with h12 h13,
        { 
          exact h12.left,
        },
        {
          exact h13.left,
        }
      }
    },
    { 
      rw h50,
      rw minus_members,
      rw singleton1,
      split,
      {
        exact hx,
      },
      {
        exact h5,
      }
    },
    {
      intros u hu hun,
      rw h50 at hu,
      rw h50,
      rw minus_members,
      rw singleton1,
      rw minus_members at hu,
      cases hu with h8 h9,
      split,
      {
        exact successorN M u h8,
      },
      {
        have h10:= successoromitszero M u h8,
        exact h10,
      }
    }
  end

lemma Ndecidable:  ℕℕ ∈ FINITE M → 
∀ (x y:M), x ∈ ℕℕ → y ∈ ℕℕ → x = y ∨ ¬(x=y):=
  begin
    intros hN,
    intros x y hx hy,
    have h10:= finitedecidable M ℕℕ hN,
    rw decidable_members at h10,
    have h11:= h10 x y ⟨hx, hy⟩, 
    exact h11, 
  end

lemma precnoinsertions:  ℕℕ ∈ FINITE M → ∀(k n:M), k ∈ STEM → n ∈ ℕℕ → ¬ k = n →  S k = S n → 
∀ (x y:M), x ∈ ℕℕ → y ∈ ℕℕ →  x ≺ y → S x ≼ y := 
  begin
    intros hN k n hk hn hkn hskn,
    intros x y hx hy h4,
    rw prec_definition at h4,
    cases h4 with h5 h6,
    have h7:= (preceq M hN k n hk hn hkn hskn (S x) y),
    rw h7,
    intros X h8 h9 h10,
    have h200: X ⊆ ℕℕ:=
      begin
        have h201:= h8,
        rw full_extensionality at h201,
        rw subset_definition,
        intros t ht,
        have h202:= h201 t,
        rw h202,
        rw binary_union_axiom,
        left,
        exact ht,
      end,
    set Z:= X ∪ single x with Zdef,
    have h40: x ∈ Z:=
      begin
        have h41:= Zdef,
        rw full_extensionality at h41,
        have h42:= h41 x,
        rw h42,
        rw binary_union_axiom,
        right,
        rw singleton1,
      end,
    have h49:= klessthann M k n hk hn hkn hskn,
    have h48:= Ndecidable M hN,
    have h50: ℕℕ = (Z ∪ (ℕℕ - Z)):=
      begin
        rw full_extensionality,
        intros t,
        split,
        {
          intros ht,
          rw binary_union_axiom,
          rw minus_members,
          rw Zdef,
          have h52:= h48 t x ht hx,
          cases h52 with h53 h54,
          {
            rw h53 at *,
            left,
            rw binary_union_axiom,
            right,
            rw singleton1,
          },
          {
            rw full_extensionality at h8,
            have h55:= (h8 t).1 ht,
            rw binary_union_axiom at h55,
            cases h55 with h56 h57,
            {
              left,
              rw binary_union_axiom,
              left,
              exact h56,
            },
            {
              right,
              split,
              {
                exact ht,
              },
              {
                rw binary_union_axiom,
                intros h,
                cases h with h60 h61,
                {
                  rw minus_members at h57,
                  cases h57 with h58 h59,
                  contradiction,
                },
                {
                  rw singleton1 at h61,
                  contradiction,
                }
              }
            }
          }
        },
        {
          intros h,
          rw binary_union_axiom at h,
          cases h with h70 h71,
          {
            rw Zdef at h70,
            rw binary_union_axiom at h70,
            cases h70 with h72 h73,
            {
              exact member_subset M X ℕℕ t h200 h72,
            },
            {
              rw singleton1 at h73,
              rw h73 at *,
              exact hx,
            }
          },
          {
            rw minus_members at h71,
            exact h71.1,
          }
        }
      end,
    have h79:  ∀ (u : M), u ∈ Z → ¬u = n → S u ∈ Z:=
      begin
        intros u h90 h91,
        rw Zdef at h90,
        rw Zdef,
        rw binary_union_axiom at h90,
        rw binary_union_axiom,
        cases h90 with h92 h93,
        {
          left,
          exact h10 u h92 h91,
        },
        {
          rw singleton1 at h93,
          rw h93 at *,
          left,
          exact h9,
        }
      end,
    have h80:= (preceq M hN k n hk hn hkn hskn x y).1 h5 Z h50 h40 h79,
    rw Zdef at h80,
    rw binary_union_axiom at h80,
    cases h80 with h81 h82,
    {
      exact h81,
    },
    {
      rw singleton1 at h82,
      rw h82 at *,
      contradiction,
    }
  end

lemma precmax:  ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → (¬ k=n) → S k = S n → 
∀ (x:M), x ∈ ℕℕ → x ≼ n:=
  begin
    intros hfinite k n hk hn h2 hskn z hz,
    have hkn: k <ℕ n:=
      begin
        have h3:= klessthann M k n hk hn h2 hskn,
        exact h3,
      end,
    have h40:= finitedecidable M ℕℕ hfinite,
    rw decidable_members at h40,
    have hdecidable:= h40,  
    have h3033: S k ≼ n:=
      begin
        have h20:= preceq M hfinite k n hk hn h2 hskn (S k) n,
        rw h20,
        intros X hX hsk hclosure,
        set Z:= (X ∪ (single n)) with h50, 
        have hZclosed: ∀ (u:M), u ∈ Z → S u ∈ Z:=
          begin
            intros x hx,
            rw h50 at hx,
            rw binary_union_axiom at hx,
            have h60: x ∈ ℕℕ:=
              begin
                rw hX,
                rw binary_union_axiom,
                rw minus_members,
                rw singleton1 at hx,
                cases hx with h61 h62,
                {
                  left,
                  exact h61,
                },
                {
                  rw h62 at *,
                  rw hX at hn,
                  rw binary_union_axiom at hn,
                  rw minus_members at hn,
                  exact hn,
                }

              end,
            cases hx with h51 h52,
            {
              have h53:= hdecidable x n  ⟨ h60, hn⟩,
              cases h53 with h54 h55,
              {
                rw h54 at *,
                rw←  hskn,
                rw h50,
                rw binary_union_axiom,
                left,
                exact hsk,
              },
              {
                have h56:= hclosure x h51 h55,
                rw h50,
                rw binary_union_axiom,
                left,
                exact h56,
              }
            },
            {
              rw singleton1 at h52,
              rw h52 at *,
              rw← hskn,
              rw h50,
              rw binary_union_axiom,
              left,
              exact hsk,
            } 
          end,
        have h60: LOOP n ⊆ Z:=
          begin
            rw subset_definition,
            intros t h61,
            rw LoopDefinition at h61,
            cases h61 with ht hclosure,
            have h63: n ∈ Z:=
              begin
                rw h50,
                rw binary_union_axiom,
                rw singleton1,
                right,
                refl,
              end,
            have h62:= hclosure Z h63 hZclosed,
            exact h62,
          end,
        have h61:= (L1 M k n hk hn h2 hskn).left,
        have h62:= (S1 M).left,
        have h63: ¬ (n = ChurchZero):=
          begin
            intro h,
            rw← h at h62,
            have h64:= LcapS M k n hk hn h2 hskn,
            rw full_extensionality at h64,
            specialize h64 n,
            rw intersection_axiom at h64,
            have h65:= h64.mp ⟨ h61, h62⟩,
            exact emptyset_axiom n h65,  
          end,
        have h64:= looponto M k n hk hn h2 hskn n h61,
        cases h64 with r h65,
        cases h65 with h66 h67,
        have h68:= member_subset M (LOOP n) Z r h60 h66,
        have h69: ¬ (r = n):=
          begin
            intro h,
            rw h at *,
            have h70:= snneqn M n hn,
            contradiction,
          end,
        have h71: r ∈ X:=
          begin
            rw h50 at h68,
            rw binary_union_axiom at h68,
            rw singleton1 at h68,
            cases h68 with h72 h73,
            {
              exact h72,
            },
            {
              contradiction,
            }
          end,
        have h72: S r ∈ X:= hclosure r h71 h69,
        rw h67 at h72,
        exact h72,
      end,   
    have base: ChurchZero ∈ Z_precmax M n:=
      begin
        rw Z_precmax_members M n,
        split,
        {
          exact zeroN M,
        },
        {
          have h3:= precmin M hfinite k n hk hn h2 hskn n hn,
          exact h3,
        }
      end,
    have step: ∀(x:M), x ∈ Z_precmax M n → S x ∈ Z_precmax M n:=
      begin
        intros x h51,
        rw Z_precmax_members M n at h51,
        cases h51 with hx h52,
        have hIH:= h52,
        rw Z_precmax_members M n,
        split,
        {
          exact successorN M x hx,
        },
        { 
          have h20:= hdecidable x n ⟨ hx, hn⟩, 
          cases h20 with h21 h22,
          {
            rw h21,
            rw← hskn,
            exact h3033,
          },
          { have h100: x ≺ n:=
              begin
                rw prec_definition,
                exact ⟨ h52, h22⟩,
              end,
            have h101:= precnoinsertions M hfinite k n hk hn h2 hskn x n hx hn h100,
            exact h101,
          }
        }
      end,     
    rw N_members at hz,
    specialize hz (Z_precmax M n),
    have h3:= hz (and.intro base step), 
    rw Z_precmax_members M n at h3,
    exact h3.right, 
  end

lemma leftpreceqsuccessor:ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n →
∀ (x y:M), x ∈ ℕℕ → y ∈ ℕℕ → x ≺ y → S x ≼ y:=
  begin
    intros hfinite k n hk hn hkn hskn x y hx hy hxy,
    rw preceq M  hfinite k n hk hn hkn hskn,
    intros X hX hsx hclosure,
    set Z:= X ∪ (single x) with h50,
    have hsep: ℕℕ = (Z ∪ (ℕℕ -Z)):=
      begin
        rw full_extensionality,
        intro t,
        have hdecidable:= finitedecidable M ℕℕ hfinite,
        rw decidable_members M at hdecidable,
        rw full_extensionality at hX,
        specialize hX t,
        split,
        {
          intro ht,
          rw hX at ht,
          rw binary_union_axiom at ht,
          cases ht with h20 h21,
          {
            rw binary_union_axiom,
            left,
            rw h50,
            rw binary_union_axiom,
            left,
            exact h20,
          },
          {
            rw minus_members at h21,
            cases h21 with h22 h23,
            rw binary_union_axiom,
            have h24:= hdecidable t x ⟨h22, hx⟩, 
            cases h24 with h25 h26,
            {
              rw h25 at *,
              left,
              rw h50,
              rw binary_union_axiom,
              right,
              rw singleton1,
            },
            {
              right,
              rw minus_members,
              split,
              {
                exact h22,
              },
              {
                intro h,
                rw h50 at h,
                rw binary_union_axiom at h,
                cases h with h51 h52,
                {
                  contradiction,
                },
                {
                  rw singleton1 at h52,
                  contradiction,
                }
              }
            } 
          }
        },
        {
          intro h,
          rw hX,
          rw binary_union_axiom at h,
          cases h with h51 h52,
          {
            rw h50 at h51,
            rw binary_union_axiom at h51,
            rw binary_union_axiom,
            cases h51 with h53 h54,
            {
              left, 
              exact h53,
            },
            {
              rw singleton1 at h54,
              rw h54 at *,
              rw hX at hx,
              rw binary_union_axiom at hx,
              exact hx,
            }
          },
          {
            rw minus_members at h52,
            cases h52 with h53 h54,
            rw binary_union_axiom,
            right,
            rw minus_members,
            split,
            {
              exact h53,
            },
            {
              rw h50 at h54,
              rw binary_union_axiom at h54,
              intro h,
              exact h54 (or.inl h),
            }
          }
        }
      end,
    have h10:S x ∈ Z:=
      begin
        rw h50,
        rw binary_union_axiom,
        left,
        exact hsx,
      end,
    have h11: x ∈ Z:=
      begin
        rw h50,
        rw binary_union_axiom,
        rw singleton1,
        right,
        refl,
      end,
    have h12: x ≼ y:=
      begin
        rw prec_definition at hxy, 
        exact hxy.left, 
      end,
    rw preceq M hfinite k n hk hn hkn hskn at h12,
    have hZclosed:∀ (u : M), u ∈ Z → ¬u = n → S u ∈ Z:=
      begin
        intros u hu hun,
        rw h50 at hu,
        rw binary_union_axiom at hu,
        rw singleton1 at hu,
        cases hu with h13 h14,
        {
          have h15:= hclosure u h13 hun,
          rw h50,
          rw binary_union_axiom,
          left,
          exact h15,
        },
        {
          rw h14 at *,
          exact h10,
        }
      end,
    have h13:= h12 Z hsep h11 hZclosed,
    rw h50 at h13,
    rw binary_union_axiom at h13,
    cases h13 with h15 h16,
    {
      exact h15,
    },
    {
      rw singleton1 at h16,
      rw h16 at *,
      rw prec_definition at hxy,
      cases hxy with h17 h18,
      contradiction,
    }
  end

lemma finiteinduction: ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n → ∀ (X:M),
ChurchZero ∈ X ∧ ( ∀ (u:M), u ∈ X → ¬(u = n) → S u ∈ X)
→ ℕℕ ⊆ X:=
  begin
    intros hfinite k n hk hn hkn hskn X hclosure,
    have base: ChurchZero ∈ Z_finiteinduction M X:=
      begin
        rw Z_finiteinduction_members M X,
        split,
        {
          exact zeroN M,
        },
        {
          intros x hx h4,
          have h5:= preceqzero M hfinite k n hk hn hkn hskn x hx h4,
          rw h5 at *,
          exact hclosure.left,
        }
      end,
    have step: ∀ (x:M),x ∈ Z_finiteinduction M X → S x ∈ Z_finiteinduction M X:=
      begin
        intros x h3,
        have hdecidable:= finitedecidable M ℕℕ hfinite,
        rw decidable_members at hdecidable,
        rw Z_finiteinduction_members M X at h3,
        rw Z_finiteinduction_members M X,
        cases h3 with hx h5,
        have h40:= hdecidable x n ⟨ hx, hn⟩,
        split,
        {
          exact successorN M x hx,
        },
        {
          intros t ht h6,
          have h7:= h5 t ht,
          have h8 := preceqsuccessor M hfinite k n hk hn hkn hskn t x ht hx,
          cases h40 with h41 h42,
          {
            rw h41 at *,
            apply h7,
            have h43:= precmax M hfinite k n hk hn hkn hskn t ht,
            exact h43,
          },
          {
            have h44:= h8 h42,
            rw h44 at h6,
            cases h6 with h45 h46,
            {
              exact h7 h45,
            },
            {
              rw h46 at *,
              cases hclosure with h47 h48,
              have h50:= preceqreflexive M hfinite k n hk hn hkn hskn x hx,
              have h49:= h5 x hx h50,
              exact h48 x h49 h42,
            }
          }
        }
      end,
    have hconclusion: ∀ (z:M),z ∈ ℕℕ → ∀ (x:M),(x ∈ ℕℕ → x ≼ z → x ∈ X):=
      begin
        intros z hz,
        rw N_members at hz,
        specialize hz (Z_finiteinduction M X),
        have h3:= hz (and.intro base step), 
        rw Z_finiteinduction_members M X at h3,
        exact h3.right,  
      end,
    rw subset_definition,
    intros z hz,
    have h52:= preceqreflexive M hfinite k n hk hn hkn hskn z hz,
    have h53:= hconclusion z hz z hz h52,
    exact h53, 
  end 

theorem prectrichotomy1:  ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n →
∀ (x y:M), x ∈ ℕℕ → y ∈ ℕℕ → x ≼ y ∨ y ≼ x:=
  begin
    intros hfinite k n hk hn hkn hskn,
    have base: ChurchZero ∈ Z_prectrichotomy1 M:=
      begin
        rw Z_prectrichotomy1_members,
        split,
        {
          exact zeroN M,
        },
        {
          intros y hy,
          left,
          have h4:= precmin M hfinite k n hk hn hkn hskn y hy,
          exact h4,
        }
      end,
    have step: ∀ (x:M),x ∈ Z_prectrichotomy1 M → ¬(x = n) → S x ∈ Z_prectrichotomy1 M:=
      begin
        intros x hIH0 h3,
        rw Z_prectrichotomy1_members at hIH0,
        cases hIH0 with h4 hIH,
        rw Z_prectrichotomy1_members,
        split,
        {
          exact successorN M x h4,
        },
        {
          intros y hy,
          have h40:= finitedecidable M ℕℕ hfinite,
          rw decidable_members at h40,
          have hdecidable:= h40 x y ⟨ h4, hy⟩,
          have h41: x ≼ y ↔ x ≺ y ∨ x = y:=
            begin
              cases hdecidable with h42 h43,
              {
                rw h42,
                have h44:= preceqreflexive M hfinite k n hk hn hkn hskn y hy,
                split,
                {
                  intro h45,
                  right,
                  refl,
                },
                {
                  intro h45,
                  exact h44,
                }
              },
              {
                rw prec_definition,
                split,
                {
                  intro h44,
                  left,
                  exact ⟨ h44, h43⟩,
                },
                {
                  intro h45,
                  cases h45 with h46 h47,
                  {
                    exact h46.left,
                  },
                  {
                    rw h47,
                    exact preceqreflexive M hfinite k n hk hn hkn hskn y hy,
                  }
                }
              }
            end,
          have h5:= hIH y hy,
          cases h5 with h6 h7,
          {
            rw h41 at h6,
            cases h6 with h42 h43,
            {
              have h44:= leftpreceqsuccessor M hfinite k n hk hn hkn hskn x y h4 hy h42,
              left,
              exact h44,
            },
            {
              rw h43 at *,
              right,
              have h46:= preceqsuccessor M hfinite k n hk hn hkn hskn y y hy hy h3,
              rw h46,
              left,
              exact preceqreflexive M hfinite k n hk hn hkn hskn y hy,
            }
          },
          {
            right,
            have h48:= preceqsuccessor M hfinite k n hk hn hkn hskn y x hy h4 h3,
            rw h48,
            left,
            exact h7,
          }
        }
      end,
    have h100:=finiteinduction M hfinite k n hk hn hkn hskn (Z_prectrichotomy1 M),
    have h101:= h100 ⟨ base, step⟩,
    intro x,
    rw subset_definition at h101,
    intros y hx hy,
    have h102:= h101 x hx,
    rw Z_prectrichotomy1_members at h102,
    cases h102 with h103 h104,
    exact h104 y hy,
  end

lemma successorprec:  ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n →
∀ (x:M), x ∈ ℕℕ →  ∀ (y:M), y ∈ ℕℕ → ¬ (y=n) → S y ≺ x → y ≼ x:=
  begin
    intros hfinite k n hk hn hkn hskn,
    have base: ChurchZero ∈ Z_successorprec M n:=
      begin
        rw Z_successorprec_members M n,
        split,
        {
          exact zeroN M,
        },
        {
          intros y hy hyn h3,
          have h4:= precmin2 M hfinite k n hk hn hkn hskn (S y) (successorN M y hy),
          contradiction,
        }
      end,
    have step: ∀ (x:M), x ∈ Z_successorprec M n → ¬ (x = n) → S x ∈ Z_successorprec M n:=
      begin
        intros x h3 hxn,
        rw Z_successorprec_members M n at h3,
        cases h3 with hx hIH,
        rw Z_successorprec_members M n,
        split,
        {
          exact successorN M x hx,
        },
        {
          intros y hy hyn h4,
          rw prec_definition at h4,
          cases h4 with h5 h6,
          have h7:= preceqsuccessor M hfinite k n hk hn hkn hskn (S y) x (successorN M y hy) hx hxn,
          rw h7 at h5,
          rw or_comm at h5,
          cases h5 with h6 h7,
          {
            contradiction,
          },
          {
            have h8: y ≼ S y:=
              begin
                have h9:= preceqsuccessor M hfinite k n hk hn hkn hskn   y y  hy hy hyn,
                rw h9,
                left,
                exact preceqreflexive M hfinite k n hk hn hkn hskn  y hy,
              end,
            have h10:= preceqtrans M hfinite k n hk hn hkn hskn y (S y) x h8 h7,
            have h11:= preceqsuccessor M hfinite k n hk hn hkn hskn y x hy hx hxn,
            rw h11,
            left,
            exact h10,
          }
        }
      end,
    have h100:=finiteinduction M hfinite k n hk hn hkn hskn (Z_successorprec  M n),
    have h101:= h100 ⟨ base, step⟩,
    intro x,
    rw subset_definition at h101,
    intros hx y hy hyn,
    have h102:= h101 x hx,
    rw Z_successorprec_members M n at h102,
    cases h102 with h103 h104,
    exact h104 y hy hyn,
  end

lemma sxnotprecx:  ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n →
∀ (x:M), x ∈ ℕℕ → ¬ (x = n) → ¬ (S x ≺ x):=
  begin
    intros hfinite k n hk hn hkn hskn x hx hxn h,
    have h40:= finitedecidable M ℕℕ hfinite,
    rw decidable_members at h40,
    set Z:= Z_sxnotprecx M x with h50,
    rw prec_definition at h,
    cases h with h3 h4,
    have h3copy:= h3,
    have h5:= preceq M hfinite k n hk hn hkn hskn (S x) x,
    rw h5 at h3,
    specialize h3 Z, 
    have base: ChurchZero ∈ Z:=
      begin
        rw h50,
        rw Z_sxnotprecx_members,
        split,
        {
          exact zeroN M,
        },
        {
          intro h6,
          cases h6 with h7 h8,
          have h9:= preceqzero M hfinite k n hk hn hkn hskn (S x) (successorN M x hx) h7,
          have h10:= successoromitszero M x hx,
          contradiction,
        }
      end,
    have step: ∀ (u:M), u ∈ Z → ¬(u = n) → S u ∈ Z:=
      begin
        intros u h6 hun,
        rw h50 at h6,
        rw Z_sxnotprecx_members at h6,
        cases h6 with hu h7,
        rw Z_sxnotprecx_members,
        split,
        {
          exact successorN M u hu,
        },
        {
          intros h8,
          cases h8 with h9 h10,
          apply h7,
          have h11:= preceqsuccessor M hfinite k n hk hn hkn hskn (S x) u (successorN M x hx) hu hun,
          rw h11 at h9,
          cases h9 with h12 h13,
          {
            split,
            {
              exact h12,
            },
            {
              have h14:= preceqreflexive M hfinite k n hk hn hkn hskn u hu,
              have h15:= preceqsuccessor M hfinite k n hk hn hkn hskn u u hu hu hun,
              have h16:= h15.mpr (or.inl h14),
              have h17:= preceqtrans M hfinite k n hk hn hkn hskn u (S u) x h16 h10,
              exact h17,
            }
          },
          { have h14:= h40 u x ⟨ hu, hx⟩, 
            cases h14 with h15 h16,
            {
              rw h15 at *,
              split,
              {
                exact h3copy,
              },
              {
                exact preceqreflexive M hfinite k n hk hn hkn hskn x hx,
              }
            },
            {
              have h13copy:= h13,
              rw sym at h13,
              have h17:= rho M hfinite k n u x hk hn hkn hskn hu hx h16 h13,
              rw sym at h16, 
              have h18:= rho M hfinite k n x u hk hn hkn hskn hx hu h16 h13copy,
              have h19:= trichotomy1 M x hx u hu,
              cases h19 with h20 h21,
              {
                have h22:= h18 h20,
                cases h22 with h23 h24,
                contradiction,
              },
              {
                cases h21 with h22 h23,
                {
                  rw←  h22 at *,
                  split,
                  {
                    exact h3copy,
                  },
                  {
                    exact preceqreflexive M hfinite k n hk hn hkn hskn x hx,
                  }
                },
                {
                  have h24:= h17 h23,
                  cases h24 with h25 h26,
                  contradiction,           
                }
              }
            }
          }
        }
      end,
    have h100:=finiteinduction M hfinite k n hk hn hkn hskn Z,
    have h101:= h100 ⟨ base, step⟩,
    rw subset_definition at h101,
    have h102:= h101 x hx,
    rw h50 at h102,
    rw Z_sxnotprecx_members at h102,
    cases h102 with h103 h104,
    apply h104,
    split,
    {
      exact h3copy,
    },
    {
      exact preceqreflexive M hfinite k n hk hn hkn hskn x hx,
    }
  end 

theorem prectrichotomy2: ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n →
∀ (y:M), y ∈ ℕℕ → ∀ (x:M), x ∈ ℕℕ → ¬ (x=y) →  ¬ (x ≼ y ∧ y ≼ x) :=
  begin
    intros hfinite k n hk hn hkn hskn,
    have base: ChurchZero ∈ Z_prectrichotomy2 M:=
      begin
        rw Z_prectrichotomy2_members,
        split,
        {
          exact zeroN M,
        },
        {
          intros x hx h4 h7,
          cases h7 with h5 h6,
          have h8:= preceqzero M hfinite k n hk hn hkn hskn x hx h5,
          contradiction,
        }
      end,
    have step: ∀ (y:M), y ∈ Z_prectrichotomy2 M → ¬ (y = n)→ S y ∈ Z_prectrichotomy2 M:=
      begin
        intros y h3 hyn,
        rw Z_prectrichotomy2_members at h3,
        cases h3 with hy hIH,
        rw Z_prectrichotomy2_members,
        split,
        {
          exact successorN M y hy,
        },
        {
          intros x hx hxy h,
          cases h with h26 h27,
          have h20:= preceqsuccessor M hfinite k n hk hn hkn hskn x y hx hy hyn,
          rw h20 at h26,
          rw or_comm at h26,
          cases h26 with h30 h28,
          {
            contradiction,
          },
          {
            have h29: S y ≺ x:=
              begin
                rw prec_definition,
                rw sym at hxy,
                exact ⟨ h27, hxy⟩,
              end,
            have h30:= successorprec M hfinite k n hk hn hkn hskn x hx y hy hyn h29,
            have h31:= hIH x hx,
            have h32: ¬ x = y:=
              begin
                intro h,
                rw h at *,
                have h33:= sxnotprecx M hfinite k n hk hn hkn hskn y hy hyn,
                contradiction,
              end,
            have h33:= h31 h32,
            exact h33 ⟨ h28, h30⟩,
          }
        }
      end,
    have h100:=finiteinduction M hfinite k n hk hn hkn hskn (Z_prectrichotomy2  M),
    have h101:= h100 ⟨ base, step⟩,
    intro x,
    rw subset_definition at h101,
    intros hx y hy hyn,
    have h102:= h101 x hx,
    rw Z_prectrichotomy2_members M at h102,
    cases h102 with h103 h104,
    exact h104 y hy hyn,
  end

theorem prectrichotomy3: ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n →
∀ (y:M), y ∈ ℕℕ → ∀ (x:M), x ∈ ℕℕ →    (x ≼ y ∧ y ≼ x) → x = y :=
  begin
    intros hfinite k n hk hn hkn hskn,
    intros y hy x hx h3,
    have h2:= prectrichotomy2 M hfinite k n hk hn hkn hskn y hy x hx,
    have h80:= finitedecidable M ℕℕ hfinite,
    rw decidable_members at h80,
    have h81 := h80 x y ⟨ hx, hy⟩, 
    cases h81 with h82 h83,
    { 
      exact h82,
    },
    {
      have h84:= h2 h83,
      contradiction,
    }
  end

lemma prectrans: ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n →
∀ (x y z:M), x ∈ ℕℕ → y ∈ ℕℕ → z ∈ ℕℕ → x ≺ y → y ≺ z → x ≺ z:=
  assume hfinite k n hk hn hkn hskn x y z hx hy hz h2 h3,
  begin
    rw prec_definition at h2 h3,
    cases h3 with h4 h5,
    cases h2 with h6 h7,
    rw prec_definition,
    have h8:= preceqtrans M hfinite k n hk hn hkn hskn x y z h6 h4,
    split,
    {
      exact h8,
    },
    {
      intro h,
      rw h at *,
      have h9:= prectrichotomy3 M hfinite k n hk hn hkn hskn y  hy z hz ⟨ h6, h4⟩,
      rw h9 at *,
      contradiction, 
    }
  end

lemma xpreceqsx: ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n →
∀ (x:M), x ∈ ℕℕ →  ¬ (x = n) → x ≼ S x:=
assume hfinite k n hk hn hkn hskn x hx hxn,
begin
  have h4:= preceqsuccessor M hfinite k n hk hn hkn hskn x x hx hx hxn,
  rw h4,
  left,
  exact preceqreflexive M hfinite k n hk hn hkn hskn x hx,
end

#axioms_all

