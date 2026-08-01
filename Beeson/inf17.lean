import inf16 
variables (M:Type) [Model M] (a b x y z u v w X R W κ μ ℓ : M)

open Model 

lemma Ncone: ∀ (x:M), x ∈ USC(𝕍) ↔ Nc M x = one:=
  assume x,
  begin
    have h2:= usc M 𝕍 x,
    have h3: x ∈ USC(𝕍) ↔ ∃(a:M), x = single a:=
      begin
        rw h2,
        split,
        {
          intro h,
          cases h with a h4,
          cases h4 with h5 h6,
          use a,
          exact h6,
        },
        {
          intro h,
          cases h with a h4,
          use a,
          split,
          {
            have h5:=V_definition a,
            exact h5,
          },
          {
            exact h4,
          }
        }
      end,
    have h4:= one_members M,
    have h6:  Nc M x = one ↔ ∃(a:M), x = single a:=
      begin
        split,
        {
          intro h,
          apply (h4 x).mp,
          rw← h,
          exact xinNcx M x,
        },
        {
          intro h,
          rw←  (h4 x) at h,
          rw full_extensionality,
          intros t,
          have h10:= Nc_members M x t,
          rw h10,
          have h11:= oneF M,
          have h13:= zeroinone M,
          have h12:= finitecardinals2 M x zero one h11 h h13,
          rw h4 t,
          have h14:=  similar_to_singleton M t,
          split,
          {
            intro h,
            have h15: similar M t zero:=
              begin
                have h16:= similar_transitive M t x zero h h12,
                exact h16,
              end,
            have h17:= zero_definition,
            rw h17 at *,
            apply h14 Λ,
            exact h15,
          },
          {
            intro h,
            cases h with a h18,
            rw h4 x at h,
            cases h with b h19,
            have h20:= similar_singletons M a b,
            rw h18,
            rw h19,
            exact h20,
          }
        }
      end,
    rw [h3,h6],
  end

theorem finitenotfinite1: FINITE M ∈ FINITE M → 𝕍 ∈ FINITE M:=
  begin
    intro hF,
    have h3:=  singletons_finite M,
    have h4: USC 𝕍 ⊆ FINITE M:=
      begin
        rw subset_definition,
        intros t h,
        rw usc at h,
        cases h with a h5,
        cases h5 with ha h6,
        rw h6,
        exact h3 a,
      end,
    have h7: ∀ (x:M), x ∈ FINITE M → Nc M x ∈ 𝔽 :=
      begin
        intros x h,
        have h8:= finitecardinals3 M x h,
        exact h8,
      end,
    have h9:= FregeNdecidable M,
    rw decidable_members at h9,
    have h10: ∀ (x:M), x ∈ FINITE M → Nc M x = one ∨ ¬ Nc M x = one:=
      begin
        intros x h,
        have h11:=  h7 x h,
        have h12:= h9 (Nc M x) one ⟨ h11, oneF M⟩,
        exact h12,
      end,
    have h13:= Ncone M,
    simp_rw← h13 at h10,
    have h14: USC 𝕍 ∈ SSC (FINITE M):=
      begin
        rw ssc_members,
        exact ⟨ h4, h10⟩,
      end,
    have h15:= separablefinite M (FINITE M) hF (USC 𝕍) h4,
    have h16:= ssc_members M (FINITE M) (USC 𝕍),
    rw h16 at h14,
    cases h14 with h17 h18,
    have h19:= uscfinite M 𝕍,
    unfold separable_subset at h15,
    have h20: USC 𝕍 ∈ FINITE M:=
      begin
        apply h15,
        split,
        {
          exact h17,
        },
        {
          rw full_extensionality,
          intros t,
          specialize h18 t,
          rw binary_union_axiom,
          rw minus_members,
          split,
          {
            intro h,
            have h19:= h18 h,
            cases h19 with h20 h21,
            {
              left,
              exact h20,
            },
            {
              right,
              exact ⟨ h, h21⟩, 
            }
          },
          {
            intro h,
            cases h with h22 h23,
            {
              rw usc at h22,
              cases h22 with a h23,
              cases h23 with h24 h25,
              have h26:= singletons_finite M a, 
              rw h25,
              exact h26,
            },
            {
              exact h23.left,
            }
          }
        }
      end,
    have h21:= uscfinite M 𝕍,
    rw h21 at h20,
    exact h20,
  end

lemma nomaxinteger: ¬ 𝔽 ∈ FINITE M → ∀ (m:M), m ∈ 𝔽  →  ¬ ( 𝕊 m = Λ):=
  assume hnotfinite m,
  begin
    intros hm hsm,
    have h3:= maxintegerimpliesFfinite M m hm hsm,
    exact hnotfinite h3,
  end

theorem successorH2: ¬ 𝔽  ∈ FINITE M → ∀(x:M), x ∈ ℍ →   𝕊 x ∈ ℍ := 
  assume hnotfinite x,
  begin
   intros h1,
   have h3:= doublecomplementF M x h1,
   have h4:= nomaxinteger M hnotfinite x,
   have h5:= double_negate (x ∈ 𝔽 → ¬ 𝕊 x = Λ),
   have h6:= h5 h4,
   have h7:= push_double_negationNF (x ∈ 𝔽) (¬ 𝕊 x = Λ) h6 h3,
   rw triplenegation at h7,
   exact successorH M x h1 h7,
  end

lemma additiononH: ¬ 𝔽  ∈ FINITE M → ∀ (y:M), y ∈ ℍ → ∀(x:M), x ∈ ℍ → x+y ∈ ℍ:=
  assume hnotfinite,
  have base: zero ∈ Z_additionclosureH M:=
     begin
       rw Z_additionclosureH_members,
       split,
       {
        exact zeroH M,
       },
       {
         intros x xH,
         rw right_identityNF,
         exact xH,
       }
     end,
  have step:∀ (m:M), m ∈ Z_additionclosureH M → ¬ 𝕊 m = Λ → 𝕊 m ∈ Z_additionclosureH M:=
    assume m,
    begin
      intros h3 hsm,
      rw Z_additionclosureH_members,
      rw Z_additionclosureH_members at h3,
      rcases h3 with ⟨h4, h5⟩,
      split,
      {
        exact successorH M  m h4 hsm,
      },
      {
        intros x hx,
        have hsx:= successorH2 M hnotfinite  x hx,
        rw successor_shift,
        have h8:= h5 (𝕊 x) hsx,
        exact h8,
      }
    end,
  begin
    intros y hy,
    rw H_members at hy,
    specialize hy (Z_additionclosureH M),
    have h12:= hy ⟨ base,step⟩,
    rw Z_additionclosureH_members at h12,
    rcases h12 with ⟨ h13, h14⟩,
    exact h14, 
  end

theorem successoroneoneonH2: ¬ 𝔽 ∈ FINITE M →  ∀(x y:M), x ∈ ℍ → y ∈ ℍ → 𝕊 x = 𝕊 y → x = y:=
  assume hnotfinite x y hx hy hsxy,
  begin
    have hsx:= successorH2 M hnotfinite x hx,
    have hsy:= successorH2 M hnotfinite y hy,
    have h12:= successoroneoneonH M x y hx hy hsx hsxy,
    exact h12,
  end 


lemma lessthansuccessorH: ¬ 𝔽 ∈ FINITE M → 
 ∀ (x m:M),  x ∈ ℍ → m ∈ ℍ →  𝕊 m ∈ ℍ → (x ≤ℍ 𝕊 m ↔ (x ≤ℍ m ∨ x = 𝕊 m)) := 
   assume hnotfinite x m,
   begin
     intros hx hm hsm,
     split,
     {
       intros h3,
       rw leH_definition at h3,
       rcases h3 with ⟨h4,h5,h6⟩,
       cases h6 with k h7,
       rcases h7 with ⟨ hk, h8⟩,
       have h9: k = zero ∨ ¬k = zero:=
          begin
            exact Hdecidable M k hk zero (zeroH M),
          end,
       cases h9 with h10 h11,
       {
         rw h10 at h8,
         rw right_identityNF at h8,
         right,
         exact h8,
       },
       {
         have h12:= nonzeroissuccessorH M k hk h11,
         cases h12 with r h13,
         rcases h13 with ⟨ hr, h14⟩ ,
         left,
         rw leH_definition,
         split,
         {
          exact hx,
         },
         {
           split,
           {
            exact hm,
           },
           {
            use r,
            split,
            {
              exact hr,
            },
            {
              rw h14 at h8,
              have h15:= addition_equation M x r,
              rw h8 at h15,
              have h16:= additiononH M hnotfinite r hr x h4,
              --symmetry at h15,
              --This works but leaves an error message! 
              have h20: 𝕊 (x+r) = 𝕊 m:=
                begin
                  symmetry,
                  exact h15,
                end,
              have h17:= successoroneoneonH2 M hnotfinite m (x+r) hm h16  h15,
              symmetry,
              exact h17,
            }
           }
         }
       }
     },
     {
       intros h,
       cases h with  h3 h4,
       {
         rw leH_definition at h3,
         rcases h3 with ⟨ hx, hm, h5⟩,
         rcases h5 with ⟨k, h6⟩,
         rcases h6 with ⟨ h7, h8⟩,
         rw leH_definition,
         split,
         {
          exact hx,
         },
         {
           split,
           {
            exact hsm,
           },
           {
            use 𝕊 k,
            split,
            {
              exact successorH2 M hnotfinite k h7,
            },
            {
              rw addition_equation,
              rw h8,
            }
           }
         }
       },
       {
         rw h4,
         rw leH_definition,
         split,
         {
          exact hsm,
         },
         {
          split,
          {
            exact hsm,
          },
          {
            use zero,
            rw right_identityNF,
            split,
            {
              exact zeroH M,
            },
            {
              reflexivity,
            }
          }
         }
       }
     }
   end
   
lemma leHzero: ∀(x k:M), x ∈ ℍ → k ∈ ℍ → x + k = zero → x = zero ∧ k = zero:=
  assume x k,
  begin
    intros hx hk hxk,
    have h3:= Hdecidable M k hk zero  (zeroH M),
    cases h3 with h4 h5,
    {
      rw h4 at hxk,
      rw right_identityNF M at hxk,
      exact ⟨ hxk, h4⟩,
    },
    {
      have h6:= nonzeroissuccessorH M k hk h5,
      rcases h6 with ⟨ r, h7⟩ ,
      rcases h7 with ⟨h9, h10⟩,
      rw h10 at *,
      rw addition_equation at hxk,
      have h12:= Fregesuccessoromits0 M (x+r),
      contradiction,
    }
  end   

lemma doublenegateleH: ¬ 𝔽 ∈ FINITE M →  ∀(x y:M), x ≤ℍ y → ¬¬ x ≤ y:=
  assume hnotfinite x y,
  begin
    intros h3,
    rw leH_definition at h3,
    rcases h3 with ⟨ hx, hy, h4⟩,
    have hxF:= doublecomplementF M x hx,
    have hyF:= doublecomplementF M y hy,
    rcases h4 with ⟨k, h5⟩,
    rcases h5 with ⟨ hk, h6⟩,
    have hkF:= doublecomplementF M k hk,
    have h62: ∃ (k:M), x+k = y ∧ k ∈ ℍ:=
      begin
        use k,
        exact ⟨ h6, hk⟩,
      end,
    have h7:= double_negate (∃ (k:M), x+k = y ∧ k ∈ ℍ) h62,
    have h8:  ∀ (k:M), k ∈ ℍ → (x+k = y ↔ ¬ ¬ x+k = y):=
      begin
        intros m hm,
        have h9: x+m = y ∨ ¬ x+m = y:=
          begin
            have h10:= additiononH M hnotfinite m hm x hx,
            have h11:= Hdecidable M (x+m) h10 y hy,
            exact h11,
          end,
        cases h9 with h12 h13,
        {
          split,
          {
            intros h13,
            have h14:= double_negate (x+m = y) h12,
            exact h14,
          },
          {
            intros h13,
            exact h12,
          }
        },
        {
          split,
          {
            intros h15,
            have h16:= double_negate (x+m=y) h15,
            exact h16,
          },
          {
            intros h17,
            contradiction,
          }
        }  
      end,  
    have h9: ¬¬∃ (k : M), ¬¬( x + k = y) ∧ k ∈ ℍ:=
      begin
        intros h20,
        apply h7,
        intros h21,
        apply h20,
        cases h21 with m h22,
        use m,
        rcases h22 with ⟨ h23, hm⟩,
        have h24:= h8 m  hm,
        rw h24 at h23,
        exact ⟨ h23, hm⟩, 
      end,
    have h10:¬¬∃ (k : M), ¬¬x + k = y ∧ ¬¬ k ∈ 𝔽:=
      begin
        intros h11,
        apply h9,
        intros h12,
        apply h11,
        cases h12 with m h13,
        use m,
        split,
        {
          exact h13.left,
        },
        {
          cases h13 with h14 h15,
          have h16:= doublecomplementF M m h15,
          exact h16,
        }
      end,
    have h11:¬¬∃ (k : M), ¬¬(x + k = y ∧ k ∈ 𝔽):=
      begin
        intros h12,
        apply h10,
        intros h13,
        apply h12,
        cases h13 with m h14,
        use m,
        have h15:= notnot_and (x+m = y) (m ∈ 𝔽 ),
        rw<- h15 at h14,
        exact h14,
      end,
    have h20: ¬¬∃ (k : M),(x + k = y ∧ k ∈ 𝔽):=
      begin
        have h21:= existsnotnot (λ (k:M), (x + k = y ∧ k ∈ 𝔽)),
        dsimp at h21,
        have h22:= h21 h11,
        exact h22,
      end,
    have h21: ¬¬ x ≤ y ↔ ¬¬ ∃(k:M),(x+k=y ∧ k ∈ 𝔽 ):=
      begin
        split,
        {
          intros h,
          exact h20,
        },
        { 
          
          have h31:= orderbyaddition M y,
          have h32:= double_negate (y ∈ 𝔽 → ∀ (p : M), p ∈ 𝔽 → (p ≤ y ↔ ∃ (k : M), k ∈ 𝔽 ∧ p + k = y)) h31,
          have h33:= push_double_negationNF (y ∈ 𝔽 )(∀ (p : M), p ∈ 𝔽 → (p ≤ y ↔ ∃ (k : M), k ∈ 𝔽 ∧ p + k = y)) h32 hyF,
          have h34:= notnot_forall (λ (p:M),p ∈ 𝔽 → (p ≤ y ↔ ∃ (k : M), k ∈ 𝔽 ∧ p + k = y) ) h33,
          dsimp at h34,
          specialize h34 x,
          have h35:= push_double_negationNF (x ∈𝔽 )(x ≤ y ↔ ∃ (k : M), k ∈ 𝔽 ∧ x + k = y) h34 hxF,
          have h36:= notnot_iff ( x ≤y) ( ∃ (k : M), k ∈ 𝔽 ∧ x + k = y) h35,
          intros h,
          rcases h36 with ⟨h37, h38⟩,
          apply h38,
         intros h40,
          apply h,
          intros h41,
          cases h41 with m h42,
          rw not_exists at h40,
          specialize h40 m,
          apply h40,
          exact ⟨ h42.right, h42.left⟩,
        }
      end,
    rcases h21 with ⟨h22, h23⟩,
    apply h23,
    exact h20, 
  end

lemma JHbarzero:∀(x:M),  x ∈ JbarH M zero ↔ x = zero:=
  assume x,
  begin
    rw JbarH_members,
    split,
    {
      assume h4,
      rcases h4 with ⟨ hx, h5⟩, 
      rw leH_definition at h5,
      rcases h5 with ⟨h6, h7, h8⟩, 
      cases h8 with k h9,
      rcases h9 with ⟨ hk, h11⟩,
      have h12:= leHzero M x k hx hk h11,
      exact h12.left, 
    },
    {
      intros h,
      split,
      {
        rw h,
        exact zeroH M,
      },
      {
        rw leH_definition,
        rw h,
        split,
        {
          exact zeroH M,
        },
        {
          split,
          {
            exact zeroH M,
          },
          {
            use zero,
            rw right_identityNF,
            split,
            {
              exact zeroH M,
            },
            {
              reflexivity,
            }
          }
        }
      }
    }
  end  

lemma JH_successor: ¬ 𝔽 ∈  FINITE M → ∀(m:M), m ∈ ℍ   → 
 JbarH M (𝕊 m)   = ((JbarH M m) ∪ single (𝕊 m)):=
  assume hnotfinite m hm,
  begin
    have h: 𝕊 m ∈ ℍ:=
      begin
        have h20:= successorH2 M hnotfinite m hm,
        exact h20,
      end, 
    have h3:= extensionality_axiom
         (JbarH M (𝕊 m))
         ((JbarH M m) ∪ single (𝕊 m)),
    apply h3,
    intros t,
    rw JbarH_members,
    rw binary_union_axiom,
    rw JbarH_members,
    rw leH_definition,
    rw leH_definition,
    rw singleton1,
    split,
    {
      intros h,
      rcases h with ⟨ ht, ht2, h4,h5⟩,
      cases h5 with k h6,
      rcases h6 with ⟨ hk, h8⟩,
      have h9: t = zero ∨ ¬ t = zero:=
        begin
          have h10:= Hdecidable M t ht zero (zeroH M),
          cases h10 with h11 h12,
          {
            left,
            exact h11,
          },
          {
            right,
            exact h12,
          },
        end, 
      cases h9 with h13 h14,
      {
        left,
        rw h13,
        split,
        {
          exact zeroH M,
        },
        { split,
         {
           exact zeroH M,
         },
         {
           split,
           {
            exact hm,
           },
           {
             use m,
             split,
             {
              exact hm,
             },
             {
              rw left_identityNF,
             }
           }
         }
        }
      },
      { 
        have h20:= Hdecidable M k hk zero (zeroH M),
        cases h20 with h20 h21,
        {
          right,
          rw h20 at h8,
          rw right_identityNF at h8,
          exact h8,
        },
        {
          left,
          split,
          {
            exact ht,
          },
          {
            split,
            {
              exact ht,
            },
            {
              split,
              {
                exact hm,
              },
              {
                have h30:=nonzeroissuccessorH M k hk h21,
                cases h30 with p h31,
                cases h31 with h32 h33,
                use p,
                split,
                {
                  exact h32,
                },
                {
                  rw h33 at h8,
                  rw addition_equation at h8,
                  have h34:= additiononH M hnotfinite p h32 t ht,
                  have h35:= successoroneoneonH M (t+p)  m h34 hm,
                  rw h8 at h35,
                  have h36:= h35 h4,
                  apply h36,
                  reflexivity,
                }
              }
            }
          }
        }
      }
    },
    {
      intros h40,
      cases h40 with h41 h42,
      {
        rcases h41 with ⟨ h43,ht,h45,h46⟩,
        cases h46 with k h47,
        cases h47 with h48 h49,
        split,
        {
          exact ht,
        },
        {
          split,
          {
            exact ht,
          },
          {
            split,
            {
              exact h,
            },
            {
              use 𝕊 k,
              split,
              {
                exact successorH2 M hnotfinite k h48,
              },
              {
                rw addition_equation,
                rw h49,
              }
            }
          }
        }
      },
      {
        have h43:= successorH2 M hnotfinite m hm,
        rw h42,
        split,
        {
          exact h43,
        },
        {
          split,
          {
            exact h43,
          },
          {
            split,
            {
              exact h43,
            },
            {
              use zero,
              split,
              {
                exact zeroH M,
              },
              {
                rw right_identityNF M,
              }
            }
          }
        }
      }
    }
  end

lemma JHfinite_helper: ¬ 𝔽 ∈ FINITE M → ∀(m:M), m ∈ ℍ → ¬ 𝕊 m ∈ JbarH M m:=
  assume hnotfinite m,
  begin
    intros hm h,
    rw JbarH_members at h,
    cases h with h2 h3,
    have h4: ¬¬ 𝕊 m ≤ m:=
      begin
        have h5:= doublenegateleH M hnotfinite (𝕊 m ) m h3,
        exact h5,
      end, 
    have h6:= doublecomplementF M m hm,
    have h7:= doublecomplementF M (𝕊 m) h2,
    have h8:= le_transitive2 M m (𝕊 m) m,
    have h9:= double_negate (m ∈ 𝔽 → 𝕊 m ∈ 𝔽 → m ∈ 𝔽 → m < 𝕊 m → 𝕊 m ≤ m → m < m) h8,
    have h10:= push_double_negationNF (m ∈ 𝔽)
      (𝕊 m ∈ 𝔽 → m ∈ 𝔽 → m < 𝕊 m → 𝕊 m ≤ m → m < m) h9 h6,
    have h11:= push_double_negationNF (𝕊 m ∈ 𝔽)
      ( m ∈ 𝔽 → m < 𝕊 m → 𝕊 m ≤ m → m < m) h10 h7,
    have h12:= push_double_negationNF (m ∈ 𝔽)
      ( m < 𝕊 m → 𝕊 m ≤ m → m < m) h11 h6,
    have h14: ∀(m:M),m ∈ 𝔽 → 𝕊 m ∈ 𝔽 → m < 𝕊 m:=
       assume m hm hsm,
       begin
         have h15:=cardinalsinhabited M (𝕊 m) hsm,
         have h13:= lessthansuccessor M m hm h15,
         exact h13,
       end, 
    have h15:= h14 m,
    have h16:= double_negate (m ∈ 𝔽 → 𝕊 m ∈ 𝔽 → m < 𝕊 m) h15,
    have h17:= push_double_negationNF (m ∈ 𝔽) 
      ( 𝕊 m ∈ 𝔽 → m < 𝕊 m) h16 h6,
    have h18:= push_double_negationNF (𝕊 m ∈ 𝔽) ( m < 𝕊 m) h17 h7,
    have h19:= le_transitive2 M m (𝕊 m) m,
    have h20:= double_negate (m ∈ 𝔽 →
      𝕊 m ∈ 𝔽 → m ∈ 𝔽 → m < 𝕊 m → 𝕊 m ≤ m → m < m) h19,
    have h21:= push_double_negationNF (m ∈ 𝔽) 
      ( 𝕊 m ∈ 𝔽 → m ∈ 𝔽 → m < 𝕊 m → 𝕊 m ≤ m → m < m) h9 h6,
    have h22:= push_double_negationNF (𝕊 m ∈ 𝔽 ) 
    (m ∈ 𝔽 → m < 𝕊 m → 𝕊 m ≤ m → m < m) h21 h7,
    have h23:= push_double_negationNF (m ∈ 𝔽) 
    (m < 𝕊 m → 𝕊 m ≤ m → m < m) h22 h6,
    have h24:= push_double_negationNF (m < 𝕊 m )
    (𝕊 m ≤ m → m < m) h23 h18,
    have h25:= push_double_negationNF (𝕊 m  ≤ m )
    (m < m) h24 h4,
    have h26:= xnotlessthanx M m,
    have h27:= double_negate (m ∈ 𝔽 → ¬ m < m ) h26,
    have h28:= push_double_negationNF (m ∈ 𝔽 )(¬ m < m) h27 h6,
    contradiction,
  end

lemma JHfinite: ¬ 𝔽 ∈ FINITE M →  ∀(m:M), m ∈ ℍ → JbarH M m ∈ FINITE M:=
  assume hnotfinite,
  begin
    have base: zero ∈ Z_JbarHfinite M:=
      begin
        have h4:= Z_JbarHfinite_members M zero,
        have h5:= h4.2,
        apply h5,
        split,
        {
          exact zeroH M,
        },
        {
          have h6:= JHbarzero M,
          have h7: JbarH M zero = single zero:=
            begin
              have h8:= extensionality_axiom (JbarH M zero) (single zero),
              apply h8,
              intros x,
              rw (h6 x),
              rw singleton1,
            end,
          rw h7,
          have h10:= singleton_finite M zero,
          exact h10,
        }
      end,
    have step: ∀(m:M), m ∈ Z_JbarHfinite M → ¬ 𝕊 m = Λ → 𝕊 m ∈ Z_JbarHfinite M :=
      assume m,
      begin
        intros h hsm,
        rw Z_JbarHfinite_members,
        rw Z_JbarHfinite_members at h,
        rcases h with ⟨ hm, h4⟩,
        have h5:= JH_successor M hnotfinite m hm,
        rw h5,
        split,
        {
          exact successorH2 M hnotfinite m hm,
        },
        {
          have h30:= JHfinite_helper M hnotfinite m hm,
          have h31:= finite_adjoin M (JbarH M m) (𝕊 m),
          apply h31,
          exact ⟨h4, h30⟩, 
        }
      end, 
    intros m hm,
    rw H_members at hm,
    specialize hm (Z_JbarHfinite M),
    have h12:= hm  ⟨ base,step⟩,
    rw Z_JbarHfinite_members at h12,
    rcases h12 with ⟨ h13, h14⟩,
    exact h14, 
  end 

theorem FequalsH: ¬ 𝔽∈ FINITE M →   ∀(m:M), m ∈ 𝔽 →  ∃(k:M), k ∈ ℍ ∧ JbarH M k ∈ 𝕊 m:=
  assume hnotfinite,
  begin
    have base: zero ∈ Z_FequalsH M:=
      begin
        rw Z_FequalsH_members M,
        split,
        {
          exact zeroF M,
        },
        {
          split,
          {
            have h3:= one_definition,
            rw<- h3,
            exact oneF M,
          },
          {
            use zero,
            split,
            {
              exact zeroH M,
          },
            {
              have h4:= JHbarzero M,
              rw<- one_definition,
              rw one_members M,
              use zero,
              have h5:= extensionality_axiom (JbarH M zero) (single zero),
              apply h5,
              simp_rw singleton1,
              exact h4,
            }
          }
        }
      end, 
    have step: ∀(m:M), m ∈ Z_FequalsH M → (∃(u:M), u ∈ 𝕊 m) → 𝕊 m ∈ Z_FequalsH M:=
      assume m h2 h3,
      begin 
        rw Z_FequalsH_members at h2,
        rcases h2 with ⟨hm,hsm,h5⟩,
        cases h5 with k h6,
        rcases h6 with ⟨ hk, h7⟩,
        rw Z_FequalsH_members,
        split,
        {
          exact hsm,
        },
        {
          have h33: JbarH M (𝕊 k) ∈ 𝕊 (𝕊 m):=
            begin
              rw successor_members M,
              use JbarH M k,
              use (𝕊 k),
              split,
              {
                exact h7,
              },
              {  
                split,
                {
                  have h8:= JHfinite_helper M hnotfinite k hk,
                  exact h8,
                },
                {
                  have h12:= JH_successor M hnotfinite k hk,
                  exact h12,
                }
              }
            end,  
          have h40: ∃ (k : M), k ∈ ℍ ∧ JbarH M k ∈ 𝕊 (𝕊 m):=
            begin
              use (𝕊 k),
              have h41:= successorH2 M hnotfinite k hk,
              exact ⟨h41, h33⟩, 
            end,
          cases h40 with k h41,
          split,
          {
            have h50:= successorF M (𝕊 m) hsm,
            apply h50,
            use JbarH M k,
            exact h41.right,
          },
          {
            use  k,
            exact h41,
          }
        }
      end,
    intros m h70,
    rw F_members at h70,
    specialize h70 (Z_FequalsH M),
    have h71:= h70 ⟨base, step⟩,
    rw Z_FequalsH_members at h71,
    rcases h71 with ⟨ h72, h73, h74⟩,
    exact h74, 
  end 

lemma FequalsH2: ¬ 𝔽 ∈ FINITE M →   (𝔽:M) = (ℍ:M) :=
  assume hnotfinite,
  begin
    have h2:= extensionality_axiom (𝔽:M) (ℍ:M),
    apply h2,
    intro x,
    split,
    {
      have h3:= FsubsetH M,
      exact member_subset M 𝔽 ℍ x h3,  
    },
    {
      intros hx,
      rw H_members at hx,
      specialize hx 𝔽,
      apply hx,
      split,
      {
        exact zeroF M,
      },
      {
        intros m hm hsm,
        have h22:= successorF M m hm,
        apply h22,
        have h23:= FequalsH M hnotfinite m hm,
        cases h23 with k h24,
        cases h24 with h25 h26,
        use JbarH M k,
        exact h26,
      }
    }
  end

lemma onemore: ∀(m:M), m ∈ 𝔽 → 𝕊 m ∈ 𝔽 → ∀(u:M),  u ∈ m → ¬¬ ∃ (c:M), u ∪ (single c) ∈ 𝕊 m ∧ ¬ c ∈ u :=
  assume m hm hsm u hu,
  begin
    have h4:= cardinalsinhabited M (𝕊 m) hsm,
    cases h4 with w h5,
    have h6:= successor_members M m w,
    have h7:= h6.1 h5,
    cases h7 with v h8,
    cases h8 with a h9,
    rcases h9 with ⟨hv,h11,h12⟩,
    have h13:= finitecardinals2 M u v m hm hu hv,
    rw h12 at h5,
    have h100:= finitecardinals1 M (𝕊 m) (v ∪ single a) hsm h5,
      
    have h14: ¬ (v ∪ (single a) ⊆ u):=
      begin
        intros h15,
         have h16: infinite M u:=
          begin
            rw infinite,
            use v,
            split,
            {
              exact  union_subset M v (single a) u h15,
            },
            {
              split,
              {
                intro h17,
                rw h17 at h15,
                have h18:= member_subset M (v ∪ (single a)) v a h15,
                have h19: a ∈ v ∪ (single a):=
                  begin
                    rw binary_union_axiom v (single a) a,
                    right,
                    rw singleton1,
                  end, 
                have h20:= h18 h19,
                contradiction,
              },
              {
                exact h13,
              }
            }
          end,
        have h30:= infiniteimpliesnotfinite M u h16,
        have h31:= finitecardinals1 M m u hm hu,
        contradiction,
      end, 
    have h20: (¬¬ ∀(t:M),(t ∈ v ∪ single a → t ∈ u)) ↔ 
             ∀(t:M), (t ∈ v ∪ single a → ¬¬ t ∈u):= 
      begin
        split,
        {
          intros h21,
          have h22:= notnot_forall (λ (t:M),t ∈ v ∪ single a → t ∈ u) h21,
          dsimp at h22,
          intros t h23,
          specialize h22 t,
          have h24:= double_negate (t ∈ v ∪ single a) h23,
          have h25:= push_double_negationNF(t ∈ v ∪ single a) (t ∈ u) h22 h24,
          exact h25,
        },
        {
          intros h30,
          have h31:= finiteDNS M u ( v ∪ single a) h100 h30,
          exact h31,
        }
      end,
    rw subset_definition at h14,
    have h101:= double_negate (¬∀ (z : M), (z ∈ v ∪ single a → z ∈ u)) h14,
    rw h20 at h101,
    have h102: ¬¬ ∃ (t:M), ¬ t ∈ u:=
      begin
        intros h103,
        apply h101,
        intros t h104 h105,
        apply h103,
        use t,
      end,
    have h103: (∃ (c:M), ¬ c ∈ u ) → (∃ (c:M), (u ∪ (single c)) ∈ 𝕊 m ∧ ¬ c ∈u ):=
      begin
        intros h104,
        cases h104 with c h105,
        use c,
        rw successor_members M,
        use u,
        use c,
        split,
        {
          exact hu,
        },
        {
          split,
          {
            exact h105,
          },
          {
            reflexivity,
          }
        },
      end,
    have h110:= notnot_imp (∃ (c : M), ¬c ∈ u) (∃ (c : M), u ∪ single c ∈ 𝕊 m ∧ ¬ c ∈ u  ) h103 h102,
    exact h110,
  end    

lemma maximalelement: ∀(m:M), m ∈ 𝔽 → (𝕊 m = Λ ↔ ∀ (k:M), k ∈ 𝔽 → k ≤ m):=
 -- one half is already in maxinteger in inf15.lean
 -- but I didn't notice that when proving this.
  assume m hm,
  begin
    split,
    {
      intros h3,
      have base: zero ∈ Z_maximal M m:=
        begin
          rw Z_maximal_members M m,
          have h4:= zero_le_x M m hm,
          exact ⟨zeroF M, h4⟩,
        end,
      have step: ∀ (k:M), k ∈ Z_maximal M m → (∃ (u:M), u ∈ 𝕊 k) → 𝕊 k ∈ Z_maximal M m:=
        begin
          intros k h5 hsk,
          rw Z_maximal_members M m at h5,
          rw Z_maximal_members M m,
          cases h5 with hk h7,
          split,
          {
            exact successorF M k hk hsk,
          },
          {
            have h8: ¬ 𝕊 k = Λ:=
              begin
                intros h9,
                cases hsk with t h10,
                rw h9 at h10,
                have h11:= emptyset_axiom t,
                contradiction,
              end,
            have h20: ¬k = m:=
              begin
                intros h21,
                rw h21 at h8,
                contradiction,
              end,
            have h22: k < m:=
              begin
                have h23:= letolessthan M k m hk hm,
                rw h23 at h7,
                cases h7 with h24 h25,
                {
                  exact h24,
                },
                {
                  rw h25,
                  contradiction,
                },
              end,
            have h23:= noinsertions M k m hk hm h22,
            exact h23,
          }
        end, 
      intros k h70,
      rw F_members at h70,
      specialize h70 (Z_maximal M m),
      have h71 := h70 ⟨ base, step ⟩,
      rw Z_maximal_members M m at h71,
      exact h71.right,
    },
    {
      intros h100,
      have h101: ¬ 𝕊 m ∈ 𝔽:= 
        begin
          intros h102,
          have h103:= h100 (𝕊 m) h102,
          have h104:= xlessthansuccessorx M m hm h102,
          have h105:= le_transitive2 M m (𝕊 m) m hm h102 hm h104 h103,
          have h106:= xnotlessthanx M m hm,
          contradiction,
        end,
      have h102:= extensionality_axiom (𝕊 m) Λ,
      apply h102,
      intros x,
      have h103:= emptyset_axiom x,
      split,
      {
        intros h104,
        have h105:= successorF M m hm ⟨ x, h104⟩,
        contradiction,
      },
      {
        intros h104,
        contradiction,
      }
    }
  end
lemma Jcardinality: ∀ (m:M), m ∈ 𝔽  → 𝕁 M m ∈ 𝕋 M (𝕋 M m):=
  begin
    have base: zero ∈ Z_Jcardinality M:=
      begin
        rw Z_Jcardinality_members,
        split,
        {
          exact zeroF M,
        },
        {
          rw Tzero,
          rw Tzero,
          rw Jzero,
          rw zero_members,
        }
      end,
    have step: ∀ (m:M), m ∈ Z_Jcardinality M → (∃(u:M), u ∈ 𝕊 m ) → 𝕊 m ∈ Z_Jcardinality M:=
      begin
        intros m h3 h4,
        rw Z_Jcardinality_members at h3,
        cases h3 with hm h5,
        rw Z_Jcardinality_members,
        split,
        {
          have h6:= successorF M m hm h4,
          exact h6,
        },
        {
          rw Tsuccessor M m hm  h4,
          have h20:= Tfinite M m hm,
          have h21:= successorF M (𝕋 M m) h20,
          have h7:= Tsuccessor M (𝕋 M m) h20, 
          have hsm:= (successorF M m hm h4),
          rw Jsuccessor M m hm hsm,
          have h8:= successor_members M (𝕋 M (𝕋 M m)) (𝕁 M m ∪ (single m)),
          have h10:= xnotlessthanx M m hm,
          have h11: ¬ m ∈ 𝕁 M m:=
            begin
              intro h,
              rw J_members at h,
              cases h with h12 h13,
              contradiction,
            end,
          have h12: (𝕁 M m ) ∪ single m ∈ 𝕊 (𝕋 M (𝕋 M m)):=
            begin
              rw successor_members,
              use (𝕁 M m),
              use m,
              split,
              {
                exact h5,
              },
              {
                split,
                {
                  exact h11,
                },
                {
                  refl,
                }
              }
            end,
          have h30:= Tfinite M (𝕊 m) hsm,
          have h14:= Tsuccessor M m hm h4,
          rw h14 at h30,
          have h21:= cardinalsinhabited M (𝕊 (𝕋 M m)) h30,
          have h13: 𝕋 M (𝕋 M (𝕊 m)) = 𝕊 (𝕋 M (𝕋 M m)):=
            begin 
              rw h14,
              exact h7 h21,
            end,
          rw← h14,
          rw h13,
          rw successor_members,
          use 𝕁 M m,
          use m,
          simp,
          exact ⟨ h5, h11⟩, 
        }
      end,
    intros m hm,
    rw F_members at hm,
    have h12:= hm (Z_Jcardinality M) ⟨ base, step⟩,
    rw Z_Jcardinality_members at h12,
    exact h12.right,
  end

lemma Tm: ∀(m:M), m ∈ 𝔽 →   (∀(k:M), k ∈ 𝔽 → k ≤ m) → 𝕋 M m < m  :=
  begin
    intros m hm h3,
    have h4:= Jcardinality M m hm,
    have h5:= mnotinJm M m hm,
    have h6: 𝕁 M m ∪ (single m) ∈ 𝕊 (𝕋 M (𝕋 M m)):=
      begin
        rw successor_members M,
        use 𝕁 M m,
        use m,
        split,
        {
          exact h4,
        },
        {
          split,
          {
            exact h5,
          },
          {
            reflexivity,
          }
        }
      end,
    have h100:= Tfinite M m hm,
    have h101:= Tfinite M (𝕋 M m) h100,
    have h7:=successorF M (𝕋 M (𝕋 M m)) h101 ⟨ 𝕁 M m ∪ single m,h6⟩,
    have h8:= maximalelement M m hm,
    have h9:= h8.2 h3,
    have h10: ¬ 𝕊 m ∈ 𝔽:=
      begin
        intros h,
        have h11:= cardinalsinhabited M (𝕊 m) h,
        cases h11 with x h12,
        rw h9 at h12,
        have h13:= emptyset_axiom x,
        contradiction,
      end,  
    have h20: ¬(𝕋 M (𝕋 M m)) = m:=
      begin
        intros h,
        rw h at h7,
        contradiction,
      end, 
    have h21: ¬ 𝕋 M m = m:=
      begin
        intros h,
        rw h at h20,
        rw h at h20,
        apply h20,
        reflexivity,
      end,
    have h22:= h3 (𝕋 M m) h100,
    rw lessthan_definition,
    exact ⟨h22, h21⟩, 
  end

lemma greaterTm:  ∀(m:M), m ∈ 𝔽 →   (∀(k:M), k ∈ 𝔽 → k ≤ m) →
  ∀(k:M), k ∈ 𝔽 → (  exp M k = Λ ↔ 𝕋 M m < k):=
  begin
    intros m hm hmax k hk,
    have hTm:= Tfinite M m hm,
    split,
    {
      intros hexpk,
      specialize hmax k hk,
      have h3:= finitetrichotomy M (𝕋 M m) hTm k hk,
      cases h3 with h4  h5,
      {
        exact h4,
      },
      {
        cases h5 with h6 h6,
        {
          rw<- h6 at hexpk,
          have h8:= expTinF M m hm,
          rw hexpk at h8,
          have h9:= cardinalsinhabited M Λ h8,
          cases h9 with x h10,
          have h11:= emptyset_axiom x,
          contradiction,
        },
        {
          have h20:= Tonto M k m hk hm h6,
          cases h20 with r h21,
          rcases h21 with ⟨hr, h23⟩,
          rw h23 at *,
          have h24:= expTinF M r hr,
          rw hexpk at h24,
          have h25:= cardinalsinhabited M Λ h24,
          cases h25 with x h26,
          have h27:= emptyset_axiom x,
          contradiction,  
        },
      },
    },
    {
      intros htm,
      have h30:= extensionality_axiom (exp M k) Λ,
      apply h30,
      intros x,
      split,
      {
        intros h31,
        have h32:= (exp_members M k x).1 h31,
        cases h32 with v h33,
        rcases h33 with ⟨ h34, h35⟩, 
        have h36:= finitecardinals1 M k (USC v) hk h34,
        have h37:= uscfinite M,
        have h38:= (h37 v).1 h36,
        have h39:= finitecardinals3 M v h38,
        have h40:= Tfinite M (Nc M v) h39,
        have h41: k  = 𝕋 M (Nc M v):=
          begin
            have h42:= cardinalsdisjoint M k (𝕋 M (Nc M v)) (USC v) hk h40,
            apply h42,
            rw intersection_axiom,
            split,
            {
              exact h34,
            },
            {
              have h44:= Tmembers M v (Nc M v),
              apply h44,
              rw Nc_members M,
              exact similar_reflexive M v
            }
          end, 
        rw h41 at htm,
        have h42:= Tlessthan M m (Nc M v) hm h39,
        have h43:= h42.2 htm,
        have h44:= hmax (Nc M v) h39,
        have h45:= le_transitive2 M m (Nc M v) m hm h39 hm h43 h44,
        have h46:= xnotlessthanx M m hm,
        contradiction,
      },
      {
        intros h,
        have h50:= emptyset_axiom x,
        contradiction,
      }
    }
  end

lemma unenlargeable2: ∀(m:M), m ∈𝔽 → (∀(k:M), k ∈ 𝔽 → k ≤ m ) → ∀(u:M), u ∈ m → ∀(x:M), ¬¬ x ∈u:=       
  begin
    have h:= unenlargeable M,
    intros m hm h4 u hu x,
    specialize h m u,
    have h5:= maximalelement M m hm,
    rw<- h5 at h4,
    have h6:= h hm h4 hu x,
    exact h6,
  end

def MAXIMAL (m:M):= m ∈ 𝔽 ∧ ∀(k:M), k ∈ 𝔽 → k ≤m
def UNENLARGEABLE (u:M):= ∀(t:M), ¬¬ t ∈ u  
lemma unenlargeable3: ∀(u:M), u ∈ FINITE M →  UNENLARGEABLE M u → ∀ (x:M), x ∈ FINITE M →  ¬¬ x ⊆ u:=
  assume u hu hbig,
  begin
    intros x hx,
    have h4: ∀(t:M),(t ∈ x → ¬¬ t ∈ u ):=
      begin
        intros t ht,
        rw UNENLARGEABLE at hbig,
        exact hbig t,
      end, 
    have h10:= finiteDNS M u x hx h4,
    rw subset_definition,
    exact h10,
  end

lemma unenlargeable4: ∀(u:M), u ∈ FINITE M → UNENLARGEABLE M u → ∀ (k:M), k ∈ 𝔽  → k ≤ Nc M u:=
  assume u hu hbig,
  begin
    have h4:= finitecardinals3 M u hu,
    have h5:= maximalelement M (Nc M u) h4,
    rw<- h5,
    have h6:= extensionality_axiom (𝕊 (Nc M u)) Λ,
    apply h6,
    intros x,
    split,
    {
      intros h,
      have hsm:= successorF M (Nc M u) h4 ⟨ x,h ⟩,
      have h7:= onemore M (Nc M u) h4 hsm u (xinNcx M u),
      have h8: ¬¬ ∃ (c:M), ¬ c ∈u:=
        begin
          intros h,
          apply h7,
          intros h30,
          apply h,
          cases h30 with c h31,
          rcases h31 with ⟨ h32, h33⟩ ,
          use c,
        end, 
      rw UNENLARGEABLE at hbig,
      have h30: false:=
        begin
          apply h8,
          intros h31,
          cases h31 with c h32,
          apply h32,
          have h33:= hbig c,
          contradiction,
        end,
      contradiction,
    },
    {
      intros h,
      have h36:= emptyset_axiom x,
      contradiction,
    }
  end  

lemma leF: ∀ (x y:M), x + (𝕊 x) < y → x ∈ 𝔽 → y ∈ 𝔽 → x + (𝕊 x) ∈ 𝔽 :=
  assume x y,
  begin
    intros h3 hx hy,
    rw lessthan_definition at h3,
    cases h3 with h4 h5,
    rw le_definition at h4,
    cases h4 with a h5,
    cases h5 with b h6,
    rcases h6 with ⟨ h7, h8, h9, h10⟩,
    have h30:= h7,
    rw addition_members at h7,
    cases h7 with u h20,
    cases h20 with v h21,
    rcases h21 with ⟨ h22, h23, h24, h25⟩,
    have h26:= successorF M x hx ⟨ v,h24⟩,
    exact inhabited_sum M  (𝕊 x) h26 x hx ⟨ a, h30⟩, 
  end 

lemma xsqF: ∀(x:M), x ∈ 𝔽 →  𝕊 x ∈ 𝔽  →    (𝕊 x) * (𝕊 x) ∈ 𝔽 → x*x ∈ 𝔽 :=
  begin
    intros x hx hsx h,
    have h3:= assoc_helper M (𝕊 x) x hsx hx hsx h,
    have h4:= multiplication_commutative M (𝕊 x) hsx x hx,
    rw<- h4 at h3,
    have h5:= assoc_helper M x x hx hx hsx h3,
    exact h5,
  end 


#axioms_all  