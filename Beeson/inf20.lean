-- odd and even 

import inf18 
variables (M:Type) [Model M] (a b x y z u v w X R W κ μ ℓ : M)

open Model 

lemma zeroeven: even M (zero:M):=
  begin
    unfold even,
    use zero,
    rw right_identityNF,
    split,
    {
      exact zeroSF M,
    },
    {
      reflexivity,
    }
  end

lemma zeronotodd: ¬ odd M (zero:M):=
  begin
    intros h,
    unfold odd at h,
    cases h with k h3,
    rw←  successorisplusone at h3,
    have h4:= Fregesuccessoromits0 M (k+k),
    rw sym at h3,
    cases h3 with h4 h5,
    contradiction,
  end

lemma oneodd: odd M (one:M):=
  begin
    unfold odd,
    use zero,
    rw left_identityNF,
    rw left_identityNF,
    split,
    {
      exact zeroSF M,
    },
    {
      reflexivity,
    }
  end

lemma halfzero: half M zero zero:=
  begin
    unfold half,
    left,
    rw right_identityNF,
    split,
    {
      exact zeroSF M,
    },
    {
      reflexivity,
    }
  end

lemma div2: ∀(x:M), x ∈ SF M → ∃ (k:M), k ∈ SF M ∧ half M x k:=
  assume x hx,
  begin
    have base: zero ∈ Z_div2 M:=
      begin
        rw Z_div2_members,
        split,
        {
          exact zeroSF M,
        },
        {
          use zero,
          exact ⟨ zeroSF M, halfzero M⟩,
        }
      end,
    have step: ∀ (x:M), x ∈ Z_div2 M→ 𝕊 x ∈ Z_div2 M:=
      begin
        intros x h,
        rw Z_div2_members at h,
        rw Z_div2_members,
        cases h with hx h4,
        cases h4 with k h5,
        cases h5 with hk h6,
        split,
        {
          exact successorSF M x hx,
        },
        {
          unfold half at h6,
          cases h6 with h20 h21,
          {
            use k,
            split,
            {
              exact hk,
            },
            {
              unfold half,
              right,
              rw← successorisplusone,
              cases h20 with hk2 h21,
              rw h21,
              split,
              {
                exact hk,
              },
              {
                reflexivity,
              }
            }
          },
          {
            use k + one,
            unfold half,
            split,
            {
              rw←  successorisplusone,
              exact successorSF M k hk,
            },
            {
              left,
              rw← successorisplusone, 
              rw← successorisplusone at h21,
              rw← addition_equation at h21,
              rw successor_shift at h21,
              cases h21 with hk2 h23,
              rw h23,
              rw← addition_equation,
              split,
              {
                exact successorSF M k hk,
              },
              {
                reflexivity,
              }
            }
          }
        }
      end,
    rw SF_members at hx,
    have h30:= hx (Z_div2 M) base step,
    rw Z_div2_members at h30,
    exact h30.2,
  end  

lemma FSF: ∀(x:M), x ∈ 𝔽 → x ∈ SF M:=
  assume x hx,
  begin
    have h4:= FsubsetSF M,
    have h5:= member_subset M 𝔽 (SF M) x h4 hx,
    exact h5,
  end   

lemma nonzeroissuccessorSF: ∀(x:M), x ∈ SF M → ¬(x =zero) → ∃(y:M), y ∈ SF M ∧  𝕊 y = x:=
 begin
   have base: zero ∈ Z_nonzeroissuccessorSF M :=
     begin
       rw Z_nonzeroissuccessorSF_members,
       split,
       {
         exact zeroSF M,
       },
       {
        intros h,
        contradiction,
       }
     end, 
    have step: ∀(x:M),x ∈ Z_nonzeroissuccessorSF M → 𝕊 x ∈ Z_nonzeroissuccessorSF M:=
      begin
        intros x h,
        rw Z_nonzeroissuccessorSF_members at h,
        rw Z_nonzeroissuccessorSF_members,
        cases h with h1 h2,
        split,
        {
          exact successorSF M x h1,
        },
        {
          intros h4,
          use x,
          split,
          {
            exact h1,
          },
          {
            reflexivity,
          }
        }
      end, 
    intros x h,
    rw SF_members at h,
    have h40:= h (Z_nonzeroissuccessorSF M) base step,
    rw Z_nonzeroissuccessorSF_members at h40,
    exact h40.2,
 end 

lemma evenoddstep: ∀ (x:M), x ∈ 𝔽 → 𝕊 x ∈ 𝔽 → 
(even M x ↔ odd M (𝕊 x)) :=
  assume x hx hsx,
  begin
    split,
      {
        intros h,
        unfold even at h,
        unfold odd,
        cases h with k h3,
        use k,
        cases h3 with hk2 h103,
        rw h103,
        rw← addition_equation,
        rw successorisplusone,
        rw associativityNF,
        split,
        {
          exact hk2,
        },
        {
          reflexivity,
        }
      },
      {
        intros h,
        unfold odd at h,
        unfold even,
        cases h with k h3,
        use k,
        rw←  successorisplusone at h3,
        cases h3 with hk2 h103,
        split,
        {
          exact hk2,
        },
        {
          rw successorisplusone at h103,
          rw successorisplusone at h103,
          have h104:= additionSF M k hk2 k hk2,
          have h105: ∃ (u:M),u ∈ k+k:=
            begin
              have h103copy:= h103,
              rw full_extensionality at h103copy,
              rw successorisplusone at hsx,
              have h104:= cardinalsinhabited M (x+one) hsx,
              cases h104 with t h105,
              have h106:= (h103copy t).1  h105,
              rw addition_members at h106,
              cases h106 with a h107,
              cases h107 with b  h108,
              use a,
              exact h108.2.1,
            end,
          have h110:= inhabitedSF M (k+k) h104 h105,
          have h112:= successorisplusone M x,
          rw h112 at hsx,
          have h111:= subtraction M one (oneF M) x (k+k) hx h110 hsx h103,
          exact h111,
        }
      }  
  end   

lemma evenoddstep2: ∀ (x:M), x ∈ 𝔽 → 𝕊 x ∈ 𝔽 → (odd M x ↔ even M (𝕊 x)):=
  assume x hx hsx,
  begin
    have hsxcopy := hsx,
    split,
    { intros h,
      unfold odd at h,
      unfold even,
      cases h with k h3,
      cases h3 with hk h4,
      use 𝕊 k,
      split,
      {
        exact successorSF M k hk,
      },
      {
        rw h4,
        rw← addition_equation,
        rw successor_shift,
        rw one_definition,
        rw← addition_equation,
        rw successor_shift,
        rw right_identityNF,
        rw← addition_equation,
        rw successor_shift,
      }
    },
    {
      intros h,
      unfold even at h,
      unfold odd,
      cases h with k h3,
      cases h3 with hk h4,
      have h5: ¬ k = zero:=
        begin
          intros h,
          rw h at *,
          rw right_identityNF at h4,
          have h5:= Fregesuccessoromits0 M x,
          contradiction,
        end,
      have h6:= nonzeroissuccessorSF M k hk h5,
      cases h6 with r h7,
      cases h7 with hr hsr,
      use r,
      split,
      {
        exact hr,
      },
      rw← hsr at h4,
      rw addition_equation at h4,
      rw successorisplusone M (𝕊 r + r) at h4,
      rw← successor_shift at h4,
      rw addition_equation at h4,
      rw←successor_shift at h4,
      rw h4 at hsx,
      have h8:= cardinalsinhabited M (r+r+𝕊 one) hsx,
      cases h8 with u h9,
      rw successorisplusone at h9,
      rw←  associativityNF at h9,
      rw addition_members at h9,
      cases h9 with a h10,
      cases h10 with b h11,
      have h12:= h11.2.1,
      have h13:= additionSF M r hr r hr,
      have h20:= additionSF M one (oneSF M) (r+r) h13 ,
      have h14:= inhabitedSF M (r+r+one) h20 ⟨a,h12⟩,
      rw successorisplusone at hsxcopy,
      have h15:= subtraction M one (oneF M) x (r+r+one) hx h14 hsxcopy,
      rw successorisplusone at h4,
      rw successorisplusone at h4,
      rw← associativityNF at h4,
      exact h15 h4,
    }
  end

lemma evenorodd: ∀ (x:M), x ∈ 𝔽 →  ((even M x ∧ ¬ odd M x) ∨ (odd M x ∧ ¬ even M x)) :=
  assume x hx,
  begin
    have base: zero ∈ Z_evenorodd M:=
      begin
        rw Z_evenorodd_members,
        have h3:= zeroeven M,
        split,
        {
          exact zeroF M,
        },
        {
          left,
          split,
          {
            exact h3,
          },
          {
            intros h,
            unfold odd at h,
            cases h with k h4,
            cases h4 with hk h5,
            rw← successorisplusone at h5,
            have h6:= Fregesuccessoromits0 M (k+k),
            rw sym at h5,
            contradiction,
          }
        }
      end,
    have step: ∀(x:M), x ∈ Z_evenorodd M → (∃(u:M), u ∈ 𝕊 x) → 𝕊 x ∈ Z_evenorodd M:=
      begin
        intros t h10 hst, 
        rw Z_evenorodd_members at h10,
        cases h10 with ht h11,
        have h12:= successorF M t ht hst,
        have h20:= evenoddstep M t ht h12,
        have h21:= evenoddstep2 M t ht h12,
        cases h11 with h22 h23,
        {
          rw Z_evenorodd_members,
          split,
          {
            exact h12,
          },
          {
            right,
            rw h20 at h22,
            rw h21 at h22,
            exact h22,
          }
        },
        {
          rw Z_evenorodd_members,
          split,
          {
            exact h12,
          },
          {
            rw h21 at h23,
            rw h20 at h23,
            left,
            exact h23,
          }
        }
      end,
    rw F_members at hx,
    have h100:= hx (Z_evenorodd M) ⟨ base, step⟩,
    rw Z_evenorodd_members at h100,
    cases h100 with hx2 h101,
    exact h101,
  end  

lemma halfunique: ∀(x:M), x ∈ 𝔽 → ∀(p q:M),  half M x p → half M x q  → p = q:=
  begin
    have base: zero ∈ Z_halfunique M:=
      begin
        rw Z_halfunique_members,
        split,
        {
          exact zeroF M,
        },
        { 
          intros p q h3 h4,
          unfold half at h3,
          cases h3 with h5 h6,
          {
            rw sym at h5,
            cases h5 with hp h55,
            have h7:= addstozero M p hp p hp h55,
            cases h7 with h8 h9,
            unfold half at h4,
            cases h4 with h28 h29,
            {
              rw sym at h28,
              cases h28 with hq h128,
              have h29:= addstozero M q hq q hq h128,
              cases h29 with h30 h31,
              rw h8,
              rw h30,
            },
            {
              rw h8 at *,
              rw one_definition at h29,
              rw addition_equation at h29,
              have h40:= successor_omits_zero M (q + q + zero),
              cases h29 with hq h129,
              rw sym at h129,
              contradiction,
            }  
          },
          {
            rw one_definition at h6,
            rw addition_equation at h6,
            have h40:= successor_omits_zero M (p + p + zero),
            rw sym at h6,
            cases h6 with h8  h9,
            contradiction,
          },
        }
      end, 
    have step: ∀ (x:M), x ∈  Z_halfunique M → (∃(u:M), u∈ 𝕊 x) → 𝕊 x ∈ Z_halfunique M:=
      begin
        intros x h3 hsx,
        rw Z_halfunique_members,
        rw Z_halfunique_members at h3,
        cases h3 with hx h4,
        split,
        {
          exact successorF M x hx hsx,
        },
        {
          intros p q  h5 h6,
          unfold half at h5,
          unfold half at h6,
          cases h5 with h20 h21,
          {
            cases h6 with h300 h301,
            { 
              cases h300 with hq h28,
              have h21: ¬ p = zero:=
                begin
                  intros h,
                  rw h at *,
                  rw right_identityNF at h20,
                  have h21:= Fregesuccessoromits0 M x,
                  cases h20 with h25 h26,
                  contradiction,
                end,
              have h31: ¬ q = zero:=
                begin
                  intros h,
                  rw h at *,
                  rw right_identityNF at h28,
                  have h31:= Fregesuccessoromits0 M x,
                  contradiction,
                end,
              cases h20 with hp h210,
              have h32:= nonzeroissuccessorSF M p hp h21,
              have h42:= nonzeroissuccessorSF M q hq h31,
              cases h32 with r h33,
              cases h42 with t h43,
              cases h33 with hr h34,
              cases h43 with ht h44,
              have h35: half M x r:=
                begin
                  unfold half,
                  right,
                  rw← h34 at h210,
                  rw one_definition,
                  rw successor_shift,
                  rw right_identityNF,
                  rw addition_equation at h210,
                  rw successorisplusone at h210,
                  rw successorisplusone at h210, 
                  have h38: x + one ∈ 𝔽 :=
                    begin
                      rw←successorisplusone,
                      exact successorF M x hx hsx, 
                    end, 
                  have h50:= successorSF M r hr,
                  have h80:= additionSF M r hr (𝕊 r) h50,                      
                  have h36: 𝕊 r + r ∈ 𝔽:=
                    begin
                      have h82: ∃ (u:M), u ∈ 𝕊 r +r:=
                        begin
                          rw← successorisplusone at h210,                            
                          simp_rw h210 at hsx,
                            cases hsx with u h83,
                            rw addition_members at h83,
                            cases h83 with a h84,
                            cases h84 with b h85,
                            have h86:= h85.2.1,
                            exact ⟨ a, h86⟩,  
                          end,                           
                          have h83:= inhabitedSF M (𝕊 r + r) h80 h82,
                        exact h83,
                      end,  
                    have h37:= subtraction M one (oneF M) x (𝕊 r + r) hx h36 h38 h210,
                    rw←  addition_equation,
                    rw successor_shift,
                    exact ⟨ hr,h37⟩,
                end,
              have h50:= h4 r t h35,
              have h135: half M x t:=
                begin
                  unfold half,
                  right,
                  rw← h44 at h28,
                  rw one_definition,
                  rw successor_shift,
                  rw right_identityNF,
                  rw addition_equation at h28,
                  rw successorisplusone at h28,
                  rw successorisplusone at h28, 
                  have h38: x + one ∈ 𝔽 :=
                    begin
                      rw←successorisplusone,
                      exact successorF M x hx hsx, 
                    end, 
                  have h50:= successorSF M t ht,
                  have h180:= additionSF M t ht (𝕊 t) h50,
                  have h136: 𝕊 t + t ∈ 𝔽:=
                    begin
                      have h82: ∃ (u:M), u ∈ 𝕊 t +t:=
                        begin                            
                          rw← successorisplusone at h28,
                          simp_rw h28 at hsx,
                          cases hsx with u h83,
                          rw addition_members at h83,
                          cases h83 with a h84,
                          cases h84 with b h85,
                          have h86:= h85.2.1,
                          exact ⟨ a, h86⟩,  
                        end, 
                      have h83:= inhabitedSF M (𝕊 t + t) h180 h82,
                      exact h83,
                    end,  
                  have h37:= subtraction M one (oneF M) x (𝕊 t + t) hx h136 h38 h28,
                  rw←  addition_equation,
                  rw successor_shift,                    
                  exact ⟨ ht,h37⟩ ,                    
                end,
              have h51:= h4 r t h35 h135,
              rw← h34,
              rw← h44,
              rw h51, 
            },
            {
              have h30: even M (𝕊 x):=
                begin
                  unfold even,
                  use p,
                  exact h20,
                end,
              have h31: odd M (𝕊 x):=
                begin
                  unfold odd,
                  use q,
                  exact h301,
                end,
              have hsx2:= successorF M x hx hsx,
              have h33:= evenorodd M (𝕊 x) hsx2,
              cases h33 with h34 h35,
              {
                cases h34 with h40 h41,
                contradiction,
              },
              {
                cases h35 with h42 h43,
                contradiction,
              }
            }
          },
          {
            cases h6 with h7 h8,
            {
              have h9: even M (𝕊 x):=
                begin
                  unfold even,
                  use q,
                  exact h7,
                end, 
              have h10: odd M (𝕊 x):=
                begin
                  unfold odd,
                  use p,
                  exact h21,
                end,
              have h33:= evenorodd M (𝕊 x) (successorF M x hx hsx),
              cases h33 with h34 h35,
              {
                cases h34 with h40 h41,
                contradiction,
              },
              {
                cases h35 with h45 h46,
                contradiction,
              }
            },
            {
              cases h21 with hp h22,
              cases h8 with hq h23,
              have hsxf:= successorF M x hx hsx,
              have h40: half M x p:=
                begin
                  unfold half,
                  left,
                  split,
                  {
                    exact hp,
                  },
                  {
                    rw successorisplusone at h22,
                    have h24: p+p ∈ 𝔽 :=
                      begin
                        rw← successorisplusone at h22,
                        rw h22 at hsxf,
                        have h23:= cardinalsinhabited M (p+p+ one) hsxf,
                        cases h23 with u h24,
                        rw addition_members at h24,
                        cases h24 with a h25,
                        cases h25 with b h26,
                        have h27:= h26.2.1,
                        have h28:= additionSF M p hp p hp,
                        have h29:= inhabitedSF M (p+p) h28 ⟨ a, h27⟩, 
                        exact h29,
                      end,
                    rw successorisplusone at hsxf,
                    have h25:= subtraction M one (oneF M) x (p+p) hx h24 hsxf h22,
                    exact h25,
                  }
                end,
              have h41: half M x q:=
                begin
                  unfold half,
                  left,
                  split,
                  {
                    exact hq,
                  },
                  {
                    rw successorisplusone at h23,
                    have h24: q+q ∈ 𝔽:=
                      begin
                        have h100:= additionSF M  q hq q hq,
                        rw←  successorisplusone at  h23,
                        rw h23 at hsxf,
                        have h24:= cardinalsinhabited M (q+q+one) hsxf,
                        cases h24 with u h25,
                        rw addition_members at h25,
                        cases h25 with a h26,
                        cases h26 with b h27,
                        have h28:= h27.2.1,
                        have h29:= inhabitedSF M (q+q) h100 ⟨ a, h28⟩, 
                        exact h29,
                      end,
                    rw successorisplusone at hsxf,
                    have h25:= subtraction M one (oneF M) x (q+q) hx h24 hsxf h23,
                    exact h25,
                  }
                end,
              have h42:= h4 p q h40 h41,
              exact h42,
            }
          }
        }
      end,
    intros x hx,
    rw F_members at hx,
    have h100:= hx (Z_halfunique M) ⟨ base, step⟩,
    rw Z_halfunique_members at h100,
    exact h100.2,
  end    

lemma halfnumber: ∀ (x k:M), x∈ 𝔽 → half M x k → k ∈ 𝔽:=
  assume x k,
  begin
    intros hx h3,
    have h3copy:= h3,
    unfold half at h3copy,
    have h35:= cardinalsinhabited M x hx,
    cases h35 with u h36,
    cases h3copy with h30 h31,
      {
        cases h30 with hk h34,
        rw h34 at h36,
        rw addition_members at h36,
        cases h36 with a h37, 
        cases h37 with b h38,
        have h39:= h38.2.1,
        have h40:= inhabitedSF M k hk ⟨ a, h39⟩,
        exact h40,
      },
      { 
        cases h31 with hk h40,
        rw h40 at h36,
        rw addition_members at h36,
        cases h36 with a h37,
        cases h37 with b h38,
        have h39:= h38.2.1,
        rw addition_members at h39,
        cases h39 with A h50,
        cases h50 with B h51,
        have h52:= h51.2.1,
        have h53:= inhabitedSF M k hk ⟨ A, h52⟩, 
        exact h53,
      }
    end

lemma mover2lem: ∀ (x k:M), x ∈ 𝔽 → k ∈ 𝔽 → half M x k → k+k ≤ x:=
  assume x k hx hk h3,
  begin
    unfold half at h3,
    cases h3 with heven hodd,
    {
      cases heven with hk h5,
      rw h5,
      have h6:= le_reflexive M x hx,
      rw h5 at h6,
      exact h6,
    },
    {
      cases hodd with hksf h8,
      have h9:= cardinalsinhabited M x hx,
      cases h9 with u h10,
      rw h8 at h10,
      rw  addition_members  at h10,
      cases h10 with a h11,
      cases h11 with b h12,
      have h13:= h12.2.1,
      have h14:= additionSF M k hksf k hksf,
      have h15:= inhabitedSF M (k+k) h14 ⟨a, h13⟩, 
      rw← successorisplusone at h8,
      rw h8 at hx, 
      have h20:= cardinalsinhabited M (𝕊 (k+k)) hx,
      have h16:= lessthansuccessor M (k+k) h15 h20,
      rw h8,
      have h18:= lessthan_definition (k+k) (𝕊 (k+k)),
      rw h18 at h16,
      exact h16.1,
    }
  end

lemma nozerodivisors: ∀ (y:M), y ∈ 𝔽 → ∀(x:M), x ∈ 𝔽  → x* y = zero → x = zero ∨ y = zero:=
  begin  
    have base: zero ∈  Z_nozerodivisors M:=
      begin
        rw Z_nozerodivisors_members,
        split,
        {
          exact zeroF M,
        },
        {
          intros x hx h,
          right,
          reflexivity,
        }
      end,
    have step: ∀ (x:M), x ∈ Z_nozerodivisors M → (∃ (u:M), u ∈ (𝕊 x)) → 𝕊 x ∈ Z_nozerodivisors M:=
      begin
        intros y h hsy,
        rw Z_nozerodivisors_members at h,
        rw Z_nozerodivisors_members,
        cases h with hy h3,
        have hsyf:= successorF M y hy hsy,
        split,
        {
          exact hsyf,
        },
        {
          intros x hx h4,
          have h5:= multiplication M x y hx hy hsyf,
          rw h4 at h5,
          rw sym at h5,
          have hx2:= FSF M x hx,
          have hy2:= successorSF M y (FSF M y hy),
          have h7:= multiplicationSF2 M x y hx hy,
          have h6:= addstozero M x hx2 (x* y) h7 h5,
          cases h6 with h9 h10,
          left,
          exact h10,
        }
      end, 
    intros y hy,
    rw F_members at hy,
    have h100:= hy (Z_nozerodivisors M) ⟨ base, step⟩, 
    rw Z_nozerodivisors_members at h100,
    exact h100.2,
  end    

lemma multle: ∀(y:M), y ∈ 𝔽 → ∀ (x a b:M), x∈ 𝔽 → y ∈ 𝔽 → a ∈ 𝔽→ b ∈ 𝔽→ a < b → x < y → b*y ∈ 𝔽 → a *x < b * y:=
  begin
    have base: zero ∈ Z_multle M:=
      begin
        rw Z_multle_members,
        split,
        {
          exact zeroF M,
        },
        {
          intros x a b hx hzero ha hb h4 h5,
          have h6:= nothinglessthanzero M x hx,
          contradiction,
        }
      end,
    have step: ∀ (y:M), y ∈ Z_multle M → (∃(u:M),u ∈ 𝕊 y) → 𝕊 y ∈ Z_multle M:=
      begin
        intros y h3 hsy,
        rw Z_multle_members at h3,
        cases h3 with hy h4,
        have hsyf:= successorF M y hy hsy,
        rw Z_multle_members,
        split,
        {
          exact hsyf,
        },
        {
          intros x a b hx h10 ha hb h11 h12 hbsy,
          have h113:= h4 x a b hx hy ha hb h11,
          have h114:= lessthansuccessor3 M x y hx hy hsy,
          rw h114 at h12,
          have hxsqsf:= multiplicationSF2 M x x hx hx,
          have hax:= multiplicationSF2 M a x ha hx,
          have hby:= multiplicationSF2 M b y hb hy,
          cases h12 with h13 h14,
          {
            have h15:= h4 x a b hx hy ha hb h11 h13,
            have hbyF: b*y ∈ 𝔽:=
              begin
                have h30:= multiplication M b y hb hy h10,
                rw h30 at hbsy,
                have h31:= cardinalsinhabited M (b*y+b) hbsy,
                cases h31 with u h32,
                rw addition_members at h32,
                cases h32 with A h33,
                cases h33 with B h34,
                have h35:= h34.2.1,
                have h36:= inhabitedSF M (b*y) hby ⟨A, h35⟩, 
                exact h36, 
              end, 
            have h16:= h15 hbyF,
            have h16copy:= h16,
            rw lessthan_definition at h16copy,
            have h110:= h16copy.1,
            rw le_definition at h110,
            cases h110 with p h111,
            cases h111 with q h112,
            have hp:= h112.1,
            have hq:= h112.2.1,
            have haxf:= inhabitedSF M (a*x) hax ⟨p,hp⟩,
            have hbyf:= inhabitedSF M (b*y) hby ⟨q,hq⟩,
            have h40:= multiplication M b y hb hy h10,
            rw h40,
            have h99: ¬ b = zero:=
              begin
               intro h,
               rw h at *,
               have h98:= nothinglessthanzero M a ha,
               contradiction,
              end,
            have h95: zero < b:=
              begin
                have h96:= zero_le_x M b hb,
                rw lessthan_definition,
                rw sym at h99,
                exact ⟨ h96, h99⟩,
              end,
            have h41: b*y < b*y+b:=
              begin
                rw h40 at hbsy,
                rw commutativityNF at hbsy,
                have h49:= le_reflexive M (b*y) hbyf,
                have h50:= addorder2 M zero b (b*y) (b*y) (zeroF M) hb hbyf hbyf hbsy h95 h49,
                rw left_identityNF at h50,
                rw commutativityNF,
                exact h50,
              end,
            rw h40 at hbsy,
            have h42:= lessthan_transitive M (a*x) (b*y) (b*y + b) haxf hbyf hbsy h16 h41,
            exact h42,
          },
          {
            rw← h14 at *,
            have h40:= cardinalsinhabited M (b*(𝕊 x)) hbsy,
            have h39: a ≤b:=
              begin
                rw lessthan_definition at h11,
                cases h11 with h38 h37,
                exact h38,
              end, 
            have h41:= orderbyaddition M b hb a ha,
            rw h41 at h39,
            cases h39 with k h38,
            cases h38 with hk h37,
            rw←h37,
            rw← h37 at hb,
            have h36:= left_distributiveNF M (𝕊 x) hsyf a k ha hk hb,
            rw h36,
            rw←  h37 at hbsy,
            rw h36 at hbsy,
            have h35:= multiplication M a x ha hx hsyf,
            rw h35 at hbsy,
            rw h35,
            have h200:= cardinalsinhabited M (a*x+a+k*(𝕊 x)) hbsy,
            cases h200 with A h201,
            rw addition_members at h201,
            cases h201 with p h202,
            cases h202 with q h203,
            rcases h203 with ⟨ h204, h205, h206, h207⟩,
            rw addition_members at h205,
            cases h205 with B h206,
            cases h206 with C h207,
            rcases h207 with ⟨h208, h209, h210,h211⟩, 
            have h212:= inhabitedSF M (a*x) hax ⟨B, h209⟩,  
            have h34:= le_reflexive M (a*x) h212,
            have h213:= addorder2 M zero (a+k*(𝕊 x)) (a*x) (a*x) (zeroF M),
            have h241: ¬ k = zero:=
              begin
                intros h,
                rw h at *,
                rw right_identityNF at h37,
                rw← h37 at *,
                have h242:= xnotlessthanx M a ha, 
                contradiction,
              end,
            have h420:a + k*(𝕊 x) ∈ SF M:=
              begin
                have h604:= multiplicationSF2 M k (𝕊 x) hk h10,
                have h603:= FSF M a ha,
                have h602:= FSF M x hx,
                have h605:= additionSF M a h603 (k*(𝕊 x)) h604,
                rw commutativityNF,
                exact h605,
              end, 
            have h214:a+ k*(𝕊 x) ∈ 𝔽 :=
              begin 
                have h421:= inhabitedSF M (a+ k*(𝕊 x)) h420,
                apply h421,
                have h422:= cardinalsinhabited M (a * x + a + k * 𝕊 x) hbsy,
                cases h422 with P h423,
                rw associativityNF at h423,
                rw addition_members at h423,
                cases h423 with P h424,
                cases h424 with Q h425,
                use Q,
                exact h425.2.2.1,
              end,
            have h215:= h213 h214 h212 h212,
            have h217: a + k * 𝕊 x + a * x ∈ 𝔽 :=
              begin
                have h216:= hbsy,
                rw commutativityNF,
                rw←  associativityNF,
                exact h216,
              end,
            have h218:= h215 h217, 
            have h219: zero < a+ k*(𝕊 x):=
              begin
                have h240:= zero_le_x M  (a + k* (𝕊 x)) h214,
                rw lessthan_definition,
                split,
                {
                  exact h240,
                },
                {
                  intros h,
                  have h250: k * (𝕊 x) ∈ SF M:=
                    begin
                      have h251:= multiplicationSF2 M k (𝕊 x) hk h10,
                      exact h251,
                    end, 
                  have h244: k * (𝕊 x) ∈ 𝔽:=
                    begin
                      exact inhabitedSF M (k * (𝕊 x)) h250 ⟨ q, h206⟩,
                    end,
                  rw sym at h,
                  have h243:= addstozero M (k* (𝕊 x)) h250 a (FSF M a ha) h,
                  cases h243 with h300 h301,
                  have h302:= Fregesuccessoromits0 M x,
                  rw multiplication_commutative at h301,
                  have h303:= nozerodivisors M k hk (𝕊 x) h10 h301,
                  cases h303 with h304 h305,
                  {
                    contradiction,
                  },
                  {
                    contradiction,
                  },
                  {
                    exact h10,
                  },
                  {
                    exact hk,
                  }
                }
              end,
            have h220:= h218 h219 h34,
            rw left_identityNF at h220,
            rw commutativityNF at h220,
            rw← associativityNF at h220,
            exact h220,
          }
        }
      end,
    intros y hy,
    rw F_members at hy,
    have h100:= hy (Z_multle M) ⟨ base, step⟩, 
    rw Z_multle_members at h100, 
    exact h100.2,
  end 

lemma Thalf: ∀(x k:M), x∈ 𝔽 →  half M x k → half M (𝕋 M x) (𝕋 M k):=
  begin
    intros x k hx h3,
    have hk:= halfnumber M x k hx h3,
    unfold half at h3,
    cases h3 with heven hodd,
    {
      cases heven with h4 h5,
      unfold half,
      left,
      have h6:= Tfinite M k hk,
      have h7:= Tfinite M x hx,
      have hxcopy:= hx,
      rw h5 at hxcopy,
      split,
      {
        exact FSF M (𝕋 M k ) h6,
      },
      {
        have h8:= Tsum M k hk k hk hxcopy,
        rw h5,
        exact h8,
      }
    },
    {
      cases hodd with h14 h15,
      unfold half,
      right,
      have h16:= Tfinite M k hk,
      have h17:= Tfinite M x hx,
      have hxcopy:= hx,
      rw h15 at hxcopy,
      split,
      {
        exact FSF M (𝕋 M k ) h16,
      },
      {
        have line1: x = k + (𝕊 k):=
          begin
            rw successorisplusone,
            rw← associativityNF,
            exact h15,
          end,
        have line2:= cardinalsinhabited M x hx,
        have line3: ∃ (u:M), u ∈ (𝕊 k):=
          begin
            cases line2 with u h4,
            rw line1 at h4,
            rw addition_members at h4,
            cases h4 with a h5,
            cases h5 with b h6,
            use b,
            exact h6.2.2.1,
          end, 
        have line4:= successorF M k hk line3,
        have line5: 𝕋 M x = 𝕋 M k + 𝕋 M (𝕊 k):=
          begin
            have hxcopy:= hx,
            rw line1 at hxcopy,
            have h8:= Tsum M  (𝕊 k) line4 k hk hxcopy,
            rw line1,
            exact h8,
          end,
        have line6:= line5,
        rw Tsuccessor at line6,
        rw successorisplusone at line6,
        rw← associativityNF at line6,
        {
          exact line6,
        },
        {
          exact hk,
        },
        {
          exact line3,
        }
      }
    }
  end

#axioms_all 