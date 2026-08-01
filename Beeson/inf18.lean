-- this file develops the theory of arithmetic
-- over Nn,  here called SF M. If there is a 
-- maximal integer, then arithmetic behaves normally,
-- but it takes a lot of proving!  

import inf17 
variables (M:Type) [Model M] (a b x y z u v w X R W κ μ ℓ : M)

open Model 

lemma maximalimplieslargest:
  ∀ (m:M), MAXIMAL M(m) → ∀(k:M), k ∈ 𝔽 → k ≤ m:=
    assume m hmax,
    begin
      intros k hk,
      unfold MAXIMAL at hmax,
      cases hmax with hm h4,
      have h5:= h4 k hk,
      exact h5,
    end 

lemma maximalimpliesnosuccessor:
    ∀ (m:M), MAXIMAL M(m) →  𝕊 m = Λ :=
  begin
    intros m hmax,
    unfold MAXIMAL at hmax,
    cases hmax with hm h4,
    have h5:= h4 (𝕊 m),
    have h6: ¬ (𝕊 m ∈ 𝔽 ):=
      begin
        intros h7,
        have h8:= h5 h7,
        have h9:= xlessthansuccessorx M m hm h7,
        have h10:= le_transitive2 M m (𝕊 m) m hm h7 hm h9 h8,
        have h11:= xnotlessthanx M m hm,
        contradiction,
      end,
    have h20: ¬ ∃ (u:M), u ∈ (𝕊 m):=
      begin
        intros h,
        cases h with u h21,
        have h22:= successorF M m hm ⟨ u, h21⟩, 
        contradiction,
      end,
    rw full_extensionality,
    intros x,
    split,
    {
      intros h34,
      have h35:= successorF M m hm ⟨ x, h34⟩,
      contradiction,
    },
    {
      intros h50,
      have h51:= emptyset_axiom x,
      contradiction,
    }
  end

lemma maximalfiniteF: ∀(m:M), MAXIMAL M(m) → 𝔽 ∈ FINITE M:=
  assume m hmax,
  begin
    have h4:= maxintegerimpliesFfinite M,
    have h5:= hmax,
    unfold MAXIMAL at h5,
    cases h5 with hm h7,
    have h6:= h4 m hm,
    apply h6,
    exact maximalimpliesnosuccessor M m hmax,
  end

lemma lambdanotinF: ¬ ( Λ:M) ∈ 𝔽:=
  begin
    intros h,
    have h3:= cardinalsinhabited M Λ h,
    cases h3 with x h4,
    have h5:= emptyset_axiom x,
    contradiction,
  end

lemma notnotlambda: ∀ (x:M), (¬¬ x = Λ)  → x = Λ:=
  begin
    intros t h11,
    rw full_extensionality,
    intros u,
    split,
      {
        intros h12,
        rw full_extensionality at h11,
        have h13:= notnot_forall (λ (x:M), x ∈ t ↔ x ∈ Λ  ) h11 u,
        dsimp at h13,
        have h14:= emptyset_axiom u,
        have h15: ¬ (t = Λ):=
          begin
            intros h16,
            rw h16 at *,
            contradiction,
          end,
        have h17:= notnot_iff (u∈ t)(u ∈ Λ) h13,
        have h18:= double_negate (u ∈ t) h12,
        rw h17 at h18, 
        contradiction,
      },
      {
        intros h30,
        have h31:= emptyset_axiom u,
        contradiction,
      }
  end

lemma maximalfiniteNn:  ∀(m:M), MAXIMAL M(m) → 𝔽 ∪ single Λ ∈ FINITE M:=
   assume m hmax,
   begin
     have h4:= maximalfiniteF M m hmax,
     have h5:= finite_adjoin M 𝔽 Λ ⟨ h4, lambdanotinF M⟩,
     exact h5,
   end
lemma Fdecidable: ∀ (x y:M), x ∈ 𝔽 → y ∈ 𝔽 → (x = y ∨ ¬ x = y):=
  begin
    have h3:= FregeNdecidable M,
    rw decidable_members at h3,
    intros x y hx hy,
    have h4:= h3 x y ⟨ hx, hy⟩,
    exact h4,
  end

lemma maximalnonemptysuccessor: ∀ (m:M), MAXIMAL M(m) → ∀(u:M), u ∈ 𝔽 → (∃ (v:M),v ∈ 𝕊 u ) ∨ 𝕊 u = Λ:=
  assume m hmax,
  begin
    intros u hu,
    have hmaxcopy:= hmax,
    unfold MAXIMAL at hmax,
    cases hmax with hm h11,
    have h12 := h11 u hu,
    have h13:= letolessthan M u m hu hm,
    rw h13 at h12,
    cases h12 with h13 h14,
    {
      left,
      have h15:= noinsertions M u m hu hm h13,
      rw le_definition at h15,
      rcases h15 with ⟨ a,b, h18, h19⟩,
      exact ⟨ a, h18⟩,
    },
    {
      rw h14,
      right,
      exact maximalimpliesnosuccessor M m hmaxcopy,
    }
  end 

lemma successorLambda: 𝕊 (Λ:M) = Λ:=
  begin
    rw full_extensionality,
    intros x,
    split,
    {
      intro h,
      rw successor_members at h,
      cases h with a  h2,
      cases h2 with b h3,
      rcases h3 with ⟨h4, h5, h6⟩,
      have h7:= emptyset_axiom a,
      contradiction, 
    },
    {
      intro h,
      have h9:= emptyset_axiom x,
      contradiction,
    }
  end

theorem maximalFNn: ∀ (m:M), MAXIMAL M (m) → (SF M) = ((𝔽:M) ∪ single Λ):=
  assume  m hmax,
  begin
    have hmaxcopy:= hmax,
    rw full_extensionality,
    intros x,
    split,
    {
      intros h3,
      rw SF_members at h3,
      have h4:= h3 (𝔽∪ (single Λ)),
      apply h4,
      {
        rw binary_union_axiom,
        left,
        exact zeroF M,
      },
      {
        intros u h20,
        rw binary_union_axiom at h20,
        cases h20 with hu h22,
        {
          unfold MAXIMAL at hmaxcopy,
          cases hmaxcopy with hm h31,
          have h32:= h31 u hu,
          have h33:= letolessthan M u m hu hm,
          rw h33 at h32,
          cases h32 with h34 h35,
          {
            have h36:= noinsertions M u m hu hm h34,
            rw le_definition at h36,
            cases h36 with a h37,
            cases h37 with b h38,
            rcases h38 with ⟨ h40, h41, h42, h43⟩,
            have h45:= successorF M u hu ⟨ a,h40⟩ ,
            rw binary_union_axiom,
            left,
            exact h45,
          },
          {
            rw h35 at *,
            rw binary_union_axiom,
            right,
            rw singleton1,
            have h50:= maximalimpliesnosuccessor M m hmax,
            exact h50,
          }
        },
        {
          rw singleton1 at h22,
          rw h22 at *,
          have h23:= successorLambda M,
          rw h23 at *,
          rw binary_union_axiom,
          right,
          rw singleton1,
        }
      } 
    },
    {
      intros h,
      rw SF_members,
      intros w h30 h31,
      rw binary_union_axiom at h,
      cases h with h32 h33,
      {
        rw F_members at h32,
        have h35:= h32 w,
        apply h35,
        split,
        {
          exact h30,
        },
        {
          intros u hu hsu,
          exact h31 u hu,
        }
      },
      {
        rw singleton1 at h33,
        rw h33 at *,
        have h34:= h31 m,
        have h35:= maximalimpliesnosuccessor M m hmax,
        rw h35 at *,
        apply h34,
        unfold MAXIMAL at hmaxcopy,
        cases hmaxcopy with hm h51,
        have h52: ∀(k:M), k ∈ 𝔽 → k ∈ w:=
          begin
            intros k hk,
            rw F_members at hk,
            have h53:= hk w,
            apply h53,
            split,
            {
              exact h30,
            },
            {
              intros u hu hsu,
              exact h31 u hu,
            }
          end, 
        exact h52 m hm, 
      }
    }
  end

lemma maximalSFdecidable: ∀(m:M), MAXIMAL M(m) → ∀ (x y:M), x ∈ SF M → y ∈ SF M → x = y ∨ ¬ x = y:=
  assume m hmax,
  begin
    have h3:= maximalfiniteNn M m hmax,
    have h4:= maximalFNn M m hmax,
    rw←h4 at h3,
    have h5:= finitedecidable M (SF M) h3,
    rw decidable_members at h5,
    intros x y hx hy,
    exact h5 x y ⟨ hx, hy⟩,
  end

lemma FA_addition: ∀(m:M), MAXIMAL M (m) → ∀ (x y:M),
x ∈ 𝔽 ∪ single Λ → y ∈ 𝔽 ∪ single Λ → x + y ∈ 𝔽 ∪ single Λ :=
  assume m hmax,
  begin
    intros x y h3 h4,
    have h5:= maximalFNn M m hmax,
    have h6:= additionSF M,
    rw← h5 at *,
    exact h6 y h4 x h3, 
  end  

lemma maximalpredofLambda: ∀(m:M), MAXIMAL M (m) → ∀(x:M), x ∈ SF M →   𝕊 x = Λ → x = Λ ∨ x = m:=
  assume m hmax,
  begin
    intros x hx h3,
    have h4:= maximalFNn M m hmax,
    rw h4 at hx,
    rw binary_union_axiom at hx,
    rw singleton1 at hx,
    have hmaxcopy:= hmax,
    unfold MAXIMAL at hmaxcopy,
    cases hmaxcopy with hm h12,
    cases hx with hx h11,
    {
      right,
      have h11:= Fdecidable M x m hx hm,
      cases h11 with h13 h14,
      {
        exact h13,
      },
      {
        have h15:= h12 x hx,
        have h16:= letolessthan M x m hx hm,
        rw h16 at h15,
        cases h15 with h17 h18,
        {
          have h19:= noinsertions M x m hx hm h17,
          rw h3 at h19,
          rw le_definition at h19,
          cases h19 with a h20,
          cases h20 with b h21,
          cases h21 with h22 h23,
          have h24:= emptyset_axiom a,
          contradiction,
        },
        {
          exact h18,
        }
      }
    },
    {
      left,
      exact h11,
    }
  end

lemma lambdaplusx: ∀ (x:M), Λ + x = Λ:=
  begin
    intros x,
    rw full_extensionality,
    intros z,
    split,
    {
      intros h3,
      rw addition_members at h3,
      cases h3 with a h4,
      cases h4 with b h5,
      rcases h5 with ⟨ h6, h7, h8, h9⟩,
      have h20:= emptyset_axiom a,
      contradiction,
    },
    {
      intros h,
      have h4:= emptyset_axiom z,
      contradiction,
    }
  end

lemma xpluslambda: ∀ (x:M), x+ Λ = Λ:=
  begin
    intros x,
    rw full_extensionality,
    intros z,
    split,
    {
      intros h3,
      rw addition_members at h3,
      cases h3 with a h4,
      cases h4 with b h5,
      rcases h5 with ⟨ h6, h7, h8, h9⟩,
      have h20:= emptyset_axiom b,
      contradiction,
    },
    {
      intros h,
      have h4:= emptyset_axiom z,
      contradiction,
    }
  end

lemma maximallambdaSF: ∀(m:M), MAXIMAL M m → Λ ∈ SF M:=
  assume m hmax,
  begin
    have h3:= maximalFNn M m hmax,
    rw h3,
    rw binary_union_axiom,
    right,
    rw singleton1,
  end 

lemma nosuchtriple:  ∀(z:M), ¬ z = Λ → ¬ triple Λ Λ z ∈ multiplication_graph M :=
  begin
    intros z hnz h2,
    rw multiplication_graph_members at h2,
    cases h2 with a h3,
    cases h3 with b h4,
    cases h4 with x1 h5,
    cases h5 with h6 h7,
    rw triple_equality at h6,
    rcases h6 with ⟨ h7, h8, h9⟩,
    rw←h7 at *,
    rw← h8 at *,
    rw← h9 at *,
    have h8:= h7 (multiplication_graph M - single (triple Λ Λ z) ),
    rw← h9 at *,
    have h10:  ∀ (u : M),
     u ∈ SF M →
      (triple u zero zero ∈ (multiplication_graph M - single (triple Λ Λ z))
      ∧ 
     triple zero u zero  ∈ (multiplication_graph M - single (triple Λ Λ z))):=
      begin
        intros u hu,
        split,
        {
          rw minus_members M,
          split,
          {
            have h21:= multiplication2a M u hu,
            cases h21 with h22 h23,
            exact h22,
          },
          {
            intros h35,
            rw singleton1 at h35,
            rw triple_equality at h35,
            rcases h35 with ⟨ h36, h37, h38⟩,
            have h40:= lambdanotinF M,
            have h41:= zeroF M,
            rw  h37 at h41,
            contradiction,
          }
        },
        {
          rw minus_members M,
          split, 
          {
            have h51:= multiplication2a M u hu,
            cases h51 with h52 h53,
            exact h53,
          },
          {
            intros h54,
            rw singleton1 at h54,
            rw triple_equality at h54,
            rcases h54 with ⟨ h55, h56, h57⟩,
            have h58:= zeroF M,
            rw h55 at h58,
            have h59:= lambdanotinF M,
            contradiction,
          }
        }
      end,
    have h60:= h8 h10,
    have h62:   (∀ (u v t : M),
       triple u v t ∈ multiplication_graph M - single (triple Λ Λ z) →
       triple u (𝕊 v) (t + u) ∈ multiplication_graph M - single (triple Λ Λ z)):=
      begin
        intros x y t h63,
        rw minus_members,
        split,
        {
          have h61:= multiplication2b M,
          rw minus_members at h63,
          cases h63 with h64 h65,
          exact h61 x y t h64,
        },
        {
          rw minus_members at h63,
          cases h63 with h66 h67,
          intros h68,
          rw singleton1 at h68,
          rw triple_equality at h68,
          rcases h68 with ⟨ h69, h70, h71⟩,
          rw h69 at *,
          rw h70 at *,
          apply h67,
          rw singleton1,
          rw triple_equality,
          have h73:= multiplicationSF M Λ y t h66,
          rcases h73 with ⟨hlambda, hy, ht⟩,
          have h75:= xpluslambda M t,
          rw h71 at h75,
          contradiction,
        }
      end,
    have h100:= h60 h62,
    rw minus_members at h100,
    cases h100 with h101 h102,
    rw singleton1 at h102,
    apply h102,
    reflexivity,
  end
lemma lambdatimeslambda:∀(m:M), MAXIMAL M m →  (Λ:M)* Λ = Λ :=
  assume m hmax,
  begin
    have h4:= nosuchtriple M,
    rw full_extensionality,
    intros x,
    split,
    {
      intros h,
      have h3:= multiplication_members2 M Λ Λ x,
      rw h3 at h,
      cases h with w h5,
      cases h5 with h6 hw,
      have h7: ¬ w = Λ:=
        begin
          intros h8,
          rw h8 at *,
          have h9:= emptyset_axiom x,
          contradiction,
        end,
      have h10:= h4 w h7,
      contradiction,
    },
    {
      intros h,
      have h40:= emptyset_axiom x,
      contradiction,
    }
  end

lemma lambdatimesx: ∀(m:M), MAXIMAL M m → ∀ (x:M), x ∈ SF M  → ¬ x = zero → Λ *  x = Λ :=
  assume m hmax x hx,
  begin
    have base: zero ∈ Z_lambdatimesx M:=
      begin
        rw Z_lambdatimesx_members,
        split,
        {
          exact zeroSF M,
        },
        {
          intro h,
          contradiction,
        }
      end,

    have step: ∀ (x:M), x ∈ Z_lambdatimesx M  → 𝕊 x ∈ Z_lambdatimesx M:=
      begin
        intros x h4,
        rw Z_lambdatimesx_members at h4,
        cases h4 with hx h6,
        rw Z_lambdatimesx_members,
        split,
        {
          exact successorSF M x hx,
        },
        {
          intros h5, 
          have h6:= multiplication4 M,
          rw full_extensionality,
          intros t,
          split,
          {
            intros h8,
            have h9:= multiplication_members2  M Λ (𝕊 x) t,
            rw h9 at h8,
            cases h8 with z h10,
            cases h10 with h11 h12,
            have h13:= multiplication3 M,
            have h14:= multiplicationSF M Λ (𝕊 x ) z h11,
            rcases h14 with ⟨h16, h17, hz⟩,
            have h15: z = zero ∨ ¬ z = zero:=
              begin
                exact maximalSFdecidable M m hmax z zero hz (zeroSF M),
              end, 
            have h20:= h13 Λ (𝕊 x) z h11,
            cases h20 with h21 h22,

            cases h15 with h16 h17,
            { 
              rw h16 at *,
              have h27: (zero:M) = zero:= 
                begin
                  reflexivity,
                end,
              have h28:= h21 h27,
              cases h28 with h29 h30,
              {
                have h32:= lambdanotinF M,
                have h33:= zeroF M,
                rw h29 at *,
                contradiction,
              },
              {
                have h31:= Fregesuccessoromits0 M x,
                contradiction,
              }
            },
            {
              have h40:= h22 h17,
              cases h40 with p h41,
              cases h41 with q h42,
              cases h42 with r h43,
              rcases h43 with ⟨ h44, h45, h46, h47⟩,
              rw←  addition_equation at h46,
              rw←  h44 at h46,
              have h49:= xpluslambda M r,
              rw h49 at h46,
              rw h46 at h12,
              exact h12,
            }
          },
          {
            intros h,
            have h50:= emptyset_axiom t,
            contradiction,
          }
        },
      end,
    rw SF_members at hx,
    have h80:= hx (Z_lambdatimesx M) base step,
    rw Z_lambdatimesx_members at h80,
    exact h80.2,
  end 

lemma SFclosedmultiplication:   ∀(x y z:M), x ∈ SF M → y ∈ SF M → triple x y z ∈ multiplication_graph M → x ∈ SF M ∧ y ∈ SF M  ∧ z ∈ SF M:= 
  begin
    intros x y z hx hy h3,
    let XX:= Z_multclosed M,
    rw multiplication_graph_members M at h3,
    cases h3 with X h4,
    cases h4 with Y h5,
    cases h5 with Z h6,
    cases h6 with h7 h8,
    rw triple_equality at h7,
    rw← h7.1 at *,
    rw← h7.2.1 at *,
    rw← h7.2.2 at *,
    have h9:= h8 XX,
    have h10:∀ (u : M), u ∈ SF M → triple u zero zero ∈ XX ∧ triple zero u zero ∈ XX:=
      begin
        intros u hu,
        split,
        {
          dsimp [XX],
          rw Z_multclosed_members,
          have h2:= multiplication2a M u hu,
          split,
          {
            exact h2.1,
          },
          {
            use u, use zero, use zero,
            split,
            {
              rw triple_equality,
              split,
              { reflexivity,
              },
              split,
              { 
                reflexivity,
              },
              {
                reflexivity,
              }
            },
            {
              split,
              { 
                exact hu,
              },
              {
                exact ⟨  zeroSF M, zeroSF M⟩ ,
              }
            }
          }
        },
        {
          dsimp [XX],
          rw Z_multclosed_members,
          have h2:= multiplication2a M u hu,
          split,
          { 
            exact h2.2,
          },
          { 
            use zero, use u, use zero,
            split,
            {
              rw triple_equality,
              split,
              { reflexivity,
              },
              split,
              { 
                reflexivity,
              },
              {
                reflexivity,
              }
            },
            {
              split,
              { 
                exact zeroSF M,
              },
              {
                exact ⟨ hu, zeroSF M⟩ ,
              }
            }
          }
        },
      end,
    have h20:(∀ (u v t : M), triple u v t ∈ XX → triple u (𝕊 v) (t + u) ∈ XX):=
      begin
        intros u v t h21,
        dsimp [XX],
        dsimp [XX] at h21,
        rw Z_multclosed_members at h21,
        rw Z_multclosed_members,
        cases h21 with h22 h23,
        have h24:= multiplication2b M u v t h22,
        split,
        {
          exact h24,
        },
        {
          use u, use (𝕊 v), use (t+u),
          split,
          {
            reflexivity,
          },
          {
            cases h23 with p h25,
            cases h25 with q h26,
            cases h26 with r h27,
            cases h27 with h28 h29,
            rw triple_equality at h28,
            rw←h28.1 at *,
            rw←h28.2.1 at *,
            rw←h28.2.2 at *,
            split,
            {
              exact h29.1,
            },
            {
              split,
              {
                exact successorSF M v h29.2.1,
              },
              {
                rcases h29 with ⟨ hu, hv, ht⟩,
                have h33:= additionSF M u hu t ht,
                exact h33,
              }
            }   
          }
        }
      end, 
    have h40:= h9 h10 h20,
    dsimp [XX] at h40,
    rw Z_multclosed_members at h40,
    cases h40 with h41 h42,
    cases h42 with A h43,
    cases h43 with B h44,
    cases h44 with C h45,
    cases h45 with h46 h47,
    rw triple_equality at h46,
    rcases h47 with ⟨ hx, hy, hz⟩,
    rw← h46.1 at *,
    rw← h46.2.1 at *,
    rw← h46.2.2 at *,
    exact ⟨ hx, ⟨ hy, hz⟩ ⟩ , 
  end  

lemma maximalmnotzero: ∀(m:M), MAXIMAL M m → ¬ m = zero:=
  assume m hmax h23,
  begin
    have h26:= maximalimpliesnosuccessor M m hmax,
    rw h23 at h26,
    rw←  one_definition at h26,
    rw full_extensionality at h26,
    have h27:= h26 (single Λ),
    rw one_members at h27,
    cases h27 with h28 h29,
    have h30: ∃ (a:M), single Λ = single a:=
      begin
        use Λ,
      end,
    have h31:= h28 h30,
    have h32:= emptyset_axiom (single Λ),
    contradiction,
  end

lemma oneSF: one ∈ SF M:=
  begin 
    have h:= zeroSF M,
    have h3:= successorSF M zero h,
    rw one_definition,
    exact h3,
  end

lemma twoSF: two ∈ SF M:= 
  begin
    have h:= oneSF M,
    have h3:= successorSF M one h,
    rw two_definition,
    exact h3,
  end

lemma maximalsone: ∀ (m:M), MAXIMAL M m → ∀ (q:M), q ∈ SF M → 𝕊 q = 𝕊 one → q = one:=
  assume m hmax q hq,
  begin
    have h2:= maximalFNn M m hmax,
    have h1:= maximallambdaSF M m hmax,
    have h3:= maximalSFdecidable M m hmax q Λ hq h1,
    cases h3 with h4 h5,
    {
      rw h4 at *,
      intros h6,
      have h7:= successorLambda M,
      rw h7 at h6,
      rw← two_definition at h6,
      rw full_extensionality at h6,
      have h8:= h6 (pair zero one), 
      have h9: (pair zero one) ∈ two:=
        begin
          rw two_members M,
          use zero, use one,
          split,
          {
            have h20:= zero_lessthan_one M,
            intros h21,
            rw h21 at h20,
            have h22:= xnotlessthanx M one (oneF M),
            contradiction,
          },
          {
            reflexivity,
          }
        end,
      have h10:= h8.2 h9,
      have h11:= emptyset_axiom (pair zero one),
      contradiction,
    },
    { 
      intros h50,
      have h50copy:= h50,
      rw← two_definition at h50copy,
      have h20: q ∈ 𝔽:=
        begin
          rw full_extensionality at h2,
          have h21:= h2 q,
          rw h21 at hq,
          rw binary_union_axiom at hq,
          cases hq with h22 h23,
          {
            exact h22,
          },
          {
            rw singleton1 at h23,
            contradiction,
          }
        end,
      have h30:= successoroneone M q one h20 (oneF M),
      have h31:= cardinalsinhabited M two (twoF M),
      simp_rw h50copy at h30,
      simp_rw← two_definition at h30,
      have h32:= h30 h31 h31,
      rw h32,
    }
  end

lemma maximalmSF: ∀ (m:M),MAXIMAL M m → m ∈ SF M:=
  assume m hmax,
  begin
    have h3:= maximalFNn M m hmax,
    rw h3,
    have hmaxcopy:= hmax,
    unfold MAXIMAL at hmaxcopy,
    cases hmaxcopy with hm h4,
    rw binary_union_axiom,
    left,
    exact hm,
  end

lemma mtimesone: ∀(m:M), MAXIMAL M m → triple m one m ∈ multiplication_graph M:=
  assume m hmax,
  begin
    rw one_definition,
    have hmaxcopy:= hmax,
    have h3:= Fregesuccessoromits0 M zero,
    have h4:= multiplication2a M m (maximalmSF M m hmax),
    cases h4 with h10 h11,
    have h12:= multiplication2b M m zero zero h10,
    rw left_identityNF at h12,
    exact h12,
  end

lemma maximalmplusk: ∀(m:M), MAXIMAL M m → ∀(k:M), k ∈ 𝔽 → (¬ k = zero) → m+k = Λ:=
  assume m hmax,
  begin
    intros k hk h3,
    have h4:= nonzeroissuccessor M k hk h3,
    cases h4 with t h5,
    cases h5 with ht h6,
    rw h6 at *,
    rw successor_shift,
    have h8:= maximalimpliesnosuccessor M m hmax,
    rw h8,
    exact lambdaplusx M t,
  end

lemma mtimesx:  ∀(m:M), MAXIMAL M m → ∀ (x:M), x ∈ SF M →  ¬  x = zero → ¬ x = one → m*x = Λ:=
  assume m hmax,
  begin
    have base: zero ∈ Z_mtimesx  M m:=
      begin
        rw Z_mtimesx_members,
        split,
        {
          exact zeroSF M,
        },
        {
          left,
          reflexivity,
        }
      end,
    have step: ∀ (x:M), x ∈ Z_mtimesx M m → 𝕊 x ∈ Z_mtimesx M m:=
      begin
        intros x h,
        rw Z_mtimesx_members at h,
        cases h with h2 h3,
        rw Z_mtimesx_members,
        split,
        {
          exact successorSF M x h2, 
        },
        {
          cases h3 with h4 h5,
          {
            right,left,
            rw one_definition,
            rw h4,
          },
          {
            have h100:= maximalSFdecidable M m hmax (𝕊 x ) one (successorSF M x h2)(oneSF M),
            cases h100 with h101 h102,
            { 
              right,
              left,
              exact h101,
            },
            { cases h5 with h6 h7,
              { 
                right, right,
                rw h6,
                rw full_extensionality,
                intros t,
                split,
                { 
                  intros h8,
                  have h9:= multiplication_members2 M m (𝕊 one) t,
                  rw h9 at h8,
                  cases h8 with r h10,
                  cases h10 with h11 h12,
                  have h13:= multiplication3 M m (𝕊 one) r h11,
                  cases h13 with h14 h15,
                  have h16:= multiplicationSF M m (𝕊 one) r h11,
                  rcases h16 with ⟨ hm, h18, hr⟩,
                  have h19:= maximalSFdecidable M m hmax r zero hr (zeroSF M),
                  cases h19 with h20 h21,
                  { 
                    rw h20 at *,
                    have h21: (zero:M) = zero:= 
                    begin 
                      reflexivity,
                    end,
                    have h22:= h14 h21,
                    cases h22 with h23 h24,
                    {
                      have h25:= maximalmnotzero M m hmax,
                      contradiction,
                    },
                    {
                      rw← two_definition at h24,
                      have h25:= zero_lessthan_two M,
                      rw h24 at h25,
                      have h26:= xnotlessthanx M zero (zeroF M),
                      contradiction,
                    }
                  },
                  {
                    have h22:= h15 h21,
                    cases h22 with p h23,
                    cases h23 with q h24,
                    cases h24 with R h25,
                    rcases h25 with ⟨ h26, h27, h28, h29⟩,
                    rw←  addition_equation at h28,
                    rw← h26 at *,
                    have h30:= multiplicationSF M m q R h29,
                    rcases h30 with ⟨h31, h32, h33⟩,
                    have h34: ¬ R = zero:=
                      begin  
                        intros h35,
                        rw h35 at *,
                        have h37:= sym M (𝕊 one)(𝕊 q),
                        rw h37 at h27,
                        have h36:= maximalsone M m hmax q h32 h27,
                        rw h36 at *,
                        have h37:= mtimesone M m hmax,
                        have hmaxcopy:= hmax,
                        unfold MAXIMAL at hmaxcopy,
                        cases hmaxcopy with hmF h38,
                        have h39:= multiplication4 M one (oneF M) m zero m h29 h37,
                        simp_rw← h39 at h38,
                        have h40:= h38 one (oneF M),
                        have h41:= zero_lessthan_one M,
                        have h42:= le_transitive3 M one zero one (oneF M)(zeroF M)(oneF M) h40 h41,
                        have h43:= xnotlessthanx M one (oneF M),
                        contradiction,
                      end,
                    rw sym M (𝕊 one)(𝕊 q) at h27,
                    have h50:= maximalsone M m hmax q h32 h27,
                    rw h50 at *,
                    have h51:= mtimesone M m hmax,
                    have h52:= multiplication4 M one (oneF M) m R m h29 h51,
                    rw h52 at *,
                    rw h28 at h12,
                    have h35:= hmax,
                    unfold MAXIMAL at h35,
                    cases h35 with hmF h36,
                    have h30:= inhabited_sum M m hmF m hmF ⟨ t, h12⟩, 
                    have h37:= h36 (m+m) h30,
                    have h38:= maximalmnotzero M m hmax,
                    have h39:= maximalmplusk M m hmax m hmF h38,
                    rw h39 at h30,
                    have h40:= lambdanotinF M,
                    contradiction,
                  }
                },
                {
                  intros h,
                  have h10:= emptyset_axiom t,
                  contradiction,
                }
              },
              {
                right,
                right,
                rw full_extensionality,
                intros t,
                split,
                {
                  intros h103,
                  rw multiplication_members2 at h103,
                  cases h103 with z h104,
                  cases h104 with h105 ht,
                  have h106:= multiplication3 M m (𝕊 x) z h105,
                  cases h106 with h107 h108,
                  have h109:= multiplicationSF M m (𝕊 x) z h105,
                  rcases h109 with ⟨ hmSF, h110, hzSF⟩,
                  have h112:= maximalSFdecidable M m hmax z zero hzSF (zeroSF M),
                  cases h112 with h113 h114,
                  {
                    have h115:= h107 h113,
                    have h116:= maximalmnotzero M m hmax,
                    have h117:= Fregesuccessoromits0 M x,
                    cases h115 with h120 h121,
                    {
                      contradiction,
                    },
                    {
                      contradiction,
                    },
                  },
                  {
                    have h120:= h108 h114,
                    cases h120 with p h121,
                    cases h121 with q h122,
                    cases h122 with r h123,
                    rcases h123 with ⟨ h124, h125, h126,h127⟩,
                    rw←  addition_equation at h126,
                    rw← h124 at h126,
                    have h130:= maximalFNn M m hmax,
                    rw full_extensionality at h130,
                    have h131:= (h130 z).1 hzSF,
                    have h132:= (h130 x).1 h2,
                    rw binary_union_axiom at h131 h132,
                    rw singleton1 at h132 h131,
                    have h134:= multiplicationSF M m q r h127,
                    rcases h134 with ⟨ h135, h136, h137⟩,
                    have h133:= maximalSFdecidable M m hmax r zero h137 (zeroSF M),
                    cases h133 with h138 h139,
                    {
                      rw h138 at *,
                      rw left_identityNF at h126,
                      rw h126 at *,
                      have h140:= multiplication3 M m q zero h127,
                      cases h140 with h141 h142,
                      have h143:(zero:M)=zero:= 
                        begin 
                          reflexivity,
                        end,
                      have h144:= h141 h143,
                      cases h144 with h145 h146,
                      {
                        contradiction,
                      },
                      {
                        rw h146 at *,
                        rw←  one_definition at h125,
                        contradiction,
                      }
                    },
                    {
                      have h200:= maximalFNn M m hmax,
                      rw full_extensionality at h200,
                      have h201:= (h200 r).1 h137,
                      rw binary_union_axiom at h201,
                      rw singleton1 at h201,
                      cases h201 with hr h203,
                      {
                        have h204:= nonzeroissuccessor M r hr h139,
                        cases h204 with p h205,
                        cases h205 with hp h206,
                        rw h206 at *,
                        rw← successor_shift at h126,
                        have h207:= maximalimpliesnosuccessor M m hmax,
                        rw h207 at h126,
                        have h208:= xpluslambda M p,
                        rw h208 at h126,
                        rw h126 at ht,
                        exact ht,
                      },
                      { 
                        rw h203 at *,
                        have h210:= lambdaplusx M m,
                        rw h210 at h126,
                        rw h126 at ht,
                        exact ht,
                      }
                    }
                  }
                },
              intro h,
              have h400:= emptyset_axiom t,
              contradiction,
             },
            },
          },
        },
      end,
    intros x hx,
    rw SF_members at hx,
    have h300:= hx (Z_mtimesx M m) base step,
    rw Z_mtimesx_members M m at h300,
    cases h300 with h301 h302,
    intros h303 h304,
    cases h302 with h305 h306,
    {
      contradiction,
    },
    {
      cases h306 with h307 h308,
      {
        contradiction,
      },
      {
        exact h308,
      }
    }
  end  

lemma xtimesm: ∀(m:M), MAXIMAL M m → ∀(p:M), ¬ p = zero → ¬ p = one → p*m = Λ:=
  assume m hmax p h3 h4,
  begin
    rw full_extensionality,
    intros x,
    split,
    {
      intros h5,
      have h5copy:= h5,
      have h6:= multiplication_members2 M p m x,
      rw h6 at h5,
      cases h5 with r h7,
      cases h7 with h8 hxr,
      have h9:= multiplicationSF M p m r h8,
      rcases h9 with ⟨hp, hm, hr⟩, 
      have hmaxcopy:= hmax,
      unfold MAXIMAL at hmaxcopy,
      cases hmaxcopy with hmf h10,
      have h11:= maximalFNn M m hmax,
      rw full_extensionality at h11,
      have h12:= (h11 p).1 hp,
      rw binary_union_axiom at h12,
      cases h12 with hpf h14,
      {
        have h15:= multiplication_commutative M m hmf p hpf,
        have h16:= mtimesx M m hmax p hp h3 h4,
        rw← h15 at h16,
        rw h16 at h5copy,
        exact h5copy,
      },
      {
        rw singleton1 at h14,
        have h20:= multiplication3 M p m r h8,
        have h21:= lambdanotinF M,
        have h22: ¬ Λ = zero:=
          begin
            intros h,
            rw h at h21,
            have h22:= zeroF M,
            contradiction,
          end,
        have h23: ¬ r = zero:=
          begin
            intros h,
            have h24:= (h20.1) h,
            cases h24 with h25 h26,
            {
              contradiction,
            },
            {
              have h27:= maximalmnotzero M m hmax,
              contradiction,
            }
          end,
        have h28:= (h20.2) h23,
        cases h28 with P h29,
        cases h29 with d h30,
        cases h30 with t h31,
        rcases h31 with ⟨ h32, h33, h34,h35⟩,
        rw h14 at *,
        rw← addition_equation at h34,
        rw← h32 at h34,
        have h40:= xpluslambda M t,
        rw h40 at h34,
        rw h34 at hxr,
        exact hxr,
      }
    },
    {
      intros h,
      have h3:= emptyset_axiom x,
      contradiction,
    }
  end  

lemma xtimeslambda_helper: ∀(m:M), MAXIMAL M m → ∀ (x r:M), x ∈ 𝔽 →
   one < x → triple x Λ r ∈ multiplication_graph M → r = Λ:=
  assume m hmax x r hx hbig h3,
  begin
    have h3copy:= h3,
    have h4:= multiplication2b M x Λ r h3,
    let X:= multiplication_graph M - Z_xtimeslambda_helper M,
    have step: ∀ (p q r:M), triple p q r ∈ X → triple p (𝕊 q) (r+p) ∈ X:=
      begin
        intros p q r h6,
        dsimp [X] at h6,
        dsimp [X],
        rw minus_members at h6,
        cases h6 with h7 h8,
        rw Z_xtimeslambda_helper_members at h8,
        rw minus_members,
        rw Z_xtimeslambda_helper_members,
        split,
        { 
          have h9:= multiplication2b M p q r  h7,
          exact h9,
        },
        {
          intros h10,
          cases h10 with P h11,
          cases h11 with Q h12,
          rcases h12 with ⟨ h13, h14, h15, h16⟩,
          rw triple_equality at h13,
          rcases h13 with ⟨ h114, h115, h116⟩, 
          rw← h114 at *,
          rw← h116 at *,
          have h1497: ¬ (q = Λ ∧ ¬ r = Λ):= 
            begin
              intros h17,
              cases h17 with h18 h19,
              rw h18 at *,
              apply h8,
              use p, use r,
              split,
              {
                reflexivity,
              },
              {
                exact ⟨ h14, h15, h19⟩,
              }
            end,
          have h1498: ¬ (q = Λ):=
            begin
              intros h30,
              rw h30 at *,
              apply h1497,
              split,
              {
                reflexivity,
              },
              {
                intros h31,
                rw h31 at *,
                have h32:= lambdaplusx M p,
                contradiction,
              }
            end,
          have h60:= multiplicationSF M p q r h7,
          rcases h60 with ⟨ hp, hq, hr⟩, 
          have h1499:q = m:=
            begin
              have h33:= maximalpredofLambda M m hmax q hq h115,
              cases h33 with h34 h35,
              {
                contradiction,
              },
              {
                exact h35,
              }
            end,
          rw h1499 at *,
          have hmaxcopy:= hmax,
          unfold MAXIMAL at hmaxcopy,
          cases hmaxcopy with hm h38,
          have h1500: r = p * m :=
            begin
              have h37:= multiplication5 M m hm p h14,
              cases h37 with h40 h41,
              have h42:= h41 r hr,
              rw← h42,
              exact h7,
            end,
          have h50:= xtimesm M m hmax p,
          have h51: ¬ p = zero:=
            begin
              intros h,
              rw h at *,
              have h52:= nothinglessthanzero M one (oneF M),
              contradiction,
            end,
          have h53: ¬ p = one:=
            begin
              intros h,
              rw h at *,
              have h54:=xnotlessthanx M one (oneF M),
              contradiction,
            end,
          have h54:= h50 h51 h53,
          rw h54 at *,
          have h55: r+p = Λ:=
            begin
              rw h1500,
              have h56:= lambdaplusx M p,
              exact h56,
            end,
          contradiction,
        }
      end,
    have h80:= multiplication_graph_members M,
    have base: ∀ (u : M), u ∈ SF M → triple u zero zero ∈ X ∧ triple zero u zero ∈ X:=
      begin
        intros u hu,
        have h81:= multiplication2a M u hu,
        cases h81 with h82 h83,
        split,
        {
          dsimp [X],
          rw minus_members,
          split,
          {
            exact h82,
          },
          {
            intros h,
            rw Z_xtimeslambda_helper_members at h,
            cases h with x h84,
            cases h84 with r h85,
            rw triple_equality at h85,
            have h86:= h85.1.2.1,
            have h87:= lambdanotinF M,
            rw← h86 at h87,
            have h88:= zeroF M,
            contradiction, 
          }
        },
        {
          dsimp [X],
          rw minus_members,
          split,
          {
            exact h83,
          },
          {
            intros h,
            rw Z_xtimeslambda_helper_members at h,
            cases h with x h84,
            cases h84 with r h85,
            rw triple_equality at h85,
            have h86:= h85.2.2.1,
            have h87:= h85.1.1,
            rw← h87 at h86,
            have h88:= nothinglessthanzero M one (oneF M),
            contradiction,
          }
        }
      end,
    have h100:= h80 (triple x Λ r),
    rw h100 at h3,
    cases h3 with a h101,
    cases h101 with b h102,
    cases h102 with c h103,
    cases h103 with h104 h105,
    rw triple_equality at h104,
    rcases h104 with ⟨ h106, h107, h108⟩,
    rw← h106 at *, 
    rw← h107 at *,
    rw← h108 at *,
    have h109:= h105 X,  
    have h90: triple x Λ r ∈ X:=
      begin
        apply h109,
        {
          exact base,
        },
        {
          exact step,
        }
      end,
    dsimp [X] at h90,
    rw minus_members at h90,
    cases h90 with h91 h92,
    rw Z_xtimeslambda_helper_members at h92,
    have h93: ¬ ¬ (r = Λ):=
      begin
        intros h,
        apply h92,
        use x, use r,
        split,
        {
          reflexivity,
        },
        {
          exact ⟨ hx, hbig,h⟩,
        }
      end,
    have h94:= multiplicationSF M x Λ r h3copy,
    rcases h94 with ⟨ h95, h96, h97⟩,
    have h98:= maximalSFdecidable M m hmax r Λ h97 h96,
    cases h98 with h99 h100,
    {
      exact h99,
    },
    {
      contradiction,
    }
  end  


lemma xtimeslambda: ∀(m:M), MAXIMAL M m → ∀ (x:M), x ∈ SF M  → ¬ x = zero → ¬ x = one → x * Λ = Λ :=
  assume m hmax,
  begin
    intros x hx h0 h1,
    have h3:= maximalFNn M m hmax,
    rw full_extensionality at h3,
    have h4:= (h3 x).1 hx,
    rw binary_union_axiom at h4,
    cases h4 with hx h6,
    {
      have h7:= finitetrichotomy M x hx one (oneF M),
      cases h7 with h8 h9,
      {
        have h10:= lessthanone M x hx h8,
        rw h10 at *,
        contradiction,
      },
      {
        cases h9 with h11 h12,
        {
          contradiction,
        },
        {
          rw full_extensionality,
          intros u,
          split,
          {
            intros h,
            have h14:= multiplication_members2 M x Λ u,
            rw h14 at h,
            cases h with r h15,
            cases h15 with h16 hr,
            have h17:= xtimeslambda_helper M m hmax x r hx h12 h16,
            rw h17 at *,
            exact hr,
          },
          {
            intros h,
            have h40:= emptyset_axiom u,
            contradiction,
          }
        }
      }
    },
    {
      rw singleton1 at h6,
      rw h6,
      exact lambdatimeslambda M m hmax,
    }
  end

lemma zerotimeslambda: ∀(m:M), MAXIMAL M m →  (zero:M) * Λ = zero:= 
  assume m hmax,
  begin
    rw full_extensionality,
    intros u,
    have h20:= maximallambdaSF M m hmax,
    rw multiplication_members2,
    rw zero_members,
    split,
    {
      intros h,
      cases h with r h3,
      cases h3 with h4 h5,
      have h6:= multiplication3helper M Λ r h4,
      rw h6 at *,
      rw zero_members at h5,
      exact h5,
    },
    {
      intros h,
      rw h at *,
      use zero,
      split,
      {
        have h6:= multiplication2a M Λ h20,
        exact h6.2,
      },
      {
        rw zero_members,
      }
    }
  end

lemma lambdanotzero: ¬(Λ:M) = zero:=
  begin
    have h4:= lambdanotinF M,
    intros h,
    rw h at h4,
    have h5:= zeroF M,
    contradiction,
  end

lemma notnotleastmember: ∀ (X u:M),X ⊆ 𝔽 → u ∈ X → ¬¬ ∃ (r:M), r ∈ X ∧ ∀(t:M), t ∈ 𝔽 → t < r → ¬ t ∈ X :=
  begin
    intros X u hX hu h3,
    have base: zero ∈ Z_notnotleastmember M X,
      begin
        rw Z_notnotleastmember_members,
        split,
        {
          exact zeroF M,
        },
        {
          intros x hx h3,
          have h4:= nothinglessthanzero M x hx,
          contradiction,
        }
      end,
    have step: ∀(m:M), m ∈Z_notnotleastmember M X → (∃(u:M),u ∈ 𝕊 m) → 𝕊 m ∈ Z_notnotleastmember M X:=
      begin
        intros m h5 hsm,
        rw Z_notnotleastmember_members,
        rw Z_notnotleastmember_members at h5,
        cases h5 with hm h7,
        split,
        {
          have h80:= successorF M m hm hsm,
          exact h80,
        },
        {
          intros x hx h8 h9, 
          have h11:= lessthansuccessor3 M x m hx hm hsm,
          rw h11 at h8,
          cases h8 with h12 h13,
          {
            have h14:= h7 x hx h12,
            contradiction,
          },
          {
            rw h13 at *,
            apply h3,
            use m,
            split,
            {
              exact h9,
            },
            {
              intros t h20 h21 h30,
              have h22:= member_subset M X 𝔽 t hX h30, 
              have h23:= h7 t h20 h21,
              contradiction,
            }
          }
        }
      end,
    have h100: ∀ (z:M), z ∈ 𝔽 → z ∈ Z_notnotleastmember M X:=
      begin
        intros z hz,
        rw F_members at hz,
        have h101:= hz (Z_notnotleastmember M X) ⟨ base, step⟩,
        rw Z_notnotleastmember_members at h101,
        rw Z_notnotleastmember_members,
        exact h101,
      end,
    have h105:= member_subset M X 𝔽 u hX hu, 
    have h110:= h100 u h105,
    rw Z_notnotleastmember_members at h110,
    apply h3,
    use u,
    split,
    {
      exact hu,
    },
    {
      exact h110.2,
    } 
  end   



lemma onetimeslambda: ∀ (m:M), MAXIMAL M m →  (one:M) * Λ = Λ :=
  assume m hmax,
  begin
    rw full_extensionality,
    intros u,
    rw multiplication_members2,
    split,
    {
      intros h,
      cases h with R h3,
      cases h3 with h4 h5,
      have h100: ¬ R = Λ:=
        begin
          intros h,
          rw h at h5,
          have h101:= emptyset_axiom u,
          contradiction,
        end,
      have h126:= multiplicationSF M one Λ R h4,
      have hRsf:= h126.2.2,
      have hRf: R ∈ 𝔽:=
        begin
          have h102:= maximalFNn M m hmax,
          rw full_extensionality at h102,
          have h103:= (h102 R).1 hRsf,
          rw binary_union_axiom at h103,
          cases h103 with h104 h105,
          {
            exact h104,
          },
          {
            rw singleton1 at h105,
            contradiction,
          }
        end, 
      have h110: R ∈ Z_onetimeslambda M:=
        begin
          rw Z_onetimeslambda_members,
          exact ⟨ hRf, h4⟩,
        end, 
      have h190: Z_onetimeslambda M ⊆ 𝔽:=
        begin
          rw subset_definition,
          intros z h191,
          rw Z_onetimeslambda_members at h191,
          exact h191.1,
        end,
      have h200:= notnotleastmember M (Z_onetimeslambda M) R h190 h110,
      have h44: ¬∃ (r : M), r ∈ Z_onetimeslambda M ∧ ∀ (t : M), t ∈ 𝔽 → t < r → ¬t ∈ Z_onetimeslambda M :=
        begin
          intros h,    
          cases h with r h2,
          rw Z_onetimeslambda_members at h2,
          cases h2 with h403 h404,
          cases h403 with hr h405,
          have h6:= multiplication3 M one Λ r h405,
          cases h6 with h7 h8,
          have h9:= lambdanotzero M,
          have h10: ¬ (r = zero):=
            begin
              intros h11,
              rw h11 at *,
              have h12: (zero:M) = zero:=
                begin 
                  reflexivity,
                end,
              have h13:= h7 h12,
              cases h13 with h14 h15,
              {
                have h16:= one_neq_zero M,
                contradiction,
              },
              {
                have h17:= lambdanotzero M,
                contradiction,
              }
            end,
      have h20:= h8 h10,
      cases h20 with p h21,
      cases h21 with q h22,
      cases h22 with t h23,
      rcases h23 with ⟨h24, h25, h26, h27⟩, 
      rw← addition_equation at h26,
      rw← h24 at *,
      have h126:= multiplicationSF M one q t h27,
      rcases h126 with ⟨hone,hq,ht⟩,
      rw sym at h25,
      have h30:= maximalpredofLambda M m hmax q hq h25,
      have h29:= successorisplusone M t,
      have h26copy:= h26,
      rw← h29 at h26,
      cases h30 with h31 h32,
      {   
        rw h31 at *,  
        have h9:= lambdanotzero M,
        have h410: ¬ (r = zero):=
          begin
            intros h411,
            rw h411 at *,
            have h412: (zero:M) = zero:=
              begin 
                reflexivity,
              end,
            have h413:= Fregesuccessoromits0 M t,
            contradiction, 
          end,
        have h33:= lessthansuccessor M t,
        
        have h434: ¬ (t = Λ):=
          begin
            intros h,
            rw h at *,
            have h35:= successorLambda M,
            rw h35 at h26,
            rw h26 at hr,
            have h27:= lambdanotinF M,
            contradiction, 
          end,
        have htf: t ∈ 𝔽 :=
          begin
            have h436:= maximalFNn M m hmax,
            rw full_extensionality at h436,
            have h437:= (h436 t).1 ht,
            rw binary_union_axiom at h437,
            rw singleton1 at h437,
            cases h437 with h438 h439,
            {
              exact h438,
            },
            {
              contradiction,
            }
          end,
        have h40:= h33 htf,
        have hrf: r ∈ 𝔽:=
          begin
            have h102:= maximalFNn M m hmax,
            rw full_extensionality at h102,
            have h226:= multiplicationSF M one Λ r h405,
            have hrsf:= h226.2.2,
            have h103:= (h102 r).1 hrsf,
            rw binary_union_axiom at h103,
            cases h103 with h104 h105,
            {
              exact h104,
            },
            {
              rw singleton1 at h105,
              rw h105 at *,
              have h305:= lambdanotinF M,
              contradiction,
            }
          end,
        have h41:= cardinalsinhabited M r hrf,   
        have h43:= h8 h10,
        have h44: t ∈ Z_onetimeslambda M:=
          begin
            rw Z_onetimeslambda_members,
            split,
            {
              exact htf,
            },
            { exact h27,
            }
          end,
        have h45: t < r:=
          begin
            rw h26 at hrf,
            have h50:= xlessthansuccessorx M t htf hrf,
            rw h26,
            exact h50,
          end,
        have h60:= h404 t htf h45,
        contradiction,
      },  
      { 
        rw h32 at *,
        have h200:= h8 h10,
        cases h200 with A h201,
        cases h201 with B h202,
        cases h202 with C h203,
        rcases h203 with ⟨ h204, h205, h206, h207⟩,
        have hmaxcopy:= hmax,
        unfold MAXIMAL at hmaxcopy, 
        cases hmaxcopy with hm h40,
        have h300: triple one m m ∈ multiplication_graph M:=
          begin
            have h50:= one_mulNF M m hm,
            have h51:= multiplication5 M m hm one (oneF M),
            cases h51 with h52 h53,
            have h55:= member_subset M 𝔽 (SF M) m  (FsubsetSF M) hm,
            have h54:= h53 m h55,
            rw h54,
            rw sym at h50,
            exact h50,
          end,
        have h301:= multiplication4 M m hm one t m h27 h300,
        rw h301 at *,
        have h302:= maximalimpliesnosuccessor M m hmax,
        rw h302 at h26,
        rw h26 at hr,
        have h210:= lambdanotinF M,
        contradiction,
      }
     end,
     contradiction,
    },
    {
      intros h,
      have h4:= emptyset_axiom u,
      contradiction,
    }
  end

lemma maximalcases: ∀(m:M), MAXIMAL M m → ∀ (x:M), x ∈ SF M →  x ∈ 𝔽 ∨ x = Λ  :=
  assume m hmax,
  begin
    intros x hxsf,
    have h3:= maximalFNn M m hmax,
    rw full_extensionality at h3,
    have h4:= (h3 x).1 hxsf,
    rw binary_union_axiom at h4,
    rw singleton1 at h4,
    exact h4,
  end

theorem maximalmulrec: ∀(m:M), MAXIMAL M m  →  ∀ (x y:M), x ∈ SF M → y ∈ SF M → x*(𝕊 y) = x*y + x:=
  assume m hmax x y hx hy,
  begin
    have h3:= maximalcases M m hmax x hx,
    have h4:= maximalcases M m hmax y hy,
    have hsysf:= successorSF M y hy, 
    have h40:= maximalcases M m hmax (𝕊 y) hsysf,
    have h41:= maximalSFdecidable M m hmax x zero hx (zeroSF M),
    have h42:= maximalSFdecidable M m hmax x one  hx (oneSF M),    
    cases h3 with hxf h6,
    {
      cases h4 with hyf h7,
      {
        cases h40 with h8 h9,
        {
          have h10:= multiplication M x y hxf hyf h8,
          exact h10,
        },
        {
          rw h9 at *,
          have h11:= xtimeslambda M m hmax x hx,
          cases h41 with h43 h44,
          {
            rw h43 at *,
            have h45:= zerotimeslambda M m hmax,
            rw h45,
            rw zero_mulNF M y hyf,
            rw right_identityNF,
          },
          {
            have h46:= h11 h44,
            cases h42 with h47 h48,
            {
              rw h47 at *,
              rw onetimeslambda M m hmax,
              rw one_mulNF M y hyf,
              rw←  successorisplusone M,
              rw sym,
              exact h9,
            },
            {
              have h49:= h46 h48,
              rw h49,
              have h50:= maximalpredofLambda M m hmax y hy h9,
              cases h50 with h51 h52,
              { 
                rw h51 at *,
                rw xtimeslambda M m hmax x hx h44 h48,
                rw lambdaplusx M x,
              },
              {
                rw h52 at *,
                have h53:= xtimesm M m hmax x h44 h48,
                rw h53,
                rw lambdaplusx M x,
              }
            }
          }
        }
      },
      {
        rw h7 at *,
        rw successorLambda,
        cases h41 with h60 h61,
        {
          rw h60 at *,
          rw zerotimeslambda M m hmax,
          rw right_identityNF,
        },
        {
          cases h42 with h62 h63,
          {
            rw h62 at *,
            rw onetimeslambda M m hmax,
            rw lambdaplusx,
          },
          {
            rw xtimeslambda M m hmax x hx h61 h63,
            rw lambdaplusx,
          }
        }
      }
    },
    {
      rw h6 at *,
      rw xpluslambda,
      have h66:= Fregesuccessoromits0 M y,
      rw lambdatimesx M m hmax (𝕊 y) hsysf h66,
    } 
  end

lemma zero_mulSF: ∀(m:M), MAXIMAL M m → ∀(x:M), x ∈ SF M → zero * x = zero:=
  assume m hmax x hx,
  begin
    have h4:= maximalcases M m hmax x hx,
    cases h4 with h5 h6,
    {
      rw zero_mulNF M x h5,
    },
    {
      rw h6,
      exact zerotimeslambda M m hmax,
    }
  end  

--mul_zeroNF  already works on SF  
lemma multiplication_commutativeSF: ∀ (m:M), MAXIMAL M m → ∀ (x y:M), x∈SF M → y ∈ SF M → x * y = y* x:=
  assume m hmax x y hx hy,
  begin
    have h4:= maximalcases M m hmax x hx,
    have h5:= maximalcases M m hmax y hy,
    have h41:= maximalSFdecidable M m hmax x zero hx (zeroSF M),
    have h141:= maximalSFdecidable M m hmax x one hx (oneSF M),
    have h241:= maximalSFdecidable M m hmax y zero hy (zeroSF M),
    have h241:= maximalSFdecidable M m hmax y one hy (oneSF M),
    cases h41 with h42 h43,
    {
      rw h42 at *,
      rw zero_mulSF M m hmax y hy,
      rw mul_zeroNF M y hy, 
    },
    {
      cases h4 with hxf h6,
      {
        cases h5 with hyf h7,
        {
          rw multiplication_commutative M x hxf y hyf,
        },
        {
          have h141copy:= h141,
          cases h141copy with h8 h9,
          { 
            rw h8 at *,
            rw h7 at *,
            rw lambdatimesx M m hmax one (oneSF M) h43,
            rw onetimeslambda M m hmax,
          },
          { 
            rw h7 at *,
            rw lambdatimesx M m hmax x hx h43,
            cases h141 with h44 h45,
            {
              rw h44 at *,
              have h46: (one:M)=one:=
                begin  
                  reflexivity,
                end,
              contradiction,
            },
            {
              rw xtimeslambda M m hmax x hx h43 h45,
            }
          },
        }
      },
      {
        rw h6 at *,
        cases h5 with h20 h21,
        {
          cases h241 with h250 h251,
          {
            rw h250 at *,
            rw onetimeslambda M m hmax,
            have h260:= one_neq_zero M,
            rw lambdatimesx M m hmax one (oneSF M) h260,
          },
          {  
            have h300:= lambdatimesx M m hmax y hy,
            cases h241 with h242 h243,
            { 
              rw h242 at *,
              rw zero_mulSF M m hmax Λ hx,
              rw mul_zeroNF M,
              exact hx,
            },
            {
              have h301:= h300 h243,
              rw h301,
              rw xtimeslambda M m hmax y hy h243 h251,
            }
          }
        },
        {
          rw h21 at *,
        }
      }
    }
  end 

lemma maximalLambdainSF: ∀(m:M), MAXIMAL M m → Λ ∈ SF M:=
  assume m hmax,
  begin
    have h89:= maximalFNn M m hmax,
    rw h89,
    rw binary_union_axiom,
    right,
    rw singleton1,
  end


lemma maximalSFclosedmultiplication: ∀ (m:M), MAXIMAL M m → ∀(x y:M), x ∈ SF M → y ∈ SF M→ x*y ∈ SF M:=
  assume m hmax x y hx hy,
  begin
    have h80:= multiplication5 M,
    have h2:= maximalcases M m hmax x hx,
    have h3:= maximalcases M m hmax y hy,
    cases h2 with hxf h5,
    {
      cases h3 with hyf h6,
      {
        have h81:= h80 y hyf x hxf,
        cases h81 with h82 h83,
        exact h82,
      },
      {
        have h83:= maximalSFdecidable M m hmax x zero hx (zeroSF M),
        cases h83 with h84 h85,
        {
          rw h84,
          rw zero_mulSF M m hmax y hy,
          exact (zeroSF M),
        },
        {
          rw h6,
          have h7 := xtimeslambda M m hmax x hx h85,
          have h86:= maximalSFdecidable M m hmax x one hx (oneSF M),
          cases h86 with h87 h88,
          {
            rw h87 at *,
            rw onetimeslambda  M m hmax,
            have h89:= maximalLambdainSF M m hmax,
            exact h89,
          },
          {
            rw xtimeslambda M m hmax x hx h85 h88,
            have h89:= maximalFNn M m hmax,
            rw h89,
            rw binary_union_axiom,
            right,
            rw singleton1,
          }
        }
      }
    },
    {
      rw h5,
      have h6:= lambdatimesx M m hmax y hy,
      have h90:= maximalSFdecidable M m hmax y zero hy (zeroSF M),
      cases h90 with h91 h92,
      {
        rw h91 at *,
        rw mul_zeroNF,
        exact (zeroSF M),
        have h89:= maximalLambdainSF M m hmax,
        exact h89,
      },
      {
        have h93:= h6 h92,
        rw h93,
        exact maximalLambdainSF M m hmax,
      }
    }
  end 




#axioms_all