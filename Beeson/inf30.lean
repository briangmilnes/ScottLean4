import inf28
-- but not inf29 which has sorry
variables (M:Type) [Model M] (a b x y z u v w X R W κ μ ℓ : M)
open Model 

lemma Vnotfinitehelper:  ∀(m:M), MAXIMAL M m →  (𝕍 ∈ FINITE M) → exp M (𝕋 M m) = m:=
  begin
    intros m hmax hfinite,
    unfold MAXIMAL at hmax,
    cases hmax with hm h3,
    have h4:= cardinalsinhabited M m hm,
    cases h4 with U hU,
    have h5:= unenlargeable2 M m hm h3 U hU,
    have h6: (¬¬∀ (x : M), x ∈ 𝕍 → x ∈ U):=
      begin
        have h7:= finiteDNS M U 𝕍 hfinite,
        apply h7,
        intros x hx,
        exact h5 x,
      end,
    have h8: ¬¬ (𝕍 ⊆ U):=
      begin
        rw subset_definition,
        exact h6,
      end,
    have h9: U ⊆ 𝕍:=
      begin
        rw subset_definition,
        intros x hx,
        exact V_definition x,
      end,
    have h11: U ⊆ 𝕍 → 𝕍 ⊆ U → U = 𝕍:=
      begin
        intros h12 h13,
        rw full_extensionality,
        intros x,
        split,
        {
          intros h,
          exact V_definition x,
        },
        {
          intros h,
          exact member_subset M  𝕍 U x h13 h,
        }
      end,
    have h15:= h11 h9,
    have h14: ¬¬ U = 𝕍:=
      begin
        have h16:= notnot_imp (𝕍 ⊆ U)(U = 𝕍) h15 h8,
        exact h16,
      end,
    have h17: ∀ (x:M), x ∈ 𝕍 → ¬¬ x ∈ SSC 𝕍 :=
      begin
        intros x hx,
        rw ssc_members,
        have h18: x ⊆ 𝕍:=
          begin
            rw subset_definition,
            intros x hx,
            exact V_definition x,
          end,
        rw notnot_and,
        split,
        {
          intros h,
          apply h,
          exact h18,
        },
        {
          have h20: ∀ (t:M), t ∈ 𝕍 → ¬¬ (t ∈ x ∨ ¬ t ∈ x):=
            begin
              intros t ht,
              have h21:= notnotLEM (t ∈ x),
              exact h21,
            end, 
          set P:= Z_decidable M x with Pdef,
          have h22:= finiteDNS M P 𝕍 hfinite,
          rw Pdef at *,
          simp_rw Z_decidable_members M at *,
          apply h22,
          exact h20,
        }
      end,
    have h23:= finiteDNS M (SSC 𝕍) 𝕍 hfinite h17,
    rw← subset_definition at h23,
    have h25 : (𝕍:M) = SSC (𝕍:M) ↔ (𝕍:M) ⊆ SSC (𝕍:M) ∧ SSC (𝕍:M) ⊆ (𝕍:M) :=
      begin
        split,
        { intro h,
          rw← h,
          simp,
          exact subset_reflexive M 𝕍,
        },
        { intro h,
          cases h with h80 h81,
          apply (full_extensionality M 𝕍 (SSC 𝕍)).2,
          intros t,
          split,
          { intros ht,
            exact member_subset M 𝕍 (SSC 𝕍) t h80 ht, 
          },
          { intro ht,
            exact V_definition t, 
          } 
        }
      end,
        
    have h24: ¬¬ ((𝕍:M) = SSC (𝕍:M)):=
      begin
        rw h25,
        rw notnot_and,
        split,
        {
          exact h23,
        },
        {
          intros h,
          apply h,
          rw subset_definition,
          intros t ht,
          exact V_definition t,
        }
      end,
    have h26: (𝕍:M) = SSC (𝕍:M) → Nc M (𝕍:M) = Nc M (SSC (𝕍:M)):=
      begin
        intros h,
        rw← h,
      end,
    have h27:= notnot_imp 
         ((𝕍:M) = SSC (𝕍:M)) 
         (Nc M (𝕍:M) = Nc M (SSC (𝕍:M))) h26 h24,
    have h28:= finitecardinals3 M (𝕍:M) hfinite,
    have h29:= finitepowerset M (𝕍:M) hfinite,
    have h30:= finitecardinals3 M (SSC (𝕍:M)) h29,
    have h31:= FregeNdecidable M,
    rw decidable_members at h31,
    have h32:= h31 (Nc M (𝕍:M))(Nc M (SSC (𝕍:M))) ⟨ h28, h30⟩,
    have h33: Nc M (𝕍:M) = Nc M (SSC (𝕍:M)):=
      begin
        cases h32 with h34 h35,
        { 
          exact h34,
        },
        {
          contradiction,
        }
      end,
    have h36: (𝕍:M) = (U:M) → Nc M 𝕍 = Nc M U:=
      begin
        intros h,
        rw h,
      end,
    have h37: (𝕍:M) = (U:M) → Nc M U = Nc M (SSC U):=
      begin 
        intros h,
        rw h at h33,
        exact h33,
      end,
    rw sym at h14,
    have h38:= notnot_imp ((𝕍:M) = (U:M))(Nc M U = Nc M (SSC U)) h37 h14,
    have h40:= finitecardinals1 M m U hm hU,
    have h39:= finitecardinals3 M U h40,
    have h41:= finitepowerset M U h40,
    have h42:= finitecardinals3 M (SSC U) h41,
    have h43: Nc M U = Nc M (SSC U):=
      begin
        have h44:= FregeNdecidable M,
        rw decidable_members at h44,
        have h45:= h44 (Nc M U) (Nc M (SSC U)) ⟨ h39, h42⟩,
        cases h45 with h46 h47,
        {
          exact h46,
        },
        {
          contradiction,
        }
      end,
    have h44: USC U ∈ 𝕋 M m:=
      begin
        rw T_members,
        use U,
        exact ⟨ hU, similar_reflexive M (USC U) ⟩,
      end,
    have h45: SSC U ∈ exp M (𝕋 M m):=
      begin
        rw exp_members,
        use U,
        exact ⟨ h44, similar_reflexive M (SSC U)⟩,
      end,
    have h46:= xinNcx M (SSC U),
    have h48:= expTinF M m hm,
    have h49: SSC U ∈ exp M (𝕋 M m) ∩ Nc M (SSC U):=
      begin
        rw intersection_axiom,
        exact ⟨ h45, h46⟩,
      end,
    have h47:= cardinalsdisjoint M (exp M (𝕋 M m)) (Nc M (SSC U)) (SSC U) h48 h42 h49,
    have h51: U ∈ Nc M U ∩ m:=
      begin
        rw intersection_axiom,
        exact ⟨ xinNcx M U, hU⟩,
      end,
    have h50:= cardinalsdisjoint M (Nc M U) m U h39 hm h51,
    rw h47,
    rw← h43,
    exact h50,
  end

lemma Idown: ∀ (n y:M), y ∈ 𝔽 → (∃(u:M), u ∈ 𝕊 y) → (∃(u:M), u ∈ 𝕀 M n (𝕊 y)) → ∃ (u:M), u ∈ 𝕀 M n y:=
  begin 
    intros n y hy hsy h4,
    cases h4 with u h5,
    rw tower_recursion_equation at h5,
    rw exp_members at h5,
    cases h5 with a h6,
    cases h6 with h7 h8,
    use USC a,
    exact h7,
    exact hy,
    exact hsy,
  end


lemma TI: ∀ (n:M), n ∈ 𝔽 →
∀ (y:M), y ∈ 𝔽 → (∃(u:M), u ∈ 𝕀 M n y) → 𝕋 M (𝕀 M n y) = 𝕀 M (𝕋 M n) (𝕋 M y) :=
  begin
    intros  n hn,
    have base: zero ∈ Z_TI M n:=
      begin
        rw Z_TI_members,
        split,
        {
          exact zeroF M,
        },
        {
          intros h3,
          rw tower_base_equation,
          rw Tzero,
          rw tower_base_equation,
        }
      end,
    have step: ∀(y:M), y ∈ Z_TI M n → (∃(u:M),u ∈ 𝕊 y) →  𝕊 y ∈ Z_TI M n:=
      begin
        intros y h3 hsy,
        rw Z_TI_members at h3,
        rw Z_TI_members,
        cases h3 with hy h4,
        split,
        {
          exact successorF M y hy hsy,
        },
        {
          intro h5,
          have h20:= Idown M n y hy hsy h5,
          rw tower_recursion_equation,
          have h21:= Tsuccessor M y hy hsy,
          rw h21,
          rw tower_recursion_equation,
          have h23:= towerF M n hn y hy h20,
          have h22:= expT M (𝕀 M n y) h23,
          cases h5 with u h24,
          rw tower_recursion_equation at h24,
          have h25:= h22 ⟨ u, h24⟩,
          rw← h25,
          have h26:= h4 h20,
          rw h26,
          exact hy,
          exact hsy,
          exact Tfinite M y hy,
          cases hsy with v h27,
          have h28: USC v ∈ 𝕋 M (𝕊 y):=
            begin
              rw T_members,
              use v,
              exact ⟨ h27, similar_reflexive M (USC v) ⟩,
            end,
          use USC v,
          rw Tsuccessor at h28,
          exact h28,
          exact hy,
          exact ⟨v, h27⟩,
          exact hy,
          exact hsy,
        }
      end,
    intros y hy,
    rw F_members at hy,
    have h200:= hy (Z_TI M n) ⟨base, step⟩,
    rw Z_TI_members at h200,
    exact h200.2,
  end


lemma towerbreakI2: ∀(n:M), ∀(y:M), n ∈ 𝔽 → (¬ n = zero)→ y ∈ 𝔽 → 
 ∀ (z:M),z ∈ 𝔽 →  
y+z ∈ 𝔽 →  (𝕀 M n (y+z)) = 𝕀 M (𝕀 M n y) z :=
  begin
    intros n y hn hn2 hy,
    {
      have base: (zero:M) ∈ Z_towerbreakI2 M n y:=
        begin
          rw (Z_towerbreakI2_members M n y),
          split,
          {
            exact (zeroF M),
          },
          {
            rw right_identityNF,
            intros hy,
            rw tower_base_equation,
          }
        end,
      have step: ∀(z:M), z ∈ Z_towerbreakI2 M n y → (∃(u:M), u ∈ 𝕊 z) → 𝕊 z ∈ Z_towerbreakI2 M n y:= 
        begin
          intros z h3 hsz,
          rw Z_towerbreakI2_members,
          rw Z_towerbreakI2_members at h3,
          cases h3 with hz h4,
          split,
          { 
            exact successorF M z hz hsz,
          },
          { 
            intros h5,
            rw addition_equation at h5,
            have h6: y+z ∈ 𝔽:= 
              begin
                have h100:= cardinalsinhabited M (𝕊 (y+z)) h5,
                cases h100 with x h101,
                rw successor_members at h101,
                cases h101 with b h102,
                cases h102 with a h103,
                cases h103 with h104 h105,
                have h106:= inhabited_sum M z hz y hy ⟨ b, h104⟩,
                exact h106,
              end,
            have h7:= h4 h6,
            rw tower_recursion_equation,
            rw←h7,
            rw addition_equation,
            rw tower_recursion_equation,
            exact h6,
            exact cardinalsinhabited M (𝕊 (y+z)) h5,
            exact hz,
            exact hsz,
          }
        end,  
      intros z hz,
      rw F_members at hz,
      specialize hz (Z_towerbreakI2 M n y),
      have h20:= hz ⟨ base, step⟩,
      rw Z_towerbreakI2_members at h20,
      cases h20 with h21 h22,
      exact h22,
    }
  end 

lemma mplusmleexpm: ∀ (m:M), m ∈ 𝔽 → exp M m ∈ 𝔽 →
  m+m ≤ exp M m:=
  begin
    have base: zero ∈ Z_mplusmleexpm M:=
      begin
        rw Z_mplusmleexpm_members,
        split,
        {
          exact zeroF M,
        },
        { intros h,
          rw right_identityNF,
          rw exp_zero,
          have h2:= zero_lessthan_one M,
          rw lessthan_definition at h2,
          exact h2.1,
        }
      end,
    have step: ∀ (m:M), m ∈ Z_mplusmleexpm M → (∃ (u:M),u ∈ 𝕊 m) → 𝕊 m ∈ Z_mplusmleexpm M:=
      begin
        intros m h3 hsm,
        rw Z_mplusmleexpm_members at h3,
        rw Z_mplusmleexpm_members,
        cases h3 with hm h4,
        split,
        {
          exact successorF M m hm hsm,
        },
        { 
          intros h2,
          have h5:= exprec M m hm h2,
          rw h5,
          have h21: exp M m ∈ 𝔽:=
            begin
              have h22:= cardinalsinhabited M (exp M (𝕊 m)) h2,
              cases h22 with u h23,
              rw h5 at h23,
              rw addition_members at h23,
              cases h23 with a h24,
              cases h24 with b h25,
              rcases h25 with ⟨ h26, h27, h28⟩,
              exact finiteexp M m hm ⟨ a, h27⟩,
            end,
          have h20:= successorF M m hm hsm,
          have h100: 𝕊 m ≤ exp M m:= 
            begin
              have h110:= mplusone_le_expm M m hm,
              apply h110,
              exact cardinalsinhabited M (exp M m) h21,
            end,
          rw h5 at h2,
          have h101:= addorder M (𝕊 m)(exp M m)(𝕊 m)(exp M m) h20 h21 h20 h21 h2 h100 h100,
          exact h101,
        }
      end, 
    intros m hm,
    rw F_members at hm,
    specialize hm (Z_mplusmleexpm M),
    have h400:= hm ⟨ base, step⟩,
    rw Z_mplusmleexpm_members M at h400,
    exact h400.2,
  end

lemma mylessthanImy: ∀ (m:M), m ∈ 𝔽 → ¬ m = zero → ∀ (y:M), y∈ 𝔽 → (¬ y = zero) → (∃(u:M), u∈ 𝕀 M m y) → m+y ≤  𝕀 M m y ∧ 𝕀 M m y ∈ 𝔽 :=
  assume m hm h999,
  begin
    have base:zero ∈ Z_mylessthanImy M m:=
      begin
        rw Z_mylessthanImy_members,
        split,
        {
          exact zeroF M,
        },
        {
          intros hzero,
          have h3: (zero:M) = (zero:M) := refl (zero:M),
          contradiction,
        }
      end,
    have step: ∀(y:M), y ∈ Z_mylessthanImy M m → (∃(u:M),u ∈ 𝕊 y) → 𝕊 y ∈ Z_mylessthanImy M m :=
      begin
        intros y h4 hsy,
        have h100:= hsy,
        cases h100 with u hu,
        rw Z_mylessthanImy_members at h4,
        cases h4 with hy h5,
        rw Z_mylessthanImy_members,
        split,
        {
          exact successorF M y hy hsy,
        },
        {
          intros h6 h7,
          cases h7 with b h8,
          have h50:= FregeNdecidable M,
          rw decidable_members at h50,
          have h51:= h50 y zero ⟨ hy, zeroF M⟩,
          cases h51 with h52 h53,
          {
            -- case y = zero
            rw h52 at *,
            rw tower_recursion_equation M m zero hy hsy,
            rw tower_base_equation M m,
            rw tower_recursion_equation M m zero hy hsy at h8,
            rw tower_base_equation M m at h8,
            have h9:= finiteexp M m hm ⟨b,h8⟩, 
            split,
            {
              have h55:= mlessthanexpm M m hm ⟨ b, h8⟩, 
              have h56: 𝕊 zero ≤ m:=
                begin
                  have h60:= lessthanone M,
                  rw←  one_definition,
                  have h61:= finitetrichotomy M m hm one (oneF M),
                  cases h61 with h62 h63,
                  {
                    have h70:= h60 m hm h62,
                    rw h70 at *,
                    contradiction,
                  },
                  {
                    cases h63 with h64 h65,
                    {
                      rw h64 at *,
                      exact le_reflexive M one (oneF M),
                    },
                    {
                      rw lessthan_definition at h65,
                      cases h65 with h66 h67,
                      exact h66,
                    }
                  }
                end,  
              have h100: m+m ≤ exp M m:= mplusmleexpm M m hm h9,
              have h102: m+m ∈ 𝔽 :=
                begin
                  rw le_definition at h100,
                  cases h100 with a h120,
                  cases h120 with b h121,
                  cases h121 with h122 h123,
                  have h124:= inhabited_sum M m hm m  hm ⟨ a, h122⟩, 
                  exact h124,
                end,
              have h103: one ≤  m:= 
                begin
                  have h200:= finitetrichotomy M one (oneF M) m hm,
                  cases h200 with h201 h202,
                  {
                    rw lessthan_definition at h201,
                    exact h201.1,
                  },
                  {
                    cases h202 with h203 h204,
                    {
                      rw← h203,
                      exact le_reflexive M one (oneF M),
                    },
                    {
                      have h205:=lessthanone M m hm h204,
                      contradiction,
                    }
                  }
                end,
              have h104: m+one ≤ m+m :=
                begin
                  have h210:= addorder M m m one m hm hm (oneF M) hm h102 (le_reflexive M m hm) h103,
                  exact h210,
                end,
              have h101: m + 𝕊 zero ≤  m+m:= 
                begin
                  rw addition_equation,
                  rw right_identityNF,
                  rw successorisplusone,
                  exact h104,
                end,
              have h1021: m+ 𝕊 zero ∈ 𝔽:=
                begin
                  rw le_definition at h101,
                  cases h101 with a h1020,
                  cases h1020 with b h103,
                  cases h103 with h104 h105,
                  rw addition_equation,
                  rw addition_equation at h104,
                  rw right_identityNF at h104,
                  rw right_identityNF,
                  exact successorF M  m hm ⟨a,h104⟩,
                end,
              have h57:= le_transitive M (m + 𝕊 zero) (exp M m) (m+m) h1021 h9 h102 h101 h100,
              exact h57, 
            },
            {
              exact h9,
            }
          },
          {
            -- case y ≠ zero
            have h80:= h5 h53,
            rw tower_recursion_equation M m y hy hsy at h8,
            have hb:= h8,
            rw tower_recursion_equation M m y hy hsy,
            rw exp_members at h8,
            cases h8 with a h9,
            cases h9 with h10 h11,
            have h81:= h80 ⟨ USC a, h10⟩,
            cases h81 with h82 h83,
            have h90:= finiteexp M (𝕀 M m y) h83 ⟨b, hb⟩,
            have hsyF:= successorF M y hy hsy,
            have h85:= mlessthanexpm M (𝕀 M m y) h83 ⟨ b, hb⟩,
            have h188: m+y ∈ 𝔽:= 
              begin
                rw le_definition at h82,
                cases h82 with a h200,
                cases h200 with b h201,
                cases h201 with h202 h203,
                have h204:= inhabited_sum M y hy m hm ⟨ a, h202⟩,
                exact h204,
              end,
            have h187:= le_transitive3 M (m+y) (𝕀 M m y)(exp M (𝕀 M m y)) h188 h83 h90 h82 h85,
            have h186: 𝕊(m+y)∈ 𝔽:= 
              begin
                have h189:= noinsertions M (m+y)(exp M (𝕀 M m y)) h188 h90 h187,
                rw le_definition at h189,
                cases h189 with a h190,
                cases h190 with b h191,
                cases h191 with h192 h193,
                exact successorF M (m+y) h188 ⟨a, h192⟩, 
              end,
            have h84:= noinsertions M (m+y) (exp M (𝕀 M m y)) h188 h90 h187,
            split,
            {
              rw addition_equation,
              exact h84,
            },
            {
              exact h90,
            }
          }
        }
      end,
    intros y hy,
    rw F_members at hy,
    have h100:= hy (Z_mylessthanImy M m) ⟨base, step⟩,
    rw Z_mylessthanImy_members M at h100,
    exact h100.2, 
  end

lemma Phitrans: ∀(n p q:M), n ∈ 𝔽 → (¬ n = zero) → p ∈ 𝔽 → q ∈ 𝔽 →
  p ∈ Φ M n → q ∈ Φ M p → q ∈ Φ M n:=
  begin
    intros n p q hn hn2 hp hq h3 h4,
    rw Phi_members at h3 h4,
    rw Phi_members,
    cases h3 with x h5,
    cases h4 with y h6,
    use x+y,
    cases h5 with hx h7,
    cases h6 with hy h8,
    cases h7 with h10 h11,
    cases h8 with h12 h13,
    rw h10 at *,
    rw h12 at *,
    have h9:= towerbreakI2 M n x hn hn2 hx y hy,
    have h190:= Fdecidable M y zero hy (zeroF M),
    cases h190 with h191 h198,
    {
      rw h191 at *,
      rw right_identityNF at *,
      rw tower_base_equation,
      simp,
      exact ⟨ hx, h11⟩,
    },
    have h192:= Fdecidable M x zero hx (zeroF M),
    cases h192 with h193 h197,
    {
      rw h193 at *,
      rw left_identityNF at *,
      rw tower_base_equation,
      simp,
      split,
      {
        exact hy,
      },
      {
        rw tower_base_equation at h12 h13,
        exact h13,
      }
    },
    have h199: ¬ 𝕀 M n x = zero:=
      begin
        have h300:= ylessthanImy M n hn hn2 x hx h197 h11,
        cases h300 with h301 h302,
        intros h,
        rw h at *,
        have h303:= xnotlessthanzero M x hx,
        contradiction,
      end,
    have h200:= mylessthanImy M (𝕀 M n x) hp h199 y hy h198 h13,
    cases h200 with h190 h191,
    have h205: ∃ (u:M), u ∈ 𝕀 M n x + y := 
      begin
        rw le_definition at h190,
        cases h190 with a h191,
        cases h191 with b h192,
        cases h192 with h193 h194,
        exact ⟨ a, h193⟩,
      end,
    have h206: ∃(u:M), u ∈ 𝕀 M n x:=
      begin
        cases h205 with u h206,
        rw addition_members at h206,
        cases h206 with a h207,
        cases h207 with b h208,
        cases h208 with h209 h210,
        exact ⟨ a, h210.1⟩,
      end, 
    have h203: x ≤  𝕀 M n x:= 
      begin
        have h211:= ylessthanImy M n hn hn2 x hx h197 h206,
        cases h211 with h212 h213,
        rw lessthan_definition at h212,
        exact h212.1,
      end, 
    have h219: 𝕀 M n x + y ∈ 𝔽 := 
      inhabited_sum M y hy (𝕀 M n x) hp h205,
    have h220: x + y ≤  𝕀 M n x + y:= 
      addorder M x (𝕀 M n x) y y hx hp hy hy h219 h203 (le_reflexive M y hy),
    have h205: ∃(u:M), u ∈ x + y:= 
      begin
        rw le_definition at h220,
        cases h220 with a h221,
        cases h221 with b h222,
        cases h222 with h223 h224,
        exact ⟨ a, h223⟩,
      end,
    have h230: x + y ∈ 𝔽 := 
      inhabited_sum M y hy x hx h205,
    have h101:= h9 h230,
    rw sym at h101,
    exact ⟨ h230, h101, h13⟩,
  end

lemma towersubset: ∀(n p:M), n ∈ 𝔽 → (¬ n = zero) → p ∈ 𝔽 → 
  p ∈ Φ M n → Φ M p ⊆ Φ M n:=
  begin
    intros n p hn hn2  hp h3,
    rw subset_definition,
    intros q h4,
    have hq: q ∈ 𝔽:= 
      begin
        rw Phi_members at h4,
        cases h4 with y h6,
        rcases h6 with ⟨ h7, h8, h9⟩,
        have h10:= IinF M p hp y h7,
        rw← h8 at *,
        exact h10 h9,
      end,
    have h5:= Phitrans M n p q hn hn2 hp hq h3 h4,
    exact h5,
  end

lemma Phiexp: ∀ (n q:M), n ∈ 𝔽  → (¬ n = zero) → q ∈ Φ M n → (∃ (u:M), u ∈ exp M q)  → exp M q ∈ Φ M n:=
  begin
    intros n q hn hn2 hq h3,
    rw Phi_members,
    rw Phi_members at hq,
    cases hq with y h4,
    use 𝕊 y,
    rcases h4 with ⟨ hy, h5, h6⟩,
    rw h5 at h6,
    have hqF:= towerF M n hn y hy h6,
    rw← h5 at hqF,
    have h3A: exp M q ∈ 𝔽:=
      finiteexp M q hqF h3,
    have h10:= towerF M n hn y hy h6,
    have h12:= cardinalsinhabited M (𝕀 M n y) h10,
    have h450:= Fdecidable M y zero hy (zeroF M),
    cases h450 with h451 h452,
    {
      rw h451 at *,
      rw h5 at *,
      rw tower_base_equation,
      split,
      {
        rw← one_definition,
        exact oneF M, 
      },
      {
        split,
        {
          rw tower_recursion_equation M n,
          rw tower_base_equation,
          exact (zeroF M),
          rw← one_definition,
          exact cardinalsinhabited M one (oneF M), 
        },
        {
          rw tower_base_equation at h3A,
          exact cardinalsinhabited M (exp M n) h3A,
        }
      }
    },
    {
      have h11:= ylessthanImy M n hn hn2 y hy h452 h6,
      have h13:= noinsertions M y (𝕀 M n y) hy h10 h11.1,
      have h14:= h13,
      rw le_definition at h14,
      cases h14 with a h15,
      cases h15 with b h16,
      cases h16 with h17 h18,
      have h19: ∃ (p:M), p ∈ 𝕊 y:= ⟨ a, h17⟩,
      have h20:= successorF M y hy h19,
      have h7:= tower_recursion_equation M n y hy h19,
      rw← h5 at h7,
      have h22: exp M q ∈ Φ M n:=
        begin
          rw Phi_members,
          use (𝕊 y),
          split,
          {
            exact h20,
          },
          {
            split,
            {
              rw sym,
              exact h7,
            },
            {
              exact cardinalsinhabited M (exp M q) h3A,
            }
          }
        end,
      split,
      {
        exact h20,
      },
      {
        rw sym at h7,
        split,
        {
          exact h7,
        },
        {
          exact cardinalsinhabited M (exp M q) h3A, 
        }
      }
    }
  end

lemma TPhi:∀(n z:M), n ∈ 𝔽 →
  z ∈ Φ M n → 𝕋 M z ∈ Φ M (𝕋 M n):=
  begin
    intros n z hn h3,
    rw Phi_members at h3,
    rw Phi_members,
    cases h3 with t h4,
    rcases h4 with ⟨ ht, h6, h7⟩,
    use 𝕋 M t,
    split,
    {
      exact Tfinite M t ht,
    },
    {
      split,
      {
        rw h6,
        have h8:= TI M n hn t ht,
        apply h8,
        rw h6 at h7,
        exact h7,
      },
      {
        cases h7 with u h9,
        use USC u,
        rw T_members,
        use u,
        exact ⟨ h9, similar_reflexive M (USC u) ⟩,
      }
    }
  end 

lemma TimagesubsetPhi: ∀(n:M), n ∈ 𝔽 → (¬ n = zero) →
  imageT M (Φ M n) ⊆  Φ M (𝕋 M n):=
  begin
    intros n hn hn2,
    rw subset_definition,
    intros z hz,
    rw imageT_members M (Φ M n) at hz,
    cases hz with u h4,
    cases h4 with h5 h6,
    rw h6,
    have h7:= TPhi M n u hn h5,
    exact h7, 
  end
 
lemma sevenpointtwo: ∀(n q:M), n ∈ 𝔽 → (¬ n = zero)→  
q ∈ Φ M n → (∀ (t:M), t ∈ Φ M n → t ≤ q) → (¬ q = n) →
Φ M (𝕋 M n) = (imageT M (Φ M n) ∪ (Φ M (exp M (𝕋 M q))))
∧ (imageT M (Φ M n) ∩ (Φ M (exp M (𝕋 M q)))) = (Λ:M):=
  begin
    intros n q hn hn2 hq hmax hqn,
    have h1: q ∈ 𝔽 :=
      begin
        rw Phi_members at hq,
        cases hq with y h40,
        rcases h40 with ⟨ hy, h42, h43⟩,
        rw h42 at h43,
        have h44:= towerF M n hn y hy h43,
        rw h42,
        exact h44,
      end,
    have hq2:= cardinalsinhabited M q h1,
    have hqcopy:= hq,
    have h2: ¬ exp M q ∈ 𝔽 :=
      begin
        intros h,
        have h19:= cardinalsinhabited M (exp M q) h,
        have h20:= mlessthanexpm M q h1 h19,
        have h21: exp M q ∈ Φ M n:=
          begin
            have h22:= Phiexp M n q hn hn2 hq h19,
            exact h22,
          end,
        have h24:= hmax (exp M q) h21,
        have h25:= le_transitive3 M (exp M q) q (exp M q) h h1 h h24 h20,
        have h26:= xnotlessthanx M (exp M q) h,
        contradiction,
      end,
    have h3:exp M q = (Λ:M):=
      begin
        have h4:= finiteexp M q h1,
        rw full_extensionality,
        intros t,
        split,
        {
          intros h30,
          have h31:= h4 ⟨ t, h30⟩,
          contradiction,
        },
        {
          intros h34,
          have h35:= emptyset_axiom t,
          contradiction,
        }
      end,
    have h4: imageT M (Φ M n) ⊆ Φ M (𝕋 M n):=
      begin
        rw subset_definition,
        intros t ht,
        rw imageT_members M (Φ M n) at ht,
        cases ht with u h40,
        cases h40 with h42 h43,
        have h44:= TPhi M n u hn h42,
        rw h43,
        exact h44,
      end,
    have h5: 𝕋 M q ∈ imageT M (Φ M n):=
      begin
        rw imageT_members M (Φ M n),
        use q,
        simp,
        exact hq,
      end,
    have h6: 𝕋 M q ∈ Φ M (𝕋 M n):=
      begin
        have h7:= member_subset M (imageT M (Φ M n)) (Φ M (𝕋 M n)) (𝕋 M q) h4 h5,
        exact h7,
      end,
    have h9: 𝕋 M n ∈ 𝔽  := Tfinite M n hn,
    have h30: zero < 𝕋 M n :=
      begin
        have h62:= Tlessthan M zero n (zeroF M) hn,
        rw Tzero at h62,
        rw← h62,
        rw lessthan_definition,
        have h400:= zero_le_x M n hn,
        split,
        {
          exact h400,
        },
        {
          intros h,
          rw sym at h,
          contradiction,
        }
      end,
    have h40:= cardinalsinhabited M q h1,
    have h300: ¬ 𝕋 M n = zero:=
      begin
        intros h301,
        have h302:= Tzero M,
        have h303:= Toneone M zero n (zeroF M) hn,
        rw h301 at h303,
        rw h302 at h303,
        simp at h303,
        rw sym at h303,
        contradiction,
      end,
    have h12:= expT_inhabited M q h1,
    have h412:= expTinF M q h1,
    have h10:exp M (𝕋 M q) ∈ Φ M (𝕋 M n):= 
      begin
        have h11:= Phiexp M (𝕋 M n)(𝕋 M q) h9 h300 h6,
        apply h11,
        exact h12,
      end,
    have h8:= towerbreakI2 M (𝕋 M n)(exp M (𝕋 M q)) h9 h300 h412,
    have h413:= towersubset M (𝕋 M n) (exp M (𝕋 M q)) h9 h300 h412 h10,
    have h80: imageT M (Φ M n) ∪ Φ M (exp M (𝕋 M q)) ⊆ Φ M (𝕋 M n):=
      begin
        have h81:= union_subset3 M (imageT M (Φ M n))( Φ M (exp M (𝕋 M q)))(Φ  M (𝕋 M n)) h4 h413,
        exact h81,
      end, 
    have hdisjoint1: ∀ (t:M), t ∈ imageT M (Φ M n) → t ≤  𝕋 M q:=
      begin
        intros t ht,
        rw imageT_members M (Φ M n) at ht,
        cases ht with u h90,
        cases h90 with h91 h92,
        rw h92 at *,
        rw← Tlessthanorequal,
        exact hmax u h91,
        rw Phi_members at h91,
        cases h91 with y h92,
        rcases h92 with ⟨ h93, h94, h95⟩,
        rw h94 at h95,
        have h96:= towerF M n hn y h93 h95,
        rw h94,
        exact h96,
        exact h1,
      end, 
    have hdisjoint2: ∀ (t:M), t ∈ Φ M (exp M (𝕋 M q)) → exp M (𝕋 M q) ≤  t:=
      begin
        intros t ht,
        have h97:= finiteexp  M q h1,
        have h98:= ht,
        have h110: t ∈ 𝔽 := 
          begin
            have h111:=Phi_members M (exp M (𝕋 M q)) t,
            have h112:= h111.1 h98,
            cases h112 with y h113,
            rcases h113 with ⟨ h114, h115, h116⟩,
            have h117:= towerF M (exp M (𝕋 M q)),
            rw h115,
            apply h117,
            exact expTinF M q h1,
            exact h114,
            rw← h115,
            exact h116,
          end,
        have h100:= sixpointfour M (exp M (𝕋 M q)) t h412 h110 h98,
        exact h100,
      end,
    have hdisjoint:imageT M (Φ M n) ∩ Φ M (exp M (𝕋 M q)) = Λ:=
      begin
        rw full_extensionality,
        intros t,
        rw intersection_axiom,
        split,
        {
          intros h201,
          cases h201 with h202 h203,
          have h204:= hdisjoint1 t h202,
          have h205:= hdisjoint2 t h203,
          have h110: t ∈ 𝔽  := 
            begin
              have h111:=Phi_members M (exp M (𝕋 M q)) t,
              have h112:= h111.1 h203,
              cases h112 with y h113,
              rcases h113 with ⟨ h114, h115, h116⟩,
              have h117:= towerF M (exp M (𝕋 M q)),
              rw h115,
              apply h117,
              have h118:= expTinF M q h1,
              exact h118,
              exact h114,
              rw← h115,
              exact h116,
            end,
          have h207:= Tfinite M q h1,
          have h206:= le_transitive M (exp M (𝕋 M q)) (𝕋 M q) t h412 h207 h110 h205 h204,
          have h209:= cardinalsinhabited M (exp M (𝕋 M q)) h412,
          have h208:= mlessthanexpm M (𝕋 M q) h207 h209,
          have h210:= le_transitive2 M (𝕋 M q)(exp M (𝕋 M q)) (𝕋 M q) h207 h412 h207 h208 h206,
          have h211:= xnotlessthanx M (𝕋 M q) h207,
          contradiction,
        },
        {
          intros h,
          have h2:= emptyset_axiom t,
          contradiction,
        }
      end,
    have lefttoright: Φ M (𝕋 M n) ⊆  imageT M (Φ M n) ∪ Φ M (exp M (𝕋 M q)) :=
      begin
        rw subset_definition,
        intros p h3000,
        rw Phi_members at hq,
        cases hq with y h301,
        rcases h301 with ⟨hy, h302, h303⟩,
        have h304:= h3000,
        have h754:= Fdecidable M y zero hy (zeroF M),
        cases h754 with h755 h335,
        {
          rw h755 at *,
          rw tower_base_equation at *,
          rw h302 at *,
          contradiction, --here's where we use the assumption q≠n 
        },
        have h340:= ylessthanImy  M n hn hn2 y hy h335,
        rw←  h302 at h340,
        have h341:= h340 h303,
        cases h341 with h342 h343,
        have h344:= noinsertions M y q hy h1 h342,
        have h345:= h344,
        rw le_definition at h345,
        cases h345 with A h346,
        cases h346 with B h347,
        rcases h347 with ⟨ h348, h349, h350⟩,
        have h399: ∃ (u:M), u ∈ 𝕊 (y) := 
          begin
            exact ⟨ A, h348⟩,
          end,
        have h380:= successorF M y hy h399,
        rw Phi_members at h304,
        cases h304 with z h305,
        rcases h305 with ⟨ hz, h307, h308⟩,
        have h311:= Tfinite M y hy,
        have h312:= finitetrichotomy M z hz (𝕋 M y) h311,
        cases h312 with case1 case2and3,
        { 
          have h316:= Tonto3 M z y hz hy case1, 
          cases h316 with r h317,
          rcases h317 with ⟨ hr, h318, h319⟩,
          have h320:= h307,
          rw  h318 at h320,
          have h401:= h1,
          rw h302 at h401,
          have h400:= Iorder M y hy r n hr hn h401 h319,
          have h403:= h400,
          rw lessthan_definition (𝕀 M n r)(𝕀 M n y) at h403,
          cases h403 with h404 h405,
          rw le_definition (𝕀 M n r)(𝕀 M n y) at h404,
          cases h404 with a h406,
          cases h406 with b h407,
          have h408:= h407.1,
          have h600:=  TI M n hn r hr ⟨ a, h408⟩,
          have h601:= h600,
          rw←  h320 at h601,
          rw sym at h601,
          have h409: 𝕀 M n r ∈ Φ M n:=
            begin
              rw Phi_members,
              use r,
              simp,
              exact ⟨ hr, ⟨ a, h408⟩⟩,
            end,
          rw binary_union_axiom,
          left,
          rw imageT_members M (Φ M n),
          use 𝕀 M n r,
          exact ⟨ h409, h601⟩,
        },
        {
          cases case2and3 with case2 case3,
          { -- case 2, z = T y
            rw case2 at *,
            rw h302 at h303,
            have h430:= TI M n hn y hy h303,
            rw binary_union_axiom,
            left,
            rw← h307 at h430,
            rw sym at h430,
            rw h430,
            rw← h302,
            rw imageT_members M (Φ M n),
            use q,
            simp,
            exact hqcopy,
          },
          {  -- case 3
            rw binary_union_axiom,
            right,
            have h402:= noinsertions M (𝕋 M y) z h311 hz case3,
            rw←  Tsuccessor M y hy h399 at h402,
            have h401: 𝕋 M (𝕊 y) ∈ 𝔽:= 
              begin
                have h402:= Tfinite M (𝕊 y),
                apply h402,
                exact h380,
              end,
            have h403:= letosum M (𝕋  M (𝕊 y)) h401 z hz h402,
            cases h403 with u h404,
            cases h404 with hu h405,
            rw sym at h405,
            have h520: ∃(u:M), u ∈ 𝕋 M (𝕊 y):=
              begin
                use USC A,
                rw T_members,
                use A,
                exact ⟨ h348, similar_reflexive M (USC A) ⟩,
              end, 
            have h424: (∃ (u : M), u ∈ 𝕀 M (𝕋 M n) (𝕋 M (𝕊 y))):= 
              begin
                have h500:=expTinhabited M q h1,
                rw h302 at h500,
                cases h500 with u h501,
                rw TI at h501,
                use u,
                have h502:= Tsuccessor M y hy h399,
                rw h502,
                rw tower_recursion_equation M (𝕋 M n) (𝕋 M y) h311,
                exact h501,
                rw← Tsuccessor,
                exact h520,
                exact hy,
                exact h399,
                exact hn,
                exact hy,
                rw← h302,
                exact h303,
              end,
            have h425:= towerbreakI2 M (𝕋 M n)(𝕋 M (𝕊 y)) h9 h300 h401 u hu,-- h424 u hu,
            rw←  h405 at h425,
            have h406: (𝕀 M (𝕋 M n) z) ∈ (Φ M (𝕀 M (𝕋 M n) ( 𝕋 M (𝕊 y)))):=
              begin
                rw Phi_members M (𝕀 M (𝕋 M n) ( 𝕋 M (𝕊 y))),
                use u,
                split,
                {
                  exact hu,
                },
                {
                  split,
                  {  
                    exact h425 hz,
                  },
                  {
                    rw←h307,
                    exact h308, 
                  }
                }
              end,
            have h407:= h406,
            rw← h307 at h407,
            rw Tsuccessor at h407,
            have h420:∃ (u : M), u ∈ 𝕊 (𝕋 M y):=
              begin
                cases h399 with u h421,
                use USC u,
                rw← Tsuccessor,
                rw T_members,
                use u,
                exact ⟨ h421, similar_reflexive M (USC u)⟩, 
                exact hy,
                exact ⟨ u, h421⟩,
              end,
            rw tower_recursion_equation M (𝕋 M n)(𝕋 M y) (Tfinite M  y hy) h420 at h407,
            rw← TI at h407,
            have h408: 𝕋 M q = (𝕋 M (𝕀 M n y)):=
              begin
                rw h302,
              end,
            rw←  h408 at h407,
            exact h407, 
            -- some leftover goals...
            exact hn,
            exact hy,
            have h409:= h303,
            rw h302 at h409,
            exact h409,
            exact hy,
            exact h399,
          },
        }
      end,
    split,
    {
      rw full_extensionality,
      intros t,
      split,
      { --left to right
        intros ht,
        have h720:= member_subset M (Φ M (𝕋 M n))(imageT M (Φ M n) ∪ Φ M (exp M (𝕋 M q))) t lefttoright ht,
        exact h720,
      },
      {
        --right to left
        intros ht,
        exact member_subset M (imageT M (Φ M n) ∪ Φ M (exp M (𝕋 M q)))( Φ M (𝕋 M n)) t h80 ht,
      }
    },
    {
      exact hdisjoint,
    }  
  end

lemma Timagefinite: ∀ (X:M), X ⊆ NC M → X ∈ FINITE M → imageT M X ∈ FINITE M:=
  begin
    intros X hX hfinite,
    have h3:= Timage M X hfinite hX,
    have h4:= finitecardinals3 M X hfinite,
    have h5:= Tfinite M (Nc M X) h4,
    have h6:= h5,
    rw← h3 at h6, 
    have h8:= xinNcx M (imageT M X),
    have h7:= finitecardinals1 M (Nc M (imageT M X)) (imageT M X) h6 h8,
    exact h7,
  end

lemma sevenpointtwoB: ∀ (m:M), MAXIMAL M m → ∀(n q:M), n ∈ 𝔽 → (¬ n = zero)→  
q ∈ Φ M n → (∀ (t:M), t ∈ Φ M n → t ≤ q) → (¬ q = n) →
Nc M (Φ M (𝕋 M n)) = 𝕋 M (Nc M (Φ M n)) + Nc M (Φ M (exp M (𝕋 M q))) :=
  begin
    intros m hmax n q hn hn2 hqphi hqmax hqn,
    have hq: q ∈ 𝔽 :=
      begin
        have h200:= hqphi,
        rw Phi_members at h200,
        cases h200 with y h201,
        rcases h201 with ⟨ hy, h203, h204⟩,
        rw h203 at h204,
        have h205:= towerF M n hn y hy h204,
        rw h203,
        exact h205,
      end,
    have h3:= sevenpointtwo M n q hn hn2 hqphi hqmax hqn,
    cases h3 with h4 h5,
    have h6: Nc M (Φ M (𝕋 M n)) = Nc M(imageT M (Φ M n) ∪ Φ M (exp M (𝕋 M q))) :=
      begin
        rw h4,
      end,
    have h101:= Phifinite M m hmax n hn,
    have h102: Φ M n ⊆ NC M:= 
      begin
        rw subset_definition,
        intros t h103,
        rw Phi_members at h103,
        cases h103 with y h104,
        cases h104 with hy h105,
        cases h105 with h106 h107,
        rw h106 at *,
        have h108:= towerNC M n (FtoNC M n hn) y hy h107,
        exact h108,   
      end,
    have h7: imageT M (Φ M n) ∈ FINITE M := 
      Timagefinite M (Φ M n) h102 h101,
    have h10:= Timage M (Φ M n) h101 h102,
    rw NCsum at h6,
    rw h10 at h6,
    exact h6,
    exact h7,
    have h120:= Phifinite M m hmax (exp M (𝕋 M q)),
    apply h120,
    exact expTinF M q hq,
    exact h5,
  end

  lemma Iorder2: ∀ (n m:M), n ∈ 𝔽 → m ∈ 𝔽 → n < m → 
    ∀ (y:M), y ∈ 𝔽 → 𝕀 M m y ∈ 𝔽 → 𝕀 M n y < 𝕀 M m y:=
    begin
      intros n m hn hm h2,
      have base: zero ∈ Z_Iorder2 M n m:=
        begin
          rw Z_Iorder2_members M n m,
          rw tower_base_equation,
          rw tower_base_equation,
          exact ⟨ zeroF M, λ(p:m∈𝔽),h2⟩,
        end,
      have step: ∀ (y:M), y ∈ Z_Iorder2 M n m → (∃ (u:M),u ∈ 𝕊 y) → (𝕊 y ∈ Z_Iorder2 M n m):=
        begin
          intros y h4 hsy,
          rw Z_Iorder2_members M n m at h4,
          rw Z_Iorder2_members M n m,
          cases h4 with hy h5,
          split,
          {
            exact successorF M y hy hsy,
          },
          { 
            intros h10,
            rw tower_recursion_equation,
            rw tower_recursion_equation,
            rw tower_recursion_equation at h10,
            have h11:= cardinalsinhabited M (exp M (𝕀 M m y )) h10,
            cases h11 with x h12,
            rw exp_members at h12,
            cases h12 with a h13,
            cases h13 with h14 h15,
            have h16: 𝕀 M m y ∈ 𝔽:=
              begin
                have h17:= towerF M m hm y hy ⟨ USC a, h14⟩,
                exact h17,
              end,
            have h312:= h5 h16,
            rw lessthan_definition at h312,
            cases h312 with h313 h314,
            rw le_definition at h313,
            cases h313 with a h314,
            cases h314 with b h315,
            cases h315 with h316 h317,
            have h17: 𝕀 M n y ∈ 𝔽 := 
              begin
                have h320:= towerF M n hn y hy ⟨a, h316⟩,
                exact h320,
              end,
            have h19:= cardinalsinhabited M (exp M (𝕀 M m y)) h10,
            have h20:= exporderstrict M (𝕀 M n y)(𝕀 M m y) h17 h16 (h5 h16) h19,
            exact h20.2,
            exact hy,
            exact hsy,
            exact hy,
            exact hsy,
            exact hy,
            exact hsy,
          }
        end,
      intros y hy, 
      rw F_members at hy,
      specialize hy (Z_Iorder2 M n m),
      have h450:= hy ⟨base, step⟩,
      rw Z_Iorder2_members at h450,
      exact h450.2,
    end

  lemma PhiF: ∀ (n p:M), n ∈ 𝔽 → p ∈ Φ M n → p ∈ 𝔽 :=
    begin
      intros n p hn hp,
      rw Phi_members at hp,
      cases hp with y h3,
      rcases h3 with ⟨ hy, h4, h5⟩,
      rw h4 at h5,
      have h6:= IinF M n hn y hy h5,
      rw h4,
      exact h6,
    end

  lemma Phimembersinhabited:∀ (n p:M), n ∈ 𝔽 → p ∈ Φ M n → ∃ (u:M), u ∈ p :=
    begin
      intros n p hn hp,
      have h4:= PhiF M n p hn hp,
      exact cardinalsinhabited M p h4,
    end

  lemma similarity_helper: ∀ (f A B R:M), maps M f A B →
    oneone M f A B → R = range f → R ⊆ B → dom f = A →
    similarity M f A R:=
    begin
      intros f A B R hmaps honeone Rdef h3 h4,
      unfold similarity,
      unfold maps at hmaps,
      rcases hmaps with ⟨ hRel, h6,h7, h8⟩,
       
      split,
      {
        unfold oneone,
        split,
        {
          unfold maps,
          split,
          {
            exact hRel,
          },
          {
            split,
            {
              intros x y h9,
              have h10:= h6 x y h9,
              rw Rdef,
              rw range_axiom f hRel,
              use x,
              exact h9.2,
            },
            {
              split,
              {
                exact h7,
              },
              {
                intros x h,
                have h9:= h8 x h,
                cases h9 with y h10,
                use y,
                cases h10 with hx h11,
                split,
                {
                  rw Rdef,
                  rw range_axiom f hRel,
                  use x,
                  exact h11,
                },
                {
                  exact h11,
                }
              }
            }
          }
        },
        {
          unfold oneone at honeone,
          rcases honeone with ⟨h20, h21, h22⟩,
          split,
          {
            exact h21,
          },
          {
            intros x y h23,
            cases h23 with h24 h25,
            have h260:= h22 x y,
            apply h260,
            split,
            {
              exact h24,
            },
            {
              rw Rdef at h25,
              rw range_axiom f hRel at h25,
              cases h25 with X h26,
              have h27:= h21 x X y,
              have h28:x ∈ A:=
                begin
                  rw← h4,
                  rw domain_axiom f hRel,
                  use y,
                  exact h24,
                end,
              have h29:= h27 ⟨ h24, h26, h28⟩,
              rw← h29 at *,
              have h30:= h8 x h28,
              cases h30 with Y h31,
              cases h31 with h32 h33,
              have h34:= h7 x y Y ⟨ h28, h26, h33⟩,
              rw← h34 at *,
              exact h32,
            }
          }
        }
      },
      {
        unfold onto,
        intros y hy,
        rw Rdef at hy,
        rw range_axiom f hRel at hy,
        cases hy with x h80,
        use x,
        rw←h4,
        rw domain_axiom f hRel,
        split,
        {
          exact ⟨ y, h80⟩,
        },
        {
          exact h80,
        }
      }
    end

  lemma lessthan_to_inhabited: ∀ (n m:M), n < m → ∃ (u:M), u ∈ n :=
    begin
      intros n m h,
      rw lessthan_definition at h,
      cases h with h2 h3,
      rw le_definition at h2,
      cases h2 with a h4,
      cases h4 with h5 h6,
      exact ⟨ a, h6.1⟩,
    end
  
  lemma le_to_inhabited: ∀ (n m:M), n ≤  m → ∃ (u:M), u ∈ n :=
    begin
      intros n m h,
      rw le_definition at h,
      cases h with a h4,
      cases h4 with h5 h6,
      exact ⟨ a, h6.1⟩,
    end


  lemma maximalPhi: ∀ (m n:M), MAXIMAL M m → 
    n ∈ 𝔽 → (¬ n = zero) → 
    ∃ (q:M), q ∈ 𝔽 ∧ q ∈ Φ M n ∧ exp M q = Λ ∧ ∀ (p:M),p ∈ Φ M n → p ≤ q:=
    begin
      intros m n hmax hn hn2,
      have h3:= Phifinite M m hmax n hn,
      have h4: Φ M n ⊆ 𝔽 :=
        begin
          rw subset_definition,
          intros t ht,
          have h11:= PhiF M n t hn ht,
          exact h11,
        end,
      have h5:= minPhim M n (cardinalsinhabited M n hn),
      have h6: ¬ (Φ M n = Λ):=
        begin
          intros h,
          rw full_extensionality at h,
          specialize h n,
          rw h at h5,
          have h6:= emptyset_axiom n,
          contradiction,
        end,
      have h10:= finitemaximal M (Φ M n) h3 h4 h6,
      cases h10 with q h11,
      use q,
      cases h11 with h12 h13,
      have h14:= PhiF M n q hn h12,
      split,
      {
        exact h14,
      },
      {
        split,
        {
          exact h12,
        },
        { 
          split,
          {
            rw full_extensionality,
            intros t,
            split,
            {
              intros h,
              have h20:= Phiexp M n q hn hn2 h12 ⟨ t, h⟩, 
              have h21:= mlessthanexpm M q h14 ⟨ t, h⟩,
              have h22:= h13 (exp M q) h20,
              have h23:= PhiF M n (exp M q) hn h20,
              have h24:= le_transitive2 M q (exp M q) q h14 h23 h14 h21 h22,
              have h25:= xnotlessthanx M q h14,
              contradiction,
            },
            {
              intros h,
              have h26:= emptyset_axiom t,
              contradiction,
            }
          },
          {
            exact h13,
          }
        }
      }
    end
  

lemma Iordertwoway: ∀ (n y z:M), n ∈ 𝔽 → y ∈ 𝔽 → z ∈ 𝔽 →
𝕀 M n y ≤  𝕀 M n z → y ≤ z:=
  begin
    intros n y z hn hy hz h4,
    have h5:=le_to_inhabited M (𝕀 M n y)(𝕀 M n z) h4,
    have h6: ∃ (u:M), u ∈ 𝕀 M n z:=
      begin 
        rw le_definition at h4,
        cases h4 with a h5,
        cases h5 with b h6,
        use b,
        exact h6.2.1,
      end,
    have h7:= finitetrichotomy M y hy z hz,
    cases h7 with h8 h9,
    {
      rw lessthan_definition at h8,
      exact h8.1,
    },
    {
      cases h9 with h10 h11,
      {
        rw h10 at *,
        exact le_reflexive M z hz,
      },
      {
        have h13:= towerF M n hn y hy h5,
        have h15:= towerF M n hn z hz h6,
        have h12:= Iorder M y hy z n hz hn h13 h11,
        have h14:= le_transitive2 M (𝕀 M n z) (𝕀 M n y)(𝕀 M n z) h15 h13 h15 h12 h4,
        have h16:= xnotlessthanx M (𝕀 M n z) h15,
        contradiction,
      }
    }
  end

lemma Iordertwowaystrict: ∀ (n y z:M), n ∈ 𝔽 → y ∈ 𝔽 → z ∈ 𝔽 →
𝕀 M n y <  𝕀 M n z → y < z:=
  begin
    intros n y z hn hy hz h3,
    rw lessthan_definition at h3,
    cases h3 with h4 h5,
    have h6:= Iordertwoway M n y z hn hy hz h4,
    rw letolessthan M y z hy hz at h6,
    cases h6 with h7 h8,
    {
      exact h7,
    },
    {
      rw h8 at *,
      contradiction,
    }
  end

  lemma reversemonotonicity: ∀(max:M), MAXIMAL M max→ ∀ (n m:M), 
    n ∈ 𝔽 → m ∈ 𝔽 → 
    n ≤ m → Nc M (Φ M m) ≤  Nc M ( Φ M n):=
    begin
      intros max hmax n m hn hm h3,
      have h950:= Fdecidable M n m hn hm,
      have h955:= Phifinite M max hmax m hm,
      cases h950 with h951 h952,
      {
        rw h951,
        have h953:= le_reflexive M (Nc M (Φ M m)),
        apply h953,
        have h954:= finitecardinals3 M (Φ M m) h955,
        exact h954,
      },
      have h956: n < m:=
        begin
          rw lessthan_definition,
          exact ⟨ h3, h952⟩,
        end,
      have hm2: ¬ (m = zero):=
        begin
          intros h,
          rw h at h956,
          have h957:= xnotlessthanzero M n hn,
          contradiction,
        end,
      set f:= freverse M n m with fdef,
      have hRel: Rel f:=
        begin
          rw Rel_definition,
          intros z hz,
          rw fdef at hz,
          rw freverse_members M n m z at hz,
          cases hz with p h4,
          cases h4 with q h5,
          use p, use q,
          exact h5.1,
        end,
      have hmaps: maps M f (Φ M m) (Φ M n):=
        begin
          unfold maps,
          split,
          { 
            exact hRel,
          },
          {
            split,
            {
              intros p q h6,
              cases h6 with hp h7,
              have h80:= hp,
              have h81:= Phimembersinhabited M m p hm h80, 
              have h82:= PhiF M m p hm h80,
              rw fdef at h7,
              rw freverse_members M n m ‹p,q ›  at h7,
              cases h7 with Q h8,
              cases h8 with P h9,
              rw ordered_pair_equality at h9,
              cases h9 with h10 h11,
              rw← h10.1 at *,
              rw← h10.2 at *,
              cases h11 with y h12,
              cases h12 with hy h13,
              cases h13 with h14 h15,
              rw Phi_members,
              use y,
              split,
              {
                exact hy,
              },
              {
                split,
                {
                  exact h15.1,
                },
                { 
                  have h19:= (letolessthan M n m hn hm).1 h3,
                  cases h19 with h30 h31,
                  {
                    rw h14 at h82,
                    have h20:= Iorder2 M n m hn hm h30 y hy h82,
                    have h21: ∃ (u:M), u ∈ 𝕀 M n y:=
                      lessthan_to_inhabited M ( 𝕀 M n y)( 𝕀 M m y) h20,
                    rw h15.1,
                    exact h21,
                  },
                  {
                    rw h31 at *,
                    rw← h14 at *,
                    rw h15.1,
                    exact h81,
                  }
                }
              }  
            },
            {
              split,
              {
                intros x y z h30,
                rcases h30 with ⟨ h31, h32, h33⟩,
                rw fdef at *,
                rw freverse_members at *,
                cases h32 with p h34,
                cases h34 with q h36,
                cases h33 with P h37,
                cases h37 with Q h38,
                rw ordered_pair_equality at *,
                cases h36 with h39 h40,
                cases h38 with h41 h42,
                cases h42 with Y h43,
                rcases h43 with ⟨ hY, h45, h46⟩,
                cases h40 with yy h47,
                rcases h47 with ⟨ hyy, h48, h49⟩,
                cases h39 with h50 h51,
                cases h41 with h52 h53,
                rw h50 at *,
                rw h53 at *,
                rw h51 at *,
                rw h52 at *,
                rw h48 at *,
                have h55:= PhiF M m (𝕀 M m yy) hm h31,
                have h54:= Ioneone M m yy Y hm hyy hY h55 h45,
                rw h54 at *,
                rw h46 at *,
                rw h49 at *,
                cases h46 with h180 h181,
                cases h49 with h182 h183,
                rw h180,
                rw h182,
              },
              {
                intros x h60,
                rw Phi_members at h60,
                cases h60 with y h61,
                rcases h61 with ⟨h62,h63,h64⟩,
                use 𝕀 M n y,
                split,
                {
                  rw Phi_members,
                  use y,
                  simp,
                  split,
                  {
                    exact h62,
                  },
                  {
                    rw h63 at h64,
                    rw letolessthan M n m hn hm at h3,
                    cases h3 with h66 h67,
                    {
                      have h68:= IinF M m hm y h62 h64,
                      have h65:= Iorder2 M n m hn hm h66 y h62 h68,
                      rw lessthan_definition at h65,
                      cases h65 with h69 h70,
                      rw le_definition at h69,
                      cases h69 with a h71,
                      cases h71 with b h72,
                      cases h72 with h73 h74,
                      exact ⟨ a, h73⟩,
                    },
                    {
                      rw h67 at *,
                      exact h64,
                    }
                  }
                },
                {
                  rw fdef,
                  rw freverse_members,
                  use x,
                  use 𝕀 M n y,
                  simp,
                  use y,
                  simp,
                  split,
                  {
                    exact h62,
                  },
                  { 
                    split,
                    {
                      exact h63,
                    },
                    {
                      rw Phi_members,
                      use y,
                      exact ⟨ h62, h63, h64⟩,
                    }
                  }
                }
              }
            }
          }
        end,
      have honeone: oneone M f (Φ M m) (Φ M n):=
        begin
          unfold oneone,
          split,
          {
            exact hmaps,
          },
          {
            split,
            {
              intros p r q h101,
              rcases h101 with ⟨ h102, h103, h104⟩,
              rw fdef at h102 h103,
              rw freverse_members at h102 h103,
              cases h103 with R h105,
              cases h105 with Q h106,
              cases h106 with h107 h108,
              rw ordered_pair_equality at h107,
              cases h107 with h108 h109,
              rw← h108 at *,
              rw← h109 at *,
              cases h108 with z h110,
              rcases h110 with ⟨ hz, h112, h113⟩,
              cases h102 with p2 h114,
              cases h114 with q2 h115,
              cases h115 with h116 h117,
              cases h117 with y h118,
              rw ordered_pair_equality at h116,
              cases h116 with h119 h120,
              rw← h119 at *,
              rw← h120 at *,
              cases h118 with hy h121,
              rcases h121 with ⟨ h122, h123, h150⟩,
              cases h113 with h151 h152,
              rw h151 at h123,
              have h130:= Phimembersinhabited M m p hm h150,
              rw h122 at h130,
              have h139:= h3,
              rw letolessthan at h139,
              cases h139 with h140 h140,
              { 
                have h142:= towerF M m hm y hy h130,
                have h141:= Iorder2 M n m hn hm h140 y hy h142,
                have h160: 𝕀 M n y ∈ 𝔽:= 
                  begin 
                    rw lessthan_definition at h141,
                    cases h141 with h144 h145,
                    rw le_definition at h144,
                    cases h144 with a h145,
                    cases h145 with b h146,
                    cases h146 with h147 h148,
                    have h149:= towerF M n hn y hy ⟨ a, h147⟩,
                    exact h149,
                  end,
                have h125:𝕀 M n z ∈ 𝔽:= 
                  begin
                    rw h123,
                    exact h160,
                  end,
              have h124:= Ioneone M n z y hn hz hy h125 h123,
              rw h124 at *,
              rw h122, 
              rw h112,
              },
              {
                rw h140 at *,
                have h161:= towerF M m hm y hy h130,
                rw sym at h123,
                have h160:= Ioneone M m y z hm hy hz h161 h123,
                rw h160 at *,
                rw h112,
                rw h122,
              },
              exact hn,
              exact hm,
            },
            {
              intros x y h130,
              cases h130 with h131 h132,
              rw fdef at h131,
              rw freverse_members at h131,
              cases h131 with P h132,
              cases h132 with Q h133,
              cases h133 with h134 h135,
              rw ordered_pair_equality at h134,
              rw h134.1 at *,
              rw h134.2 at *,
              cases h135 with y h136,
              cases h136 with hy h137,
              cases h137 with h138 h139,
              rw h138,
              rw Phi_members,
              use y,
              simp,
              cases h139 with h140 h141,
              have h142:= Phimembersinhabited M m P hm h141,
              rw h138 at *,
              exact ⟨ hy, h142⟩,
            }
          }
        end,
      set R:= range f with Rdef,
      have h205: R ⊆ Φ M n:= 
        begin
          have h311:= hmaps,
          unfold maps at h311,
          rcases h311 with ⟨h312, h313, h314, h315⟩,
          rw Rdef,
          rw subset_definition,
          intros t h300,
          rw range_axiom f hRel at h300,
          cases h300 with P h320,
          have h321: P ∈ Φ M m:= 
            begin
              rw fdef at h320,
              rw freverse_members at h320,
              cases h320 with p h321,
              cases h321 with q h322,
              cases h322 with h323 h324,
              rw ordered_pair_equality at h323,
              cases h323 with h325 h326,
              rw h325 at *,
              cases h324 with y h327,
              rcases h327 with ⟨h328, h329, h330, h331⟩,
              exact h331, 
            end,
          have h322:= h313 P t ⟨ h321, h320⟩,
          exact h322,
        end,
      have hsim: similarity M f (Φ M m) R:=
        begin
          have h501: dom f = Φ M m:=
            begin
              rw full_extensionality,
              intros t,
              rw Phi_members,
              rw domain_axiom f hRel,
              split,
              {
                intros h,
                cases h with y h504,
                rw fdef at h504,
                rw freverse_members at h504,
                cases h504 with p h505,
                cases h505 with q h506,
                cases h506 with h507 h508,
                rw ordered_pair_equality at h507,
                cases h507 with h508 h509,
                rw← h508 at *,
                rw←h509 at *,
                cases h508 with Y h510,
                rcases h510 with ⟨h511, h512, h513, h514⟩, 
                use Y,
                split,
                {
                  exact h511,
                },
                {
                  split,
                  {
                    exact h512,
                  },
                  {
                    have h515:= PhiF M m t hm h514,
                    exact cardinalsinhabited M t h515,
                  }
                }
              },
              {
                intros h,
                cases h with y h400,
                rcases h400 with ⟨ h401, h402, h403⟩,
                rw fdef,
                use 𝕀 M n y,
                rw freverse_members,
                use t, use 𝕀 M n y,
                simp,
                use y,
                simp,
                split,
                {
                  exact h401,
                },
                {
                  split,
                  {
                    exact h402,
                  },
                  {
                    rw Phi_members,
                    use y,
                    exact ⟨ h401, h402, h403⟩,
                  }
                }
              }
            end,
          have h500:= similarity_helper M f (Φ M m) (Φ M n) R hmaps honeone Rdef h205 h501,
          exact h500,
        end,
      have h201: similar M (Φ M m) R:=
        begin
          unfold similar,
          exact ⟨ f, hsim⟩,
        end,
      have h200:= xinNcx M (Φ M m),
      have h203:= Phifinite M max hmax m hm,
      have h204:= finitecardinals3 M (Φ M m) h203,
      have h202:= finitecardinals0 M (Nc M (Φ M m))(Φ M m) R h204 h200 h201,
      have h1112: ∀ (p q:M), ‹p,q› ∈ f ↔ ∃(x:M),x ∈ 𝔽 ∧ p = 𝕀 M m x ∧ q = 𝕀 M n x ∧ p ∈ Φ M m:=
        begin
          intros p q,
          split,
          {
            intros h,
            rw fdef at h,
            rw freverse_members at h,
            cases h with P h30,
            cases h30 with Q h31,
            cases h31 with h32 h33,
            rw ordered_pair_equality at h32,
            rw← h32.1 at *,
            rw← h32.2 at *,
            cases h33 with Y h34,
            rcases h34 with ⟨ hY, h35, h36, h37⟩,
            use Y,
            exact ⟨ hY, h35, h36, h37⟩,
          },
          {
            intros h,
            cases h with Y h40,
            rcases h40 with ⟨ hY, h41, h42, h43⟩,
            rw fdef,
            rw freverse_members,
            use p, use q,
            simp,
            use Y,
            exact ⟨ hY, h41, h42, h43⟩,
          }
        end, 
      have h210: Φ M n = (R ∪ Φ M n - R):= 
        begin
          rw full_extensionality,
          intros t,
          rw binary_union_axiom,
          have h800:= maximalPhi M max m hmax hm hm2,
          cases h800 with q h801,
          rcases h801 with ⟨ h802, h803, h804, h805⟩,
          have h900:= h803,
          rw Phi_members at h900,
          cases h900 with Y h901,
          rcases h901 with ⟨ hY, h903, h904⟩,
          rw  h903 at h904,
          have h600: ∀ (x:M),x∈ 𝔽 → (𝕀 M n x ∈ R ↔ x ≤ Y):=
            begin
              intros x hx,
              split,
              { --left to right,
                intros h,
                have h806:= member_subset M R (Φ M n) (𝕀 M n x) h205 h, 
                have h799:= PhiF M n (𝕀 M n x) hn h806,
                rw Rdef at h,
                rw range_axiom at h,
                cases h with p h807,
                have h808:= (h1112 p (𝕀 M n x)).1 h807,
                cases h808 with z h809,
                rcases h809 with ⟨ hz, h810, h811, h812⟩,
                have h813:= Ioneone M n x z hn hx hz h799 h811,
                rw← h813 at *,
                rw h810 at *,
                have h814:= h805 (𝕀 M m x) h812,
                rw h903 at h814,
                have h815:= Iordertwoway M m x Y hm hx hY h814,
                exact h815,
                exact hRel,
              },
              {
                intros h40,
                rw Rdef,
                rw range_axiom f hRel,
                use 𝕀 M m x,
                have h808:= h1112 (𝕀 M m x) (𝕀 M n x),
                rw h808,
                use x,
                simp,
                split,
                {
                  exact hx,
                },
                {
                  have h41: 𝕀 M m Y ∈ Φ M m:=
                    begin
                      rw← h903,
                      exact h803,
                   end,
                  have h42:= h41,
                  rw Phi_members at h42,
                  cases h42 with z h43,
                  rcases h43 with ⟨ hz, h44, h45⟩,
                  rw h903 at h802,
                  have h46:= Iorderle M Y hY x m hx hm h802 h40,
                  have h47:= le_to_inhabited M (𝕀 M m x)( 𝕀 M m Y) h46,
                  rw Phi_members,
                  use x,
                  simp,
                  exact ⟨ hx, h47⟩,
                }
              }
            end,
          split,
          {
            intros h,
            rw Phi_members at h,
            cases h with y h806,
            rcases h806 with ⟨ hy, h811, h812⟩,
            have h807: y ≤ Y ∨ Y < y:=
              begin
                have h750:= finitetrichotomy M y hy Y hY,
                cases h750 with h751 h752,
                {
                  left,
                  rw lessthan_definition at h751,
                  exact h751.1,
                },
                {
                  cases h752 with h753 h754,
                  {
                    left,
                    rw h753,
                    exact le_reflexive M Y hY,
                  },
                  {
                    right,
                    exact h754,
                  }
                }
              end,
            cases h807 with h808 h809,
            {
              left,
              rw Rdef,
              rw range_axiom,
              use 𝕀 M m y,
              rw h811 at *,
              rw fdef,
              rw freverse_members,
              use 𝕀 M m y,
              use 𝕀 M n y,
              simp,
              use y,
              simp,
              split,
              {
                exact hy,
              },
              {
                rw Phi_members,
                use y,
                simp,
                split,
                {
                  exact hy,
                },
                {  
                  rw h903 at h802,
                  have h906:= towerF M m hm Y hY h904,
                  have h910:= letolessthan M y Y hy hY,
                  rw h910 at h808,
                  cases h808 with h907 h908,
                  {
                    have h905:= Iorder M Y hY y m hy hm h906 h907,
                    have h912:= lessthan_to_inhabited M (𝕀 M m y)(𝕀 M m Y) h905,
                    exact h912,
                  },
                  {
                    rw h908 at *,
                    exact h904,
                  }
                }
              },
              exact hRel,
            },
            {
              right,
              rw h811 at *,
              rw minus_members,
              split,
              {
                rw Phi_members,
                use y,
                simp,
                exact ⟨ hy, h812⟩,
              },
              {
                intros h813,
                have h814:= h600 y hy,
                rw h814 at h813,
                have h815:= le_transitive2 M Y y Y hY hy hY h809 h813,
                have h816:= xnotlessthanx M Y hY,
                contradiction,
              }
            }
          },
          {
            intros h,
            cases h with h40 h41,
            {
              exact member_subset M R (Φ M n) t h205 h40,
            },
            {
              rw minus_members at h41,
              cases h41 with h42 h43,
              exact h42,
            }
          }
        end,
      have h206:= xinNcx M (Φ M n),
      rw le_definition,
      use R, use Φ M n,
      split,
      {
        exact h202,
      },
      {
        split,
        {
          exact h206,
        },
        {
          split,
          {
            exact h205,
          },
          {
            exact h210,
          }
        }
      }
    end

#axioms_all  

