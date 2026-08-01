import inf22
import Dedekind2
variables (M:Type) [Model M] (a b x y z u v w X R W κ μ ℓ : M)

open Model 

lemma Tmax: ∀(m n:M), MAXIMAL M m → n ∈ 𝔽  →  𝕋 M m < n → exp M n = Λ :=
  begin
    intros m n hmax hn h3,
    rw full_extensionality,
    intros x,
    have h4:= emptyset_axiom x,
    split,
    {
      intros h,
      have h5:= exp_members M n x,
      rw h5 at h,
      cases h with u h6,
      cases h6 with h7 h8,
      have h10:= finitecardinals1 M n (USC u) hn h7,
      have hu:= (uscfinite M u).1 h10,
      have h9:= finitecardinals3 M u hu,
      have h11:= xinNcx M u,
      have h12:= Tmembers M u (Nc M u) h11,
      have h13:= Tfinite M (Nc M u) h9,
      have hmaximal:= hmax,
      unfold MAXIMAL at hmaximal,
      have h14: (USC u) ∈ n ∩ (𝕋 M (Nc M u)):= 
        begin
          rw intersection_axiom,
          exact ⟨h7, h12⟩, 
        end,
      have h15:= cardinalsdisjoint M n (𝕋 M (Nc M u)) (USC u) hn h13 h14,
      rw h15 at h3,
      have h16:= Tlessthan M m (Nc M u) hmaximal.1  h9,
      rw← h16 at h3,
      have h17:= hmaximal.2 (Nc M u) h9,
      have h18:= le_transitive2 M m (Nc M u) m hmaximal.1 h9 hmaximal.1 h3 h17,
      have h19:= xnotlessthanx M m hmaximal.1,
      contradiction,
    },
    {
      intros h,
      contradiction,
    }
  end

lemma Tmax2: ∀(m n: M), MAXIMAL M m → n ∈ 𝔽 → exp M n ∈ 𝔽  → n ≤ 𝕋 M m:=
  begin
    intros m n hmax hn hn2,
    have hmax2 := hmax,
    unfold MAXIMAL at hmax2,
    cases hmax2 with hm h3,
    have h4:= Tfinite M m hm,
    have h5:= finitetrichotomy M (𝕋 M m) h4 n hn,
    cases h5 with h6 h7,
    { 
      have h10:= Tmax M m n hmax hn h6,
      have h11:= cardinalsinhabited M (exp M n) hn2,
      cases h11 with x h12,
      rw h10 at *,
      have h12:= emptyset_axiom x,
      contradiction, 
    },
    {
      cases h7 with h8 h9,
      { 
        rw letolessthan M,
        right,
        rw h8,
        exact hn,
        exact h4,
      },
      {
        rw letolessthan M,
        left,
        exact h9,
        exact hn,
        exact h4,
      }
    }
  end

lemma Tmax3: ∀(m n:M), MAXIMAL M m → n ∈ 𝔽 →  𝕋 M m < n → exp M n = Λ:=
  begin
    intros m n hmax hn h3,
    rw full_extensionality,
    intros x,
    split,
    {
      intros h,
      rw exp_members at h,
      cases h with z h2,
      cases h2 with h1 hsim,
      have h4:= exp_members2 M n z hn h1,
      set κ := Nc M z with kappadef,
      have h5:= finitecardinals1 M n (USC z) hn h1,
      have hz:= (uscfinite M z).1 h5,
      have h7:= finitecardinals3 M z hz,
      have h8:= xinNcx M z,
      rw← kappadef at h7 h8,
      have h100:= Tfinite M κ h7,
      have h9: USC z ∈ 𝕋 M κ  :=
        begin 
          have h10:= similar_reflexive M (USC z),
          have h11:= (T_members M κ (USC z)).2,
          apply h11,
          use z,
          exact ⟨ h8, h10⟩,
        end,
      have h11: n = 𝕋 M κ :=
        begin
          have h12:= (intersection_axiom n (𝕋 M κ)(USC z)).2 ⟨ h1,h9⟩,
          have h13:= cardinalsdisjoint M n (𝕋 M κ) (USC z)hn  h100  h12,
          exact h13, 
        end,  
      rw h11 at *,
      unfold MAXIMAL at hmax,
      cases hmax with hm h101,
      have h14:= (Tlessthan M  m κ hm h7).2 h3,   
      have h15:= h101 κ h7,
      have h16:= letolessthan M κ m h7 hm,
      rw h16 at h15,
      cases h15 with h17 h18,
      {
        have h19:= lessthan_transitive M m κ m hm h7 hm h14 h17,
        have h20:= xnotlessthanx M m hm,
        contradiction,
      },
      {
        rw h18 at *,
        have h20:= xnotlessthanx M m hm,
        contradiction,
      }
    },
    {
      intros h40,
      have h41:= emptyset_axiom x,
      contradiction,
    }
  end

lemma Tmax4: ∀(m n:M), MAXIMAL M m → n ∈ 𝔽 → exp M n = Λ → 𝕋 M m < n:=
  begin
    intros m n hmax hn h,
    unfold MAXIMAL at hmax,
    cases hmax with hm h3,
    have h4:= Tfinite M m hm,
    have h2:= finitetrichotomy M (𝕋 M m) h4 n hn,
    cases h2 with h5 h6,
    {
      exact h5,
    },
    {
      cases h6 with h7 h8,
      {
        rw←  h7 at *,
        have h10:= expTinF M m hm,
        rw h at *,
        have h11:= cardinalsinhabited M Λ h10,
        cases h11 with x h12,
        have h13:= emptyset_axiom x,
        contradiction,
      },
      {
        have h20:= Tonto M n m hn hm h8,
        cases h20 with k h21,
        cases h21 with hk h22,
        have h23:= expTinF M k hk,
        rw←h22 at *,
        rw h at h23,
        have h11:= cardinalsinhabited M Λ h23,
        cases h11 with x h12,
        have h13:= emptyset_axiom x,
        contradiction,
      }
    }
  end

lemma maxT: ∀(m n k:M), MAXIMAL M m → n ∈ 𝔽 → k ∈ 𝔽  →  𝕋 M k = n → n ≤  𝕋 M m:=
  begin
    intros m n k hmax hn hk hT,
    rw← hT,
    have h4:= Tlessthan M,
    unfold MAXIMAL at hmax,
    cases hmax with hm h6,
    have h7:= h6 k hk,
    have h20:= letolessthan M k m hk hm,
    rw h20 at h7,
    have h21:= Tfinite M k hk,
    have h22:= Tfinite M m hm,
    have h23:= letolessthan M (𝕋 M k)(𝕋 M m) h21 h22,
    rw h23,
    cases h7 with h9 h10,
    {
      have h11:= (h4 k m hk hm).1 h9,
      left,
      exact h11,
    },
    {
      right,
      rw h10,
    }
  end

lemma Tmax5: ∀ (m n: M), MAXIMAL M m → n ∈ 𝔽 → (n ≤ 𝕋 M m ↔ exp M n ∈ 𝔽 ):=
  begin
    intros m n hmax hn,
    have hmax2:= hmax,
    unfold MAXIMAL at hmax2,
    cases hmax2 with hm h100,
    split,
    {
      intros h3,
      have h4:= Tonto M n m hn hm,
      have h5:= Tfinite M m hm,
      have h6:= letolessthan M n (𝕋 M m) hn h5,
      rw h6 at h3,
      cases h3 with h7 h8,
      {
        have h9:= h4 h7,
        cases h9 with k h10,
        cases h10 with hk h11,
        rw h11 at *,
        exact expTinF M k hk,
      },
      {
        rw h8 at *,
        exact expTinF M m hm,
      }
    },
    {
      intros h200,
      exact Tmax2 M m n hmax hn h200
    }
  end

lemma exprec2: ∀ (m p:M), MAXIMAL M m → p ∈ 𝔽 →  ¬ p = 𝕋 M m → (exp M p) + (exp M p) ∈ 𝔽 → exp M (𝕊 p) ∈ 𝔽:=
  begin
    intros m p hmaximal hp hspecial h3,
    have h4:= cardinalsinhabited M (exp M p + exp M p) h3,
    cases h4 with x h5,
    have h6:= addition_members M (exp M p )(exp M p) x,
    rw h6 at h5,
    cases h5 with u h7,
    cases h7 with v h8,
    cases h8 with h9 h10,
    cases h10 with hu h11,
    cases h11 with hv h12,
    have h13:= finiteexp M p hp ⟨u, hu⟩,
    have h14:= mlessthanexpm M p hp ⟨u, hu⟩,
    have h15:= mplusone_le_expm M p hp ⟨u, hu⟩,
    have h16:= le_definition (𝕊 p) (exp M p),
    rw h16 at h15,
    cases h15 with a h16,
    cases h16 with b h17,
    cases h17 with h18 h19,
    have h20:= successorF M p hp ⟨ a, h18 ⟩, 
    have h21:= cardinalsinhabited M (exp M p) h13,
    cases h21 with x h22,
    have h23:= exp_inhabited M p,
    have h24:= (h23.2) ⟨ x, h22⟩, 
    cases h24 with t h25, 
    have h26:= xinNcx M t,
    have h50:= finitecardinals1 M p (USC t) hp h25,
    have h51:= (uscfinite M t).1 h50,
    have h52:= finitecardinals3 M t h51,
    have h60:= Tfinite M (Nc M t) h52,
    have h53: (USC t) ∈ 𝕋 M (Nc M t):=
      Tmembers M t (Nc M t) h26,
    have h27: p = 𝕋 M (Nc M t):=
      begin
        have h54:= cardinalsdisjoint M p (𝕋 M (Nc M t)) (USC t) hp h60,
        apply h54,
        rw intersection_axiom,
        exact ⟨h25, h53⟩, 
      end,
    have h55:= Tmax M,
    have h54:= Tsuccessor M (Nc M t) h52,
    have h56:𝕋 M (Nc M t) = p:=
      begin
        rw h27,        
      end,
    have h55:= maxT M m p (Nc M t) hmaximal hp h52 h56,
    have h57:= Tfinite M m,
    unfold MAXIMAL at hmaximal,
    cases hmaximal with hm h60,
    have h58:= Tfinite M m hm,
    have h61:= letolessthan M p (𝕋 M m) hp h58,
    rw h61 at h55,
    have h62: p < 𝕋 M m:=
      begin
        cases h55 with h63 h64,
        {
          exact h63,
        },
        {
          contradiction,
        }
      end,
    have h65: ¬ (Nc M t) = m:=
      begin
        intros h66,
        rw h66 at *,
        contradiction,
      end,
    have h67:= h60 (Nc M t) h52,
    have h68:= letolessthan M (Nc M t) m h52 hm,
    rw h68 at h67,
    have h71: (Nc M t ) < m:=
      begin
        cases h67 with h69 h70,
        {
          exact h69,
        },
        {
          contradiction,
        }
      end,
    have h72:= successorbounded M (Nc M t) m h52 hm h71,
    have h73:= cardinalsinhabited M (𝕊 (Nc M t)) h72,
    have h74:= Tsuccessor M (Nc M t) h52 h73,
    have h75: 𝕊 p = 𝕋 M (𝕊 (Nc M t)):=
      begin
        rw h27,
        rw h74,
      end,
    have h76:= expTinF M (𝕊 (Nc M t)) h72,
    rw h75,
    exact h76,
  end

theorem Vnotfinite:  𝕍 ∈ FINITE M → (Nc M 𝕍)= exp M (𝕋 M (Nc M 𝕍)):=
  begin
    intros h,
    have h1: UNENLARGEABLE M 𝕍:=
      begin
        unfold UNENLARGEABLE,
        intros t,
        have h4:= V_definition t,
        intros h5,
        apply h5,
        exact h4,
      end,
    have hmax:= unenlargeable4 M 𝕍 h h1,
    have h5:= V_definition (USC (𝕍:M)),
    have h10:= finitecardinals3 M 𝕍 h,
    have h7:= SpeckerT M 𝕍 h10,
    have h12:= unenlargeable4 M 𝕍 h h1,
    have h8:= TmlessthanM M (Nc M 𝕍),
    unfold MAXIMAL at h8,
    have h20:= h8 ⟨ h10, h12⟩,
    have h22:= Tfinite M (Nc M 𝕍) h10,
    have h23:= expT_inhabited M (Nc M 𝕍) h10,
    have h24:= expTinF M (Nc M 𝕍) h10,
    have h21:= mlessthanexpm M (Nc M 𝕍) h10,
    have h30:= exp_members M (Nc M 𝕍),
    have h31: ∀ (x y:M), x ∈ 𝕍 → y ∈ 𝕍 → ¬ ¬ (x ∈ y ∨ ¬ x ∈ y):=
      begin
        intros x y hx hy,
        exact notnotLEM (x∈ y),
      end,
    have h32:∀ (x:M), x ∈ 𝕍 → ∀ (y:M),y ∈ 𝕍 → ¬ ¬ (x ∈ y ∪ (𝕍 -y)):=
      begin
        intros x hx y hy,
        rw binary_union_axiom,
        rw minus_members,
        have h33:= V_definition x,
        intros h34,
        have h35:= h31 x y hx hy,
        apply h35,
        intros h36,
        cases h36 with h37 h38,
          { apply h34,
            left,
            exact h37,
          },
          {
            apply h34,
            right,
            exact ⟨h33, h38⟩, 
          }
      end,
    have h40:= finiteDNS M (Z_Vfinite M) 𝕍 h,
    simp_rw Z_Vfinite_members at h40,
    have h50: ¬¬ ∀ (x:M), x ∈ 𝕍 → ∀ (y:M), y ∈ 𝕍 → x ∈ (y ∪ (𝕍 -y)):=
      begin
        apply h40,
        intros x hx,
        have h41:= h32 x hx,
        have h42:= finiteDNS M (Z_Vfinite2 M x) 𝕍 h,
        simp_rw Z_Vfinite2_members at h42,
        apply h42,
        exact h41,
      end,
    have h51: SSC(𝕍) ⊆ (𝕍:M):=
      begin
        rw subset_definition,
        intros z hz,
        exact V_definition z,
      end,
    have h52: ¬¬ ∀ (y:M), y ∈ 𝕍 → ∀ (x:M), x ∈ 𝕍 → x ∈ (y ∪ (𝕍 -y)):=
      begin
        intros h53,
        apply h50,
        intros h54,
        apply h53,
        intros y hy x hx,
        exact h54 x hx y hy,
      end,
    have h55: ¬¬ ∀(y:M), y ∈ (SSC 𝕍):=
      begin
        intros h56,
        apply h52,
        intros h57,
        apply h56,
        intros y,
        have hy:= V_definition y,
        have h58:= h57 y hy,
        have h59:= ssc_definition 𝕍 y,
        rw h59,
        split,
        {
          rw subset_definition,
          intros z h60,
          exact V_definition z,
        },
        {
          rw full_extensionality,
          intros u,
          split,
          {
            intros hu,
            exact h58 u hu,
          },
          {
            intros h62,
            exact V_definition u,
          }
        }       
      end,
    have h65: ¬¬ ( 𝕍 ⊆ SSC (𝕍:M) ):=
      begin
        intros h66,
        apply h55,
        intros h67,
        apply h66,
        rw subset_definition,
        intros u hu,
        exact h67 u,
      end,
    have h68: ¬¬ (𝕍 = SSC (𝕍:M)):=
      begin
        have h69:= subsets_to_equal M 𝕍 (SSC 𝕍),
        intros h70,
        apply h65,
        intros h71,
        apply  h70,
        apply h69,
        exact h71,
        rw subset_definition,
        intros u hu,
        exact V_definition u,
      end,
    have h74: USC(𝕍) ∈ 𝕋 M (Nc M 𝕍):=
      begin
        have h75:= T_members M (Nc M 𝕍) (USC 𝕍),
        rw h75,
        use (𝕍:M),
        split,
        {
          exact xinNcx M 𝕍,
        },
        {
          exact similar_reflexive M (USC 𝕍),
        }
      end,
    have h100:= xinNcx M 𝕍,
    have h101: 𝕍 = SSC 𝕍 → SSC 𝕍 ∈ Nc M 𝕍:=
      begin
        intros h102,
        rw← h102,
        exact h100,
      end,
    have h103:= notnot_imp2way(𝕍 = SSC 𝕍)( SSC 𝕍 ∈ Nc M 𝕍),
    have h104:= double_negate (𝕍 = SSC 𝕍 → SSC 𝕍 ∈ Nc M 𝕍) h101,
    rw h103 at h104,
    have h80:= h104 h68,
    have h81: SSC 𝕍 ∈ exp M (𝕋 M (Nc M 𝕍)):=
      begin
        have h82:= exp_members2 M (𝕋 M (Nc M 𝕍)) 𝕍 ,
        apply h82,
        exact h22,
        exact h74,
      end,
    have h83: SSC 𝕍 ∈ exp M (𝕋 M (Nc M 𝕍)) → 
              SSC 𝕍 ∈ Nc M 𝕍 →
              (Nc M 𝕍) = exp M (𝕋 M (Nc M 𝕍)):=
      begin
        intros h84 h85,
        have h86:= cardinalsdisjoint M (Nc M 𝕍)  (exp M (𝕋 M (Nc M 𝕍))) (SSC 𝕍),
        apply h86,
        exact h10,
        exact h24,
        rw intersection_axiom,
        split,
        {
          exact h85,
        },
        {
          exact h84,
        }
      end,
    have h93: ¬¬ (Nc M 𝕍) = exp M (𝕋 M (Nc M 𝕍)):=
      begin
        have h94:= notnot_imp2way (SSC 𝕍 ∈ exp M (𝕋 M (Nc M 𝕍)))
             ( SSC 𝕍 ∈ Nc M 𝕍 → Nc M 𝕍 = exp M (𝕋 M (Nc M 𝕍))),
        have h95:= double_negate (SSC 𝕍 ∈ exp M (𝕋 M (Nc M 𝕍)) → SSC 𝕍 ∈ Nc M 𝕍 → Nc M 𝕍 = exp M (𝕋 M (Nc M 𝕍))) h83,
        rw h94 at h95,
        have h97:= double_negate (SSC 𝕍 ∈ exp M (𝕋 M (Nc M 𝕍))) h81,
        have h96:= h95 h97,
        have h98:= notnot_imp2way (SSC 𝕍 ∈ Nc M 𝕍)( Nc M 𝕍 = exp M (𝕋 M (Nc M 𝕍))),
        rw h98 at h96,
        apply h96,
        exact h80,
      end,
    have h110:= FregeNdecidable M,
    rw decidable_members at h110,
    have h111:= h110 (Nc M 𝕍) (exp M (𝕋 M (Nc M 𝕍))) ⟨ h10, h24⟩,
    cases h111 with h112 h113,
    {
      exact h112,
    },
    {
      contradiction,
    }    
  end 

lemma smallsubset: ∀(y:M), y ∈ FSFS M → ∀ (x:M), x⊆y → y = (x ∪ (y-x)) → x ∈ FSFS M:=
  begin
    intros y hy x hx hsep,
    rw FSFS_members M x,
    rw FSFS_members M at hy,
    cases hy with hy1 hy2,
    have h3:= separablefinite M y hy1 x hx,
    unfold separable_subset at h3,
    have h4:= h3 ⟨ hx, hsep ⟩,
    split,
    {
      exact h4,
    },
    {
      rw subset_definition,
      intros t ht,
      have h5:= member_subset M x y t hx ht,
      have h6:= member_subset M y (FINITE M) t hy2 h5,
      exact h6,
    }
  end

lemma lessthansmall: ∀(k:M),k ∈ 𝔽  → ∀ (n:M), n ∈ 𝔽 → k ∈ SMALL M → n ≤  k → n ∈ SMALL M:=
  begin
    intros k hk n hn hksmall hnk,
    rw small_members M,
    split,
    {
      exact hn,
    },
    {
      have h4:= le2 M n k hn hk,
      rw small_members M at hksmall,
      cases hksmall with hk2 h5,
      cases h5 with x h6,
      cases h6 with hx h7,
      have h8:= h4 ⟨ x, hx⟩,  
      have h9:= h8.1 hnk x hx,
      cases h9 with y h10,
      cases h10 with hy h11,
      use y,
      split,
      {
        exact hy,
      },
      {
        have h12:= smallsubset M x h7 y h11.1 h11.2,
        exact h12,
      }
    }
  end 

lemma smallbound_helper: ∀ (m:M), MAXIMAL M m → (exp M (𝕋 M m)) ∈ SMALL M:=
  begin
    intros m hmax,
    unfold MAXIMAL at hmax,
    cases hmax with hm h4,
    have h5:= cardinalsinhabited M m hm,
    cases h5 with U hU,
    have h6:= Tmembers M U m hU,
    have hT:= Tfinite M m hm,
    have h7:= exp_members2 M (𝕋 M m) U hT h6,
    have h8:= expTinF M m hm, 
    have h9:= finitecardinals1 M  (exp M (𝕋 M m)) (SSC U) h8 h7,
    rw small_members,
    split,
    {
      exact h8,
    },
    {
      use (SSC U),
      split,
      {
        exact h7,
      },
      {
        rw FSFS_members,
        split,
        {
          exact h9,
        },
        {
          rw subset_definition,
          intros t ht,
          rw ssc_members at ht,
          have hUfinite:= finitecardinals1 M m U hm hU,
          have h10:= separablefinite M U hUfinite t ht.1,
          apply h10,
          unfold separable_subset,
          cases ht with h20 h21,
          split,
          {
            exact h20,
          },
          {
            rw full_extensionality,
            intros z,
            rw binary_union_axiom,
            rw minus_members M,
            have h24:= h21 z,
            split,
            {
              intros hz,
              have h25:= h24 hz,
              cases h25 with h26 h27,
              {
                left,
                exact h26,
              },
              {
                right,
                exact ⟨ hz, h27⟩,
              }
            },
            {
              intros h28,
              cases h28 with h29 h30,
              {
                exact member_subset M t U z h20 h29,
              },
              {
                exact h30.1,
              }
            }
          }
        }
      }
    }
  end

lemma finiteunion2: ∀ (X a b:M), X ∈ FINITE M → a ∈ FINITE M → b ∈ FINITE M → a ⊆ X → b ⊆ X → a ∪ b ∈ FINITE M:=
  begin
    intros X a b hX ha hb h3 h4,
    have h5:=finiteseparable M X a hX ha h3,
    have h6:=finiteseparable M X b hX hb h4,
    have h7:= separablefinite M X hX (a ∪ b),
    apply h7,
    rw subset_definition,
    intros z h8,
    rw binary_union_axiom at h8,
    cases h8 with h9 h10,
    {
      exact member_subset M a X z h3 h9,
    },
    {
      exact member_subset M b X z h4 h10,
    },
    {
      unfold separable_subset,
      split,
      {
        rw subset_definition,
        intros z h10,
        rw binary_union_axiom at h10,
        cases h10 with h11 h12,
        {
          exact member_subset M a X z h3 h11,
        },
        { 
          exact member_subset M b X z h4 h12,
        }
      },
      {
        rw full_extensionality,
        intros z,
        rw binary_union_axiom,
        rw minus_members,
        rw  binary_union_axiom,
        rw full_extensionality at h5 h6,
        specialize h5 z,
        specialize h6 z,
        rw binary_union_axiom at h5 h6,
        rw minus_members at h5 h6,
        split,
        {
          intros hz,
          have hz2:= hz,
          have hz3:= hz,
          rw h5 at hz2,
          rw h6 at hz3,
          cases hz2 with h20 h21,
          {
            cases hz3 with h22 h23,
            {
              right,
              split,
              {
                exact h20.1,
              },
              {
                intros h25,
                cases h25 with h26 h27,
                {
                  exact h20.2 h26,
                },
                {
                  cases h22 with h28 h29,
                  contradiction,
                }
              }
            },
            {
              left, right,
              exact h23,
            }
          },
          {
            left,left,
            exact h21,
          }
        },
        {
          intros h30,
          cases h30 with h31 h32,
          {
            cases h31 with h32 h33,
            {
              exact member_subset M a X z h3 h32,
            },
            {
              exact member_subset M b X z h4 h33,
            }
          },
          {
            exact h32.1,
          }
        }
      }
    }
  end

lemma finiteunion3: ∀ (X:M),X ∈ FINITE M → ∀(y:M), y ∈ FINITE M → y ⊆ SSC X → union y ∈ FINITE M:=
  begin
    intros X hX,
    have h4: union Λ = (Λ:M) :=
      begin
        rw full_extensionality,
        intros x,
        rw union_axiom x Λ,
        split,
        {
          intros h6,
          cases h6 with z h7,
          cases h7 with h9 h10,
          have h11:= emptyset_axiom z,
          contradiction,
        },
        {
          intros h20,
          have h21:= emptyset_axiom x,
          contradiction,
        }
      end,
    have base: Λ ∈ W_finiteunion3 M X,
      begin
        rw W_finiteunion3_members,
        repeat{split},
        {
          exact lambda_finite M,
        },
        {
          rw subset_definition,
          intros  h,
          rw h4,
          exact lambda_finite M,
        },
      end,
    have step: ∀(y c:M), (¬ c ∈ y ∧ y ∈ W_finiteunion3 M X)→ y ∪ single c ∈ W_finiteunion3 M X:=
      begin
        intros y c h400,
        cases h400 with hc h4,
        have h100: union (y ∪ single c) = ((union y)  ∪ c):= 
          begin
            rw full_extensionality,
            intros x,
            split,
            {
              intros h5,
              rw union_axiom at h5,
              cases h5 with z h6,
              cases h6 with h7 hx,
              rw binary_union_axiom,
              rw binary_union_axiom at h7,
              cases h7 with h8 h9,
              {
                left,
                rw union_axiom,
                use z,
                exact ⟨ h8, hx⟩,
              },
              {
                right,
                rw singleton1 at h9,
                rw h9 at *,
                exact hx,
              }
            },
            {
              intros h20,
              rw binary_union_axiom at h20,
              rw union_axiom,
              cases h20 with h21 h22,
              {
                rw union_axiom at h21,
                cases h21 with z h23,
                use z,
                rw binary_union_axiom,
                cases h23 with h24 h25,
                split,
                {
                  left,
                  exact h24,
                },
                {
                  exact h25,
                }
              },
              {
                use c,
                split,
                rw binary_union_axiom,
                right,
                rw singleton1,
                exact h22,
              }
            }
          end,
        rw W_finiteunion3_members at h4,
        cases h4 with hy h5,
        rw W_finiteunion3_members,
        split,
        {
          have h6:= finite_adjoin M y c ⟨ hy, hc⟩,
          exact h6,
        },
        { 
          intros h7,
          have h101: c ∈ SSC X:=
            begin
              rw subset_definition at h7,
              apply h7,
              rw binary_union_axiom,
              right,
              rw singleton1,
            end,
          have h90:= finitepowerset M X hX,
          have h91: y ⊆ SSC X:=
            begin
              rw subset_definition,
              intros  z hz,
              rw subset_definition at h7,
              apply h7,
              rw binary_union_axiom,
              left,
              exact hz,
            end,
          rw h100,
          have h92:= h5 h91,
          have h93:= separablefinite M X hX c,
          rw ssc_members at h101,
          have h94: c ∈ FINITE M:=
            begin
              apply h93,
              exact h101.1,
              cases h101 with h102 h103,
              unfold separable_subset,
              split,
              {
                exact h102,
              },
              {
                rw full_extensionality,
                simp_rw binary_union_axiom,
                intros x,
                specialize h103 x,
                split,
                {
                  intros hx,
                  have h104:= h103 hx,
                  cases h104 with h105 h106,
                  {
                    left,
                    exact h105,
                  },
                  {
                    right,
                    rw minus_members,
                    exact ⟨ hx, h106⟩,
                  }
                },
                {
                  intros h106,
                  cases h106 with h107 h108,
                  {
                    exact member_subset M c X x h102 h107,
                  },
                  {
                    rw minus_members at h108,
                    exact h108.1,
                  }
                }
              }
            end,
          have h120: union y ⊆ X:=
            begin
              rw subset_definition,
              intros z hz,
              rw union_axiom at hz,
              cases hz with t h121,
              have h122:= member_subset M y (SSC X) t h91 h121.1,
              rw ssc_members at h122,
              cases h122 with h123 h124,
              have h125:= member_subset M t X z h123 h121.2,
              exact h125,
            end,
          have h110:= finiteunion2 M X (union y) c hX h92 h94 h120 h101.1,
          exact h110,
        }
      end,
    intros y hy,
    have h200:= (finite_members M y).1 hy (W_finiteunion3 M X) ⟨ base, step⟩,
    rw W_finiteunion3_members at h200,
    exact h200.2,
  end

lemma unionssc: ∀(x y:M), x ∈ FINITE M → y ∈ SSC(SSC x) → union y ∈ SSC x:=
  begin
    intros x y hxfinite hy,
    have h3: union y ⊆ x :=
      begin
        rw subset_definition,
        rw ssc_members at hy,
        cases hy with h4 h5,
        intros t ht,
        rw union_axiom at ht,
        cases ht with z h6,
        cases h6 with hz ht,
        have h7:= member_subset M y (SSC x) z h4 hz,
        rw ssc_members at h7,
        cases h7 with h8 h9,
        exact member_subset M z x t h8 ht,
      end,
    have h10:= finitepowerset M x hxfinite,
    rw ssc_members at hy,
    cases hy with h30 h31,
    have h13: separable_subset M y (SSC x):=
      begin
        unfold separable_subset,
        split,
        {
          exact h30,
        },
        {
          rw full_extensionality,
          intros t,
          specialize h31 t,
          rw binary_union_axiom,
          rw minus_members,
          split,
          {
            intros ht,
            have h32:= h31 ht,
            cases h32 with h33 h34,
            {
              left, 
              exact h33,
            },
            {
              right,
              exact ⟨ ht, h34⟩,
            }
          },
          {
            intros h35,
            cases h35 with h36 h37,
            {
              exact member_subset M y (SSC x) t h30 h36,
            },
            {
              exact h37.1,
            }
          }
        }
      end,
    have hyfinite:= separablefinite M (SSC x) h10 y h30 h13,
    have h20:= finiteunion3 M x hxfinite y hyfinite h30,
    have h21:= finiteseparable M x (union y) hxfinite h20 h3,
    rw ssc_members,
    split,
    {
      exact h3,
    },
    {
      intros t ht,
      rw full_extensionality at h21,
      specialize h21 t,
      rw h21 at ht,
      rw binary_union_axiom at ht,
      rw minus_members at ht,
      cases ht with h22 h23,
      {
        right,
        exact h22.2,
      },
      {
        left,
        exact h23,
      }
    }
  end   


lemma oneout: ∀(X c:M), X ∈ FINITE M →  c ∈ X → X- single c ∈ FINITE M:=
  begin
    intros X c hX hc,
    have h3: X- single c ⊆ X:=
      begin
        rw subset_definition,
        intros z h4,
        rw minus_members at h4,
        exact h4.1,
      end,
    have h20:= finite_decidable2 M X,
    have h5: separable_subset M (X - single c) X :=
      begin
        unfold separable_subset,
        split,
        {
          exact h3,
        },
        {
          rw full_extensionality,
          intros x,
          have h21:= h20 c x hX hc,
          split,
          {
            intro hx,
            have h22:= h21 hx,
            rw binary_union_axiom,
            cases h22 with h23 h24,
            {
              rw h23 at *,
              right,
              rw minus_members,
              split,
              {
                exact hc,
              },
              {
                rw minus_members,
                intros h25,
                rw singleton1 at h25,
                cases h25 with h26 h27,
                simp at h27,
                exact h27,
              }
            },
            {
              left,
              rw minus_members,
              rw singleton1,
              split,
              {
                exact hx,
              },
              {
                intros h28,
                rw h28 at *,
                contradiction,
              }
            }
          },
          {
            intros h30,
            rw binary_union_axiom at h30,
            cases h30 with h31 h32,
            {
              rw minus_members at h31,
              exact h31.1,
            },
            {
              rw minus_members at h32,
              exact h32.1,
            }
          }
        }
      end,
    have h8:= separablefinite M X hX (X - single c) h3 h5,
    exact h8,
  end 

theorem dedekind3:∀(X:M), X ∈ FINITE M → ∀ (Y f:M),Y ∈ FINITE M → maps M f X Y → onto M  f X Y →
dom f = X → Nc M Y ≤ Nc M X:= 
  begin
    have base: Λ ∈ W_dedekind3 M:=
      begin
        rw W_dedekind3_members,
        split,
        {
          exact lambda_finite M,
        },
        {
          intros Y f hY hmaps honto hdom,
          unfold maps at hmaps,
          unfold onto at honto,
          cases hmaps with hrel h10,
          cases h10 with h11 h12,
          cases h12 with h13 h14,
          have h4:= domain_axiom f hrel,
          rw hdom at *,
          have h5: Y = Λ:=
            begin
              rw full_extensionality,
              intros y,
              split,
              {
                intros hy,
                have h6:= honto y hy,
                cases h6 with x h7,
                cases h7 with h8 h9,
                have h10:= emptyset_axiom x,
                contradiction,
              },
              {
                intros h11,
                have h12:= emptyset_axiom y,
                contradiction,
              }
            end,
          rw h5 at *,
          have h15:= le_reflexive M (Nc M Λ),
          apply h15,
          have h16:= finitecardinals3 M Λ (lambda_finite M),
          exact h16,
        }
      end,
    have step: ∀ (X a : M), ¬a ∈ X ∧ X ∈ W_dedekind3 M → (X ∪ single a) ∈ W_dedekind3 M :=
      begin
        intros X c h20,
        cases h20 with hc h21,
        rw W_dedekind3_members M at h21,
        cases h21 with hX h22,
        rw W_dedekind3_members,
        split,
        {
          exact finite_adjoin M X c ⟨hX, hc⟩,
        },
        {
          intros Y f hY hmaps honto hdom,
          have hmaps2:= hmaps,
          unfold maps at hmaps2,
          cases hmaps2 with hrel h30,
          cases h30 with h31 h32,
          cases h32 with h33 h34,
          have h35:= h34 c,
          have h36: c ∈ X ∪ single c:=
            begin
              rw binary_union_axiom,
              right,
              rw singleton1,
            end,
          have h37:= h35 h36,
          cases h37 with fc h38,
          cases h38 with hfc h39,
          set g:= f ∩ (X× Y) with gdef,
           -- g is the restriction of f to X
          have hrelg: Rel g:=
            begin
              rw Rel_definition,
              intros z hz,
              rw gdef at hz,
              rw intersection_axiom at hz,
              cases hz with h200 h201,
              have hrel2:= hrel,
              rw Rel_definition at hrel2,
              exact hrel2 z h200,
            end,
          have hmaps3: maps M g X Y:=
            begin
              unfold maps,
              repeat{split},
              { 
                exact hrelg,
              },
              {
                intros x y h60,
                cases h60 with hx h61,
                have h65: x ∈ X ∪ single c:=
                begin
                  rw binary_union_axiom,
                  left,
                  exact hx,
                end,
                apply h31 x y,
                split,
                {
                  rw binary_union_axiom,
                  left,
                  exact hx,
                },
                { 
                  rw gdef at h61,
                  rw intersection_axiom at h61,
                  exact h61.1,
                }
              },
              {
                intros x y z h60,
                cases h60 with h61 h62,
                cases h62 with h63 h64,
                rw gdef at h63,
                rw intersection_axiom at h63,
                rw gdef at h64,
                rw intersection_axiom at h64,
                have h65: x ∈ X ∪ single c:=
                begin
                  rw binary_union_axiom,
                  left,
                  exact h61,
                end,
                have h66:= h33 x y z ⟨ h65,h63.1, h64.1⟩,
                exact h66, 
              },
              {
                intros x hx,
                have h65: x ∈ X ∪ single c:=
                begin
                  rw binary_union_axiom,
                  left,
                  exact hx,
                end,
                have h70:= h34 x h65,
                cases h70 with y h71,
                cases h71 with hy h72,
                use y,
                split,
                {
                  exact hy,
                },
                {
                  rw gdef,
                  rw intersection_axiom,
                  split,
                  {
                    exact h72,
                  },
                  {
                    rw product_axiom,
                    use x, use y,
                    simp,
                    exact ⟨ hx, hy⟩,
                  }
                }
              }
            end,
          have h40:= decidable_image M X Y g hX hY hmaps3,
          have h80: dom g = X:=
            begin
              rw full_extensionality,
              intros t,
              rw domain_axiom,
              split,
              {
                intros h81,
                cases h81 with y h82,
                rw gdef at h82,
                rw intersection_axiom at h82,
                cases h82 with h83 h84,
                rw product_axiom at h84,
                cases h84 with a h85,
                cases h85 with b h86,
                cases h86 with h87 h88,
                rw ordered_pair_equality at h88,
                cases h88 with h89 h90,
                cases h90 with h91 h92,
                rw h91 at *,
                rw h92 at *,
                exact h87,
              },
              {
                intros ht,
                have h91: t ∈ X ∪ single c:=
                  begin
                    rw binary_union_axiom,
                    left,
                    exact ht,
                  end,
                have h90:= h34 t h91,
                cases h90 with y h92,
                cases h92 with h93 h94,
                use y,
                rw gdef,
                rw intersection_axiom,
                split,
                {
                  exact h94,
                },
                {
                  rw product_axiom,
                  use t,use y,
                  simp,
                  exact ⟨ ht, h93⟩, 
                }
              },
              {
                exact hrelg,
              } 
            end,
          have h101:= h40 h80 hrelg fc hfc,
          cases h101 with h130 h131,
          {
            cases h130 with xprime h150,
            have hgonto:  onto M g X Y:=
              begin
                unfold onto,
                intros y hy,
                unfold onto at honto,
                have h132:= honto y hy,
                cases h132 with x h133,
                cases h133 with h134 h135,
                rw binary_union_axiom at h134,
                cases h134 with h136 h137,
                use x,
                rw gdef,
                split,
                {
                  exact h136,
                },
                {
                  rw intersection_axiom,
                  split,
                  {
                    exact h135,
                  },
                  {
                    rw product_axiom,
                    use x, use y, simp,
                    exact ⟨ h136, hy⟩, 
                  }
                },
                {
                  rw singleton1 at h137,
                  rw h137 at *,
                  have h138:= h33 c y fc,
                  have h139: c ∈ X ∪ single c:= 
                    begin
                      rw binary_union_axiom,
                      right,
                      rw singleton1,
                    end,
                  have h140:= h138 ⟨ h139, h135, h39⟩,
                  rw h140 at *,
                  use xprime,
                  exact h150,
                }
              end,
            have h200:= h22 Y g hY hmaps3 hgonto h80,
            have h201: Nc M X ∈ 𝔽 :=
              finitecardinals3 M X hX,
            have h223:= xinNcx M X,
            have h202: ∃ (u : M), u ∈ 𝕊 (Nc M X):=
              begin
                use X ∪ single c,
                have h203:= successor_members M (Nc M X) (X ∪ single c),
                rw h203,
                use X, use c,
                simp,
                exact ⟨ h223, hc⟩,
              end,
            have h210:= lessthansuccessor M (Nc M X) h201 h202,
            have h211:= Ncsuccessor M X c hc,
            have h213:= finitecardinals3 M X hX,
            have h214:= finitecardinals3 M Y hY,
            have h215:= successorF M (Nc M X) h213 h202,
            have h212:= le_transitive3 M (Nc M Y) (Nc M X) (𝕊 (Nc M X)) h214 h213 h215 h200 h210,
            rw← h211 at h212,
            rw letolessthan,
            left,
            exact h212,
            exact h214,
            rw h211,
            exact successorF M (Nc M X) h213 h202,
          },
          {
            have h300: onto M g X (Y - single fc):=
              begin
                unfold onto,
                intros y hy,
                unfold onto at honto,
                rw minus_members at hy,
                cases hy with hy2 hy3,
                have h301:= honto y hy2,
                cases h301 with x h302,
                use x,
                cases h302 with h303 h304,
                rw binary_union_axiom at h303,
                cases h303 with h305 h306,
                split,
                {
                  exact h305,
                },
                {
                  rw gdef,
                  rw intersection_axiom,
                  split,
                  {
                    exact h304,
                  },
                  {
                    rw product_axiom,
                    use x, use y,
                    simp,
                    exact ⟨ h305, hy2⟩,
                  }
                },
                {
                  rw singleton1 at h306,
                  rw h306 at *,
                  rw singleton1 at hy3,
                  have h307:= h33 c y fc,
                  have h308: y = fc:=
                    begin
                      apply h307,
                      exact ⟨ h36, h304, h39⟩,
                    end,
                  rw h308 at *,
                  contradiction,
                }
              end,
            have h309:= oneout M Y fc hY hfc,
            have h310:= h22 (Y- single fc) g h309,
            have h311: maps M g X (Y - single fc) :=
              begin
                unfold maps at hmaps3,
                cases hmaps3 with h311 h312,
                cases h312 with h313 h314,
                cases h314 with h315 h316,
                unfold maps,
                repeat{split},
                {
                  exact hrelg,
                },
                {
                  intros x y h317,
                  cases h317 with hx h318,
                  rw gdef at h318,
                  rw intersection_axiom at h318,
                  cases h318 with h319 h320,
                  rw product_axiom at h320,
                  cases h320 with a h321,
                  cases h321 with b h322,
                  rw ordered_pair_equality at h322,
                  cases h322 with h323 h324,
                  cases h324 with h325 h326,
                  rw h326.1 at *,
                  rw h326.2 at *,
                  rw minus_members,
                  rw singleton1,
                  split,
                  {
                    exact h325,
                  },
                  {
                    intros h320,
                    apply h131,
                    rw h320 at *,
                    use x,
                    rw h326.1,
                    split,
                    {
                      exact hx,
                    },
                    {
                      rw gdef,
                      rw intersection_axiom,
                      split,
                      {
                        exact h319,
                      },
                      {
                        rw product_axiom,
                        use a, use fc,
                        simp,
                        exact ⟨ hx, h325⟩,
                      }
                    }
                  }
                },
                {
                  exact h315,
                },
                {
                  intros x hx,
                  have h317:= h316 x hx,
                  cases h317 with y h318,
                  use y,
                  cases h318 with hy h319,
                  split,
                  {
                    have h320: ¬ y = fc:=
                      begin
                        intros h321,
                        apply h131,
                        use x,
                        rw h321 at *,
                        exact ⟨ hx, h319⟩,
                      end,
                    rw minus_members,
                    rw singleton1,
                    exact ⟨ hy, h320⟩, 
                  },
                  {
                    exact h319,
                  }
                }
              end,
            have h330:= h310 h311 h300 h80,
            have h331:= finitedecidable M Y hY,
            rw decidable_members M at h331,
            have h332: (Y - single fc) ∪ single fc = Y:=
              begin
                rw full_extensionality,
                intros x,
                split,
                {
                  intros h333,
                  rw binary_union_axiom at h333,
                  rw minus_members at h333,
                  cases h333 with h334 h335,
                  {
                    exact h334.1,
                  },
                  {
                    rw singleton1 at h335,
                    rw h335 at *,
                    exact hfc,
                  }
                },
                {
                  intros hx,
                  rw binary_union_axiom,
                  rw minus_members,
                  rw singleton1,
                  have h336:= h331 x fc ⟨ hx, hfc⟩,
                  cases h336 with h337 h338,
                  {
                    right,
                    exact h337,
                  },
                  {
                    left,
                    exact ⟨ hx, h338⟩,
                  }
                }
              end,
            have h339: ∃(u:M), u ∈ 𝕊 (Nc M X):=
              begin
                use X ∪ single c,
                rw successor_members, 
                use X, use c, simp,
                split,
                {
                  exact xinNcx M X,
                },
                {
                  exact hc,
                }
              end,
            have h340: ∃(u:M), u ∈ 𝕊 (Nc M (Y- single fc)):=
              begin
                use (Y - single fc) ∪ single fc,
                rw successor_members, 
                use Y-single fc, use fc, 
                repeat{split},
                {
                  exact xinNcx M (Y-single fc),
                },
                {
                  intros h341,
                  rw minus_members at h341,
                  rw singleton1 at h341,
                  cases h341 with h342 h343,
                  contradiction,
                },
              end,
            have h344:= finitecardinals3 M X hX,
            have h345:= successorF M (Nc M X) h344 h339,
            have h346:= finitecardinals3 M (Y - single fc) h309,
            have h347:= successorF M (Nc M (Y-single fc)) h346 h340,
            have h360:= ordersuccessor M (Nc M (Y - single fc)) (Nc M X) h346 h344 h339,
            have h361:= h360.1 h330,
            have h368:= xinNcx M Y,
            have h369:= Ncsuccessor M X c hc,
            have h362:𝕊 (Nc M (Y-single fc)) = Nc M Y:=
              begin
                have h363:= xinNcx M (Y-single fc),
                have h364: (Y-single fc) ∪ (single fc) ∈ 𝕊 (Nc M (Y-single fc)):=
                  begin
                    rw successor_members,
                    use Y- single fc,
                    use fc,
                    repeat{split},
                    {
                      exact h363,
                    },
                    {
                      intros h365,
                      rw minus_members at h365,
                      rw singleton1 at h365,
                      cases h365 with h366 h367,
                      contradiction,
                    }
                  end,
                rw h332 at h364,
                have h380:= finitecardinals3 M Y hY,
                have h365:= cardinalsdisjoint M (𝕊 (Nc M (Y - single fc)))  (Nc M Y) Y h347 h380,
                apply h365,
                rw intersection_axiom,
                exact ⟨ h364, h368⟩,
              end,
            rw h362 at h361,
            rw← h369 at h361,
            exact h361,
          }
        }
      end,
    intros X hX,
    have h400:= finite_members M X,
    have h401:= h400.1 hX (W_dedekind3 M) ⟨ base, step⟩,
    rw W_dedekind3_members at h401,
    exact h401.2,
  end

  #axioms_all  -- This file is clean. 