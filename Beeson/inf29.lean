import inf28

variables (M:Type) [Model M] (a b x y z u v w X R W κ μ ℓ : M)

open Model 

lemma PhiNC: ∀ (n:M), n ∈ NC M → φ M n ⊆  NC M:=
  begin
    intros n hn,
    rw subset_definition,
    intros z hz,
    rw phi_members at hz,
    cases hz with y h5,
    rcases h5 with ⟨ hy, h7, h8⟩,
    rw h7 at h8,
    have h10:= towerENC M n hn y hy h8,
    rw h7,
    exact h10,
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

lemma towerorder2: ∀ (m y z), m ∈ NC M → y ∈ 𝔽 → z ∈ 𝔽 →
tower M m y ⪯ tower M m z → y ≤ z:=
  begin
    intros m y z hm hy hz h3,
    have h3copy:= h3,
    rw ledot_definition at h3,
    cases h3 with a h4,
    cases h4 with b h5,
    rcases h5 with ⟨ h60, h61, h62⟩,
    have h20: ∃ (u:M), u ∈ tower M m z:= ⟨ b, h61⟩,
    have h21: ∃ (u:M), u ∈ tower M m y:= ⟨ a, h60⟩, 
    have h10:= towerinNC M m hm y hy h21,
    have h4: z < y ∨ y ≤ z:=
      begin
        have h20:= finitetrichotomy M z hz y hy,
        cases h20 with h24 h25,
        {
          left,
          exact h24,
        },
        {
          cases h25 with h26 h27,
          {
            rw h26 at *,
            right,
            exact le_reflexive M y hy,
          },
          {
            right,
            rw letolessthan M y z hy hz,
            left,
            exact h27,
          }
        }
      end,
    cases h4 with h5 h6,
    {
      have h7:= towerorder M y hy z m hz hm h10 h5,
      rw lessdot_definition at h7,
      rcases h7 with ⟨ h8, h9, h30⟩,
      contradiction,
    },
    { 
      exact h6,
    }
  end

lemma nogaps: ∀(m p:M), m ∈ NC M → zero ⋖ m → p ∈ NC M → exp2 M p ∈ φ M m → p ∈ φ M m → z ∈ φ M m → z ⪯ exp2 M p → ¬(z = exp2 M p) → z ⪯ p:=
  begin
    intros m p hm hm0 hp hp2 hp3 hz h4 h5,
    have hp4:= hp3,
    rw phi_members at hp3,
    cases hp3 with y h6,
    rcases h6 with ⟨hy, h7, h8⟩,
    have hp2copy := hp2,
    rw phi_members at hp2,
    have h61:= h8,
    rw h7 at h61,
    have h60:= ylessdottower M y hy m hm hm0 h61,
    have h63:= hp,
    rw h7 at h63,
    have h62:= noinsertionsNC M y (tower M m y) (FtoNC M y hy) h63 h60,
    have h64: ∃ (u:M), u ∈ 𝕊 y :=
      begin
        have h65:= h62,
        rw ledot_definition at h65,
        cases h65 with A h66,
        cases h66 with B h67,
        rcases h67 with ⟨ h68, h69, h70⟩,
        use A,
        exact h68,
      end, 
    have hsy:= successorF M y hy h64,
    have h40:= PhiNC M m hm,
    have h41:= member_subset M (φ M m)(NC M) z h40 hz,
    have h30:= sixpointfour2 M m z hm h41 hz,
    have h9:= towerE_recursion_equation M m y hy h64,
    rw phi_members at hz,
    cases hz with u h80,
    rcases h80 with ⟨hu, h81, h82⟩,
    have h84: tower M m u ⪯ tower M m (𝕊 y):=
      begin
        rw h9,
        rw← h81,
        rw← h7,
        exact h4,
      end,
    have h83: u ≤ 𝕊 y:= 
      begin
        have h300:= towerorder2 M m u (𝕊 y) hm hu hsy h84,
        exact h300,
      end,
    have h84: ¬ u = 𝕊 y:=
      begin
        intros h,
        apply h5,
        rw h81,
        rw h7,
        rw ←h9,
        rw h,
      end,
    have h85: u ≤ y:=
      begin
        have h86:= lessthansuccessor2 M u y hu hy h83,
        cases h86 with h87 h88,
        exact h87,
        contradiction,
      end, 
    have h90:= (letolessthan M u y hu hy).1 h85,
    cases h90 with h91 h92,
    {
      have h86:=towerorder M y hy u m hu hm h63 h91,
      rw← h81 at h86,
      rw← h7 at h86,
      rw lessdot_definition at h86,
      exact h86.1,
    },
    {
      rw h92 at *,
      rw h81,
      rw h7,
      exact ledotreflexive M (tower M m y) h63,
    }
  end

lemma exp2lambda: exp2 M (Λ:M) = Λ:=
  begin
    rw full_extensionality,
    intros t,
    split,
    {
      intros h,
      rw exp2_members at h,
      cases h with a h2,
      cases h2 with h3 h4,
      have h5:= emptyset_axiom (USC a),
      contradiction,
    },
    {
      intros h,
      have h8:= emptyset_axiom t,
      contradiction,
    }
  end

lemma sixpointtwo2_helper:  ∀ (m:M), m ∈ NC M → exp2 M m= Λ → ∀(p:M), p ∈ 𝔽 → (𝕊 p ∈ 𝔽  →  tower M m (𝕊 p) = Λ):= 
  assume m hm hexpm,  
  begin
    have base: zero ∈  Z_sixpointtwo2 M m:=
      begin
        rw Z_sixpointtwo2_members M m, 
        have h3:= towerE_base_equation M m,
        have h4:= towerE_recursion_equation M m zero (zeroF M),
        rw h3 at *,
        rw hexpm at *,
        split,
        {
          exact zeroF M,
        },
        { intros h10,
          apply h4,
          rw← one_definition ,
          exact cardinalsinhabited2 M one (oneNC M),
        }
      end,
    have step: ∀(p:M), p ∈ Z_sixpointtwo2 M m → (∃(v : M), v ∈ 𝕊 p)→  𝕊 p ∈ Z_sixpointtwo2 M m:=
      begin
        intros p h10 h20,
        rw Z_sixpointtwo2_members M m  at h10,
        rw Z_sixpointtwo2_members M m,
        cases h10 with hp h12,
        have h21:= successorF M p hp h20,
        have h22:= h12 h21,
        have h13:= towerE_recursion_equation M m (𝕊 p )  h21,
        simp_rw h22 at *,
        have h14:= exp2lambda M,
        rw h14 at *,
        split,
        {
          exact h21,
        },
        {
          intros h22,
          have h23:= cardinalsinhabited M (𝕊 (𝕊 p)) h22,
          exact h13 h23,
        }
      end,
    intros p hp,
    rw F_members at hp,
    specialize hp (Z_sixpointtwo2 M m),
    have h200:= hp ⟨ base, step⟩, 
    rw Z_sixpointtwo2_members M m at h200,
    exact h200.2,
  end  

lemma sixpointtwo2: ∀ (m:M), m ∈ NC M → exp2 M m= Λ → φ M m = single m:=
  begin
    intros m hm h3,
    rw full_extensionality,
    intros n,
    split,
    {
      intros h4,
      have h4copy := h4,
      rw phi_members at h4,
      cases h4 with k h5,
      cases h5 with hk h21,
      cases h21 with h22 h23,
      have h23copy:= h23,
      cases h23copy with b h24,
      rw h22 at h23,
      rw singleton1,
      
      have h40:= towerENC M m hm k hk h23,
      have hn:= h40,
      rw← h22 at hn,
      have h6:= sixpointfour2 M m n hm hn h4copy,
      -- cases h5 with k h8,
      -- cases h8 with hk h7,
    
      have h8: k = zero ∨ ¬ k = zero:=
        begin
          have h9:= FregeNdecidable M,
          rw decidable_members M at h9,
          have h10:= h9 k zero ⟨ hk, zeroF M⟩,
          exact h10,
        end,
      cases h8 with h11 h12,
      {
        rw h11 at *,
        have h12:=towerE_base_equation M m,
        rw h12 at *,
        exact h22,
      },
      {
        have h13:= nonzeroissuccessor M k hk h12,
        cases h13 with p h14,
        cases h14 with hp h15,
        rw h15 at *,
        have h16:= cardinalsinhabited M (𝕊 p) hk,
        have h17:= tower_recursion_equation M m p hp h16,
        have h18:= sixpointtwo2_helper M m hm h3 p hp hk,
        rw h18 at *,
        rw h22 at *,
        have h30:= cardinalsinhabited2 M Λ hn,
        cases h30 with q h31,
        have h32:= emptyset_axiom q,
        contradiction,
      }
    },
    {
      rw singleton1,
      intros h40,
      rw h40 at *,
      exact minPhim2 M m hm,
    }  
  end

lemma Tmaximalfinite1A: 
 ∀(q κ :M), κ = Nc M 𝕍 → q ∈ NC M → 
 𝕋 M κ ⋖ exp2 M (𝕋 M q) →
exp2 M (exp2 M (𝕋 M q))  = (Λ:M):=
  begin
    intros q κ hk hq h6,
    have h8:= exp2TinNC M q hq,
    have h7:= Tkappa M κ (exp2 M (𝕋 M q)) hk h8 h6,
    exact h7,
  end

lemma Tmaximalfinite1B: 
 ∀(q κ :M), κ = Nc M 𝕍 → q ∈ NC M → 𝕋 M κ ⋖ q → 
( ∃ (u:M),u ∈ exp2 M (exp2 M (𝕋 M q))) →
exp2 M (exp2 M (exp2 M (𝕋 M q)))  = (Λ:M):=
  begin
    intros q κ hk hq hTk h6,
    have h3:= fourpointthree M κ hk,
    have h4:= Tkappa M κ q hk hq hTk,
    have h41: κ ∈ NC M:= kappaNC M κ hk,
    have h35:= TNC M κ h41,
    have h36:= TNC M (𝕋 M κ) h35,
    have h37:= TNC M q hq,
    have h5:= Tlessdot M (𝕋 M κ) q h35 hq hTk,
    have h38:= h5,
    rw lessdot_definition at h38,
    cases h38 with h39 h40,
    have h20:=exp2TinNC M κ h41,
    have h21:= cardinalsinhabited2 M (exp2 M (𝕋 M κ) ) h20,
    have h41:= h6,
    cases h41 with u h42,
    have h43:= (exp2_members M (exp2 M (𝕋 M q)) u).1 h42,
    cases h43 with a h44,
    cases h44 with h45 h46,
    have h30:= exporderNC M (𝕋 M (𝕋 M κ))(𝕋 M q) h36 h37 h39 ⟨ USC a, h45⟩,
    cases h30 with h50 h51,
    have h53:= Tsqkappa M κ hk,
    rw h53 at h51,
    have h59:= exp2TinNC M q hq,
    have h60:= kmlessdotexp2m M (𝕋 M κ) (exp2 M (𝕋 M q)) h35 h59 h51 ⟨ u, h42⟩,
    have h62:= NCexp2 M (exp2 M (𝕋 M q)) h59 ⟨ u, h42⟩,
    have h61:= Tkappa M κ (exp2 M (exp2 M (𝕋 M q))) hk h62 h60,
    exact h61,
  end

lemma Tmaximalfinite2: 
 ∀(n q:M), n ∈ NC M → zero ⋖ n →  
 φ M n ∈ FINITE M → q ∈ φ M n → 
 (∀ (t:M), t ∈ φ M n → t ⪯ q) →
 κ = Nc M 𝕍 → 
 𝕋 M κ ⋖ exp2 M (𝕋 M q) →
φ M (exp2 M (𝕋 M q))  = single (exp2 M (𝕋 M q)):=
  begin
    intros n q hn hn2 hfinite hq hmax hk h40, 
    have h3:= minPhim2 M n hn,
    have h4:= PhiNC M n hn,
    have h41: κ ∈ NC M:= kappaNC M κ hk,
    have h10:= member_subset M (φ M n) (NC M) q h4 hq,
    have h5:= exp2TinNC M q h10,
    have h60:= sixpointtwo2 M (exp2 M (𝕋 M q)) h5,
    apply h60,
    have h6:= Tmaximalfinite1A M q κ hk h10 h40, 
    exact h6,  
  end

lemma Tmaximalfinite3: 
 ∀(n q:M), n ∈ NC M → zero ⋖ n →  
 φ M n ∈ FINITE M → q ∈ φ M n → 
 (∀ (t:M), t ∈ φ M n → t ⪯ q) →
 κ = Nc M 𝕍 → 
 exp2 M (exp2 M (𝕋 M q)) = Λ → 
φ M (exp2 M (𝕋 M q))  = single (exp2 M (𝕋 M q)):=
  begin
    intros n q hn hn2 hfinite hq hmax hk h6, 
    have h3:= minPhim2 M n hn,
    have h4:= PhiNC M n hn,
    have h41: κ ∈ NC M:= kappaNC M κ hk,
    have h10:= member_subset M (φ M n) (NC M) q h4 hq,
    have h5:= exp2TinNC M q h10,
    have h60:= sixpointtwo2 M (exp2 M (𝕋 M q)) h5,
    apply h60,
    exact h6,  
  end

lemma offtheend2: ∀ (n:M), ∀ (y:M), y ∈ 𝔽 → ∀ (z:M), z ∈ 𝔽 → z < y → tower M n z = Λ → tower M n y = Λ:=
  begin
    intros n,
    have base: zero ∈ Z_offtheend2 M n:=
      begin
        rw Z_offtheend2_members M n,
        split,
        {
          exact zeroF M,
        },
        {
          intros z hz h3 h4,
          have h5:= xnotlessthanzero M z hz,
          contradiction,
        }
      end,
    have step: ∀ (y:M), y ∈ Z_offtheend2 M n → (∃(u:M), u ∈ 𝕊 y) → (𝕊 y ∈ Z_offtheend2 M n):=
      begin
        intros y h3 h4,
        rw Z_offtheend2_members M n at h3,
        cases h3 with hy h5,
        rw Z_offtheend2_members M n,
        split,
        {
          exact successorF M y hy h4,
        },
        {
          intros z hz h8 h9,
          rw towerE_recursion_equation M n y hy h4,
          have h12:= lessthansuccessor3 M z y hz hy h4,
          have h13:= h12.1 h8,
          have h14: tower M n y = Λ :=
            begin
              cases h13 with h15 h16,
              {
                have h17:= h5 z hz h15 h9,
                exact h17,
              },
              {
                rw h16 at *,
                exact h9,
              }
            end,
          have h20:= exp2lambda M,
          rw h14,
          exact h20,
        }
      end,
    intros y hy,
    rw F_members at hy,
    have h30:= hy (Z_offtheend2 M n) ⟨ base, step⟩,
    rw Z_offtheend2_members at h30,
    exact h30.2,
  end

lemma Tqmax: ∀ (n:M), n ∈ NC M → zero ⋖ n → 
∀ (κ q:M), κ = Nc M 𝕍 → q ∈ φ M n → exp2 M q = Λ  →
∀(t:M),(t ∈ φ M n → t ⪯ q):=
  begin
    intros n hn hzero κ q hk hq h2 t ht,
    have htcopy:= ht,
    have hqcopy:= hq,
    rw phi_members at ht,
    cases ht with y h4,
    rcases h4 with ⟨ hy, h5, h6⟩,
    rw phi_members at hq,
    cases hq with z h7,
    rcases h7 with ⟨ hz, h8, h9⟩,
    have h14:= PhiNC M n hn,
    have h15:= member_subset M (φ M n) (NC M) t h14 htcopy,
    have h115:= member_subset M (φ M n) (NC M) q h14 hqcopy,
    rw h5 at h15,
    rw h8 at h115,
    have h13:= towerorder M z hz y n hy hn h115,
    have h10:= towerE_recursion_equation M n z hz,
    have h16: y < z → t ⋖ q :=
      begin
        intros h17,
        rw h5, 
        rw h8,
        apply h13,
        exact h17,
      end,
    have h17: y < z → t ⪯ q:=
      begin
        intros h18,
        have h19:= h16 h18,
        rw lessdot_definition at h19,
        exact h19.1,
      end,
    have h20:= finitetrichotomy M y hy z hz,
    cases h20 with h21 h22,
    {
      exact h17 h21,
    },
    {
      cases h22 with h23 h24,
      {
        rw h23 at *,
        rw← h8 at h5,
        rw h5 at *,
        have h100:= towerinNC M n hn z hz,
        rw← h8 at h100,
        have h101:= h100 h9,
        exact ledotreflexive M q h101,
      },
      {
        have h30:= noinsertions M z y hz hy h24,
        have h31: ∃(u:M), u ∈ 𝕊 z:=
          begin
            rw le_definition at h30,
            cases h30 with a h31,
            cases h31 with b h32,
            exact ⟨ a, h32.1⟩,
          end,
        have h33:= h10 h31,
        rw← h8 at h33,
        rw h2 at h33,
        have h34:= offtheend2 M n y hy (𝕊 z)(successorF M z hz h31),
        have hsz:= successorF M z hz h31,
        have h35:= (letolessthan M (𝕊 z) y hsz hy).1 h30,
        cases h35 with h36 h37,
        {
          have h38:= h34 h36 h33,
          have h39:= cardinalsinhabited2 M (tower M n y) h15,
          rw h38 at h39,
          cases h39 with x h41,
          have h42:= emptyset_axiom x,
          contradiction,
        },
        {
          rw h37 at *,
          rw← h5 at h33,
          cases h6 with u h34,
          rw h33 at h34,
          have h35:= emptyset_axiom u,
          contradiction,
        }
      }
    }
  end 

lemma exp2kappa: ∀ (κ n: M),κ = Nc M 𝕍 → n ∈ NC M →
(∃ (u:M), u ∈ exp2 M n) → n ⪯ 𝕋 M κ:=
  begin
    intros κ n hk hn h2,
    have h3:= NCexp2 M n hn h2,
    have h4:= exp2uscsc M n h3,
    cases h4 with a h5,
    cases h5 with h6 h7,
    have h8: a ⊆ 𝕍 :=
      begin
        rw subset_definition,
        intros t ht,
        exact V_definition t,
      end,
    have h9:= (usc_subset M a 𝕍).1 h8,
    have h10:= xinNcx M 𝕍,
    rw← hk at h10,
    have h12: USC 𝕍 ∈ 𝕋 M κ :=
      begin
        rw T_members,
        use 𝕍 ,
        exact ⟨ h10, similar_reflexive M (USC 𝕍) ⟩,
      end, 
    rw ledot_definition,
    use USC a, use USC 𝕍,
    exact ⟨ h6, h12, h9⟩,
  end

lemma exp2kappa2: ∀ (κ n: M),κ = Nc M 𝕍 → n ∈ NC M →
n ⪯ 𝕋 M κ → (∃ (u:M), u ∈ exp2 M n):=
  begin
    intros κ n hk hn hTk,
    have h3:= xinNcx M 𝕍,
    rw← hk at h3,
    have h12: USC(𝕍) ∈ 𝕋 M κ:=
      begin
        rw T_members M κ (USC 𝕍),
        use 𝕍,
        exact ⟨ h3, similar_reflexive M (USC 𝕍)⟩,
      end,
    have h15: κ ∈ NC M:=
      begin
        rw NC_members,
        use 𝕍, 
        exact hk,
      end,
    have h14:= TNC M κ h15,
    have h13:= le2NC M (USC 𝕍) n (𝕋 M κ) hn h14 hTk h12,
    cases h13 with a h14,
    cases h14 with ha h15,
    have h16:= subset_usc2 M a 𝕍 h15,
    cases h16 with c h17,
    cases h17 with h18 h19,
    have h20:= exp2_members M n (SC c),
    use (SC c),
    rw h20,
    use c,
    split,
    {
      rw h19 at ha,
      exact ha,
    },
    {
      exact similar_reflexive M (SC c),
    }
  end

lemma exp2kappa3: ∀ (κ n: M),κ = Nc M 𝕍 → n ∈ NC M →
((¬ (n ⪯ 𝕋 M κ)) ↔ exp2 M n = Λ):=
  begin
    intros κ n hk hn,
    have h4:= exp2kappa M κ n hk hn,
    have h5:= exp2kappa2 M κ n hk hn,
    split,
    {
      intros h6,
      rw full_extensionality,
      intros t,
      split,
      {
        intros h,
        have h7:= h4 ⟨ t, h⟩,
        contradiction,
      },
      {
        intros h,
        have h7:= emptyset_axiom t,
        contradiction,
      }
    },
    {
      intros h h8,
      have h9:= h5 h8,
      rw h at h9,
      cases h9 with u h10,
      have h11:= emptyset_axiom u,
      contradiction,
    }
  end

-- phitwo is not used
lemma phitwo: ∀ (n q:M), n ∈ NC M → q ∈ NC M → 
zero ⋖ q → exp2 M (exp2 M (𝕋 M q)) = Λ → 
Nc M (φ M (𝕋 M q)) = two:= 
  begin
    intros n q hn hq hq2  h5,
    have h4:= exp2TinNC M q hq,
    have h5:= sixpointtwo2 M (exp2 M (𝕋 M q)) h4 h5,
    have hTq:= TNC M q hq,
    have h6:= exp2Tinhabited M q hq,
    have h6copy:= h6,
    cases h6 with u h20,
    rw exp2_members at h20,
    cases h20 with a h21,
    cases h21 with h22 h23,
    have h24:∃ (u v : M), u ∈ 𝕋 M q ∧ v ∈ u:=
      begin
         have h25:= cardinalsinhabited2 M q hq,
         cases h25 with b h26,
         rw lessdot_definition at hq2,
         cases hq2 with h27 h28,
         cases h28 with h29 h30,
         cases h30 with A h31,
         cases h31 with B h32,
         rcases h32 with ⟨ h33, h34, h35, h36⟩,
         cases h36 with w h37,
         use USC B,
         use single w,
         split,
         {
          rw T_members,
          use B,
          split,
          {
            exact h34,
          },
          {
            have h37:= cardinals2 M q b B hq h26 h34,
            rw← uscsimilar,
            exact similar_reflexive M B,
          }
         },
         {
          rw usc_members,
          rw minus_members at h37,
          exact h37.1,
         }
      end,
    have h108:= exp2Tinhabited M q hq,
    have h7:= sixpointsix2 M (𝕋 M q) hTq h24 h108,
    rw h5 at h7,
    have h8: φ M (𝕋 M q) = { 𝕋 M q, exp2 M (𝕋 M q)}:=
      begin
        rw full_extensionality,
        intros x,
        rw h7,
        rw binary_union_axiom,
        repeat{ rw singleton1},
        rw pairing_axiom,  
      end,
    have h9: φ M (𝕋 M q) ∈ two:=
      begin
        rw two_members,
        use (exp2 M (𝕋 M q)),
        use (𝕋 M q),
        split,
        {
          have h90:= xneqexp2x  M (𝕋 M q) hTq,
          intros h10,
          rw h10 at h90,
          apply h90,
          simp,
        },
        { 
          rw h8,
          rw full_extensionality,
          intros x,
          repeat{rw pairing_axiom},
          rw or_comm,
        }
      end, 
    have h10:= xinNcx M ( φ M (𝕋 M q)),
    have h13:Nc M (φ M (𝕋 M q)) ∈ NC M :=
      begin
        rw NC_members,
        use φ M (𝕋 M q),
      end,
    have h14: two ∈ NC M:= twoNC M,
    have h11:=cardinalsdisjoint2 M (Nc M (φ M (𝕋 M q))) two (φ M (𝕋 M q)) h13 h14 h10 h9,
    exact h11,
  end      

lemma phithree: ∀ (m:M),  m ∈ NC M → 
(∃(u:M), u ∈ exp2 M m) → 
zero ⋖ m →
exp2 M (exp2 M m) = Λ → 
Nc M (φ M m) = two:= 
  begin
    intros m hm h4 hm2 h5,
    have h40:= NCexp2 M m hm h4,
    have h50:= sixpointtwo2 M (exp2 M m) h40 h5,
    have h6copy:= h4,
    cases h4 with u h20,
    rw exp2_members at h20,
    cases h20 with a h21,
    cases h21 with h22 h23,
    have h24:∃ (u v : M), u ∈ m ∧ v ∈ u:=
      begin
        have h25:= cardinalsinhabited2 M m hm,
        cases h25 with b h26,
        rw lessdot_definition at hm2,
        cases hm2 with h27 h28,
        cases h28 with h29 h30,
        cases h30 with A h31,
        cases h31 with B h32,
        rcases h32 with ⟨ h33, h34, h35, h36⟩,
        cases h36 with w h37,
        use B, use w,
        rw minus_members at h37,
        exact ⟨h34, h37.1⟩, 
      end,
    have h7:= sixpointsix2 M m hm h24 h6copy,
    rw h50 at h7,
    have h8: φ M m = {m, exp2 M m}:=
      begin
        rw full_extensionality,
        intros x,
        rw h7,
        rw binary_union_axiom,
        repeat{ rw singleton1},
        rw pairing_axiom,  
      end,
    have h9: φ M m ∈ two:=
      begin
        rw two_members,
        use (exp2 M m),
        use m,
        split,
        {
          have h90:= xneqexp2x  M m hm,
          intros h10,
          rw h10 at h90,
          apply h90,
          simp,
        },
        { 
          rw h8,
          rw full_extensionality,
          intros x,
          repeat{rw pairing_axiom},
          rw or_comm,
        }
      end, 
    have h10:= xinNcx M ( φ M m),
    have h13:Nc M (φ M m) ∈ NC M :=
      begin
        rw NC_members,
        use φ M m,
      end,
    have h14: two ∈ NC M:= twoNC M,
    have h11:=cardinalsdisjoint2 M (Nc M (φ M m)) two (φ M m) h13 h14 h10 h9,
    exact h11,
  end    

lemma sevenpointtwo:
 ∀(n q:M), n ∈ NC M → zero ⋖ n →  
 ∀ (κ:M), κ = Nc M 𝕍 → 
 φ M n ∈ FINITE M → 
 q ∈ φ M n → 
 𝕋 M κ ⋖ q → 
 ¬¬ (
      Nc M (φ M (𝕋 M n)) =  𝕋 M (Nc M (φ M n)) + one  ∨ 
      Nc M (φ M (𝕋 M n)) =  𝕋 M (Nc M (φ M n)) + two
    )
 :=
  begin
    intros n q hn hn2 κ hk hfinite hq hTq,
    have h30:= PhiNC M n hn,
    have h31:= member_subset M (φ M n)(NC M) q h30 hq,
    have h23:=Tkappa M κ q hk h31 hTq,
    have hmax:= Tqmax M n hn hn2 κ q hk hq h23,
    have h5:= exp2kappa3 M,
    have h10:= sevenpointtwoA M n q hn hn2  hq hmax,
    cases h10 with h11 h12,
    have h13: Nc M (φ M (𝕋 M n)) = Nc M (imageT M (φ M n) ∪ φ M (exp2 M (𝕋 M q))):=
      begin 
        rw h11,
      end,
    have h16:= PhiNC M n hn,
    have h15:= Timagefinite M (φ M n) h16 hfinite,
    have h31:= member_subset M (φ M n)(NC M) q h16 hq,
    have h30:= Tmaximalfinite1B M q κ hk h31 hTq,
    have h17:= Tmaximalfinite3 M κ n q hn hn2 hfinite hq hmax hk,
    have h18:= singleton_finite M (exp2 M (𝕋 M q)),
 
    have h4489: exp2 M (exp2 M (𝕋 M q)) = Λ → Nc M (φ M (exp2 M (𝕋 M q))) = one:=
      begin
        intros h40,
        rw h17,
        have h41:= NcSingleton M ( exp2 M (𝕋 M q)),
        exact h41,
        exact h40,
      end,
    have h4501: (∃ (u:M), u ∈ exp2 M (exp2 M (𝕋 M q))) → Nc M (φ M (exp2 M (𝕋 M q))) = two:=
      begin
        intros h43,
        have h44:= h30 h43,
        have h50: Nc M (φ M (exp2 M (𝕋 M q))) = two:=
         --φ M (exp2 M (𝕋 M q)) = {(exp2 M (𝕋 M q)), exp2 M ((exp2 M (𝕋 M q)))} :=
          begin
            have h54: zero ⋖ exp2 M (𝕋 M q):= 
              begin
                have h55:= mlessdotexp2m M (𝕋 M q) (TNC M q h31) (exp2Tinhabited M q h31),
                have h60:zero ⪯ (𝕋 M q):= zeroledotx M (𝕋 M q)(TNC M q h31),
                have h61:= kmlessdotexp2m M zero (𝕋 M q) (zeroNC M)(TNC M q h31) h60 (exp2Tinhabited M q h31),
                exact h61,
              end,
            have h53:= exp2TinNC M q h31,
            have h51:= phithree M (exp2 M (𝕋 M q)) h53 h43 h54 h44,
            exact h51,
          end,
        exact h50,
      end,
    have h4522: ¬¬(exp2 M (exp2 M (𝕋 M q)) = Λ ∨
                  (∃ (u:M),u ∈ exp2 M (exp2 M (𝕋 M q)))):=
      begin
        intros h,
        rw not_orNF at h,
        cases h with h201 h202,
        rw not_exists at h202,
        rw full_extensionality at h201,
        have h203: ∀(x:M), ¬ x ∈ Λ:=
          begin
            intros x,
            have h204:=emptyset_axiom x,
            exact h204,
          end, 
        have h204:  ¬∀ (x : M), ¬ x ∈ exp2 M (exp2 M (𝕋 M q)):=
          begin
            intros h205,
            apply h201,
            intros x,
            specialize h203 x,
            split,
            {
              intros h206,
              have h207:= h202 x,
              contradiction,
            },
            {
              intros h208,
              contradiction,
            }
          end,
        contradiction,
      end,
    have h14:  φ M (exp2 M (𝕋 M q)) ∈ FINITE M →
    Nc M (imageT M (φ M n) ∪ φ M (exp2 M (𝕋 M q))) = Nc M (imageT M (φ M n)) + Nc M (φ M (exp2 M (𝕋 M q))):=
      begin
        intros h180,
        have h200:= NCsum M (imageT M (φ M n))( φ M (exp2 M (𝕋 M q))) h15 h180 h12,
        exact h200,
      end,
    have h20:= Timage M (φ M n) hfinite h16,
    have h21:= Nc_unitclass M (exp2 M (𝕋 M q)),
    have h22:= Timagefinite M,
    have h4659:exp2 M (exp2 M (𝕋 M q)) = Λ →
      Nc M (φ M (𝕋 M n)) = 𝕋 M  (Nc M (φ M n)) + one:=
      begin
        intros h400,
        have h401:= h4489 h400,
        rw h14 at h13,
        rw h20 at h13,
        rw h401 at h13,
        exact h13,
        have h402:= xinNcx M (φ M (exp2 M (𝕋 M q))),
        rw h401 at h402,
        have h403:= finitecardinals1 M one (φ M (exp2 M (𝕋 M q))) (oneF M) h402,
        exact h403,
      end,
    have h4660: (∃ (u:M), u ∈ exp2 M (exp2 M (𝕋 M q))) →
      Nc M (φ M (𝕋 M n)) = 𝕋 M  (Nc M (φ M n)) + two:=
      begin
        intros h410,
        have h411:= h4501 h410,
        rw h14 at h13,
        rw h20 at h13,
        rw h411 at h13,
        exact h13,
        have h412:= xinNcx M (φ M (exp2 M (𝕋 M q))),
        rw h411 at h412,
        have h403:= finitecardinals1 M two (φ M (exp2 M (𝕋 M q))) (twoF M) h412,
        exact h403,
      end,
    have h400:= pushnotnot 
         (exp2 M (exp2 M (𝕋 M q)) = Λ )  
          (∃ (u:M), u ∈ exp2 M (exp2 M (𝕋 M q)))
          ( (Nc M (φ M (𝕋 M n))) = 𝕋 M (Nc M (φ M n)) + one)
          ( (Nc M (φ M (𝕋 M n))) = 𝕋 M (Nc M (φ M n)) + two)
          h4522  h4659 h4660,
    exact h400,
  end   

lemma exp2orderstrict: ∀ (n m:M), n ∈ NC M →
m ∈ NC M → n ⋖ m →
(∃ (u:M), u ∈ exp2 M (𝕋 M m)) →
(¬ (exp2 M (𝕋 M m)  ⪯  exp2 M (𝕋 M n))) →
exp2 M (𝕋 M n) ⋖ exp2 M (𝕋 M m):=
  begin
    intros n m hn hm h3 h100 h40,
    rw lessdot_definition at h3,
    rcases h3 with ⟨h4, h5, h6⟩,
    cases h6 with a h7,
    cases h7 with b h8,
    rcases h8 with ⟨ h9, h10, h11, h12⟩,
    cases h12 with u h13, 
    have hTn:= TNC M n hn,
    have hTm:= TNC M m hm,
    have hT4:= (Tledot M n m hn hm).1 h4,
    have h14:= exporderNC M (𝕋 M n) (𝕋 M m) hTn hTm hT4 h100,
    cases h14 with h15 h16, 
    have h17:= cardinalsinhabited2 M (exp2 M (𝕋 M n)) h15,
    cases h17 with x h18,
    have h19: SC a ∈ exp2 M (𝕋 M n):=
      begin
        rw exp2_members,
        use a,
        split,
        {
          rw T_members,
          use a,
          exact ⟨ h9, similar_reflexive M (USC a) ⟩, 
        },
        {
          exact similar_reflexive M (SC a),
        }
      end,
    have h20: SC b ∈ exp2 M (𝕋 M m ):=
      begin
        rw exp2_members,
        use b,
        split,
        {
          rw T_members,
          use b,
          exact ⟨ h10, similar_reflexive M (USC b) ⟩, 
        },
        {
          exact similar_reflexive M (SC b),
        }
      end,
    have h21: b ∈ SC b:=
      begin
        rw sc_members,
        exact subset_reflexive M b,
      end,
    have h22: a ∈ SC a:=
      begin 
        rw sc_members,
        exact subset_reflexive M a,
      end,
    have h23: ¬ (b ∈ SC a):=
      begin
        intros h,
        rw sc_members at h,
        rw minus_members at h13,
        cases h13 with h24 h25,
        have h26:= member_subset M b a u h h24,
        contradiction,
      end,
    have h24: b ∈ (SC b) -(SC a):=
      begin
        rw minus_members,
        exact ⟨ h21, h23⟩,
      end,
    rw lessdot_definition,
    split,
    {
      exact h16,
    },
    {
      split,
      {
        exact h40,
      },
      {
        use SC a,
        use SC b,
        have h50:= sc_subset M a b h11,
        exact ⟨ h19, h20, h50, ⟨ b, h24⟩⟩, 
      }
    }
  end

lemma topsdown: ∀ (κ n q:M), κ = Nc M 𝕍 → n ∈ NC M → zero ⋖ n → 
φ M n ∈ FINITE M → q ∈  φ M n → 𝕋 M κ ⋖ q → 
(exp2 M (exp2 M (𝕋 M q)) = Λ ∨ ∃(u:M), u ∈ exp2 M (exp2 M (𝕋 M q))) →
∃(Q:M),Q ∈ φ M (𝕋 M n) ∧ 𝕋 M κ ⋖ Q :=
  begin
    intros κ n q hk hn hn2 hfinite hq htop h290,
    have hknc:= kappaNC M κ hk,
    have h19:= TNC M κ hknc,
    have h18:= PhiNC M n hn,
    have hqnc:= member_subset M (φ M n)(NC M) q h18 hq,
    have h17:= exp2Tinhabited M q hqnc,
    have h30:= exp2Tinhabited M κ hknc,
    have h16:= TNC M q hqnc,
    have h20:= Tlessdot M (𝕋 M κ) q h19 hqnc htop, 
    have h15:= TNC M (𝕋 M κ) h19,
    have h115:= TNC M n hn,
    have h300:= sevenpointtwohelper M n q hn hq,
    have h26:= fourpointthree M κ hk,
    have h301:= Tlessdot M zero n (zeroNC M) hn hn2,
    have h302:= Tzero M,
    rw h302 at h301,
    have h24:= exp2T M (𝕋 M κ) h19 h30,
    have h32:= exp2TinNC M q hqnc,
    have h31:= phiexp2 M (𝕋 M n) (𝕋 M q) h115 h301 h300 h32,
    have h80:= Tsqkappa M κ hk,
    have h40:USC 𝕍 ∈  𝕋 M κ :=
      begin
        rw T_members,
        use 𝕍,
        rw hk,
        split,
        {
          exact xinNcx M 𝕍,
        },
        {
          exact similar_reflexive M (USC 𝕍),
        }
      end,
    have h41:= Tlessdot M (𝕋 M κ) q h19 hqnc htop,
    rw lessdot_definition at h41,
    cases h41 with h42 h43,
    have h45:= exp2Tinhabited M q hqnc,
    have h44:= exporderNC M (𝕋 M (𝕋 M κ))(𝕋 M q) h15 h16 h42 h45,
    cases h44 with h45 h46,
    rw h80 at h46,
    cases h290 with case1 case2,
    { have h4626:¬ (exp2 M (𝕋 M q)  ⪯ 𝕋 M κ ):=
        begin
          intros h,
          have h49:= le2NC M (USC 𝕍) (exp2 M (𝕋 M q))(𝕋 M κ) h32 h19 h h40,
          cases h49 with P h50,
          cases h50 with h51 h52,
          have h53:= uscsubsetisusc M P 𝕍 h52,
          cases h53 with c h54,
          cases h54 with h55 h56,
          rw h56 at *,
          have h57: SC c ∈ (exp2 M (exp2 M (𝕋 M q))):=
            begin
              rw exp2_members,
              use c,
              exact ⟨ h51, similar_reflexive M (SC c) ⟩,
            end,
          rw case1 at h57,
          have h58:= emptyset_axiom (SC c),
          contradiction,
        end,
      have h81:= h4626,
      rw←  h80 at h81,
      have h82:= exp2orderstrict M (𝕋 M κ) q h19 hqnc htop h17 h81,
      rw h80 at h82,
      use exp2 M (𝕋 M q),
      exact ⟨ h31,h82⟩,  
    },
    {
      use exp2 M (exp2 M (𝕋 M q)),
      have hnT2: zero ⋖ 𝕋 M n:= 
        begin
          have h52:= Tlessdot M zero n (zeroNC M) hn hn2,
          rw Tzero at h52,
          exact h52,
        end,
      have h51:= NCexp2 M (exp2 M (𝕋 M q)) h32 case2,
      split,
      {
        have h50:= phiexp2 M (𝕋 M n)(exp2 M (𝕋 M q)) h115 hnT2 h31 h51,
        exact h50,
      },
      {
        have h60:= kmlessdotexp2m M (𝕋 M κ)(exp2 M (𝕋 M q)) h19 h32 h46 case2,
        exact h60,
      }
    }  
  end

lemma towercontainspowers: ∀ (n q:M), n ∈ NC M → q ∈ φ M n → ¬(q = n)→
∃ (m:M), m ∈ NC M ∧ q = exp2 M m ∧ m ∈ φ M n:=
  begin
    intros n q hn hq hnq,
    rw phi_members at hq,
    cases hq with y h4,
    rcases h4 with ⟨ hy, h5, h6⟩,
    have h7:= towerE_base_equation M n,
    have h8: ¬ y = zero:=
      begin
        intros h,
        rw h at *,
        rw towerE_base_equation at h5,
        contradiction,
      end, 
    have h9:= nonzeroissuccessor M y hy h8,
    cases h9 with p h10,
    cases h10 with hp hsp,
    have h11:= h5,
    rw hsp at h11,
    have h30: ∃ (v:M), v ∈ 𝕊 p:=
      begin 
        have h31:= hy,
        rw hsp at h31,
        exact cardinalsinhabited M (𝕊 p) h31,   
      end,
    rw towerE_recursion_equation M n p hp h30 at h11,
    have h20:= h6,
    rw h11 at h20,
    cases h20 with u h21,
    have h22:= (exp2_members M (tower M n p) u).1 h21,
    cases h22 with a h23,
    cases h23 with h24 h25,
    use tower M n p,
    split,
    {
      have h12:= towerinNC M n hn p hp ⟨ USC a, h24⟩,
      exact h12,
    },
    { 
      split,
      { 
        exact h11,
      },
      {
        rw phi_members,
        use p,
        simp,
        exact ⟨hp,⟨ USC a, h24⟩⟩,
      }
    }
  end

lemma exp2kappaisempty: ∀(κ:M), κ = Nc M 𝕍 → exp2 M κ = Λ:=
  begin
    intros κ hk,
    have h3:= kappaNC M κ hk,
    have h4: ∀ (u:M), ¬ (u ∈ exp2 M κ):=
      begin
        intros u hu,
        have h5:= mlessdotexp2m M κ h3 ⟨ u, hu⟩,
        rw lessdot_definition at h5,
        rcases h5 with ⟨ h6, h7, h8⟩,
        have h10:= NCexp2 M κ h3 ⟨ u, hu⟩,
        have h9:= kappamax M κ (exp2 M κ ) hk h10,
        contradiction,
      end,
    rw full_extensionality,
    intros t,
    specialize h4 t,
    split,
    {
      intros h,
      contradiction,
    },
    {
      intros h,
      have h20:= emptyset_axiom t,
      contradiction,
    }
  end

lemma Phikappa: ∀(κ:M), κ = Nc M 𝕍 → φ M κ = single κ ∧ Nc M (φ M κ) = one:=
  begin
    intros κ hk,
    have h2: κ ∈ NC M:=
      begin
        rw NC_members,
        use 𝕍,
        exact hk,
      end, 
    have h3:= exp2kappaisempty M κ hk,
    have h4:= sixpointtwo2 M κ h2 h3,
    split,
    {
      exact h4,
    },
    {
      rw h4,
      have h5:= NcSingleton M κ,
      exact h5,
    }
  end

lemma Xcard: ∀ (n κ:M), n ∈ NC M → zero ⋖ n →
κ = Nc M  𝕍 → κ ∈ φ M n →
φ M n ∈ FINITE M →  
Nc M (φ M (𝕋 M n)) = 𝕋 M (Nc M (φ M n)) + one:=
  begin
    intros n κ hn hn2 hk hkphi hfinite,
    have h6:= PhiNC M n hn,
    have h3: (∀ (t : M), t ∈ φ M n → t ⪯ κ) :=
      begin
        intros t ht,
        have h7:= member_subset M (φ M n) (NC M) t h6 ht,
        have h5:= kappamax M κ t hk h7,
        exact h5,
      end,
    have h4:= sevenpointtwoA M n κ hn hn2 hkphi h3,
    cases h4 with h10 h11,
    have h9:= Timage M (φ M n) hfinite h6,
    have h12:= finitecardinals3 M (φ M n) hfinite,
    have h13:= Tfinite M ( Nc M (φ M n)) h12,
    have h14:= xinNcx M (imageT M (φ M n)),
    have h16:= h13,
    rw← h9 at h16,
    have h15:= finitecardinals1 M (Nc M (imageT M (φ M n))) (imageT M (φ M n)) h16 h14,
    have h19:= Phikappa M κ hk,
    cases h19 with h20 h21,
    have h23:= fourpointthree M κ hk,
    rw h23 at *, 
    have h24: φ M κ ∈ FINITE M:= 
      begin
        rw h20,
        exact singleton_finite M κ,
      end, 
    have h30:= NCsum M (imageT M (φ M n))( φ M κ ) h15 h24 h11,
    rw h9 at h30,
    rw← h10 at h30,
    rw h21 at h30,
    exact h30,
  end

lemma Xdown:  ∀ (n κ:M), n ∈ NC M → zero ⋖ n →
κ = Nc M  𝕍 → κ ∈ φ M n → κ ∈ φ M (𝕋 M n):=
  begin
    intros n κ hn hn2 hk hkphi,
    have h40:= hkphi,
    rw phi_members at h40,
    cases h40 with z h3,
    rcases h3 with ⟨hz, h4, h5⟩,
    have h7:= xinNcx M 𝕍,
    rw← hk at h7,
    rw h4 at h7,
    have h6:= TofI M n hn z hz ⟨𝕍, h7⟩,
    have h8:= Tfinite M z hz,
    have h30: (∀ (t : M), t ∈ φ M n → t ⪯ κ) :=
      begin
        intros t ht,
        have h60:= PhiNC M n hn,
        have h7:= member_subset M (φ M n) (NC M) t h60 ht,
        have h5:= kappamax M κ t hk h7,
        exact h5,
      end,
    have h10:= sevenpointtwoA M n κ hn hn2 hkphi h30,
    cases h10 with h70 h71,
    have h72: imageT M (φ M n) ⊆  φ M (𝕋 M n):=
      begin
        rw subset_definition,
        intros t ht,
        have h73:= h70,
        rw full_extensionality at h73,
        specialize h73 t,
        rw h73,
        rw binary_union_axiom,
        left,
        exact ht,
      end,
    have h31: 𝕋 M κ ∈ imageT M (φ M n):=
      begin
        rw imageT_members M (φ M n),
        use κ,
        simp,
        exact hkphi,
      end,
    have h32:= h31,
    have h33:= member_subset M (imageT M (φ M n))( φ M (𝕋 M n)) ( 𝕋 M κ) h72 h31,
    have h40:= TNC M n hn,
    have h41:= Tlessdot M zero n (zeroNC M) hn hn2,
    rw Tzero at h41,
    have h23:= fourpointthree M κ hk,
    have h35:= kappaNC M κ hk,
    have h34:= phiexp2 M (𝕋 M n) (𝕋 M κ) h40 h41 h33,
    rw h23 at *,
    exact h34 h35,  
  end

/-- lemma Xup: ∀ (n r κ:M), n ∈ NC M → r ∈ NC M → zero ⋖ n →
κ = Nc M  𝕍 → κ ∈ φ M n → n = 𝕋 M r → φ M n ∈ FINITE M → 
κ ∈ φ M r:=
  begin
    intros n r κ hn hr hn2 hk hkphi hTr hfinite,
    have h100:= hkphi,
    rw phi_members M n at hkphi,
    cases hkphi with z h3,
    rcases h3 with ⟨ h4, h5, h6⟩,
    have h10:= exp2kappaisempty M κ hk,
    have h7: ¬ n = κ:=
      begin
        intros h,
        rw h at *, 
        rw hTr at h10,
        have h11:= exp2Tinhabited M r hr,
        rw h10 at h11,
        cases h11 with u h12,
        have h13:= emptyset_axiom u,
        contradiction,
      end,
    have h8: ¬ z = zero:=
      begin
        intros h,
        rw h at *,
        rw towerE_base_equation at h5,
        rw sym at h5,
        contradiction,
      end,
    have h9:= nonzeroissuccessor M z h4 h8,
    cases h9 with y h11,
    cases h11 with hy h12,
    have h14:= cardinalsinhabited M z h4,
    rw h12 at h14,
    have h13:= towerE_recursion_equation M n y hy h14,
    have h15:= h14,
    rw← h12 at h13,
    rw←  h5 at h13,
    set ξ := tower M n y with xidef,
    have h20: exp2 M ξ = κ:=
      begin
        rw sym,
        exact h13,
      end,
    have h21:= kappaNC M κ hk,
    rw← h20 at h21,
    have h22:= exp2uscsc M ξ h21,
    cases h22 with c h23,
    cases h23 with h24 h25,
    have h26:= xinNcx M c,
    have h27: USC c ∈ 𝕋 M (Nc M c):=
      begin
        rw T_members,
        use c,
        exact ⟨ h26, similar_reflexive M (USC c)⟩,
      end,
    have h28: Nc M c ∈ NC M:=
      begin
        rw NC_members,
        use c,
      end,
    have h29:= TNC M (Nc M c) h28,
    have h30: ξ ∈ NC M:=
      begin
        rw xidef,
        have h31:= towerENC M n hn y hy,
        apply h31,
        use USC c,
        rw xidef at h24,
        exact h24,
      end,
    have h31:= cardinalsdisjoint2 M (𝕋 M (Nc M c)) ξ (USC c) h29 h30 h27 h24,
    have h32:= ylessdottower M y hy n hn hn2,
    rw←  xidef at h32,
    have h33:= h32 ⟨ USC c, h24⟩,
    have h34:= h33,
    rw← h31 at h34,
    have h35:= h34,
    rw lessdot_definition at h35,
    rcases h35 with ⟨h36, h37, h38⟩,
    have h40:= FtoNC M y hy,
    have h39:= TontoNC M y (Nc M c) h40 h28 h36,
    cases h39 with p h40,
    cases h40 with h41 h42, 
    have h43:= h13,
    rw xidef at h13,
    rw h42 at h13,
    rw hTr at h13,
    have h50: p ∈ 𝔽 := sorry,
    have h44:= TofI M r hr p h50,
    



  end
--/

lemma sevenpointtwoB:
 ∀(n q:M), n ∈ NC M → zero ⋖ n →  
 ∀ (κ:M), κ = Nc M 𝕍 → 
 φ M n ∈ FINITE M → 
 q ∈ φ M n → 
 𝕋 M  κ ⋖ q → 
 φ M (𝕋 M n) ∈ FINITE M:=
  begin
    intros n q hn hn2 κ hk hfinite hq hTq,
    have h30:= PhiNC M n hn,
    have h31:= member_subset M (φ M n)(NC M) q h30 hq,
    have h23:=Tkappa M κ q hk h31 hTq, 
    have hmax:= Tqmax M n hn hn2 κ q hk hq h23,
    have h3:= sevenpointtwoA M n q hn hn2 hq hmax,
    cases h3 with h20 h21,
    have h16:= PhiNC M n hn,
    have h25:= kappaNC M κ hk,
    have h26:= TNC M κ h25,
    have h27:= TNC M q h31,
    have h30:= kmlessdotexp2m M (𝕋 M κ) (𝕋 M q) h26 h27,
    have h17:= Tmaximalfinite2 M κ n q hn hn2 hfinite hq hmax hk, 
    have h18:= singleton_finite M (exp2 M (𝕋 M q)),
    rw←  h17 at h18,
    have h4:= Timagefinite M (φ M n) h16 hfinite, 
    have h10:= union M (imageT M (φ M n)) (φ M (exp2 M (𝕋 M q))) h4 h18 h21,
    rw← h20 at h10,
    exact h10,
  
  end 
   
 


lemma sevenpointone2:∀(k:M),k ∈ 𝔽 → ∀(m:M), m ∈ NC M → (∃(u v:M), (u ∈ m ∧ v ∈ u)) → (k = Nc M m → φ M m ∈ FINITE M):=
  begin
    have base: zero ∈ Z_sevenpointone2 M:=
      begin
        rw Z_sevenpointone2_members,
        split,
        {
          exact zeroF M,
        },
        {
          intros m hm huv h3,
          have hTm:= TNC M m hm,
          have h4:= minPhim2 M (𝕋 M m) hTm,
          have h5:= xinNcx M (φ M (𝕋 M m)),
          have h6:= h5,
          rw← h3 at h6,
          have h7:= h6,
          rw zero_members at h7,
          rw h7 at h4,
          have h8:= emptyset_axiom (𝕋 M m),
          contradiction,
        }
      end,
    have step: ∀ (k:M),k ∈ Z_sevenpointone2 M → (∃ (u:M),u ∈ 𝕊 k) → 𝕊 k ∈ Z_sevenpointone2 M:=
      begin
        intros k h12 hsk,
        rw Z_sevenpointone2_members at h12,
        rw Z_sevenpointone2_members,
        cases h12 with hk h13,
        split,
        {
          exact successorF M k hk hsk,
        },
        { 
          intros m hm huv h140,
          have h15:= Tinhabitedmember M m hm huv,
          cases h15 with h14 h17,
          have h18:= exp2Tinhabited M m hm,
          have h20:= sixpointsix2 M (𝕋 M m) h14 h17 h18,
          have h21:= sixpointfive2 M (𝕋 M m) h14 h18,
          have h30:= exp2TinNC M m hm,
          have h31:= xinNcx M (φ M (𝕋 M m)),
          rw←h140 at h31,
          have hskF:= successorF M k hk hsk, 
          have h40:= finitecardinals1 M (𝕊 k) (φ M (𝕋 M m)) hskF h31,
          rw union_commutative at h20,
          have h41:= finitedown M (φ M (𝕋 M m))(φ M (exp2 M (𝕋 M m))) (𝕋 M m) h20 h40 h21,
          have h22:= Ncadjoint M (φ M (exp2 M (𝕋 M m))) (𝕋 M m) h41 h21,
          rw←h20 at h22,
          rw sym at h22,  
          rw← successorisplusone at h22,
          rw← h140 at h22,
          have h45:= finitecardinals3 M (φ M (exp2 M (𝕋 M m))) h41,
          have h23:= successoroneone M k (Nc M (φ M (exp2 M (𝕋 M m)))) hk h45 hsk,
          simp_rw←  h22 at h23,
          have h24:= h23 hsk,
          simp at h24, 
          have h25:  𝕊 k =  (Nc M (φ M (exp2 M (𝕋 M m)))) + one:=
            begin
              rw sym at h22,
              rw successorisplusone at h22,
              rw sym at h22,
              exact h22,
            end,
          have h30:= finite_adjoin M,
          have h31: exp2 M (𝕋 M m) = 𝕋 M (exp2 M m) :=
            begin
              have h32:= exp2T M m hm,
              apply h32,
              
            end,
        }
      end,
     
  end



theorem Vnotfinite2: ¬ 𝕍 ∈ FINITE M:=
  begin
    intros hfinite,
    have h3:= finitedecidable M 𝕍 hfinite,
    rw decidable_members at h3,
    have h4: ∀ (x y:M), x = y ∨ ¬ x = y:=
      begin 
        intros x y,
        have hx:= V_definition x,
        have hy:= V_definition y,
        have h5:= h3 x y ⟨ hx, hy⟩, 
        exact h5,
      end,
    have h5:  ∀ (x y:M), x ∈  y ∨ ¬ x ∈  y:=
      begin
        intros x y,
        have h7: x ∈ y ↔ membershipF M x y = single x:=
          begin
            split,
            {
              intros h8,
              rw full_extensionality,
              intros z,
              rw membershipF_members M x y,
              rw singleton1 M,
              simp,
              intros h9,
              rw h9 at *,
              exact h8,
            },
            {
              intros h10,
              have h11:= membershipF_members M x y x,
              rw h10 at h11,
              rw singleton1 at h11,
              simp at h11,
              exact h11,
            }
          end,
        rw h7,
        have h12:= h4 (membershipF M x y) (single x),
        exact h12,
      end,
    have h13: SSC (𝕍:M) = 𝕍:=
      begin
        rw full_extensionality,
        intros x,
        split,
        {
          intros h3,
          exact V_definition x,
        },
        {
          intros hx,
          rw ssc_members,
          split,
          {
            rw subset_definition,
            intros z hz,
            exact V_definition z,
          },
          {
            intros y hy,
            exact h5 y x,
          }
        }
      end,
    have h14:= finitecardinals3 M 𝕍 hfinite,
    set m:= Nc M 𝕍 with mdef,
    have h15: 𝕍 ∈ SSC(𝕍):=
      begin 
        rw ssc_members,
        split,
        {
          exact subset_reflexive M 𝕍,
        },
        {
          intros t ht,
          exact h5 t 𝕍,
        }
      end,
    have h20:  UNENLARGEABLE M 𝕍:=
      begin
        unfold UNENLARGEABLE,
        intros t,
        have h21:= V_definition t,
        intros h22,
        apply h22,
        exact h21,
      end,
    have h23: MAXIMAL M m:=
      begin
        unfold MAXIMAL,
        have h25:= unenlargeable4 M 𝕍 hfinite h20,
        split,
        {
          exact h14,
        },
        {
          rw mdef,
          exact h25, 
        }
      end,
    have h26:= xinNcx M 𝕍,
    rw← mdef at h26,
    have h27: USC 𝕍 ∈ 𝕋 M m:=
      begin
        rw T_members,
        use 𝕍,
        exact ⟨ h26, similar_reflexive M (USC 𝕍)⟩,
      end,
    have h28: SSC 𝕍 ∈ exp M (𝕋 M m):= 
      begin
        rw exp_members,
        use 𝕍,
        exact ⟨ h27, similar_reflexive M (SSC 𝕍)⟩,
      end,
    have h29:= h28,
    rw h13 at h29,
    have h30:= expTinF M m h14,
    have h33:= cardinalsdisjoint M (exp M (𝕋 M m)) m 𝕍 h30 h14,
    have h34: exp M (𝕋 M m) = m:=
      begin
        apply h33,
        rw intersection_axiom,
        exact ⟨ h29, h26⟩,
      end,
    have h35:= Tfinite M m h14,
    have h36:= mlessthanexpm M (𝕋 M m) h35 ⟨ SSC 𝕍,h28⟩,
    have h37:= (Tlessthan M (𝕋 M m)(exp M (𝕋 M m)) h35 h30).1 h36,
    have h38:= expT M (𝕋 M m) h35 ⟨ SSC 𝕍 , h28⟩,
    have h39: (exp M (exp M (𝕋 M (𝕋 M m)))) = exp M (𝕋 M (exp M (𝕋 M m))):=
      begin
        rw h38,
      end,
    have h40:= h39,
    rw h34 at h40,
    have h41:= h40,
    rw h34 at h41,
    have h42:= smalltower M m h23,
    have h43:= Phitwo M m m h23 h14,
    set n:= Nc M (Φ M zero) with ndef,
    have h44:= sevenpointtwo M,

    
  end

lemma notnotusc: ∀ (m U:M), MAXIMAL M m → U ∈ m → 
   ∀ (x:M), x ∈ USC 𝕍 → ¬¬ x ∈ USC U:=
  begin
    sorry,
  end

lemma uscseparable:  ∀ (m U:M), MAXIMAL M m → U ∈ m → 
  ∀ (x:M), x ∈ FINITE M → x ∈ USC 𝕍 ∨ ¬ x ∈ USC 𝕍 :=
  begin
    sorry,
  end

theorem nomax1: (¬ 𝕍 ∈ FINITE M) → ¬ ∃(m:M), MAXIMAL M m:=
  begin
    intros hV hm2,
    cases hm2 with m hmax,
    have hmaximal:= hmax,
    unfold MAXIMAL at hmaximal,
    cases hmaximal with hm h3,
    have h4:= cardinalsinhabited M m hm,
    cases h4 with U hU,
    have h5:= finitecardinals1 M m U hm hU,
    set X:= (SSC U) - USC U  with Xdef,
    have h100: USC 𝕍 ⊆ FINITE M -X:=
      begin
        rw subset_definition,
        intros t ht,
        rw minus_members,
        split,
        {
          rw usc at ht,
          cases ht with a h6,
          rw h6.2 at *,
          exact singletons_finite M a,
        },
        {
          intros h8,
          rw Xdef at h8,
          rw minus_members at h8,
          cases h8 with h9 h10,
          have h11:= notnotusc M m U hmax hU t ht,
          contradiction,
        }
      end,
    have h110:= finitenotfinite3 M hV X h100,
    have h120: USC U ⊆ FINITE M - X:=
      begin
        rw subset_definition,
        intros t ht,
        rw usc at ht,
        cases ht with a h121,
        rw h121.2 at *,
        have h122:single a ∈ USC 𝕍:=
          begin
            rw usc_members,
            have h123:= V_definition a,
            exact h123,
          end,
        exact member_subset M (USC 𝕍)( FINITE M - X)(single a) h100 h122,
      end,
    have h122: ∀ (t:M), t ∈ FINITE M - X → ¬¬ t ∈ USC U:=
      begin
        intros t ht,
        rw Xdef at ht,
        rw minus_members at ht,
        cases ht with htfinite h123,
        have h124:= uscseparable M m U hmax hU t htfinite,
        cases h124 with h125 h126,
        {
          have h127:= notnotusc M m U hmax hU t h125,
          exact h127,
        },
        {
          have h130: ¬ t ∈ USC U:=
            begin
              intros h131,
              rw usc at h131,
              cases h131 with a h132,
              rw h132.2 at *,
              apply h126,
              rw usc_members,
              have h127:= V_definition a,
              exact h127,
            end,
          have h135: ¬¬ t ∈ SSC U:=
            begin
              have h136:= notnotssc2 M m U hmax hU t htfinite,
              exact h136,
            end,
          have h140: ¬¬ t ∈ SSC U - USC U :=
            begin
              rw minus_members,
              have h141:= notnot_and (t ∈ SSC U) (¬ t ∈ USC U),
              rw triplenegation at h141,
              rw h141,
              exact⟨h135,h130⟩,
            end,
          contradiction,
        }
      end,
    have h150:= finiteDNS M (USC U) (FINITE M - X),
    have h112: ¬¬ FINITE M -X = USC U :=
      begin
        rw Xdef,
        rw full_extensionality,
        have h113:= notnot_iff_2way,
      end
  end


lemma towerEstrictlyincreasing: ∀ (y:M), y ∈ 𝔽 →  ∀ (m:M), m ∈ NC M  → (∃ (u:M), u ∈ tower M m y)→ (¬ ((y = zero ∨ y = one ∨ y = two) ∧ m = zero)) → y < tower M m y:=
  begin
    have base: zero ∈ Z_towerEstrictlyincreasing M:=
      begin
        rw Z_towerEstrictlyincreasing_members,
        split,
        {
          exact zeroF M,
        },
        {
          intros m h h2 h3,
          rw towerE_base_equation M,
          simp at h3, 
          rw lessdot_definition,
          split,
          { 
            exact zero_ledot_x M m h, 
          },
          { 
            rw sym,
            exact h3, 
          }
        }
      end,
    have step: ∀(y:M), y ∈ Z_towerEstrictlyincreasing M → (∃(u:M), u ∈ 𝕊 y) → 𝕊 y ∈ Z_towerEstrictlyincreasing M:=
      begin 
        intro y, 
        rw Z_towerEstrictlyincreasing_members M, 
        intros  h h2,
        cases h with h3 h4, 
        rw Z_towerEstrictlyincreasing_members M, 
        split,
        {
          exact successorF M y h3 h2, 
        },
        intros m h5 h6 h7,  
        have h40:= h4 m h5, 
        cases h6 with u h9,
        have h9copy:= h9, 
        rw towerE_recursion_equation M m y h3 h2 at h9, 
        have h90 := h9, 
        have h42:= mlessthanexpm M y h3, 
        rw exp2_members at h9,
        cases h9 with a h10,
        cases h10 with h11 h12,
        have h13:= h4 m h5 ⟨ USC a, h11⟩, 
        have h14:= towerEincreasing M m h5 y h3 ⟨ USC a, h11⟩, 
        have h38: tower M m y ∈ NC M := towerENC M m h5 y h3 ⟨ USC a, h11⟩, 
        have h17:= exporderNC M y (tower M m y) (FtoNC M y h3) h38 h14 ⟨ u, h90⟩,
        cases h17 with h18 h19, 
        have h15:= FregeNdecidable M,
        rw decidable_members M at h15, 
        have h16 := h15 y zero ⟨ h3 ,(zeroF M)⟩, 
  
        have h17 := h15 m zero ⟨ h5, (zeroF M)⟩, 
        have h20 := successorF M y h3 h2, 
        have h21 := h15 (𝕊 y) zero ⟨ h20, zeroF M⟩, 
        have h22 := h15 (𝕊 y) one  ⟨ h20, oneF M⟩, 
        have h23 := h15 y one ⟨ h3, (oneF M)⟩, 
        have h24 := h15 (𝕊 y) two  ⟨ h20, twoF M⟩, 
        have h35 := h15 y two ⟨ h3, (twoF M)⟩, 
        have h219: ∃(u:M), u ∈ 𝕊 zero:=
          begin
            rw← one_definition,
            use zero,
            rw one_members, 
            use Λ,
            rw zero_definition, 
          end,
        have h91: ((𝕊 y = zero ∨ 𝕊 y = one ∨ 𝕊 y = two) ∧ m = zero) ∨ ¬ (((𝕊 y = zero ∨ 𝕊 y = one ∨ 𝕊 y = two) ∧ m = zero)):=
          begin
            cases h17 with h100 h101,
            {
              cases h21 with h102 h103,
              {
                left,
                exact ⟨ or.inl h102, h100⟩,
              },
              {
                cases h22 with h104 h105,
                {
                  left,
                  exact ⟨ or.inr (or.inl h104), h100⟩,
                },
                {
                  cases h24 with h106 h107,
                  {
                    left,
                    exact ⟨ or.inr (or.inr h106), h100⟩,
                  },
                  {
                    right,
                    intro h108,
                    cases h108 with h109 h110,
                    cases h109 with h111 h112,
                    {
                      contradiction, 
                    },
                    {
                      cases h112 with h113 h114,
                      {
                        contradiction,
                      },
                      {
                        contradiction, 
                      }
                    }
                  }
                }
              }
            },
            {
              right,
              intro h102,
              cases h102 with h103 h104,
              contradiction,
            }   
          end, 
        cases h91 with h92 h93,
        {  
            contradiction, 
        },
        {   
          rw tower_recursion_equation M m y  h3 h2,
          have h8:= mlessthanexpm M (𝕊 y) (successorF M y h3 h2),
          push_neg at h93, 
          rw exp_members at h90,
          have h90copy:= h90,
          cases h90 with a h10,
          cases h10 with h11 h12,
          have h13:= h4 m h5 ⟨ USC a, h11⟩, 
          have h14:= towerincreasing M m h5 y h3 ⟨ USC a, h11⟩, 
          have h15:= towerF M m h5 y h3 ⟨ USC a, h11⟩, 
          have h116:= h42 h18,
          have h110: ((y = zero ∨ y = one ∨ y = two) ∧ m = zero) ∨ ¬((y = zero ∨ y = one ∨ y = two) ∧ m = zero) :=
            begin
              cases h17 with h200 h201,
              { 
                cases h16 with h202 h203,
                {
                  left,
                  exact ⟨ or.inl h202, h200 ⟩, 
                },
                {
                  cases h23 with h204 h205,
                  {
                    left,
                    exact ⟨ or.inr (or.inl h204), h200⟩,
                  },
                  {
                    cases h35 with h206 h207,
                    {
                      left,
                      exact ⟨ or.inr (or.inr h206), h200⟩,
                    },
                    {
                      right,
                      intro h208,
                      cases h208 with h209 h210,
                      cases h209 with h211 h212,
                      {
                        contradiction,
                      },
                      {
                        cases h212 with h213 h214,
                        {
                          contradiction,
                        },
                        {
                          contradiction,
                        }
                      }
                    }
                  }
                }
              },
              {
                right,
                intro h202,
                cases h202 with h203 h204,
                contradiction, 
              }
            end, 
          cases h110 with h111 h112,
          {  --the exceptional cases y=1,2,3 and m = 0
            cases h111 with h113 h114, 
            rw h114 at *,
            cases h113 with h115 h116, 
            {  
              rw h115 at *,
              simp at h13, 
              rw tower_base_equation M zero at *,
              rw one_definition at h93, 
              simp at h93, 
              contradiction, 
            },
            { cases h116 with h117 h118,
              {
                  rw h117 at *,
                  rw two_definition at h7,
                  simp at h7,
                  contradiction,  
              },
              {
                rw h118 at *,
                rw← three_definition,
                rw two_definition,
                have h119:= cardinalsinhabited M two (twoF M),
                rw two_definition at h119,
                have h120:= tower_recursion_equation M zero one  (oneF M) h119, 
                rw h120,
                rw one_definition,
                have h121:= cardinalsinhabited M one (oneF M),
                rw one_definition at h121,
                rw tower_recursion_equation M zero zero (zeroF M) h121,
                rw tower_base_equation M zero,
                rw exp_zero M,
                rw exp_one M,
                rw exp_two M, 
                exact three_lessthan_four M, 
              }
            }
          },
          { --the non-exceptional cases
            have h114:= h13 h112,
            have h115:= noinsertions M y ( 𝕀 M m y) h3 h15 h114,
            have h116:= le_definition (exp M y) (exp M (𝕀 M m y)),
            have h117:= h116.mp  h19,  
            cases h117 with r h118,
            cases h118 with s h119,
            rcases h119 with ⟨ h120, h121, h122⟩, 
            have h130:= mlessthanexpm M (𝕀 M m y) h15 ⟨ s, h121⟩,
            have h131:= finiteexp M (𝕀 M m y) h15 ⟨ s, h121⟩ ,
            have h132:= le_transitive3 M (𝕊 y)(𝕀 M m y)(exp M (𝕀 M m y)) 
                h20 h15 h131  h115 h130, 
            exact h132, 
          }
        }
      end,
    intros y h m h2, 
    rw F_members y at h,
    specialize h (Z_towerstrictlyincreasing M),
    have h200:= h ⟨ base, step⟩,
    rw Z_towerstrictlyincreasing_members at h200,
    cases h200 with h201 h202,
    exact h202 m h2, 
  end


