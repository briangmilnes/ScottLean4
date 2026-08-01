import inf30
-- but not inf29 which has sorry
variables (M:Type) [Model M] (a b x y z u v w X R W κ μ ℓ : M)
open Model 

lemma finitetrichotomy3: ∀ (x y:M), x ∈ 𝔽 → y ∈ 𝔽  → x < y ∨ y ≤ x:=
  begin
    intros x y hx hy,
    have h4:= finitetrichotomy M x hx y hy,
    cases h4 with h5 h6,
    {
      left,
      exact h5,
    },
    {
      cases h6 with h7 h8,
      {
        rw h7 at *,
        right,
        exact le_reflexive M y hy,
      },
      {
        right,
        rw lessthan_definition at h8,
        exact h8.1,
      }
    }
  end

lemma finitetrichotomy4: ∀ (x y:M), x ∈ 𝔽 → y ∈ 𝔽  → x ≤ y ∨ y < x:=
  begin
    intros x y hx hy,
    have h4:= finitetrichotomy M x hx y hy,
    cases h4 with h5 h6,
    {
      left,
      rw lessthan_definition at h5,
      cases h5 with h6 h7,
      exact h6,
    },
    {
      cases h6 with h7 h8,
      {
        rw h7 at *,
        left,
        exact le_reflexive M y hy,
      },
      {
        right,
        exact h8,
      }
    }
  end



lemma ILambda:∀(t:M),t ∈ 𝔽 → 𝕀 M Λ t = Λ:=
  begin
    have base: zero ∈ Z_ILambda M:=
      begin
        rw Z_ILambda_members,
        rw tower_base_equation,
        simp,
        exact zeroF M,
      end,
    have step: ∀ (t:M), t ∈ Z_ILambda M → (∃ (u:M), u ∈ 𝕊 t) → 𝕊 t ∈ Z_ILambda M:=
      begin
        intros t h3 hst,
        rw Z_ILambda_members at h3,
        cases h3 with ht h4,
        rw Z_ILambda_members,
        rw tower_recursion_equation,
        rw h4,
        split,
        {
          exact successorF M t ht hst,
        },
        {
          exact explambda M,
        },
        exact ht,
        exact hst,
      end,
    intros t ht,
    rw F_members at ht,
    specialize ht (Z_ILambda M),
    have h200:= ht ⟨base,step⟩,
    rw Z_ILambda_members at h200,
    exact h200.2,
  end

lemma topmaximal:∀ (m:M), MAXIMAL M m → ∀(n:M), n ∈ 𝔽 → (¬n = zero)→
∀ (q:M), q ∈ Φ M n → exp M q = Λ → ∀ (p:M), p ∈ Φ M n → p ≤ q:=
  begin
    intros m hmax n hn hn2 q h3 h4 p h5,
    have h3copy:= h3,
    have h5copy:= h5,
    rw Phi_members at h3 h5,
    cases h3 with Y h7,
    cases h5 with y h8,
    rcases h7 with ⟨hY, h10, h11⟩,
    rcases h8 with ⟨hy, h20, h21⟩,
    have hp:= PhiF M n p hn h5copy,
    have hq:= PhiF M n q hn h3copy,
    have h30:= finitetrichotomy4 M p q hp hq,
    cases h30 with h31 h32,
    {
      exact h31,
    },
    {
      rw h20 at h32,
      rw h10 at h32,
      have h33:= Iordertwowaystrict M n Y y hn hY hy h32,
      have h34:= noinsertions M Y y hY hy h33,
      have hy2: ¬ y = zero:= 
        begin
          intros h,
          rw h at *,
          have h300:= xnotlessthanzero M Y hY,
          contradiction,
        end,
      have h21copy:= h21,
      rw h20 at h21copy,
      have h35:= ylessthanImy M n hn hn2 y hy hy2 h21copy,
      cases h35 with h36 h37,
      have h38:= noinsertions M y (𝕀 M n y) hy h37 h36,
      have h39:= le_to_inhabited M (𝕊 y)(𝕀 M n y) h38,
      have h40:= successorF M y hy h39,
      have h41:= xlessthansuccessorx M y hy h40,
      have h43:= le_to_inhabited M (𝕊 Y) y h34,
      have h44:= successorF M Y hY h43,
      have h42:= le_transitive3 M (𝕊 Y) y (𝕊 y) h44 hy h40 h34 h41,
      have h46:= tower_recursion_equation M n y hy h39,
      have h56:= tower_recursion_equation M n Y hY h43,
      rw← h20 at h46,
      rw← h10 at h56,
      rw h4 at h56,
      have h58: ∃ (t:M), t ∈ 𝔽  ∧ 𝕊 Y + t = y:= 
        begin
        have h110:= (orderbyaddition M y hy (𝕊 Y) h44).1 h34,
        exact h110,
        end,
      cases h58 with t h59,
      cases h59 with  ht h60,
      have h61:= towerbreakI2 M n (𝕊 Y) hn hn2 h44 t ht,
      rw h60 at h61,
      have h62:= h61 hy,
      rw h56 at h62,
      have h63:= ILambda M t ht,
      rw h63 at h62,
      rw← h20 at h62,
      rw h62 at hp,
      have h64:= cardinalsinhabited M Λ hp,
      cases h64 with x h65,
      have h66:= emptyset_axiom x,
      contradiction,
    }
  end



lemma Phibound: ∀ (m:M), MAXIMAL M m → ∀(n:M), n ∈ 𝔽 → 
∀ (y:M), y ∈ 𝔽 → (∃ (u:M), u ∈ 𝕀 M n y) → 
Nc M (Φ M (𝕀 M n y)) + 𝕋 M (𝕋 M y) = Nc M (Φ M n):=
  begin
    intros m hmax n hn,
    have base: zero ∈ Z_Phibound M m n:=
      begin
        rw Z_Phibound_members,
        rw Tzero,
        rw Tzero,
        rw right_identityNF,
        rw tower_base_equation,
        simp,
        exact zeroF M,
      end,
    have step: ∀ (y:M), y ∈ Z_Phibound M m n → (∃ (u:M), u ∈ (𝕊 y)) → 𝕊 y ∈ Z_Phibound M m n:=
      begin
        intros y h3 hsy,
        rw Z_Phibound_members at *,
        cases h3 with hy h4,
        have h2:= Phifinite M m hmax y hy,
        split,
        {
          exact successorF M y hy hsy,
        },
        {
          intros h6,
          rw tower_recursion_equation at h6,
          have h7:= h6,
          cases h7 with u h8,
          rw exp_members at h8,
          cases h8 with a h9,
          cases h9 with h10 h11,
          have h12:= towerF M n hn y hy ⟨ USC a, h10⟩,
          have h13:= Phifinite M m hmax (𝕀 M n y) h12,
          have h5:= sixpointseven M (𝕀 M n y) h12 h13 h6,
          rw←  tower_recursion_equation at h5,
          have h14: Nc M (Φ M (𝕀 M n y)) + 𝕋 M (𝕋 M y) = (Nc M (Φ M (𝕀 M n (𝕊 y))) + one) + 𝕋 M (𝕋 M y):=
            begin
              rw h5,
            end,
          have h15: Nc M (Φ M (𝕀 M n y)) + 𝕋 M (𝕋 M y) = (Nc M (Φ M (𝕀 M n (𝕊 y))) + (𝕋 M (𝕋 M y) + one)):=
            begin
              rw h14,
              rw associativityNF,
              have h16: one+ 𝕋 M (𝕋 M y) = 𝕋 M (𝕋 M y) + one,
                begin
                  rw commutativityNF,
                end,
              rw h16,
            end,
          rw← successorisplusone at h15,
          rw  Tsuccessor,
          rw Tsuccessor,
          rw← h15,
          have h20:= h4 ⟨ USC a,h10⟩,
          exact h20,
          exact Tfinite M y hy,
          have h21: ∃(u:M), u ∈ 𝕊 (𝕋 M y):= 
            begin
              rw←  Tsuccessor,
              have hsyf:= successorF M y hy hsy,
              have h400:= Tfinite M (𝕊 y) hsyf,
              have h401:= cardinalsinhabited M (𝕋 M (𝕊 y)) h400,
              exact h401,
              exact hy,
              exact hsy,
            end,
          exact h21,
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
    specialize hy ( Z_Phibound M m n),
    have h200:= hy ⟨base,step⟩,
    rw Z_Phibound_members at h200,
    exact h200.2, 
  end

lemma Jcardinality2: ∀ (k:M), k ∈ 𝔽 → Nc M (𝕁 M k) = 𝕋 M (𝕋 M k):=
  begin
    intros k hk,
    have h3:= Jcardinality M k hk,
    have h4:= xinNcx M (𝕁 M k),
    have h10:= Jfinite M k hk,
    have h11:= finitecardinals3 M (𝕁 M k) h10,
    have h12:= Tfinite M k hk,
    have h13:= Tfinite M (𝕋 M k) h12,
    have h14: 𝕁 M k ∈ (Nc M (𝕁 M k) ∩ 𝕋 M (𝕋 M k)):=
      begin
        rw intersection_axiom,
        exact ⟨ h4, h3⟩,
      end,
    have h5:= cardinalsdisjoint M (Nc M (𝕁 M k)) (𝕋 M (𝕋 M k)) (𝕁 M k) h11 h13 h14,
    exact h5,
  end

lemma finitecardinals4: ∀ (x y:M), x ∈ FINITE M → y ∈ FINITE M →
similar M x y → Nc M x = Nc M y:=
  begin
    intros x y hx hy hsim,
    have h3:= xinNcx M x,
    have h4:= xinNcx M y,
    have h10:= finitecardinals3 M x hx,
    have h11:= finitecardinals3 M y hy,
    have h5:= finitecardinals0 M (Nc M x) x y h10 h3 hsim,
    have h12: y ∈ (Nc M x) ∩ (Nc M y):=
      begin
        rw intersection_axiom,
        exact ⟨ h5,h4⟩,
      end,
    have h6:= cardinalsdisjoint M (Nc M x)(Nc M y) y h10 h11 h12,
    exact h6,
  end 

lemma Jhelper: ∀ (k:M), k∈ 𝔽 → 𝕊 k ∈ 𝔽 → Jbar M k = 𝕁 M (𝕊 k):=
  begin
    intros k hk hsk,
    rw full_extensionality,
    intros x,
    have h10:= lessthansuccessor2b M x k,
    rw Jbar_members,
    rw J_members,
    split,
    {
      intros h,
      cases h with hx h2,
      split,
      {
        exact hx,
      },
      {
        have h3:= xlessthansuccessorx M k hk hsk,
        have h4:= le_transitive3 M x k (𝕊 k) hx hk hsk h2 h3,
        exact h4,
      }
    },
    {
      intros h,
      cases h with hx h20,
      split,
      {
        exact hx,
      },
      {
        have h21:= h10 hx hk (cardinalsinhabited M (𝕊 k) hsk),
        rw lessthan_definition at h20,
        cases h20 with h22 h23,
        rw h21 at h22,
        cases h22 with h24 h25,
        {
          exact h24,
        },
        {
          contradiction,
        }
      }
    }
  end

lemma lessthansum: ∀ (q:M),q ∈ 𝔽 → ∀ (n p: M), n ∈ 𝔽 → p ∈ 𝔽 → 
n = p+q → zero < q → p < n:=
  begin
    have base: zero ∈ Z_lessthansum M:=
      begin
        rw Z_lessthansum_members,
        split,
        {
          exact zeroF M,
        },
        {
          intros n p hn hp h4 h5,
          have h6:= xnotlessthanx M zero (zeroF M),
          contradiction,
        }
      end,
    have step: ∀ (q:M), q ∈ Z_lessthansum M → (∃(u:M),u ∈ 𝕊 q) → 𝕊 q ∈ Z_lessthansum M:=
      begin
        intros q h3 hsq,
        rw Z_lessthansum_members at h3,
        cases h3 with hq h4,
        rw Z_lessthansum_members,
        split,
        {
          exact successorF M q hq hsq,
        },
        {
          intros n p hn hp h5 h6,
          rw successor_shift M p q at h5,
          have h30:= cardinalsinhabited M n hn,
          cases h30 with u h31,
          rw h5 at h31,
          rw addition_members at h31,
          cases h31 with a h32,
          cases h32 with b h33,
          have hsp:= h33.2.1,
          have h7:= finitetrichotomy M q hq zero (zeroF M),
          cases h7 with h8 h9,
          {
            have h10:= xnotlessthanzero M q hq,
            contradiction,
          },
          {
            cases h9 with h11 h12,
            {
              rw h11 at *,
              rw← successor_shift at h5,
              have h12:= one_definition,
              rw←h12 at h5,
              rw← successorisplusone at h5,
              rw h5 at hn,
              have h13:= xlessthansuccessorx M p hp hn, 
              rw← h5 at h13,
              exact h13,
            },
            {
              have hspf:= successorF M p hp ⟨ a, hsp⟩,
              have h14:= h4 n (𝕊 p) hn hspf h5 h12,
              have h15:= xlessthansuccessorx M p hp hspf,
              have h16:= lessthan_transitive M p (𝕊 p) n hp hspf hn h15 h14,
              exact h16,
            }
          }       
        }
      end,
    intros q hq,
    rw F_members at hq,
    specialize hq (Z_lessthansum M),
    have h200:= hq ⟨ base, step⟩,
    rw Z_lessthansum_members at h200,
    exact h200.2,
  end

lemma gsim: ∀ (m:M), MAXIMAL M m →
∃ (Y:M), similar M (Jbar M Y ) (Φ M one) ∧ 
Y∈ 𝔽 ∧ 𝕀 M one Y ∈ Φ M one ∧ exp M (𝕀 M one Y) = Λ := 
  begin
    intros m hmax, 
    set g:= gNbound M with gdef,
    have h6:= one_neq_zero M,
    have h5:= maximalPhi M m one hmax (oneF M) h6,
    cases h5 with q h7,
    rcases h7 with ⟨ hq, h8, h9, hmaximal⟩,
    have h10:= h8,
    rw Phi_members at h10,
    cases h10 with Y h11,
    use Y,
    have h900: similarity M g (Jbar M Y ) (Φ M one):=
      begin
        have hRel: Rel g:=
          begin
            rw Rel_definition,
            intros z hg,
            rw gdef at hg,
            rw gNbound_members at hg,
            cases hg with a h5,
            cases h5 with b h6,
            use a, use b,
            exact h6.1,
          end,
        have h4: range g = Φ M one:=
          begin
            rw full_extensionality,
            intros t,
            rw range_axiom g hRel,
            rw Phi_members,
            split,
            {
              intros h,
              cases h with x h2,
              rw gdef at h2,
              rw gNbound_members at h2,
              cases h2 with a h5,
              cases h5 with b h6,
              rcases h6 with ⟨ h7, ha,h9,h20⟩,
              rw ordered_pair_equality at h7,
              cases h7 with h10 h11,
              rw h10 at *,
              rw h11 at *,
              use a,
              split,
              {
                exact ha,
              },
              {
                split,
                {
                  rw sym,
                  exact h9,
                },
                {
                  rw← h9,
                  rw Phi_members at h20,
                  cases h20 with y h21,
                  rcases h21 with ⟨ hy, h23, h24⟩,
                  rw h23 at h24,
                  rw← h9 at h23,
                  rw← h23 at h24,
                  have h26:= IinF M one (oneF M) a ha h24,
                  exact cardinalsinhabited M (𝕀 M one a) h26,
                }
              }
            },
            {
              intros h,
              cases h with y h30,
              rcases h30 with ⟨ hy, h32, h33⟩,
              rw h32 at h33,
              use y,
              rw gdef,
              rw gNbound_members,
              use y, use t,
              simp,
              split,
              {
                exact hy,
              },
              {
                split,
                {
                  rw h32,
                },
                {
                  rw Phi_members,
                  use y,
                  rw←  h32 at h33,
                  exact ⟨ hy, h32, h33⟩,
                }
              }
            }
          end,
        
        rcases h11 with ⟨ hY, h12, h13⟩,
        have hYPhi: ∀ (y:M), y ∈ 𝔽 → (𝕀 M one y ∈ Φ M one ↔ y ≤ Y):=
          begin
            intros y hy,
            split,
            {
              -- left to right,
              intros h,
              have h14:= hmaximal (𝕀 M one y) h,
              rw h12 at h14,
              have h15:= Iordertwoway M one y Y (oneF M) hy hY h14,
              exact h15,
            },
            {
              -- right to left
              intros h20,
              rw Phi_members,
              use y,
              simp,
              split,
              {
                exact hy,
              },
              {
                rw letolessthan M y Y hy hY at h20,
                cases h20 with h21 h22,
                {
                  have h30:= hq,
                  rw h12 at h30,
                  have h23:= Iorder M Y hY y one hy (oneF M) h30 h21,
                  have h25:= h23,
                  rw lessthan_definition at h25,
                  have h24:= le_to_inhabited M (𝕀 M one y)(𝕀 M one Y) h25.1,
                  exact h24,
                },
                {
                  rw h22 at *,
                  rw← h12,
                  exact h13,
                }   
              }
            }
          end,
        have h40: similarity M g (Jbar M Y ) (Φ M one):=
          begin
            unfold similarity,
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
                    intros x y h20,
                    cases h20 with h31 h32,
                    rw Jbar_members at h31,
                    cases h31 with hx h22,
                    have h33:=hYPhi x hx,
                    rw← h33 at h22,
                    rw gdef at h32,
                    rw gNbound_members at h32,
                    cases h32 with a h33,
                    cases h33 with b h34,
                    rcases h34 with ⟨ h35, h36, h37⟩,
                    rw ordered_pair_equality at h35,
                    rw← h35.1 at *,
                    rw← h35.2 at *,
                    exact h37.2,
                  },
                  {
                    split,
                    {
                      intros x y z h,
                      rcases h with ⟨ h40, h41, h42⟩,
                      rw gdef at h41 h42,
                      rw gNbound_members at h41 h42,
                      cases h42 with a h45,
                      cases h45 with b h46,
                      cases h41 with A h47,
                      cases h47 with B h48,
                      rcases h46 with ⟨ h50, h51, h52⟩,
                      rcases h48 with ⟨ h60, h61, h62⟩,
                      rw ordered_pair_equality at h50 h60,
                      rw← h50.1 at *,
                      rw← h50.2 at *,
                      rw← h60.1 at *,
                      rw← h60.2 at *, 
                      cases h52 with h53 h54,
                      cases h62 with h63 h64,
                      rw←h53,
                      rw← h63, 
                    },
                    {
                      intros x h70,
                      rw Jbar_members at h70,
                      cases h70 with hx h71,
                      have h72:= hYPhi x hx,
                      rw← h72 at h71,
                      use 𝕀 M one x,
                      split,
                      {
                        exact h71,
                      },
                      {
                        rw gdef,
                        rw gNbound_members,
                        use x,
                        use 𝕀 M one x,
                        simp,
                        exact ⟨ hx, h71⟩,
                      }
                    }
                  }
                }
              },
              {
                split,
                {
                  intros x u y h,
                  rcases h with ⟨h80, h90, h82⟩,
                  rw Jbar_members at h82,
                  cases h82 with hx h83,
                  rw gdef at h80 h90,
                  rw gNbound_members at h80 h90,
                  cases h80 with a h81,
                  cases h81 with b h82,
                  cases h90 with A h91,
                  cases h91 with B h92,
                  rcases h82 with ⟨ h83, h84, h85⟩,
                  rcases h92 with ⟨ h93, h94, h95⟩,
                  rw ordered_pair_equality at h83 h93,
                  rw← h83.1 at *,
                  rw← h83.2 at *,
                  rw← h93.1 at *,
                  rw← h93.2 at *,
                  cases h85 with h86 h87,
                  cases h95 with h96 h97,
                  have h98:= Ioneone M one x u (oneF M) h84 h94,
                  rw h86 at h98,
                  rw h96 at h98,
                  simp at h98,
                  apply h98,
                  rw Phi_members at h97,
                  cases h97 with t h100,
                  rcases h100 with ⟨ h101, h102,h103⟩,
                  rw h102 at h103,
                  have h104:= towerF M one (oneF M) t h101 h103,
                  rw h102,
                  exact h104,
                },
                {
                  intros x y h,
                  cases h with h110 h111,
                  rw gdef at h110,
                  rw gNbound_members at h110,
                  cases h110 with a h111,
                  cases h111 with b h112,
                  rcases h112 with ⟨ h113, hx, h114⟩,
                  rw ordered_pair_equality at h113,
                  rw← h113.1 at *,
                  rw← h113.2 at *,
                  cases h114 with h115 h116,
                  rw Jbar_members,
                  split,
                  {
                    exact hx,
                  },
                  {
                    apply (hYPhi x hx).1,
                    rw h115,
                    exact h116,
                  }
                }
              }
            },
            {
              unfold onto,
              intros y h,
              have h300:= h,
              rw Phi_members at h,
              cases h with t h120,
              rcases h120 with ⟨ ht, h121, h122⟩,
              rw h121 at h122,
              have h124:= IinF M one (oneF M) t ht h122,
              use t,
              have h125:= hYPhi t ht,
              rw Jbar_members,
              rw h121 at h300,
              rw h125 at h300,
              split,
              {
                exact ⟨ ht, h300⟩,
              },
              {
                rw gdef,
                rw gNbound_members,
                use t, use y,
                simp,
                rw sym at h121,
                split,
                {
                  exact ht,
                },
                {
                  split,
                  {
                    exact h121,
                  },
                  {
                    rw Phi_members,
                    use t,
                    rw sym at h121,
                    rw h121,
                    simp,
                    exact ⟨ ht, h122⟩,
                  }
                }
              }
            }
          end,
        exact h40,
      end,
    split,
    {
      unfold similar,
      use g,
      exact h900,
    },
    {
      rcases h11 with ⟨ hY, h301, h302⟩,
      split,
      {
        exact hY,
      },
      {
        split,
        {
          rw←  h301,
          exact h8,
        },
        {
          rw← h301,
          exact h9,
        }
      }
    }
  end

lemma Nbound: ∀ (m:M), MAXIMAL M m →
Nc M (Φ M one) ≤ (𝕋 M (𝕋 M m)) + one:=
  begin
    intros m hmax,
    set g:= gNbound M with gdef,
    have hRel: Rel g:=
      begin
        rw Rel_definition,
        intros z hg,
        rw gdef at hg,
        rw gNbound_members at hg,
        cases hg with a h5,
        cases h5 with b h6,
        use a, use b,
        exact h6.1,
      end,
    have h4: range g = Φ M one:=
      begin
        rw full_extensionality,
        intros t,
        rw range_axiom g hRel,
        rw Phi_members,
        split,
        {
          intros h,
          cases h with x h2,
          rw gdef at h2,
          rw gNbound_members at h2,
          cases h2 with a h5,
          cases h5 with b h6,
          rcases h6 with ⟨ h7, ha,h9,h20⟩,
          rw ordered_pair_equality at h7,
          cases h7 with h10 h11,
          rw h10 at *,
          rw h11 at *,
          use a,
          split,
          {
            exact ha,
          },
          {
            split,
            {
              rw sym,
              exact h9,
            },
            {
              rw← h9,
              rw Phi_members at h20,
              cases h20 with y h21,
              rcases h21 with ⟨ hy, h23, h24⟩,
              rw h23 at h24,
              rw← h9 at h23,
              rw← h23 at h24,
              have h26:= IinF M one (oneF M) a ha h24,
              exact cardinalsinhabited M (𝕀 M one a) h26,
            }
          }
        },
        {
          intros h,
          cases h with y h30,
          rcases h30 with ⟨ hy, h32, h33⟩,
          rw h32 at h33,
          use y,
          rw gdef,
          rw gNbound_members,
          use y, use t,
          simp,
          split,
          {
            exact hy,
          },
          {
            split,
            {
              rw h32,
            },
            {
              rw Phi_members,
              use y,
              rw←  h32 at h33,
              exact ⟨ hy, h32, h33⟩,
            }
          }
        }
      end,
    have h6:= one_neq_zero M,
    have h5:= maximalPhi M m one hmax (oneF M) h6,
    cases h5 with q h7,
    rcases h7 with ⟨ hq, h8, h9, hmaximal⟩,
    have h10:= h8,
    rw Phi_members at h10,
    cases h10 with Y h11,
    rcases h11 with ⟨ hY, h12, h13⟩,
    have hYPhi: ∀ (y:M), y ∈ 𝔽 → (𝕀 M one y ∈ Φ M one ↔ y ≤ Y):=
      begin
        intros y hy,
        split,
        {
          -- left to right,
          intros h,
          have h14:= hmaximal (𝕀 M one y) h,
          rw h12 at h14,
          have h15:= Iordertwoway M one y Y (oneF M) hy hY h14,
          exact h15,
        },
        {
          -- right to left
          intros h20,
          rw Phi_members,
          use y,
          simp,
          split,
          {
            exact hy,
          },
          {
            rw letolessthan M y Y hy hY at h20,
            cases h20 with h21 h22,
            {
              have h30:= hq,
              rw h12 at h30,
              have h23:= Iorder M Y hY y one hy (oneF M) h30 h21,
              have h25:= h23,
              rw lessthan_definition at h25,
              have h24:= le_to_inhabited M (𝕀 M one y)(𝕀 M one Y) h25.1,
              exact h24,
            },
            {
              rw h22 at *,
              rw← h12,
              exact h13,
            }   
          }
        }
      end,
    have h40: similarity M g (Jbar M Y ) (Φ M one):=
      begin
        unfold similarity,
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
                intros x y h20,
                cases h20 with h31 h32,
                rw Jbar_members at h31,
                cases h31 with hx h22,
                have h33:=hYPhi x hx,
                rw← h33 at h22,
                rw gdef at h32,
                rw gNbound_members at h32,
                cases h32 with a h33,
                cases h33 with b h34,
                rcases h34 with ⟨ h35, h36, h37⟩,
                rw ordered_pair_equality at h35,
                rw← h35.1 at *,
                rw← h35.2 at *,
                exact h37.2,
              },
              {
                split,
                {
                  intros x y z h,
                  rcases h with ⟨ h40, h41, h42⟩,
                  rw gdef at h41 h42,
                  rw gNbound_members at h41 h42,
                  cases h42 with a h45,
                  cases h45 with b h46,
                  cases h41 with A h47,
                  cases h47 with B h48,
                  rcases h46 with ⟨ h50, h51, h52⟩,
                  rcases h48 with ⟨ h60, h61, h62⟩,
                  rw ordered_pair_equality at h50 h60,
                  rw← h50.1 at *,
                  rw← h50.2 at *,
                  rw← h60.1 at *,
                  rw← h60.2 at *, 
                  cases h52 with h53 h54,
                  cases h62 with h63 h64,
                  rw←h53,
                  rw← h63, 
                },
                {
                  intros x h70,
                  rw Jbar_members at h70,
                  cases h70 with hx h71,
                  have h72:= hYPhi x hx,
                  rw← h72 at h71,
                  use 𝕀 M one x,
                  split,
                  {
                    exact h71,
                  },
                  {
                    rw gdef,
                    rw gNbound_members,
                    use x,
                    use 𝕀 M one x,
                    simp,
                    exact ⟨ hx, h71⟩,
                  }
                }
              }
            }
          },
          {
            split,
            {
              intros x u y h,
              rcases h with ⟨h80, h90, h82⟩,
              rw Jbar_members at h82,
              cases h82 with hx h83,
              rw gdef at h80 h90,
              rw gNbound_members at h80 h90,
              cases h80 with a h81,
              cases h81 with b h82,
              cases h90 with A h91,
              cases h91 with B h92,
              rcases h82 with ⟨ h83, h84, h85⟩,
              rcases h92 with ⟨ h93, h94, h95⟩,
              rw ordered_pair_equality at h83 h93,
              rw← h83.1 at *,
              rw← h83.2 at *,
              rw← h93.1 at *,
              rw← h93.2 at *,
              cases h85 with h86 h87,
              cases h95 with h96 h97,
              have h98:= Ioneone M one x u (oneF M) h84 h94,
              rw h86 at h98,
              rw h96 at h98,
              simp at h98,
              apply h98,
              rw Phi_members at h97,
              cases h97 with t h100,
              rcases h100 with ⟨ h101, h102,h103⟩,
              rw h102 at h103,
              have h104:= towerF M one (oneF M) t h101 h103,
              rw h102,
              exact h104,
            },
            {
              intros x y h,
              cases h with h110 h111,
              rw gdef at h110,
              rw gNbound_members at h110,
              cases h110 with a h111,
              cases h111 with b h112,
              rcases h112 with ⟨ h113, hx, h114⟩,
              rw ordered_pair_equality at h113,
              rw← h113.1 at *,
              rw← h113.2 at *,
              cases h114 with h115 h116,
              rw Jbar_members,
              split,
              {
                exact hx,
              },
              {
                apply (hYPhi x hx).1,
                rw h115,
                exact h116,
              }
            }
          }
        },
        {
          unfold onto,
          intros y h,
          have h300:= h,
          rw Phi_members at h,
          cases h with t h120,
          rcases h120 with ⟨ ht, h121, h122⟩,
          rw h121 at h122,
          have h124:= IinF M one (oneF M) t ht h122,
          use t,
          have h125:= hYPhi t ht,
          rw Jbar_members,
          rw h121 at h300,
          rw h125 at h300,
          split,
          {
            exact ⟨ ht, h300⟩,
          },
          {
            rw gdef,
            rw gNbound_members,
            use t, use y,
            simp,
            rw sym at h121,
            split,
            {
              exact ht,
            },
            {
              split,
              {
                exact h121,
              },
              {
                rw Phi_members,
                use t,
                rw sym at h121,
                rw h121,
                simp,
                exact ⟨ ht, h122⟩,
              }
            }
          }
        }
      end,
    have h41: ¬ Y = zero:=
      begin
        intros h130,
        rw h130 at *,
        rw tower_base_equation at h12,
        rw h12 at h9,
        rw exp_one at h9,
        have h131:= twoF M,
        have h132:= cardinalsinhabited M two (twoF M),
        rw h9 at h132,
        cases h132 with x h133,
        have h134:= emptyset_axiom x,
        contradiction,
      end,
    rw h12 at h13,
    have h42:= ylessthanImy M one (oneF M) h6 Y hY h41 h13,
    cases h42 with h43 h44,
    have h45:= noinsertions M Y (𝕀 M one Y) hY h44 h43,
    have h46:= le_to_inhabited M (𝕊 Y)(𝕀 M one Y) h45,
    have h47:= successorF M Y hY h46,
    --have h48:= Jsuccessor M Y hY h47,
    have h49:= Phifinite M m hmax one (oneF M),
    have h50:= Jbarfinite M  Y hY,
    have h51: similar M (Jbar M Y)(Φ M one):=
      begin
        unfold similar,
        use g,
        exact h40,
      end,
    have h52:= xinNcx M (Jbar M Y),
    have h53:= xinNcx M (Φ M one),
    have h60:= finitecardinals4 M (Jbar M Y)(Φ M one) h50 h49 h51,
    have h61:= Jcardinality2 M (𝕊 Y) h47,
    have h62:= Jhelper M Y hY h47,
    rw← h62 at h61,
    have h70:= hmax,
    unfold MAXIMAL at h70,
    cases h70 with hm h71,
    have h72:= h71 Y hY,
    have h73:= (Tlessthanorequal M Y m hY hm).1 h72,
    have h74:= Tfinite M Y hY,
    have h75:= Tfinite M m hm,
    have h76:= (Tlessthanorequal M (𝕋 M Y)(𝕋 M m)  h74 h75).1 h73,
    have h90:= Tfinite M (𝕋 M Y) h74,
    have h81:= Tsuccessor M Y hY h46,
    have h82: ∃ (u:M), u ∈ 𝕊 (𝕋 M Y):= 
      begin
        have h229: ¬ 𝕋 M Y = zero:=
          begin
            intros h,
            rw← Tzero at h, 
            have h230:= Toneone M Y zero hY  (zeroF M) h,
            contradiction,
          end,
        have h230:= ylessthanImy M one (oneF M)(one_neq_zero M) Y hY h41 h13,
        cases h230 with h232 h2330,
        have h233:= Tlessthan M Y (𝕀 M one Y) hY h2330,
        rw h233 at h232,
        have h234:= lessthan_to_inhabited M (𝕋 M Y)(𝕋 M (𝕀 M one Y)) h232,
        have h235:= Tfinite M (𝕀 M one Y ) h44,
        have h236:= noinsertions M (𝕋 M Y)(𝕋 M (𝕀 M one Y)) h74 h235 h232,
        have h237:= le_to_inhabited M (𝕊 (𝕋 M Y))(𝕋 M (𝕀 M one Y)) h236,
        exact h237,
      end,
    have h83:= Tsuccessor M (𝕋 M Y) h74 h82,
    rw←  h81 at h83, 
    rw sym at h83,
    have h77:= Tfinite M (𝕋 M m) h75,
    have h78:= cardinalsinhabited M (𝕋 M (𝕋 M m)) h77,
    have h79: (∃ (w : M), w ∈ 𝕊 (𝕋 M (𝕋 M m))):= 
      begin
        have h430:= TmlessthanM M m hmax,
        have h429:= Tlessthan M (𝕋 M m) m (Tfinite M m hm) hm,
        rw h429 at h430,
        have h431:= noinsertions M (𝕋 M (𝕋 M m)) (𝕋 M m) h77 h75 h430,
        have h432:= le_to_inhabited M (𝕊 (𝕋 M (𝕋 M m))) (𝕋 M m) h431,
        exact h432,
      end,
    have h80:= (ordersuccessor M (𝕋  M (𝕋 M Y) )(𝕋 M (𝕋 M m)) h90 h77 h79).1 h76,
    rw h83 at h80,
    rw← h61 at h80,
    rw h60 at h80, 
    rw successorisplusone at h80,
    exact h80,
  end

lemma NcPhi: ∀ (m:M), MAXIMAL M m → ∀ (n:M), n ∈ 𝔽 → zero < Nc M (Φ M n):=
  begin
    intros m hmax n hn,
    have h3:= cardinalsinhabited M n hn,
    have h2:= minPhim M n h3,
    have h5:= Phifinite M m hmax n hn,
    have h6: one ≤ Nc M (Φ M n):=
      begin
        rw le_definition,
        use single n,
        use Φ M n,
        split,
        {
          rw one_members,
          use n,
        },
        {
          split,
          {
            exact xinNcx M (Φ M n),
          },
          {
            split,
            {
              rw subset_definition,
              intros t ht,
              rw singleton1 at ht,
              rw ht,
              exact h2,
            },
            {
              rw full_extensionality,
              intros t,
              rw binary_union_axiom,
              rw minus_members,
              rw singleton1,
              split,
              {
                intros h,
                have ht:= PhiF M n t hn h,
                have h30:= Fdecidable M t n ht hn,
                cases h30 with h31 h32,
                {  
                  left,
                  exact h31,
                },
                {
                  right,
                  exact ⟨ h, h32⟩,
                }
              },
              {
                intros h,
                cases h with h50 h51,
                {
                  rw h50,
                  exact h2,
                },
                {
                  cases h51 with h52 h53,
                  exact h52,
                }
              }
            }
          }
        }
      end,
    have h70:= zero_lessthan_one M,
    have h71:= finitecardinals3 M (Φ M n) h5,
    have h80:= le_transitive2 M zero one (Nc M (Φ M n)) (zeroF M)(oneF M) h71 h70 h6,
    exact h80,
  end

lemma TNlessthanN: ∀ (m:M), MAXIMAL M m →
𝕋 M (Nc M (Φ M one)) < (Nc M (Φ M one)):=
  begin
    intros m hmax,
    set N:= (Nc M (Φ M one)) with Ndef,
    have h199:= Phifinite M m hmax one (oneF M),
    have h200:= finitecardinals3 M (Φ M one) h199,
    have hN := h200,
    rw← Ndef at hN,
    have h3:= one_neq_zero M,
    have h4:= maximalPhi M m one hmax (oneF M) h3,
    cases h4 with q h5,
    rcases h5 with ⟨ hq, h6, h7, h8 ⟩,
    have h20:= exp_one M,
    have h10: ¬ q= one:= 
      begin
        intros h,
        rw← h at h20,
        rw h20 at h7,
        rw full_extensionality at h7,
        specialize h7 {zero, one},
        rw two_members at h7,
        cases h7 with h14 h16,
        have h30: (∃ (a b : M), ¬a = b ∧ {zero,one} = {a,b}):=
          begin
            use zero, use one,
            simp,
            rw sym,
            exact h3,
          end,
        have h31:= h14 h30,
        have h32:= emptyset_axiom {zero,one},
        contradiction,
      end, 
    have h9:= sevenpointtwoB M m hmax one q (oneF M) h3 h6 h8 h10,
    rw Tone at h9,
    rw← Ndef at h9,
    have h21:= expTinhabited M q hq,
    have h22:= minPhim M (exp M (𝕋 M q)) h21,
    have h23:= xinNcx M (exp M (𝕋 M q)),
    have h25:= Tfinite M  N hN,
    have h27: 𝕋 M N < N ∨ N ≤ 𝕋 M N:=
      finitetrichotomy3 M (𝕋 M N) N h25 hN,
    cases h27 with h28 h29,
    {
      exact h28,
    },
    { --case N ≤ 𝕋 M N
      have h30: Nc M (Φ M (exp M (𝕋 M q))) ∈ 𝔽 := 
        begin
          have h50:= Phifinite M m hmax (exp M (𝕋 M q)) (expTinF M q hq),
          have h51:= finitecardinals3 M ( Φ M (exp M (𝕋 M q))) h50,
          exact h51,
        end,
      have h31: zero < Nc M (Φ M (exp M (𝕋 M q))):=
        begin
          have h40:= NcPhi M m hmax (exp M (𝕋 M q)),
          apply h40,
          exact expTinF M q hq,
        end,
      have hTN:= Tfinite M N hN,
      set x:= Nc M (Φ M (exp M (𝕋 M q))) with xdef,
      have h32:= lessthansum M x h30 N (𝕋 M N) hN hTN h9 h31,
      exact h32,
    }
  end

lemma Yunique: ∀ (m:M), MAXIMAL M m →
∀ (Y Z:M), Y ∈ 𝔽 → Z ∈ 𝔽 → 𝕀 M one Y ∈ Φ M one → 
𝕀 M one Z ∈ Φ M one →
exp M (𝕀 M one Y) = Λ →
exp M (𝕀 M one Z) = Λ → Y = Z:=
  begin
    intros m hmax Y Z hY hZ h3 h4 h5 h6,
    have h7:= topmaximal M m hmax one (oneF M)(one_neq_zero M) (𝕀 M one Y) h3 h5,
    have h8:= topmaximal M m hmax one (oneF M)(one_neq_zero M) (𝕀 M one Z) h4 h6,
    have h9:= h7 (𝕀 M one Z) h4,
    have h10:= h8 (𝕀 M one Y) h3,
    have h20:= PhiF M one (𝕀 M one Y) (oneF M) h3,
    have h21:= PhiF M one (𝕀 M one Z) (oneF M) h4,
    have h11:= finitetrichotomy2 M (𝕀 M one Y)(𝕀 M one Z) h20 h21 h10 h9,
    have h30:= Ioneone M one Y Z (oneF M) hY hZ h20 h11,
    exact h30,
  end

#axioms_all