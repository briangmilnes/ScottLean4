import inf31 ChurchNumbers12
-- but not inf29 which has sorry
variables (M:Type) [Model M] (a b x y z u v w X R W κ μ ℓ : M)
open Model 
-- formalize work on Church numbers done November 2025

--FC M t is the Church number corresponding to Frege number t
--its graph is the inverse of ChurchFrege
--We need some basic lemmas about FC.


lemma FCmaps: ∀ (x: M), x ∈ 𝔽 → ∃(y:M),‹y,x › ∈ ChurchFrege M
∧ ∀ (z:M), ‹z,x› ∈ ChurchFrege M → z = y:=
  begin
    have base: zero ∈ Z_FCmaps M:=
      begin
        rw Z_FCmaps_members,
        split,
        {
          exact zeroF M,
        },
        {
          use ChurchZero,
          split,
          {
            have h4:= ChurchFrege0 M,
            exact h4,
          },
          {
            intros z h,
            have h5:= ChurchFrege2 M z zero h,
            cases h5 with h6 h7,
            {
              exact h6.1,
            },
            {
              cases h7 with t h8,
              cases h8 with r h9,
              have h10:= h9.2.2,
              have h11:= Fregesuccessoromits0 M r,
              rw h10 at h11,
              contradiction,
            }
          }
        }
      end,
    have step: ∀ (x:M),x ∈ Z_FCmaps M → (∃ (u:M),u ∈ 𝕊 x) → 𝕊 x ∈ Z_FCmaps M:=
      begin
        intros x h hsx,
        rw Z_FCmaps_members,
        rw Z_FCmaps_members at h,
        cases h with hx h4,
        cases h4 with y h5,
        cases h5 with h6 h7,
        split,
        {
          exact successorF M x hx hsx,
        },
        {
          use S y,
          have h8:= ChurchFrege1 M y x h6 (successorF M x hx hsx),
          split,
          {
             exact h8,
          },
          {
            intros z h9,
            have h10:= ChurchFrege3 M z x hx h9,
            cases h10 with p h11,
            cases h11 with h12 h13,
            rw h13 at *,
            have h14:= h7 p h12,
            rw h14, 
          }
        }
      end,
    intros x hx,
    rw F_members at hx,
    specialize hx (Z_FCmaps M),
    have h200:= hx ⟨base,step⟩,
    rw Z_FCmaps_members at h200,
    exact h200.2,
  end

lemma FCmaps2:∀ (x: M), x ∈ 𝔽 → ‹FC M x,x › ∈ ChurchFrege M :=
  begin
    intros x hx,
    unfold FC,
    set f := inv (ChurchFrege M) with fdef,
    have h2:= Apmaps2 M 𝔽 ℕℕ f,
    have h3: f ∈ FUNC:= 
      begin
        rw FUNC_members,
        intros t y z h19 h20,
        rw fdef at h19 h20,
        rw inverse_axiom2 at h19 h20,
        have h23:= ChurchFrege_domainrange M z t h20,
        cases h23 with hz ht,
        have h21:= FCmaps M t ht,
        cases h21 with Y h22,
        cases h22 with h23 h24,
        have h25:= h24 z h20,
        have h26:= h24 y h19,
        rw h25,
        rw h26,
        exact ChurchFregeRel M,
        exact ChurchFregeRel M,
      end,
    have h4: maps M  f 𝔽 ℕℕ:=
      begin
        unfold maps,
        split,
        {
          rw fdef,
          have h4:= inverse_axiom1 (ChurchFrege M) (ChurchFregeRel M),
          exact h4,
        },
        {
          split,
          {
            intros x y h,
            cases h with hx h5,
            rw fdef at h5,
            rw inverse_axiom2 at h5,
            have h6:= ChurchFrege_domainrange M y x h5,
            exact h6.1,
            exact ChurchFregeRel M,
          },
          {
            split,
            {
              intros x y z h,
              cases h with hx h8,
              cases h8 with h9 h10,
              have h11:= h3,
              rw FUNC_members at h11,
              have h12:= h11 x y z h9 h10,
              exact h12,
            },
            {
              intros x hx,
              have h18:= FCmaps M x hx,
              cases h18 with y h19,
              use y,
              cases h19 with h20 h21,
              have h22:= ChurchFrege_domainrange M y x h20,
              cases h22 with hy hx2,
              split,
              {
                exact hy,
              },
              {
                rw fdef,
                rw inverse_axiom2,
                exact h20,
                exact ChurchFregeRel M,
              }
            }
          }
        }
      end,
    have h5:=  h2 x h4 h3 hx,
    rw fdef at h5,
    rw inverse_axiom2 at h5,
    rw fdef,
    exact h5,
    exact ChurchFregeRel M,
  end 

lemma FCzero: FC M zero = ChurchZero:=
  begin
    have h2:= FCmaps2 M zero (zeroF M),
    have h3:= ChurchFrege0 M,
    have h4:= FCmaps M zero (zeroF M),
    cases h4 with y h5,
    cases h5 with h6 h7,
    have h8:= h7 ChurchZero h3,
    have h9:= h7 (FC M zero) h2,
    rw h8 at *,
    rw h9 at *,
  end

lemma FCsuccessor: ∀ (x:M), x ∈ 𝔽 → 𝕊 x ∈ 𝔽 → FC M (𝕊 x) = S (FC M x):=
  begin
    intros x hx hsx,
    have h3:= FCmaps2 M x hx,
    have h4:= FCmaps2 M (𝕊 x) hsx,
    have h5:= ChurchFrege1 M (FC M x) x h3 hsx,
    have h6:= FCmaps M (𝕊 x)hsx,
    cases h6 with y h7,
    cases h7 with h8 h9,
    have h10:= h9  (S (FC M x)) h5,
    have h11:= h9 (FC M (𝕊 x)) h4,
    rw h10, 
    rw h11,
  end

lemma FCplus:∀(y:M),y ∈ 𝔽 →∀(x:M),x ∈ 𝔽 → x + y ∈ 𝔽 → FC M (x+y) = (FC M x) ⊕ (FC M y):=
  begin
    have base: zero ∈ Z_FCplus M:=
      begin
        rw Z_FCplus_members,
        split,
        {
          exact zeroF M,
        },
        {
          intros x hx h3,
          rw right_identityNF,
          rw FCzero,
          rw ChurchZero_equation,
          have h39:= FCmaps2 M x hx,
          have h40:= ChurchFrege_domainrange M (FC M x) x h39,
          exact h40.1,
        }
      end,
    have step: ∀ (y:M), y ∈ Z_FCplus M → (∃ (u:M), u ∈ 𝕊 y) → 𝕊 y ∈ Z_FCplus M:=
      begin
        intros y h3 hsy,
        rw Z_FCplus_members at h3,
        rw Z_FCplus_members,
        cases h3 with hy h4,
        split,
        { 
          exact successorF M y hy hsy,
        },
        {
          intros x hx h5,
          rw addition_equation,
          have h7:= FCsuccessor M y hy (successorF M y hy hsy),
          rw h7,
          rw ChurchAddition_equation,
          rw addition_equation at h5,
          have h6: x+y ∈ 𝔽:= 
            begin
              have h50:= cardinalsinhabited M (𝕊 (x+y)) h5,
              cases h50 with p h51,
              rw successor_members at h51,
              cases h51 with q h52,
              cases h52 with r h53,
              have h54:= h53.1,
              have h55:= inhabited_sum M y hy x hx ⟨ q, h54⟩,
              exact h55,
            end,
          have h8:= FCsuccessor M (x+y) h6 h5,
          rw h8,
          have h9:= h4 x hx h6,
          rw h9,
          have h10:= FCmaps2 M x hx,
          have h11:= ChurchFrege_domainrange M (FC M x) x h10,
          exact h11.1,
          have h12:= FCmaps2 M y hy,
          have h13:= ChurchFrege_domainrange M (FC M y) y h12,
          exact h13.1,
        }
      end,
    intros y hy,
    rw F_members at hy,
    have h200:= hy (Z_FCplus M) ⟨ base, step⟩,
    rw Z_FCplus_members at h200,
    exact h200.2,
  end

lemma propersmaller: ∀ (X Y:M), X ∈ FINITE M → 
Y ∈ FINITE M → X ⊆ Y →  (¬ (Y-X = Λ)) → Nc M X < Nc M Y:=
  begin
    intros X Y hX hY hXY h3,
    have h4: Y = (X ∪ (Y-X)):=
      begin
        have h5:= finiteseparable M Y X hY hX hXY,
        rw union_commutative,
        exact h5,
      end,
    have h6: ¬ zero = Nc M (Y-X):=
      begin
        intros h7,
        have h8:= xinNcx M (Y-X),
        rw← h7 at h8,
        rw zero_members at h8,
        contradiction,
      end,
    have h11:= finitedif M Y X hY hX hXY,
    have h10:= finitecardinals3 M (Y-X) h11,
    have h9:= xnotlessthanzero M (Nc M (Y-X)) h10,
    have h12:= finitetrichotomy M zero (zeroF M) (Nc M (Y-X)) h10,
    have h20: zero < Nc M (Y - X):=
      begin
        cases h12 with h13 h14,
        {
          exact h13,
        },
        {
          cases h14 with h15 h16,
          {
            contradiction,
          },
          {
            contradiction,
          }
        }
      end,
    have h30:= finitecardinals3 M X hX,
    have h31:= finitecardinals3 M Y hY,
    have h35: X ∩ (Y-X) = Λ:=
      begin
        rw full_extensionality,
        intros t,
        split,
        {
          intros h,
          rw intersection_axiom at h,
          cases h with h45 h46,
          rw minus_members at h46,
          cases h46 with h47 h48,
          contradiction,
        },
        {
          intros h,
          have h49:= emptyset_axiom t,
          contradiction,
        }
      end,
    have h40: Nc M Y = Nc M X + Nc M (Y-X):=
      begin
        have h41:= cardinality_additive M X (Y-X) hX h11 h35,
        rw← h4 at h41,
        exact h41,
      end,
    have h21:= lessthansum M (Nc M (Y-X)) h10 (Nc M Y) (Nc M X) h31 h30 h40 h20,
    exact h21,
  end

lemma preceqtoprec:ℕℕ ∈ FINITE M → ∀(k n:M), k ∈ STEM → n ∈ ℕℕ → ¬ k = n →  S k = S n → k <ℕ n →
∀(x y:M), x ∈ ℕℕ → y ∈ ℕℕ → 
(x ≼ y ↔ x ≺ y ∨ x = y):=
  begin
    intros hN k n hk hn hkn hskn h2 x y hx hy,
    split,
    {
      intros h,
      have h40:= Ndecidable M hN x y hx hy,
      cases h40 with h41 h42,
      {
        right,
        exact h41,
      },
      {
        left,
        rw prec_definition,
        exact ⟨ h, h42⟩,
      }
    },
    {
      intros h,
      cases h with h50 h51,
      {
        rw prec_definition at h50,
        exact h50.1,
      },
      {
        rw h51,
        have h52:= preceqreflexive M hN k n hk hn hkn hskn,
        exact h52 y hy,
      }
    }
  end

lemma prectrichotomy4:ℕℕ ∈ FINITE M → ∀(k n:M), k ∈ STEM → n ∈ ℕℕ → ¬ k = n →  S k = S n → 
∀(x y:M), x ∈ ℕℕ → y ∈ ℕℕ → x ≺ y ∨ x = y ∨ y ≺ x:=
  begin
    intros hN k n hk hn hkn hskn  x y hx hy,
    have h2:= klessthann M k n hk hn hkn hskn,
    have h4:= prectrichotomy1 M hN k n hk hn hkn hskn x y hx hy,
    have h6:= preceqtoprec M hN k n hk hn hkn hskn h2 y x hy hx,
    have h5:= preceqtoprec M hN k n hk hn hkn hskn h2 x y hx hy,
    rw h5 at h4,
    rw h6 at h4,
    rw or_assoc at h4,
    rw sym at h4,
    cases h4 with h10 h11,
    {
      left,
      exact h10,
    },
    {
      cases h11 with h12 h13,
      {
        rw sym at h12,
        right,left,
        exact h12,
      },
      {
        cases h13 with h14 h15,
        {  
          right,right,
          exact h14,
        },
        {
          rw sym at h15,
          right,left,
          exact h15,
        }
      }
    }
  end

lemma prectrans2:ℕℕ ∈ FINITE M → ∀(k n:M), k ∈ STEM → n ∈ ℕℕ → ¬ k = n →  S k = S n → 
∀(x y z:M), x ∈ ℕℕ → y ∈ ℕℕ → z ∈ ℕℕ →
x ≺ y → y ≼ z → x ≺ z:=
  begin
    intros hN k n hk hn hkn hskn x y z hx hy hz h3 h4,
    have h2:= klessthann M k n hk hn hkn hskn,
    rw prec_definition at h3,
    cases h3 with h6 h5,
    have h7:= preceqtrans M hN k n hk hn hkn hskn x y z h6 h4,
    have h8:= prectrichotomy3 M hN k n hk hn hkn hskn z hz y hy,
    have h9:¬ x= z:=
      begin
        intros h,
        rw h at *,
        have h10:= h8 ⟨ h4, h6⟩,
        rw sym at h10,
        contradiction,
      end,
    rw prec_definition,
    exact ⟨ h7, h9⟩,
  end

lemma xnotprecx: ℕℕ ∈ FINITE M → ∀(k n:M), k ∈ STEM → n ∈ ℕℕ → ¬ k = n →  S k = S n → 
∀(x:M), x ∈ ℕℕ → ¬ x ≺ x:=
  begin
    intros hN k n hk hn hkn hskn x hx h,
    have h2 := klessthann M k n hk hn hkn hskn,
    rw prec_definition at h,
    cases h with h10 h11,
    contradiction,
  end

lemma precmaximal: ℕℕ ∈ FINITE M → ∀(k n:M), k ∈ STEM → n ∈ ℕℕ → ¬ k = n →  S k = S n → k <ℕ n →
∀(X:M), X ∈ FINITE M → (∃(u:M), u ∈ X) → X ⊆ ℕℕ →  
∃ (m:M), m ∈ X ∧ ∀ (x:M), x ∈ X → x ≼ m:=
  begin
    intros hN k n hk hn hkn hskn h2,
    have base: Λ ∈ W_precmaximal M k n:=
      begin
        rw W_precmaximal_members,
        split,
        {
          exact lambda_finite M,
        },
        {  
          intros h,
          cases h with u h5,
          have h6:= emptyset_axiom u,
          contradiction,
        }
      end,
    have step: ∀(X c:M),((¬ c ∈ X) ∧ X ∈ W_precmaximal M k n) → X ∪ single c ∈ W_precmaximal M k n:=
      begin
        intros A c h400,
        cases h400 with  h4 h,
        rw W_precmaximal_members at h,
        rw W_precmaximal_members,
        cases h with h5 h6,
        split,
        {
          exact finite_adjoin M A c ⟨ h5, h4⟩,
        },
        {
          intros h200 h201,
          have h202: A ⊆ ℕℕ:=
            begin
              rw subset_definition,
              rw subset_definition at h201,
              intros t ht,
              have h202:= h201 t,
              apply h202,
              rw binary_union_axiom,
              left,
              exact ht,
            end,
          have h90:= empty_or_inhabited M A h5,
          have hc: c ∈ ℕℕ:=
            begin
              rw subset_definition at h201,
              have h42:= h201 c,
              rw binary_union_axiom at h42,
              rw singleton1 at h42,
              simp at h42,
              exact h42,
            end,
          cases h90 with h91 h92,
          {
            rw h91 at *,
            use c,
            split,
            {
              rw binary_union_axiom,
              rw singleton1,
              simp,
            },
            {
              intros x h96,
              rw binary_union_axiom at h96,
              rw singleton1 at h96,
              cases h96 with h97 h98,
              { 
                have h99:= emptyset_axiom x,
                contradiction,
              },
              {
                rw h98 at *,
                have h100:= preceqreflexive M hN k n hk hn hkn hskn c hc,
                exact h100,
              }
            },
          },
          {
            -- so we may assume A is inhabited
            have h41:= h202,
            have h13:= h6 h92 h41,
            cases h13 with m h14,
            cases h14 with h15 h16,
            have hm:= member_subset M A ℕℕ m h41 h15,
            have h20:= prectrichotomy1 M hN k n hk hn hkn hskn m c hm hc,
            cases h20 with h21 h22,
            { 
              use c,
              split,
              {
                rw binary_union_axiom,
                rw singleton1,
                simp,
              },
              {
                intros x h50,
                rw binary_union_axiom at h50,
                cases h50 with h51 h52,
                {
                  have h53:= h16 x h51,
                  have hx:= member_subset M A ℕℕ x h41 h51,
                  have h53:= preceqtrans M hN k n hk hn hkn hskn x m c h53 h21,
                  exact h53,
                },
                {
                  rw singleton1 at h52,
                  rw h52 at *,
                  have h54:= preceqreflexive M hN k n hk hn hkn hskn c hc,
                  exact h54,
                }
              }
            },
            { 
              use m,
              split,
              {
                rw binary_union_axiom,
                left,
                exact h15,
              },
              {
                intros x h20,
                rw binary_union_axiom at h20,
                cases h20 with h21 h222,
                {
                  exact h16 x h21,
                },
                {
                  rw singleton1 at h222,
                  rw h222 at *,
                  exact h22,
                }
              }
            }
          },
        }
      end,
    intros X hX,
    rw finite_members at hX,
    specialize hX (W_precmaximal M k n),
    have h200:= hX ⟨ base, step⟩, 
    rw W_precmaximal_members at h200,
    exact h200.2,
  end

lemma FCinitial: ℕℕ ∈ FINITE M → ∀(k n:M), k ∈ STEM → n ∈ ℕℕ → ¬ k = n →  S k = S n → 
∀(x:M), x ∈ 𝔽 → ∀ (q:M), q = FC M x → 
∀ (p:M), p ∈ ℕℕ → p ≺ q → ∃(y:M), y ∈ 𝔽 ∧ 
FC M y = p:=
  begin
    intros hNfinite k n hk hn hkn hskn,
    have h3:= klessthann M k n hk hn hkn hskn,
    have base: zero ∈ Z_FCinitial M k n:=
      begin
        rw Z_FCinitial_members,
        split,
        {
          exact zeroF M,
        },
        {
          intros q hq p hp hpq,
          rw FCzero at hq,
          rw hq at *,
          have h4:= precmin2 M hNfinite k n hk hn hkn hskn p hp,
          contradiction,
        }
      end,
    have step: ∀ (x:M), x ∈ Z_FCinitial M k n → (exists (u:M), u ∈ 𝕊 x) →
    𝕊 x ∈ Z_FCinitial M k n:=
      begin
        intros x h10 hsx,
        rw Z_FCinitial_members at h10,
        rw Z_FCinitial_members,
        set r:= FC M x with rdef,
        cases h10 with hx h11,
        split,
        {
          exact successorF M x hx hsx,
        },
        {
          intros q hq p hp hpq,
          have h12:= hq,
          rw FCsuccessor at h12,
          rw← rdef at h12,
          have h14:= FCmaps2 M x hx,
          rw ChurchFrege_members at h14,
          cases h14 with h15 h16,
          cases h15 with P h16,
          cases h16 with Q h17,
          cases h17 with h18 h19,
          rw ordered_pair_equality at h18,
          rw← h18.1 at *,
          rw← h18.2 at *,
          cases h19 with hr h21,
          rw← rdef at hr, 
          have h13:= prectrichotomy4 M hNfinite k n hk hn hkn hskn p r hp hr,
          cases h13 with case1 case23,
          {
            -- case1, p ≺ r
            have h30:= h11 r,
            simp at h30,
            have h31:= h30 p hp,
            apply h31,
            exact case1,
          },  
          {
            cases case23 with case2 case3,
            {
              --case 2, p = r
              rw case2 at *,
              use x,
              rw sym,
              exact ⟨ h21, rdef⟩,
            },
            {
              -- case 3, r ≺ q
              have h40:= precnoinsertions M hNfinite k n hk hn hkn hskn r p hr hp case3,
              have hqn: q ∈ ℕℕ:= 
                begin
                  have h50:= successorN M r hr,
                  rw h12,
                  exact h50,
                end,
              have h41:= prectrans2 M hNfinite k n hk hn hkn hskn p q p hp hqn hp hpq,
              rw h12 at h41,
              have h42:= h41 h40,
              have h43:= xnotprecx M hNfinite k n hk hn hkn hskn p hp,
              contradiction,
            }
          },
          exact hx,
          exact successorF M x hx hsx,
        }
      end,
    intros x hx,
    rw F_members at hx,
    specialize hx (Z_FCinitial M k n),
    have h200:= hx ⟨base,step⟩,
    rw Z_FCinitial_members at h200,
    exact h200.2,
  end

lemma CFdef: ∀ (k n p q:M), ‹p,q› ∈ CF M k n ↔ 
q = 𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (Ap (Ap p succ) zero)))))):=
  begin
    intros k n p q,
    split,
      { intros h,
        rw CF_members at h,
        cases h with P h2,
        cases h2 with Q h3,
        rw ordered_pair_equality at h3,
        cases h3 with h4 h5,
        rw← h4.1 at *,
        rw← h4.2 at *, 
        exact h5,
      },
      {
        intros h,
        rw CF_members,
        use p, use q,
        simp,
        exact h,
      }
  end

lemma CFFunc: ∀ (k n:M),(CF M k n) ∈ FUNC:=
  begin
    intros k n,
    rw FUNC_members,
    intros x y z h3 h4,
    rw CF_members at h3,
    rw CF_members at h4,
    cases h3 with p h5,
    cases h5 with q h6,
    cases h6 with h7 h8,
    rw ordered_pair_equality at h7,
    rw← h7.1 at *,
    rw← h7.2 at *,
    cases h4 with P h10,
    cases h10 with Q h11,
    cases h11 with h12 h13,
    rw ordered_pair_equality at h12,
    rw← h12.1 at *,
    rw← h12.2 at *,
    rw h8,
    rw h13,
  end

lemma CFApp: ∀ (k n p:M), Ap (CF M k n) p=
 𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (Ap (Ap p succ) zero)))))):=
  begin
    intros k n p,
    set q:= 𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (Ap (Ap p succ) zero)))))) with qdef,
    have h3:= Apdef M (CF M k n) (CFFunc M k n) p q,
    rw CFdef M k n p q at h3,
    rw qdef at *,
    simp at h3,
    rw sym,
    exact h3,
  end

lemma succ_members: ∀(z:M), z ∈ succ ↔
∃ (x y:M), z = ‹x,y› ∧ y = 𝕊 x:=
  begin
    intros z,
    have hrel:= succ1,
    have h2:= succ2,
    split,
    { 
      intros h,
      rw Rel_definition at hrel,
      have h3:= hrel z h,
      cases h3 with a h4,
      cases h4 with b h5,
      use a, use b,
      have h6:= h2 a b,
      rw h5 at h,
      rw h6 at h,
      exact ⟨ h5, h⟩,
    },
    {
      intros h,
      cases h with a h6,
      cases h6 with b h7,
      have h8:= h2 a b,
      rw h7.1,
      rw h8,
      exact h7.2,
    }
  end


lemma successorFUNC: (succ:M)  ∈ FUNC :=
  begin
    rw FUNC_members M succ,
    intros x y z h1 h2,
    rw succ_members M at h1,
    rw succ_members M at h2,
    cases h1 with a h10,
    cases h10 with b h11,
    cases h11 with h12 h13,
    rw ordered_pair_equality at h12,
    rw← h12.1 at *,
    rw← h12.2 at *, 
    cases h2 with A h20,
    cases h20 with B h21,
    cases h21 with h22 h23,
    rw ordered_pair_equality at h22,
    rw← h22.1 at *,
    rw← h22.2 at *, 
    rw h13,
    rw h23,
  end

lemma SFmaps: ∀ (m:M), MAXIMAL M m → maps M succ (𝔽 ∪ single Λ) (𝔽 ∪ single Λ):=
  begin
    intros m hmax,
    have h100:= hmax,
    unfold MAXIMAL at h100,
    cases h100 with hm h101,
    unfold maps,
    split,
    { 
      exact succ1,
    },
    {
      split,
      {
        intros x y h,
        cases h with h2 h3,
        rw succ_members at h3,
        cases h3 with X h40,
        cases h40 with Y h41,
        cases h41 with h42 h43,
        rw ordered_pair_equality at h42,
        rw← h42.1 at *,
        rw← h42.2 at *,
        rw binary_union_axiom at h2,
        cases h2 with hx h5,
        {
          have h6:= finitetrichotomy M x hx m hm,
          cases h6 with h7 h8,
          {
            have h9:= noinsertions M x m hx hm h7,
            have h10:= le_to_inhabited M (𝕊 x) m h9,
            have h11:= successorF M x hx h10,
            rw h43 at *,
            rw binary_union_axiom,
            left,
            exact h11,
          },
          {
            cases h8 with h50 h51,
            {
              rw h50 at *,
              rw binary_union_axiom,
              right,
              rw h43,
              rw singleton1,
              rw full_extensionality,
              intros t,
              split,
              {
                intros h,
                rw successor_members at h,
                cases h with x h200,
                cases h200 with a h201,
                rcases h201 with ⟨ h202, h203, h204⟩,
                have h203:= unenlargeable2 M m hm h101 x h202 a,
                contradiction,
              },
              {
                intros h,
                have h300:= emptyset_axiom t,
                contradiction,
              }
            },
            {
              have h310:= h101 x hx,
              have h311:= le_transitive2 M m x m hm hx hm h51 h310,
              have h312:= xnotlessthanx M m hm,
              contradiction,
            }
          }
        },
        {
          rw singleton1 at h5,
          rw h5 at *,
          have h50:= successorLambda M,
          rw h50 at *,
          rw h43 at *,
          rw binary_union_axiom,
          right,
          rw singleton1,
        } 
      },
      {
        split,
        {
          intros x y z h,
          rcases h with ⟨h301, h302, h303⟩,
          rw succ2 at h303,
          rw succ2 at h302,
          rw h302,
          rw h303,
        },
        {
          intros x h,
          use 𝕊 x,
          split,
          {
            rw binary_union_axiom at h,
            cases h with hx h311,
            {
              have h320:= h101 x hx,
              have h321:= (letolessthan M x m hx hm).1 h320,
              cases h321 with h322 h323,
              {
                have h324:= noinsertions M x m hx hm h322,
                have h325:= le_to_inhabited M (𝕊 x) m h324,
                have h326:= successorF M x hx h325,
                rw binary_union_axiom,
                left,
                exact h326,
              },
              {
                rw h323 at *,
                rw binary_union_axiom,
                right,
                rw singleton1,
                rw full_extensionality,
                intros t,
                split,
                {
                  intros h,
                  rw successor_members at h,
                  cases h with U h330,
                  cases h330 with a h331,
                  cases h331 with h332 h333,
                  cases h333 with h334 h335,
                  have h336:= unenlargeable2 M m hm h101 U h332 a,
                  contradiction,
                },
                {
                  intros h,
                  have h340:= emptyset_axiom t,
                  contradiction,
                }
              }
            },
            { 
              rw singleton1 at h311,
              rw h311 at *,
              rw binary_union_axiom,
              right,
              rw singleton1,
              rw successorLambda,
            }
          },
          {
            have h400:= succ2 x (𝕊 x),
            simp at h400,
            exact h400,
          }
        }
      }
    }
  end

lemma ChurchToFrege: ∀ (m:M), MAXIMAL M m → ℕℕ ∈ FINITE M → ∀(k n:M), k ∈ STEM → n ∈ ℕℕ → ¬ k = n →  S k = S n → 
∀ (p:M), p ∈ ℕℕ → 
  𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (Ap (Ap p succ) zero)))))) ∈ 𝔽 ∧
𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (Ap (Ap p succ) zero)))))) = p ∧
∀ (x:M),x <  𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (Ap (Ap p succ) zero)))))) → 
∃ (q:M), q ≺ p ∧ 𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (Ap (Ap q succ) zero)))))) = x :=
  begin
    intros m hmax hN k n hk hn hkn hskn,
    have base: ChurchZero ∈ Z_ChurchToFrege M k n:=
      begin
        rw Z_ChurchToFrege_members,
        split,
        {
          exact zeroN M,
        },
        {
          split,
          {
            rw zeroAp,
            repeat{rw Tzero},
            exact zeroF M,
          },
          {
            split,
            {
              rw zeroAp,
              repeat{rw Tzero},
              rw FCzero,
            },
            {
              rw zeroAp,
              repeat{rw Tzero},
              intros x h h40,
              have h4:= xnotlessthanzero M x h,
              contradiction,
            }
          }
        }
      end,
    have step: ∀ (p:M), p ∈ Z_ChurchToFrege M k n → (¬ p = n) → S p ∈ Z_ChurchToFrege M k n:=
      begin
        intros p hp hpn,
        rw Z_ChurchToFrege_members at hp,
        rw Z_ChurchToFrege_members,
        rcases hp with ⟨ hp, h4, h5, h6⟩,
        split,
        {
          exact successorN M p hp,
        },
        {
          have h25:= successorFUNC M,
          have h31:= SFmaps M m hmax,
          have h32: (zero:M) ∈ 𝔽 ∪ single (Λ:M):=
            begin
              rw binary_union_axiom,
              left,
              exact zeroF M,
            end,
          have h30:= successorequation M (𝔽 ∪ single Λ) succ h25 succ1 h31 p zero hp h32,
        
          split,
          {
            
          },
          {
            split,
            {

            },
            {

            }
          }
        }
      end,
    
  end
 
 

lemma NfiniteimpFfinite: ℕℕ ∈ FINITE M → ∀(k n:M), k ∈ STEM → n ∈ ℕℕ → ¬ k = n →  S k = S n → 
∀ (p:M), p ∈ 𝔽  → FC M p = n → MAXIMAL M p ∧ 𝔽 ∈ FINITE M:=
  begin
    intros hN k n hk hn hkn hskn p hp h3,
    rw sym at h3,
    have h4:= FCinitial M hN k n hk hn hkn hskn p hp n h3,
    have h5:= precmax M hN k n hk hn hkn hskn,
    have h6: ∀ (x:M),x ∈ ℕℕ → ∃ (y:M),(y ∈ 𝔽 ∧ x = FC M y):=
      begin
        intros x hx,
        have h7:= h5 x hx,
        have h8:= member_subset M STEM ℕℕ k (SN M) hk,
        have h9:= Ndecidable M hN x n hx hn,
        cases h9 with h10 h11,
        {
          use p,
          rw h10 at *,
          exact ⟨ hp, h3⟩,
        },
        {
          have h20:x ≺ n:=
            begin
              rw prec_definition,
              exact ⟨ h7, h11⟩,
            end,
          have h21:= h4 x hx h20,
          cases h21 with y h22,
          use y,
          split,
          {
            exact h22.1,
          },
          {
            rw sym,
            exact h22.2,
          }
        }
      end,
    
  end

#axioms_all