-- exponentiation recursion equation

import inf20
variables (M:Type) [Model M] (a b x y z u v w X R W κ μ ℓ : M)

open Model 

lemma unionlambda: union (Λ:M)= (Λ:M):=
  begin
    rw full_extensionality,
    intros x,
    have h4:= union_axiom x (Λ:M),
    rw h4,
    split,
    {
      intros h,
      cases h with z h4,
      cases h4 with h5 h6,
      have h7:= emptyset_axiom z,
      contradiction,
    },
    {
      intros h,
      have h8:= emptyset_axiom x,
      contradiction,
    }
  end  

lemma notnotfiniteunion:∀(x:M),x ∈ FINITE M → (∀(y:M), y ∈ x → y ∈ FINITE M) → ¬¬ union x ∈ FINITE M:=
  begin
    have base: Λ ∈ Z_notnotfiniteunion M:=
      begin
        rw Z_notnotfiniteunion_members,
        split,
        { 
          exact lambda_finite M,
        },
        { 
          intros y h,
          apply h,
          rw unionlambda,
          exact lambda_finite M,
        }  
      end,
    have step: ∀ (x c:M), ¬ c ∈ x ∧ x ∈ Z_notnotfiniteunion M →   x ∪  (single c) ∈ Z_notnotfiniteunion M:=
      begin
        intros x c h3,
        cases h3 with h4 h5,
        rw Z_notnotfiniteunion_members,
        rw Z_notnotfiniteunion_members at h5,
        cases h5 with h6 h7,
        split,
        {
          have h8:= finite_adjoin M x c ⟨ h6, h4⟩,
          exact h8,
        },
        { 
          intros h,
          have h11:= adjoin_member M c x,
          have hc: c ∈ FINITE M:= h c h11,
          have h12: ¬¬ union x ∈ FINITE M:=
            begin
              apply h7,
              intros y h13,
              have h14:= adjoin_member2 M y c x h13,
              exact h y h14,
            end,
          have h15: ¬¬ ((union x) ∪ c ∈ FINITE M):=
            begin 
              have h16:= union2 M (union x),
              have h17:= double_negate (union x ∈ FINITE M → ∀ (b : M), b ∈ FINITE M → ¬¬union x ∪ b ∈ FINITE M) h16, 
              have h18:= push_double_negationNF (union x ∈ FINITE M)(∀ (b : M), b ∈ FINITE M → ¬¬union x ∪ b ∈ FINITE M) h17 h12,
              have h19:= notnot_forall (λ(b : M), b ∈ FINITE M → ¬¬union x ∪ b ∈ FINITE M) h18,
              dsimp at h19,
              have h20:= h19 c,
              have h30:= double_negate (c ∈ FINITE M) hc,
              have h21:= push_double_negationNF (c ∈ FINITE M)(¬¬union x ∪ c ∈ FINITE M) h20 h30,
              rw triplenegation at h21,
              exact h21,
            end,
          have h40: (union (x ∪ (single c))) = ((union x) ∪ c) :=
            begin
              rw full_extensionality,
              intros t,
              rw union_axiom,
              split,
              {
                intros h50,
                rw binary_union_axiom,
                cases h50 with z h51,
                cases h51 with h53 ht,
                rw binary_union_axiom at h53,
                rw singleton1 at h53,
                cases h53 with h54 h55,
                {
                  left,
                  rw union_axiom,
                  use z,
                  exact ⟨ h54, ht⟩,
                },
                {
                  right,
                  rw h55 at *,
                  exact ht,
                }
              },
              {
                intros h60,
                rw binary_union_axiom at h60,
                cases h60 with h60 h61,
                {
                  rw union_axiom at h60,
                  cases h60 with z h62,
                  use z,
                  rw binary_union_axiom,
                  rw singleton1,
                  split,
                  {
                    left,
                    exact h62.1,
                  },
                  {
                    exact h62.2,
                  }
                },
                {
                  use c,
                  split,
                  {
                    have h66:= adjoin_member M c x,
                    exact h66,
                  },
                  {
                    exact h61,
                  }
                }
              }
            end,
          rw h40,
          exact h15,
        }
      end,
    intros x h,
    rw finite_members at h,
    have h100:= h (Z_notnotfiniteunion M) ⟨ base, step⟩,
    rw Z_notnotfiniteunion_members at h100,
    exact h100.2, 
  end   

theorem finitenotfinite2: ∀ (m:M), MAXIMAL M m → ¬ (𝕍 ∈  FINITE M) →  ¬ FINITE M ∈ FINITE M:=
-- a second proof that M is not finite, assuming V is not finite.
-- see also finitenotfinite1 in inf17.lean
-- If I had realized finitenotfinite1 existed,  I wouldn't have proved this.
  assume m hmax hVnotfinite,
  begin
    have hmaxcopy:= hmax,
    unfold MAXIMAL at hmaxcopy,
    cases hmaxcopy with hm h3,
    have h4:= cardinalsinhabited M m hm,
    cases h4 with u hu,
    have h6:= unenlargeable2 M m hm h3 u hu,
    have h7:= finitecardinals1 M m u hm hu,
    have h5:= unenlargeable3 M u h7,
    unfold UNENLARGEABLE at h5,
    have h8:= h5 h6,
    have h10:
    (∀ (t : M), ¬¬t ∈ u) → ∀ (x : M), x ∈ FINITE M → ¬¬x ∈ SSC(u):=
      begin
        intros h40 x h41,
        have h42:= h8 x h41,
        --rw ssc_members,
        have h43:= notnotSSC M u x h7,
        have h44:= double_negate (x ⊆ u → ¬¬x ∈ SSC u) h43,
        have h45:= push_double_negationNF (x ⊆ u) (¬¬x ∈ SSC u) h44 h42,
        rw triplenegation at h45,
        exact h45,
      end,
    have h11:= h10 h6,
    intros h,
    have h12:= finiteDNS M (SSC u) (FINITE M) h h11,
    have h13: (∀ (x:M),x ∈ FINITE M → x ∈ SSC u) → 𝕍 ⊆ u :=
      begin
        intros h40,
        rw subset_definition,
        intros t ht,
        have h41:= h40 (single t),
        rw ssc_members at h41,
        have h42:= singleton_finite M t,
        have h43:= h41 h42,
        cases h43 with h44 h45,
        rw subset_definition at h44,
        have h46:= h44 t,
        rw singleton1 at h46,
        apply h46,
        reflexivity,
      end,
    have h30:= double_negate ((∀ (x : M), x ∈ FINITE M → x ∈ SSC u) → 𝕍 ⊆ u) h13,
    have h31:= push_double_negationNF (∀ (x : M), x ∈ FINITE M → x ∈ SSC u) (𝕍 ⊆ u) h30 h12,
    have h32:= notnotseparable M u 𝕍 h7,
    have h33:= separablefinite M u h7 𝕍,
    unfold separable_subset at h33,
    have h34:= double_negate (𝕍 ⊆ u → 𝕍 ⊆ u ∧ u = (𝕍 ∪ u - 𝕍) → 𝕍 ∈ FINITE M) h33,
    have h35:= push_double_negationNF (𝕍 ⊆ u)(𝕍 ⊆ u ∧ u = (𝕍 ∪ u - 𝕍) → 𝕍 ∈ FINITE M) h34 h31,
    have h36:= push_double_negationNF (𝕍 ⊆ u ∧ u = (𝕍 ∪ u - 𝕍)) (𝕍 ∈ FINITE M) h35,
    have h40:= double_negate (𝕍 ⊆ u → ¬¬u = (𝕍 ∪ u - 𝕍)) h32,
    have h41:= push_double_negationNF (𝕍 ⊆ u)(¬¬u = (𝕍 ∪ u - 𝕍)) h40 h31,
    rw triplenegation at h41,
    have h37: ¬¬(𝕍 ⊆ u ∧ u = (𝕍 ∪ u - 𝕍)):=
      begin
        rw notnot_and,
        split,
        {
          exact h31,
        },
        {
          exact h41,
        }
      end,
    have h42:= h36 h37,
    contradiction,
  end

lemma nodisjointunenlargeables: ∀(m:M), MAXIMAL M m → u ∈ m → v ∈  m → ¬ u ∩ v = Λ :=
  assume m hmax hu hv,
  begin
    have h3:= hmax,
    unfold MAXIMAL at h3,
    have h3copy:= h3,
    cases h3copy with hm3 h20,
    cases h3 with hm h4,
    have h5:= finitecardinals1 M m u hm hu,
    have h6:= finitecardinals1 M m v hm hv,
    have h30:= empty_or_inhabited M u h5,
    cases h30 with h31 h32,
    {
      have hucopy:= hu,
      rw h31 at hucopy,
      have h32: Λ ∈ zero :=
        begin
          rw zero_members M,
        end,
      have h33: Λ ∈ zero ∩ m:=
        begin
          rw intersection_axiom,
          exact ⟨h32, hucopy⟩, 
        end, 
      have h38:=cardinalsdisjoint M  zero m Λ (zeroF M) hm h33,
      have h39:= h20 one (oneF M),
      rw←  h38 at h39,
      have h40:= zero_lessthan_one M,
      have h41:= le_transitive2 M zero one zero (zeroF M) (oneF M)(zeroF M) h40 h39,
      have h42:= xnotlessthanx M zero (zeroF M),
      contradiction,
    },
    {
      cases h32 with z h50,
      have h8:= unenlargeable2 M m hm h20 v hv z,
      intros h51,
      have h51copy:= h51,
      rw full_extensionality at h51,
      have h52:= h51 z,
      have h53:= emptyset_axiom z,
      rw← h51copy at h53,
      have h60: ¬¬ (z ∈ u ∩ v ):=
        begin
          intros h,
          apply h8,
          intros h80,
          apply h53,
          rw intersection_axiom,
          exact ⟨ h50, h80⟩,
        end,
      contradiction,
    },
  end  

lemma markov2: ∀ (X:M), X ∈ FINITE M → (¬¬ ∃ (u:M), u ∈ X) → ∃ (u:M), u ∈ X:=
-- this is a copy of "markov", which is in ChurchNumbers2.lean
-- but it's not actually used here.
  assume X,
  begin
    intros hX,
    have h:= empty_or_inhabited M X hX, 
    cases h with h3 h4,
    {
      rw h3 at *,
      intros h2,
      have h5: ¬ ∃ (u:M), u ∈ Λ:=
        begin
          intros h6,
          cases h6 with u h7,
          have h8:= emptyset_axiom u,
          contradiction,
        end,
      contradiction,
    },
    {
      intros h9,
      exact h4,
    }
  end

lemma butone: ∀(x:M), x ∈ 𝔽 → (∃(v:M), v ∈ 𝕊 x) →  ∀(u:M), u ∈ x → ¬¬ ∃ (c:M), ¬ c ∈ u:=
  -- same as butone2 below, but with a different proof.
  begin
    intros x hx hsx u hu,
    have hsxcopy:= hsx,
    have hsxf:= successorF M x hx hsx,
    cases hsx with w hw,
    have h10:= finitecardinals1 M x u hx hu,
    have h11:= finitecardinals1 M (𝕊 x) w hsxf hw,
    have h3: ¬ w ⊆ u:=
      begin
        intros h4,
        have h5: w ∈ SSC u:=
          begin
            rw ssc_members,
            split,
            {
              exact h4,
            },
            {
              intros y hy,
              have h5:= finiteseparable M u w h10 h11 h4,
              rw full_extensionality at h5,
              specialize h5 y,
              rw h5 at hy,
              rw binary_union_axiom at hy,
              cases hy with h20 h21,
              {
                right,
                rw minus_members at h20,
                exact h20.2,
              },
              {
                left,
                exact h21,
              }
            }
          end, 
        have h30: 𝕊 x ≤ x:=
          begin
            rw le_definition,
            use w,
            use u,
            split,
            {
              exact hw,
            },
            {
              split,
              {
                exact hu,
              },
              {
                split,
                {
                  exact h4,
                },
                {
                  rw ssc_members at h5,
                  cases h5 with h40 h41,
                  rw full_extensionality,
                  intros p,
                  rw binary_union_axiom,
                  rw minus_members,
                  have h42:= h41 p,
                  split,
                  {
                    intros hp,
                    have h43:= h42 hp,
                    cases h43 with h44 h45,
                    {
                      left,
                      exact h44,
                    },
                    {
                      right,
                      exact ⟨hp, h45⟩, 
                    }
                  },
                  {
                    intros h46,
                    cases h46 with h47 h48,
                    {
                      exact member_subset M w u p h4 h47,
                    },
                    {
                      exact h48.1,
                    }
                  }
                }
              }
            }
          end,
        have h50:= xlessthansuccessorx M x hx hsxf,
        have h51:= le_transitive2 M x (𝕊 x ) x hx hsxf hx h50 h30,
        have h52:= xnotlessthanx M x hx,
        contradiction,
      end,
    intros h60, 
    rw subset_definition at h3,
    have h70: ¬¬ ∃(t:M), t ∈ w ∧ ¬ t ∈ u:=
      begin
        intros h71,
        rw not_exists at h71,
        simp_rw not_and at h71,
        have h72:= finiteDNS M u w h11 h71,
        contradiction,
      end,
    have h72: ¬¬ ∃(t:M),¬ t ∈ u:=
      begin
        intros h73,
        apply h70,
        intros h74,
        apply h73,
        cases h74 with t h75,
        use t,
        exact h75.2,
      end,
    contradiction,
  end

lemma butone2: ∀(x:M), x ∈ 𝔽 → (∃(v:M), v ∈ 𝕊 x) →  ∀(u:M), u ∈ x → ¬¬ ∃ (c:M), ¬ c ∈ u:=
  begin
    intros x hx hsx u hu,
    have hxscopy:= hsx,
    cases hsx with v h30,
    rw successor_members at h30,
    cases h30 with z h31,
    cases h31 with e h32,
    cases h32 with hz h34,
    cases h34 with h35 h36,
    have h28:= xinNcx M u,
    have hu3:= finitecardinals1 M x u hx hu,
    have h25: u ∈  x ∩ (Nc M u):=
      begin
        rw intersection_axiom,
        exact ⟨ hu, h28⟩,
      end,
    have h29: Nc M u = x:=
      begin
        have h29:= finitecardinals3 M u hu3,
        have h27:= cardinalsdisjoint M x (Nc M u) u hx h29 h25,
        rw sym,
        exact h27,
      end,
    have h40: ¬¬ (exists (c:M), ¬ c ∈ u):=
      begin
        intro h,
        have h41: UNENLARGEABLE M u:=
          begin
            unfold UNENLARGEABLE,
            intros t,
            intros h42,
            apply h,
            use t,
          end,
        have h43: MAXIMAL M (Nc M u):=
          begin
            unfold MAXIMAL,
            rw h29,
            have h28:= unenlargeable4 M u hu3 h41,
            rw h29 at h28,
            exact ⟨ hx, h28⟩,
          end,
        rw h29 at *,
        have h80:= maximalimpliesnosuccessor M x h43,
        cases hxscopy with r h81,
        rw h80 at *,
        have h82:= emptyset_axiom r,
        contradiction,
      end,
    exact h40,
  end   


lemma addition_reverse: ∀(m:M), MAXIMAL M m → 
    ∀(q:M),q ∈ 𝔽 → ∀ (p a:M), p ∈ 𝔽 →  a ∈ p → p+q < m → ¬¬∃ (b:M), b ∈q ∧ a ∩ b = Λ:=   
  assume m hmax,
  begin
    have base: zero ∈ Z_addition_reverse M m:=
      begin
        rw Z_addition_reverse_members,
        split,
        {
          exact zeroF M,
        },
        {
          intros p a hp ha h3,
          have h100:∃(b : M), b ∈ zero ∧ a ∩ b = Λ:=
            begin
              use Λ,
              split,
              {
                rw zero_members,
              },
              {
                have h4:= x_intersect_empty M a,
                exact h4,
              }
            end,
          have h101:= double_negate (∃(b : M), b ∈ zero ∧ a ∩ b = Λ) h100,
          exact h101,
        }
      end,
    have step: ∀(q:M), q ∈ Z_addition_reverse M m → (∃ (z:M),z ∈ 𝕊 q) → 𝕊 q ∈ Z_addition_reverse M m:=
      begin
        intros q h10 hsq,
        rw Z_addition_reverse_members at h10,
        cases h10 with hq h11,
        rw Z_addition_reverse_members,
        split,
        {
          exact successorF M q hq hsq,
        },
        {
          intros p a hp ha h12,
          have hsqf:= successorF M q hq hsq,
          have hpNn:= FSF M  p hp,
          have hsqNn:= FSF M (𝕊 q) hsqf,
          have h13:= additionSF M (𝕊 q) hsqNn p hpNn,
          have h14: p + 𝕊 q ≤ m:=
            begin
              rw lessthan_definition at h12,
              exact h12.1,
            end, 
          have h15: exists (u:M), u ∈ p + 𝕊 q:=
            begin
              rw le_definition at h14,
              cases h14 with A h16,
              cases h16 with B h17,
              use A,
              exact h17.1,
            end, 
          have h20:= inhabitedSF M (p + 𝕊 q) h13 h15,
          have h21:= subterms3 M p q hp hq h20,
          have h23: p+q < m:=
            begin
              have h20copy:= h20,
              rw addition_equation at h20,
              have h25:= cardinalsinhabited M (𝕊 (p+q)) h20, 
              have h24:= lessthansuccessor M (p+q) h21 h25,
              rw← addition_equation at h24,
              unfold MAXIMAL at hmax,
              cases hmax with hm h30,
              have h26:= lessthan_transitive M (p+q) (p+ 𝕊 q) m h21 h20copy  hm h24 h12,
              exact h26,
            end,
          have h30:= h11 p a hp ha h23,
          have h19:=h20,
          rw addition_equation at h19,
          have h40:= cardinalsinhabited M (𝕊 (p+q)) h19,
          have h41: (∃(b : M), b ∈ q ∧ a ∩ b = Λ) → ¬¬∃ (b : M), b ∈ 𝕊 q ∧ a ∩ b = Λ:=
            begin
              intros h42,
              cases h42 with b h43,
              cases h43 with h44 h45,
              have h50: (a ∪ b) ∈ p+q:=
                begin
                  rw addition_members,
                  use a, use b,
                  split,
                  {
                    reflexivity,
                  },
                  {
                    exact ⟨ ha, h44, h45⟩,
                  }
                end, 
              have h51:= butone M (p+q) h21 h40 (a ∪ b) h50,
              have h52:  (∃(c : M), ¬c ∈ a ∪ b) → ¬¬∃ (b : M), b ∈ 𝕊 q ∧ a ∩ b = Λ:=
                begin
                  intros h53,
                  cases h53 with c h54,
                  rw binary_union_axiom at h54,
                  have h55: ¬ c ∈ b:=
                    begin
                      intros h56,
                      apply h54,
                      right,
                      exact h56,
                    end,
                  have h57: (b ∪ single c) ∈ 𝕊 q:=
                    begin
                      rw successor_members,
                      use b, use c,
                      split,
                      {
                        exact h44,
                      },
                      {
                        split,
                        {
                          exact h55,
                        },
                        {
                          reflexivity,
                        }
                      } 
                    end,
                  have h58: ∃(b: M), b ∈ 𝕊 q ∧ a ∩ b = Λ:=
                    begin
                      use (b ∪ single c),
                      split,
                      {
                        exact h57,
                      },
                      {
                        rw full_extensionality,
                        intros t,
                        split,
                        {
                          intros h60,
                          rw intersection_axiom at h60,
                          cases h60 with ht h61,
                          rw binary_union_axiom at h61,
                          rw singleton1 at h61,
                          cases h61 with h62 h63,
                          {
                            have h64: t ∈ a ∩ b:=
                              begin
                                rw intersection_axiom,
                                exact ⟨ ht, h62⟩,
                              end,
                            have h65:= emptyset_axiom t,
                            rw h45 at h64,
                            contradiction,
                          },
                          {
                            rw h63 at *,
                            have h66:false:=
                              begin
                                apply h54,
                                left,
                                exact ht,
                              end,
                            contradiction,
                          }
                        },
                        {
                          intros h60,
                          have h61:= emptyset_axiom t,
                          contradiction,
                        }
                      }
                    end,
                  have h80:= double_negate (∃(b: M), b ∈ 𝕊 q ∧ a ∩ b = Λ) h58,
                  exact h80,
                end,
              have h81:= notnot_imp (∃ (c : M), ¬c ∈ a ∪ b) (¬¬∃ (b : M), b ∈ 𝕊 q ∧ a ∩ b = Λ) h52 h51,
              rw triplenegation at h81,
              exact h81,
            end,
          have h82:= notnot_imp (∃ (b : M), b ∈ q ∧ a ∩ b = Λ)(¬¬∃ (b : M), b ∈ 𝕊 q ∧ a ∩ b = Λ) h41 h30,
          rw triplenegation at h82,
          exact h82,
        }
      end,
    intros q hq,
    rw F_members at hq,
    have h100:= hq (Z_addition_reverse M m) ⟨ base,step⟩,
    rw Z_addition_reverse_members at h100,
    exact h100.2,
  end

lemma subtractone: ∀(k r x c:M), k∈ 𝔽 → r ∈ 𝔽 →  k = 𝕊 r → x ∈ k → c ∈ x → x - single c ∈ r:=
  assume k r x c hk hr hsr hx hc,
  begin
    have h4:= finitecardinals1 M k x hk hx,
    have h5:= finite_decidable2 M x,
    have h6: x = ((x - (single c)) ∪ (single c)):=
      begin
        rw full_extensionality,
        intros z,
        have h7:= h5 z c h4,
        rw binary_union_axiom,
        rw minus_members,
        rw singleton1,
        split,
        {
          intros h20,
          have h21:= h7 h20 hc,
          cases h21 with h22 h23,
          {
            right,
            exact h22,
          },
          {
            left,
            exact ⟨ h20, h23⟩,
          }
        },
        {
          intros h30,
          cases h30 with h31 h32,
          {
            exact h31.1,
          },
          {
            rw h32 at *,
            exact hc,
          }
        }
      end,
    let q:= Nc M (x - (single c)),
    have h40: x ∈ 𝕊 q:=
      begin
        rw successor_members,
        use x - (single c),
        use c,
        split,
        {
          dsimp [q],
          have h41:= xinNcx M (x - (single c)),
          exact h41,
        },
        {
          split,
          {
            rw minus_members,
            rw singleton1,
            intros h,
            cases h with h42 h43,
            apply h43,
            reflexivity,
          },
          {
            exact h6,
          }
        }
      end,
    have h46: (single c) ⊆ x:=
      begin
        rw subset_definition,
        intros z,
        rw singleton1,
        intros h,
        rw h at *,
        exact hc,
      end,
    have h47:= finitedif M x (single c) h4 (singleton_finite M c) h46,
    have h48:= finitecardinals3 M (x - single c) h47,
    have hq: q ∈ 𝔽 :=
      begin
        dsimp [q],
        exact h48,
      end,
    have h49:= successorF M q hq ⟨ x, h40⟩,
    have h50: k = 𝕊 q:=
      begin
        have h51:= cardinalsdisjoint M k (𝕊 q) x hk h49,
        apply h51,
        rw intersection_axiom,
        split,
        {
          exact hx,
        },
        {
          exact h40,
        }
      end,
    have h51: 𝕊 r = 𝕊 q:=
      begin
        rw hsr at h50,
        exact h50,
      end,
    have h53: ∃ (u:M), u ∈ 𝕊 r:=
      begin
        use x,
        rw← hsr,
        exact hx,
      end,
    have h54: ∃ (u:M), u ∈ 𝕊 q:=
      begin
        use x,
        rw← h50,
        exact hx,
      end,
    have h52:= successoroneone M r q hr hq h53 h54,
    rw← h52 at h51,
    rw h51,
    dsimp[q],
    have h60:= xinNcx M (x - (single c)),
    exact h60,
  end 

lemma lambdanotcofinite: (¬ 𝕍 ∈ FINITE M) →  ¬ (𝕍 - Λ) ∈ FINITE M:= 
  begin
    intros hV h,
    rw x_minus_empty at h,
    contradiction
  end
 
theorem noleastcofinite: (¬ (𝕍:M) ∈ FINITE M) → ∀ (k:M), COFINITE M k → ¬¬ ∃ (r:M), COFINITE M r ∧ r < k:=
  assume hV k h,
  begin
    unfold COFINITE at h,
    cases h with hk h3,
    cases h3 with X h4,
    cases h4 with h5 h6,
    have h10:= finitecardinals1 M k (𝕍 -X) hk h5,
    have h8: ¬ k = zero:=
      begin
        have h9:= lambdanotcofinite M hV,
        intros h,
        rw h at h5,
        rw zero_members at h5,
        rw h5 at h10,
      end, 
    have h9: ¬(𝕍 - X = Λ) :=
      begin
        intros h,

      end,   
     
    
  end


#axioms_all