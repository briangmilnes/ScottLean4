 --   T and exponentiation continued 
import inf11 
variables (M:Type) [Model M] (a b x y z u v w X R W κ μ ℓ : M)
-- using ℓ where the source text has λ because you can't use λ for a variable.

open Model 

lemma expexistsT: ∀ (m:M), m ∈ 𝔽 → exp M m ∈ 𝔽 → ∃ (r:M), r ∈ 𝔽 ∧ m = 𝕋 M r:=
  assume m,
  begin
    intros hm h,
    have h2:= cardinalsinhabited M (exp M m) h,
    cases h2 with x h3,
    rw exp_members at h3, 
    cases h3 with a h4,
    cases h4 with h5 h6,
    have h10:= finitecardinals1 M m (USC a) hm h5, 
    have h11:= uscfinite M a,
    rw h11 at h10, 
    use (Nc M a), 
    split,
    {
      have h8:= finitecardinals3 M a h10,
      exact h8,
    },
    { 
      rw full_extensionality,
      intro t,
      rw T_members,
      split,
      {
        intro ht,
        use a,
        split,
        {
          exact xinNcx M a,
        },
        {
          have h12:=finitecardinals2 M t (USC a) m hm ht h5,
          exact h12, 
        }
      },
      {
        intro h12,
        cases h12 with b h13,
        cases h13 with h14 h15,
        have h16:= Nc_members M a b,
        rw h16 at h14,
        rw  uscsimilar M b a at h14, 
        have h17:= similar_transitive M t (USC b) (USC a) h15 h14,
        rw similar_symmetric at h17, 
        have h18:= finitecardinals0 M m (USC a) t hm h5 h17,
        exact h18, 
      }
    }
  end



lemma two_plus_two: (two:M) + (two:M) = (four:M):=
  begin
    rw four_definition,
    rw three_definition,
    rw two_definition,
    rw one_definition,
    repeat {rw successor_shift},
    rw right_identityNF,
  end

lemma exp_two: exp M (two: M) =  (four:M) :=
  begin 
    have h: USC({zero,one}) ∈ two:=
      begin
        rw two_members M, 
        use single zero, use single one,
        split,
        {
          intro h,
          have h2:= single_oneone M zero one h,
          have h3:= one_neq_zero M,
          rw sym at h2,
          contradiction, 
        },
        {
          rw full_extensionality,
          intro t,
          rw usc,
          split,
          {
            intro h,
            cases h with a h2,
            cases h2 with h3 h4,
            rw pairing_axiom at h3,
            rw h4,
            rw pairing_axiom,
            cases h3 with h5 h6,
            {
              left,
              rw h5,
            },
            {
              right,
              rw h6,
            }
          },
          {
            intro h,
            rw pairing_axiom at h,
            cases h with h2 h3,
            {
              use zero,
              rw pairing_axiom,
              simp,
              exact h2,
            },
            {
              use one,
              rw pairing_axiom,
              simp,
              exact h3,
            }
          }
        } 
      end,
    have h3:=exp_members2 M two {zero,one} (twoF M) h,
    have h4:=finiteexp M two (twoF M) ⟨ SSC {zero,one},h3⟩,
    rw two_definition at h4,
    have h5:=exprec M one (oneF M) h4,
    rw [two_definition, h5],
    rw exp_one M,
    exact two_plus_two M,
  end
 


lemma addorder2: ∀ (a b p q:M), a ∈ 𝔽 → b ∈ 𝔽 → p ∈ 𝔽 → q ∈ 𝔽 → b + q ∈ 𝔽 → 
a < b → p ≤ q → a+p < b + q:=  
  assume a b p q,
  begin
    intros ha hb hp hq h3 h4 h5,
    have h6:= noinsertions M a b ha hb h4, 
    have h7: 𝕊 a + p = 𝕊 (a + p):=
      begin 
        rw← successor_shift, 
        rw addition_equation, 
      end,
    have h6copy:= h6,
    rw le_definition at h6copy,
    cases h6copy with u h10,
    cases h10 with v h11,
    cases h11 with h12 h13,
    have h14:= successorF M a ha ⟨ u, h12⟩,
    have h8:= addorder M (𝕊 a) b p q h14 hb hp hq h3 h6 h5, 
    rw← successor_shift M a p at h8,
    rw addition_equation M a p at h8,
    have h18copy:= h8,
    rw le_definition at h18copy,
    cases h18copy with r h20,
    cases h20 with s h21,
    cases h21 with h22 h23,
    have h22copy:= h22,
    rw successor_members M at h22,
    cases h22 with x h24,
    cases h24 with c h25,
    cases h25 with h26 h27,
    have h28:= inhabited_sum M p hp a ha  ⟨x,h26⟩, 
    have h29:= successorF M (a+p) h28 ⟨ r, h22copy⟩ ,
    have h15: a+p < 𝕊 (a+p) := xlessthansuccessorx M (a+p) h28 h29,
    have h30:= xlessthansuccessorx M (a+p) h28,
    have h31:= le_transitive2 M (a+p)(𝕊 (a+p))(b+q) h28 h29 h3 h15 h8,
    exact h31,
  end
  

lemma exponeonebase: ∀ (m:M), m ∈ 𝔽 → (exp M m = one ↔ m = zero):=
  assume m,
  begin
    intro h,
    split,
    {
      intro h2,
      have h3: exp M two = four:= exp_two M,
      have h4:= cardinalsinhabited M one (oneF M),
      rw← h2 at h4,
      have h5:= cardinalsinhabited M four (fourF M),
      have h10:= λ p, (exporder M two m (twoF M) h p h4).right,
      rw [h2,h3] at h10, 
      have h11:= one_lessthan_four M, 
      have h12: ¬ (two ≤ m):=
        begin
          intro h12,
          have h13:= h10 h12,
          have h14:= Theorem2 M one four (oneF M)(fourF M),
          cases h14 with h15 h16,
          rw letolessthan M four one (fourF M) (oneF M)at h13,
          cases h13 with h20 h21,
          {
            exact h16 ⟨ h11, h20⟩, 
          },
          {
            rw h21 at *,
            exact h16 ⟨ h11, h11⟩, 
          }
        end,
      have h13:= Theorem2 M m two h (twoF M), 
      cases h13 with h14 h15, 
      have h16: m < two:=
        begin
          rw letolessthan M two m (twoF M) h at h12,
          cases h14 with h20 h21,
          {
            exact h20,
          },
          {
            rw or_comm at h21,
            rw sym at h21, 
            have h22:= h12 h21,
            contradiction,
          }
        end,
      have h17:= lessthantwo M m h,
      rw h17 at h16, 
      have h18:= exp_one M, 
      have h19:= xnotequalsuccessorx M one (oneF M),
      rw← two_definition at h19,
      have h20: ¬ m = one:=
        begin
          intro h21,
          rw h21 at *,
          rw h18 at h2,
          rw sym at h2,
          contradiction,
        end,
      cases h16 with h20 h21,
      {
        exact h20,
      },
      {
        contradiction, 
      }
    },
    {
      intro h2,
      rw h2,
      have h3:= exp_zero M,
      exact h3, 
    }
  end

lemma exponeone: ∀ (n:M), n ∈ 𝔽 →  (∃(u:M), u ∈ exp M n) → ∀ (m:M), m ∈ 𝔽 →  exp M n = exp M m → n = m :=
  begin 
    have base: zero ∈ Zexponeone M:=
      begin
        rw Zexponeone_members M,
        have h3:= exponeonebase M,
        split,
        {
          exact zeroF M,
        },
        {
          intros h m h2 h4,
          have h5:= h3 m h2, 
          symmetry,
          cases h5 with h6 h7,
          apply h6,
          rw← h4,
          rw exp_zero M, 
        }
      end,
    have step: ∀ (n:M),  n ∈ Zexponeone M → (∃(u:M), u ∈ 𝕊 n) →  𝕊 n ∈ Zexponeone M:=
      begin
        intros n  h3 h2,
        rw Zexponeone_members M at h3,
        cases h3 with h h5,
        rw Zexponeone_members M,
        split,
        {
          exact successorF M n h h2, 
        },
        {         
          intros h6 m h7 h8,
          have h9:= FregeNdecidable M,
          rw decidable_members M at h9,
          have h10:= h9 m zero ⟨ h7 ,(zeroF M)⟩, 
          have h20:= successorF M n h h2,
          cases h10 with h11 h12,
          {   -- case m = 0
            rw h11 at *,
            have h12:= exponeonebase M (𝕊 n) h20, 
            apply h12.mp, 
            rw h8,
            rw exp_zero M, 
          },
          { -- case m ≠ 0 
            have h13:= nonzeroissuccessor M m h7 h12,
            cases h13 with r h14,
            cases h14 with h15 h16,
            rw h16 at *,
            have h17:= finiteexp M (𝕊 n) h20 h6, 
            have h18:= exprec M n h h17,
            have h19: exp M (𝕊 r) ∈ 𝔽:= 
              begin 
                rw← h8,
                exact h17,
              end, 
            have h21:= exprec M r h15 h19, 
            have h22:= finiteexp M (𝕊 n) h20 h6, 
            have h23:= finiteexp M r h15, 
            have h24: exp M r ∈ 𝔽 :=
              begin
                have h25:= cardinalsinhabited M (exp M (𝕊 r)) h19, 
                cases h25 with x h26,
                rw h21 at h26, 
                rw addition_members M at h26,
                cases h26 with u h27,
                cases h27 with v h28,
                rcases h28 with ⟨ h29, h30, h31, h32⟩, 
                exact finiteexp M r h15 ⟨ v, h31⟩, 
              end,
            have h34: exp M n ∈ 𝔽 :=
              begin
                have h25:= cardinalsinhabited M (exp M (𝕊 n)) h22, 
                cases h25 with x h26,
                rw h18 at h26, 
                rw addition_members M at h26,
                cases h26 with u h27,
                cases h27 with v h28,
                rcases h28 with ⟨ h29, h30, h31, h32⟩, 
                exact finiteexp M n h  ⟨ v, h31⟩, 
              end,
            rw h18 at h17, 
            have h40:= Theorem2 M r n h15 h,
            cases h40 with h41 h42,
            cases h41 with h43 h44,
            {  -- case 1, r < n
              rw lessthan_definition r n at h43, 
              cases h43 with h44 h45,
              have h46:= exporder M r n h15 h h44 (cardinalsinhabited M (exp M n) h34), 
              cases h46 with h47 h48,
              have h49:= cardinalsinhabited M (exp M n) h34, 
              have h50:= h5 h49 r h15, 
              have h51: ¬ ( exp M r = exp M n):= 
                begin 
                  intro h52,
                  rw h52 at *,
                  simp at h50,
                  rw sym at h50,
                  contradiction,  
                end, 
              have h52:  exp M r < exp M n:=
                begin
                  rw lessthan_definition,
                  exact ⟨ h48, h51⟩,
                end,
              have h30:= addorder2 M (exp M r) (exp M n) (exp M r) (exp M  n) h24 h34 h24 h34 h17 h52 h48,
              have h31: exp M (𝕊 r) < exp M (𝕊 n):= 
                begin 
                  rw [h18, h21],
                  exact h30,
                end, 
              rw h8 at h31, 
              have h32:= xnotlessthanx M (exp M (𝕊 r)), 
              have h33:= h32 h19,
              contradiction, 
            },
            {
              cases h44 with h45 h46,
              {
                rw h45 at *,
              },
              {
                rw lessthan_definition at h46,
                cases h46 with h54 h55,
                have h56:= exporder M n r h  h15 h54 (cardinalsinhabited M (exp M r) h24), 
                cases h56 with h57 h58,
                have h59:= cardinalsinhabited M (exp M r) h24,
                have h60:= h5 h57 r h15, 
                have h61: ¬ ( exp M r = exp M n):= 
                  begin 
                    intro h80,
                    rw sym at h80,
                    have h81:= h60 h80,
                    contradiction,
                  end, 
                have h62:  exp M n < exp M r:=
                  begin
                    rw lessthan_definition,
                    rw sym at h61,
                    exact ⟨ h58, h61⟩,
                  end,
                rw h21 at h19, 
                have h30:= addorder2 M (exp M n) (exp M r) (exp M n) (exp M r) h34 h24 h34 h24 h19 h62, 
                have h31: exp M (𝕊 n) < exp M (𝕊 r):= 
                  begin 
                    rw [h18, h21],
                    apply h30,
                    exact h58, 
                  end, 
                rw h8 at h31,
                have h32:= xnotlessthanx M (exp M (𝕊 r)), 
                rw h8 at h22,
                have h33:= h32 h22,
                contradiction, 
              }
            }
          }
        }
      end,
    intros n   h, 
    rw F_members at h, 
    specialize h ( Zexponeone M),
    have h3:= h ⟨ base, step⟩, 
    rw ( Zexponeone_members M) at h3, 
    cases h3 with h4 h5, 
    exact h5, 
  end

lemma exporderstrict: ∀(m n:M), m ∈ 𝔽 → n ∈ 𝔽 → m < n → (∃ (u:M), u ∈ exp M n) → 
(∃ (u:M), u ∈ exp M m) ∧ exp M m < exp M n:=
  assume m n,
  begin
    intros hm hn h2 h3,
    have h4:= h2,
    rw lessthan_definition at h4,
    cases h4 with h5 h6,
    have h7:= exporder M m n hm hn h5 h3,
    cases h7 with h8 h9,
    have h10:= exponeone M n hn h3 m hm, 
    have h11: ¬ (exp M m = exp M n):= 
      begin 
        intro h12,
        rw sym at h10,
        have h13:= h10 h12, 
        rw sym at h13,
        contradiction, 
      end, 
    split,
    {
      exact h8,
    },
    {
      rw lessthan_definition,
      exact ⟨ h9, h11⟩, 
    }
  end

lemma xnotlessthanzero: ∀ (x:M), x∈ 𝔽 → ¬ (x < zero):=
  assume x,
  begin
    intros h h2,
    rw lessthan_definition at h2,
    cases h2 with h3 h4,
    rw le_definition at h3,
    cases h3 with a h5,
    cases h5 with b h6,
    rcases h6 with ⟨ h7, h8,h9, h10⟩, 
    rw zero_definition at h8,
    rw singleton1 at h8,
    rw h8 at *,
    rw subset_of_empty M a at h9,
    rw h9 at *,
    have h10: Λ ∈ x ∩ zero:=
      begin
        rw zero_definition,
        rw intersection_axiom,
        rw singleton1,
        simp,
        exact h7,
      end,
    have h11:= cardinalsdisjoint M x zero Λ h (zeroF M) h10, 
    contradiction,
  end

lemma orderbyaddition: ∀ (q:M), q ∈ 𝔽 → ∀ (p:M), p ∈ 𝔽 → (p ≤ q ↔ ∃ (k:M), k ∈ 𝔽 ∧ p + k = q):=
  begin
    have base: zero ∈ Z_orderbyaddition M:=
      begin
        rw Z_orderbyaddition_members M,
        split,
        {
          exact zeroF M,
        },
        {
          intros p h,
          split,
          { intro h3, 
            have h2:= letolessthan M p zero h (zeroF M),
            rw h2 at h3,
            cases h3 with h4 h5,
            { 
              have h6:= xnotlessthanzero M p h,
              contradiction,
            },
            {
              rw h5 at *, 
              use zero,
              rw right_identityNF, 
              simp,
              exact zeroF M,
            }
          },
          {
            intro h2,
            cases h2 with k h3, 
            cases h3 with h4 h5,
            rw zero_definition at h5, 
            rw le_definition,
            use Λ, use Λ,
            rw full_extensionality at h5,
            specialize h5 Λ, 
            rw singleton1 at h5, 
            simp at h5, 
            rw addition_members at h5, 
            cases h5 with a h6,
            cases h6 with b h7,
            rcases h7 with ⟨ h8, h9, h10, h11⟩, 
            have h12: a ⊆ a ∪ b:= subset_union2 M a b, 
            rw← h8 at h12,
            rw subset_of_empty M a at h12, 
            rw h12 at *,
            rw zero_definition,
            rw singleton1, 
            rw subset_of_empty M Λ, simp,
            split,
            {
              exact h9,
            },
            {
              rw full_extensionality,
              intro t,
              rw binary_union_axiom,
              rw minus_members,
              have h12:= emptyset_axiom t,
              simp,
            }
          }
        }
      end,
    have step: ∀ (q:M), q ∈ Z_orderbyaddition M → (∃ (u:M), u ∈ 𝕊 q) → 𝕊 q ∈ Z_orderbyaddition M:=
      begin
        intros q h2 h3,
        rw Z_orderbyaddition_members at h2,
        rw Z_orderbyaddition_members,
        cases h2 with h4 h5,

        split,
        {
          exact successorF M q h4 h3, 
        },
        {
          intros p h6,
          split,
          {  --left to right
            intro h7, 
            have h8:= lessthansuccessor2 M p q h6  h4 h7,
            cases h8 with h9 h10,
            { 
              rw h5 p h6 at h9,
              cases h9 with k h10,
              use 𝕊 k,
              cases h10 with h11 h12,
              split,
              { 
                have h19:= successorF M q h4 h3, 
                rw← h12 at h19,
                rw←  addition_equation at h19,
                have h20:=cardinalsinhabited M (p + 𝕊 k) h19,
                cases h20 with x h21,
                rw addition_members at h21,
                cases h21 with u h22,
                cases h22 with v h23,
                rcases h23 with ⟨ h24, h25, h26, h27⟩, 
                have h28:= successorF M k h11 ⟨v, h26⟩, 
                exact h28,    
              },
              {
                rw addition_equation,
                rw h12,
              }
            },
            {
              use zero, 
              rw right_identityNF,
              exact ⟨ zeroF M, h10⟩, 
            }
          },
          {  --right to left
            intro h7,
            cases h7 with k h8,
            cases h8 with h9 h10,
            cases h3 with u h11,
            rw full_extensionality at h10,
            specialize h10 u,
            rw← h10 at h11,
            rw addition_members at h11,
            cases h11 with a h12,
            cases h12 with b h13,
            rcases h13 with ⟨ h14, h15, h16, h17⟩, 
            rw le_definition,
            use a, use a ∪ b, 
            repeat {split},
            {
              exact h15,
            },
            {
              rw← h14,
              rw← h10,
              rw addition_members,
              use a, use b,
              exact ⟨ h14, h15, h16, h17⟩, 
            },
            {
              exact subset_union2 M a b, 
            },
            {
              rw full_extensionality,
              intro t,
              repeat {rw binary_union_axiom},
              rw minus_members,
              rw binary_union_axiom,
              split,
              {
                intro h18,
                cases h18 with h19 h20,
                {
                  left,
                  exact h19,
                },
                {
                  right,
                  rw full_extensionality at h17,
                  specialize h17 t,
                  have h21:= emptyset_axiom t,
                  rw← h17 at h21,
                  rw intersection_axiom at h21,
                  rw and_comm at h21,
                  push_neg at h21,
                  have h22:= h21 h20,
                  split,
                  {
                    right,
                    exact h20,
                  },
                  {
                    exact h22,
                  }
                }
              },
              {
                intro h18,
                cases h18 with h19 h20,
                {
                  left,
                  exact h19,
                },
                {
                  cases h20 with h21 h22,
                  exact h21, 
                }
              }
            }
          }
        }
      end,
    intros q h, 
    rw F_members at h, 
    specialize h ( Z_orderbyaddition M),
    have h3:= h (and.intro base  step), 
    rw ( Z_orderbyaddition_members M) at h3, 
    cases h3 with h5 h6, 
    exact h6, 
  end

lemma qleqplusq: ∀ (q:M), q ∈ 𝔽 → q + q ∈ 𝔽 → q ≤ q + q:=
  assume q,
  begin
    intros h h2,
    have h3:= xlessthan_xplusy M q q h h h2,
    exact h3, 
  end

#axioms_all  --This file is clean