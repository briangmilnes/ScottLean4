import ChurchNumbers10
-- proof that (if 𝔽 is infinite) every Church number is (not-not) the order of some permutation on a finite set

variables (M:Type) [Model M] (a b x y z u v w X R W κ μ ℓ : M)

open Model 


lemma allorders: ℕℕ ∈ FINITE M → (∀ (x:M), x ∈ 𝔽 → 𝕊 x ∈ 𝔽) → ∀ (q:M), q ∈ ℕℕ → ¬ q = ChurchZero → ¬ q = S ChurchZero → ¬¬ ∃ (X f a:M), X ∈ FINITE M ∧ cyclicperm M f X a ∧ permorder M f X a q:=
  assume hNfinite hSmaps,
  begin
    have h2:= kinstem M hNfinite,
    cases h2 with k h3,
    cases h3 with n h4,
    rcases h4 with ⟨ hk, hn, hkn, hskn, hstem⟩,
    have base: ChurchZero ∈ Z_allorders M:=
      begin
        rw Z_allorders_members,
        split,
        {
          exact zeroN M,
        },
        {
          intro h,
          contradiction,
        }
      end,
    have step: ∀ (q:M), q ∈ Z_allorders M → ¬ q = n → S q ∈ Z_allorders M:=
      begin
        intros q h hqn,
        rw Z_allorders_members at h,
        cases h with hq h6,
        rw Z_allorders_members,
        split,
        {
          exact successorN M q hq,
        },
        {
          intros h7 h8,
          have h9:= successorN M ChurchZero (zeroN M),
          have h109: ¬ q = ChurchZero:=
            begin
              intro h,
              rw h at h8,
              contradiction,
            end,
          have h80:= finitedecidable M ℕℕ hNfinite,
          rw decidable_members at h80,
          have h81:= h80 q (S ChurchZero) ⟨ hq, h9⟩,
          cases h81 with h10 h11,
          {
            rw h10 at *,
            intro h,
            have h12:= emptyneqsingletonempty M,
            have h14:= simplestperm M hNfinite Λ (single Λ) h12,
            cases h14 with f h15,
            rcases h15 with ⟨ h16, h17, h18 ⟩,
            apply h,
            use {Λ,single Λ},
            use f,
            use Λ,
            have h19: {Λ,single Λ} ∈ FINITE M:=
              begin
                have h20:= singleton_finite M Λ,
                have h21: ¬ single (Λ:M) ∈ single Λ :=
                  begin 
                    rw singleton1,
                    rw sym at h12, 
                    exact h12,
                  end,
                have h22:= finite_adjoin M (single Λ) (single Λ) ⟨ h20, h21⟩,
                have h23: {(Λ:M), single Λ} = (single (Λ:M) ∪ single (single Λ)):=
                  begin
                    rw full_extensionality,
                    intros t,
                    rw pairing_axiom,
                    rw binary_union_axiom,
                    repeat{rw singleton1},
                  end,
                rw h23,
                exact h22, 
              end, 
            exact ⟨ h19, h17, h18⟩,
          },
          {
            intro h,
            have h20: ¬ q = ChurchZero:=
              begin
                intro h21,
                rw h21 at *,
                contradiction,
              end,
            have h21:= h6 h20 h11,
            have h22:= orderstep3 M k n q hk hn hNfinite hskn hkn hstem hq hqn h20,
            apply h21,
            rw not_exists,
            intros X,
            rw not_exists,
            intro f,
            rw not_exists,
            intro a,
            intro h23,
            have h25: ∃ (b:M), ¬ (b = a) ∧ ‹ b,a › ∈ f:=
              begin
                rcases h23 with ⟨ h30, h31, h32⟩,
                unfold cyclicperm at h31,
                rcases h31 with ⟨ h33, h34, h35⟩,
                cases h33 with h36 h37,
                unfold injection at h36,
                rcases h36 with ⟨ h38, h39, h40, h41, h42⟩,
                unfold oneone at h38,
                unfold permorder at h32,
                rcases h32 with ⟨ h43, h44, h45, h46⟩,
                unfold onto at h37,
                have h47:= h37 a h34,
                cases h47 with b h48,
                use b,
                cases h48 with hb h49,
                rw and_comm,
                split,
                {
                  exact h49,
                },
                { 
                  intro h,
                  rw h at *,
                  have h51:= Apdef M f h40 a a h49,
                  have h52: Ap (Ap (S ChurchZero) f) a = a:=
                    begin
                      have h53:= ApOne M f h40 h39,
                      rw←  h53 at h51,
                      rw sym at h51,
                      exact h51,
                    end,
                  have h55: S ChurchZero ≼ q:= 
                    begin
                      have h56:= prectrichotomy1 M hNfinite k n hstem hn hkn hskn (S ChurchZero) q (successorN M ChurchZero (zeroN M)) hq,
                      cases h56 with h57 h58,
                      {
                        exact h57,
                      },
                      {
                        have h60:= nneqzero M k n hstem hn hkn hskn,
                        rw sym at h60,
                        have h59:= preceqsuccessor M hNfinite k n hstem hn hkn hskn q ChurchZero hq (zeroN M) h60, 
                        rw h59 at h58,
                        cases h58 with h61 h62,
                        {
                          have h63:= preceqzero M hNfinite k n hstem hn hkn hskn q hq h61,
                          rw h63 at *,
                          contradiction,
                        },
                        {
                          rw h62 at *,
                          have h64:= preceqreflexive M hNfinite k n hstem hn hkn hskn (S ChurchZero) (successorN M ChurchZero (zeroN M)),
                          exact h64,
                        }
                      }
                    end,
                  have h54:= h45 (S ChurchZero) (successorN M ChurchZero (zeroN M)) h55 (successoromitszero M ChurchZero (zeroN M)) h52,  
                  rw sym at h54,
                  contradiction,
                }
              end,
            cases h25 with b h40,
            cases h40 with h26 h41,
            have h27:= enlarge M hSmaps X h23.left,
            have h28: ¬ exists (c:M), ¬ c ∈ X:=
              begin
                intro h29,
                cases h29 with c h30,
                rw sym at h26, 
                set g:=  (f - single  ‹ b,a ›  ∪ single  ‹ b,c ›  ∪ single  ‹ c,a › ) with h50,
                have h31:= h22 X f a b c g h23.left h30 h41 h26 h50 h23.right.left h23.right.right,
                apply h,
                use X ∪ (single c),
                use g,
                use a,
                split,
                {
                  have h42:= finite_adjoin M X c ⟨ h23.left, h30⟩,
                  exact h42,
                },
                {
                  rw and_comm,
                  split,
                  {
                    exact h31,
                  },
                  {
                    have h60:= orderstep4 M k n q hk hn hNfinite hskn hkn hstem hq hqn h20,
                    have h61:= h60 X f a b c g h23.left h30 h41 h26 h50 h23.right.left h23.right.right,
                    exact h61,
                  }
                }
              end,
            contradiction,
          }
        }
      end,
    intros q hq,
    have h100:= finiteinduction M hNfinite k n hstem hn hkn hskn (Z_allorders M) ⟨ base, step⟩,
    rw subset_definition at h100,
    have h101:= h100 q hq,
    rw Z_allorders_members at h101,
    exact h101.right,
  end