-- This file proves 2^x not empty and x > 6 implies 2^x > 2*x^2
  
import inf18 
variables (M:Type) [Model M] (a b x y z u v w X R W κ μ ℓ : M)

open Model 

lemma zerolex: ∀(x:M),x ∈ 𝔽→ zero ≤ x:= 
  assume x hx,
  begin
    have h3:= cardinalsinhabited M x hx,
    cases h3 with u h4,
    rw le_definition,
    use Λ, use u,
    rw zero_members,
    split,
    {
      reflexivity,
    },
    {
      split,
      {
        exact h4,
      },
      {
        split,
        {
          rw subset_definition,
          intros z hz,
          have h6:= emptyset_axiom z,
          contradiction,
        },
        {
          rw full_extensionality,
          intros t,
          split,
          {
            intros h,
            rw binary_union_axiom,
            right,
            rw minus_members,
            have h3:= emptyset_axiom t,
            exact ⟨ h, h3⟩,
          },
          {
            intros h9,
            rw binary_union_axiom at h9,
            cases h9 with h10 h11,
            {
              have h12:= emptyset_axiom t,
              contradiction,
            },
            {
              rw minus_members at h11,
              exact h11.1,
            }
          }
        }
      }
    }
  end  

lemma le_square_helper: ∀(y:M), y ∈ 𝔽→ 𝕊 y ∈ 𝔽 → (𝕊 y) * (𝕊 y) ∈ 𝔽 → y * y ∈ 𝔽:=
  assume y hy hsy h4,
  begin
    have h4copy:= h4,
    have h5:= multiplication M (𝕊 y) y hsy hy hsy,
    rw h5 at h4,
    have h6:= multiplication_commutative M y hy (𝕊 y) hsy,
    rw h6 at h4,
    have h7:= multiplication M y y hy hy hsy,
    rw h7 at h4,
    have h8:= associativityNF M (y*y)  y (𝕊 y),
    rw h8 at h4,
    have h9:= cardinalsinhabited M (𝕊 y) hsy,
    have h10:= multiplicationSF2 M y y hy hy,
    rw h6 at h5,
    rw h7 at h5, 
    rw h8 at h5,
    rw full_extensionality at h5,
    have h12: ∃ (u:M), u ∈ (𝕊 y)* (𝕊 y):=
      cardinalsinhabited M ((𝕊 y)* (𝕊 y)) h4copy,
    cases h12 with u h20,
    specialize h5 u,
    rw h5 at h20,
    have h13: ∃ (v:M), v ∈ y *y:=
      begin
        have h14:= addition_members M (y*y) (y + 𝕊 y) u,
        rw h14 at h20,
        cases h20 with a h21,
        cases h21 with b h22,
        have h23:= h22.2.1,
        use a,
        exact h23,
      end,
    have h11:= inhabitedSF M (y*y) h10 h13,
    exact h11,
  end  

lemma le_square_helper2: ∀(y:M), y ∈ 𝔽 → (𝕊 y) ∈ 𝔽 → 
   (𝕊 y) * (𝕊 y) ∈ 𝔽 → y + (𝕊 y) ∈ 𝔽:=
   assume y hy hsy h3,
   begin
     have h4:= multiplication M (𝕊 y) y hsy hy hsy,
     rw←  multiplication_commutative M (𝕊 y) hsy y hy at h4,
     have h5:= multiplication M y y hy hy hsy,
     rw h5 at h4,
     rw associativityNF at h4,
     have h6:= cardinalsinhabited M ((𝕊 y)*(𝕊 y)) h3,
     simp_rw h4 at h6,
     cases h6 with u h7,
     rw addition_members at h7,
     cases h7 with a h8,
     cases h8 with b h9,
     rcases h9 with ⟨ h10, h11, h12,h13⟩,
     have h14:= inhabited_sum M (𝕊 y) hsy y hy ⟨ b, h12⟩,
     exact h14,
   end 

lemma successorsquare: ∀(y:M), y ∈ 𝔽 → (𝕊 y) ∈ 𝔽 → 
   (𝕊 y) * (𝕊 y) ∈ 𝔽  → (𝕊 y) * (𝕊 y) = y * y + y + (𝕊 y):=
  assume y hy hsy h3,
  begin
    have h4:= multiplication M (𝕊 y) y hsy hy hsy,
    rw←  multiplication_commutative M (𝕊 y) hsy y hy at h4,
    have h5:= multiplication M y y hy hy hsy,
    rw h5 at h4,
    exact h4,
  end

lemma le_square: ∀(y:M), y ∈ 𝔽  → ∀(x:M), x ∈ 𝔽  → y* y ∈ 𝔽 → x ≤ y → ( x*x ∈ 𝔽 ∧    x * x ≤ y * y) :=  
  begin
    have base: zero ∈ Z_le_square M:=
      begin
        rw Z_le_square_members,
        split,
        {
          exact zeroF M,
        },
        {
          intros x hx h3 h4,
          have h5:= le_zero M x hx h4,
          rw h5,
          rw zero_mulNF M zero (zeroF M),
          have h6:= le_reflexive M zero (zeroF M),
          split,
          {
            exact zeroF M,
          },
          {
            exact h6,
          }
        }
      end,
    have step: ∀ (y:M), y ∈ Z_le_square M → (∃ (u:M), u ∈ 𝕊 y) → 𝕊 y ∈ Z_le_square M:=
      begin
        intros y h3 hsy,
        rw Z_le_square_members at h3,
        rw Z_le_square_members,
        cases h3 with hy h4,
        have hsyf:= successorF M y hy hsy,
        split,
        {
          exact hsyf,
        },
        { 
          intros x hx h5 h6,
          have h7:= lessthansuccessor2 M x y hx hy h6,
          cases h7 with h8 h9,
          {
            have h10:= h4 x hx,
            have h11:= le_square_helper M y hy hsyf h5,
            have h12:= h10 h11 h8,
            cases h12 with h13 h14,
            split,
            {
              exact h13,
            },
            {  
      
              have hsyf:= successorF M y hy hsy,
              have h17:= le_square_helper2 M y hy hsyf h5,
              have h18:= zerolex M (y + 𝕊 y) h17,
              have h15:= addorder M (x*x) (y*y) zero (y + 𝕊 y) h13 h11 (zeroF M) h17,
              have hsyf:= successorF M y hy hsy,
              have h16:= successorsquare M y hy hsyf h5,
              rw h16 at h5,
              rw  associativityNF at h5,
              have h20:= h15 h5 h14 h18,
              rw right_identityNF at h20,
              rw h16,
              rw associativityNF,
              exact h20,
            }
          },
          {
            rw h9 at *,
            split,
            {
              exact h5,
            },
            {
              have h20:= le_reflexive M ((𝕊 y)* (𝕊 y)) h5,
              exact h20,
            }
          }
        }
      end, 
    intros y hy,
    rw F_members at hy,
    have h30:= hy (Z_le_square M) ⟨ base, step⟩,
    rw Z_le_square_members at h30,
    cases h30 with hy h31,
    exact h31,
  end

/- this lemma uses sorry and is not used
lemma expquad2: ∀(m:M), MAXIMAL M (m) → ∀(x:M), x ∈ SF M → (¬ x*x = Λ) → two < x →  x+x+one < x * x :=
  assume m hmax,
  begin
    have base: zero ∈ Z_expquad2 M:=
      begin
        rw Z_expquad2_members M,
        split,
        {
          exact zeroSF M,
        },
        { intros h2 h3,
          have h4:= nothinglessthanzero M two (twoF M),
          contradiction,
        }
      end,
    have step: ∀(x:M), x ∈ Z_expquad2 M  → 𝕊 x ∈ Z_expquad2 M:=
      begin
        intros x h3,
        rw Z_expquad2_members at h3,
        rw Z_expquad2_members M,
        cases h3 with hx h6,
        split,
        {
          exact successorSF M x hx,
        },
        {
          intros h9 h10,
          have h80:= maximalcases M m hmax x hx,
          have hxf:x ∈ 𝔽:= 
            begin
              cases h80 with h82 h83,
              {
                exact h82,
              },
              {
                rw h83 at *,
                rw successorLambda at h9,
                have h10:= lambdatimeslambda M m hmax,
                contradiction,
              }
            end,
          have hsxf: 𝕊 x ∈ 𝔽:=
            begin
              have h84:= maximalcases M m hmax (𝕊 x) (successorSF M x hx),
              cases h84 with h85 h86,
              {
                exact h85,
              },
              {
                rw h86 at h9,
                have h87:= lambdatimeslambda M m hmax,
                contradiction,
              }
            end,
          have h88:= cardinalsinhabited M (𝕊 x) hsxf,
          have h81:=  lessthansuccessor3 M two x (twoF M) hxf h88,
          rw h81 at h10,
          cases h10 with h11 h12,
          { --case 2 in the paper, 2 < x
            sorry,
            
          },  
          {  --case 1 in the paper, x = 2
             sorry,
          }
        }
      end, 
    intros x hx,
    rw SF_members at hx,
    have h30:= hx (Z_expquad2 M) base step,
    rw Z_expquad2_members at h30,
    exact h30.2,
  end
-/  

#axioms_all

