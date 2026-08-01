-- Multiplication and Division in ℕℕ 

import ChurchNumbers3

variables (M:Type) [Model M] (a b x y z u v w X R W κ μ ℓ : M)
-- using ℓ where the source text has λ because you can't use λ for a variable.

open Model 

lemma ChurchMultiplicationMaps: ∀ (y:M),y ∈ ℕℕ → ∀ (x:M), x ∈ ℕℕ → x ⊗ y ∈ ℕℕ:=
  begin
    have base: ChurchZero ∈ Z_ChurchMultiplicationMaps M:=
      begin
        rw Z_ChurchMultiplicationMaps_members,
        split,
        {
          exact zeroN M,
        },
        {
          intros x hx,
          have h3:= ChurchMultiplicationBase x hx,
          rw h3, 
          exact zeroN M,
        }
      end,
    have step: ∀ (y:M), y ∈ Z_ChurchMultiplicationMaps M → S y ∈ Z_ChurchMultiplicationMaps M:=
      begin
        intros y h,
        rw Z_ChurchMultiplicationMaps_members at h,
        cases h with hy hIH,
        rw Z_ChurchMultiplicationMaps_members,
        split,
        {
          exact successorN M y hy,
        },
        {
          intros x hx,
          have h5:= ChurchMultiplicationEquation x y hx hy,
          rw h5,
          have h6:= hIH x hx,
          have h7:= ChurchAdditionMaps M x hx (x ⊗ y) h6,
          exact h7,
        }
      end,
    intros y hy,
    rw N_members at hy,
    specialize hy (Z_ChurchMultiplicationMaps M),
    have h3:= hy (and.intro base step), 
    rw Z_ChurchMultiplicationMaps_members M at h3,
    exact h3.right, 
  end

lemma zerotimes: ∀ (y:M), y ∈ ℕℕ → ChurchZero ⊗ y = ChurchZero:=
  begin
    have base: ChurchZero ∈ Z_zerotimes M:=
      begin
        rw Z_zerotimes_members,
        split,
        {
          exact zeroN M,
        },
        {
          have h4:= ChurchMultiplicationBase ChurchZero (zeroN M),
          exact h4,
        }
      end,
    have step: ∀ (y:M), y ∈ Z_zerotimes M → S y ∈ Z_zerotimes M:=
      begin
        intros y h2,
        rw Z_zerotimes_members at h2,
        rw Z_zerotimes_members,
        cases h2 with hy hIH,
        split,
        {
          exact successorN M y hy,
        },
        {
          have h3:= ChurchMultiplicationEquation ChurchZero y (zeroN M) hy,
          rw h3,
          have h4: ChurchZero ⊗ y ∈ ℕℕ :=
            ChurchMultiplicationMaps M y hy ChurchZero (zeroN M),
          rw ChurchZero_equation (ChurchZero ⊗ y) h4,
          exact hIH,
        }
      end,
    intros y hy,
    rw N_members at hy,
    specialize hy (Z_zerotimes M),
    have h3:= hy (and.intro base step), 
    rw Z_zerotimes_members M at h3,
    exact h3.right, 
  end

lemma successortimes: ∀ (y:M), y ∈ ℕℕ  → ∀ (x:M),x ∈ ℕℕ → S x ⊗ y = x ⊗ y ⊕ y:=
  begin
    have base: ChurchZero ∈ Z_successortimes M:=
      begin
        rw Z_successortimes_members,
        split,
        {
          exact zeroN M,
        },
        {
          intros x hx,
          rw ChurchMultiplicationBase  (S x) (successorN M x hx),
          rw ChurchMultiplicationBase x hx,
          rw ChurchZero_equation,
          exact zeroN M,
        }
      end,
    have step: ∀ (y:M), y ∈ Z_successortimes M → S y ∈ Z_successortimes M:=
      begin
        intros y h2,
        rw Z_successortimes_members at h2,
        cases h2 with hy hIH,
        rw Z_successortimes_members,
        split,
        {
          exact successorN M y hy,
        },
        {
          intros x hx,
          have h4:= hIH x hx,
          rw ChurchMultiplicationEquation (S x) y (successorN M x hx) hy,
          rw h4,
          rw ChurchMultiplicationEquation x y hx hy,
          have h3:= ChurchMultiplicationMaps M y hy x hx,
          have h6:= ChurchAdditionAssociative M y hy (x ⊗ y) (S x) h3  (successorN M x hx),
          rw h6,
          have h5:= ChurchSuccessorShift M x hx y hy, 
          rw h5,
          rw ChurchAdditionCommutative M x hx (S y) (successorN M y hy),
          rw←  ChurchAdditionAssociative M x hx (x ⊗ y) (S y) h3 (successorN M y hy),
        }
      end,
    intros y hy,
    rw N_members at hy,
    specialize hy (Z_successortimes M),
    have h3:= hy (and.intro base step), 
    rw Z_successortimes_members M at h3,
    exact h3.right, 
  end

lemma Church_leftdistrib: ∀(x y z:M), x ∈ ℕℕ → y ∈ ℕℕ → z ∈ ℕℕ →  x ⊗ (y ⊕ z) = x ⊗ y ⊕ x  ⊗ z:=
  begin
    have h3: ∀(x:M), x ∈ ℕℕ → ∀ (y z:M),y ∈ ℕℕ → z ∈ ℕℕ → x ⊗ (y ⊕ z) = x ⊗ y ⊕ x ⊗ z:=
      begin
        have base: ChurchZero ∈ Z_Church_leftdistrib M:=
          begin
            rw Z_Church_leftdistrib_members,
            split,
            {
              exact zeroN M,
            },
            {
              intros x y hx hy,
              rw zerotimes M (x ⊕ y) (ChurchAdditionMaps M y hy x hx),
              rw zerotimes M x hx,
              rw zerotimes M y hy,
              rw ChurchZero_equation ChurchZero (zeroN M),
            }
          end,
        have step: ∀ (x:M), x ∈ Z_Church_leftdistrib M → S x ∈ Z_Church_leftdistrib M:=
          begin
            intros x h2,
            rw Z_Church_leftdistrib_members at h2,
            cases h2 with hx hIH,
            rw Z_Church_leftdistrib_members,
            split,
            {
              exact successorN M x hx,
            },
            {
              intros y z hy hz,
              rw successortimes M (y ⊕ z) (ChurchAdditionMaps M z hz y hy) x hx,
              have h5:= hIH y z hy hz,
              rw h5,
              rw successortimes M y hy x  hx,
              rw successortimes M z hz x hx,
              have h6:= ChurchAdditionAssociative M,
              have h7:= ChurchMultiplicationMaps M y hy x hx,
              have h10:= ChurchMultiplicationMaps M z hz x hx, 
              have h8:= ChurchAdditionMaps M z hz (x ⊗ z) h10,
              have h9:= h6 y hy (x ⊗ y)( x ⊗ z ⊕ z) h7 h8,
              rw h9,
              have h11:= h6 (x ⊗ z) h10 y z hy hz,
              rw← h11,
              have h12:= ChurchAdditionCommutative M (x ⊗ z) h10 y hy,
              rw h12,
              have h14:= ChurchAdditionMaps M z hz y hy,
              rw← h6,
              rw← h6,
              rw← h6,
              exact h10,
              exact h7,
              exact hy,
              exact ChurchAdditionMaps M y hy (x ⊗ z) h10,
              exact h7,
              exact hz,
              exact hy,
              exact ChurchAdditionMaps M (x ⊗ z) h10 (x ⊗ y) h7,
              exact hz,
            }
          end,
        intros x hx,
        rw N_members at hx,
        specialize hx (Z_Church_leftdistrib M),
        have h3:= hx (and.intro base step), 
        rw Z_Church_leftdistrib_members M at h3,
        cases h3 with h4 h5,
        exact h5,
      end,
    intros x y z hx hy hz,
    exact h3 x hx y z hy hz,
  end 

lemma Church_rightdistrib: ∀(z:M), z ∈ ℕℕ →   ∀ (x y:M),x ∈ ℕℕ → y ∈ ℕℕ → (x ⊕ y) ⊗ z = x ⊗ z ⊕ y ⊗ z :=
  begin
    have base: ChurchZero ∈ Z_Church_rightdistrib M:=
      begin
        rw Z_Church_rightdistrib_members,
        split,
        {
          exact zeroN M,
        },
        {
          intros x y hx hy,
          have h3:= ChurchAdditionMaps M y hy x hx,
          rw ChurchMultiplicationBase (x ⊕  y) h3,
          rw ChurchMultiplicationBase x hx,
          rw ChurchMultiplicationBase y hy,
          rw ChurchZero_equation,
          exact zeroN M,
        }
      end,
    have step: ∀ (z:M), z ∈ Z_Church_rightdistrib M →  S z ∈ Z_Church_rightdistrib M:=
      begin
        intros z h3,
        rw Z_Church_rightdistrib_members at h3,
        cases h3 with hz h4,
        rw Z_Church_rightdistrib_members,
        split,
        {
          exact successorN M z hz,
        },
        { 
          intros x y hx hy,
          have hIH:= h4 x y hx hy,
          have hxy:= ChurchAdditionMaps M y hy x hx,
          have hyz:= ChurchMultiplicationMaps M z hz y hy,
          have hxz:= ChurchMultiplicationMaps M z hz x hx,
          rw ChurchMultiplicationEquation  (x ⊕ y) z hxy hz, 
          rw hIH,
          rw ChurchMultiplicationEquation x z hx hz,
          rw ChurchMultiplicationEquation y z hy hz,
          rw ChurchAdditionAssociative,
          rw ChurchAdditionAssociative,
          have h6 : y ⊗ z ⊕ (x ⊕ y) = x ⊕ (y ⊗ z ⊕ y):=
            begin
              rw← ChurchAdditionAssociative,
              rw← ChurchAdditionAssociative,
              have h8:= ChurchAdditionCommutative M x hx (y ⊗ z) hyz,
              rw h8,
              exact hyz,
              exact hx,
              exact hy,
              exact hx,
              exact hyz,
              exact hy,
            end,
          rw h6,
          exact hx,
          exact hxz,
          exact ChurchAdditionMaps M y hy (y ⊗ z) hyz,
          exact hyz,
          exact hxz,
          exact ChurchAdditionMaps M y hy x hx,
        }
      end,
    intros z hz,
    rw N_members at hz,
    specialize hz (Z_Church_rightdistrib M),
    have h3:= hz (and.intro base step),
    rw Z_Church_rightdistrib_members M at h3,
    cases h3 with h4 h5,
    exact h5,
  end

lemma ChurchMultiplicationAssociative: ∀ (x y z:M),x ∈ ℕℕ → y ∈ ℕℕ → z ∈ ℕℕ → x ⊗ (y ⊗ z) = x ⊗ y ⊗ z:=
  begin
    have h: ∀ (y:M), y ∈ ℕℕ → ∀ (x z:M),  x ∈ ℕℕ → z ∈ ℕℕ → x ⊗ (y ⊗ z) = x ⊗ y ⊗ z:=
      begin
        have base: ChurchZero ∈ Z_ChurchMultiplicationAssociative M:=
          begin
            rw Z_ChurchMultiplicationAssociative_members,
            split,
            {
              exact zeroN M,
            },
            {
              intros x z hx hz,
              rw ChurchMultiplicationBase,
              rw zerotimes M,
              rw ChurchMultiplicationBase,
              exact hx,
              exact hz,
              exact hx,
            }
          end,
        have step: ∀(y:M), y ∈ Z_ChurchMultiplicationAssociative M → S y ∈ Z_ChurchMultiplicationAssociative M:=
          begin
            intros y h3,
            rw Z_ChurchMultiplicationAssociative_members at h3,
            cases h3 with hy h5,
            rw Z_ChurchMultiplicationAssociative_members,
            split,
            {
              exact successorN M y hy,
            },
            {
              intros x z hx hz,
              have hxy:= ChurchMultiplicationMaps M y hy x hx,
              have hyz:= ChurchMultiplicationMaps M z hz y hy,
              have hIH:= h5 x z hx hz,
              rw successortimes,
              rw Church_leftdistrib,
              rw hIH,
              rw← Church_rightdistrib,
              rw ChurchMultiplicationEquation,
              exact hx,
              exact hy,
              exact hz,
              exact hxy,
              exact hx,
              exact hx,
              exact hyz,
              exact hz,
              exact hz,
              exact hy,
            }
          end,
        intros z hz,
        rw N_members at hz,
        specialize hz (Z_ChurchMultiplicationAssociative M),
        have h3:= hz (and.intro base step),
        rw Z_ChurchMultiplicationAssociative_members M at h3,
        cases h3 with h4 h5,
        exact h5,
      end,
    intros x y z hx hy hz,
    exact h y hy x z hx hz,
  end

lemma ChurchMultiplicationCommutative: ∀ (x y:M), x ∈ ℕℕ → y ∈ ℕℕ →  x ⊗ y = y ⊗ x:=
  begin
    have h: ∀ (y:M), y ∈ ℕℕ → ∀ (x:M), x ∈ ℕℕ → x ⊗ y = y ⊗ x:=
      begin
        have base: ChurchZero ∈ Z_ChurchMultiplicationCommutative M:=
          begin
            rw Z_ChurchMultiplicationCommutative_members,
            split,
            {
              exact zeroN M,
            },
            {
              intros x hx,
              rw ChurchMultiplicationBase,
              rw zerotimes,
              exact hx,
              exact hx,
            }
          end,
        have step: ∀ (y:M), y ∈ Z_ChurchMultiplicationCommutative M → S y ∈ Z_ChurchMultiplicationCommutative M:=
          begin
            intros y h3,
            rw Z_ChurchMultiplicationCommutative_members at h3,
            cases h3 with hy h4,
            rw Z_ChurchMultiplicationCommutative_members,
            split,
            {
              exact successorN M y hy,
            },
            {
              intros x hx,
              have hIH:= h4 x hx,
              rw ChurchMultiplicationEquation,
              rw successortimes,
              rw hIH,
              exact hx,
              exact hy,
              exact hx,
              exact hy,
            }
          end,
        intros y hy,
        rw N_members at hy,
        specialize hy (Z_ChurchMultiplicationCommutative M),
        have h3:= hy (and.intro base step),
        rw Z_ChurchMultiplicationCommutative_members M at h3,
        cases h3 with h4 h5,
        exact h5,
      end,
    intros x y hx hy,
    exact h y hy x hx,
  end



lemma CSGAp: ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n →
∀(x:M),x ∈ LOOP n → Ap (CSG M n) x = S x:=
  begin
    intros hfinite k n hk hn hkn hskn x hx,
    rw full_extensionality,
    intro t,
    rw Ap_members,
    split,
    {
      intro h,
      cases h with y h3,
      cases h3 with h4 h5,
      rw CSG_members at h4,
      cases h4 with z h6,
      cases h6 with h7 h8,
      rw ordered_pair_equality at h7,
      cases h7 with h9 h10,
      rw← h9 at *,
      rw h10 at *,
      exact h5,
    },
    {
      intro h,
      use S x,
      rw and_comm,
      split,
      {
        exact h,
      },
      {
        rw CSG_members,
        use x,
        simp,
        exact hx,
      }
    }
  end

lemma CSGperm: ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n →
permutation M (CSG M n) (LOOP n) :=
  begin
    intros hfinite k n hk hn hkn hskn,
    unfold permutation,
    have hRel: Rel (CSG M n):=
      begin
        rw Rel_definition,
        intros z h,
        rw CSG_members at h,
        cases h with x h3,
        cases h3 with h4 h5,
        use x, use S x,
        exact h4,
      end,
    split,
    {
      unfold injection,
      repeat {split},
      {
        exact hRel,
      },
      {
        intros x y h,
        cases h with h3 h4,
        rw CSG_members at h4,
        cases h4 with z h5,
        cases h5 with h6 h7,
        rw ordered_pair_equality at h6,
        cases h6 with h8 h9,
        rw ← h8 at *,
        rw h9 at *,
        have h10:= L1 M k n hk hn hkn hskn,
        cases h10 with h11 h12,
        exact h12 x h7,
      },
      {
        intros x y z h,
        rcases h with ⟨ h3, h4, h5⟩,
        rw CSG_members at h4 h5,
        cases h5 with p h6,
        cases h4 with q h7,
        cases h6 with h8 h9,
        cases h7 with h10 h11,
        rw ordered_pair_equality at h8 h10,
        cases h8 with h12 h13,
        cases h10 with h14 h15,
        rw← h12 at *,
        rw← h14 at *,
        rw h13, 
        rw h15,
      },
      {
        intros x h,
        use S x,
        have h10:= L1 M k n hk hn hkn hskn,
        have h11:= h10.right x h,
        split,
        {
          exact h11,
        },
        {
          rw CSG_members,
          use x,
          simp,
          exact h,
        }
      },
      {
        intros x u y h,
        rcases h with ⟨ h3, h4, h5⟩,
        rw CSG_members at h3 h4,
        cases h4 with p h7,
        cases h3 with q h6,
        cases h7 with h8 h9,
        cases h6 with h10 h11,
        rw ordered_pair_equality at h8 h10,
        cases h10 with h12 h13,
        cases h8 with h14 h15,
        rw← h12 at *,
        rw← h14 at *,
        rw h13 at h15,
        have h16:= looponeone M hfinite k n hk hn hkn hskn,
        have h17:= h16 x u h11 h9 h15,
        exact h17,
      },
      {
        intros x y h,
        cases h with h3 h4,
        rw CSG_members at h3,
        cases h3 with p h5,
        cases h5 with h6 h7,
        rw ordered_pair_equality at h6,
        cases h6 with h8 h9,
        rw← h8 at *,
        exact h7,
      },
      {
        exact hRel,
      },
      {
        rw FUNC_members,
        intros x y z h3 h4,
        rw CSG_members at h3 h4,
        cases h3 with p h5,
        cases h4 with q h6,
        cases h5 with h7 h8,
        cases h6 with h9 h10,
        rw ordered_pair_equality at h7 h9,
        cases h9 with h11 h12,
        cases h7 with h13 h14,
        rw← h11 at *,
        rw← h13 at *,
        rw h12,
        rw h14,
      },
      {
        rw subset_definition,
        intros z h,
        rw domain_axiom at h,
        cases h with y h3,
        rw CSG_members at h3,
        cases h3 with x h4,
        cases h4 with h5 h6,
        rw ordered_pair_equality at h5,
        cases h5 with h7 h8,
        rw h7 at *,
        exact h6,
        exact hRel,
      },
      {
        rw subset_definition,
        intros z h,
        rw range_axiom (CSG M n) hRel at h,
        cases h with x h4,
        rw CSG_members at h4,
        cases h4 with u h5,
        cases h5 with h6 h7,
        rw ordered_pair_equality at h6,
        cases h6 with h8 h9,
        rw h8 at *,
        rw h9, 
        have h16:= L1 M k n hk hn hkn hskn,
        exact h16.right u h7,
      }
    },
    {
      unfold onto,
      intros y h,
      have h3: ¬ (ChurchZero ∈ LOOP n):=
        begin 
          intro h2,
          have h4:= (S1 M).left,
          have h5:= LcapS M k n hk hn hkn hskn,
          rw full_extensionality at h5,
          specialize h5 ChurchZero,
          rw intersection_axiom at h5,
          have h6:= h5.mp ⟨ h2, h4⟩, 
          have h7:= emptyset_axiom ChurchZero,
          contradiction,
        end,
      have h4: ¬ (y = ChurchZero):=
        begin
          intro h5,
          rw h5 at *,
          contradiction,
        end,
      have h5:= LcupS M k n hk hn hkn hskn,
      rw full_extensionality at h5,
      specialize h5 y,
      rw binary_union_axiom at h5,
      have h6:= h5.mpr (or.inl h),
      have h7:= looponto M k n hk hn hkn hskn y h,
      cases h7 with x h8,
      cases h8 with h9 h10,
      use x,
      split,
       {
         exact h9,
       },
       {
         rw← h10,
         rw CSG_members,
         use x,
         simp,
         exact h9,
       }
    }
  end

lemma leastelement: ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n → 
∀ (X:M), X ∈ FINITE M → X ⊆ ℕℕ → ¬ (X = Λ) → ∃ (p:M), p ∈ X ∧ ∀ (q:M),q ∈ X → p ≼ q:=
  assume hfinite k n hk hn  hkn hskn,
  begin
    have base: Λ ∈ W_leastelement M n:=
      begin
        rw W_leastelement_members,
        split,
        {
          exact lambda_finite M,
        },
        {
          intros h2 h3,
          contradiction,
        }
      end,
    have step: adjoin_closed M (W_leastelement M n):=
      begin
        unfold adjoin_closed,
        intros Y b h,
        cases h with h3 h4,
        rw W_leastelement_members at h3,
        cases h3 with h5 h6,
        rw W_leastelement_members,
        split,
        {
          exact finite_adjoin M Y b ⟨h5,h4⟩,
        },
        {
          intros h7 h8,
          have h9: Y ⊆ ℕℕ:=
            begin
              rw subset_definition,
              intros t h,
              rw subset_definition at h7,
              specialize h7 t,
              rw binary_union_axiom at h7,
              exact h7 (or.inl h),
            end,
          have h10:= empty_or_inhabited M Y h5,
          cases h10 with h11 h12,
          {
            use b,
            split,
            {
              rw binary_union_axiom,
              right,
              rw singleton1,
            },
            {
              intros q h,
              rw binary_union_axiom at h,
              rw singleton1 at h,
              cases h with h13 h14,
              {
                rw h11 at h13,
                have h15:=emptyset_axiom q,
                contradiction,
              },
              {
                rw h14,
                have hb: b ∈ ℕℕ:=
                  begin
                    rw subset_definition at h7,
                    specialize h7 b,
                    rw binary_union_axiom at h7,
                    rw singleton1 at h7,
                    simp at h7,
                    exact h7,
                  end,
                exact preceqreflexive M hfinite k n hk hn hkn hskn b hb,
              }
            }
          },
          {
            have h14: ¬ (Y = Λ ):=
              begin
                cases h12 with u h15,
                intro h,
                rw h at h15,
                have h16:= emptyset_axiom u,
                contradiction,
              end,
            have h15:= h6 h9 h14,
            cases h15 with r h16,
            cases h16 with h17 h18,
            have hr:= member_subset M Y ℕℕ r h9 h17,
            have hb: b ∈ ℕℕ:=
              begin
                rw subset_definition at h7,
                specialize h7 b,
                rw binary_union_axiom at h7,
                rw singleton1 at h7,
                apply h7,
                simp,
              end,
            have h19:= prectrichotomy1 M hfinite k n hk hn hkn hskn r b hr hb, 
            cases h19 with h20 h21,
            {
              use r,
              split,
              {
                rw binary_union_axiom,
                left,
                exact h17,
              },
              {
                intros q h,
                rw binary_union_axiom at h,
                cases h with h22 h23,
                {
                  exact h18 q h22,
                },
                {
                  rw singleton1 at h23,
                  rw h23,
                  exact h20,
                }
              }
            },
            {
              use b,
              split,
              {
                rw binary_union_axiom,
                right,
                rw singleton1, 
              },
              {
                intros q h,
                rw binary_union_axiom at h,
                cases h with h24 h25,
                {
                  have h26:= h18 q h24,
                  have h27:= preceqtrans M hfinite k n hk hn hkn hskn b r q h21 h26,
                  exact h27,
                },
                {
                  rw singleton1 at h25,
                  rw h25,
                  exact preceqreflexive M hfinite k n hk hn hkn hskn b hb,
                }
              }
            }
          }
        }
      end,
    intros X h,
    rw finite_members at h,
    specialize h (W_leastelement M n),
    unfold adjoin_closed at step,
    simp_rw and_comm at step,
    have h3:= h ⟨ base, step⟩,
    rw W_leastelement_members at h3,
    exact h3.right,
  end

lemma rho2: ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n → 
∀ (j l:M), j ∈ ℕℕ → l ∈ ℕℕ → ¬ (j = l)→ S j = S l →
((j = n ∧ l = k) ∨ (j = k ∧ l = n)):= 
  assume hfinite k n hk hn hkn hskn j l hj hl hjl hsjl,
  begin
    have h3:= trichotomy1 M j hj l hl, 
    have h10:= rho  M hfinite k n j l hk hn hkn hskn hj hl hjl hsjl,
    rw sym at hjl hsjl,
    have h20:= rho  M hfinite k n l j hk hn hkn hskn hl hj hjl hsjl,
    cases h3 with h4 h5,
    {
      have h11:= h10 h4,
      cases h11 with h12 h13,
      rw h12 at *,
      rw h13 at *,
      right,
      simp,
    },
    {
      cases h5 with h11 h12,
      { 
        rw h11 at *,
        contradiction,
      },
      {
        have h21:= h20 h12,
        cases h21 with h22 h23,
        rw h22 at *,
        rw h23 at *,
        left,
        simp,
      }
    }
  end


lemma divtransitive: 
 ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n → 
∀ (x y z:M), x ∈ ℕℕ → y ∈ ℕℕ → z ∈ ℕℕ → divides x y → divides y z → divides x z:=
  assume hfinite k n hk hn hkn hskn x y z hx hy hz hxy hyz,
  begin
    rw divides_definition at hxy hyz,
    rw divides_definition,
    rcases hyz with ⟨ h10, h11, h12, h13⟩,
    rcases hxy with ⟨ h20, h21, h22, h23⟩,
    have h24:= preceqtrans M hfinite k n hk hn hkn hskn x y z h22 h12,
    cases h23 with u h25,
    cases h25 with h26 h27,
    cases h13 with v h14,
    cases h14 with h15 h16,
    split,
    {
      exact hx,
    },
    { 
      split,
      { 
        exact hz,
      },
      {
        split,
        {
          exact h24,
        },
        {
          rw← h27 at h16,
          use u ⊗ v,
          split,
          { 
            exact ChurchMultiplicationMaps M v h15 u h26,
          },
          {
            rw ChurchMultiplicationAssociative,
            exact h16,
            exact hx,
            exact h26,
            exact h15,
          }
        }
      }
    },
  end



lemma divreflexive:  ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n →   
∀ (x:M), x∈ ℕℕ → divides x x:=
  begin
    intros hfinite k n hk hn hkn hskn x hx,
    rw divides_definition,
    split,
    {
      exact hx,
    },
    {
      split,
      {
        exact hx,
      },
      {
        split,
        {
          exact preceqreflexive M hfinite k n hk hn hkn hskn x hx,
        },
        {
          use S ChurchZero,
          split,
          {
            exact successorN M ChurchZero (zeroN M),
          },
          {
            rw ChurchMultiplicationEquation,
            rw ChurchMultiplicationBase,
            rw zeroplusx,
            exact hx,
            exact hx,
            exact hx,
            exact zeroN M,
          }
        }
      }
    }
  end


lemma precsum:  ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n → 
∀ (b:M), b ∈ ℕℕ → ∀ (a:M), a ∈ ℕℕ → a ≼ b → ∃ (x:M), x ∈ ℕℕ ∧ a ⊕ x = b:=
  assume hfinite k n hk hn hkn hskn,
  begin
    have base: ChurchZero ∈ Z_precsum M:=
      begin
        rw Z_precsum_members,
        split,
        {
          exact zeroN M,
        },
        {
          intros a ha h3,
          have h4:= preceqzero M hfinite k n hk hn hkn hskn a ha h3,
          rw h4 at *,
          use ChurchZero,
          rw ChurchZero_equation ChurchZero (zeroN M),
          simp,
          exact zeroN M,
        }
      end,
    have step: ∀ (b:M), b ∈ Z_precsum M → ¬(b = n) → S b ∈ Z_precsum M:=
      begin
        intros b h hbn,
        rw Z_precsum_members at h,
        cases h with hb h4,
        rw Z_precsum_members,
        split,
        {
          exact successorN M b hb,
        },
        {
          intros a ha h5,
          have h6:= preceqsuccessor M hfinite k n hk hn hkn hskn a b ha hb hbn,
          rw h6 at h5,
          rw or_comm at h5,
          cases h5 with h7 h8,
          {
            use ChurchZero,
            split,
            {
              exact zeroN M,
            },
            {
              rw ChurchZero_equation a ha,
              exact h7,
            }
          },
          {
            have h9:= h4 a ha h8,
            cases h9 with y h10,
            cases h10 with h11 h12,
            use S y,
            split,
            {
              exact successorN M y h11,
            },
            {
              rw ChurchAddition_equation,
              rw h12,
              exact ha,
              exact h11,
            }
          }
        }
      end,
    intros b hb,
    have h100:= finiteinduction M hfinite k n hk hn hkn hskn (Z_precsum M) ⟨ base, step⟩,
    intros a ha,
    rw subset_definition at h100,
    have h101:= h100 b hb,
    rw Z_precsum_members at h101,
    cases h101 with h102 h103,
    have h104:= h103 a ha,
    exact h104,
  end 

#axioms_all 




