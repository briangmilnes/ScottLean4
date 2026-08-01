import ChurchNumbers7

variables (M:Type) [Model M] (a b x y z u v w X R W κ μ ℓ : M)
-- using ℓ where the source text has λ because you can't use λ for a variable.

open Model 

 

lemma JRel: Rel (JLift M):=
  begin
    rw Rel_definition,
    intros z h,
    rw JLift_members at h,
    cases h with p h2,
    cases h2 with q h3,
    use single p, use q,
    exact h3.left,
  end

lemma JLift0: ‹ single ChurchZero, single ChurchZero› ∈ JLift M:=
  begin
    rw JLift_members,
    use ChurchZero, use (single ChurchZero),
    simp,
    intros w h h2,
    exact h,
  end 

lemma JLiftRec: ∀ (x y:M), ‹ single x, y› ∈ JLift M → ¬ S x ∈ y → ‹ single (S x), y ∪ single (S x)› ∈ JLift M:=
  begin
    intros x y h h30,
    rw JLift_members at h,
    rw JLift_members,
    use S x, use y ∪ (single (S x)),
    simp,
    intros W h3 h4,
    apply h4,
    { 
      cases h with p h5,
      cases h5 with q h6,
      rcases h6 with ⟨h7, h8⟩,
      rw ordered_pair_equality at h7,
      cases h7 with h10 h11,
      have h12:= single_oneone M x p h10,
      rw← h10 at *,
      rw← h11 at *,
      specialize h8 W,
      apply h8,
      split,
      {
        exact h3,
      },
      {
        exact h4,
      }
    },
    {
      exact h30,
    }
  end

lemma JLiftfinite: ∀ (x y:M), ‹ single x, y › ∈ JLift M → y ∈ FINITE M ∧ y ⊆ ℕℕ ∧ x ∈ ℕℕ :=
  begin
    intros x y h,
    rw JLift_members at h,
    cases h with p h1,
    cases h1 with q h2,
    cases h2 with h3 h4,
    rw ordered_pair_equality at h3,
    cases h3 with h5 h6,
    have h7:= single_oneone M x p h5,
    rw← h6 at *,
    rw← h7 at *,
    set W:= Z_JLiftfinite M with h50,
    have h8:= h4 W,
    rw h50 at h8,
    repeat{rw Z_JLiftfinite_members at h8},
    have h9:  ∃ (p q : M),  ‹ single x,y ›  =  ‹ single p,q ›  ∧  ‹ single x,y ›  ∈ JLift M ∧ q ∈ FINITE M ∧ q ⊆ ℕℕ ∧ p ∈ ℕℕ:=
      begin
        apply h8,
        split,
        {
          use ChurchZero, use (single ChurchZero),
          simp,
          split,
          {
            exact JLift0 M,
          },
          {
            repeat{split},
            {
              exact singletons_finite M ChurchZero, 
            },
            {
              rw subset_definition,
              intros t h,
              rw singleton1 at h,
              rw h,
              exact zeroN M,
            },
            {
              exact zeroN M,
            }
          }
        },
        {
          intros u v h h30,
          have h31:= JLiftRec M u v,
          rw Z_JLiftfinite_members,
          rw Z_JLiftfinite_members at h,
          cases h with p h40,
          cases h40 with q h41,
          cases h41 with h42 h43,
          rw ordered_pair_equality at h42,
          cases h42 with h44 h45,
          rw← h44 at *,
          rw← h45 at *,
          rcases h43 with ⟨ h46, h47, h48, h49⟩, 
          use S u, 
          use v ∪ (single (S u)),
          simp,
          repeat{split},
          {
            apply h31,
            exact h46,
            exact h30,
          },
          {
            have h49:= finite_adjoin M v (S u) ⟨ h47, h30⟩, 
            exact h49,
          },
          {
            have h50:= single_oneone M u p h44,
            rw h50 at *,
            rw subset_definition,
            intros t h,
            rw binary_union_axiom at h,
            rw singleton1 at h,
            cases h with h51 h52,
            {
              exact member_subset M v ℕℕ t h48 h51,
            },
            {
              rw h52,
              exact successorN M p h49,
            }
          },
          {
            have h50:= single_oneone M u p h44,
            rw h50 at *,
            exact successorN M p h49,
          }
        }
      end,
    cases h9 with p h10,
    cases h10 with q h11,
    rcases h11 with ⟨ h12, h13, h14, h15, h16⟩,
    rw ordered_pair_equality at h12,
    cases h12 with h17 h18,
    rw← h17 at *,
    rw← h18 at *,
    have h19:= single_oneone M x p h17,
    rw← h19 at *,
    exact ⟨ h14, h15, h16⟩, 
  end

lemma JLiftMaps_helper: ∀ (p:M), p ∈ JLift M → ∃(x y:M), p = ‹ single x, y › ∧ ChurchZero ∈ y ∧ x ∈ y ∧ ∀(u:M), u ∈ y → ¬ u = x → S u ∈ y:=
  begin
    set W:= Z_JLiftMaps_helper M with h50,
    have h200: JLift M ⊆ W:=
      begin
        rw subset_definition,
        intros p h,
        rw JLift_members at h,
        cases h with x1 h2,
        cases h2 with y1 h3,
        cases h3 with h4 h5,
        specialize h5 W,
        apply h5,
        split,
        {
          rw h50,
          rw Z_JLiftMaps_helper_members,
          split,
          {
            exact  JLift0 M,
          },
          {
            use ChurchZero, use (single ChurchZero),
            rw singleton1, 
            simp,
            intros u h6 h7,
            rw singleton1 at h6,
            contradiction,
          }
        },
        { 
          intros x y h6 h7,
          rw h50 at h6,
          rw Z_JLiftMaps_helper_members at h6,
          cases h6 with h8 h9,
          cases h9 with a h10,
          cases h10 with b h11,
          rcases h11 with ⟨ h12, h13, h14, h15⟩,
          rw ordered_pair_equality at h12,
          cases h12 with h16 h17,
          have h18:= single_oneone M x a h16,
          rw← h17 at *,
          rw← h18 at *,
          rw h50,
          rw Z_JLiftMaps_helper_members,
          repeat{split},
          {
            rw JLift_members,
            use  S x,
            use (y ∪ (single (S x))),
            simp,
            intros w h20 h21,
            rw JLift_members at h8,
            cases h8 with p h22,
            cases h22 with q h23,
            cases h23 with h24 h25,
            rw ordered_pair_equality at h24,
            cases h24 with h26 h27,
            have h28:= single_oneone M x p h26,
            rw← h28 at *,
            rw← h27 at *,
            specialize h25 w,
            have h30:= h25 ⟨ h20, h21⟩,
            exact h21 x y h30 h7,
          },
          {
            rw binary_union_axiom,
            left,
            exact h13,
          },
          {
            rw binary_union_axiom,
            right,
            rw singleton1, 
          },
          {
            intros u h20 h21,
            rw binary_union_axiom at h20,
            rw singleton1 at h20,
            rw binary_union_axiom,
            rw singleton1,
            have h30:= JLiftfinite M x y h8,
            rcases h30 with ⟨ h31, h32, h33⟩,
            have h34:= finitedecidable M y h31,
            rw decidable_members at h34,
            rw or_comm at h20,
            cases h20 with h23 h22,
            {
              contradiction,
            },
            {
              have h35:= h34 u x ⟨ h22, h14⟩,
              cases h35 with h36 h37,
              {
                rw h36 at *,
                simp, 
              },
              {
                left,
                exact h15 u h22 h37,
              }
            }
          }
        }
      end,
    rw subset_definition at h200,
    simp_rw h50 at h200,
    simp_rw Z_JLiftMaps_helper_members at h200,
    intros p h201,
    have h202:= h200 p h201,
    cases h202 with h203 h204, 
    exact h204,
  end

lemma noloops: ¬ ℕℕ ∈ FINITE M → ∀ (x y:M), ‹ single x, y › ∈ JLift M → ¬ S x ∈ y:=
  assume hnotfinite x y h hsx,
  begin
    have h3:= JLiftMaps_helper M ‹ single x, y› h,
    cases h3 with p h4,
    cases h4 with q h5,
    cases h5 with h6 h7,
    rw ordered_pair_equality at h6,
    cases h6 with h17 h8,
    have h9:= single_oneone M x p h17,
    rw← h8 at *,
    rw← h9 at *,
    rcases h7 with ⟨ h10, h11, h12⟩,
    have h20:= JLiftfinite M x y h,
    rcases h20 with ⟨ h21, h22, h23⟩,
    have h80:= finitedecidable M y h21,
    rw decidable_members at h80,
    have h100: ℕℕ ⊆  y:=
      begin
        rw subset_definition,
        intros t ht,
        rw N_members at ht,
        specialize ht y,
        apply ht,
        split,
        {
          exact h10,
        },
        {
          intros u hu,
          have h81:= h80 u x ⟨ hu, h11⟩,
          cases h81 with h82 h83,
          {
            rw h82 at *,
            exact hsx,
          },
          {
            exact h12 u hu h83,
          }
        }
      end,
    have h101: ℕℕ = y:=
      begin
        rw full_extensionality,
        intro t,
        split,
        { 
          intro ht,
          exact member_subset M ℕℕ y t h100 ht,
        },
        {
          intro hy,
          exact member_subset M y ℕℕ t h22 hy,
        }
      end,
    rw h101 at *,
    contradiction,
  end

lemma JLiftMaps: ¬ ℕℕ ∈ FINITE M → ∀ (x:M), x ∈ ℕℕ → ∃(y:M), ‹ single x, y › ∈ JLift M:=
  assume hnotfinite, 
  begin
    have base: ChurchZero ∈ Z_JLiftMaps M:=
      begin
        rw Z_JLiftMaps_members,
        split,
        {
          exact zeroN M,
        },
        {
          use single ChurchZero,
          exact JLift0 M,
        }
      end,
    have step: ∀ (x:M), x ∈ Z_JLiftMaps M → S x ∈ Z_JLiftMaps M:=
      begin
        intros x h,
        rw Z_JLiftMaps_members,
        rw Z_JLiftMaps_members at h,
        cases h with hx h2,
        cases h2 with y h3,
        split,
        {
          exact successorN M x hx,
        },
        {
          have h20:= JLiftMaps_helper M ‹ single x, y› h3,
          cases h20 with p h21,
          cases h21 with q h22,
          cases h22 with h23 h24,
          rw ordered_pair_equality at h23,
          cases h23 with h25 h26,
          have h27:= single_oneone M x p h25,
          rw← h27 at *,
          rw← h26 at *,
          rcases h24 with ⟨ h28, h29, h30⟩,
          use y ∪ single (S x),
          have h31:= JLiftRec M x y h3,
          apply h31,
          have h32:= noloops M hnotfinite x y h3,
          exact h32,
        }
      end,
    intros t ht,
    rw N_members at ht,
    have h5:= ht (Z_JLiftMaps M) ⟨ base, step⟩,
    rw Z_JLiftMaps_members at h5,
    exact h5.right,
  end

lemma JLiftdom:   ∀ (x p:M), ‹ single x, p › ∈ JLift M → 
x = ChurchZero ∨ (x ∈ ℕℕ ∧ ∃ (u:M), S u = x  ∧ u ∈ ℕℕ) :=
  begin
    have base: ‹ single ChurchZero, single ChurchZero › ∈ W_JLiftdom M:=
      begin
        rw W_JLiftdom_members,
        split,
        {
          exact JLift0 M,
        },
        {
          simp,
        }
      end,
    have step: ∀ (x y:M), ‹ single x, y › ∈ W_JLiftdom M → ¬ S x ∈ y → ‹ single (S x), (y ∪ single (S x)) › ∈ W_JLiftdom M:=
      begin
        intros x y h,
        rw W_JLiftdom_members at h,
        cases h with h3 h4,
        cases h4 with h5 h6,
        rw ordered_pair_equality at h5,
        cases h5 with h6 h7,
        have h8:= single_oneone M x ChurchZero h6,
        rw h7 at *,
        rw h8 at *,
        intro h9,
        rw singleton1 at h9,
        rw W_JLiftdom_members,
        split,
        {
          have h10:= JLiftRec M,
          specialize h10 ChurchZero (single ChurchZero),
          rw singleton1 at h10,
          have h11:= h10 h3 h9,
          exact h11,
        },
        {
          right,
          use ChurchZero,
          use single ChurchZero ∪ single (S ChurchZero),
          simp,
          exact zeroN M,
        },
        {
          intro h40,
          have h7:= JLiftMaps_helper M ‹ single x, y› h3,
          cases h7 with p h8,
          cases h8 with q h9,
          cases h9 with h10 h11,
          rcases h11 with ⟨ h12, h13, h14⟩, 
          rw ordered_pair_equality at h10,
          cases h10 with h15 h16,
          have h17:= single_oneone M x p h15,
          rw← h17 at *,
          rw← h16 at *,
          rw W_JLiftdom_members,
          split,
          {
            have h18:= JLiftRec M x y h3 h40,
            exact h18,
          },
          {
            right,
            use x, use (y ∪ single (S x)),
            simp,
            cases h6 with a h30,
            cases h30 with b h31,
            cases h31 with h32 h33,
            rw ordered_pair_equality at h32,
            cases h32 with h34 h35,
            have h36:= single_oneone M x (S a) h34,
            rw h36 at *,
            exact successorN M a h33,
          }
        }
      end,
    have h100: JLift M ⊆ W_JLiftdom M:=
      begin
        rw subset_definition,
        intros z h101,
        rw JLift_members at h101,
        cases h101 with p h102,
        cases h102 with q h103,
        cases h103 with h104 h105,
        have h106:= h105 (W_JLiftdom M) ⟨ base, step⟩, 
        exact h106,
      end,
    intros x p h,
    have h101:= member_subset M (JLift M) (W_JLiftdom M) ‹ single x,p › h100 h,
    rw W_JLiftdom_members at h101,
    cases h101 with h102 h103,
    cases h103 with h104 h105,
    {
      rw ordered_pair_equality at h104,
      cases h104 with h105 h106,
      have h107:= single_oneone M x ChurchZero h105,
      left,
      exact h107,
    },
    {
      cases h105 with u h106,
      cases h106 with y h107,
      rw ordered_pair_equality at h107,
      cases h107 with h108 h109,
      cases h108 with h110 h111,
      have h112:= single_oneone M x (S u) h110,
      right,
      split,
      {
        rw h112,
        exact successorN M u h109,
      },
      {
        use u,
        rw sym at h112,
        exact ⟨ h112, h109⟩,
      }
    }
  end 
 


lemma JLift1: ∀ (p:M), ‹ single ChurchZero, p › ∈ JLift M → p = single ChurchZero:=
  assume p h,
  begin
    have h2:= JLiftfinite M ChurchZero p h,
    rcases h2 with ⟨ h3, h4, h5⟩,
    have h80:= finitedecidable M p h3,
    have h6:= JLiftMaps_helper M ‹ single ChurchZero, p› h,
    cases h6 with x5 h7,
    cases h7 with y5 h8,
    cases h8 with h9 h10,
    rw ordered_pair_equality at h9,
    cases h9 with h11 h12,
    rw← h11 at *,
    rw← h12 at *,
    rcases h10 with ⟨ h13, h14, h15⟩,
    set Z:= JLift M - single ‹ single ChurchZero, p › with h50,
    have h30: ¬¬ single ChurchZero = p:=
      begin
      intro h31,
        have base: ‹ single ChurchZero, single ChurchZero› ∈  Z:=
          begin
            rw h50,
            rw minus_members,
            split,
            {
              exact JLift0 M,
            },
            {
              rw singleton1,
              intro h20,
              rw ordered_pair_equality at h20,
              simp at h20,
              contradiction,
            }
          end,
        have step: ∀ (x p:M), ‹ single x, p› ∈ Z → ¬ S x ∈ p → ‹ single (S x), p ∪ single (S x) › ∈  Z:=
          begin
            intros x q h34 hxq,
            rw h50 at h34,
            rw minus_members at h34,
            rw singleton1 at h34,
            cases h34 with h35 h36,
            have h37:=JLiftRec M x q h35 hxq,
            rw h50,
            rw minus_members,
            split,
            {
              exact h37,
            },
            {
              rw singleton1,
              intro h38,
              rw ordered_pair_equality at h38,
              cases h38 with h39 h40,
              have h41:= single_oneone M (S x) ChurchZero h39,
              have h42:= JLiftdom M x q h35,
              cases h42 with h20 h21,
              {
                rw h20 at h41,
                have h42:= snneqn M ChurchZero (zeroN M),
                contradiction,
              },
              { 
                cases h21 with hx h22,
                cases h22 with v h23,
                have h42:= successoromitszero M x hx,
                contradiction,
              }
            }
          end,
        have h60: JLift M ⊆ Z:=
          begin
            rw subset_definition,
            intros t h61,
            rw JLift_members at h61,
            cases h61 with p h62,
            cases h62 with q h63,
            cases h63 with h64 h65,
            rw h64 at *,
            have h66:= h65 Z,
            apply h66,
            split,
            {
              exact base,
            },
            {
              exact step,
            }
          end,
        have h61:= member_subset M (JLift M) Z ‹ single ChurchZero,p › h60 h,
        rw h50 at h61,
        rw minus_members at h61,
        cases h61 with h62 h63,
        rw singleton1 at h63,
        contradiction,
      end,
    rw full_extensionality at h30,
    have h65:= notnot_forall (λ (x:M),x ∈ single ChurchZero ↔ x ∈ p ) h30,
    dsimp at h65,
    rw full_extensionality,
    intro t,
    rw singleton1,
    specialize h65 t,
    rw singleton1 at h65,
    have h67:= notnot_iff ( t= ChurchZero)(t∈ p) h65,
    cases h67 with h68 h69,
    rw decidable_members at h80,
    have h81:= h80 t ChurchZero,
    split,
    {
      intro h66,
      have h82:= h81 ⟨ h66, h13⟩,
      cases h82 with h83 h84,
      {
        exact h83,
      },
      {
        have h70:= double_negate (t ∈ p) h66,
        have h71:= h69 h70,
        contradiction,
      }
    },
    {
      intros h70,
      rw h70 at *,
      exact h13,
    }  
  end

lemma JLift2: ∀ (x y:M), x ∈ ℕℕ → ‹ single (S x), y › ∈ JLift M → ∃ (u p:M), S u = S x ∧  ‹ single u, p › ∈ JLift M ∧  ¬ S u ∈ p ∧ y = (p ∪ single (S u)):=
  begin
    set W:= W_JLift2 M with h50,
    have h51: JLift M ⊆ W:=
      begin
        rw subset_definition,
        intros t ht,
        rw JLift_members at ht,
        cases ht with x h2,
        cases h2 with y h3,
        cases h3 with h4 h5,
        rw h4 at *,
        specialize h5 W,
        apply h5,
        rw h50,
        rw W_JLift2_members,
 
        repeat{ split},
        {
          exact JLift0 M,
        },
        {   -- first condition in definition of JLift
          left,
          simp,
        },
        { -- second condition in definition of JLift
          intros u p h21 h22,
          rw W_JLift2_members,
          rw W_JLift2_members at h21,
          cases h21 with h23 h124,
          cases h124 with h24 h25,
          {     
            rw ordered_pair_equality at h24,
            cases h24 with h26 h27,
            rw h27 at *,
            have h28:= single_oneone M u ChurchZero h26,
            rw h28 at *,
            split,
            {
              have h30:= JLiftRec M ChurchZero (single ChurchZero) h23 h22,
              exact h30,
            },
            { 
              right, 
              split,
              {
                use ChurchZero,
                use single ChurchZero ∪ single (S ChurchZero),
                simp,
                exact zeroN M,
              },
              {
                intros x2 y2 h hx2,
                rw ordered_pair_equality at h,
                cases h with h30 h31,
                have h32:= single_oneone M (S ChurchZero) (S x2) h30,
                rw← h32 at *,
                rw← h31 at *,
                use ChurchZero,
                use (single ChurchZero),
                split,
                {
                  exact JLift0 M,
                },
                {
                  simp,
                  exact⟨ hx2, zeroN M, h22⟩,
                } 
              }
            } 
          },
          { 
            split,
            {
              have h30:= JLiftRec M u p h23 h22,
              exact h30,
            },
            { 
              right,
              cases h25 with h26 h27,
              cases h26 with x4 h28,
              cases h28 with y4 h29,
              cases h29 with h30 hx4,
              rw ordered_pair_equality at h30,
              cases h30 with h31 h32,
              have h33:= single_oneone M u (S x4) h31,
              have hu:= successorN M x4 hx4,
              split,
              {
                use u,
                use p ∪ (single (S u)),
                simp,
                rw h33,
                exact hu,  
              },
              { 
                intros x3 y3 h hx3, 
                use u, use p,
                rw ordered_pair_equality at h,
                cases h with h90 h91,
                rw h91,
                have h92:= single_oneone M (S u) (S x3) h90,
                rw h92,
                simp,
                rw← h92,
                rw h33 at *,
                exact ⟨ h23, hx3, hu, h22⟩,
              }
            }
          }, 
        }
      end,
    intros x y hx h,
    have h120:= member_subset M (JLift M) W ‹ single (S x), y › h51 h,
    rw h50 at h120,
    rw W_JLift2_members at h120,
    cases h120 with h121 h122,
    cases h122 with h40 h41,
    {
      rw ordered_pair_equality at h40,
      cases h40 with h41 h42,
      have h43:= single_oneone M (S x) ChurchZero h41,
      have h44:= successoromitszero M x hx,
      contradiction,
    },
    { 
      cases h41 with h42 h43,
      have h44:= h43 x y,
      simp at h44,
      have h45:= h44 hx,
      cases h45 with u h46,
      cases h46 with p h47,
      use u, use p,
      rcases h47 with ⟨ h61, hx, hu, h64, h65, h66⟩,
      exact ⟨ h64, h61, h65, h66⟩, 
    }
  end 



lemma JFUNC_helper2: ∀ (x y:M), ‹ single x, y› ∈  JLift M → 
(∀ (u p:M), ‹ single u, p› ∈ JLift M → comparable M y p) →
(∀ (z:M), ‹ single x, z› ∈ JLift M → y = z) → 
(∀ (u p:M), ‹ single u, p› ∈ JLift M → comparable M (y ∪ single (S x)) p):=
  assume x y hy hcomp hfunc u p hp,
  begin
    have h3:= hcomp u p hp,
    unfold comparable at h3,
    have h4: (x = u ∨ ¬ x = u) → (y ⊆ p ∨ p ⊆ y) → y ∪ single (S x) ⊆ p ∨ p ⊆ y ∪ single (S x):=
      begin
        intros hxu h4,
        rw or_comm at h4,
        cases h4 with h5 h6,
        {
          rw subset_definition at h5,
          right,
          rw subset_definition,
          intro t,
          rw binary_union_axiom,
          intro ht,
          left,
          exact h5 t ht,
        },
        {
          have h7:= JLiftMaps_helper M ‹ single x,y› hy,
          cases h7 with a h8,
          cases h8 with b h9,
          cases h9 with h10 h11,
          rw ordered_pair_equality at h10,
          cases h10 with h12 h13,
          have h14:= single_oneone M x a h12,
          rw← h13 at *,
          rw← h14 at *,
          rcases h11 with ⟨ h15, h16, h17⟩, 
          have h18:= member_subset M y p x h6 h16,
          have h19:= JLiftMaps_helper M ‹ single u, p › hp,
          cases h19 with c h20,
          cases h20 with d h21,
          cases h21 with h22 h23,
          rw ordered_pair_equality at h22,
          cases h22 with h24 h25,
          have h26:= single_oneone M u c h24, 
          rw← h25 at *,
          rw← h26 at *,
          rcases h23 with ⟨ h27, h28, h29⟩,
          have h30:= h29 x h18,
          cases hxu with h31 h32,
          {
            right,
            rw← h31 at *,
            have h33:= hfunc p hp,
            rw← h33 at *,
            have h34:= subset_union M y y (single (S x)) (subset_reflexive M y),
            exact h34,
          },
          {
            have h35:= h30 h32,
            have h36: y ∪ single (S x) ⊆ p:=
              begin
                rw subset_definition,
                intros t h,
                rw binary_union_axiom at h,
                rw singleton1 at h,
                cases h with h33 h34,
                {
                  exact member_subset M y p t h6 h33, 
                },
                {
                  rw h34 at *,
                  exact h35,
                }
              end, 
            left,
            exact h36,
          }
        }
      end,
    unfold comparable,
    have h40:= notnotLEM (x = u),
    have h41:= double_negate (x = u ∨ ¬x = u → y ⊆ p ∨ p ⊆ y → y ∪ single (S x) ⊆ p ∨ p ⊆ y ∪ single (S x)) h4,
    have h42:= notnot_imp2way (x = u ∨ ¬x = u )(y ⊆ p ∨ p ⊆ y → y ∪ single (S x) ⊆ p ∨ p ⊆ y ∪ single (S x)),
    rw h42 at h41,
    have h43:= h41 h40,
    have h44:= notnot_imp2way (y ⊆ p ∨ p ⊆ y )(y ∪ single (S x) ⊆ p ∨ p ⊆ y ∪ single (S x)),
    rw h44 at h43,
    have h45:= h43 h3,
    exact h45,
  end

lemma JFUNC_helper3: ¬ ℕℕ ∈ FINITE M →  ∀ (x y:M), x ∈ ℕℕ → ‹ single x, y› ∈  JLift M → 
(∀ (u p:M), ‹ single u, p› ∈ JLift M → comparable M y p) →
(∀ (z:M), ‹ single x, z› ∈ JLift M → y = z) → 
(∀ (t u:M), ‹ single t, u › ∈ JLift M → t = x ∨ ¬ t = x) →
∀ (u v:M), ‹ single (S x),u › ∈ JLift M → ‹ single (S x), v › ∈ JLift M → u = v:=
  assume hnotfinite x y hx hy hcomp hfunc hdom u v hsu hsv,
  begin
    have h3:= JLift2 M x u hx hsu,
    cases h3 with t h4, 
    cases h4 with p h5,
    rcases h5 with ⟨ h6, h7, h8, h9⟩,
    have h13:= JLift2 M x v hx hsv,
    cases h13 with r h14,
    cases h14 with q h15,
    rcases h15 with ⟨ h16, h17, h18, h19⟩,
    have h30:= noloops M hnotfinite x y hy,
    have h20:= JLiftRec M x y hy h30,
    have h21:= hcomp t p h7,
    have h121:= hcomp r q h17,
    have h22:= JLiftMaps_helper M ‹ single x, y › hy,
    cases h22 with a h23,
    cases h23 with b h24,
    cases h24 with h25 h26,
    rw ordered_pair_equality at h25,
    cases h25 with h26 h27,
    have h28:= single_oneone M x a h26,
    rw← h28 at *,
    rw← h27 at *,
    rcases h26 with ⟨ h27, h28, E5339⟩,
    have h32:= JLiftMaps_helper M ‹ single t,p › h7,
    cases h32 with a1 h33,
    cases h33 with b1 h34,
    cases h34 with h35 h36,
    rw ordered_pair_equality at h35,
    cases h35 with h36 h37,
    have h38:= single_oneone M t a1 h36,
    rw← h38 at *,
    rw← h37 at *,
    rcases h36 with ⟨ h37, h38, E5340⟩,
    have h232:= JLiftMaps_helper M ‹ single r,q › h17,
    cases h232 with a11 h233,
    cases h233 with b11 h234,
    cases h234 with h235 h236,
    rw ordered_pair_equality at h235,
    cases h235 with h236 h237,
    have h238:= single_oneone M r a11 h236,
    rw← h238 at *,
    rw← h237 at *,
    rcases h236 with ⟨ h237, h238, E5341⟩,
    have h40:= hdom t p h7,
    have E5538: t = x:=
      begin
        cases h40 with h41 h42,
        {
          exact h41,
        },
        {
          have h45: ¬ t ∈ y:=
            begin
              intro h43,
              have h44:= E5339 t h43 h42,
              rw h6 at *,
              contradiction,
            end, 
          have h46: ¬ x ∈ p:=
            begin
              intro h43,
              rw sym at h42,
              have h44:= E5340 x h43 h42, 
              rw← h6 at *,
              contradiction, 
            end,
          have h47: ¬ (p ⊆ y):=
            begin
              intro h,
              have h48:= member_subset M p y t h h38,
              contradiction,
            end,
          have h49: ¬ (y ⊆ p):=
            begin
              intro h,
              have h50:= member_subset M y p x h h28,
              contradiction, 
            end,
          have h51: ¬ comparable M y p:=
            begin
              intro h,
              unfold comparable at h,
              apply h,
              intro h55,
              cases h55 with h56 h57,
              {
                contradiction,
              },
              {
                contradiction,
              } 
            end,
          contradiction,
        }
      end,
    have E5539: r = x:=
      begin
        have h140:= hdom r q h17,
        cases h140 with h141 h142,
        {
          exact h141,
        },
        {
          have h145: ¬ r ∈ y:=
            begin
              intro h143,
              have h144:= E5339 r h143 h142,
              rw h16 at *,
              contradiction,
            end, 
          have h146: ¬ x ∈ q:=
            begin
              intro h143,
              rw sym at h142,
              have h144:= E5341 x h143 h142, 
              rw← h16 at *,
              contradiction, 
            end,
          have h147: ¬ (q ⊆ y):=
            begin
              intro h,
              have h148:= member_subset M q y r h h238,
              contradiction,
            end,
          have h49: ¬ (y ⊆ q):=
            begin
              intro h,
              have h50:= member_subset M y q x h h28,
              contradiction, 
            end,
          have h151: ¬ comparable M y q:=
            begin
              intro h,
              unfold comparable at h,
              apply h,
              intro h155,
              cases h155 with h156 h157,
              {
                contradiction,
              },
              {
                contradiction,
              } 
            end,
          contradiction,
        }
      end,
    rw E5538 at *,
    rw E5539 at *,
    have h70:= hfunc p h7,
    have h71:= hfunc q h17,
    rw h9 at *,
    rw h19 at *,
    rw← h70,
    rw← h71,
  end

lemma JFUNC_helper4: ¬ ℕℕ ∈ FINITE M → 
∀ (x y:M), x ∈ ℕℕ →  ‹ single x, y › ∈  JLift M →
(∀ (t u:M), ‹ single t, u › ∈ JLift M → comparable M y u) →
(∀ (z:M), ‹ single x,z› ∈ JLift M → y = z) →
(∀ (t u:M), ‹ single t, u › ∈ JLift M → t = x ∨ ¬ t = x) →
‹ single (S x), u › ∈ JLift M →
∀ (t q:M), ‹ single t,q › ∈ JLift M → S x = t ∨ ¬ S x = t:=
  assume hnotfinite x y hx hxy hcomparability hfunctionality hdomaindecidability E5519,
  begin
    intros t q htq,
    have h2:= noloops M hnotfinite x y hxy,
    have h3:= JLiftRec M x y hxy h2,
    have h4:= JLiftMaps_helper M ‹ single x, y› hxy,
    cases h4 with a h5,
    cases h5 with b h6,
    cases h6 with h7 h8,
    rw ordered_pair_equality at h7,
    cases h7 with h9 h10,
    have h11:= single_oneone M x a h9,
    rw← h10 at *,
    rw← h11 at *,
    rcases h8 with ⟨ h12, h13, h14⟩,
    have h15:= JLiftfinite M x y hxy,
    rcases h15 with ⟨ hyfinite, hysubsetN, hx⟩, 
    have h16:= JLiftfinite M t q htq,
    rcases h16 with ⟨ hqfinite, hqsubsetN, ht⟩,
    have h80:= decidable0 M t ht,
    cases h80 with h81 h82,
    {
      have h17:= successoromitszero M x hx,
      right,
      rw h81,
      exact h17,
    },
    {
      have h18:= predecessor M t ht h82,
      cases h18 with m h19,
      cases h19 with hm hsmt,
      rw← hsmt at *,
      have h20:= JLiftMaps M hnotfinite m hm,
      cases h20 with u h21,
      have h22:= hdomaindecidability m u h21,
      cases h22 with h23 h24,
      {
        rw h23 at *,
        simp,
      },
      {  --case 2b in the paper
        right,
        intro hsxm,
        have h25: ‹ single (S x), q › ∈ JLift M:=
          begin
            rw hsxm,
            exact htq,
          end,
        have h26:= JFUNC_helper3 M hnotfinite x y hx hxy hcomparability
                   hfunctionality hdomaindecidability q (y ∪ (single (S x))) h25 h3,
        have h27:= JLiftMaps_helper M ‹ single m, u › h21,
        cases h27 with a1 h28,
        cases h28 with b1 h29,
        cases h29 with h30 h31,
        rw ordered_pair_equality at h30,
        cases h30 with h32 h33,
        have h34:= single_oneone M m a1 h32,
        rw← h34 at *,
        rw← h33 at *,
        rcases h31 with ⟨ h35,hmu, h37⟩,
        have h40:= noloops M hnotfinite m u h21,
        have h38:= JLiftRec M m u h21 h40,
        have h39:= h38,
        rw← hsxm at h39,
        have h41:= JFUNC_helper3 M hnotfinite x y hx hxy hcomparability
                   hfunctionality hdomaindecidability (u ∪ (single (S x))) (y ∪ (single (S x))) h39 h3,
        have h42:= noloops M hnotfinite m u h21,
        have h43:= h42,
        rw← hsxm at h43,
        have h44: u = y:=
          begin
            rw full_extensionality,
            intro t,
            rw full_extensionality at h41,
            have h45:= h41 t,
            rw binary_union_axiom at h45,
            rw binary_union_axiom at h45,
            rw singleton1 at h45,
            cases h45 with h46 h47,
            split,
            {
              intro h,
              have h48:= h46 (or.inl h),
              cases h48 with h49 h50,
              {
                exact h49,
              },
              {
                rw h50 at *,
                contradiction,
              }
            },
            {
              intro h,
              have h48:= h47 (or.inl h),
              cases h48 with h49 h50,
              {
                exact h49,
              },
              {
                rw h50 at *,
                contradiction,
              }
            }
          end,
        have h51:= hmu,
        rw h44 at h51,
        have h52:= h14 m h51 h24,
        rw← hsxm at h52,
        contradiction,
      }
    }
  end

lemma JLiftFUNC: ¬ ℕℕ ∈ FINITE M → ∀ (x : M), x ∈ ℕℕ →  
∀ (y z:M), ‹ single x,y› ∈ JLift M → ‹ single x, z› ∈ JLift M → y = z:=
  assume hnotfinite, 
  begin
    set Z:= Z_functionality M ∩ Z_domaindecidability M ∩ Z_comparability M with h50,
    have base: ChurchZero ∈ Z:=
      begin
        rw h50,
        rw intersection_axiom,
        rw intersection_axiom,
        repeat{split},
        {
          rw Z_functionality_members,
          split,
          {
            exact zeroN M,
          },
          {
            intros y z hy hz,
            rw JLift1 M y hy,
            rw JLift1 M z hz,
          }
        },
        {
          rw Z_domaindecidability_members,
          split,
          {
            exact zeroN M,
          },
          {
            intros y p t hy hz,
            have h3:= JLift1 M y hy,
            rw h3 at *,
            have h4:= JLiftfinite M t p hz,
            rcases h4 with ⟨ h5, h6, h7⟩, 
            have h5:= decidable0 M t h7,
            rw sym at h5,
            exact h5,
          }
        },
        {
          rw Z_comparability_members,
          split,
          {
            exact zeroN M,
          },
          {
            intros y p t hy hp,
            unfold comparable,
            have h3:= JLift1 M y hy,
            rw h3,
            have h4:= JLiftMaps_helper M ‹ single t, p› hp,
            cases h4 with a h5,
            cases h5 with b h6,
            cases h6 with h7 h8,
            rw ordered_pair_equality at h7,
            cases h7 with h9 h10,
            have h11:= single_oneone M t a h9,
            rw← h11 at *,
            rw← h10 at *,
            rcases h8 with ⟨ h12, h13, h14⟩,
            intro h15,
            have h16:single ChurchZero ⊆ p:=
              begin
                rw subset_definition,
                intros z h,
                rw singleton1 at h,
                rw h,
                exact h12,
              end,
            exact h15 (or.inl h16),
          }
        }
      end,
    have step: ∀ (x:M), x ∈ Z → S x ∈ Z:=
      begin
        intros x h,
        rw h50 at h,
        rw intersection_axiom at h,
        rw intersection_axiom at h,
        rw and_assoc at h,
        rcases h with ⟨ h2, h3, h4⟩,
        rw h50,
        rw intersection_axiom,
        rw intersection_axiom,
        rw and_assoc,
        rw Z_functionality_members at h2,
        cases h2 with hx h6,
        have hupFUNC:  S x ∈ Z_functionality M:=
          begin
            rw Z_functionality_members M,
            split,
            {
              exact successorN M x hx,
            },
            {
              have h6:= JLiftMaps M hnotfinite x hx,
              cases h6 with y h7,
              have h5:= JFUNC_helper3 M hnotfinite x y hx,
              apply h5,
              {
                exact h7,
              },
              {
                rw Z_comparability_members at h4,
                cases h4 with h10 h11,
                intros u p h,
                have h12:= h11 y p u h7 h,
                exact h12,
              },
              {
                intro z,
                exact h6 y z h7,
              },
              {
                rw Z_domaindecidability_members at h3,
                intros t u h,
                cases h3 with h10 h11,
                have h12:= h11 y u t h7 h,
                rw sym,
                exact h12,
              }
            }
          end, 
        repeat{split},
        { 
          exact hupFUNC,
        },
        {
          rw Z_domaindecidability_members M,
          split,
          {
            exact successorN M x hx,
          },
          {
            intros u p t,
            have h8:= JLiftMaps M hnotfinite x hx,
            cases h8 with y h9,
            have h7:= JFUNC_helper4 M u hnotfinite x y hx h9,
            rw Z_comparability_members at h4,
            cases h4 with h10 h11,
            have h12: ∀ (t u : M),  ‹ single t,u ›  ∈ JLift M → comparable M y u:=
              begin
                intros T U h,
                have h13:= h11 y U T h9 h,
                exact h13,
              end,
            have h14:∀ (z : M),  ‹ single x,z ›  ∈ JLift M → y = z:=
              begin
                intro z,
                exact h6 y z h9,
              end,
            have h15:∀ (t u : M),  ‹ single t,u ›  ∈ JLift M → t = x ∨ ¬t = x:=
              begin
                rw Z_domaindecidability_members at h3,
                cases h3 with h20 h21,
                intros t u h,
                have h22:= h21 y u t h9 h,
                rw sym,
                exact h22,
              end,
            intro h,
            have h13:= h7 h12 h14 h15 h,
            intro h30,
            exact h13 t p h30,
          }
        },
        {
          rw Z_comparability_members,
          split,
          {
            exact successorN M x hx,
          },
          { 
            rw Z_comparability_members at h4,
            cases h4 with h10 h11,
            intros y p t hxy h12,
            have h20:= JLiftMaps M hnotfinite x hx,
            cases h20 with u h21,
            have h23:= noloops M hnotfinite x u h21,
            have h22:= JLiftRec M x u h21 h23,
            have h24:= hupFUNC,
            rw Z_functionality_members at h24,
            cases h24 with h25 h26,
            have h27:= h26 y (u ∪ (single (S x))) hxy h22,
            rw h27,
            have h30: (∀ (u_1 p : M),  ‹ single u_1,p ›  ∈ JLift M → comparable M u p) :=
              begin
                intros u1 p1 h31,
                have h29:= h11 u p1 u1 h21 h31,
                exact h29,
              end, 
            have h31:  ∀ (z : M),  ‹ single x,z ›  ∈ JLift M → u = z:=
              begin
                intros z h, 
                have h32:= h6 u z h21 h,
                exact h32,
              end,
            have h28:= JFUNC_helper2 M x u h21 h30 h31 t p h12,
            exact h28,
          }
        }
      end,
    intros x hx,
    rw N_members at hx,
    specialize hx Z,
    have h5:= hx ⟨base,step⟩,
    rw h50 at h5,
    rw intersection_axiom at h5,
    rw intersection_axiom at h5,
    rw and_assoc at h5,
    rcases h5 with ⟨ h6, h7, h8⟩,
    rw Z_functionality_members at h6,
    cases h6 with h9 h10,
    exact h10,
  end

lemma JC0:  JC M ChurchZero = single ChurchZero:=
  begin
    rw full_extensionality,
    intro t,
    rw singleton1,
    rw JC_members,
    split,
    {
      intro h,
      specialize h (single ChurchZero),
      have h2:= JLift0 M,
      rw singleton1 at h,
      exact h h2,
    },
    { 
      intros h y h3,
      rw h at *,
      have h4:= JLiftMaps_helper M ‹ single ChurchZero,y › h3,
      cases h4 with p h5,
      cases h5 with q h6,
      cases h6 with h7 h8,
      rw ordered_pair_equality at h7,
      cases h7 with h9 h10,
      have h11:= single_oneone M ChurchZero p h9,
      rw← h11 at *,
      rw← h10 at *,
      exact h8.left,
    }
  end

theorem Churchsuccessorweaklyoneone: ¬ ℕℕ ∈ FINITE M → ∀(x t:M), x ∈ ℕℕ → t ∈ ℕℕ → ¬ x = t → ¬ S x = S t:= 
  assume hnotfinite x t hx ht hnxt hxst,
  begin
    have h3:= JLiftMaps M hnotfinite x hx,
    cases h3 with y h4,
    have h5:= noloops M hnotfinite x y h4,
    have h6:= JLiftRec M x y h4 h5,
    have h7:= JLiftMaps M hnotfinite t ht,
    cases h7 with p h8,
    have h9:= noloops M hnotfinite t p h8,
    have h10:= JLiftRec M t p h8 h9,
    rw← hxst at h10,
    have hsx:= successorN M x hx, 
    have h11:= JLiftFUNC M hnotfinite (S x) hsx (y ∪ (single (S x))) (p ∪ (single (S x))) h6 h10,
    rw← hxst at h9,
    have h12: p = y:=
      begin
        rw full_extensionality,
        intro t,
        rw full_extensionality at h11,
        specialize h11 t,
        rw binary_union_axiom at h11,
        rw binary_union_axiom at h11,
        rw singleton1 at h11,
        cases h11 with h12 h13,
        split,
        {
          intro h,
          have h14:= h13 (or.inl h),
          cases h14 with h15 h16,
          {
            exact h15,
          },
          {
            rw h16 at *,
            contradiction,
          }
        },
        {
          intro h,
          have h14:= h12 (or.inl h),
          cases h14 with h15 h16,
          {
            exact h15,
          },
          {
            rw h16 at *,
            contradiction,
          }
        }
      end,
    have h15:= JLiftMaps_helper M ‹ single x,y› h4,
    have h25:= JLiftMaps_helper M ‹ single t,p› h8,
    cases h15 with a h16,
    cases h16 with b h17,
    cases h17 with h18 h19,
    rw ordered_pair_equality at h18,
    cases h18 with h20 h21,
    have h22:= single_oneone M x a h20,
    rw← h22 at *,
    rw← h21 at *,
    cases h25 with a1 h26,
    cases h26 with b1 h27,
    cases h27 with h28 h29,
    rw ordered_pair_equality at h28,
    cases h28 with h30 h31,
    have h32:= single_oneone M t a1 h30,
    rw← h32 at *,
    rw← h31 at *,
    rcases h19 with ⟨ h32, h33, h34⟩,
    rcases h29 with ⟨ h35, h36, h37⟩,
    have h38:= JLiftfinite M x y h4,
    rcases h38 with ⟨ hyfinite, hynn, hx⟩,
    have h80:= finitedecidable M y hyfinite,
    rw decidable_members at h80,

    have h100: ∀ (u:M), u ∈ y → S u ∈ y:=
      begin
        intros u h,
        have h101:= h80 x u ⟨ h33, h⟩, 
        cases h101 with h102 h103,
        {
          rw h12 at *,
          have h104:= h37 u h,
          rw← h102 at *, 
          have h105:= h80 x t ⟨ h33,h36⟩,
          cases h105 with h106 h107,
          {
            contradiction,
          },
          {
            exact h104 h107,
          }
        },
        {
          rw sym at h103,
          exact h34 u h h103,
        }
      end,
    have h200: ℕℕ ⊆ y:=
      begin
        rw subset_definition,
        intros t ht,
        rw N_members at ht,
        have h5:= ht y ⟨ h32,h100⟩, 
        exact h5,
      end,
    have h201: y = ℕℕ :=
      begin
        rw full_extensionality,
        intros t,
        split,
        {
          intro h,
          exact member_subset M y ℕℕ t hynn h,
        },
        {
          intro h,
          exact member_subset M ℕℕ y t h200 h,
        }
      end,
    rw h201 at *,
    contradiction,
  end

lemma oneoneimpliesdecidableequality: ¬ ℕℕ ∈ FINITE M → ℕℕ ∈ DECIDABLE M:=
  assume hnotfinite,
  begin
    have base: ChurchZero ∈ Z_decidableequality M:=
      begin
        rw Z_decidableequality_members,
        split,
        {
          exact zeroN M,
        },
        {
          have h4:= decidable0 M,
          intros n h,
          have h5:= h4 n h,
          rw sym,
          exact h5,
        }
      end,
    have step: ∀ (x:M), x ∈ Z_decidableequality M → S x ∈ Z_decidableequality M:=
      begin
        intros x hx,
        rw Z_decidableequality_members at hx,
        cases hx with h3 h4,
        rw Z_decidableequality_members,
        split,
        {
          exact successorN M x h3,
        },
        {
          intros y hy,
          have h5:= decidable0 M y hy,
          cases h5 with h6 h7,
          {
            rw h6 at *,
            right,
            have h8:= successoromitszero M x h3,
            exact h8,
          },
          {
            have h9:= predecessor M y hy h7,
            cases h9 with z h10,
            cases h10 with hz h11,
            rw← h11 at *,
            have h12:= h4 z hz,
            cases h12 with h13 h14,
            {
              left,
              rw h13,
            },
            {
              right,
              have h15:= Churchsuccessorweaklyoneone M hnotfinite x z h3 hz h14,
              exact h15,
            }
          }
        }
      end,
    have h200: ℕℕ ⊆ Z_decidableequality M:=
      begin
        rw subset_definition,
        intros t ht,
        rw N_members at ht,
        have h5:= ht (Z_decidableequality M) ⟨ base, step⟩,
        exact h5,
      end,
    rw decidable_members,
    intro x,
    rw subset_definition at h200,
    specialize h200 x,
    rw Z_decidableequality_members at h200,
    intros v h,
    cases h with hx hv,
    have h201:= h200 hx,
    cases h201 with h202 h203,
    exact h203 v hv,
  end

theorem Churchsuccessoroneone: ¬ ℕℕ ∈ FINITE M → ∀ (x y:M), x ∈ ℕℕ → y ∈ ℕℕ → S x = S y → x = y:=
  assume hnotfinite,
  begin
    intros x y hx hy hsxy,
    have h3:= oneoneimpliesdecidableequality M hnotfinite,
    have h4:= Churchsuccessorweaklyoneone M hnotfinite x y hx hy,
    rw decidable_members at h3,
    have h5:= h3 x y ⟨ hx, hy⟩,
    cases h5 with h6 h7,
    {
      exact h6,
    },
    {
      have h8:= h4 h7,
      contradiction,
    }
  end

theorem infinity1:  ¬ ℕℕ ∈ FINITE M → infinite M ℕℕ :=
  assume hnotfinite,
  begin
    have h3:= Churchsuccessoroneone M hnotfinite,
    unfold infinite,
    use ℕℕ - single ChurchZero,
    split,
    {
      rw subset_definition,
      intros t h,
      rw minus_members at h,
      rw singleton1 at h,
      exact h.left,
    },
    {
      split,
      {
        intro h,
        rw full_extensionality at h,
        specialize h ChurchZero,
        rw minus_members at h,
        rw singleton1 at h,
        cases h with h2 h3,
        have h4:= zeroN M,
        have h5:= h2 h4,
        cases h5 with h6 h7,
        contradiction,
      },
      {
        unfold similar,
        use (SG M),
        unfold similarity,
        split,
        {
          have h4:= SGFUNC M,
          unfold oneone,
          have h5:= SGMaps M,
          unfold maps at h5,
          rcases h5 with ⟨ h6, h7, h8, h9⟩,
          split,
          {
            unfold maps,
            repeat{split},
            {
              exact h6,
            },
            {
              intros x y h,
              have h10:= h7 x y h,
              rw minus_members,
              rw singleton1,
              split,
              {
                exact h10,
              },
              {
                cases h with h11 h12,
                rw SG_members at h12,
                cases h12 with z h13,
                rw ordered_pair_equality at h13,
                cases h13 with h14 hz,
                cases h14 with h15 h16,
                rw← h15 at *,
                rw h16,
                exact successoromitszero M x h11,
              }
            },
            {
              rw FUNC_members at h4,
              intros x y z h,
              rcases h with ⟨ h20, h21, h22⟩,
              exact h4 x y z h21 h22,
            },
            {
              intros x hx,
              use S x,
              split,
              {
                rw minus_members,
                rw singleton1,
                split,
                {
                  exact successorN M x hx,
                },
                {
                  exact successoromitszero M x hx,
                }
              },
              {
                rw SG_members,
                use x,
                simp,
                exact hx,
              }
            }
          },
          {
            split,
            {
              intros x u y h,
              rcases h with ⟨ h10, h11, hx⟩,
              rw SG_members at h10 h11,
              cases h11 with a h12,
              cases h10 with b h13,
              cases h12 with h14 h15,
              cases h13 with h16 h17,
              rw ordered_pair_equality at h14 h16,
              cases h16 with h18 h19,
              rw← h18 at *,
              cases h14 with h20 h21,
              rw← h20 at *,
              rw h21 at *,
              rw sym,
              have h22:= Churchsuccessoroneone M hnotfinite u x h15 h17 h19,
              exact h22,
            },
            {
              intros x y h,
              cases h with h30 h31,
              rw SG_members at h30,
              cases h30 with c h33,
              cases h33 with h34 h35,
              rw ordered_pair_equality at h34,
              cases h34 with h36 h37,
              rw← h36 at *,
              exact h35,
            }
          }
        },
        {
          unfold onto,
          intros y h,
          rw minus_members at h,
          cases h with hy h5,
          rw singleton1 at h5,
          have h6:= predecessor M y hy h5,
          cases h6 with r h7,
          cases h7 with hr h8,
          use r,
          split,
          {
            exact hr,
          },
          {
            rw SG_members,
            use r,
            rw h8,
            simp,
            exact hr,
          }
        }
      }
    }
  end

#axioms_all




