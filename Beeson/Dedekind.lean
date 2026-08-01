import ChurchNumbers

variables (M:Type) [Model M] (a b x y z u v w X R W κ μ ℓ : M)
-- using ℓ where the source text has λ because you can't use λ for a variable.

open Model 

lemma finitefunction: ∀(X f:M), X ∈ FINITE M → Rel f → dom f = X → maps M f X X → f ∈ FINITE M:=
  assume X f,
  begin
    intros hX hrel hdom hmaps,
    have hrelcopy:= hrel,
    have h2:= finitedecidable M X hX,
    have h30:= h2, 
    rw decidable_members at h2,
    have h3: ∀ (x y:M), x ∈ X → y ∈ X → ‹ x,y › ∈ f ∨ ¬  ‹ x,y› ∈ f:=
      assume x y,
      begin
        intros hx hy,
        unfold maps at hmaps,
        rcases hmaps with ⟨ h4, h5, h6, h7⟩,
        have h8:= h7 x hx,
        cases h8 with z h9,
        cases h9 with h10 h11,
        have h12:= h2 y z ⟨ hy, h10 ⟩,
        cases h12 with h13 h14,
        {
          rw h13 at *,
          left,
          exact h11,
        },
        {
          right,
          intros h,
          have h15:= h6 x y z ⟨ hx, h, h11⟩, 
          contradiction,
        }
      end,
    have h4:= subset_reflexive M X,
    have h5:= productfinite M X hX X X h30 hX h4 h4, 
    have h6: f ⊆ X × X:=
      begin
        rw subset_definition,
        intros t h,
        rw full_extensionality at hdom,
        rw Rel_definition at hrel,
        have h7:= hrel t h,
        cases h7 with x h8,
        cases h8 with y h9,
        rw h9 at *,
        have h10:= domain_axiom f hrelcopy x,
        have h11:= hdom x,
        rw h11 at h10,
        have h12:= h10.mpr ⟨ y, h⟩,
        unfold maps at hmaps,
        rcases hmaps with ⟨ h24, h25, h26, h27⟩,
        have h28:= h27 x h12,
        cases h28 with z h29,
        cases h29 with h30 h31,
        have h32:= h26 x y z ⟨ h12, h, h31⟩,
        rw h32 at *,
        rw product_axiom,
        use x, use z,
        simp,
        exact ⟨ h12, h30⟩,
      end,
    have h10:= separablefinite M (X × X) h5 f h6,
    apply h10,
    unfold separable_subset,
    split,
    {
      exact h6,
    },
    {
      rw full_extensionality,
      intro t,
      split,
      {
        intro ht,
        rw product_axiom at ht,
        cases ht with x h20,
        cases h20 with y h21,
        rcases h21 with ⟨ h22, h23, h24⟩, 
        rw binary_union_axiom,
        rw minus_members,
        rw h24,
        have h25:= h3 x y h22 h23,
        cases h25 with h26 h27,
        {
          left,
          exact h26,
        },
        {
          right,
          split,
          {
            rw product_axiom,
            use x, use y,
            simp,
            exact ⟨ h22, h23⟩, 
          },
          {
            exact h27,
          }
        }
      },
      {
        intros h11,
        rw binary_union_axiom at h11,
        rw minus_members at h11,
        cases h11 with h12 h13,
        {
          have h14:= member_subset M f (X × X) t h6 h12,
          exact h14,
        },
        {
          exact h13.left,
        }
      }
    }
  end

lemma decidable_preimage: ∀ (X f y:M), X ∈ FINITE M → maps M f X X → dom f = X → Rel f → y ∈ X →
(∃ (x:M), x ∈ X ∧ ‹ x,y› ∈ f) ∨ (¬ ∃ (x:M), x ∈ X ∧ ‹ x,y › ∈ f):=
  assume X f y,
  begin
    intros hX hmaps hdom hrel hy,
    have hrelcopy:= hrel,
    set Z:= preimage M f X y with h50,
    have h3: f ⊆ X × X:=
      begin
        rw subset_definition,
        intros t ht,
        rw Rel_definition at hrel,
        have h3:= hrel t ht,
        cases h3 with x h4,
        cases h4 with y h5,
        rw h5 at *,
        rw product_axiom,
        use x, use y,
        simp,
        rw full_extensionality at hdom,
        have h6:= hdom x,
        rw domain_axiom f hrelcopy at h6,
        have h7:= h6.mp ⟨ y, ht⟩, 
        unfold maps at hmaps,
        rcases hmaps with ⟨ h17, h8, h9, h10⟩, 
        have h11:= h8 x y ⟨ h7, ht⟩, 
        exact ⟨ h7, h11⟩, 
      end,
    have h20:= finitefunction M X f hX hrel hdom hmaps, 
    have h21:= finitedecidable M X hX,
    have h22:= subset_reflexive M X,
    have h23:= productfinite M X hX X X h21 hX h22 h22,
    have h24:= finiteseparable M   (X × X) f h23 h20 h3,
    have h25:= boundedquantification M f X X,
    apply h25,
    {
      repeat{split},
      {
        exact hX,
      },
      {
        exact h22,
      },
      {
        exact h21,
      },
      {
        intros u z hu hz,
        rw full_extensionality at h24,
        specialize h24 ‹ u,z›,
        rw product_axiom at h24,
        have h25: (∃ (a b : M), a ∈ X ∧ b ∈ X ∧  ‹ u,z ›  =  ‹ a,b › ):=
          begin
            use u, use z,
            simp,
            exact ⟨ hu, hz⟩,
          end,
        rw h24 at h25,
        rw binary_union_axiom at h25,
        cases h25 with h26 h27,
        {
          rw minus_members at h26,
          right,
          exact h26.right,
        },
        {
          left,
          exact h27,
        }
      }
    },
    {
      exact hy,
    }
  end

theorem dedekind1: ∀ (X:M), X ∈ FINITE M → ∀ (f:M), oneone M f X X → Rel f → dom f = X → onto M f X X:=
  begin
    have base: Λ ∈ W_dedekind1 M:=
      begin
        rw W_dedekind1_members,
        split,
        {
          exact lambda_finite M,
        },
        {
          intros f h hrel hdom,
          unfold onto,
          intros y h10,
          have h11:= emptyset_axiom y,
          contradiction,
        }
      end,
    have step: adjoin_closed M (W_dedekind1 M):=
      begin
        unfold adjoin_closed,
        intros B a h,
        cases h with h3 h4,
        rw W_dedekind1_members at h3,
        cases h3 with h5 h6,
        rw W_dedekind1_members,
        have h55:= finitedecidable M B h5,
        rw decidable_members at h55,
        split,
        {
          have h7:= finite_adjoin M B a ⟨ h5, h4⟩, 
          exact h7,
        },
        {
          intros f h8 hrel hdom,
          unfold oneone at h8,
          rcases h8 with ⟨ h9, h10, h11⟩, 
          have hmaps:= h9,
          unfold maps at h9,
          rcases h9 with ⟨ h12, h13, h14, h15⟩,
          have h16: a ∈ B ∪ single a:=
            begin
              rw binary_union_axiom,
              right,
              rw singleton1,
            end,
          set X:= B ∪ single a with h50,
          have h99:= finite_adjoin M B a ⟨ h5, h4⟩, 
          rw← h50 at h99,
          have h100:= decidable_preimage M X f a h99 hmaps hdom hrel h16,
          have h80:= finitedecidable M X h99,
          rw decidable_members at h80,
          cases h100 with h101 h102,
          {  --case 1 in the paper
            
            cases h101 with c h102,
            cases h102 with h103 h104,
            have h105:= h80 c a ⟨ h103, h16⟩, 
            cases h105 with h106 h107,
            {  -- case 1a in the paper, c = a
              rw h106 at *,
              set g:= restrict f B with h51,
              have h90: Rel g:=
                begin
                  rw Rel_definition,
                  intros z hz,
                  rw h51 at hz,
                  rw restrict_definition f B at hz,
                  rw intersection_axiom at hz,
                  cases hz with h30 h31,
                  rw product_axiom at h31,
                  cases h31 with a h32,
                  cases h32 with b h33,
                  use a, use b,
                  exact h33.right.right,
                end,
              have h108: oneone M g B B:=
                begin
                  unfold oneone,
                  unfold maps,
                  rw h51 at *, 
                  repeat{split},
                  {
                    rw Rel_definition,
                    intros z hz,
                    rw restrict_definition at hz,
                    rw intersection_axiom at hz,
                    cases hz with h20 h21,
                    rw product_axiom at h21,
                    cases h21 with a h22,
                    cases h22 with b h23,
                    use a, use b,
                    exact h23.right.right,
                  },
                  {
                    intros x y h21,
                    cases h21 with h22 h23,
                    rw restriction at h23,
                    cases h23 with h24 h25,
                    have h28: x ∈ X:=
                      begin
                        rw h50,
                        rw binary_union_axiom,
                        left,
                        exact h25,
                      end,
                    have h26: ¬ x = a:=
                      begin
                        intro h27,
                        rw h27 at *,
                        contradiction,
                      end,
                    have h27: y ∈ X:=
                      begin
                        have h29:= h13 x y ⟨ h28, h24⟩, 
                        exact h29,
                      end,
                    rw h50 at h27,
                    rw binary_union_axiom at h27,
                    cases h27 with h28 h29,
                    {
                      exact h28,
                    },
                    {
                      rw singleton1 at h29,
                      rw h29 at *,
                      have h30:= h10 x a a ⟨ h24, h104, h28⟩, 
                      contradiction, 
                    }
                  },
                  {
                    intros x y z h,
                    rcases h with ⟨ h20, h21, h22⟩,
                    rw restriction M f at h21 h22,
                    cases h22 with h23 h24,
                    cases h21 with h25 h26,
                    have h27: x ∈ X:=
                      begin
                        rw h50,
                        rw binary_union_axiom,
                        left,
                        exact h26,
                      end,
                    have h28:= h14 x y z ⟨ h27, h25, h23⟩, 
                    exact h28,
                  },
                  {
                    intros x hx,
                    have h27: x ∈ X:=
                      begin
                        rw h50,
                        rw binary_union_axiom,
                        left,
                        exact hx,
                      end,
                    have h28:= h15 x h27,
                    cases h28 with y h29,
                    cases h29 with h30 h31,
                    use y,
                    have h32: ¬ x = a:=
                      begin
                        intro h33,
                        rw h33 at *,
                        contradiction,
                      end,
                    have h33: ¬ y = a:=
                      begin
                        intro h,
                        rw h at *,
                        have h34:= h10 x a a ⟨ h31, h104, h27⟩, 
                        contradiction,
                      end,
                    split,
                    {
                      rw h50 at h30,
                      rw binary_union_axiom at h30,
                      cases h30 with h31 h32,
                      {
                        exact h31,
                      },
                      {
                        rw singleton1 at h32,
                        contradiction,
                      }
                    },
                    {
                      rw restriction,
                      exact ⟨ h31, hx⟩, 
                    }
                  },
                  {
                    intros x u y h,
                    rcases h with ⟨ h20, h21, h22⟩,
                    rw restriction at h20 h21,
                    cases h21 with h23 h24,
                    cases h20 with h25 h26,
                    have h27: x ∈ X:=
                      begin
                        rw h50,
                        rw binary_union_axiom,
                        left,
                        exact h26,
                      end,
                    have h28:= h10 x u y ⟨ h25, h23, h27⟩, 
                    exact h28,
                  },
                  {
                    intros x y h,
                    cases h with h20 h21,
                    rw restriction at h20,
                    cases h20 with h21 h22,
                    exact h22,
                  }
                end,
              have h91: dom g = B:=
                begin
                  rw full_extensionality,
                  intro t,
                  split,
                  { 
                    intro h31,
                    rw domain_axiom g h90 at h31, 
                    cases h31 with z h32,
                    rw h51 at h32,
                    rw restriction at h32,
                    exact h32.right,
                  },
                  { 
                    intro h31,
                    rw domain_axiom g h90,
                    unfold oneone at h108,
                    cases h108 with h24 h25,
                    unfold maps at h24,
                    rcases h24 with ⟨ h25, h26, h27, h28⟩,
                    have h29:= h28 t h31,
                    cases h29 with p h32,
                    use p,
                    exact h32.right,
                  }
                end,
              have h109:= h6 g h108 h90 h91,
              unfold onto,
              intros y hy,
              have h30:= h80 y a ⟨ hy, h103⟩, 
              cases h30 with h31 h32,
              {
                use a,
                rw h31 at *,
                exact ⟨ hy, h104⟩,
              },
              {
                have h33:y ∈ B:=
                  begin
                    rw h50 at hy,
                    rw binary_union_axiom at hy,
                    rw singleton1 at hy,
                    cases hy with h34 h35,
                    {
                      exact h34,
                    },
                    {
                      contradiction, 
                    }
                  end,
                unfold onto at h109,
                have h110:= h109 y h33,
                cases h110 with x h111,
                cases h111 with h112 h113,
                use x,
                split,
                {
                  rw h50,
                  rw binary_union_axiom,
                  left,
                  exact h112,
                },
                {
                  rw h51 at h113,
                  rw restriction at h113, 
                  exact h113.left,
                }
              }
            },
            {  -- case 1b in the paper, c ≠ a
              have h20:= h15 a h16,
              cases h20 with b h21,
              cases h21 with h22 h23,
              have h200: ¬ b=a:=
                begin
                  intros h,
                  rw h at *,
                  have h201:= h10 a c a ⟨ h23, h104, h16⟩,
                  rw sym at h201,
                  contradiction, 
                end,
              set g:= ((f - (single ‹ c,a›) - (single ‹ a,b› )) ∪ (single ‹c,b› )) with h56,
              have h24: Rel g:=
                begin
                  rw Rel_definition,
                  intros z hz,
                  rw h56 at hz,
                  rw binary_union_axiom at hz,
                  rw minus_members at hz,
                  cases hz with h25 h26,
                  {
                    cases h25 with h27 h28,
                    rw minus_members at h27,
                    rw Rel_definition at h12,
                    have h29:= h12 z h27.left,
                    exact h29,
                  },
                  {
                    rw singleton1 at h26,
                    use c, use b,
                    exact h26,
                  }
                end,
              have h25: dom g = B:=
                begin
                  rw full_extensionality,
                  intro t,
                  rw domain_axiom g h24,
                  split,
                  {
                    intro h,
                    cases h with y h25,
                    rw h56 at h25,
                    rw binary_union_axiom at h25,
                    rw minus_members at h25,
                    rw singleton1 at h25,
                    rw singleton1 at h25,
                    cases h25 with h26 h27,
                    { 
                      cases h26 with h29 h30,
                      rw minus_members at h29,
                      cases h29 with h31 h32, 
                      have h33:= (domain_axiom f hrel t).mpr ⟨ y, h31⟩, 
                      rw hdom at h33,
                      rw h50 at h33,
                      rw binary_union_axiom at h33,
                      cases h33 with h34 h35,
                      {
                        exact h34,
                      },
                      {
                        rw singleton1 at h35,
                        rw h35 at *,
                        have h36: a ∈ X:=
                          begin
                            rw h50,
                            rw binary_union_axiom,
                            right,
                            rw singleton1, 
                          end,
                        have h37:= h14 a y b ⟨ h36, h31, h23⟩, 
                        rw h37 at *,
                        contradiction, 
                      }
                    },
                    {
                      rw ordered_pair_equality at h27,
                      cases h27 with h28 h29,
                      rw h28 at *,
                      rw h29 at *,
                      rw h50 at h103,
                      rw binary_union_axiom at h103,
                      cases h103 with h104 h105,
                      {
                        exact h104,
                      },
                      {
                        rw singleton1 at h105,
                        contradiction,
                      }
                    }
                  },
                  {
                    intro h,
                    have h115: t ∈ X:=
                      begin
                        rw h50,
                        rw binary_union_axiom,
                        left,
                        exact h,
                      end,
                    have h116:= h15 t h115,
                    cases h116 with z h117,
                    cases h117 with h118 h119,
                    have h120:= h80 t c ⟨ h115, h103⟩,
                    have h130:= h80 t a ⟨ h115, h16⟩,
                    cases h120 with h121 h122,
                    { 
                      rw h121 at *,
                      use b,
                      rw h56,
                      rw binary_union_axiom,
                      right,
                      rw singleton1,
                    },
                    {
                      cases h130 with h131 h132,
                      {
                        rw h131 at *,
                        contradiction,
                      },
                      {
                        use z,
                        rw h56,
                        rw binary_union_axiom,
                        left,
                        rw minus_members,
                        split,
                        {
                          rw minus_members,
                          rw singleton1,
                          split,
                          {
                            exact h119,
                          },
                          {
                            intro h133,
                            rw ordered_pair_equality at h133,
                            cases h133 with h134 h135,
                            contradiction,
                          }
                        },
                        {
                          rw singleton1,
                          intro h133,
                          rw ordered_pair_equality at h133,
                          cases h133 with h134 h135,
                          contradiction,
                        }
                      }
                    }                     
                  }
                end,
              have h30: oneone M g B B:=
                begin
                  unfold oneone,
                  repeat{split},
                  {
                    exact h24,
                  },
                  {
                    intros x y h26,
                    cases h26 with h27 h28,
                    rw h56 at h28,
                    rw binary_union_axiom at h28,
                    cases h28 with h29 h30,
                    {
                      rw minus_members at h29,
                      rw minus_members at h29,
                      rw singleton1 at h29,
                      rw singleton1 at h29,
                      cases h29 with h30 h31,
                      cases h30 with h32 h33,
                      have h34: x ∈ X:=
                        begin
                          have h35:= domain_axiom f hrel x,
                          rw hdom at h35,
                          rw h35,
                          exact ⟨ y, h32⟩, 
                        end,
                      have h35:= h13 x y ⟨ h34, h32⟩,
                      rw h50 at h35,
                      rw binary_union_axiom at h35,
                      cases h35 with h36 h37,
                      {
                        exact h36,
                      },
                      {
                        rw singleton1 at h37,
                        rw h37 at *,
                        rw ordered_pair_equality at h31 h33,
                        simp at h33,
                        have h38:= h10 x c a ⟨ h32, h104, h34⟩, 
                        contradiction,
                      }
                    },
                    {
                      rw singleton1 at h30,
                      rw ordered_pair_equality at h30,
                      rw h30.left at *,
                      rw h30.right at *,
                      rw h50 at h22,
                      rw binary_union_axiom at h22,
                      rw singleton1 at h22,
                      cases h22 with h31 h32,
                      {
                        exact h31,
                      },
                      {
                        rw h32 at *,
                        contradiction, 
                      }
                    }
                  },
                  {
                    intros x y z h,
                    rcases h with ⟨ h30, h31, h32⟩,
                    have h33: x ∈ X:=
                      begin
                        rw h50,
                        rw binary_union_axiom,
                        left,
                        exact h30,
                      end,
                    have h34:= h80 x c ⟨ h33, h103⟩, 
                    cases h34 with h35 h36,
                    { 
                      rw h35 at *,
                      rw h56 at h31 h32,
                      rw binary_union_axiom at h31 h32,
                      cases h31 with h37 h38,
                      {
                        cases h32 with h39 h40,
                        {
                          rw minus_members at h37 h39,
                          rw minus_members at h37 h39,
                          rw singleton1 at h37 h39,
                          rw singleton1 at h37 h39,
                          have h40:= h39.left.left,
                          have h41:= h37.left.left,
                          have h46:= h14 c y z ⟨ h33, h41, h40⟩,
                          exact h46,
                        },
                        { 
                          rw singleton1 at h40,
                          rw ordered_pair_equality at h40,
                          cases h40 with h41 h42,
                          rw h42 at *,
                          rw minus_members at h37,
                          cases h37 with h43 h44,
                          rw minus_members at h43,
                          cases h43 with h45 h46,
                          have h47:= h14 c y a ⟨ h33, h45, h104⟩,
                          rw h47 at *,
                          rw singleton1 at h46,
                          contradiction,
                        }
                      },
                      {
                        rw singleton1 at h38,
                        rw ordered_pair_equality at h38,
                        cases h38 with h39 h40,
                        rw h40 at *,
                        cases h32 with h41 h42,
                        {
                          rw minus_members at h41,
                          cases h41 with h43 h44,
                          rw minus_members at h43,
                          cases h43 with h45 h46,
                          have h47:= h14 c z a ⟨ h33, h45, h104⟩, 
                          rw h47 at *,
                          rw singleton1 at h46,
                          rw ordered_pair_equality at h46,
                          simp at h46,
                          contradiction, 
                        },
                        {
                          rw singleton1 at h42,
                          rw ordered_pair_equality at h42,
                          symmetry,
                          exact h42.right, 
                        }
                      }
                    },
                    {
                      rw h56 at h31 h32,
                      rw binary_union_axiom at h31 h32,
                      cases h31 with h33 h34,
                      {
                        cases h32 with h35 h36,
                        {
                          rw minus_members at h33 h35,
                          rw minus_members at h33 h35,
                          cases h35 with h36 h37,
                          cases h36 with h38 h39,
                          cases h33 with h40 h41,
                          cases h40 with h42 h43,
                          have h44:= h14 x y z ⟨ h33, h42, h38⟩,
                          exact h44, 
                        },
                        {
                          rw singleton1 at h36,
                          rw ordered_pair_equality at h36,
                          cases h36 with h40 h41,
                          contradiction, 
                        }
                      },
                      {
                        rw singleton1 at h34,
                        rw ordered_pair_equality at h34,
                        cases h34 with h40 h41,
                        contradiction, 
                      }
                    }
                  },
                  {
                    intros x h,
                    rw←  h25 at h,
                    rw domain_axiom g h24 at h, 
                    cases h with y h40,
                    use y,
                    rw and_comm,
                    split,
                    {
                      exact h40,
                    },
                    {
                      rw h56 at h40,
                      rw binary_union_axiom at h40,
                      rw minus_members at h40,
                      rw minus_members at h40,
                      have h41: b ∈ B :=
                        begin
                          rw h50 at h22,
                          rw binary_union_axiom at h22,
                          cases h22 with h41 h42,
                          {
                            exact h41,
                          },
                          {
                            rw singleton1 at h42,
                            contradiction, 
                          }
                        end,
                      rw or_comm at h40,
                      cases h40 with h42 h43,
                      {
                        rw singleton1 at h42,
                        rw ordered_pair_equality at h42,
                        cases h42 with h43 h44,
                        rw h44 at *,
                        exact h41, 
                      },
                      {
                        cases h43 with h44 h45,
                        cases h44 with h46 h47,
                        have h48: x ∈ X:=
                          begin
                            rw ← hdom,
                            rw domain_axiom f hrel,
                            use y,
                            exact h46, 
                          end,
                        have h48:= h13 x y ⟨ h48, h46⟩,
                        rw h50 at h48,
                        rw binary_union_axiom at h48,
                        cases h48 with h49 h51,
                        {
                          exact h49,
                        },
                        {
                          rw singleton1 at h51,
                          rw h51 at *,
                          have h51:= h10 x c a ⟨ h46, h104, h48⟩, 
                          rw h51 at *,
                          rw singleton1 at h47,
                          contradiction, 
                        }
                      }
                    }
                  },
                  {
                    intros x y u h,
                    rcases h with ⟨ h30, h31, h32⟩,
                    have h33:x ∈ X:=
                      begin
                        rw h50,
                        rw binary_union_axiom,
                        left, 
                        exact h32,
                      end,
                    rw h56 at h30 h31,
                    rw binary_union_axiom at h30 h31,
                    rw minus_members at h30 h31,
                    rw minus_members at h30 h31,
                    cases h31 with h32 h33,
                    {
                      cases h30 with h34 h35,
                      {
                        cases h34 with h36 h37,
                        cases h36 with h38 h39,
                        cases h32 with h40 h41,
                        cases h40 with h42 h43,
                        have h44:= h13 x u ⟨ h33, h38⟩,
                        have h45:= h10 x y u ⟨ h38, h42, h33⟩, 
                        exact h45,
                      },
                      {
                        rw singleton1 at h35,
                        rw ordered_pair_equality at h35,
                        cases h35 with h36 h37,
                        rw h36 at *,
                        rw h37 at *,
                        cases h32 with h38 h39,
                        cases h38 with h40 h41,
                        have h43: y ∈ X:=
                          begin
                            rw← hdom,
                            rw domain_axiom f hrel,
                            use b,
                            exact h40,
                          end, 
                        have h42:= h10 y a b ⟨ h40, h23, h43⟩,
                        rw h42 at *,
                        rw singleton1 at h39,
                        contradiction,
                      }
                    },
                    {
                      rw singleton1 at h33,
                      rw ordered_pair_equality at h33, 
                      cases h33 with h34 h35,
                      rw  h34 at *,
                      rw h35 at *, 
                      rw or_comm at h30,
                      cases h30 with h36 h37,
                      {
                        rw singleton1 at h36,
                        rw ordered_pair_equality at h36,
                        cases h36 with h38 h39,
                        exact h38,
                      },
                      {
                        cases h37 with h38 h39,
                        cases h38 with h40 h41,
                        have h42:= h10 x a b ⟨ h40, h23, h33⟩,
                        rw h42 at *,
                        rw singleton1 at h39,
                        contradiction, 
                      }
                    }
                  },
                  {
                    intros x y h,
                    rw←  h25,
                    rw domain_axiom g h24,
                    use y,
                    exact h.left,
                  }
                end,
              have h70:= h6 g h30 h24 h25,
              unfold onto,
              intros y hy,
              have h71:= h80 y a ⟨ hy, h16⟩,
              cases h71 with h72 h73,
              {
                rw h72 at *,
                use c,
                exact ⟨ h103, h104⟩,
              },
              {
                have h74:= h80 y b ⟨ hy, h22⟩,
                cases h74 with h75 h76,
                {
                  rw h75 at *,
                  use a,
                  exact ⟨ h16, h23⟩, 
                },
                {
                  have h77: y ∈ B:=
                    begin
                      rw h50 at hy,
                      rw binary_union_axiom at hy,
                      cases hy with h78 h79,
                      {
                        exact h78,
                      },
                      {
                        rw singleton1 at h79,
                        contradiction,
                      }
                    end,
                  unfold onto at h70,
                  have h81:= h70 y h77,
                  cases h81 with x h82,
                  use x,
                  cases h82 with h83 h84,
                  split,
                  {
                    rw h50,
                    rw binary_union_axiom,
                    left, 
                    exact h83,
                  },
                  {
                    rw h56 at h84,
                    rw binary_union_axiom at h84,
                    cases h84 with h85 h86,
                    {
                      rw minus_members at h85,
                      rw minus_members at h85,
                      cases h85 with h86 h87,
                      cases h86 with h88 h89,
                      exact h88, 
                    },
                    {
                      rw singleton1 at h86,
                      rw ordered_pair_equality at h86,
                      rw h86.left at *,
                      rw h86.right at *,
                      contradiction,
                    }
                  }
                }
              }
            }
          },
          {  -- case 2 in the paper 
            set g:= restrict f B  with h57,
            have h20: Rel g:=
              begin
                rw Rel_definition,
                intros z h,
                rw h57 at h,
                rw restrict_definition at h,
                rw intersection_axiom at h,
                cases h with h58 h59,
                rw product_axiom at h59,
                cases h59 with a h60,
                cases h60 with b h61,
                use a, use b,
                exact h61.right.right,
              end,
            have h21: dom g = B:=
              begin
                rw full_extensionality,
                intro t,
                split,
                {
                  intro h,
                  rw domain_axiom g h20 at h,
                  cases h with y h22,
                  rw h57 at h22,
                  rw restriction at h22,
                  exact h22.right,
                },
                {
                  rw domain_axiom g h20,
                  rw Rel_definition at h20,
                  intro h,
                  have h23:t ∈ X:=
                    begin
                      rw h50,
                      rw binary_union_axiom,
                      left,
                      exact h,
                    end,
                  have h24:=h15 t h23,
                  cases h24 with y h25,
                  use y,
                  rw h57,
                  rw restriction, 
                  exact ⟨ h25.right, h⟩, 
                }
              end,
            have h22: oneone M g B B:=
              begin
                unfold oneone,
                repeat {split},
                {
                  exact h20,
                },
                {
                  intros x y h,
                  cases h with h23 h24,
                  rw h57 at h24,
                  rw restriction at h24,
                  have h25:x ∈ X:=
                    begin
                      rw h50,
                      rw binary_union_axiom,
                      left,
                      exact h23,
                    end,
                  have h26:= h13 x y ⟨ h25, h24.left⟩,
                  have h27: ¬ (y = a):=
                    begin
                      intro h28,
                      rw h28 at *,
                      exact h102 ⟨ x, ⟨ h25, h24.left⟩ ⟩, 
                    end,
                  rw h50 at h26,
                  rw binary_union_axiom at h26,
                  cases h26 with h29 h30,
                  {
                    exact h29,
                  },
                  {
                    rw singleton1 at h30,
                    contradiction,
                  } 
                },
                {
                  intros x y z h,
                  rcases h with ⟨ h30, h31, h32⟩,
                  have h33: x ∈ X:=
                    begin
                      rw h50,
                      rw binary_union_axiom,
                      left,
                      exact h30,
                    end,
                  rw h57 at h31 h32,
                  rw restriction at h31 h32,
                  cases h31 with h34 h35,
                  cases h32 with h36 h37,
                  have h38:= h14 x y z ⟨ h33, h34, h36⟩,
                  exact h38,
                },
                {
                  intros x h30,
                  have h33: x ∈ X:=
                    begin
                      rw h50,
                      rw binary_union_axiom,
                      left,
                      exact h30,
                    end,
                  have h34:= h15 x h33,
                  cases h34 with y h31,
                  use y,
                  have h35: ¬ y = a:=
                    begin
                      intro h,
                      rw h at *,
                      exact h102 ⟨ x, ⟨ h33, h31.right⟩ ⟩, 
                    end,
                  rw h50 at h33,
                  rw binary_union_axiom at h33,
                  cases h33 with h36 h37,
                  {
                    split,
                    {
                      cases h31 with h40 h141,
                      rw h50 at h40,
                      rw binary_union_axiom at h40,
                      rw singleton1 at h40,
                      cases h40 with h41 h42,
                      {
                        exact h41,
                      },
                      {
                        contradiction,
                      }
                    },
                    {
                      rw h57,
                      rw restriction,
                      exact ⟨ h31.right, h30⟩, 
                    }
                  },
                  {
                    rw singleton1 at h37,
                    rw h37 at *,
                    contradiction,
                  } 
                },
                {
                  intros x u y h,
                  rcases h with ⟨ h30, h31, h32⟩, 
                  rw h57 at h31 h30, 
                  rw restriction at h30 h31,
                  cases h31 with h320 h33,
                  cases h30 with h34 h35,
                  have h36:x ∈ X:=
                    begin
                      rw h50,
                      rw binary_union_axiom,
                      left,
                      exact h35,
                    end,
                  have h37:= h10 x u y ⟨ h34, h320, h36⟩,
                  exact h37,
                },
                {
                  intros x y h,
                  cases h with h30 h31,
                  rw← h21,
                  rw domain_axiom g h20,
                  use y,
                  exact h30,
                }
              end,
            have h40:= h6 g h22 h20 h21,
            have h41:= h15 a h16,
            cases h41 with b h42,
            cases h42 with h43 h44,
            have h45: ¬ b = a:=
              begin
                intro h,
                rw h at *,
                exact h102 ⟨ a, ⟨ h43, h44⟩ ⟩, 
              end,
            have h46: b ∈ B:=
              begin
                rw h50 at h43,
                rw binary_union_axiom at h43,
                cases h43 with h47 h48,
                {
                  exact h47,
                },
                {
                  rw singleton1 at h48,
                  contradiction,
                }
              end,
            unfold onto at h40,
            have h47:= h40 b h46,
            cases h47 with x h48,
            cases h48 with h49 h51,
            rw h57 at h51,
            rw restriction at h51,
            cases h51 with h52 h53,
            have h54: x ∈ X:=
              begin
                rw h50,
                rw binary_union_axiom,
                left,
                exact h49,
              end,
            have h60:= h10 x a b ⟨ h52, h44, h54⟩, 
            rw h60 at *,
            contradiction,
          } -- end of case 2
        }
      end,
    intro X, 
    have h2: (FINITE M)⊆ W_dedekind1 M := (finite_conditions M) (W_dedekind1 M)  step base, 
    rw subset_definition at h2, 
    specialize h2 X,
    rw (W_dedekind1_members M) at h2,  
    intro h3,
    have h4:= h2 h3, 
    cases h4 with h5 h6, 
    exact h6, 
  end 



#axioms_all 