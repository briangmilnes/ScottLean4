import ChurchNumbers9
-- proof that the order of a permutation isn't n
-- proof of the induction step for every finite set has a permutation

variables (M:Type) [Model M] (a b x y z u v w X R W κ μ ℓ : M)

open Model 

lemma prectrichotomystrict:  ℕℕ ∈ FINITE M → ∀ (k n:M), n ∈ ℕℕ → k ∈ STEM → ¬ k = n →  S k = S n → ∀ (x y:M), x ∈ ℕℕ → y ∈ ℕℕ → x ≺ y ∨ x = y ∨ y ≺ x:=
  begin
    intros hfinite k n hn hstem   hkn hskn x y hx hy,
    have h80:= finitedecidable M ℕℕ hfinite,
    rw decidable_members at h80,
    have h81:= h80 x y ⟨ hx, hy⟩, 
    cases h81 with h10 h11,
    {
      right,left,
      exact h10,
    },
    {
      have h12:= prectrichotomy1 M hfinite k n hstem hn hkn hskn x y hx hy,
      cases h12 with h13 h14,
      {
        left,
        rw prec_definition,
        exact ⟨ h13, h11⟩,
      },
      {
        right,
        right,
        rw prec_definition,
        rw sym at h11,
        exact ⟨ h14, h11⟩,
      }
    }
  end

lemma enlarge: (∀(x:M), x ∈ 𝔽 → 𝕊 x ∈ 𝔽 ) → ∀ (X:M), X ∈ FINITE M → ¬¬ ∃ (c:M), ¬ (c ∈ X):=
  assume hF X hfinite,
  begin
    set p:= Nc M X with h50,
    have hp:= finitecardinals3 M X hfinite,
    rw← h50 at hp,
    have h4:= hF p hp,
    have h5:= cardinalsinhabited M (𝕊 p) h4,
    cases h5 with u h6,
    have h6copy:= h6,
    rw successor_members M p u at h6,
    cases h6 with v h7,
    cases h7 with c h8,
    rcases h8 with ⟨ h9, h10, h11⟩, 
    have h12:= xinNcx M X,
    rw← h50 at h12,
    have h13:= finitecardinals2 M X v p hp h12 h9,
    have h20:= finiteimpliesnotinfinite M X hfinite,
    unfold infinite at h20,
    have h21:c ∈ u:=
      begin
        rw h11,
        rw binary_union_axiom,
        rw singleton1,
        simp,
      end,
    have h14: ¬ u ⊆ X:=
      begin
        intros h,
        have h15: ¬ (v=X):=
          begin
            intro h22,
            rw full_extensionality at h22,
            specialize h22 c,
            have h23:= member_subset M u X c h h21,
            rw← h22 at h23,
            contradiction,  
          end,
        apply h20,
        use v,
        have h23:v ⊆ X:=
          begin
            rw subset_definition,
            intros z hz,
            have h24: z ∈ u:=
              begin
                rw h11,
                rw binary_union_axiom,
                rw singleton1,
                left,
                exact hz,
              end,
            have h25:= member_subset M u X z h h24,
            exact h25,
          end,
        rw sym at h15,
        exact ⟨ h23, h15, h13⟩, 
      end,
    have h28:= finitecardinals1 M (𝕊 p) u h4 h6copy,
    have h30:= finiteDNS M X u h28,
    rw subset_definition at h14,
    have h32: ¬ ∀ (z:M), z ∈ u → ¬¬ z ∈ X:=
      begin
        intro h,
        have h33:= h30 h,
        contradiction,
      end,
    have h33: ¬¬ ∃ (z:M), z ∈ u ∧ ¬ z ∈ X:=
      begin
        intro h,
        apply h32,
        intros z hz,
        intro h33,
        apply h,
        use z,
        exact ⟨ hz, h33⟩,
      end,
    have h40 : (∃ (z : M), z ∈ u ∧ ¬z ∈ X) → ∃ (c : M), ¬c ∈ X :=
      begin
        intro h,
        cases h with z h41,
        cases h41 with h42 h43,
        use z,
      end,
    have h45:= double_negate ((∃ (z : M), z ∈ u ∧ ¬z ∈ X) → (∃ (c : M), ¬c ∈ X)) h40,
    have h46:= push_double_negationNF (∃ (z : M), z ∈ u ∧ ¬z ∈ X)  (∃ (c : M), ¬c ∈ X) h45 h33,
    exact h46,
  end

lemma permorder2: ∀ (f X a q:M), X ∈ FINITE M → q ∈ ℕℕ → cyclicperm M f X a →  Ap (Ap q f) a = a → ∀ (x:M), x ∈ X → Ap (Ap q f) x = x:=
  begin
    intros f X a q hfinite hq h hqa x hx,
    unfold cyclicperm at h,
    cases h with hperm h3,
    cases h3 with ha h5,
    have h6:= h5 x hx,
    cases h6 with j h7,
    cases h7 with hj h8,
    have h9: Ap (Ap q f) x = Ap (Ap q f) (Ap (Ap j f) a):=
      begin
        rw← h8,
      end,
    unfold permutation at hperm,
    unfold injection at hperm,
    cases hperm with h30 honto,
    rcases h30 with ⟨ honeone, hRel, hFUNC, hdom, hrange⟩, 
    unfold oneone at honeone,
    rcases honeone with ⟨ hmaps, h31, h32⟩, 
    have h10:= doubleiteration M q hq X f j a hFUNC hmaps hj ha,
    rw h10 at h9,
    have h11:= ChurchAdditionCommutative M q hq j hj,
    rw← h11 at h9,
    have h12:= doubleiteration M j hj X f q a hFUNC hmaps hq ha,
    rw← h12 at h9,
    rw hqa at h9,
    rw← h8 at h9,
    exact h9,
  end
 
lemma orderstep1: ∀ (k n q:M), k ∈ ℕℕ → n ∈ ℕℕ → ℕℕ ∈ FINITE M → S k = S n → k ∈ STEM → q ∈ ℕℕ → ¬ q = n → ¬ q = ChurchZero → ∀ (X f a b c g:M), X ∈ FINITE M → ¬ c ∈ X → ‹ b,a › ∈ f → g= (f - single ‹ b,a › ∪ single ‹ b,c › ∪ single ‹ c,a›) → permutation M f X → permutation M g (X ∪ single c):=
  assume k n q hk hn hNfinite hskn hstem hq hqn hqz X f a b c g hfinite h3 h11 h50 h5,
  begin
    unfold permutation at h5,
    cases h5 with h7 h8,
    unfold onto at h8,
    unfold injection at h7,
    rcases h7 with ⟨ h20, h21, h22, h23, h24⟩, 
    have h25: b ∈ dom f:=
      begin
        rw domain_axiom f h21,
        use a,
        exact h11,
      end,     
    have hb:= member_subset M (dom f) X b h23 h25,
    have h26: a ∈ range f:=
      begin
        rw range_axiom f h21,
        use b,
        exact h11,
      end,
    have ha:= member_subset M (range f) X a h24 h26,
    unfold permutation,
    split,
    {
      unfold injection,
      rw and_comm,
      rw and_assoc,
      have hRelg: Rel g:= 
        begin
          rw Rel_definition,
          intros z hz,
          rw h50 at hz,
          repeat{rw binary_union_axiom at hz},
          rw minus_members at hz,
          repeat{rw singleton1 at hz},
          cases hz with h12 h13,
          {
            cases h12 with h14 h15,
            {
              cases h14 with h16 h17,
              rw Rel_definition at h21,
              exact h21 z h16,
            },
            {
              use b, use c,
              exact h15,
            }
          },
          {
            use c, use a,
            exact h13,
          }
        end,
      split,
      {
        exact hRelg,
      },
      {
        split,
        {
          split,
          {
            rw FUNC_members,
            rw FUNC_members at h22,
            intros x y z hxy hxz,
            rw h50 at hxy,
            rw h50 at hxz,
            repeat {rw binary_union_axiom at hxy hxz},
            rw minus_members at hxy hxz,
            repeat {rw singleton1 at hxy hxz},
            cases hxy with h31 h32,
            {
              cases h31 with h33 h34,
              {
                cases hxz with h41 h42,
                {
                  cases h41 with h43 h44,
                  {
                    exact h22 x y z h33.left h43.left,
                  },
                  {
                    rw ordered_pair_equality at h44,
                    cases h44 with h45 h46,
                    rw h45 at *,
                    rw h46 at *,
                    cases h33 with h47 h48,
                    have h49:= h22 b a y h11 h47,
                    rw h49 at h48,
                    contradiction,
                  }
                },
                {
                  rw ordered_pair_equality at h42,
                  cases h42 with h43 h44,
                  rw h43 at *,
                  rw h44 at *,
                  cases h33 with h45 h46,
                  have h47: c ∈ dom f:=
                    begin
                      rw domain_axiom f h21,
                      use y,
                      exact h45,
                    end,
                  have h48:= member_subset M (dom f) X c h23 h47,
                  contradiction,
                }
              },
              {
                rw ordered_pair_equality at h34,
                cases h34 with h35 h36,
                rw h35 at *,
                rw h36 at *,
                cases hxz with h40 h41,
                {
                  cases h40 with h42 h43,
                  {
                    cases h42 with h44 h45,
                    have h46:= h22 b a z h11 h44,
                    rw← h46 at *,
                    contradiction,
                  },
                  {
                    rw ordered_pair_equality at h43,
                    symmetry,
                    exact h43.right,
                  }
                },
                {
                  rw ordered_pair_equality at h41,
                  cases h41 with h42 h43,
                  rw h42 at *,
                  rw h43 at *,
                  contradiction,
                }
              }
            },
            {
              rw ordered_pair_equality at h32,
              cases h32 with h33 h34,
              rw h33 at *,
              rw h34 at *,
              cases hxz with h40 h41,
              {
                cases h40 with h42 h43,
                {
                  cases h42 with h44 h45,
                  have h46: c ∈ dom f:=
                    begin
                      rw domain_axiom f h21,
                      use z,
                      exact h44,
                    end,
                  have h47:= member_subset M (dom f) X c h23 h46,
                  contradiction,
                },
                {
                  rw ordered_pair_equality at h43,
                  cases h43 with h44 h45,
                  rw h44 at *,
                  rw h45 at *,
                  contradiction,
                }
              },
              {
                rw ordered_pair_equality at h41,
                symmetry,
                exact h41.right,
              }
            }
          },
          {
            rw subset_definition,
            split,
            {
              intros t h60,
              rw domain_axiom g hRelg at h60,
              cases h60 with y h61,
              rw h50 at h61,
              repeat {rw binary_union_axiom at h61},
              rw minus_members at h61,
              repeat {rw singleton1 at h61},
              cases h61 with h62 h63,
              {
                cases h62 with h64 h65,
                {
                  cases h64 with h66 h67,
                  have h68: t ∈ dom f:=
                    begin
                      rw domain_axiom f h21,
                      use y,
                      exact h66,
                    end,
                  have h69:= member_subset M (dom f) X t h23 h68,
                  rw binary_union_axiom,
                  left,
                  exact h69,
                },
                {
                  rw ordered_pair_equality at h65,
                  cases h65 with h66 h67,
                  rw h66 at *,
                  rw h67 at *,
                  rw binary_union_axiom,
                  left,
                  exact hb,
                }
              },
              {
                rw ordered_pair_equality at h63,
                cases h63 with h64 h65,
                rw h64 at *,
                rw h65 at *,
                rw binary_union_axiom,
                right,
                rw singleton1,
              }
            },
            {
              rw subset_definition,
              intros t h40,
              rw range_axiom g hRelg at h40,
              cases h40 with x h41,
              rw h50 at h41,
              repeat{rw binary_union_axiom at h41},
              rw minus_members at h41,
              repeat{rw singleton1 at h41},
              cases h41 with h42 h43,
              {
                cases h42 with h44 h45,
                {
                  cases h44 with h46 h47,
                  have h48: t ∈ range f:=
                    begin
                      rw range_axiom f h21,
                      use x,
                      exact h46,
                    end,
                  have h49:= member_subset M (range f) X t h24 h48,
                  rw binary_union_axiom,
                  left,
                  exact h49,
                },
                {
                  rw ordered_pair_equality at h45,
                  cases h45 with h46 h47,
                  rw h46 at *,
                  rw h47 at *,
                  rw binary_union_axiom,
                  right,
                  rw singleton1,
                }
              },
              {
                rw ordered_pair_equality at h43,
                cases h43 with h44 h45,
                rw h44 at *,
                rw h45 at *,
                rw binary_union_axiom,
                left,
                have h46: a ∈ range f:=
                  begin
                    rw range_axiom f h21,
                    use b,
                    exact h11,
                  end,
                have h47:= member_subset M (range f) X a h24 h46,
                exact h47,
              }
            }
          }
        },
        {
          unfold oneone,
          split,
          {
            unfold maps,
            split,
            {
              exact hRelg,
            },
            {
              split,
              {
                intros x y h60,
                cases h60 with h61 h62,
                rw h50 at h62,
                repeat{rw binary_union_axiom at h62},
                rw minus_members at h62,
                repeat{rw singleton1 at h62},
                cases h62 with h63 h64,
                {
                  cases h63 with h65 h66,
                  {
                    cases h65 with h67 h68,
                    have h69: y ∈ range f:=
                      begin
                        rw range_axiom f h21,
                        use x,
                        exact h67,
                      end,
                    have h70:= member_subset M (range f) X y h24 h69,
                    rw binary_union_axiom,
                    left,
                    exact h70,
                  },
                  {
                    rw ordered_pair_equality at h66,
                    cases h66 with h67 h68,
                    rw h67 at *,
                    rw h68 at *,
                    rw binary_union_axiom,
                    right,
                    rw singleton1,
                  }
                },
                {
                  rw ordered_pair_equality at h64,
                  cases h64 with h65 h66,
                  rw h65 at *,
                  rw h66 at *,
                  rw binary_union_axiom,
                  left,
                  have h68: a ∈ range f:=
                    begin
                      rw range_axiom f h21,
                      use b,
                      exact h11,
                    end,
                  have h69:= member_subset M (range f) X a h24 h68,
                  exact h69,
                }  
              },
              {
                split,
                {
                  intros x y z,
                  intros h,
                  rcases h with ⟨ h30, h31, h32⟩,
                  rw h50 at h31 h32,
                  repeat{rw binary_union_axiom at h31 h32},
                  rw minus_members at h31 h32,
                  repeat{rw singleton1 at h31 h32},
                  unfold oneone at h20,
                  rcases h20 with ⟨ h100, h101, h102⟩,
                  unfold maps at h100,
                  rcases h100 with ⟨ h103, h104, h105, h106⟩,
                  cases h32 with h33 h34,
                  {
                    cases h33 with h35 h36,
                    {
                      cases h35 with h37 h38,
                      cases h31 with h40 h41,
                      {
                        cases h40 with h42 h43,
                        {
                          cases h42 with h44 h45,
                          rw binary_union_axiom at h30,
                          cases h30 with h46 h47,
                          {
                            exact h105 x y z ⟨ h46, h44, h37⟩,
                          },
                          {
                            rw singleton1 at h47,
                            rw h47 at *,
                            have h48: c ∈ dom f:=
                              begin
                                rw domain_axiom f h21,
                                use z,
                                exact h37,
                              end,
                            have h49:= member_subset M (dom f) X c h23 h48,
                            contradiction,
                          }
                        },
                        {
                          rw ordered_pair_equality at h43,
                          cases h43 with h44 h45,
                          rw h44 at *,
                          rw h45 at *,
                          rw binary_union_axiom at h30,
                          cases h30 with h46 h47,
                          {
                            have h48:= h105 b a z ⟨ h46, h11, h37⟩, 
                            rw← h48 at *,
                            contradiction,
                          },
                          { 
                            rw singleton1 at h47,
                            rw h47 at *,
                            contradiction,
                          }
                        }
                      },
                      {
                        rw ordered_pair_equality at h41,
                        cases h41 with h42 h43,
                        rw h42 at *,
                        rw h43 at *,
                        have h44: c ∈ dom f:=
                          begin
                            rw domain_axiom f h21,
                            use z,
                            exact h37,
                          end,
                        have h45:= member_subset M (dom f) X c h23 h44,
                        contradiction,
                      }
                    },
                    {
                      rw ordered_pair_equality at h36,
                      cases h36 with h37 h38,
                      rw h37 at *,
                      rw h38 at *,
                      cases h31 with h32 h33,
                      {
                        cases h32 with h34 h35,
                        {
                          cases h34 with h60 h61,
                          have h62:= h105 b a y,
                          rw binary_union_axiom at h30,
                          cases h30 with h63 h64,
                          {
                            have h65:= h62 ⟨ h63, h11, h60⟩, 
                            rw← h65 at *,
                            contradiction,
                          },
                          {
                            rw singleton1 at h64,
                            rw h64 at *,
                            contradiction, 
                          }
                        },
                        {
                          rw ordered_pair_equality at h35,
                          cases h35 with h40 h41,
                          exact h41,
                        }
                      },
                      {
                        rw ordered_pair_equality at h33,
                        cases h33 with h40 h41,
                        rw h40 at *,
                        contradiction, 
                      }
                    }
                  },
                  {
                    rw ordered_pair_equality at h34,
                    cases h34 with h35 h36,
                    rw h35 at *,
                    rw h36 at *,
                    cases h31 with h40 h41,
                    {
                      cases h40 with h42 h43,
                      {
                        cases h42 with h44 h45,
                        have h46: c ∈ dom f:=
                          begin
                            rw domain_axiom f h21,
                            use y,
                            exact h44,
                          end,
                        have h47:= member_subset M (dom f) X c h23 h46,
                        contradiction,
                      },
                      {
                        rw ordered_pair_equality at h43,
                        cases h43 with h44 h45,
                        rw h44 at *,
                        rw h45 at *,
                        contradiction,
                      }
                    },
                    {
                      rw ordered_pair_equality at h41,
                      exact h41.right,
                    }
                  }
                },
                {
                  intros x h30,
                  rw binary_union_axiom at h30,
                  rw singleton1 at h30,
                  cases h30 with h31 h32,
                  {
                    have h200:= finitedecidable M X hfinite,
                    rw decidable_members at h200,
                    have h201:= h200 b x ⟨ hb, h31⟩,
                    cases h201 with h202 h203,
                    {
                      rw← h202 at *,
                      use c,
                      split,
                      { 
                        rw binary_union_axiom,
                        rw singleton1,
                        right,
                        simp,
                      },
                      {
                        rw h50,
                        repeat{rw binary_union_axiom},
                        rw minus_members,
                        repeat{rw singleton1},
                        simp,                           
                      }
                    },
                    {
                      unfold oneone at h20,
                      unfold maps at h20,
                      rcases h20 with ⟨ h80, h81, h82⟩,
                      rcases h80 with ⟨ h83, h84, h85, h86⟩, 
                      have h87:= h86 x h31,
                      cases h87 with y h88,
                      cases h88 with h89 h90,
                      use y,
                      split,
                      {
                        rw binary_union_axiom,
                        left,
                        exact h89,
                      },
                      {
                        rw h50,
                        repeat {rw binary_union_axiom},
                        rw minus_members,
                        repeat {rw singleton1},
                        left,
                        left,
                        split,
                        {
                          exact h90,
                        },
                        {
                          intro h91,
                          rw ordered_pair_equality at h91,
                          cases h91 with h92 h93,
                          rw sym at h92,
                          contradiction,
                        }
                      }
                    }
                  },
                  {
                    rw h32 at *,
                    use a,
                    split,
                    {
                      rw binary_union_axiom,
                      left,
                      exact ha,
                    },
                    {
                      rw h50,
                      repeat{rw binary_union_axiom},
                      rw minus_members,
                      repeat{rw singleton1},
                      right,
                      simp,
                    }
                  }
                }
              }
            }
          },
          {
            split,
            {
              intros x u y h,
              rcases h with ⟨ h30, h31, h32⟩,
              rw h50 at h30 h31,
              repeat {rw binary_union_axiom at h30 h31},
              rw minus_members at h30 h31,
              repeat{rw singleton1 at h30 h31},
              unfold oneone at h20,
              rcases h20 with ⟨ h80, h81, h82⟩,
              cases h30 with h33 h34,
              {
                cases h33 with h35 h36,
                {
                  cases h31 with h37 h38,
                  {
                    cases h37 with h39 h40,
                    {
                      rw binary_union_axiom at h32,
                      cases h32 with h41 h42,
                      {
                        exact h81 x u y ⟨ h35.left, h39.left, h41⟩, 
                      },
                      {
                        rw singleton1 at h42, 
                        rw h42 at *,
                        have h43: c ∈ dom f:=
                          begin
                            rw domain_axiom f h21,
                            use y,
                            exact h35.left,
                          end,
                        have h44:= member_subset M (dom f) X c h23 h43,
                        contradiction, 
                      }
                    },
                    {
                      rw ordered_pair_equality at h40,
                      cases h40 with h41 h42,
                      rw h41 at *,
                      rw h42 at *,
                      have h43: c ∈ range f:=
                        begin
                          rw range_axiom f h21,
                          use x,
                          exact h35.left,
                        end,
                      have h44:= member_subset M (range f) X c h24 h43,
                      contradiction, 
                    }
                  },
                  {
                    rw ordered_pair_equality at h38,
                    cases h38 with h39 h40,
                    rw h39 at *,
                    rw h40 at *,
                    have h41:= h81 x b a,
                    rw binary_union_axiom at h32,
                    cases h32 with h80 h81,
                    {
                      have h82:= h41 ⟨ h35.left, h11, h80⟩,
                      rw h82 at *,
                      cases h35 with h83 h85,
                      contradiction, 
                    },
                    {
                      rw singleton1 at h81,
                      exact h81,
                    }
                  }
                },
                {
                  rw ordered_pair_equality at h36,
                  cases h36 with h37 h38,
                  rw h37 at *,
                  rw h38 at *,
                  cases h31 with h39 h40,
                  {
                    cases h39 with h41 h42,
                    {
                      have h43: c ∈ range f:=
                        begin
                          rw range_axiom f h21,
                          use u,
                          exact h41.left, 
                        end,
                      have h44:= member_subset M (range f) X c h24 h43,
                      contradiction,
                    },
                    {
                      rw ordered_pair_equality at h42,
                      symmetry,
                      exact h42.left, 
                    }
                  },
                  {
                    rw ordered_pair_equality at h40,
                    cases h40 with h41 h42,
                    rw h41 at *,
                    rw h42 at *,
                    contradiction,
                  }
                }
              },
              {
                rw ordered_pair_equality at h34,
                cases h34 with h35 h36,
                rw h35 at *,
                rw h36 at *,
                rw binary_union_axiom at h32,
                cases h32 with h37 h38,
                {
                  contradiction,
                },
                {
                  rw singleton1 at h38,
                  rw h38 at *,
                  cases h31 with h40 h41,
                  {
                    cases h40 with h42 h43,
                    {
                      have h44: u ∈ dom f:=
                        begin
                          rw domain_axiom f h21,
                          use a,
                          exact h42.left,
                        end,
                      have h45:= member_subset M (dom f) X u h23 h44,
                      have h46:= h81 u b a ⟨ h42.left, h11, h45⟩,
                      rw h46 at *,
                      cases h42 with h47 h48,
                      contradiction,
                    },
                    {
                      rw ordered_pair_equality at h43,
                      cases h43 with h44 h45,
                      rw h44 at *,
                      rw h45 at *,
                      contradiction, 
                    }
                  },
                  {
                    rw ordered_pair_equality at h41,
                    symmetry,
                    exact h41.left,
                  }
                }
              }
            },
            {
              intros x y h90,
              cases h90 with h90 h91,
              rw h50 at h90,
              repeat {rw binary_union_axiom at h90},
              rw minus_members at h90,
              repeat{rw singleton1 at h90},
              cases h90 with h92 h93,
              {
                cases h92 with h94 h95,
                {
                  have h96: x ∈  dom f:=
                    begin
                      rw domain_axiom f h21,
                      use y,
                      exact h94.left,
                    end,
                  have h97:= member_subset M (dom f) X x h23 h96,
                  rw binary_union_axiom,
                  left,
                  exact h97,
                },
                {
                  rw ordered_pair_equality at h95,
                  cases h95 with h96 h97,
                  rw h96 at *,
                  rw h97 at *,
                  rw binary_union_axiom,
                  left,
                  exact hb, 
                }
              },
              { 
                rw ordered_pair_equality at h93,
                cases h93 with h94 h95,
                rw h94 at *,
                rw h95 at *,
                rw binary_union_axiom,
                right,
                rw singleton1, 
              }
            }
          }
        }
      }
    },
    {
      unfold onto,
      have h80:= finitedecidable M X hfinite,
      rw decidable_members at h80,
      intros y h30,
      rw binary_union_axiom at h30,
      cases h30 with h31 h32,
      {
        have h81:= h80 a y ⟨ ha, h31⟩, 
        cases h81 with h82 h83,
        {
          use c,
          rw←  h82 at *,
          split,
          {
            rw binary_union_axiom,
            right,
            rw singleton1,
          },
          {
            rw h50,
            repeat{rw binary_union_axiom},
            right,
            rw singleton1, 
          }
        },
        {
          have h84:= h8 y h31,
          cases h84 with x h85,
          cases h85 with h86 h87,
          use x,
          split,
          {
            rw binary_union_axiom,
            left,
            exact h86,
          },
          {
            rw h50,
            repeat{rw binary_union_axiom},
            rw minus_members,
            repeat{rw singleton1},
            left, left,
            split,
            {
              exact h87,
            },
            {
              intro h,
              rw ordered_pair_equality at h,
              cases h with h88 h89,
              rw h88 at *,
              rw h89 at *,
              contradiction,
            }
          }
        }
      },
      {
        rw singleton1 at h32,
        rw h32 at *,
        use b,
        split,
        {
          rw binary_union_axiom,
          left,
          exact hb,
        },
        {
          rw h50,
          repeat {rw binary_union_axiom},
          rw minus_members,
          repeat {rw singleton1},
          left,
          right,
          refl,
        }
      }
    }
  end

lemma precmax2: ℕℕ ∈ FINITE M → ∀ (k n:M), n ∈ ℕℕ → k ∈ STEM → ¬ k = n →  S k = S n → ∀(x:M), x ∈ ℕℕ → ¬ (n ≺ x):=
  assume hNfinite k n hn hstem  hkn hskn x hx h,
  begin
    have h3:= precmax M hNfinite k n hstem hn hkn hskn x hx,
    rw prec_definition at h,
    cases h with h4 h5,
    have h6:= prectrichotomy2 M hNfinite k n hstem hn hkn hskn x hx n hn h5,
    apply h6,
    exact ⟨ h4, h3⟩, 
  end

lemma precpred: ℕℕ ∈ FINITE M → ∀ (k n:M), n ∈ ℕℕ → k ∈ STEM → ¬ k = n →  S k = S n → ∀(x y:M), x ∈ ℕℕ → y ∈ ℕℕ → S x ≼ S y → ¬ x = n  → x ≼ y:=
  assume hNfinite k n hn hstem  hkn hskn x y hx hy h3 h4,
  begin
    have h80:= finitedecidable M ℕℕ hNfinite,
    rw decidable_members at h80,
    have h81:= h80 y n ⟨ hy, hn⟩,
    cases h81 with h82 h90,
    {
      rw h82 at *,
      have h84:= precmax M hNfinite k n hstem hn hkn hskn x hx,
      exact h84,
    },
    {
      have h5:= xpreceqsx M hNfinite k n hstem hn hkn hskn  x hx h4,
      have h6:= snneqn M x hx,
      have h7: x ≺  S x:=
        begin
          rw prec_definition,
          rw sym at h6,
          exact ⟨ h5, h6⟩, 
        end,
      have h8:= preceqsuccessor M hNfinite k n hstem hn hkn hskn x y hx hy h90,
      have h9:= preceqtrans M hNfinite k n hstem hn hkn hskn x (S x) (S y) h5 h3,
      rw h8 at h9,
      cases h9 with h10 h11,
      {
        exact h10,
      },
      {
        rw←  h11 at *,
        have h12:= prectrichotomy3 M hNfinite k n hstem hn hkn hskn x hx (S x) (successorN M x hx) ⟨ h3, h5⟩, 
        have h13:= snneqn M x hx,
        contradiction,   
      } 
    }  
  end

lemma formula62:  ∀ (k n q:M), k ∈ ℕℕ → n ∈ ℕℕ → ℕℕ ∈ FINITE M → S k = S n → ¬(k=n)→  k ∈ STEM → q ∈ ℕℕ → ¬ q = n → ¬ q = ChurchZero → ∀ (X f a b c g:M), X ∈ FINITE M → ¬ c ∈ X → ‹ b,a › ∈ f → ¬ (a=b) → g= (f - single ‹ b,a › ∪ single ‹ b,c › ∪ single ‹ c,a›) →  
cyclicperm M f X a → permorder M f X a q → ∀ (t:M),t ∈ ℕℕ → S t = q → ¬ t = n →  ∀ (z : M), z ∈ ℕℕ → z ≺ t → Ap (Ap z g) a = Ap (Ap z f) a ∧ ¬Ap (Ap z f) a = b:=
  assume k n q hk hn hNfinite hskn hkn hstem hq hqn hqz X f a b c g hfinite h3 h11 hab h50 h4 h5 t ht hst htn,
  begin
    intros z h30,
    unfold cyclicperm at h4,
    rcases h4 with ⟨ hpermf, ha, h7⟩,
    have h100:= orderstep1 M k n q hk hn hNfinite hskn hstem hq hqn hqz X f a b c g hfinite h3 h11 h50 hpermf,   
    have base: ChurchZero ∈ Z_orderstep M t g f a b:=
      begin
        rw Z_orderstep_members,
        split,
        {
          exact zeroN M,
        },
        {
          intro h3,
          rw ApZero, 
          rw ApId,
          rw ApZero,
          rw ApId,
          simp,
          exact hab,
        }
      end,
    have step: ∀ (r:M), r ∈ Z_orderstep M t g f a b → ¬ r = n → S r ∈ Z_orderstep M t g f a b :=
      begin
        intros r h10 hrn,
        rw Z_orderstep_members at h10,
        rw Z_orderstep_members,
        cases h10 with hr h41,
        split,
        {
          exact successorN M r hr,
        },
        {
          intro h44,
          unfold permutation at h100,
          cases h100 with h101 h102,
          unfold injection at h101,
          rcases h101 with ⟨ honeoneg, hRelg, hFUNCg, hdomg, hrangeg⟩,
          unfold oneone at honeoneg,
          rcases honeoneg with ⟨ hmapsg, h103, h104⟩,
          have h105: a ∈ X ∪ single c:=
            begin
              rw binary_union_axiom,
              left,
              exact ha,
            end,
          have h45:= successorequation M (X ∪ single c) g hFUNCg hRelg hmapsg r a hr h105,
          unfold permutation at hpermf,
          cases hpermf with h200 h201,
          unfold injection at h200,
          rcases h200 with ⟨ honeonef, hRelf, hFUNCf, hdomf, hrangef⟩,
          unfold oneone at honeonef,
          rcases honeonef with ⟨ hmapsf, h203,h204⟩,
          have h55:= successorequation M X f hFUNCf hRelf hmapsf r a hr ha,
          have h46:= xpreceqsx M hNfinite k n hstem hn hkn hskn r hr hrn,
          have h47: r ≺ S r:=
            begin
              rw prec_definition,
              split,
              {
                exact h46,
              },
              {
                have h47:= snneqn M r hr,
                rw sym,
                exact h47,
              }
            end,
          have h48:= prectrans M hNfinite k n hstem hn hkn hskn r (S r) t hr (successorN M r hr) ht h47 h44,
          have h49:= h41 h48,
          cases h49 with h51 h52,
          split,
          {
            rw h45,
            rw h55,
            rw h51,
            have h57:= Apdef M f hFUNCf,
            have h58:= Apdef M g hFUNCg,
            have h59:= xfmaps M X f a hFUNCf hRelf hmapsf ha r hr,
            unfold maps at hmapsf,
            rcases hmapsf with ⟨h60, h61, h62,h63⟩,
            have h64:= h63 (Ap (Ap r f) a) h59,
            cases h64 with y h65,
            cases h65 with hy h66,
            have h67:= h57 (Ap (Ap r f) a) y h66,
            rw← h67,
            have h69:= xfmaps M (X ∪ single c) g a hFUNCg hRelg hmapsg h105 r hr,
            unfold maps at hmapsg,
            rcases hmapsg with ⟨ h70,h71,h72,h73⟩,
            
            have h74:= h73 (Ap (Ap r g) a) h69,
            cases h74 with z h75,
            cases h75 with hz h76,
            have h77:= h58 (Ap (Ap r g) a) z h76,
            rw h51 at *,
            rw← h77,
            rw h50 at h76,
            repeat {rw binary_union_axiom at h76},
            rw minus_members at h76,
            repeat{rw singleton1 at h76},
            rw FUNC_members at hFUNCf,
            have h90:= hFUNCf (Ap (Ap r f) a) z y,
            cases h76 with h80 h81,
            {
              cases h80 with h82 h83,
              {
                cases h82 with h84 h85,
                exact h90 h84 h66,
              },
              {
                rw ordered_pair_equality at h83,
                cases h83 with h91 h92,
                contradiction,
              }
            },
            {
              rw ordered_pair_equality at h81,
              cases h81 with h91 h92,
              rw h91 at *,
              contradiction,
            }
          },
          {
            intro h,
            have h110: Ap f (Ap (Ap (S r) f) a) = Ap f b:=
              begin
                rw h,
              end,
            have h111:= Apdef M f hFUNCf b a h11,
            rw←  h111 at h110,
            have h112:= successorequation M X f hFUNCf hRelf hmapsf (S r) a (successorN M r hr) ha,
            rw← h112 at h110,
            have h113:  S (S r) ≼ q → q = S(S r):=
              begin
                intro h120,
                unfold permorder at h5,
                rcases h5 with ⟨ hq, h114, h115, h117⟩,
                have h121:= successoromitszero M (S r) (successorN M r hr),
                have h116:= h115 (S (S r)) (successorN M (S r)(successorN M r hr)) h120 h121 h110,
                symmetry,
                exact h116,
              end,
            have hsr := successorN M r hr,
            have hssr := successorN M (S r ) hsr,
            have h117: q ≼ S (S r):=
              begin
                have h120:= prectrichotomy1 M hNfinite k n hstem hn hkn hskn q (S (S r)) hq hssr,
                cases h120 with h121 h122,
                {
                  exact h121,
                },
                {
                  have h123:= h113 h122,
                  rw h123,
                  have h124:= preceqreflexive M hNfinite k n hstem hn hkn hskn (S (S r)) hssr,
                  exact h124,
                }
              end,
            rw← hst at h117,
            have h120:= precmax2 M hNfinite k n hn hstem hkn hskn t ht,
            have h121: ¬ S r = n:=
              begin
                intros h122,
                rw h122 at *,
                contradiction,
              end,
            have h122:= precpred M hNfinite k n hn hstem hkn hskn t (S r) ht (successorN M r hr) h117 htn,
            rw prec_definition at h44,
            cases h44 with h123 h124,
            have h125:= prectrichotomy3 M hNfinite k n hstem hn hkn hskn (S r) (successorN M r hr) t ht ⟨ h122, h123⟩, 
            rw sym at h125,
            contradiction,
          }
        }
      end,
    have h200: ∀ (z:M), z ∈ ℕℕ → z ∈ Z_orderstep M t g f a b:=
      begin
        intros z hz,
        have h202:= finiteinduction M hNfinite k n hstem hn hkn hskn (Z_orderstep M t g f a b) ⟨ base, step⟩, 
        have h201:= member_subset M ℕℕ  (Z_orderstep M t g f a b) z h202 hz, 
        exact h201,
      end,
    simp_rw Z_orderstep_members at h200,
    have h201:= h200 z h30,
    exact h201.right,
  end

lemma formula63:  ∀ (k n q:M), k ∈ ℕℕ → n ∈ ℕℕ → ℕℕ ∈ FINITE M → S k = S n → ¬(k=n)→  k ∈ STEM → q ∈ ℕℕ → ¬ q = n → ¬ q = ChurchZero → ∀ (X f a b c g:M), X ∈ FINITE M → ¬ c ∈ X → ‹ b,a › ∈ f → ¬ (a=b) → g= (f - single ‹ b,a › ∪ single ‹ b,c › ∪ single ‹ c,a›) →  
cyclicperm M f X a → permorder M f X a q → ∀ (t:M),t ∈ ℕℕ → S t = q → ¬ t = n →  Ap (Ap t f) a = Ap (Ap t g) a :=
  assume k n q hk hn hNfinite hskn hkn hstem hq hqn hqz X f a b c g hfinite h3 h11 hab h50 h4 h5 t ht hst htn,
  begin
    have h4copy:= h4,
    have h5copy:= h5,
    unfold cyclicperm at h4,
    rcases h4 with ⟨ hpermf, ha, h7⟩,
    set z := Ap (Ap t f) a with h219,
    have h220: Ap  f z = Ap f (Ap (Ap t f) a):=
      begin
        rw←  h219,
      end,
    have h100:= orderstep1 M k n q hk hn hNfinite hskn hstem hq hqn hqz X f a b c g hfinite h3 h11 h50 hpermf,   
    unfold permutation at hpermf,
    unfold injection at hpermf,
    cases hpermf with h300 h301,
    rcases h300 with ⟨honeonef,hRelf, hFUNCf, hdomf,hrangef⟩,
    unfold oneone at honeonef,
    rcases honeonef with ⟨ hmapsf, h302, h303⟩,
    unfold permutation at h100,
    cases h100 with h101 h102,
    unfold injection at h101,
    rcases h101 with ⟨ honeoneg, hRelg, hFUNCg, hdomg, hrangeg⟩,
    unfold oneone at honeoneg,
    rcases honeoneg with ⟨ hmapsg, h103, h104⟩,
    have h221:= successorequation M X f hFUNCf hRelf hmapsf t a ht ha,
    rw← h220 at h221,
    rw sym at h221,
    rw hst at h221,
    unfold permorder at h5,
    rcases h5 with ⟨ h201, h202, h203, h204⟩,
    rw h202 at h221,
    have hmapsf2:= hmapsf,
    unfold maps at hmapsf,
    rcases hmapsf with ⟨ h310, h311, h312, h313⟩,
    have h314:= xfmaps M X f a hFUNCf hRelf hmapsf2 ha t ht,
    have hz: z ∈ X:=
      begin
        rw h219,
        exact h314,
      end,
    have h223: ‹ z, Ap f z› ∈ f:=
      begin
        have h224:= h313 z hz,
        cases h224 with u h226,
        cases h226 with hu h227,
        have h228:= Apdef M f hFUNCf z u h227,
        rw← h228 at *,
        exact h227,
      end,
    rw  h221 at h223,
    have h224:= h302 z b a ⟨ h223, h11, hz⟩,
    have h225: ¬ t = ChurchZero:=
      begin
        intro h,
        rw h at *,
        rw ApZero at h219,
        rw ApId at h219,
        rw sym at h219,
        rw← h219 at *,
        contradiction,
      end,
    have h226:= predecessornotn M hNfinite k n hstem hn hkn hskn t ht h225,
    cases h226 with p h227,
    rcases h227 with ⟨ hp , h228, hpn⟩,
    have h229: p ≺ t:=
      begin
        have h230:= xpreceqsx M hNfinite k n hstem hn hkn hskn p hp hpn,
        rw h228 at *,
        rw prec_definition,
        split,
        {
          exact h230,
        },
        {
          intro h,
          rw h at h228,
          have h229:= snneqn M t ht,
          contradiction,
        }
      end,
    have h2000 := formula62 M k n q hk hn hNfinite  hskn hkn hstem hq hqn hqz X f a b c g hfinite h3 h11 hab h50 h4copy h5copy t ht hst htn,
    have h403: a ∈ X ∪ (single c):=
      begin
        rw binary_union_axiom,
        left,
        exact ha,
      end,
    set u:= Ap (Ap p f) a with h750,
    have h230: u = Ap (Ap p g) a:=
      begin
        have h233:= h2000 p hp,
        have h234:= h233 h229,
        cases h234 with h235 h236,
        rw h235, 
      end,
    have h231: Ap g u = Ap (Ap t g) a:=
      begin
        rw← h228,
        have h232:= successorequation M (X ∪ single c) g hFUNCg hRelg hmapsg p a hp h403,
        rw h232,
        rw h230,
      end,
    have h232: Ap f u = b:=
      begin
        rw← h224,
        rw h219,
        rw← h228,
        have h229:= successorequation M X f hFUNCf hRelf hmapsf2 p a hp ha,
        rw h229,
      end,
    rw h224 at h221,
    have h240:= hab,
    rw←  h232 at h240,
    rw← h221 at h240,
    have h242: ¬ u = b:=
      begin
        intro h,
        rw h at h240,
        contradiction,
      end,
    have hu: u ∈ X:=
      begin
        rw h750,
        have h250:= xfmaps M X f a hFUNCf hRelf hmapsf2 ha p hp,
        exact h250,
      end,
    have h245: ‹u, Ap f u › ∈ f:=
      begin
        have h246:= h313 u hu,
        cases h246 with y h247,
        cases h247 with hy h248,
        have h249:= Apdef M f hFUNCf u y h248,
        rw h249 at h248,
        exact h248,
      end,
    have h246: ‹ u, Ap f u › ∈ g:=
      begin
        rw h50,
        repeat {rw binary_union_axiom},
        rw minus_members,
        repeat {rw singleton1},
        left,left,
        split,
        {
          exact h245,
        },
        {
          intro h,
          rw ordered_pair_equality at h,
          cases h with h250 h251,
          rw h250 at *,
          rw h251 at *,
          contradiction,
        }
      end,
    rw h232 at h246,
    have h247:= Apdef M g hFUNCg u b h246,
    rw← h231,
    rw← h247,
    exact h224,
  end

lemma formula64:  ∀ (k n q:M), k ∈ ℕℕ → n ∈ ℕℕ → ℕℕ ∈ FINITE M → S k = S n → ¬(k=n)→  k ∈ STEM → q ∈ ℕℕ → ¬ q = n → ¬ q = ChurchZero → ∀ (X f a b c g:M), X ∈ FINITE M → ¬ c ∈ X → ‹ b,a › ∈ f → ¬ (a=b) → g= (f - single ‹ b,a › ∪ single ‹ b,c › ∪ single ‹ c,a›) →  
cyclicperm M f X a → permorder M f X a q → ∀ (t:M),t ∈ ℕℕ → S t = q → ¬ t = n →  Ap (Ap q g) a = c:=
  assume k n q hk hn hNfinite hskn hkn hstem hq hqn hqz X f a b c g hfinite h3 h11 hab h50 h4 h5 t ht hst htn,
  begin
    have h4copy:= h4,
    have h5copy:= h5,
    unfold cyclicperm at h4,
    rcases h4 with ⟨ hpermf, ha, h7⟩,
    set z := Ap (Ap t f) a with h219,
    have h220: Ap  f z = Ap f (Ap (Ap t f) a):=
      begin
        rw←  h219,
      end,
    have h100:= orderstep1 M k n q hk hn hNfinite hskn hstem hq hqn hqz X f a b c g hfinite h3 h11 h50 hpermf,   
    unfold permutation at hpermf,
    unfold injection at hpermf,
    cases hpermf with h300 h301,
    rcases h300 with ⟨honeonef,hRelf, hFUNCf, hdomf,hrangef⟩,
    unfold oneone at honeonef,
    rcases honeonef with ⟨ hmapsf, h302, h303⟩,
    unfold permutation at h100,
    cases h100 with h101 h102,
    unfold injection at h101,
    rcases h101 with ⟨ honeoneg, hRelg, hFUNCg, hdomg, hrangeg⟩,
    unfold oneone at honeoneg,
    rcases honeoneg with ⟨ hmapsg, h103, h104⟩,
    have h221:= successorequation M X f hFUNCf hRelf hmapsf t a ht ha,
    rw← h220 at h221,
    rw sym at h221,
    rw hst at h221,
    unfold permorder at h5,
    rcases h5 with ⟨ h201, h202, h203, h204⟩,
    rw h202 at h221,
    have hmapsf2:= hmapsf,
    unfold maps at hmapsf,
    rcases hmapsf with ⟨ h310, h311, h312, h313⟩,
    have h314:= xfmaps M X f a hFUNCf hRelf hmapsf2 ha t ht,
    have hz: z ∈ X:=
      begin
        rw h219,
        exact h314,
      end,
    have h223: ‹ z, Ap f z› ∈ f:=
      begin
        have h224:= h313 z hz,
        cases h224 with u h226,
        cases h226 with hu h227,
        have h228:= Apdef M f hFUNCf z u h227,
        rw← h228 at *,
        exact h227,
      end,
    rw  h221 at h223,
    have h224:= h302 z b a ⟨ h223, h11, hz⟩,
    have h225: ¬ t = ChurchZero:=
      begin
        intro h,
        rw h at *,
        rw ApZero at h219,
        rw ApId at h219,
        rw sym at h219,
        rw← h219 at *,
        contradiction,
      end,
    have h226:= predecessornotn M hNfinite k n hstem hn hkn hskn t ht h225,
    cases h226 with p h227,
    rcases h227 with ⟨ hp , h228, hpn⟩,
    have h229: p ≺ t:=
      begin
        have h230:= xpreceqsx M hNfinite k n hstem hn hkn hskn p hp hpn,
        rw h228 at *,
        rw prec_definition,
        split,
        {
          exact h230,
        },
        {
          intro h,
          rw h at h228,
          have h229:= snneqn M t ht,
          contradiction,
        }
      end,
    have h2000 := formula62 M k n q hk hn hNfinite  hskn hkn hstem hq hqn hqz X f a b c g hfinite h3 h11 hab h50 h4copy h5copy t ht hst htn,
    have h403: a ∈ X ∪ (single c):=
      begin
        rw binary_union_axiom,
        left,
        exact ha,
      end,
    have line63:= formula63 M k n q hk hn hNfinite  hskn hkn hstem hq hqn hqz X f a b c g hfinite h3 h11 hab h50 h4copy h5copy t ht hst htn,
    rw← hst,
    have h500:t ≼ q:=
      begin
        rw← hst,
        have h501:= xpreceqsx M hNfinite k n hstem hn hkn hskn t ht htn,
        exact h501,
      end,
    have h502:= successorequation M X f hFUNCf hRelf hmapsf2 t a ht ha,
    rw hst at h502,
    rw h202 at h502,
    rw sym at h502,
    have h499:= xfmaps M X f a hFUNCf hRelf hmapsf2 ha t ht,
    have hb:b ∈ X:=
      begin
        have h520: b ∈ dom f:=
          begin
            rw domain_axiom f hRelf,
            use a,
            exact h11,
          end,
        exact member_subset M (dom f) X b hdomf h520, 
      end,
    unfold maps at hmapsf2,
    rcases hmapsf2 with ⟨ hRelf, h504, h505,h506⟩ ,
    have h507:= h506 (Ap (Ap t f)a) h499,
    cases h507 with y h508,
    cases h508 with hy h509,
    have h510:= Apdef M f hFUNCf (Ap (Ap t f) a) y h509,
    rw h502 at h510,
    rw h510 at h509,
    have h511:= h302 b (Ap (Ap t f)a) a ⟨ h11, h509, hb⟩,
    rw line63 at h511,
    have h512: ‹ b, c › ∈ g:=
      begin
        rw h50,
        repeat {rw binary_union_axiom},
        rw minus_members,
        repeat {rw singleton1},
        left,
        right,
        refl,
      end,
    have h513:= Apdef M g hFUNCg b c h512, 
    rw h511 at h513,
    have h514:= successorequation M (X ∪ single c) g hFUNCg hRelg hmapsg t a ht h403,
    rw← h514 at h513,
    symmetry,
    exact h513,
  end

lemma tfa:  ∀ (k n q:M), k ∈ ℕℕ → n ∈ ℕℕ → ℕℕ ∈ FINITE M → S k = S n → ¬(k=n)→  k ∈ STEM → q ∈ ℕℕ → ¬ q = n → ¬ q = ChurchZero → ∀ (X f a b c g:M), X ∈ FINITE M → ¬ c ∈ X → ‹ b,a › ∈ f → ¬ (a=b) → g= (f - single ‹ b,a › ∪ single ‹ b,c › ∪ single ‹ c,a›) →  
cyclicperm M f X a → permorder M f X a q → ∀ (t:M),t ∈ ℕℕ → S t = q → ¬ t = n →  Ap (Ap t f) a = b:=
  assume k n q hk hn hNfinite hskn hkn hstem hq hqn hqz X f a b c g hfinite h3 h11 hab h50 h4 h5 t ht hst htn,
  begin
    have h4copy:= h4,
    have h5copy:= h5,
    unfold cyclicperm at h4,
    rcases h4 with ⟨ hpermf, ha, h7⟩,
    set z := Ap (Ap t f) a with h219,
    have h220: Ap  f z = Ap f (Ap (Ap t f) a):=
      begin
        rw←  h219,
      end,
    have h100:= orderstep1 M k n q hk hn hNfinite hskn hstem hq hqn hqz X f a b c g hfinite h3 h11 h50 hpermf,   
    unfold permutation at hpermf,
    unfold injection at hpermf,
    cases hpermf with h300 h301,
    rcases h300 with ⟨honeonef,hRelf, hFUNCf, hdomf,hrangef⟩,
    unfold oneone at honeonef,
    rcases honeonef with ⟨ hmapsf, h302, h303⟩,
    unfold permutation at h100,
    cases h100 with h101 h102,
    unfold injection at h101,
    rcases h101 with ⟨ honeoneg, hRelg, hFUNCg, hdomg, hrangeg⟩,
    unfold oneone at honeoneg,
    rcases honeoneg with ⟨ hmapsg, h103, h104⟩,
    have h221:= successorequation M X f hFUNCf hRelf hmapsf t a ht ha,
    rw← h220 at h221,
    rw sym at h221,
    rw hst at h221,
    unfold permorder at h5,
    rcases h5 with ⟨ h201, h202, h203, h204⟩,
    rw h202 at h221,
    have hmapsf2:= hmapsf,
    unfold maps at hmapsf,
    rcases hmapsf with ⟨ h310, h311, h312, h313⟩,
    have h314:= xfmaps M X f a hFUNCf hRelf hmapsf2 ha t ht,
    have hz: z ∈ X:=
      begin
        rw h219,
        exact h314,
      end,
    have h223: ‹ z, Ap f z› ∈ f:=
      begin
        have h224:= h313 z hz,
        cases h224 with u h226,
        cases h226 with hu h227,
        have h228:= Apdef M f hFUNCf z u h227,
        rw← h228 at *,
        exact h227,
      end,
    rw  h221 at h223,
    have h224:= h302 z b a ⟨ h223, h11, hz⟩,
    exact h224,
  end


lemma orderstep2: ∀ (k n q:M), k ∈ ℕℕ → n ∈ ℕℕ → ℕℕ ∈ FINITE M → S k = S n → ¬(k=n)→  k ∈ STEM → q ∈ ℕℕ → ¬ q = n → ¬ q = ChurchZero → ∀ (X f a b c g:M), X ∈ FINITE M → ¬ c ∈ X → ‹ b,a › ∈ f → ¬ (a=b) → g= (f - single ‹ b,a › ∪ single ‹ b,c › ∪ single ‹ c,a›) →  
cyclicperm M f X a → permorder M f X a q →  cyclicperm M g (X ∪ single c) a :=
  assume k n q hk hn hNfinite hskn hkn hstem hq hqn hqz X f a b c g hfinite h3 h11 hab h50 h4 h5,
  begin
    have h31:= predecessornotn M hNfinite k n hstem hn hkn hskn q hq hqz,
    cases h31 with t h32,
    rcases h32 with ⟨ ht, hst, htn⟩,
    have h4copy:= h4,
    have h5copy:= h5,
    unfold cyclicperm at h4,
    rcases h4 with ⟨ hpermf, ha, h7⟩,
    have h100:= orderstep1 M k n q hk hn hNfinite hskn hstem hq hqn hqz X f a b c g hfinite h3 h11 h50 hpermf,   
    unfold cyclicperm,
    split,
    {
      exact h100,
    },
    {
      split,
      {
        rw binary_union_axiom,
        left,
        exact ha,
      },
      {          
        intros z h30,
        -- h2000 is formula (62) from the paper
        have h2000 := formula62 M k n q hk hn hNfinite  hskn hkn hstem hq hqn hqz X f a b c g hfinite h3 h11 hab h50 h4copy h5 t ht hst htn,
        unfold permorder at h5,
        rcases h5 with ⟨ h201, h202, h203, h204⟩,
        have h30copy:= h30,
        rw binary_union_axiom at h30,
        rw singleton1 at h30,
        have h400:= finite_adjoin M X c ⟨hfinite, h3⟩,
        have h401:= finitedecidable M (X ∪ single c) h400,
        rw decidable_members at h401,
        have h403: a ∈ X ∪ (single c):=
          begin
            rw binary_union_axiom,
            left,
            exact ha,
          end,
        have h402:= h401 z a ⟨ h30copy, h403⟩,
        have line63 := formula63 M k n q hk hn hNfinite hskn hkn hstem hq hqn hqz X f a b c g hfinite h3 h11 hab h50 h4copy h5copy t ht hst htn,
        cases h402 with h403 h404,
        {
          use ChurchZero,
          rw h403 at *,
          split,
          {
            exact zeroN M,
          },
          {
            rw ApZero,
            rw ApId,
          }
        },
        { 
          unfold permutation at hpermf,
          unfold injection at hpermf,
          cases hpermf with h300 h301,
          rcases h300 with ⟨honeonef,hRelf, hFUNCf, hdomf,hrangef⟩,
          unfold oneone at honeonef,
          rcases honeonef with ⟨ hmapsf, h302, h303⟩,
          unfold permutation at h100,
          cases h100 with h101 h102,
          unfold injection at h101,
          rcases h101 with ⟨ honeoneg, hRelg, hFUNCg, hdomg, hrangeg⟩,
          unfold oneone at honeoneg,
          rcases honeoneg with ⟨ hmapsg, h103, h104⟩,   
          cases h30 with h205 h206,
          { -- Case 1, z ∈ X
            have h207:= h204 z h205,
            cases h207 with r h208,
            rcases h208 with ⟨ hr, h210, h211⟩,
            use r,
            have h213:= h2000 r hr,
            have h214:= prectrichotomystrict M hNfinite k n hn hstem hkn hskn r t hr ht,
            have h300: r = t → t ∈ ℕℕ ∧ z = Ap (Ap r g) a:=
              begin
                intro h217,
                rw h217 at *,
                have h219: z = Ap (Ap t f) a:=
                  begin
                    rw sym at h211,
                    exact h211,
                  end,
                have h220: Ap  f z = Ap f (Ap (Ap t f) a):=
                  begin
                    rw←  h219,
                  end,
                have h221:= successorequation M X f hFUNCf hRelf hmapsf t a hr ha,
                rw← h220 at h221,
                rw sym at h221,
                rw hst at h221,
                rw h202 at h221,
                have hmapsf2:= hmapsf,
                unfold maps at hmapsf,
                rcases hmapsf with ⟨ h310, h311, h312, h313⟩,
                have h223: ‹ z, Ap f z› ∈ f:=
                  begin
                    have h224:= h313 z h205,
                    cases h224 with u h226,
                    cases h226 with hu h227,
                    have h228:= Apdef M f hFUNCf z u h227,
                    rw← h228 at *,
                    exact h227,
                  end,
                rw  h221 at h223,
                have h224:= h302 z b a ⟨ h223, h11, h205⟩,
                have h225: ¬ t = ChurchZero:=
                  begin
                    intro h,
                    rw h at *,
                    rw ApZero at h211,
                    rw ApId at h211,
                    rw sym at h211,
                    contradiction,
                  end,
                have h226:= predecessornotn M hNfinite k n hstem hn hkn hskn t ht h225,
                cases h226 with p h227,
                rcases h227 with ⟨ hp , h228, hpn⟩,
                have h229: p ≺ t:=
                  begin
                    have h230:= xpreceqsx M hNfinite k n hstem hn hkn hskn p hp hpn,
                    rw h228 at *,
                    rw prec_definition,
                    split,
                    {
                      exact h230,
                    },
                    {
                      intro h,
                      rw h at h228,
                      have h229:= snneqn M t ht,
                      contradiction,
                    }
                  end,
                set u:= Ap (Ap p f) a with h750,
                have h230: u = Ap (Ap p g) a:=
                  begin
                    have h233:= h2000 p hp,
                    have h234:= h233 h229,
                    cases h234 with h235 h236,
                    rw h235, 
                  end,
                have h231: Ap g u = Ap (Ap t g) a:=
                  begin
                    rw← h228,
                    have h232:= successorequation M (X ∪ single c) g hFUNCg hRelg hmapsg p a hp h403,
                    rw h232,
                    rw h230,
                  end,
                have h232: Ap f u = b:=
                  begin
                    rw← h224,
                    rw h219,
                    rw← h228,
                    have h229:= successorequation M X f hFUNCf hRelf hmapsf2 p a hp ha,
                    rw h229,
                  end,
                rw h224 at h221,
                have h240:= hab,
                rw←  h232 at h240,
                rw← h221 at h240,
                have h242: ¬ u = b:=
                  begin
                    intro h,
                    rw h at h240,
                    contradiction,
                  end,
                have hu: u ∈ X:=
                  begin
                    rw h750,
                    have h250:= xfmaps M X f a hFUNCf hRelf hmapsf2 ha p hp,
                    exact h250,
                  end,
                have h245: ‹u, Ap f u › ∈ f:=
                  begin
                    have h246:= h313 u hu,
                    cases h246 with y h247,
                    cases h247 with hy h248,
                    have h249:= Apdef M f hFUNCf u y h248,
                    rw h249 at h248,
                    exact h248,
                  end,
                have h246: ‹ u, Ap f u › ∈ g:=
                  begin
                    rw h50,
                    repeat {rw binary_union_axiom},
                    rw minus_members,
                    repeat {rw singleton1},
                    left,left,
                    split,
                    {
                      exact h245,
                    },
                    {
                      intro h,
                      rw ordered_pair_equality at h,
                      cases h with h250 h251,
                      rw h250 at *,
                      rw h251 at *,
                      contradiction,
                    }
                  end,
                rw h232 at h246,
                have h247:= Apdef M g hFUNCg u b h246,
                have h248: z = Ap (Ap r g) a:=
                  begin
                    rw h217,
                    rw← h231,
                    rw←  h247,
                    exact h224,
                  end,
                rw h217 at h248,
                exact ⟨ ht, h248⟩,
              end,
            cases h214 with h215 h216,
            {
              -- Case 1A, r ≺ t
              have h219:= h2000 r hr,
              have h220:= h219 h215,
              cases h220 with h221 h222,
              have h223: z = Ap (Ap r g) a:=
                begin
                  rw← h211,
                  symmetry,
                  exact h221,
                end,
              exact ⟨ hr, h223⟩,
            },
            { 
              cases h216 with h217 h218,
              {  -- case 1B, r=t
                have h301:= h300 h217,
                rw h217 at h301,
                split,
                {
                  exact hr,
                },
                {
                  have h301copy:= h301,
                  cases h301copy with ht2 h303,
                  rw h217,
                  exact h303,
                }
              },
              {  -- Case 1C, t ≺ r 
                rw← hst at h210,
                have h230:= preceqsuccessor M hNfinite k n hstem hn hkn hskn r t hr ht htn,
                rw h230 at h210,
                cases h210 with h231 h232,
                { 
                  rw prec_definition at h218,
                  cases h218 with h233 h234, 
                  have h235:= prectrichotomy3 M hNfinite k n hstem hn hkn hskn r hr t ht ⟨ h233, h231⟩,
                  contradiction,
                },
                { 
                  rw hst at h232,
                  rw←  h232 at *, 
                  split,
                  {
                    exact hq,
                  },
                  {
                    rw← h211,
                    rw← h202 at h404,
                    rw← h211 at h404,
                    contradiction, 
                  }
                }
              }
            } 
          },
          {  
            --case 2, z = c
            use q,
            rw h206 at *,
            split,
            { 
              exact h201,
            },
            { 
              have line64:= formula64 M k n q hk hn hNfinite  hskn hkn hstem hq hqn hqz X f a b c g hfinite h3 h11 hab h50 h4copy h5copy t ht hst htn,
              symmetry,
              exact line64,
            }
          }
        }  
      }
    } 
  end

lemma orderstep3: ∀ (k n q:M), k ∈ ℕℕ → n ∈ ℕℕ → ℕℕ ∈ FINITE M → S k = S n → ¬(k=n)→  k ∈ STEM → q ∈ ℕℕ → ¬ q = n → ¬ q = ChurchZero → ∀ (X f a b c g:M), X ∈ FINITE M → ¬ c ∈ X → ‹ b,a › ∈ f → ¬ (a=b) → g= (f - single ‹ b,a › ∪ single ‹ b,c › ∪ single ‹ c,a›) →  
cyclicperm M f X a → permorder M f X a q  →  permorder M g (X ∪ single c) a (S q) :=
  assume k n q hk hn hNfinite hskn hkn hstem hq hqn hqz X f a b c g hfinite h3 h11 hab h50 h4 h5,
  begin
    have h5copy:= h5,
    unfold permorder at h5,
    unfold permorder,
    have h4copy:= h4,
    unfold cyclicperm at h4,
    rcases h5 with ⟨ hq, hqfa, h6, h7⟩,
    have h31:= predecessornotn M hNfinite k n hstem hn hkn hskn q hq hqz,
    cases h31 with t h32,
    rcases h32 with ⟨ ht, hst, htn⟩,
    have line62:= formula62 M k n q hk hn hNfinite hskn hkn hstem hq hqn hqz X f a b c g hfinite h3 h11 hab h50 h4copy h5copy t ht hst htn,
    have line63:= formula63 M k n q hk hn hNfinite hskn hkn hstem hq hqn hqz X f a b c g hfinite h3 h11 hab h50 h4copy h5copy t ht hst htn,
    have htfa:=  tfa M k n q hk hn hNfinite hskn hkn hstem hq hqn hqz X f a b c g hfinite h3 h11 hab h50 h4copy h5copy t ht hst htn,    
    have h70:= orderstep1 M k n q hk hn hNfinite hskn hstem hq hqn hqz X f a b c g hfinite h3 h11 h50 h4.left,
    unfold permutation at h70,
    cases h70 with h71 h72,
    unfold injection at h71,
    rcases h71 with ⟨ honeoneg, hRelg, hFUNCg,  hdomg,hrangeg⟩,
    unfold oneone at honeoneg,
    rcases honeoneg with ⟨ hmapsg, h73, h74⟩,
    rcases h4 with ⟨ hpermf, ha, h75⟩,
    have line64:= formula64 M k n q hk hn hNfinite hskn hkn hstem hq hqn hqz X f a b c g hfinite h3 h11 hab h50 h4copy h5copy t ht hst htn, 
    have h403: a ∈ X ∪ (single c):=
    begin
      rw binary_union_axiom,
      left,
      exact ha,
    end,
    have h65:= successorequation M (X ∪ single c) g hFUNCg hRelg hmapsg q a hq h403,
    rw h65,
    rw line64,
    have h76: ‹ c,a › ∈ g:=
      begin
        rw h50,
        rw binary_union_axiom,
        right,
        rw singleton1, 
      end,
    have h77:= Apdef M g hFUNCg c a h76,
    split,
    {
      exact successorN M q hq,
    },
    {
      split,
      {
        symmetry,
        exact h77,
      },
      {
        split,
        {
          intros r hr htsq htz htga,
          have h83:= preceqsuccessor M hNfinite k n hstem hn hkn hskn r q hr hq hqn,
          rw h83 at htsq,
          rw or_comm at htsq,
          cases htsq with h84 h85,
          { 
            exact h84,
          },
          {
            rw← hst at h85,
            have h86:= preceqsuccessor M hNfinite k n hstem hn hkn hskn r t hr ht htn,
            rw h86 at h85,
            have h90: ¬ r = t:=
              begin
                have h91:= line63,
                intro h,
                have h92:= htfa,
                rw←  h at h91 h92,
                rw htga at h91,
                rw h91 at h92,
                contradiction,
              end,
            cases h85 with h87 h88,
            {
              have h93: r ≺ t:=
                begin
                  rw prec_definition,
                  exact ⟨ h87,h90⟩,
                end,
              have h94:= line62 r hr h93,
              cases h94 with h95 h96,
              rw h95 at htga,
              have h196:r ≼ q:=
                begin
                  rw← hst,
                  rw h86,
                  left,
                  exact h87,
                end, 
              have h97:= h6 r hr h196 htz htga,
              rw← h97 at line64,
              rw h95 at line64,
              rw htga at line64,
              rw line64 at *,
              contradiction, 
            },
            {
              have h95: ¬ r = q:=
                begin
                  intro h,
                  rw h at htga,
                  rw htga at line64,
                  rw line64 at *,
                  contradiction,
                end,  
              rw hst at h88,
              contradiction,
            }
          }
        },
        {
          intros x h,
          rw binary_union_axiom at h,
          cases h with hx h101,
          { 
            have h102:= h7 x hx,
            cases h102 with r h103,
            rcases h103 with ⟨ hr, h104, h105⟩,
            have h80:= finitedecidable M X hfinite,
            rw decidable_members at h80,
            have h81:= h80 x a ⟨ hx, ha⟩, 
            cases h81 with h82 h83,
            { 
              use (S q),
              split,
              {
                exact successorN M q hq,
              },
              {
                split,
                {
                  have h200:= preceqreflexive M hNfinite k n hstem hn hkn hskn (S q) (successorN M q hq),
                  exact h200,
                },
                {
                  rw h82,
                  rw h65,
                  rw line64,
                  have h83:= Apdef M g hFUNCg c a h76,
                  rw h83,                
                }
              }
            },
            { 
              -- we need hRelf, but it's hard to find
              unfold permutation at hpermf,
              unfold injection at hpermf,
              cases hpermf with h83 h84,
              rcases h83 with ⟨ honeonef, hRelf, hFUNCf, hdomf,hrangef⟩,
              have hb:b ∈ X:=
                begin
                  have h200: b ∈ dom f:=
                    begin
                      rw domain_axiom f hRelf,
                      use a,
                      exact h11,
                    end,
                  exact member_subset M (dom f) X b hdomf h200,
                end,
              have h85:= h80 x b ⟨ hx, hb⟩, 
              cases h85 with h86 h87,
              { 
                rw h86 at *,
                use t,
                split,
                {
                  exact ht,
                },
                {
                  rw← line63,
                  rw htfa,
                  simp,
                  rw← hst,
                  have h88:= xpreceqsx M hNfinite k n hstem hn hkn hskn t ht htn,
                  have h89: ¬ S t = n:=
                    begin
                      rw hst,
                      exact hqn,
                    end,
                  have h90:= xpreceqsx M hNfinite k n hstem hn hkn hskn (S t) (successorN M t ht) h89,
                  have h91:= preceqtrans M hNfinite k n hstem hn hkn hskn t (S t) (S (S t)) h88 h90,
                  exact h91,
                }
              },
              {  
                -- Case 4 in the paper
                rw← hst at h104,
                have h1105:= preceqsuccessor M hNfinite k n hstem hn hkn hskn r t hr ht htn,
                rw h1105 at h104,
                have h180:= finitedecidable M ℕℕ hNfinite,
                rw decidable_members at h180,
                have h109:= h180 r t ⟨ hr, ht⟩,
                cases h104 with h106 h107,
                {
                  have h108: r ≺ t ∨ r = t:=
                    begin
                      rw prec_definition,
                      cases h109 with h110 h111,
                      {
                        right,
                        exact h110,
                      },
                      {
                        left,
                        exact ⟨ h106, h111⟩,
                      }
                    end,
                  have h115: t ≼ S t:= xpreceqsx M hNfinite k n hstem hn hkn hskn t ht htn,
                  have h116: ¬ S t = n :=
                    begin
                      rw hst,
                      exact hqn,
                    end,
                  have h117:= xpreceqsx M hNfinite k n hstem hn hkn hskn (S t) (successorN M t ht) h116,
                  have h118:= preceqtrans M hNfinite k n hstem hn hkn hskn t (S t) (S (S t)) h115 h117,
                  have h119:=  preceqtrans M hNfinite k n hstem hn hkn hskn r t (S (S t)) h106 h118,
                  cases h108 with h109 h110,
                  { 
                    use r,
                    have h112:= line62 r hr h109,
                    cases h112 with h113 h114,
                    rw h113,
                    split,
                    {
                      exact hr,
                    },
                    {
                      split,
                      {
                        rw← hst,
                        exact h119,
                      },
                      {
                        exact h105,
                      }
                    }
                  },
                  { 
                    rw h110 at *,
                    have h111: x= b:=
                      begin
                        rw← h105,
                        rw← htfa,
                      end,
                    contradiction,
                  }
                },
                { 
                  rw hst at h107,
                  rw h107 at *,
                  rw hqfa at h105,
                  rw← h105,
                  rw sym at h105,
                  contradiction, 
                }
              }  
            }
          },
          {
            rw singleton1 at h101,
            rw h101 at *,
            use q,
            rw line64,
            simp,
            split,
            {
              exact hq,
            },
            {
              have h200:= xpreceqsx M hNfinite k n hstem hn hkn hskn q hq hqn,
              exact h200,
            }
          }
        }
      }
    }
  end

lemma nneqone: ∀ (k n:M), k ∈ ℕℕ → n ∈ ℕℕ → ℕℕ ∈ FINITE M → S k = S n → ¬(k=n)→  k ∈ STEM →  ¬ n = S ChurchZero:=
  assume k n hk hn hNfinite hskn hkn hstem hnzero,
  begin
    have h2:= nneqzero M k n hstem hn hkn hskn,
    have h3:= successorN M n hn,
    have h4:= precmax M hNfinite k n hstem hn hkn hskn (S n) h3,
    have h6:= snneqn M n hn,
    have h7:= preceqsuccessor M hNfinite k n hstem hn hkn hskn n (S n) hn (successorN M n hn) h6,
    have h8:= ssnneqn M n hn,
    have h9:= L1 M k n hstem hn hkn hskn,
    cases h9 with h10 h11,
    have h12:= LcapS M k n hstem hn hkn hskn,
    rw full_extensionality at h12,
    specialize h12 n,
    rw  intersection_axiom at h12,
    have h13:= emptyset_axiom n,
    have h14: ¬ n ∈ STEM:=
      begin
        intro h,
        exact h13 (h12.mp ⟨ h10, h⟩ ),
      end,
    rw hnzero at h14,
    have h15:= looponto M k n hstem hn hkn hskn n h10,
    cases h15 with r h16,
    cases h16 with hr hsr,
    have h7: ¬ r = ChurchZero:=
      begin
        intro h,
        rw h at *,
        have h17:= S1 M,
        cases h17 with h18 h19,
        have h21:= LcapS M k n hstem hn hkn hskn,
        rw full_extensionality at h21,
        specialize h21 ChurchZero,
        have h20:= emptyset_axiom ( ChurchZero:M), 
        have h19: ChurchZero ∈ LOOP n ∩ STEM:=
          begin
            rw intersection_axiom,
            rw intersection_axiom at h21, 
            exact  ⟨hr, h18 ⟩ ,
          end,
        rw h21 at h19,
        contradiction,
      end,
    have h29:= LN M k n hstem hn hkn hskn,
    have h28:= member_subset M (LOOP n) ℕℕ r h29 hr,
    rw sym at h7, 
    rw hnzero at hsr, 
    rw sym at hsr,
    have h30:= rho M hNfinite k n ChurchZero r hstem hn hkn hskn (zeroN M) h28 h7 hsr,
    have h31: ChurchZero <ℕ r:=
      begin
        rw ChurchOrder,
        rw sym at h7,
        have h32:= predecessor M r h28 h7,
        cases h32 with p h33,
        cases h33 with h34 h35,
        use p,
        split,
        {
          exact h34,
        },
        {
          rw zeroplusx M (S p) (successorN M p h34),
          exact h35,
        }
      end,
    have h32:= h30 h31,
    cases h32 with h33 h34,
    have h35: S r = S n:=
      begin
        rw h34,
      end,
    rw←  hsr at h35,
    rw hnzero at h35,
    rw sym at h35,
    have h36:= snneqn M (S ChurchZero)(successorN M ChurchZero (zeroN M)),
    contradiction,
  end

lemma orderstep4: ∀ (k n q:M), k ∈ ℕℕ → n ∈ ℕℕ → ℕℕ ∈ FINITE M → S k = S n → ¬(k=n)→  k ∈ STEM → q ∈ ℕℕ → ¬ q = n → ¬ q = ChurchZero → ∀ (X f a b c g:M), X ∈ FINITE M → ¬ c ∈ X → ‹ b,a › ∈ f → ¬ (a=b) → g= (f - single ‹ b,a › ∪ single ‹ b,c › ∪ single ‹ c,a›) →  
cyclicperm M f X a → permorder M f X a q  →  cyclicperm M g (X ∪ single c) a :=
  assume k n q hk hn hNfinite hskn hkn hstem hq hqn hqz X f a b c g hfinite h3 h11 hab h50 h4 h5,
  begin
    have h5copy:= h5,
    unfold permorder at h5,
    unfold cyclicperm,
    have h4copy:= h4,
    unfold cyclicperm at h4,
    rcases h5 with ⟨ hq, hqfa, h6, h7⟩,
    have h31:= predecessornotn M hNfinite k n hstem hn hkn hskn q hq hqz,
    cases h31 with t h32,
    rcases h32 with ⟨ ht, hst, htn⟩,
    have line62:= formula62 M k n q hk hn hNfinite hskn hkn hstem hq hqn hqz X f a b c g hfinite h3 h11 hab h50 h4copy h5copy t ht hst htn,
    have line63:= formula63 M k n q hk hn hNfinite hskn hkn hstem hq hqn hqz X f a b c g hfinite h3 h11 hab h50 h4copy h5copy t ht hst htn,
    have htfa:=  tfa M k n q hk hn hNfinite hskn hkn hstem hq hqn hqz X f a b c g hfinite h3 h11 hab h50 h4copy h5copy t ht hst htn,    
    have h70:= orderstep1 M k n q hk hn hNfinite hskn hstem hq hqn hqz X f a b c g hfinite h3 h11 h50 h4.left,
    unfold permutation at h70,
    cases h70 with h71 h72,
    unfold injection at h71,
    rcases h71 with ⟨ honeoneg, hRelg, hFUNCg,  hdomg,hrangeg⟩,
    unfold oneone at honeoneg,
    rcases honeoneg with ⟨ hmapsg, h73, h74⟩,
    rcases h4 with ⟨ hpermf, ha, h75⟩,
    have line64:= formula64 M k n q hk hn hNfinite hskn hkn hstem hq hqn hqz X f a b c g hfinite h3 h11 hab h50 h4copy h5copy t ht hst htn, 
    have h403: a ∈ X ∪ (single c):=
    begin
      rw binary_union_axiom,
      left,
      exact ha,
    end,
    have h200:= orderstep2 M k n q hk hn hNfinite hskn hkn hstem hq hqn hqz X f a b c g hfinite h3 h11 hab h50 h4copy h5copy,
    unfold cyclicperm at h200,
    exact h200,
  end



lemma simplestperm:  ℕℕ ∈ FINITE M →  ∀ (a b:M), ¬ a =b →   ∃(f:M), ‹ a,b› ∈ f ∧ cyclicperm M f { a, b }  a ∧ permorder M f { a, b } a (S (S ChurchZero)):=
  assume hNfinite a b hab,
  begin  
    have h2:= kinstem M hNfinite,
    cases h2 with k h3,
    cases h3 with n h4,
    rcases h4 with ⟨ hk, hn, hkn, hskn, hstem⟩,
    set X:= pair a b with hX,
    set f:= pair ‹ a,b› ‹ b,a› with hf,
    have hRel: Rel f:=
      begin
        rw Rel_definition,
        intros z hz,
        rw hf at hz,
        rw pairing_axiom at hz,
        cases hz with h3 h4,
        {
          use a, use b,
          exact h3,
        },
        {
          use b, use a,
          exact h4,
        } 
      end,
    have hFUNC: f ∈ (FUNC:M):=
      begin
        rw FUNC_members M,
        intros x y z h20 h21,
        rw hf at h20 h21,
        rw pairing_axiom at h20 h21,
        cases h20 with h22 h23,
        {
          cases h21 with h24 h25,
          {
            rw ordered_pair_equality at h22 h24,
            rw h24.right,
            rw h22.right,
          },
          {
            rw ordered_pair_equality at h22 h25, 
            rw← h22.left at *,
            rw← h25.left at *,
            contradiction,
          }
        },
        {
          cases h21 with h24 h25,
          { 
            rw ordered_pair_equality at h23 h24,
            rw← h24.left at *,
            rw← h23.left at *,
            contradiction,
          },
          {
            rw ordered_pair_equality at h23 h25,
            rw h23.right,
            rw h25.right,
          }
        }
      end,
    use f,
    have h20: X ∈ FINITE M:=
      begin
        rw hX,
        have h10:= singleton_finite M a,
        have h12: ¬ b ∈ single a:= 
          begin
            intro h,
            rw singleton1 at h,
            rw sym at h,
            contradiction,
          end,
        have h11:= finite_adjoin M (single a ) b  ⟨ h10, h12⟩,
        have h13: (pair a b) = ((single a) ∪ (single b)):=
          begin
            rw full_extensionality,
            intro t,
            rw pairing_axiom,
            rw binary_union_axiom,
            rw singleton1,
            rw singleton1,
          end,
        rw h13,
        exact h11,
      end,
    split,
    {
      rw hf,
      rw pairing_axiom,
      left,
      refl,
    },
    { 
      split,
      {
        unfold cyclicperm,
        split,
        {
          unfold permutation,
          split,
          {
            unfold injection,
            repeat{split},
            {
              exact hRel,
            },
            {
              intros x y h,
              cases h with h3 h4,
              rw hX at h3,
              rw hX,
              rw pairing_axiom at h3,
              rw pairing_axiom,
              cases h3 with h5 h6,
              {
                rw h5 at *,
                right,
                rw FUNC_members at hFUNC,
                have h7: ‹ a,b › ∈ f:=
                  begin
                    rw hf,
                    rw pairing_axiom,
                    simp,
                  end,
                have h8:= hFUNC a y b h4 h7,
                exact h8,
              },
              {
                left,
                rw h6 at *,
                have h7: ‹ b,a› ∈  f:=
                  begin
                    rw hf,
                    rw pairing_axiom,
                    simp,
                  end,
                rw FUNC_members at hFUNC,
                have h8:= hFUNC b y a h4 h7,
                exact h8,
              }
            },
            {
              rw FUNC_members at hFUNC,
              intros x y z h10,
              rcases h10 with ⟨ h11, h12, h13⟩,
              exact hFUNC x y z h12 h13,
            },
            {
              intros x hx,
              rw hX at hx,
              rw pairing_axiom at hx,
              cases hx with h10 h11,
              {
                use b,
                rw h10 at *,
                rw hX,
                rw pairing_axiom,
                rw hf,
                simp,
                rw pairing_axiom,
                simp,
              },
              {
                rw h11 at *,
                use a,
                rw hX,
                rw hf,
                rw pairing_axiom,
                rw pairing_axiom,
                simp,
              }
            },
            {
              intros x u y,
              intros h,
              cases h with h3 h4 h5,
              rw hf at h3,
              rw pairing_axiom at h3,
              rw hX at h4,
              cases h3 with h5 h6, 
              { 
                rw ordered_pair_equality at h5,
                cases h5 with h6 h7,
                rw h6 at *,
                rw h7 at *,
                rw hf at h4,
                rw pairing_axiom at h4,
                rw pairing_axiom at h4,
                simp at h4,
                cases h4 with h8 h9,
                {
                  rw ordered_pair_equality at h8,
                  symmetry,
                  exact h8.left,
                },
                {
                  rw ordered_pair_equality at h9,
                  rw h9.left at *,
                  symmetry,
                  exact h9.right,
                }
              },
              { 
                rw ordered_pair_equality at h6,
                rw h6.left at *,
                rw h6.right at *,
                cases h4 with h7 h8,
                rw hf at h7,
                rw pairing_axiom at h7,
                cases h7 with h9 h10,
                {
                  rw ordered_pair_equality at h9,
                  rw h9.left at *,
                  rw← h9.right at *,
                },
                {
                  rw ordered_pair_equality at h10,
                  symmetry,
                  exact h10.left,
                } 
              }
            },
            { 
              intros x y h,
              rw hX at h,
              rw hf at h,
              rw pairing_axiom at h,
              rw pairing_axiom at h,
              cases h with h3 h4,
              cases h4 with h5 h6, 
              {
                rw h5 at *,
                cases h3 with h7 h8,
                { 
                  rw ordered_pair_equality at h7,
                  rw h7.left at *,
                  rw← h7.right at *,
                  rw hX,
                  rw pairing_axiom,
                  simp,
                },
                {
                  rw hX,
                  rw ordered_pair_equality at h8,
                  rw h8.left,
                  rw pairing_axiom,
                  simp,
                }    
              },
              {
                rw h6 at *,
                cases h3 with h4 h5,
                {
                  rw ordered_pair_equality at h4,
                  rw h4.left at *,
                  rw hX,
                  rw pairing_axiom,
                  simp,
                },
                {
                  rw ordered_pair_equality at h5,
                  rw h5.right at *,
                  contradiction, 
                }
              }      
            },
            {
              exact hRel,
            },
            {
              exact hFUNC,
            },
            {
              rw subset_definition,
              intros t h,
              rw domain_axiom f hRel at h,
              rw hX,
              rw pairing_axiom,
              cases h with h4 h5,
              {
                rw hf at h5,
                rw pairing_axiom at h5,
                cases h5 with h6 h7,
                {
                  left,
                  rw ordered_pair_equality at h6,
                  exact h6.left,
                },
                {
                  right,
                  rw ordered_pair_equality at h7,
                  exact h7.left,
                } 
              } 
            },
            {
              rw subset_definition,
              intros t h,
              rw range_axiom f hRel at h,
              rw hX,
              rw pairing_axiom,
              cases h with x h4,
              rw hf at h4,
              rw pairing_axiom at h4,
              cases h4 with h5 h6,
              {
                right,
                rw ordered_pair_equality at h5,
                exact h5.right,
              },
              {
                left,
                rw ordered_pair_equality at h6,
                exact h6.right,
              }
            }
          },
          {
            unfold onto,
            intros y hy,
            rw hX at hy,
            rw pairing_axiom at hy,
            cases hy with h5 h6,
            {
              rw h5 at *,
              use b,
              rw hX,
              rw hf,
              rw pairing_axiom,
              simp,
              rw pairing_axiom,
              simp,
            },
            {
              rw h6 at *,
              use a,
              rw hX,
              rw hf,
              rw pairing_axiom,
              simp,
              rw pairing_axiom,
              simp, 
            }
          }
        },
        {
          split,
          {
            rw pairing_axiom,
            simp,
          },
          {
            intros t ht,
            rw hX at ht,
            rw pairing_axiom at ht,
            cases ht with h5 h6,
            {
              rw h5 at *,
              use ChurchZero,
              split,
              {
                exact zeroN M,
              },
              {
                rw ApZero,
                rw ApId, 
              }
            },
            {
              rw h6 at *,
              use S ChurchZero,
              split,
              {
                exact successorN M ChurchZero (zeroN M),
              },
              {
                rw ApOne M f hFUNC hRel,
                have h7: ‹ a, b› ∈ f:=
                  begin
                    rw hf,
                    rw pairing_axiom,
                    simp,
                  end,
                have h8:= Apdef M f hFUNC a b h7,
                exact h8,
              }
            }
          }
        }
      },
      {
        unfold permorder, 
        split,
        {
          have h4:= successorN M ChurchZero (zeroN M),
          exact successorN M (S ChurchZero) h4,
        },
        { 
          have h2: ‹ b,a › ∈ f:=
            begin
              rw hf,
              rw pairing_axiom,
              simp,
            end,
          have h3: ‹ a,b› ∈  f:=
            begin
              rw hf,
              rw pairing_axiom,
              simp,
            end, 
          have h4: Ap( Ap  (S ChurchZero) f)  a = b:=
            begin
              rw ApOne M f hFUNC hRel,
              have h5:= Apdef M f hFUNC a b h3, 
              symmetry,
              exact h5,
            end,
          have h5: Ap (Ap (S ChurchZero) f ) b = a:=
            begin
              rw ApOne M f hFUNC hRel,
              have h6:= Apdef M f hFUNC b a h2,
              symmetry,
              exact h6,
            end,
          have ha: a ∈ X:=
            begin
              rw hX,
              rw pairing_axiom,
              simp,
            end,
          have h6: maps M f X X:=
            begin
              unfold maps,
              split,
              {
                exact hRel,
              },
              {
                split,
                {
                  intros x y h100,
                  cases h100 with hx h101,
                  rw hX at hx,
                  rw hX,
                  rw pairing_axiom at hx,
                  rw pairing_axiom,
                  rw FUNC_members at hFUNC,
                  cases hx with h102 h103,
                  {
                    rw h102 at *,
                    right,
                    have h104:= hFUNC a b y h3 h101,
                    symmetry,
                    exact h104,
                  },
                  {
                    rw h103 at *,
                    left,
                    have h105:= hFUNC b a y h2 h101,
                    symmetry,
                    exact h105, 
                  }
                },
                {
                  split,
                  { 
                    rw FUNC_members at hFUNC,
                    intros x y z h110,
                    rcases h110 with ⟨ hx, h111, h112⟩ ,
                    exact hFUNC x y z h111 h112,
                  },
                  {
                    intros x hx,
                    rw hX at hx,
                    rw pairing_axiom at hx,
                    cases hx with h113 h114,
                    {
                      rw h113 at *,
                      use b,
                      rw hX,
                      rw pairing_axiom,
                      rw hf,
                      rw pairing_axiom,
                      simp, 
                    },
                    {
                      use a,
                      rw h114 at *,
                      rw hX,
                      rw hf,
                      rw pairing_axiom,
                      rw pairing_axiom,
                      simp,
                    }
                  }
                }
              }
            end,
          have h20: Ap (Ap (S (S ChurchZero)) f) a = a :=
            begin
              have h8:= successorequation M X f hFUNC hRel h6 (S ChurchZero) a (successorN M ChurchZero (zeroN M)) ha,
              rw h8,
              rw h4,
              have h9:= Apdef M f hFUNC b a h2,
              symmetry,
              exact h9,
            end,
          split,
          {
            exact h20,
          },
          {
            split,
            {
              intros t ht h7 h8,
              have h13:= mbig2 M,
              have h14: ¬ ChurchZero = n:=
                begin
                  intro h, 
                  have h19:= nissuccessor M k n hstem hn hkn hskn, 
                  cases h19 with p h21,
                  cases h21 with h22 h23,
                  rw← h at h23,
                  have h25:= LN M k n hstem hn hkn hskn,
                  have hp:= member_subset M (LOOP n) ℕℕ p h25 h22,
                  have h26:= successoromitszero M p hp, 
                  contradiction,
                end, 
              have h10: ¬  S ChurchZero =n :=  
                begin
                  have h11:= nneqone M k n hk hn hNfinite hskn hkn hstem, 
                  rw sym at h11, 
                  exact h11, 
                end,
              have h9:= preceqsuccessor M hNfinite k n hstem hn hkn hskn t (S ChurchZero) ht (successorN M ChurchZero (zeroN M)) h10,
              rw h9 at h7,
              cases h7 with h11 h12,
              {
                have h13:= preceqsuccessor M hNfinite k n hstem hn hkn hskn t ChurchZero ht (zeroN M) h14,     
                rw h13 at h11,
                cases h11 with h15 h16,
                {
                  have h17:= preceqzero M hNfinite k n hstem hn hkn hskn t ht h15,
                  contradiction, 
                },
                {
                  rw←  h16 at h4,
                  intro h,
                  rw h4 at h,
                  rw sym at h,
                  contradiction,
                }
              },
              {
                intro h,
                exact h12, 
              }
            },
            {
              intros x hx,
              rw hX at hx,
              rw pairing_axiom at hx,
              cases hx with h120 h21,
              {
                use ChurchZero,
                rw h120 at *,
                rw ApZero,
                rw ApId,
                simp,
                split,
                {
                  exact zeroN M,
                },
                {
                  have h8:= successorN M ChurchZero (zeroN M),
                  have h11:= successorN M (S ChurchZero) h8,
                  have h9:= precmin M hNfinite k n hstem hn hkn hskn (S (S ChurchZero)) h11,
                  exact h9, 
                }
              },
              {
                use S ChurchZero,
                rw h21,
                rw h4,
                simp,
                split,
                { 
                  exact successorN M ChurchZero (zeroN M),
                },
                {
                  have snz: ¬ S ChurchZero = n:= 
                    begin
                      have h11:= nneqone M k n hk hn hNfinite hskn hkn hstem, 
                      rw sym at h11, 
                      exact h11,  
                    end,
                  have h23:= successorN M ChurchZero (zeroN M),
                  have h22:= preceqsuccessor M hNfinite k n hstem hn hkn hskn (S ChurchZero)(S ChurchZero) h23 h23 snz,
                  rw h22,
                  left,
                  have h24:= preceqreflexive M hNfinite k n hstem hn hkn hskn (S ChurchZero) h23,
                  exact h24, 
                }
              }
            }
          }
        }
      }
    }       
  end

lemma emptyneqsingletonempty: ¬ (Λ:M)  = single (Λ:M) :=
  begin
    intro h14,
    rw full_extensionality at h14, 
    specialize h14 Λ,
    rw singleton1 at h14,
    simp at h14,
    exact emptyset_axiom Λ h14,
  end

#axioms_all