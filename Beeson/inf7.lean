
import inf6     
variables (M:Type) [Model M] (a b x y z u v w X R W κ μ ℓ : M)
-- using ℓ where the source text has λ because you can't use λ for a variable.

open Model 

lemma one_neq_zero: ¬ (one:M) = (zero:M):=
  begin
    rw one_definition,
    exact successor_omits_zero M zero,
  end 

lemma zero_lessthan_one:  (zero:M) < (one:M):=
  begin
    rw lessthan_definition,
    split,
    {
      rw le_definition,
      use Λ, use zero,
      repeat {split},
      {
        rw zero_definition,
        rw singleton1 M,
      },
      {
        rw one_definition,
        rw successor_members,
        use Λ, use Λ, 
        rw zero_definition,
        rw singleton1 M,
        rw empty_union_x M (single Λ ),
        exact ⟨ refl Λ, emptyset_axiom Λ, refl (single Λ )⟩, 
      },
      {
        exact (empty_always_subset M zero),
      },
      {
        rw (empty_union_x M (zero - Λ )), 
        rw (x_minus_empty M zero), 
      }
    },
    {
      rw one_definition, 
      have h8:= successor_omits_zero M zero, 
      intro h9,
      rw sym at h9,
      contradiction, 
    }
  end

lemma zerolessthanone :(zero:M) < (one:M):=  
  begin
    exact zero_lessthan_one M, 
  end 

lemma oneF: (one:M) ∈ 𝔽  :=
  begin
    rw one_definition,
    have h:= successorF M zero (zeroF M),
    have h2: zero ∈ 𝕊 zero:=
      begin
        rw successor_members M,
        use Λ, use Λ, 
        rw empty_union_x M (single Λ ),
        rw zero_definition,
        rw singleton1 M, 
        exact ⟨ refl Λ, emptyset_axiom Λ, refl (single Λ )⟩ ,
      end,
    exact successorF M zero (zeroF M) ⟨ zero, h2⟩ , 
  end 


lemma zeroinone: (zero:M) ∈ one:=
  begin
    rw one_definition,
    rw successor_members,
    use Λ, use Λ,
    rw zero_definition,
    rw (singleton1 M),
    repeat {split}, 
    { 
      exact (emptyset_axiom (Λ:M) ), 
    },
    {
      rw empty_union_x M (single (Λ:M)),
    },
  end

lemma twoF: (two:M) ∈ 𝔽 := 
  begin
    rw two_definition,
    have h:= successorF M one (oneF M),
    have h2: (zero ∪ (single zero))  ∈ 𝕊 one:=
      begin
        rw successor_members M,
        use zero, use zero,
        split,
        { 
          exact zeroinone M, 
        },
        {
          split,
          {
            rw zero_definition,
            rw singleton1 M,
            intro h3, 
            rw full_extensionality at h3, 
            specialize h3 Λ, 
            rw singleton1 M at h3, 
            have h4:= emptyset_axiom (Λ:M), 
            simp at h3,
            contradiction,
          },
          {  
            exact (refl (zero ∪ (single zero))),
          }
        }
      end,
    exact successorF M one  (oneF M) ⟨zero ∪ (single zero), h2⟩ , 
  end 


lemma one_lessthan_two: (one:M) < (two:M):=
  begin
    rw two_definition,
    rw one_definition,
    have h: (zero:M) < (one:M) := zero_lessthan_one M, 
    have h1: ∃ (u:M), u ∈ (one:M):=  cardinalsinhabited M one (oneF M), 
    have h2: ∃ (u : M), u ∈ 𝕊 zero:= 
      begin
        simp_rw← one_definition, 
        exact h1, 
      end,
    have h3: ∃ (u:M), u ∈ (two:M):=  cardinalsinhabited M two (twoF M), 
    have h5: ∃ (u : M), u ∈ 𝕊 one:= 
      begin
        simp_rw← two_definition, 
        exact h3, 
      end,
    have h4:= successorstrict M zero one (zeroF M)(oneF M) h2 h5, 
    rw h4 at h,
    rw one_definition at h,
    exact h,
  end

lemma zero_lessthan_two: (zero:M) < two :=
  begin
    have h1:= zero_lessthan_one M,
    have h2:= one_lessthan_two M,
    have h3:= lessthan_transitive M zero   one two (zeroF M) (oneF M) (twoF M) h1 h2 ,
    exact h3,
  end


theorem infiniteimpliesnotfinite2: ∀ (X:M), X ∈ FINITE M → ∀ (Y:M), Y ⊆ X → similar M X Y → X=Y:=
  begin
    have base: (Λ:M) ∈ Winfiniteimpliesnotfinite M:=
      begin
        rw Winfiniteimpliesnotfinite_members M, 
        split,
        {
          exact lambda_finite M,
        },
        {
          intros X  h h2, 
          have h6:= similar_to_empty  M X,
          symmetry, 
          rw← h6,
          rw similar_symmetric, 
          exact h2, 
        }
      end,
    have step: adjoin_closed M (Winfiniteimpliesnotfinite M):=
      begin
        intros A b h, 
        rw Winfiniteimpliesnotfinite_members M at *,  
        cases h with h2 h3,
        cases h2 with h4 h5,
        have h6:=finite_adjoin M A b ⟨ h4, h3⟩, 
        split,
        {
          exact h6,
        },
        { intros Y h16 h18, 
          have h175:= finitesimilar M (A ∪ (single b)) Y h18 h6, 
          have h9:= finitedecidable M (A ∪ (single b)) h6, 
          unfold similar at h18, 
          cases h18 with f h19, 
          unfold similarity at h19,
          cases h19 with h20 h21,
          unfold oneone at h20, 
          rcases h20 with ⟨ h22, h23, h24⟩,
          unfold onto at h21, 
          unfold maps at h22, 
          rcases h22 with ⟨ h25, h26,h27, h28⟩, 
          have h29:= adjoin_member M b A,
          have h30:= h28 b h29,
          cases h30 with c h31,   --  c = f(b)
          cases h31 with h32 h33,
          set U:= Y - (single c) with h34,
          rw decidable_members M at h9, 
          have h35: similarity M f A U:=
            begin
              unfold similarity,
              split,
              {
                unfold oneone,
                unfold maps,
                repeat{split},
                {
                  exact h25, 
                },
                {
                  rw h34,
                  intros x y,
                  rw minus_members,
                  rw singleton1, 
                  specialize h26 x y,
                  intro h27,
                  cases h27 with h28 h29,
                  have h30: x ∈ A ∪ (single b):=
                    begin
                      rw binary_union_axiom,
                      left,
                      exact h28,
                    end,
                  have h31:= h26 ⟨ h30, h29⟩, 
                  split,
                  {
                    exact h31,
                  },
                  {
                    intro h32, 
                    rw h32 at *,
                    have h33:= h23 x b c ⟨ h29, h33,h30 ⟩, 
                    rw h33 at *,
                    contradiction, 
                  }
                },
                {
                  intros x y z, 
                  intro h35,
                  rcases h35 with ⟨ h36, h37, h38⟩,
                  have h39:= h27 x y z,
                  have h40: x ∈ A ∪ (single b):=
                    begin
                      rw binary_union_axiom,
                      left,
                      exact h36,
                    end,
                  have h41:= h39 ⟨ h40, h37, h38⟩, 
                  exact h41,
                },
                {
                  intros x h,
                  have h35:x ∈ A ∪ (single b):=
                    begin
                      rw binary_union_axiom,
                      left,
                      exact h,
                    end,
                  have h36:= h28 x h35,
                  cases h36 with y h37,
                  cases h37 with h38 h39,
                  use y,
                  rw h34,
                  rw minus_members,
                  split,
                  {
                    split,
                    {
                      exact h38,
                    },
                    {
                      rw singleton1,
                      intro h40,
                      rw h40 at *,
                      have h41:= h23 x b c ⟨ h39, h33, h35⟩,
                      rw h41 at *,
                      contradiction, 
                    }
                  },
                  {
                    exact h39, 
                  }
                },
                {
                  intros x u y h35,
                  rcases h35 with ⟨ h36, h37, h38⟩, 
                  have h39: x ∈ A ∪ (single b):=
                    begin
                      rw binary_union_axiom,
                      left,
                      exact h38,
                    end,
                  have h40:= h23 x u y ⟨ h36, h37, h39⟩, 
                  exact h40, 
                },
                {
                  intros x y,
                  rw h34,
                  rw minus_members,
                  intro h35,
                  rcases h35 with ⟨ h36, h37, h38⟩, 
                  have h36:= h24 x y ⟨ h36,h37⟩, 
                  rw binary_union_axiom at h36,
                  rw singleton1 at h36,
                  rw singleton1 at h38,
                  cases h36 with h39 h40,
                  {
                    exact h39,
                  },
                  {
                    rw h40 at *,
                    have h41:= h27 b c y ⟨ h29, h33, h36⟩ ,
                    rw← h41 at *,
                    contradiction,
                  }
                }
              },
              {
                unfold onto, 
                intros y h35,
                rw h34 at h35, 
                rw minus_members at h35,
                rw singleton1 at h35,
                cases h35 with h36 h37,
                have h38:= h21 y h36,
                cases h38 with x h39,
                cases h39 with h40 h41, 
                use x,
                rw binary_union_axiom at h40,
                rw singleton1 at h40,
                cases h40 with h42 h43, 
                {
                  exact ⟨ h42, h41⟩, 
                },
                {
                  rw h43 at *,
                  have h44 := h27 b c y ⟨ h29, h33, h41⟩, 
                  rw←  h44 at *,
                  contradiction, 
                }
              }
            end, 
          have h50: similar M A U:=
            begin
              unfold similar,
              use f,
              exact h35, 
            end,
          have h36: c ∈ A ∪ (single b):= member_subset M Y (A ∪ single b) c h16 h32,  
          have h40:= h9 b c ⟨ h29, h36⟩, 
          cases h40 with h41 h42,
          { -- case 1, b = c
            have h43: U ⊆ A:=
              begin
                rw subset_definition,
                intro t,
                intro h44,
                rw h34 at h44,
                rw subset_definition at h16,
                specialize h16 t,
                rw binary_union_axiom at h16, 
                rw h41 at *,
                rw singleton1 at h16,
                rw minus_members at h44,
                rw singleton1 at h44,
                have h45:= h16 h44.left, 
                cases h45 with h100 h101,
                {
                  exact h100,
                },
                {
                  rw h101 at *,
                  cases h44 with h102 h103,
                  contradiction, 
                }
              end,  
            have h101: A=U := h5 U h43 h50, 
            rw h41 at *,
            rw← h101 at *, 
            rw full_extensionality,
            intro t,
            have h60:= finite_decidable2 M (A ∪ (single c)) t c h6, 
            split,
            {
              intro h61,
              have h63:= adjoin_member M c A,
              have h62:= h60 h61 h63,
              cases h62 with h64 h65,
              {
                rw h64 at *,
                exact h32, 
              },
              {
                rw binary_union_axiom at h61,
                cases h61 with h66 h67,
                {
                  rw h34 at h66,
                  rw minus_members at h66,
                  rw singleton1 at h66,
                  exact h66.left, 
                },
                {
                  rw singleton1 at h67,
                  contradiction, 
                }
              }
            },
            {
              intro h61,
              have h62:= member_subset M Y (A ∪ (single c)) t h16 h61,
              exact h62, 
            }  
          },
          {  -- case 2, b ≠ c 
            have h51:  b ∈ (Y:M)  → Y = (A ∪ (single b)) := 
              begin 
                intro h52,
                have h53:= h21 b h52,
                cases h53 with p h54, 
                cases h54 with h55 h56,
                have h57: ¬ p = b:=
                  begin
                    intro h58,
                    rw h58 at *,
                    have h59:= h27 b b c ⟨ h55, h56, h33⟩, 
                    contradiction, 
                  end, 
                set g:= ((f - single(‹ b,c ›)) - single(‹ p, b› )) ∪ single(‹ p,c › ) with h60,
                have h61: similarity M g A (Y - single(b)):=
                  begin
                    unfold similarity, 
                    split,
                    {
                      unfold oneone,
                      unfold maps,
                      repeat{split},
                      {
                        rw Rel_definition, 
                        intros t h62,
                        rw h60 at h62,
                        rw binary_union_axiom at h62, 
                        repeat{ rw minus_members at h62},
                        repeat{rw singleton1 M  at h62}, 
                        rw Rel_definition at h25,
                        specialize h25 t,
                        cases h62 with h63 h64,
                        {
                          cases h63 with h65 h66,
                          cases h65 with h67 h68,
                          exact h25 h67, 
                        },
                        {
                          use p, use c,  
                          exact h64, 
                        }
                      },
                      {
                        intros x y h62,
                        cases h62 with h63 h64, 
                        rw h60 at h64,
                        rw binary_union_axiom at h64, 
                        repeat{ rw minus_members at h64},
                        repeat{rw singleton1 M  at h64}, 
                        cases h64 with h65 h66,
                        {
                          cases h65 with h66 h67,
                          cases h66 with h68 h69,
                          have h70: x ∈ A ∪ (single b):=
                            begin
                              rw binary_union_axiom,
                              left,
                              exact h63,
                            end,
                          have h71:= h26 x y ⟨ h70, h68⟩, 
                          rw minus_members,
                          split,
                          {
                            exact h71,
                          },
                          {
                            rw singleton1 M,
                            intro h72,
                            rw h72 at *,
                            rw ordered_pair_equality at h67,
                            simp at h67,
                            have h69:= h23 p x b ⟨ h56,h68,h55⟩,
                            rw h69 at h67,
                            contradiction, 
                          }
                        },
                        {
                          rw minus_members,
                          rw singleton1,
                          rw ordered_pair_equality M at h66, 
                          cases h66 with h67 h68,
                          rw h67 at *,
                          rw h68 at *,
                          rw sym, 
                          exact ⟨ h32, h42⟩, 
                        }
                      }, 
                      {
                        intros x y z h61,
                        rcases h61 with ⟨ h62, h63, h64⟩, 
                        rw h60 at h63 h64, 
                        rw binary_union_axiom at h64, 
                        repeat{ rw minus_members at h64},
                        repeat{rw singleton1 M  at h64}, 
                        rw binary_union_axiom at h63, 
                        repeat{ rw minus_members at h63},
                        repeat{rw singleton1 M  at h63}, 
                        cases h64 with h65 h66,
                        {
                          cases h65 with h67 h68,
                          cases h67 with h69 h70,
                          cases h63 with h71 h72,
                          {
                            cases h71 with h73 h74,
                            cases h73 with h75 h76,
                            have h77: x ∈ A ∪ (single b):=
                              begin
                                rw binary_union_axiom,
                                left,
                                exact h62,
                              end,
                            have h78:= h27 x y z ⟨ h77, h75, h69⟩, 
                            exact h78,
                          },
                          {
                            rw ordered_pair_equality at h72,
                            cases h72 with h73 h74,
                            rw h73 at *,
                            rw h74 at *, 
                            rw ordered_pair_equality at h68 h70, 
                            simp at h68, 
                            have h75:= h27 p b z ⟨ h55, h56, h69⟩, 
                            rw← h75 at *,
                            contradiction, 
                          }
                        },
                        {
                          cases h63 with h71 h72,
                          {
                            rw ordered_pair_equality at h66,
                            cases h66 with h73 h74,
                            rw h73 at *,
                            rw h74 at *,
                            cases h71 with h75 h76,
                            cases h75 with h77 h78,
                            have h79:= h27 p b y ⟨ h55, h56, h77⟩,
                            rw← h79 at *,
                            contradiction, 
                          },
                          {
                            rw ordered_pair_equality at h66 h72, 
                            cases h72 with h73 h74,
                            cases h66 with h75 h76,
                            rw h74 at *,
                            rw h76 at *,  
                          }
                        },
                      },
                      {
                        intros x h61, 
                        have h62: x ∈ A ∪ (single b):=
                          begin
                            rw binary_union_axiom,
                            left,
                            exact h61,
                          end,
                        have h63:= h28 x h62, 
                        cases h63 with y h64,
                        have h90:= finitedecidable M (A ∪ (single b)) h6,
                        rw decidable_members M at h90, 
                        have h91:= h90 x p ⟨ h62, h55⟩, 
                        have h92: b ∈ A ∪ (single b):=
                          begin 
                            rw binary_union_axiom,
                            rw singleton1,
                            right,
                            exact refl b, 
                          end,
                        have h93:= h90 x b ⟨ h62, h92⟩, 
                        cases h91 with h94 h95,
                        {
                          rw h94 at *,
                          use c,
                          split,
                          {
                            rw minus_members,
                            rw singleton1, 
                            split,
                            {
                              exact h26 b c ⟨ h29, h33⟩, 
                            },
                            {
                              cases h93 with h94 h95,
                              {
                                rw h94 at *,
                                rw sym,
                                exact h42, 
                              },
                              {
                                intro h96,
                                rw h96 at *,
                                contradiction, 
                              }
                            }
                          },
                          {
                            rw h60,
                            rw binary_union_axiom,
                            right,
                            rw singleton1, 
                          }
                        },
                        {  
                          cases h93 with h96 h97,
                          { 
                            rw h96 at *,
                            contradiction, 
                          },
                          {
                            use y,
                            cases h64 with h65 h66,
                            rw minus_members,
                            rw singleton1, 
                            split,
                            {
                              split,
                              {
                                exact h65,
                              },
                              {
                                intro h67, 
                                rw h67 at *,
                                have h68:= h23 x p b ⟨ h66, h56, h62⟩, 
                                rw h68 at *, 
                                contradiction, 
                              }
                            },
                            {
                              rw h60,
                              rw binary_union_axiom,
                              repeat{ rw minus_members} ,
                              repeat{rw singleton1}, 
                              left,
                              split,
                              {
                                split,
                                {
                                  exact h66,
                                },
                                {
                                  intro h67,
                                  rw ordered_pair_equality M at h67,
                                  cases h67 with h68 h69,
                                  rw h68 at *,
                                  rw h69 at *,
                                  contradiction, 
                                }
                              },
                              {  
                                intro h67, 
                                rw ordered_pair_equality M at h67, 
                                cases h67 with h68 h69, 
                                rw h68 at *,
                                rw h69 at *, 
                                contradiction, 
                              }
                            }
                          }
                        }
                      },
                      { -- g is one-to-one
                        intros x u y h70,
                        rcases h70 with ⟨ h71, h72, h73⟩, 
                        rw h60 at h72 h71,
                        rw binary_union_axiom at h72 h71,
                        repeat {rw minus_members at h72 h71},
                        repeat {rw singleton1 at h72 h71},
                        cases h71 with h74 h75,
                        {
                          cases h74 with h76 h77,
                          cases h76 with h78 h79,
                          cases h72 with h80 h81,
                          {
                            cases h80 with h82 h83,
                            cases h82 with h84 h85,
                            have h88: x ∈ A ∪ (single b):=
                              begin
                                rw binary_union_axiom,
                                left,
                                exact h73,
                              end,
                            have h86:= h23 x u y ⟨ h78, h84, h88⟩, 
                            exact h86,
                          },
                          {
                            rw ordered_pair_equality at h81, 
                            cases h81 with h82 h83,
                            rw h82 at *,
                            rw h83 at *, 
                            rw ordered_pair_equality at h79 h77,
                            simp at h79 h77,
                            have h88: x ∈ A ∪ (single b):=
                              begin
                                rw binary_union_axiom,
                                left,
                                exact h73,
                              end,
                            have h84:= h23 x b c ⟨ h78, h33, h88⟩, 
                            contradiction, 
                          }
                        },
                        {
                          rw ordered_pair_equality at h75,
                          cases h75 with h76 h77,
                          rw h76 at *,
                          rw h77 at *, 
                          cases h72 with h78 h79,
                          {
                            cases h78 with h80 h81,
                            cases h80 with h82 h83,
                            have h84:= h23 b u c ⟨ h33, h82, h29⟩,
                            rw h84 at h83,
                            contradiction, 
                          },
                          {
                            rw ordered_pair_equality at h79,
                            simp at h79,
                            symmetry, 
                            exact h79, 
                          }
                        }
                      },
                      {
                        intros x y h61,
                        cases h61 with h62 h63,
                        rw h60 at h62,
                        rw binary_union_axiom at h62,
                        repeat {rw minus_members  at h62},
                        repeat { rw singleton1 at h62}, 
                        cases h62 with h64 h65,
                        {
                          cases h64 with h66 h67,
                          cases h66 with h68 h69,
                          rw minus_members at h63,
                          cases h63 with h70 h71,
                          rw singleton1 at h71,
                          have h72:= h24 x y ⟨ h68, h70⟩,
                          rw binary_union_axiom at h72,
                          cases h72 with h73 h74,
                          {
                            exact h73,
                          },
                          {
                            rw singleton1 at h74,
                            rw h74 at *, 
                            rw ordered_pair_equality at h69,
                            simp at h69,
                            have h75:= h27 b c y ⟨ h29, h33, h68⟩, 
                            rw h75 at h69,
                            contradiction, 
                          }
                        },
                        {
                          rw ordered_pair_equality at h65,
                          cases h65 with h66 h67,
                          rw h66 at *,
                          rw h67 at *,
                          rw binary_union_axiom at h55,
                          cases h55 with h68 h69,
                          {
                            exact h68,
                          },
                          {
                            rw singleton1 at h69,
                            rw h69 at *,
                            contradiction, 
                          }
                        }
                      }
                    },
                    {  -- g is onto
                      unfold onto,
                      intros y h61,
                      rw minus_members at h61,
                      rw singleton1 at h61,
                      cases h61 with h62 h63,
                      {
                        have h64:= member_subset M Y (A ∪ (single b)) y h16 h62, 
                        have h66:= h9 y c ⟨ h64, h36⟩, 
                        cases h66 with h67 h68,
                        {
                          rw h67 at *,
                          use p,
                          split,
                          {
                            rw binary_union_axiom at h55,
                            cases h55 with h70 h71,
                            {
                              exact h70,
                            },
                            {
                              rw singleton1 at h71,
                              contradiction, 
                            }
                          },
                          {
                            rw h60,
                            rw binary_union_axiom,
                            repeat {rw minus_members},
                            repeat {rw singleton1 },
                            right,
                            refl, 
                          }
                        },
                        { 
                          have h70:= h21 y h62, 
                          cases h70 with x h71,
                          cases h71 with h72 h73,
                          rw binary_union_axiom at h72,
                          cases h72 with h74 h75,
                          {
                            use x,
                            split,
                            {
                              exact h74,
                            },
                            {
                              rw h60,
                              rw binary_union_axiom,
                              left,
                              repeat {rw minus_members},
                              repeat {rw singleton1},
                              repeat {rw ordered_pair_equality},
                              split,
                              {
                                split,
                                {
                                  exact h73,
                                },
                                {
                                  intro h75,
                                  cases h75 with h76 h77,
                                  rw h76 at *,
                                  rw h77 at *,
                                  contradiction,
                                }
                              },
                              {
                                intro h75,
                                cases h75 with h76 h77,
                                rw h76 at *,
                                rw h77 at *,
                                contradiction, 
                              }
                            }
                          },
                          {
                            rw singleton1 at h75, 
                            rw h75 at *,
                            have h76:= h27 b y c ⟨ h29, h73, h33⟩,
                            contradiction,               
                          }
                        }
                      },
                    }
                  end, 
                have h62:similar M A (Y -(single b)):=
                  begin 
                    unfold similar,
                    use g,
                    exact h61, 
                  end,
                have h63: Y - (single b) ⊆ A :=
                  begin
                    rw subset_definition at h16,
                    rw subset_definition,
                    intro t,
                    specialize h16 t,
                    rw [minus_members, singleton1],
                    intro h64,
                    cases h64 with h65 h66,
                    have h67:= h16 h65,
                    rw [binary_union_axiom, singleton1] at h67, 
                    cases h67 with h68 h69,
                    {
                      exact h68,
                    },
                    {
                      contradiction, 
                    }
                  end, 
                have h64: Y = ((Y - (single b)) ∪ (single b)):=
                  begin
                    rw full_extensionality,
                    intro t,
                    rw binary_union_axiom,
                    rw minus_members,
                    repeat {rw singleton1}, 
                    have h65:t ∈ Y → t ∈ A ∪ (single b):=
                      begin
                        intro h66,
                        rw subset_definition at h16,
                        have h17:= h16 t h66,
                        exact h17,
                      end, 
                    split,
                    {
                      intro h66,
                      have h67:= h9 t b ⟨ h65 h66, h29⟩,
                      rw or_comm, 
                      cases h67 with h68 h69,
                      {
                        left,
                        exact h68,
                      },
                      {
                        right,
                        exact ⟨ h66, h69⟩, 
                      }
                    },
                    {
                      intro h66,
                      cases h66 with h67 h68,
                      {
                        exact h67.left,
                      },
                      {
                        rw h68 at *,
                        exact h52,
                      }
                    }
                  end, 
                have h1112:A = Y - single b := h5 (Y- (single b)) h63 h62, 
                rw←  h1112 at h64,
                exact h64, 
              end, 
            have h100:= finiteseparable M (A ∪ (single b)) Y h6 h175 h16, 
            have h103: b ∈ Y ∨ ¬ b ∈ Y:=
              begin
                rw full_extensionality at h100,
                specialize h100 b,
                repeat {rw binary_union_axiom at h100},
                rw minus_members at h100,
                rw binary_union_axiom at h100,
                rw singleton1 at h100, 
                simp at h100, 
                cases h100 with h101 h102,
                {
                  right,
                  exact h101,
                },
                {
                  left,
                  exact h102, 
                }
              end, 
            cases h103 with h104 h105,
            {
              have h106:= h51 h104,
              symmetry,
              exact h106, 
            },
            {
              have h52: Y ⊆ A :=
                begin
                  rw subset_definition at h16, 
                  rw subset_definition,
                  intro t,
                  specialize h16 t,
                  intro h53,
                  have h54:= h16 h53,
                  rw binary_union_axiom at h54,
                  cases h54 with h55 h56,
                  {
                    exact h55,
                  },
                  {
                    rw singleton1 at h56,
                    rw h56 at *,
                    contradiction, 
                  }
                end, 
              have h53: Y - (single c) ⊆ A:=
                begin
                  rw subset_definition,
                  intro t,
                  rw subset_definition at h52,
                  specialize h52 t,
                  rw minus_members,
                  intro h106,
                  exact h52 h106.left, 
                end, 
              have h54: similar M A (Y-(single c)):=
                begin
                  unfold similar, 
                  rw h34 at h35,
                  use f, 
                  exact h35, 
                end,
              have h55: ¬ (A = Y - (single c)):=
                begin 
                  intro h56,
                  have h57: A ∪ (single c) = ((Y - (single c)) ∪ (single c)):=
                    begin
                      rw h56,
                    end, 
                  have h58: ¬ c ∈ A:=
                    begin
                      intro h59,
                      rw full_extensionality at h56,
                      specialize h56 c,
                      rw minus_members at h56,
                      rw singleton1 at h56,
                      rw h56 at h59,
                      cases h59 with h60 h61,
                      contradiction, 
                    end,
                  have h59:c∈ Y := h26 b c ⟨ h29, h33⟩, 
                  rw subset_definition at h52,
                  specialize h52 c,
                  have h60:= h52 h59, 
                  contradiction,
                end, 
              have h78:= h5 (Y- (single c)) h53 h54, 
              contradiction,  
            }
          }
        }
      end,
		have h: (FINITE M) ⊆ Winfiniteimpliesnotfinite M:= finite_conditions M (Winfiniteimpliesnotfinite M) step base, 
    rw subset_definition at h, 
    intros X h2, 
    specialize h X,
    rw (Winfiniteimpliesnotfinite_members M) at h, 
    have h5:= h h2, 
		cases h5 with h6 h7, 
    exact h7, 
  end


theorem infiniteimpliesnotfinite: ∀(x:M), (infinite M x → ¬ x ∈ FINITE M ):=
  assume x,
  begin
    intro h,
    unfold infinite at h,
    cases h with y h2,
    rcases h2 with ⟨ h3, h4, h5⟩, 
    intro h6,
    have h7:= infiniteimpliesnotfinite2 M x h6 y h3 h5, 
    contradiction,
  end
 

lemma finiteimpliesnotinfinite: ∀(x:M), (x ∈ FINITE M → ¬ infinite M x):=
  assume x,
  begin
    intros h h2,
    have h3:= infiniteimpliesnotfinite M x h2,
    contradiction,
  end


#axioms_all  --This file is clean.  
