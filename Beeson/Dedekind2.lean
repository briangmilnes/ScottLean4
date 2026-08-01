import Dedekind 

variables (M:Type) [Model M] (a b x y z u v w X R W κ μ ℓ : M)
-- using ℓ where the source text has λ because you can't use λ for a variable.

open Model 


lemma adjoin_cardinality: ∀ (B a:M), B ∈ FINITE M → ¬ a ∈ B → Nc M (B ∪ (single a)) = 𝕊 (Nc M B):=
  begin
    intros B a hB ha,
    have h3:= xinNcx M B,
    have h4:= xinNcx M (B ∪ (single a)),
    have h5: B ∪ (single a) ∈ 𝕊 (Nc M B):=
      begin
        rw successor_members,
        use B, use a,
        simp,
        exact ⟨ h3, ha⟩, 
      end,
    have h6: B ∪ (single a) ∈ ( Nc M (B ∪ (single a))) ∩ 𝕊 (Nc M B):=
      begin
        rw intersection_axiom,
        exact ⟨ h4, h5⟩, 
      end,
    have h7:= finite_adjoin M B a ⟨ hB, ha⟩,
    have h8:= finitecardinals3 M (B ∪ (single a)) h7,
    have h9:= finitecardinals3 M B hB,
    have h10:= successorF M (Nc M B) h9 ⟨ B ∪ (single a), h5⟩,
    have h11:= cardinalsdisjoint M (Nc M (B ∪ (single a))) (𝕊 (Nc M B)) (B ∪ (single a)) h8 h10 h6,
    exact h11, 
  end

lemma nothingbetween: ∀ (m n:M), m ∈ 𝔽 → n ∈ 𝔽 → m + n ≤ 𝕊 m → m+n ∈ 𝔽 → ¬ n = zero → n = one:=
  assume m n,
  begin
    intros hm hn h3 h20 h4,
    have h3copy:= h3,
    rw le_definition at h3copy,
    cases h3copy with a h10,
    cases h10 with b h11,
    rcases h11 with ⟨ h12, h13, h14⟩,
    have h15:= successorF M m hm ⟨ b, h13⟩,
    have h200:= orderbyaddition M (𝕊 m) h15 (m+n) h20 ,
    rw h200 at h3,
    cases h3 with k h16,
    cases h16 with h17 h18,
    have h5:= nonzeroissuccessor M n hn h4,
    cases h5 with r h6,
    cases h6 with h7 h8,
    rw h8 at *, 
    rw addition_equation M at h18,
    rw←  successor_shift M at h18,
    rw addition_equation at h18,
    have h19 :=subterms3 M m r hm h7 h20,
    have h18copy:= h18,
    rw← addition_equation  at h18copy,
    have h20:= subterms3 M (m+r) k h19 h17,
    rw h18copy at h20,
    have h21:= h20 h15,
    have h22: 𝕊 (m+r+k) ∈ 𝔽:=
      begin
        rw h18,
        exact h15,
      end,
    have h15:= successoroneone M (m+r+k) m h21 hm (cardinalsinhabited M (𝕊 (m+r+k)) h22) (cardinalsinhabited M (𝕊 m) h15),
    rw← h15 at h18,
    rw associativityNF at h18,
    have h23: m + (r+k) = m + zero:=
      begin
        rw right_identityNF,
        exact h18,
      end,
    have h24: r+k + m = zero + m:=
      begin
        rw commutativityNF,
        have h25:zero + m = m + zero:=
          begin
            rw right_identityNF,
            rw left_identityNF,
          end,
        rw← h25 at h23,
        exact h23,
      end,
    have h25:= subterms M m r k hm h7 h17 h21,
    cases h25 with h26 h27,
    have h28: r+k + m ∈ 𝔽 :=
      begin
        rw commutativityNF,
        rw←  associativityNF,
        exact h21,
      end,
    have h30:= subtraction M m hm (r+k) zero h27 (zeroF M) h28 h24,
    have h33:= adds_to_zero M r k,
    rw h30 at h33,
    simp at h33,
    rw h33,
    rw one_definition,
  end


lemma dedekind2_helper: ∀(Y:M), Y ∈ FINITE M → ∀ (X:M), X ∈ FINITE M →
  Nc M X ≤ Nc M Y → 
  ∀ (f:M), f ∈ FUNC → Rel f → dom f ⊆ X → 
  (∀ (x:M), x ∈ X → ∃ (y:M), y ∈ Y ∧ ‹ x,y› ∈ f) →
  (∀ (y:M), y ∈ Y → ∃ (x:M), x ∈ X ∧ ‹ x,y› ∈ f) →
  (∀ (y:M), y ∈ Y → ∀  (x z:M), x ∈ X → z ∈ X → ‹ x,y› ∈ f → ‹ z,y› ∈ f → x=z):=
  begin
    have base: Λ ∈ W_dedekind2 M:=
      begin
        rw W_dedekind2_members,
        split,
        {
          exact lambda_finite M,
        },
        {
          intros X hX hsize f hfunc hrel hdom h4 h5 y hy,
          have h6:= emptyset_axiom y,
          contradiction, 
        }
      end,
    have step: adjoin_closed M (W_dedekind2 M):=
      begin
        unfold adjoin_closed,
        intros B a h,
        cases h with h2 h3,
        rw W_dedekind2_members at h2,
        cases h2 with h4 h5,
        rw W_dedekind2_members,
        split,
        {
          exact finite_adjoin M B a ⟨ h4, h3⟩, 
        },
        {
          intros X hX hsize f hf hrel hdom hmaps honto,
          set Z:= dom (f ∩ (X × (single a))) with h50,
          have h70: ∀(x:M), x ∈ Z ↔ x ∈ X ∧ ‹ x, a › ∈ f:=
            begin
              intro x,
              rw h50,
              rw domain_axiom, 
              { 
                simp_rw intersection_axiom,
                simp_rw product_axiom,
                split,
                {
                  intros h,
                  cases h with y h7,
                  cases h7 with h8 h9,
                  cases h9 with p h10,
                  cases h10 with q h11,
                  rw singleton1 at h11,
                  rw ordered_pair_equality at h11,
                  rcases h11 with ⟨ h12, h13, h14, h15⟩,
                  rw← h14 at *,
                  rw← h15 at *,
                  rw h13 at *,
                  exact ⟨ h12, h8⟩,
                },
                {
                  intros h,
                  cases h with h7 h8,
                  use a,
                  split,
                  {
                    exact h8,
                  },
                  {
                    use x, use a,
                    rw singleton1,
                    simp,
                    exact h7,
                  }
                }
              },
              {
                rw Rel_definition,
                intros z,
                rw intersection_axiom,
                rw product_axiom,
                intros h,
                cases h with h7 h8,
                cases h8 with p h9,
                cases h9 with q h10,
                use p, use q,
                exact h10.right.right,
              }
            end,
          have h84: X = (Z ∪ (X-Z)):=
            begin
              rw full_extensionality,
              intro x,
              rw binary_union_axiom,
              rw minus_members,
              rw h70 x,
              split,
              {
                intro hx,
                have h8:= hmaps x hx,
                cases h8 with y h9,
                cases h9 with h10 h11,
                have h77 := finitedecidable M  (B ∪ (single a)) (finite_adjoin M B a ⟨ h4, h3⟩),
                rw decidable_members at h77,
                have h12: a ∈ B ∪ (single a):=
                  begin
                    rw binary_union_axiom,
                    right,
                    rw singleton1,
                  end,
                have h78:= h77 y a ⟨ h10, h12⟩, 
                cases h78 with h79 h80,
                {
                  rw h79 at *,
                  left,
                  exact ⟨ hx, h11⟩,
                },
                {
                  right,
                  split,
                  {
                    exact hx,
                  },
                  {
                    intros h13,
                    cases h13 with h14 h15,
                    rw FUNC_members at hf,
                    have h16:= hf x y a h11 h15,
                    contradiction,
                  }
                }
              },
              {
                intros h8,
                cases h8 with h9 h10,
                {
                  exact h9.left,
                },
                {
                  exact h10.left,
                }
              }
            end,
          have h80: Z ⊆ X:=
            begin
              rw subset_definition,
              intro t,
              rw h84,
              rw binary_union_axiom,
              intros h,
              left,
              exact h,
            end,
          have h81:  separable_subset M Z X:=
            begin
              unfold separable_subset,
              exact ⟨ h80, h84⟩, 
            end,
          have h85:= separablefinite M X hX Z h80 h81,
          have h82: X - Z ⊆ X:=
            begin
              rw subset_definition,
              intro t,
              rw minus_members,
              rw h84,
              intro h,
              cases h with h90 h91,
              exact h90,
            end,
          have h79: ∀ (x:M), x ∈ X → x ∈ Z ∨ ¬ x ∈ Z:=
            begin
              intros u hu,
              rw full_extensionality at h84,
              rw h84 u at hu,
              rw binary_union_axiom at hu,
              cases hu with h120 h121,
              {
                left, 
                exact h120,
              },
              {
                rw minus_members at h121,
                right,
                exact h121.right,
              }
            end,
          have h83: separable_subset M (X-Z) X:=
            begin
              unfold separable_subset,
              split,
              {
                exact h82,
              },
              {
                rw full_extensionality,
                intro t,
                split,
                {
                  intro h,
                  rw binary_union_axiom,
                  rw minus_members,
                  have h123:= h79 t h,
                  cases h123 with h124 h125,
                  {
                    right,
                    rw minus_members,
                    split,
                    {
                      exact h,
                    } ,
                    {
                      intro h126,
                      rw minus_members at h126,
                      cases h126 with h127 h128,
                      contradiction,
                    }
                  },
                  {
                    left,
                    exact ⟨ h, h125⟩,
                  }
                },
                {
                  intro h,
                  rw binary_union_axiom at h,
                  cases h with h127 h128,
                  {
                    rw minus_members at h127,
                    exact h127.left,
                  },
                  {
                    rw minus_members at h128,
                    exact h128.left, 
                  }
                }
              }
            end,
          have h86:= separablefinite M X hX (X-Z) h82 h83,
          set g:= restrict f (X-Z) with h51,
          have h101: a ∈ B ∪ (single a):=
            begin
              rw binary_union_axiom,
              right,
              rw singleton1, 
            end,
           
          
          have h100: ∃(u:M), u ∈ Z:=
            begin
              have h102:= honto a h101,
              cases h102 with u h103,
              use u,
              rw h70,
              exact h103,
            end,
          have h104: Nc M X = Nc M (Z ∪ (X-Z)):=
            begin
              rw←  h84,
            end,
         
          have h105: Z ∩ (X - Z) = Λ:=
            begin
              rw full_extensionality,
              intro t,
              rw intersection_axiom,
              rw minus_members,
              split,
              {
                intro h,
                rcases h with ⟨ h30, h31,h32⟩,
                contradiction,
              },
              {
                intro h,
                have h30:= emptyset_axiom t,
                contradiction,
              }
            end,
          have h106:= cardinality_additive M Z (X-Z) h85 h86 h105,
          rw← h104 at h106,
          have h103: Nc M (X-Z) < Nc M X:=
            begin
              have h20 := h80,
              have h21 := h84,
              have h22 := h100,
              rw lessthan_definition,
              split,
              {
                rw le_definition,
                use X-Z, use X,
                repeat{split},
                {
                  exact xinNcx M (X-Z),
                },
                {
                  exact xinNcx M X,
                },
                {
                  exact h82,
                },
                {
                  rw full_extensionality,
                  intro t,
                  have h87:= h79 t,
                  split,
                  {
                    intro h,
                    have h88:= h87 h,
                    cases h88 with h89 h90,
                    {
                      rw binary_union_axiom,
                      right,
                      rw minus_members,
                      split,
                      {
                        exact h,
                      },
                      {
                        rw minus_members,
                        intro h91,
                        cases h91 with h92 h93,
                        contradiction,
                      }
                    },
                    {
                      rw binary_union_axiom,
                      left,
                      rw minus_members,
                      exact ⟨ h, h90⟩,
                    }
                  },
                  {
                    intro h,
                    rw binary_union_axiom at h,
                    cases h with h90 h91,
                    {
                      rw minus_members at h90,
                      exact h90.left,
                    },
                    {
                      rw minus_members at h91,
                      exact h91.left,
                    }
                  }
                }
              },
              {
                intro h,
                have h107:= xinNcx M (X-Z),
                have h108:= xinNcx M X,
                have h109:= finitecardinals3 M X hX,
                have h110:= finitecardinals3 M (X-Z) h86,
                rw h at h107,
                have h120:= finitecardinals2 M X (X-Z) (Nc M X) h109 h108 h107,
                have h121: infinite M X:=
                  begin
                    unfold infinite,
                    use X-Z,
                    split,
                    {
                      rw subset_definition,
                      intro t,
                      intro h121,
                      rw minus_members at h121,
                      exact h121.left,
                    },
                    {
                      split,
                      {
                        cases h100 with u h122,
                        intro h123,
                        rw full_extensionality at h123,
                        specialize h123 u,
                        have h124:= member_subset M Z X u h20 h122,
                        rw h123 at h124,
                        rw minus_members at h124,
                        cases h124 with h125 h126,
                        contradiction,
                      },
                      {
                        exact h120,
                      }
                    }
                  end,
                have h122:= infiniteimpliesnotfinite M X h121,
                contradiction, 
              }             
            end, 
          have h107: Nc M (B ∪ (single a)) = 𝕊 (Nc M B):=
            adjoin_cardinality M B a h4 h3,
          rw h107 at hsize, 
          have h110:= finitecardinals3 M (X-Z) h86,
          have h111:= finitecardinals3 M X hX,
          have h112:= finitecardinals3 M B h4,
          have h113: B ∪ (single a) ∈ 𝕊 (Nc M B):=
            begin
              rw successor_members,
              use B, use a,
              simp,
              split,
              {
                exact x_in_Ncx M B,
              },
              {
                exact h3,
              }
            end,
          have h114:= successorF M (Nc M B) h112 ⟨ B ∪ (single a), h113⟩, 
          have h108:= le_transitive2 M (Nc M (X-Z)) (Nc M X) (𝕊 (Nc M B)) h110 h111 h114 h103 hsize,
          have h87: Nc M (X-Z) ≤  Nc M B:=
            begin
              have h109:= lessthansuccessor3 M (Nc M (X-Z)) (Nc M B) h110 h112 ⟨ B ∪ (single a), h113⟩, 
              rw  h109 at h108,
              rw letolessthan,
              {
                exact h108,
              },
              {
                exact h110,
              },
              {
                exact h112,
              }
            end,
          have hrelg: Rel g:=
            begin
              rw h51,
              rw Rel_definition,
              intros z h40,
              rw restrict_definition at h40,
              rw intersection_axiom at h40,
              cases h40 with h41 h42,
              rw product_axiom at h42,
              cases h42 with a h43,
              cases h43 with b h44,
              use a, use b,
              exact h44.right.right,
            end,
          have hfuncg: g ∈ FUNC:=
            begin
              rw FUNC_members,
              intros x y z h88 h89,
              rw h51 at h88 h89, 
              rw restriction at h89 h88,
              cases h88 with h90 h91,
              cases h89 with h92 h93,
              rw FUNC_members at hf,
              have h94:= hf x y z h90 h92,
              exact h94,
            end,
          have hdomg: dom g ⊆ X-Z:=
            begin
              rw subset_definition,
              intro t,
              intro h88,
              rw domain_axiom g hrelg at h88,
              cases h88 with y h89, 
              rw h51 at h89,
              rw restriction at h89,
              exact h89.right,
            end,   
          have h7: maps M g (X-Z) B:=
            begin
              unfold maps,
              split,
              {
                exact hrelg,
              },
              {
                split,
                {
                  intros x y h88,
                  cases h88 with h89 h90,
                  rw h51 at h90,
                  rw restriction at h90,
                  cases h90 with h91 h92,
                  rw minus_members at h92,
                  cases h92 with h93 h94,
                  rw h50 at h94,
                  rw domain_axiom at h94,
                  {
                    rw minus_members at h89,
                    cases h89 with h95 h96,
                    rw h70 at h96,
                    have h97: ¬ ‹ x,a› ∈ f:=
                      begin
                        intro h98,
                        rw FUNC_members at hf,
                        have h99:= hf x y a h91 h98,
                        rw h99 at *,
                        apply h94,
                        use a,
                        rw intersection_axiom,
                        split,
                        {
                          exact h91,
                        },
                        {
                          rw product_axiom,
                          use x, use a,
                          rw singleton1,
                          simp,
                          exact h95,
                        }
                      end,
                    have h98:= hmaps x h93,
                    cases h98 with p h99,
                    cases h99 with h120 h121,
                    rw FUNC_members at hf,
                    have h122:= hf x y p h91 h121,
                    rw h122 at *,
                    rw binary_union_axiom at h120,
                    cases h120 with h123 h124,
                    {
                      exact h123,
                    },
                    {
                      rw singleton1 at h124,
                      rw h124 at *,
                      contradiction, 
                    }
                  },
                  {
                    rw Rel_definition,
                    intros z h95,
                    rw intersection_axiom at h95,
                    cases h95 with h96 h97,
                    rw product_axiom at h97,
                    cases h97 with p h98,
                    cases h98 with q h99,
                    use p, use q,
                    exact h99.right.right, 
                  }
                },
                {
                  split,
                  {
                    intros x y z h,
                    rcases h with ⟨ h120, h121, h122⟩,
                    rw h51 at h121 h122,
                    rw restriction at h122 h121,
                    cases h121 with h123 h124,
                    cases h122 with h125 h126,
                    rw FUNC_members at hf,
                    have h127:= hf x y z h123 h125,
                    exact h127,
                  },
                  {
                    intros x h120,
                    rw minus_members at h120,
                    cases h120 with h121 h122,
                    have h123:= hmaps x h121,
                    cases h123 with y h124,
                    use y,
                    cases h124 with h125 h126,
                    rw binary_union_axiom at h125,
                    rw singleton1 at h125,
                    cases h125 with h127 h128,
                    {
                      split,
                      {
                        exact h127,
                      },
                      {
                        rw h51,
                        rw restriction,
                        rw minus_members,
                        exact ⟨ h126, h121, h122⟩, 
                      }
                    },
                    {
                      rw h128 at *,
                      rw h70 at h122,
                      have h123: false:=
                        begin
                          apply h122,
                          exact ⟨ h121, h126⟩,
                        end,
                      contradiction, 
                    }
                  }
                }
              }
            end,
          have h8: onto M g (X-Z) B:=
            begin
              unfold onto,
              intros y hy,
              have h120: y ∈ B ∪ (single a):=
                begin
                  rw binary_union_axiom,
                  left,
                  exact hy,
                end,
              have h121:= honto y h120,
              cases h121 with x h122,
              cases h122 with h123 h124,
              use x,
              split,
              {
                rw minus_members,
                split,
                {
                  exact h123,
                },
                {
                  intro h125,
                  rw h70 at h125,
                  cases h125 with h126 h127,
                  rw FUNC_members at hf,
                  have h128:= hf x y a h124 h127,
                  rw h128 at *,
                  contradiction,
                }
              },
              {
                rw h51,
                rw restriction,
                split,
                {
                  exact h124,
                },
                {
                  rw minus_members,
                  split,
                  {
                    exact h123,
                  },
                  {
                    intro h125,
                    rw h70 at h125,
                    cases h125 with h126 h127,
                    rw FUNC_members at hf,
                    have h128:= hf x y a h124 h127,
                    rw h128 at *,
                    contradiction, 
                  }
                }
              }
            end,
          have h7copy:= h7,
          unfold maps at h7copy,
          rcases h7copy with ⟨ h40, h41, h42, h43⟩,
          unfold onto at h8, 
          have h6:= h5 (X-Z) h86 h87 g hfuncg hrelg hdomg h43 h8, 
          have h9: oneone M g (X-Z) B:=
            begin
              unfold oneone,
              split,
              {
                exact h7,
              },
              {
                split,
                { 
                  intros x u y h,
                  rcases h with ⟨ h30, h31, h32⟩, 
                  have h33: u ∈ dom g:=
                    begin
                      rw domain_axiom g hrelg,
                      exact ⟨ y, h31⟩, 
                    end,
                  have h34: u ∈ X - Z:=
                    member_subset M (dom g) (X-Z) u hdomg h33,
                  have h42:= h41 x y ⟨ h32, h30⟩,
                  have h43:= h6 y h42 x u h32 h34 h30 h31,
                  exact h43,
                },
                {
                  intros x y h,
                  cases h with h33 h34,
                  rw h51 at h33,
                  rw restriction at h33,
                  exact h33.right,
                }
              }
            end,
          have h10: similarity M g (X-Z) B:=
            begin
              unfold similarity,
              split,
              { 
                exact h9,   
              },
              {
                exact h8,
              }
            end,
          have h11: similar M (X-Z) B:=
            begin
              unfold similar,
              exact ⟨ g, h10⟩, 
            end,
          have h12: Nc M (X-Z) = Nc M B:=
            begin
              have h35: X-Z ∈ Nc M (X-Z):=
                xinNcx M (X-Z), 
              have h36:= xinNcx M B,
              have h37:= finitecardinals3 M (X-Z) h86,
              have h38:= finitecardinals3 M B h4,
              have h34:= finitecardinals0 M (Nc M (X-Z)) (X-Z) B h37 h35 h11,
              have h39: B ∈ (Nc M (X-Z)) ∩ (Nc M B):=
                begin
                  rw intersection_axiom,
                  exact ⟨ h34, h36⟩,
                end, 
              have h60:= cardinalsdisjoint M (Nc M (X-Z)) (Nc M B) B h37 h38 h39,
              exact h60,
            end, 
          have h13: 𝕊 (Nc M (X-Z)) = 𝕊 (Nc M B):=
            begin
              rw h12,
            end,
          have h14:  Nc M X = Nc M (X-Z) + Nc M Z:=
            begin
              have h20: (X-Z) ∩ Z = Λ :=
                begin
                  rw full_extensionality,
                  intro t,
                  rw intersection_axiom,
                  rw minus_members,
                  split,
                  {
                    intro h,
                    cases h with h30 h31,
                    cases h30 with h32 h33,
                    contradiction,
                  },
                  {
                    intro h,
                    have h3:= emptyset_axiom t,
                    contradiction,
                  }
                end,
              have h15:= cardinality_additive M (X-Z) Z h86 h85 h20,
              rw union_commutative at h15,
              rw←  h84 at h15,
              exact h15, 
            end, 
          have h15: Nc M X = Nc M B + Nc M Z:=
            begin
              rw h14, 
              rw h12,
            end,
          rw h15 at hsize,
          have h16:= finitecardinals3 M Z h85,
          rw h15 at h111,
          have h17: ¬ Nc M Z = zero:=
            begin
              intro h,
              cases h100 with u h101,
              rw zero_definition at h,
              have h102:= xinNcx M Z,
              rw h at h102,
              rw singleton1 at h102,
              rw h102 at h101,
              have h103:= emptyset_axiom u,
              contradiction,
            end,
          have h18:= nothingbetween M (Nc M B) (Nc M Z) h112 h16 hsize h111 h17, 
          have h19:= xinNcx M Z,
          rw h18 at h19,
          rw one_members at h19,
          cases h19 with c h20,
          have h70copy:= h70,
          simp_rw h20 at h70,
          simp_rw singleton1 at h70,
          intros y h,
          intros x z hx hz h30 h31,
          rw binary_union_axiom at h,
          cases h with h32 h33,
          {
            have h34: ‹ x,y › ∈ g:=
              begin
                rw h51,
                rw restriction,
                split,
                {
                  exact h30,
                },
                {
                  rw minus_members,
                  split,
                  { 
                    exact hx,
                  },
                  {
                    intro h,
                    rw (h70copy x) at h,
                    cases h with h33 h34,
                    rw FUNC_members at hf,
                    have h35:= hf x y a h30 h34,
                    rw h35 at *,
                    contradiction, 
                  }
                }
              end,
            have h134: ‹ z,y › ∈ g:=
              begin
                rw h51,
                rw restriction,
                split,
                {
                  exact h31,
                },
                {
                  rw minus_members,
                  split,
                  { 
                    exact hz,
                  },
                  {
                    intro h,
                    rw (h70copy z) at h,
                    cases h with h33 h34,
                    rw FUNC_members at hf,
                    have h35:= hf z y a h31 h34,
                    rw h35 at *,
                    contradiction, 
                  }
                }
              end,
            unfold oneone at h9, 
            rcases h9 with ⟨ h135, h136, h137⟩,
            have h138:= h136 x z y, 
            have h139: x ∈ X - Z:=
              begin
                have h140:= hdomg,
                have h141: x ∈ dom g:=
                  begin
                    rw domain_axiom g hrelg,
                    exact ⟨ y, h34⟩,
                  end,
                have h142:= member_subset M (dom g)(X-Z) x hdomg h141,
                exact h142,
              end,
            have h143:= h138 ⟨ h34, h134, h139⟩,
            exact h143,
          },
          {
            rw singleton1 at h33,
            rw h33 at *,
            have h34:= (h70 x).mpr ⟨ hx, h30⟩,
            have h35:= (h70 z).mpr ⟨ hz, h31⟩, 
            rw h34,
            rw h35,
          }
        }
      end,
    intro Y, 
    have h2: (FINITE M)⊆ W_dedekind2 M := (finite_conditions M) (W_dedekind2 M)  step base, 
    rw subset_definition at h2, 
    specialize h2 Y,
    rw (W_dedekind2_members M) at h2,  
    intro h3,
    have h4:= h2 h3, 
    cases h4 with h5 h6, 
    exact h6,
  end


theorem dedekind2: ∀ (X f:M), X ∈ FINITE M → f ∈ FUNC → Rel f  → dom f ⊆ X  → maps M f X X → onto M f X X → oneone M f X X:=
  assume X f,
  begin
    intros hX hf hrel hdom hmaps,
    have h2:= finitecardinals3 M X hX,
    have h3:= le_reflexive M (Nc M X) h2,
    intro honto,
    unfold onto at honto,
    have hmapscopy:= hmaps,
    unfold maps at hmaps,
    rcases hmaps with ⟨ h4, h5, h6, h7⟩,
    have h:= dedekind2_helper M X hX X hX h3 f hf hrel hdom h7 honto,
    unfold oneone,
    split,
    {
      exact hmapscopy,
    },
    {
      split,
      {
        intros x z y h100,
        rcases h100 with ⟨ h102, h103, h104⟩,
        have h105: x ∈ dom f:=
          begin
            rw domain_axiom f hrel,
            exact ⟨ y, h102⟩,
          end,
        have h106:= member_subset M (dom f) X x hdom h105,
        have h205: z ∈ dom f:=
          begin
            rw domain_axiom f hrel,
            exact ⟨ y, h103⟩,
          end,
        have h206:= member_subset M (dom f) X z hdom h205,
        have h107:= h5 x y ⟨ h104, h102⟩,
        have h108:= h y h107 x z h106 h206 h102 h103,
        exact h108,
      },
      {
        intros x y h8,
        cases h8 with h9 h10,
        have h105: x ∈ dom f:=
          begin
            rw domain_axiom f hrel,
            exact ⟨ y, h9⟩,
          end,
         have h106:= member_subset M (dom f) X x hdom h105,
         exact h106,
      }
    }
  end 

#axioms_all 