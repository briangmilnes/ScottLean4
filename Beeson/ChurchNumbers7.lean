import ChurchNumbers6

variables (M:Type) [Model M] (a b x y z u v w X R W κ μ ℓ : M)
-- using ℓ where the source text has λ because you can't use λ for a variable.

open Model 

theorem main: ( ∀ (x:M), x ∈ ℕℕ →  Ap ( Ap x (SG M)) ChurchZero = x) →
¬ ℕℕ ∈ FINITE M:=
  assume ChurchCountingAxiom hfinite,
  begin
    have h5:= kinstem M hfinite,
    cases h5 with k h6,
    cases h6 with n h7,
    rcases h7 with ⟨ hk2, hn, hkn, hskn, hk⟩,
    have h20:= mexists M hfinite k n hk hn hkn hskn,
    cases h20 with m h21,
    rcases h21 with ⟨ hm, hkplusm, hmin⟩,
    rw sym at hkplusm,
    have h23: ∀ (l:M), k ⊕ l = n ↔ n = k ⊕ l:=
      assume l,
      begin
        split,
        {
          intros h,
          symmetry,
          exact h,
        },
        {
          intros h,
          symmetry,
          exact h,
        },
      end,
    simp_rw h23 at hmin,
    have h4523:= orderm M hfinite k n hk hn hkn hskn ChurchCountingAxiom m hm hkplusm hmin,
    set X:= LOOP n - (single n) with h50,
    have h24:= nneqzero M k n hk hn hkn hskn,
    have h101:= L1 M k n hk hn hkn hskn,
    have h80 := finitedecidable M ℕℕ hfinite,
    rw decidable_members at h80,
    have h25:= looponto M  k n hk hn hkn hskn n h101.left,  
    cases h25 with p h26,
    cases h26 with hp hsp,
    set f:=  ((SG M) ∩ (X × ℕℕ)) - (single ‹ p,  n› ) ∪ single ‹ p, S n ›  with h51,
    have hRel: Rel f:= 
      begin
        rw h51,
        rw Rel_definition,
        intros z h,
        rw binary_union_axiom at h,
        rw minus_members at h,
        cases h with h2 h3,
        {
          cases h2 with h4 h5,
          rw intersection_axiom at h4,
          cases h4 with h5 h6,
          rw product_axiom at h6,
          cases h6 with a h8,
          cases h8 with b h7,
          use a, use b,
          exact h7.right.right,
        },
        {
          rw singleton1 at h3,
          use p, use S n,
          exact h3,
        } 
      end,
    have hFUNC: f ∈ FUNC:= 
      begin
        rw FUNC_members,
        intros x y z hxy hxz,
        rw binary_union_axiom at hxy hxz,
        rw minus_members at hxy hxz, 
        cases hxy with h60 h61,
        {
          cases h60 with h62 h63,
          cases hxz with h64 h65,
          {
            cases h64 with h66 h67,
            rw intersection_axiom at h62 h66,
            cases h66 with h68 h69,
            cases h62 with h70 h71,
            have h72:= SGFUNC M,
            rw FUNC_members at h72,
            exact h72 x y z h70 h68,
          },
          { 
            rw singleton1 at h65,
            rw ordered_pair_equality at h65,
            cases h65 with h66 h67,
            rw h66 at *,
            rw intersection_axiom at h62,
            cases h62 with h68 h69,
            rw SG_members at h68,
            cases h68 with a h70,
            cases h70 with h71 ha,
            rw ordered_pair_equality at h71,
            cases h71 with h72 h73,
            rw← h72 at *,
            rw hsp at *,
            rw singleton1 at h63,
            rw h73 at *,
            contradiction,
          }
        },
        {
          rw singleton1 at h61,
          rw ordered_pair_equality at h61,
          cases h61 with h70 h71,
          rw h70 at *,
          rw h71 at *,
          rw or_comm at hxz,
          cases hxz with h72 h73,
          {
            rw singleton1 at h72,
            rw ordered_pair_equality at h72,
            simp at h72,
            symmetry,
            exact h72,
          },
          {
            cases h73 with h74 h75,
            rw singleton1 at h75,
            rw ordered_pair_equality at h75,
            simp at h75, 
            rw intersection_axiom at h74,
            cases h74 with h76 h77,
            rw SG_members at h76,
            cases h76 with q h78,
            cases h78 with h79 h82,
            rw ordered_pair_equality at h79,
            cases h79 with h83 h84,
            rw h83 at *,
            rw h84 at *,
            contradiction, 
          }
        } 
      end,
    have hdom: dom f ⊆ X := 
      begin
        rw subset_definition,
        intros t h,
        rw domain_axiom f hRel at h,
        cases h with y h4,
        rw h51 at h4,
        rw h50,
        rw binary_union_axiom at h4,
        rw or_comm at h4,
        cases h4 with h5 h6,
        {
          rw singleton1 at h5,
          rw ordered_pair_equality at h5,
          cases h5 with h6 h7,
          rw h6 at *,
          rw h7 at *,
          rw minus_members,
          rw singleton1,
          split,
          {
            exact hp,
          },
          {
            intro h,
            rw h at *,
            have h10:= snneqn M n hn,
            contradiction,
          }
        },
        {
          rw minus_members at h6,
          cases h6 with h7 h8,
          rw singleton1 at h8,
          rw ordered_pair_equality at h8,
          rw intersection_axiom at h7,
          cases h7 with h9 h10,
          rw pair_in_product at h10,
          cases h10 with h11 hy,
          rw h50 at h11,
          exact h11, 
        }
      end,
    have hrange: range f ⊆ X:= 
      begin
        rw subset_definition,
        intros t h,
        rw range_axiom f hRel at h,
        cases h with x h90,
        rw h51 at h90,
        rw binary_union_axiom at h90,
        cases h90 with h91 h92,
        {
          rw minus_members at h91,
          cases h91 with h93 h94,
          rw singleton1 at h94,
          rw ordered_pair_equality at h94,
          rw intersection_axiom at h93,
          cases h93 with h95 h96,
          rw SG_members at h95,
          cases h95 with q h97,
          cases h97 with h98 hq,
          rw ordered_pair_equality at h98,
          cases h98 with h99 h100,
          rw h99 at *,
          rw h100 at *,
          rw pair_in_product at h96,
          cases h96 with h102 h103,
          rw h50,
          rw h50 at h102,
          rw minus_members at h102,
          cases h102 with h103 h104,
          rw minus_members,
          rw singleton1,
          split,
          {
            exact h101.right q h103,
          },
          {
            intro h,
            rw← h at *,
            simp at h94,
            rw singleton1 at h104,
            have h105:= looponeone M hfinite k (S q) hk hn hkn hskn p q hp h103 hsp,
            rw sym at h105,
            contradiction,
          }
        },
        {
          rw singleton1 at h92,
          rw ordered_pair_equality at h92,
          cases h92 with h93 h94,
          rw h50,
          rw minus_members,
          rw singleton1,
          rw h94,
          split,
          {
            have h95:= h101.left,
            exact h101.right n h95,
          },
          {
            have h95:= snneqn M n hn,
            exact h95,
          }
        }
      end,
    have h17: X ⊆ LOOP n:=
      begin
        rw subset_definition,
        intros t h,
        rw h50 at h,
        rw minus_members at h,
        exact h.left,
      end,
    have hmaps: maps M f X X:=
      begin
        unfold maps,
        split,
        {
          exact hRel,
        },
        {
          split,
          {
            intros x y h,
            have h20: y ∈ range f:=
              begin
                rw range_axiom f hRel,
                use x,
                exact h.right,
              end,
            have h21:= member_subset M (range f) X y hrange h20, 
            exact h21,
          },
          { 
            split,
            {
              rw FUNC_members at hFUNC,
              intros x y z h,
              rcases h with ⟨ h30, h31, h32⟩,
              exact hFUNC x y z h31 h32,
            },
            {
              intros x hx,
              rw h50 at hx,
              rw minus_members at hx,
              cases hx with h20 h21,
              rw singleton1 at h21,
              have hx:= member_subset M (LOOP n)  ℕℕ x (LN M k n hk hn hkn hskn) h20,
              have hp2:= member_subset M (LOOP n)  ℕℕ p (LN M k n hk hn hkn hskn) hp,
              have h81:= h80 x p ⟨ hx, hp2⟩, 
              cases h81 with h82 h83,
              {
                rw h82 at *,
                use S n,
                split,
                {
                  rw h50,
                  rw minus_members,
                  rw singleton1,
                  split,
                  {
                    exact h101.right n h101.left,
                  },
                  {
                    exact snneqn M n hn,
                  }
                },
                {
                  rw h51,
                  rw binary_union_axiom,
                  right,
                  rw singleton1,
                }
              },
              {
                use S x,
                split,
                {
                  rw h50,
                  rw minus_members,
                  split,
                  {
                    exact h101.right x h20,
                  },
                  {
                    intro h,
                    rw singleton1 at h,
                    have h22:= looponeone M hfinite k n hk hn hkn hskn x p h20 hp,
                    rw hsp at h22,
                    rw h at h22, 
                    simp at h22,
                    contradiction,
                  }
                },
                {
                  rw h51,
                  rw binary_union_axiom,
                  left,
                  rw minus_members,
                  rw singleton1,
                  split,
                  {
                    rw intersection_axiom,
                    split,
                    { 
                      rw SG_members,
                      use x,
                      simp,
                      exact hx,
                    },
                    {
                      rw pair_in_product,
                      split,
                      {
                        rw h50,
                        rw minus_members,
                        rw singleton1,
                        exact ⟨ h20, h21⟩, 
                      },
                      {
                        exact successorN M x hx,
                      }
                    }
                  },
                  {
                    rw ordered_pair_equality,
                    intro h,
                    exact h83 h.left,
                  }
                }
              }
            }
          }
        }
      end,
    have honeone: oneone M f X X:= 
      begin
        unfold oneone,
        split,
        {
          exact hmaps,
        },
        {
          rw and_comm,
          split,
          {
            intros x y h,
            cases h with h3 h4,
            have h5: x ∈ dom f:=
              begin
                rw domain_axiom f hRel,
                use y,
                exact h3,
              end,
            exact member_subset M (dom f) X x hdom h5,
          },
          {
            intros x u y h,
            rcases h with ⟨h2,h3,h4⟩,
            have h5: y ∈ range f:=
              begin
                rw range_axiom f hRel,
                use x,
                exact h2,
              end,
            have h6:= member_subset M (range f) X y hrange h5,
            have h7: X ⊆ ℕℕ :=
              begin
                rw subset_definition,
                intros t h,
                rw h50 at h,
                rw minus_members at h,
                cases h with h10 h11,
                have h12:= LN M k n hk hn hkn hskn,
                exact member_subset M (LOOP n) ℕℕ t h12 h10,
              end,
            have hy:= member_subset M X ℕℕ y h7 h6,
            have h81:= h80 y (S n) ⟨ hy, successorN M n hn⟩,
            have E4545: ∀ (x:M), ‹ x, S n › ∈ f → x = p:=
              begin
                intros t h,
                rw h51 at h,
                rw binary_union_axiom at h,
                cases h with h20 h21,
                {
                  rw minus_members at h20,
                  cases h20 with h22 h23,
                  rw intersection_axiom at h22,
                  cases h22 with h24 h25,
                  rw pair_in_product at h25,
                  cases h25 with h26 h27,
                  rw SG_members at h24,
                  cases h24 with a h28,
                  rw ordered_pair_equality at h28,
                  cases h28 with h29 h30,
                  cases h29 with h31 h32,
                  rw← h31 at *,
                  have htloop: t ∈ LOOP n:=
                    member_subset M X (LOOP n) t h17 h26, 
                  have hnloop := h101.left,
                  have h35:= looponeone M hfinite k n hk hn hkn hskn t n htloop hnloop,
                  rw sym at h32,
                  have h36:= h35 h32,
                  rw h36 at *,
                  rw h50 at h26,
                  rw minus_members at h26,
                  cases h26 with h37 h38,
                  rw singleton1 at h38,
                  contradiction,
                },
                {
                  rw singleton1 at h21,
                  rw ordered_pair_equality at h21,
                  exact h21.left,
                }
              end,
            cases h81 with h82 h83,
            { 
              rw h82 at *,
              have h120:= E4545 x h2,
              have h121:= E4545 u h3,
              rw h120,
              rw h121,
            },
            {
              rw h51 at h2 h3,
              rw binary_union_axiom at h2 h3,
              cases h2 with h30 h31,
              {
                rw minus_members at h30,
                cases h30 with h32 h33,
                rw intersection_axiom at h32,
                cases h32 with h34 h35,
                rw SG_members at h34,
                cases h34 with a h36,
                cases h36 with h37 h38,
                rw ordered_pair_equality at h37,
                cases h37 with h39 h42,
                rw← h39 at *,
                cases h3 with h60 h61,
                {
                  rw minus_members at h60,
                  cases h60 with h62 h63,
                  rw intersection_axiom at h62,
                  cases h62 with h64 h65,
                  rw SG_members at h64,
                  cases h64 with b h66,
                  cases h66 with h67 h68,
                  rw ordered_pair_equality at h67,
                  cases h67 with h69 h43,
                  rw← h69 at *,
                  rw h42 at *,
                  have hxloop:= member_subset M X (LOOP n) x h17 h4,
                  rw pair_in_product at h65,
                  have huloop:= member_subset M X (LOOP n) u h17 h65.left,
                  have h35:= looponeone M hfinite k n hk hn hkn hskn x u hxloop huloop h43,
                  exact h35, 
                },
                {
                  rw singleton1 at h61,
                  rw ordered_pair_equality at h61,
                  cases h61 with h62 h63,
                  rw h42 at *,
                  contradiction,
                }
              },
              {
                rw singleton1 at h31,
                rw ordered_pair_equality at h31,
                cases h31 with h32 h33,
                rw h33 at *,
                contradiction,
              }
            }
          }
        }
      end, 
    have h40: injection M f X:=
      begin
        unfold injection,
        exact ⟨ honeone, hRel, hFUNC, hdom, hrange⟩, 
      end,
    have h41: ¬ m = ChurchZero:=
      begin
        intro h,
        rw h at *,
        rw ChurchZero_equation k hk2 at hkplusm,
        rw sym at hkn,
        contradiction,
      end,
    have h42: n ⊕ m = n :=
      begin
        have h43:= nplusm M hfinite k n hk hn hkn hskn m hm h41 hkplusm,
        symmetry,
        exact h43, 
      end,
    have E4598:= annihilation M n m hn hm h42 X f h40,
    set α:= S n with halpha,
    have h102: α ∈ X:=
      begin
        rw halpha,
        rw h50,
        rw minus_members,
        rw singleton1,
        have hloopn:= h101.left,
        have hloopsn:= h101.right n hloopn,
        exact ⟨ hloopsn, snneqn M n hn ⟩, 
      end,
    have E4424: ∀ (q:M), q ∈ ℕℕ →  ¬ q = n → S q ≺ m → Ap (Ap q f) α = Ap (Ap q (SG M)) α :=
      begin
        have base: ChurchZero ∈ Z_E4424 M f α m n:=
          begin
            rw Z_E4424_members,
            split,
            {
              exact zeroN M,
            },
            { 
              intro h,
              rw zeroAp,
              rw zeroAp,
              intro h2,
              refl, 
            }
          end,
        have step: ∀ (q:M), q ∈ Z_E4424 M f α m n → ¬ (q = n) → S q ∈ Z_E4424 M f α m n:=
          begin
            intros q h4 h61,
            rw Z_E4424_members at h4,
            rw Z_E4424_members,
            cases h4 with hq h5,
            have h200:= decidable0 M q hq,
            split,
            {
              exact successorN M q hq,
            },
            {  
              intros hqn E4628,
              have h7:= successorequation M X f hFUNC hRel hmaps q α hq h102,
              have h9:= xpreceqsx M hfinite k n hk hn hkn hskn (S q) (successorN M q hq) hqn, 
              have h30: S q ≺ S (S q):=
                begin
                  rw prec_definition,
                  split,
                  {
                    exact h9,
                  },
                  {
                    have h31:= snneqn M (S q) (successorN M q hq),
                    rw sym,
                    exact h31,
                  }
                end,
              have h8: S q ≺   m:=
                begin
                  have h90:= xpreceqsx M hfinite k n hk hn hkn hskn q hq h61, 
                  have h10: q ≺ S q:=
                    begin
                      rw prec_definition,
                      split,
                      {
                        exact h90,
                      },
                      {
                        have h11:= snneqn M q hq,
                        rw sym,
                        exact h11,
                      }
                    end,
                  have h20:= prectrans M  hfinite k n hk hn hkn hskn (S q) (S (S q)) m (successorN M q hq) (successorN M (S q) (successorN M q hq)) hm h30 E4628, 
                  exact h20, 
                end, 
              have h20: α ∈ LOOP n:=
                begin
                  rw halpha,
                  have h21:= L1 M k n hk hn hkn hskn,
                  exact h21.right n h21.left,
                end,
              have h9:= xsmapsloop M hfinite k n hk hn hkn hskn q hq α h20, 
              have h10:= LN M k n hk hn hkn hskn,
              have hqsalpha:= member_subset M (LOOP n) ℕℕ (Ap (Ap q (SG M)) α ) h10 h9,
              have hp2:= member_subset M (LOOP n) ℕℕ p h10 hp,
              have h81:= h80 (Ap (Ap q (SG M)) α ) p ⟨ hqsalpha, hp2⟩,
              cases h81 with h30 h31,
              { --case 2a
                have h21:  S (Ap (Ap q (SG M)) α) = S p:=
                  begin
                    rw h30, 
                  end,
                rw hsp at h21,
                have h28: S (S ( Ap (Ap q (SG M)) α)) = α:=
                  begin
                    rw h21,
                  end,
                have h29:= successorequation M (LOOP n) (SG M) (SGFUNC M) (SGRel M) (SGMapsLoop M hfinite k n hk hn hkn hskn) q α hq h20,
                {
                  rw ApSG at h29,
                  rw← h29 at h28,
                  have h32:= successorequation M (LOOP n) (SG M) (SGFUNC M) (SGRel M) (SGMapsLoop M hfinite k n hk hn hkn hskn) (S q) α (successorN M q hq) h20,
                  {
                    rw ApSG at h32,
                    rw← h32 at h28,
                    have hsq:= successorN M q hq,
                    have hssq:= successorN M (S q) hsq,
                    have h33:= successoromitszero M (S q) hsq,
                    have h35:= orderq_helper2 M hfinite k n hk hn hkn hskn  (S(S q)) hssq h33 α h20 h28,
                    {
                      have h36:= orderm M hfinite k n hk hn hkn hskn ChurchCountingAxiom m hm hkplusm hmin, 
                      have h37:= h35 n h101.left,
                      have h38:= h36 (S (S q)) hssq (successoromitszero M (S q) hsq) h37,
                      rw prec_definition at E4628,
                      cases E4628 with h39 h55,
                      rw sym at h55, 
                      have h56:= prectrichotomy2 M hfinite k n hk hn hkn hskn (S (S q)) hssq m hm h55, 
                      have h57:= h56 ⟨ h38, h39⟩, 
                      contradiction,
                    },
                    {
                      rw h29,
                      exact successorN M (Ap (Ap q (SG M)) α) hqsalpha, 
                    }
                  },
                  {
                    exact hqsalpha,
                  }
                }
              },
              { --case 2b
                have h58: α ∈ ℕℕ:=
                  begin
                    rw halpha,
                    exact successorN M n hn,
                  end,
                have h60:= successorequation M X f hFUNC hRel hmaps q α hq h102,
                have h62:= h5 h61 h8, 
                rw h62 at h60,
                have h63: Ap f (Ap (Ap q (SG M)) α) = S (Ap (Ap q (SG M)) α ):=
                  begin
                    have h70:= Apdef M f hFUNC,
                    symmetry, 
                    specialize h70 (Ap (Ap q (SG M)) α) (S (Ap (Ap q (SG M)) α)),
                    apply h70,
                    rw h51,
                    rw binary_union_axiom,
                    left,
                    rw minus_members,
                    split,
                    {
                      rw intersection_axiom,
                      split,
                      {
                        rw SG_members,
                        use Ap (Ap q (SG M)) α,
                        simp,
                        exact hqsalpha,
                      },
                      {
                        rw pair_in_product,
                        split,
                        {
                          rw← h62,
                          have h71:= xfmaps M X f α hFUNC hRel hmaps h102 q hq,
                          exact h71,
                        },
                        {
                          exact successorN M (Ap (Ap q (SG M)) α) hqsalpha, 
                        }
                      }
                    },
                    {
                      intro h,
                      rw singleton1 at h,
                      rw ordered_pair_equality at h,
                      cases h with h76 h77,
                      contradiction,
                    }
                  end,
                rw  h63 at h60,
                have h64:= successorequation M ℕℕ  (SG M) (SGFUNC M) (SGRel M)(SGMaps M) q α hq h58,
                rw ApSG at h64,
                rw← h64 at h60,
                exact h60, 
                exact hqsalpha, 
              }
            }
          end,
        intros q hq,
        have h3:= finiteinduction M hfinite k n hk hn hkn hskn (Z_E4424 M f α m n) ⟨ base, step⟩,
        rw subset_definition at h3,
        have h5:= h3 q hq, 
        rw Z_E4424_members at h5,
        exact h5.right, 
      end,
    have h59: ¬ m = ChurchZero:= 
      begin
        intro h,
        rw h at *,
        rw ChurchZero_equation at hkplusm,
        {
          contradiction,
        },
        {
          exact member_subset M STEM ℕℕ k (SN M) hk, 
        }
      end, 
    have h60:= predecessornotn M hfinite k n hk hn hkn hskn m hm h59,
    cases h60 with m1 h61,
    rcases h61 with ⟨ hm1, h63, hm1not⟩,
    have h64: ¬ m1 = ChurchZero:=
      begin
        intro h,
        rw h at *,
        rw← h63 at *,
        rw ChurchSuccessorShift at hkplusm,
        { rw ChurchZero_equation at hkplusm,
          {
            have h84: S (S k) = S n:=
              begin
                rw← hkplusm,
              end,
            rw halpha at hskn,
            rw hskn at h84,
            have hsn:= successorN M n hn,
            have h85:= snneqn M (S n) hsn,
            contradiction,
          },
          {
            exact successorN M k hk2,
          }
        },
        {
          exact zeroN M,
        },
        {
          exact hk2, 
        }
      end,
    have h65:= predecessornotn M hfinite k n hk hn hkn hskn m1 hm1 h64,
    cases h65 with m2 h66,
    rcases h66 with ⟨ hm2, h67, hm2not⟩,
    have h68: m1 ≺ S m1:=
      begin
        have h69:= xpreceqsx M hfinite k n hk hn hkn hskn m1 hm1 hm1not,
        rw prec_definition,
        split,
        {
          exact h69,
        },
        {
          have h70:= snneqn M m1 hm1,
          rw sym, 
          exact h70,
        }
      end,
    have h69: S m2 ≺ m :=
      begin
        rw h67,
        rw h63 at h68,
        exact h68,
      end,
    have E4455:= E4424 m2 hm2 hm2not h69,
    rw sym at hkplusm,
    have halphaloop:= h101.right n h101.left,
    rw← halpha at halphaloop, 
    have h70:= smloop M hfinite k n hk hn hkn hskn m hm hkplusm α halphaloop,
    have h71: S ( S m2) = m :=
      begin
        rw h67,
        rw h63,
      end,
    rw← h71 at h70,
    have h72:= successorequation M (LOOP n) (SG M) (SGFUNC M) (SGRel M) (SGMapsLoop M hfinite k n hk hn hkn hskn) (S m2) α (successorN M m2 hm2) halphaloop,
    have h74: Ap (Ap (S m2) (SG M)) α ∈ LOOP n:=
    begin
      have h75:= xsmapsloop M hfinite k n hk hn hkn hskn (S m2)(successorN M m2 hm2) α halphaloop,
      exact h75,
    end,
    have h170: LOOP n ⊆ ℕℕ := LN M k n hk hn hkn hskn, 
    have h174: Ap (Ap (S m2) (SG M)) α ∈ ℕℕ :=
      member_subset M (LOOP n) ℕℕ (Ap (Ap (S m2) (SG M)) α) h170 h74,
    rw ApSG M ( Ap (Ap (S m2) (SG M)) α) h174 at h72,
    rw h70 at h72,
    have h73:= halpha,
    rw h72 at h73,
  
    have h76:= looponeone M hfinite k n hk hn hkn hskn (Ap (Ap (S m2) (SG M)) α) n h74 h101.left h73,
    have h77:= hsp,
    rw← h76 at h77,
    have h78:= successorequation M (LOOP n) (SG M) (SGFUNC M) (SGRel M) (SGMapsLoop M hfinite k n hk hn hkn hskn)   m2  α  hm2  halphaloop,
    rw h78 at h77,
      have h79: Ap (Ap m2 (SG M)) α ∈ LOOP n:=
      begin
        have h75:= xsmapsloop M hfinite k n hk hn hkn hskn  m2  hm2  α halphaloop,
        exact h75,
      end,
    have h179: Ap (Ap m2 (SG M)) α ∈ ℕℕ :=
      member_subset M (LOOP n) ℕℕ (Ap (Ap m2 (SG M)) α) h170 h79,
    rw ApSG M (Ap (Ap m2 (SG M)) α) h179 at h77,
    rw sym at h77,
    have E4459:= looponeone M hfinite k n hk hn hkn hskn (Ap (Ap m2 (SG M)) α) p h79 hp h77,
    rw← E4455 at E4459,
    have h82: Ap f (Ap (Ap m2 f) α) = Ap f p:=
      begin
        rw E4459,
      end,
    have h83:= successorequation M X f hFUNC hRel  hmaps m2  α  hm2  h102,
    rw h82 at h83,
    rw h67 at h83,
    have h84: Ap f p = α :=
      begin
        have h85:= Apdef M f hFUNC p α, 
        symmetry,
        apply h85,
        rw h51,
        rw binary_union_axiom,
        right,
        rw singleton1,
      end,
    rw h84 at h83,
    have h85: Ap f ( Ap (Ap m1 f) α) = Ap f α:=
      begin
        rw h83,
      end,
    have h86:= successorequation M X f hFUNC hRel  hmaps m1  α  hm1  h102,
    rw h85 at h86,
    rw h63 at h86,
    have h87:= ssnneqn M n hn, 
    have h88: ¬ α = p:=
      begin
        intro h,
        rw← halpha at h87,
        rw← hsp at h87, 
        rw h at h87,
        contradiction,
      end,
    have h101: α ∈ ℕℕ:=
      member_subset M (LOOP n) ℕℕ α h170 halphaloop, 
    have h89: Ap f α = S α :=
      begin
        have h90:= Apdef M f hFUNC α (S α), 
        symmetry,
        apply h90,
        rw h51,
        rw binary_union_axiom,
        left,
        rw minus_members,
        split,
        {
          rw intersection_axiom,
          split,
          {
            rw SG_members,
            use α,
            simp,
            exact h101,
          },
          {
            rw pair_in_product,
            split,
            {
              exact h102,
            },
            {
              exact successorN M α h101,
            }
          }
        },
        {
          intro h91,
          rw singleton1 at h91,
          rw ordered_pair_equality at h91,
          cases h91 with h92 h93,
          contradiction, 
        }
      end,
    rw← h86 at h89,
    have h90:= snneqn M α h101,
    rw← h89 at h90, 
    have h91:= annihilation M n m hn hm h42 X f h40 α h102,
    contradiction,
  end

#axioms_all  
