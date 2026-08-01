import ChurchNumbers10
-- proof that every finite set has a cyclic permutation 

variables (M:Type) [Model M] (a b x y z u v w X R W κ μ ℓ : M)

open Model 

lemma ordernotn: ∀ (k n:M), k ∈ ℕℕ → n ∈ ℕℕ → ℕℕ ∈ FINITE M → S k = S n → ¬(k=n)→  k ∈ STEM →  ∀ (X:M), X ∈ FINITE M →   ∀ (a f q:M), a ∈ X  →   cyclicperm M f X a →  permorder M f X a q → ¬ q = n:=
  assume k n  hk hn  hNfinite   hskn hkn hstem   X hfinite a f q ha hcp hpo,
  begin
    unfold cyclicperm at hcp,
    rcases hcp with ⟨ hperm, ha, h21⟩,
    unfold permutation at hperm,
    cases hperm with h22 honto,
    have hinjection:= h22,
    unfold injection at h22,
    rcases h22 with ⟨ honeone, hRel, hFUNC, hdom, hrange⟩,
    unfold oneone at honeone,
    rcases honeone with ⟨ hmaps, h23, h24⟩,
    have h13copy:= hpo,
    unfold permorder at h13copy,
    rcases h13copy with ⟨ hq, h27, h28, h29⟩,
    have h3:= mexists M hNfinite k n hstem hn hkn hskn,
    cases h3 with m h4,
    rcases h4 with ⟨ hm, h62, h63⟩,
    have h73: ¬ m = ChurchZero := 
      begin
        intro h,
        rw h at *,
        have h74:= ChurchZero_equation k hk, 
        rw← h62 at hkn,
        rw h74 at hkn,
        contradiction,
      end,
    rw sym at h62,
    have h72:= nplusm M hNfinite k n hstem hn hkn hskn m hm h73 h62, 
    rw sym at h72,
    have h71:= annihilation M n m hn hm h72 X f hinjection a ha, 
    have h74:= h28 m hm, 
    have h75: m ≼ q → m = q:=
      begin
        intro h,
        exact h74 h  h73 h71, 
      end,
    intro hqn,
    rw hqn at *,
    have h30:= precmax M hNfinite k n hstem hn hkn hskn m hm,
    have hmn:= h75 h30,
    rw hmn at *,
    have hmapscopy:= hmaps,
    unfold maps at hmapscopy,
    rcases hmapscopy with ⟨ hRel, h31, h32, h33⟩,
    have h34:= h33 a ha,
    cases h34 with b h35,
    cases h35 with hb hab,
    have h36 := Apdef M f hFUNC a b hab,
    have h38:= precmax M hNfinite k n hstem hn hkn hskn,
    have h37: ¬ b=a:=
      begin
        intros h,
        rw h at *,
        have h39:= ApOne M f hFUNC hRel,
        have h40:= (successorN M ChurchZero (zeroN M)),
        have h41:= h38 (S ChurchZero) h40,
        have h42:= snneqn M ChurchZero (zeroN M),
        have h43:= h28 (S ChurchZero) h40 h41 h42,
        rw h39 at h43,
        rw sym at h36,
        have h44:= h43 h36,
        have h45:= nneqone M k n hk hn hNfinite hskn hkn hstem,
        rw sym at h45,
        contradiction,
      end,
    have h38:= h33 b hb,
    cases h38 with c h39,
    cases h39 with hc h40,
    have h41:= Apdef M f hFUNC b c h40,
    have h42: ¬ b = c:=
      begin
        intros h,
        rw h at *,
        have h43:= h23 a c c ⟨ hab, h40, ha⟩,
        rw sym at h43,
        contradiction,
      end, 
    set g:= (f - single ‹ a,b› - single ‹ b,c ›) ∪ single ‹ a,c› with h50,
    set Y:= X - single b with h51,
    have hRelg: Rel g:=
      begin
        rw Rel_definition,
        intros z h,
        rw h50 at h,
        rw binary_union_axiom at h,
        repeat{ rw minus_members at h},
        repeat{ rw singleton1 at h},
        cases h with h1 h2,
        {
          cases h1 with h3 h4,
          cases h3 with h5 h6,
          rw Rel_definition at hRel,
          exact hRel z h5,
        },
        {
          use a, use c, 
          exact h2,
        }
      end,
    have hFUNCg: g ∈ FUNC:=
      begin
        rw FUNC_members,
        intros x y z hxy hxz,
        rw h50 at hxy hxz,
        rw binary_union_axiom at hxy hxz,
        repeat{rw minus_members at hxy},
        repeat{rw minus_members at hxz},
        repeat{rw singleton1 at hxy},
        repeat{rw singleton1 at hxz},
        rw FUNC_members at hFUNC,
        cases hxy with h52 h53,
        {  
          cases hxz with h54 h55,
          {    
            exact hFUNC x y z h52.left.left h54.left.left,
          },
          {
            rw ordered_pair_equality at h55,
            cases h55 with h56 h57,
            rw h56 at *,
            rw h57 at *,
            cases h52 with h58 h59,
            cases h58 with h60 h61,
            have h611:= hFUNC a b y hab h60,
            rw ordered_pair_equality at h61,
            simp at h61,
            rw sym at h61,
            contradiction,
          }
        },
        {
          rw ordered_pair_equality at h53,
          rw h53.left at *,
          rw h53.right at *,
          cases hxz with h54 h55,
          {
            cases h54 with h56 h57,
            cases h56 with h58 h59,
            have h61:= hFUNC a b z hab h58,
            rw← h61 at *,
            contradiction,
          },
          {
            rw ordered_pair_equality at h55,
            symmetry,
            exact h55.right,
          }
        }
      end,
    have haY: a ∈ Y:=
      begin
        rw h51,
        rw minus_members,
        rw singleton1,
        rw sym at h37,
        exact ⟨ ha, h37⟩, 
      end,
    have hmapsg: maps M g Y Y:=
      begin
        unfold maps,
        split,
        {
          exact hRelg,
        },
        {
          repeat{split},
          {
            intros x y h,
            cases h with hx hxy,
            rw h50 at hxy,
            rw h51,
            rw h51 at hx,
            rw minus_members,
            rw singleton1,
            rw binary_union_axiom at hxy,
            rw minus_members at hxy,
            rw singleton1 at hxy,
            rw minus_members at hxy,
            rw singleton1 at hxy,
            rw minus_members at hx,
            rw singleton1 at hx,
            cases hx with hx hxb,
            cases hxy with h310 h311,
            {
              cases h310 with h312 h313,
              cases h312 with h314 h315,
              split,
              {
                rw subset_definition at hrange,
                have h317: y ∈ range f:=
                  begin
                    have h318:= range_axiom f hRel y,
                    rw h318,
                    exact ⟨ x, h314⟩, 
                  end,
                exact hrange y h317,
              },
              {
                have h80:= finitedecidable M X hfinite,
                rw decidable_members at h80,
                have h81:=  h80 x a ⟨ hx, ha⟩,
                cases h81 with h82 h83,
                {
                  rw h82 at *,
                  rw ordered_pair_equality at h315,
                  simp at h315,
                  exact h315,
                },
                {
                  intro h,
                  rw h at *,
                  have h316:= h23 a x b ⟨ hab, h314, ha⟩, 
                  rw sym at h316,
                  contradiction,
                }
              }
            },
            {
              rw singleton1 at h311,
              rw ordered_pair_equality at h311,
              rw h311.right at *,
              rw h311.left at *,
              rw sym at h42,
              exact ⟨ hc, h42⟩,
            }
          },
          { 
            rw FUNC_members at hFUNCg,
            intros x y z h,
            rcases h with ⟨ h2, h3, h4⟩,
            exact hFUNCg x y z h3 h4,
          },
          { 
            intros x h52,
            rw h51 at h52,
            rw minus_members at h52,
            rw singleton1 at h52,
            cases h52 with hx h53,
            have h80:= finitedecidable M X hfinite,
            rw decidable_members at h80,
            have h81:=  h80 x a ⟨ hx, ha⟩,
            cases h81 with h82 h83,
            {
              use c,
              split,
              {
                rw h51,
                rw minus_members,
                rw singleton1,
                rw sym at h42,
                exact ⟨ hc, h42⟩,
              },
              {
                rw h50,
                rw h82 at *,
                rw binary_union_axiom,
                right,
                rw singleton1,
              }
            },
            {
              have h54:= h33 x hx,
              cases h54 with y h55,
              use y,
              cases h55 with hy h56,
              split,
              {
                rw h51,
                rw minus_members,
                rw singleton1,
                split,
                {
                  exact hy,
                },
                { 
                  intro h,
                  rw h at *,
                  have h57:= h23 a x b ⟨hab, h56, ha⟩,
                  rw← h57 at *,
                  contradiction,
                }
              },
              {
                rw h50,
                rw binary_union_axiom,
                rw minus_members,
                rw singleton1,
                rw minus_members,
                rw singleton1, 
                left,
                split,
                {
                  split,
                  {
                    exact h56,
                  },
                  {
                    intros h,
                    rw ordered_pair_equality at h,
                    cases h with h2 h3,
                    contradiction, 
                  }
                },
                {
                  intros h, 
                  rw ordered_pair_equality at h,
                  cases h with h2 h3,
                  contradiction,
                }
              }
            }  
          }
        }
      end, 
    have h100: ∀ (r:M),r ∈ ℕℕ → ¬ r = ChurchZero → ¬ r = n → Ap (Ap r g) a = Ap (Ap (S r) f) a:=
      begin
        have base: ChurchZero ∈ Z_gf M a f g n:=
          begin
            rw Z_gf_members,
            split,
            {
              exact zeroN M,
            },
            { 
              intros h101 h102,
              contradiction, 
            }
          end,
        have step: ∀ (r:M), r ∈ Z_gf M a f g n → ¬ r = n → (S r) ∈ Z_gf M a f g n:=
          assume r h5 hrn,
          begin 
            rw Z_gf_members at h5,
            rw Z_gf_members,
            cases h5 with hr h6,
            split,
            {
              exact successorN M r hr,
            },
            {
              intros h7 h8,
              have h9:= decidable0 M r hr,
              cases h9 with h10 h11,
              {
                rw h10 at *,
                rw ApOne M g hFUNCg hRelg,
                have h12: ‹ a, c› ∈ g:=
                  begin
                    rw h50,
                    rw binary_union_axiom,
                    right,
                    rw singleton1,
                  end,
                have h13:= Apdef M g hFUNCg a c h12,
                rw← h13,
                have h14:= successorequation M X f hFUNC hRel hmaps (S ChurchZero) a (successorN M ChurchZero (zeroN M)) ha,
                rw h14,
                rw ApOne M f hFUNC hRel,
                rw← h36,
                exact h41,
              },
              {
                have h12:= h6 hrn h11,
                have h13:= successorequation M X f hFUNC hRel hmaps (S r) a (successorN M r hr) ha,
                rw h13,
                have h14:= successorequation M Y g hFUNCg hRelg hmapsg r a hr haY,
                rw h14,
                rw h12,
                have h15: ¬ Ap (Ap (S r) f) a = a:=
                  begin
                    unfold permorder at hpo,
                    rcases hpo with ⟨ h16, h17, h18, h19⟩,
                    intros h,
                    have h21:= precmax M hNfinite k n hstem   hn hkn hskn (S r)(successorN M r hr),
                    have h20:= h18 (S r) (successorN M r hr) h21 h8 h,
                    contradiction, 
                  end,
                have h16: ¬ Ap (Ap (S r) f) a = b:=
                  begin
                    rw← h12,
                    have h200:= xfmaps M Y g a hFUNCg hRelg hmapsg haY r hr,
                    intro h,
                    rw h at h200,
                    rw h51 at h200,
                    rw minus_members at h200,
                    rw singleton1 at h200,
                    cases h200 with h201 h202,
                    contradiction, 
                  end,
                have h17: Ap (Ap (S r) f) a ∈ Y:=
                  begin
                    rw h51,
                    rw minus_members,
                    rw singleton1,
                    split,
                    {
                      have h18:= xfmaps M X f a hFUNC hRel hmaps ha (S r)(successorN M r hr),
                      exact h18,
                    },
                    {
                      exact h16,
                    }
                  end,
                have h20: ∀ (x:M), x ∈ Y → ¬ x = a → Ap f x = Ap g x:=
                  begin
                    intros x hx hxa,
                    rw h51 at hx,
                    rw minus_members at hx,
                    rw singleton1 at hx,
                    cases hx with h30 h31,
                    have h32:= h33 x h30,
                    cases h32 with y h34,
                    cases h34 with hy hxy,
                    have h35:= Apdef M f hFUNC x y hxy,
                    rw←  h35,
                    have h36: ‹ x,y › ∈ g:=
                      begin
                        rw h50,
                        rw binary_union_axiom,
                        rw minus_members,
                        rw singleton1,
                        rw minus_members,
                        rw singleton1,
                        left,
                        split,
                        { 
                          split,
                          {
                            exact hxy,
                          },
                          {
                            intro h,
                            rw ordered_pair_equality at h,
                            cases h with h2 h3,
                            rw h2 at *,
                            rw h3 at *,
                            contradiction, 
                          }
                        },
                        {
                          intro h,
                          rw ordered_pair_equality at h,
                          cases h with h2 h3,
                          contradiction,
                        }
                      end,
                    have h37:= Apdef M g hFUNCg x y h36,
                    exact h37, 
                  end,
                have h21:= h20 (Ap (Ap (S r) f) a) h17 h15,
                symmetry,
                exact h21,
              }
            }
          end,
        intros r hr hrn hrz,
        have h5:= finiteinduction M hNfinite k n hstem hn hkn hskn (Z_gf M a f g n) ⟨ base, step⟩, 
        rw subset_definition at h5, 
        have h6:= h5 r hr,
        rw Z_gf_members at h6,
        cases h6 with h7 h8,
        have h9:= h8 hrz hrn,
        exact h9,
      end,
    have hac: ‹ a,c › ∈ g:=
      begin
        rw h50,
        rw binary_union_axiom,
        right,
        rw singleton1,
      end,
    have hdomg: dom g ⊆ Y:=
      begin
        rw subset_definition,
        intros t h,
        rw domain_axiom g hRelg at h,
        cases h with y h200,
        rw h50 at h200,
        rw binary_union_axiom at h200,
        rw minus_members at h200,
        rw singleton1 at h200,
        rw minus_members at h200,
        rw singleton1 at h200,
        rw h51,
        rw minus_members,
        rw singleton1,
        cases h200 with h201 h202,
        {
          cases h201 with h203 h204,
          cases h203 with h205 h206,
          rw ordered_pair_equality at h204,
          split,
          {
            have h210: t ∈ dom f:=
              begin
                rw domain_axiom f hRel,
                exact ⟨ y, h205⟩,
              end,
            have h211:= member_subset M (dom f) X t hdom h210,
            exact h211,
          },
          {
            intro h,
            rw h at *,
            simp at h204,
            have h215:= h32 b y c ⟨ hb, h205, h40⟩,
            contradiction,
          }
        },
        {
          rw singleton1 at h202,
          rw ordered_pair_equality at h202,
          cases h202 with h203 h204,
          rw h203 at *,
          rw h204 at *,
          rw sym at h37,
          exact ⟨ ha, h37⟩,
        }

      end,
    have hrangeg: range g ⊆ Y:=
      begin
        rw subset_definition,
        intros t h,
        rw range_axiom g hRelg at h,
        cases h with y h200,
        rw h50 at h200,
        rw binary_union_axiom at h200,
        rw minus_members at h200,
        rw singleton1 at h200,
        rw minus_members at h200,
        rw singleton1 at h200,
        rw h51,
        rw minus_members,
        rw singleton1,
        cases h200 with h201 h202,
        {
          cases h201 with h203 h204,
          cases h203 with h205 h206,
          rw ordered_pair_equality at h204,
          split,
          { 
            have h210: t ∈ range f:=
              begin
                rw range_axiom f hRel,
                exact ⟨ y, h205⟩,
              end,
            have h211:= member_subset M (range f) X t hrange h210,
            exact h211,
          },
          { 
            intro h,
            rw h at *,
            have h207: ¬ y = a:=
              begin
                intros h,
                rw h at *,
                contradiction,
              end,
            unfold injection at hinjection,
            cases hinjection with honeone hjunk,
            unfold oneone at honeone,
            rcases honeone with ⟨ h208, h209, h210⟩,
            have h211:= h209 a y b ⟨ hab, h205, ha⟩,
            rw sym at h211,
            contradiction,
          }
        },
        {
          rw singleton1 at h202,
          rw ordered_pair_equality at h202,
          cases h202 with h203 h204,
          rw h203 at *,
          rw h204 at *,
          rw sym at h42,
          exact ⟨ hc, h42⟩,
        }
      end,
    have h70:  cyclicperm M g Y a :=
      begin
        unfold cyclicperm,
        split,
        {
          unfold permutation,
          split,
          {
            unfold injection,
            split,
            {
              unfold oneone,
              split,
              {
                exact hmapsg,
              },
              {
                split,
                {
                  intros x u y h,
                  rcases h with ⟨h200, h201, h202⟩,
                  rw h50 at h200 h201,
                  rw binary_union_axiom at h200 h201,
                  rw minus_members at h200 h201,
                  rw singleton1 at h200 h201,
                  rw minus_members at h200 h201,
                  rw singleton1 at h200 h201,
                  cases h201 with h203 h204,
                  {
                    cases h203 with h205 h206,
                    cases h205 with h207 h208,
                    cases h200 with h209 h210,
                    {
                      cases h209 with h211 h212,
                      cases h211 with h213 h214,
                      rw h51 at h202,
                      rw minus_members at h202,
                      have h215:= h23 x u y ⟨ h213, h207, h202.left⟩,
                      exact h215, 
                    },
                    {
                      rw singleton1 at h210,
                      rw ordered_pair_equality at h210,
                      cases h210 with h216 h217,
                      rw h216 at *,
                      rw h217 at *,
                      have h220: u ∈ dom f:=
                        begin
                          rw domain_axiom f hRel,
                          exact ⟨ c, h207⟩,
                        end,
                      have h221:= member_subset M (dom f) X u hdom h220,
                      have h218:= h23 u b c ⟨ h207, h40, h221⟩,
                      rw h218 at *,
                      contradiction,
                    }
                  },
                  {
                    rw singleton1 at h204,
                    rw ordered_pair_equality at h204,
                    cases h204 with h220 h221,
                    rw h220 at *,
                    rw h221 at *,
                    cases h200 with h222 h223,
                    {
                      cases h222 with h224 h225,
                      cases h224 with h226 h227,
                      have h320: x ∈ dom f:=
                        begin
                          rw domain_axiom f hRel,
                          exact ⟨ c, h226⟩,
                        end,
                      have h221:= member_subset M (dom f) X x hdom h320,
                      have h228:= h23 x b c ⟨ h226, h40,h221⟩,
                      rw h228 at *,
                      contradiction,
                    },
                    {
                      rw singleton1 at h223,
                      rw ordered_pair_equality at h223,
                      cases h223 with h230 h231,
                      rw h230 at *,
                    }
                  }
                },
                {
                  intros x y h,
                  cases h with h232 h233,
                  have h234: x ∈ dom g:=
                    begin
                      rw domain_axiom g hRelg,
                      exact ⟨ y, h232⟩,
                    end,
                  exact member_subset M (dom g) Y x hdomg h234, 
                }
              }
            },
            {
              exact ⟨ hRelg, hFUNCg, hdomg, hrangeg⟩,
            }
          },
          {
            unfold onto,
            unfold onto at honto,
            intros y hy,
            rw h51 at hy,
            rw minus_members at hy,
            rw singleton1 at hy,
            cases hy with hyX h52,
            have h53:= honto y hyX,
            cases h53 with x h54,
            cases h54 with hx h55,
            have h80:= finitedecidable M X hfinite,
            rw decidable_members at h80,
            have h81:= h80 y c ⟨ hyX, hc⟩,
            cases h81 with h82 h83,
            {
              use a,
              rw h82 at *,
              exact ⟨ haY, hac⟩,
            },
            { 
              use x,
              split,
              { 
                rw h51,
                rw minus_members,
                rw singleton1,
                split,
                {
                  exact hx,
                },
                {
                  intros h,
                  rw h at *,
                  have h308:= h32 b c y ⟨ hx, h40, h55⟩, 
                  rw sym at h308,
                  contradiction,
                }
              },
              {
                rw h50,
                rw binary_union_axiom,
                rw minus_members,
                rw singleton1,
                rw minus_members,
                rw singleton1,
                left,
                split,
                {
                  split,
                  {
                    exact h55,
                  },
                  {
                    intro h,
                    rw ordered_pair_equality at h,
                    cases h with h2 h3,
                    rw h2 at *,
                    rw h3 at *,
                    contradiction, 
                  }
                },
                {
                  intros h,
                  rw ordered_pair_equality at h,
                  cases h with h2 h3,
                  rw h2 at *,
                  rw h3 at *,
                  contradiction,
                }
              }
            }
          }
        },
        {
          split,
          {
            exact haY,
          },
          {
            intros z hz,
            rw h51 at hz,
            rw minus_members at hz,
            rw singleton1 at hz,
            cases hz with hzX h220,
            have h221:= h21 z hzX,
            cases h221 with r h222,
            cases h222 with hr h223,
            have h224:= decidable0 M r hr,
            cases h224 with h225 h226,
            {
              rw h225 at *,
              use ChurchZero,
              rw ApZero, 
              rw ApZero at h223,
              rw ApId at h223,
              rw ApId,
              exact ⟨ hr, h223⟩,
            },
            {
              have h227:= predecessor M r hr h226,
              cases h227 with p h228,
              cases h228 with hp h229,
              use p,
              have h230:= h100 p hp,
              have h231:= decidable0 M p hp,
              cases h231 with h232 h233,
              {
                rw h232 at *,
                rw← h229 at *,
                rw ApOne M f hFUNC hRel at h223,
                rw← h36 at h223,
                contradiction, 
              },
              {
                have h235:= h100 p hp h233, 
                have h236: ¬ p = n:= 
                  begin
                    intros h,
                    rw h at *,
                    rw← h229 at *,
                    have h240:= successorequation M X f hFUNC hRel hmaps n a hn ha, 
                    rw h71 at h240,
                    rw h240 at h223,
                    rw← h36 at h223,
                    contradiction, 
                  end,
                have h237:= h235 h236,
                rw h237,
                rw h229,
                rw← h223,
                simp,
                exact hp,
              }
            }
          }
        }
      end,
    have h59:= predecessor M n hn h73,
    cases h59 with r h60,
    cases h60 with hr hsr,
    have h61:  permorder M g Y a r :=
      begin
        unfold permorder,
        split,
        {
          exact hr,
        },
        {
          unfold permorder at hpo,
          rcases hpo with ⟨ h400, h401, h402, h403⟩,
          have h404: ¬ r = ChurchZero:=
            begin
              intros h,
              rw h at *,
              have h405:= nneqone M k n hk hn hNfinite hskn hkn hstem, 
              rw sym at h405,
              contradiction,
            end,
          have h405: ¬ r = n:=
            begin
              assume h, 
              rw h at *,
              have h406:= snneqn M n hn,
              contradiction, 
            end,
          have h407:= h100 r hr h404 h405,
          rw hsr at h407,
          rw h71 at h407,
          split,
          {
            exact h407,
          },
          {
            split,
            {
              intros t ht htr htz h408,
              have h409: ¬ t = n:=
                begin
                  assume h,
                  rw h at *,
                  have h410:= precmax2 M hNfinite k n hn hstem hkn hskn r hr,
                  have h411: n ≺ r:= 
                    begin
                      rw prec_definition,
                      rw sym at h405,
                      exact ⟨ htr, h405⟩,
                    end,
                  contradiction,
                end,
              have h512:= h100 t ht htz h409,
              rw h408 at h512,
              have h513:= precmax M hNfinite k n hstem hn hkn hskn (S t) (successorN M t ht),
              rw sym at h512,
              have h514:= h402 (S t)(successorN M t ht) h513 (successoromitszero M t ht) h512,
              rw← h514 at hsr,
              have h515:= rho2 M hNfinite k n hstem  hn hkn hskn r t hr ht, 
              have h80:= finitedecidable M ℕℕ hNfinite,
              rw decidable_members at h80,
              have h81:= h80 r t ⟨ hr, ht⟩,
              cases h81 with h516 h517,
              {
                symmetry,
                exact h516,
              },
              {
                have h518:= h515 h517 hsr,
                cases h518 with h519 h520,
                {
                  cases h519 with h522 h521,
                  contradiction,
                },
                {
                  cases h520 with h521 h522,
                  contradiction,
                }
              }
            },
            {
              intros x hxY,
              rw h51 at hxY,
              rw minus_members at hxY,
              rw singleton1 at hxY,
              cases hxY with hx hxb,
              have h500:= h403 x hx,
              cases h500 with t h501,
              rcases h501 with ⟨ ht, htn, h502⟩,
              have h80:= decidable0 M t ht,
              cases h80 with h503 h504,
              {
                rw h503 at *,
                rw ApZero at h502,
                rw ApId at h502,
                use ChurchZero,
                rw ApZero,
                rw ApId,
                have h503:= precmin M hNfinite k n hstem hn hkn hskn r hr,
                exact ⟨ zeroN M, h503, h502⟩, 
              },
              {
                have h505:= predecessornotn M hNfinite k n hstem hn hkn hskn t ht h504,
                cases h505 with z h506,
                rcases h506 with⟨ hz, h507, hzn⟩,
                use z,
                repeat{split},
                {
                  exact hz,
                },
                {
                  have h508: S z ≼ S r:=
                    begin
                      rw h507,
                      rw hsr,
                      have h509:= precmax M hNfinite k n hstem hn hkn hskn t ht,
                      exact h509,
                    end,
                  have h510:= preceqsuccessor M hNfinite k n hstem hn hkn hskn (S z) r (successorN M z hz) hr h405,
                  rw h510 at h508,
                  cases h508 with h509 h520,
                  {
                    have h511:= xpreceqsx M hNfinite k n hstem hn hkn hskn z hz hzn,
                    have h512:= preceqtrans M hNfinite k n hstem hn hkn hskn z (S z) r h511 h509,
                    exact h512,
                  },
                  {
                    have h80:= finitedecidable M ℕℕ hNfinite,
                    rw decidable_members at h80,
                    have h81:= h80 z r ⟨ hz, hr⟩,
                    cases h81 with h82 h83,
                    {
                      rw h82 at *,
                      have h83:= preceqreflexive M hNfinite k n hstem hn hkn hskn r hr,
                      exact h83,
                    },
                    {
                      have h513:= rho2 M hNfinite k n hstem hn hkn hskn z r hz hr h83 h520,
                      cases h513 with h514 h515,
                      {
                        cases h514 with h516 h517,
                        contradiction,
                      },
                      {
                        cases h515 with h516 h517,
                        contradiction,
                      }
                    }
                  }
                },
                {
                  have h508:= h100 z hz,
                  have h509:= decidable0 M z hz,
                  cases h509 with h510 h511,
                  {
                    rw h510 at *,
                    rw← h507 at h502,
                    rw ApOne M f hFUNC  hRel  at h502,
                    rw← h36 at h502,
                    rw sym at h502,
                    contradiction,
                  },
                  {
                    rw← h507 at h502,
                    have h512:= h508 h511 hzn,
                    rw h512,
                    exact h502, 
                  }
                }
              }    
            }
          }
        }
      end,
    have hrz: ¬ r = ChurchZero:=
      begin
        intros h,
        have h2:= nneqone M k n hk hn hNfinite hskn hkn hstem,
        rw h at hsr,
        rw hsr at h2,
        contradiction,
      end, 
    have h102: ¬ r = n:=
      begin
        intros h,
        rw h at hsr,
        have h3:= snneqn M n hn,
        contradiction, 
      end,
    have h101:= h100 r hr hrz h102,
    rw hsr at h101, 
    rw h71 at h101,
    unfold cyclicperm at h70,
    rcases h70 with ⟨h81, h82, h83⟩,
    unfold permutation at h81,
    cases h81 with h84 h85,
    have h90:= annihilation M n n hn hn h72 Y g h84 a h82,
    rw← hsr at h90,
    have h91:= successorequation M Y g hFUNCg hRelg hmapsg r a hr haY,
    rw h90 at h91,
    rw sym at h91,
    rw h101 at h91,
    have h103: Ap (Ap (S ChurchZero) g) a = a:=
      begin
        rw ApOne M g hFUNCg hRelg, 
        exact h91,
      end,
    unfold permorder at h61,
    rcases h61 with ⟨ h62, h63, h64, h65⟩,
    have h66:= h64 (S ChurchZero)(successorN M ChurchZero (zeroN M)),
    have h67: S ChurchZero ≼ r:=
      begin
        have h200:= prectrichotomy1 M hNfinite k n hstem hn hkn hskn (S ChurchZero) r (successorN M ChurchZero (zeroN M)) hr,
        cases h200 with h201 h202,
        {
          exact h201,
        },
        { 
          have hnz:= nneqzero M k n hstem hn hkn hskn,
          rw sym at hnz,
          have h203:= preceqsuccessor M hNfinite k n hstem hn hkn hskn r ChurchZero hr (zeroN M) hnz, 
          rw h203 at h202,
          cases h202 with h204 h205,
          {
            have h206:= preceqzero M hNfinite k n hstem hn hkn hskn r hr h204,
            contradiction,
          },
          {
            rw← h205,
            have h207:= preceqreflexive M hNfinite k n hstem hn hkn hskn r hr,
            exact h207,
          }
        }
      end,
    have h68:= h66 h67 (successoromitszero M ChurchZero (zeroN M)) h103,
    have h69: n = S (S ChurchZero):=
      begin
        rw h68,
        symmetry,
        exact hsr,
      end,
    have h70:= mbig2 M n hn,
    rw← h69 at h70,
    rw sym at h70,
    contradiction, 
  end

lemma finiteperm: ℕℕ ∈ FINITE M →  ∀ (X:M), X ∈ FINITE M → ¬ X = Λ → ∀ (a:M), a ∈ X  → ∃(a f q:M), cyclicperm M f X a ∧ permorder M f X a q:=
  assume hNfinite,
  begin
    have h2:= kinstem M hNfinite,
    cases h2 with k h3,
    cases h3 with n h4,
    rcases h4 with ⟨ hk, hn, hkn, hskn, hstem⟩,
    have base: Λ ∈ W_finiteperm M:=
      begin
        rw W_finiteperm_members,
        split,
        {
          exact lambda_finite M,
        },
        { simp,
        }
      end,
    have step: ∀(X c:M), (¬ c ∈ X  ∧  X ∈ W_finiteperm M) → X ∪ (single c) ∈ W_finiteperm M:=
      begin
        intros X c h200,
        cases h200 with hc h5,
        rw W_finiteperm_members at h5,
        rw W_finiteperm_members,
        cases h5 with hfinite h6,
        split,
        {
          have h7:= finite_adjoin M X c ⟨ hfinite, hc⟩, 
          exact h7,
        },
        { 
          right,
          cases h6 with h7 h8,
          {
            use c,
            set f:= single ‹ c,c› with hf,
            use f,
            use ChurchZero,
            split,
            {
              rw binary_union_axiom,
              right,
              rw singleton1,
            },
            {
              rw h7,
              rw empty_union_x M (single c), 
              have hRel:Rel f:=
                begin
                  rw Rel_definition,
                  intros z h,
                  rw hf at h,
                  rw singleton1 at h,
                  use c, use c,
                  exact h,
                end,
              have hFUNC: f ∈ FUNC:=
                begin
                  rw FUNC_members,
                  intros x y z hx hz,
                  rw hf at hx hz,
                  rw singleton1 at hx hz,
                  rw ordered_pair_equality at hx hz,
                  rw hz.right,
                  rw hx.right,
                end,
              split,
              {
                unfold cyclicperm,
                rw singleton1,
                simp,
                split,
                {
                  unfold permutation,
                  split,
                  {
                    unfold injection,
                    split,
                    {
                      unfold oneone,
                      split,
                      {
                        unfold maps,
                        split,
                        {
                          exact hRel,
                        },
                        {
                          split,
                          {
                            intros x y,
                            rw singleton1,
                            rw singleton1,
                            intros h,
                            cases h with h3 h4,
                            rw h3 at *,
                            rw ordered_pair_equality at h4,
                            rw h4.right,
                            rw singleton1,
                          },
                          {
                            split,
                            {
                              intros x y z h,
                              rw singleton1 at h,
                              rw hf at h,
                              rw singleton1 at h,
                              rw singleton1 at h,
                              rcases h with ⟨ h2, h3, h4⟩,
                              rw h2 at *,
                              rw ordered_pair_equality at h3 h4,
                              rw h3.right,
                              rw h4.right,
                            },
                            {
                              intros x h,
                              rw singleton1 at h,
                              rw h at *,
                              use c,
                              rw singleton1,
                              rw hf,
                              rw singleton1,
                              simp,
                            }
                          }
                        }
                      },
                      {
                        split,
                        {
                          intros x u y h,
                          rcases h with ⟨h2, h3, h4⟩,
                          rw hf at h2 h3,
                          rw singleton1 at h4 h3 h2,
                          rw h4 at *,
                          rw ordered_pair_equality at h3 h2,
                          rw h3.left,
                        },
                        {
                          intros x y h,
                          rw hf at h,
                          rw singleton1 at h,
                          rw singleton1 at h,
                          rw ordered_pair_equality at h,
                          rw h.left.left,
                          rw singleton1,
                        }
                      }
                    },
                    {
                      split,
                      {
                        exact hRel,
                      },
                      {
                        split,
                        {
                          exact hFUNC,
                        },
                        {
                          split,
                          {
                            rw subset_definition,
                            intros t h,
                            rw domain_axiom f hRel at h,
                            rw singleton1,
                            cases h with y h3,
                            rw hf at h3,
                            rw singleton1 at h3,
                            rw ordered_pair_equality at h3,
                            exact h3.left,
                          },
                          {
                            rw subset_definition,
                            intros t h,
                            rw range_axiom f hRel at h,
                            rw singleton1,
                            cases h with x h3,
                            rw hf at h3,
                            rw singleton1 at h3,
                            rw ordered_pair_equality at h3,
                            exact h3.right,
                          }
                        }
                      }
                    }
                  },
                  {
                    unfold onto,
                    intros y hy,
                    rw singleton1 at hy,
                    use c,
                    rw singleton1,
                    simp,
                    rw hy,
                    rw hf,
                    rw singleton1,
                  }
                },
                {
                  intros z h,
                  use ChurchZero,
                  rw singleton1 at h,
                  rw h at *,
                  split,
                  {
                    exact zeroN M,
                  },
                  {
                    rw ApZero,
                    rw ApId,
                  }
                }
              },
              {
                unfold permorder,
                split,
                {
                  exact zeroN M,
                },
                {
                  split,
                  {
                    rw ApZero,
                    rw ApId,
                  },
                  {
                    split,
                    {
                      intros t ht h3 htz h4,
                      have h5:= preceqzero M hNfinite k n hstem hn hkn hskn t ht h3,
                      exact h5,
                    },
                    {
                      intros x h,
                      rw singleton1 at h,
                      rw h at *,
                      use ChurchZero,
                      split,
                      {
                        exact zeroN M,
                      },
                      {
                        rw ApZero,
                        rw ApId,
                        simp,
                        have h8:= preceqreflexive M hNfinite k n hstem hn hkn hskn ChurchZero (zeroN M),
                        exact h8,
                      }
                    }
                  }
                }
              }
            }
          },
          {
            cases h8 with a h9,
            cases h9 with f h10,
            cases h10 with q h11,
            rcases h11 with ⟨ ha, h12, h13⟩,
            use a,
            have h14: X - (single a) ∈ FINITE M:=
              begin
                have h16: single a ⊆ X:=
                  begin
                    rw subset_definition,
                    intros t h,
                    rw singleton1 at h,
                    rw h at *,
                    exact ha,
                  end,
                have h15:= finitedif M X (single a) hfinite (singletons_finite M a) h16,
                exact h15,
              end,
            have h15:= empty_or_inhabited M (X - single a) h14,
            cases h15 with h16 h17,
            {
              have h19: X = single a:=
                begin
                  rw full_extensionality,
                  intros t,
                  rw singleton1,
                  rw full_extensionality at h16,
                  specialize h16 t,
                  rw minus_members at h16,
                  rw singleton1 at h16,
                  have h17:= emptyset_axiom t,
                  split,
                  {
                    intro h,
                    cases h16 with h18 h19,
                    have h80:= finitedecidable M X hfinite,
                    rw decidable_members at h80,
                    have h81 := h80 t a ⟨ h, ha⟩,
                    cases h81 with h82 h83,
                    {
                      exact h82,
                    },
                    {
                      have h84:= h17 (h18 ⟨ h, h83⟩ ),
                      contradiction,
                    }
                  },
                  {
                    intro h,
                    rw h at *,
                    exact ha,
                  }
                end,
              have h20: ¬ a = c:=
                begin
                  intro h,
                  rw h at *,
                  contradiction,
                end,
              have h18:= simplestperm M hNfinite a c h20,
              cases h18 with F h29,
              use F,
              use (S (S ChurchZero)),
              have h21: X ∪ single c = {a,c}:=
                begin
                  rw h19,
                  rw full_extensionality,
                  intro t,
                  rw pairing_axiom,
                  rw binary_union_axiom,
                  rw singleton1,
                  rw singleton1,
                end,
              rw h21,
              split,
              {
                rw pairing_axiom,
                simp,
              },
              {
                cases h29 with h30 h31,
                exact h31,
              }
            },
            {
              have h12copy:= h12,
              unfold cyclicperm at h12copy,
              rcases h12copy with ⟨ h20, h21, h22⟩,
              unfold permutation at h20,
              cases h20 with h23 h24,
              unfold onto at h24,
              have h25 := h24 a ha,
              cases h25 with b h26,
              cases h26 with hb hba,
              have h13copy:= h13,
              unfold permorder at h13copy,
              rcases h13copy with ⟨ hq, h27, h28, h29⟩,
              have h60:= mexists M hNfinite k n hstem hn hkn hskn,
              cases h60 with m h61,
              rcases h61 with ⟨ hm, h62, h63⟩, 
              have h73: ¬ m = ChurchZero := 
                begin
                  intro h,
                  rw h at *,
                  have h74:= ChurchZero_equation k hk, 
                  rw← h62 at hkn,
                  rw h74 at hkn,
                  contradiction,
                end,
              rw sym at h62, 
              have h72:= nplusm M hNfinite k n hstem hn hkn hskn m hm h73 h62, 
              rw sym at h72,
              have h71:= annihilation M n m hn hm h72 X f h23 a ha, 
              have h74:= h28 m hm, 
              have h75: m ≼ q → m = q:=
                begin
                  intro h,
                  exact h74 h  h73 h71, 
                end,
              have hqn: ¬ q = n:=
                begin
                  intro h,
                  rw h at *,
                  have h76:= precmax M hNfinite k n hstem hn hkn hskn m hm,  
                  have h77:= h75 h76, 
                  rw← h at h13,
                  have h78:= ordernotn M k n hk hn hNfinite hskn hkn hstem X hfinite a f q ha h12 h13, 
                  contradiction, 
                end,
              have hqnz: ¬ q = ChurchZero:=
                begin
                  cases h17 with u h90,
                  rw minus_members at h90,
                  cases h90 with hu h91,
                  rw singleton1 at h91,
                  have h92:= h29 u hu,
                  cases h92 with r h93,
                  rcases h93 with ⟨ hr, h94, h95⟩,
                  intros h,
                  rw h at *,
                  have h96:= preceqzero M hNfinite k n hstem hn hkn hskn r hr h94,
                  rw h96 at *,
                  rw ApZero at h95,
                  rw ApId at h95,
                  rw sym at h95,
                  contradiction,
                end,
              have hab: ¬ a=b:=
                begin
                  intro h,
                  rw←  h at *,
                  cases h17 with u h300,
                  rw minus_members at h300,
                  rw singleton1 at h300,
                  cases h300 with hu h301,
                  have h302:= h29 u hu,
                  cases h302 with r h303,
                  rcases h303 with ⟨ hr, h305, h306⟩,
                  have h3051: ∀ (t:M), t ∈ ℕℕ →  Ap (Ap t f) a = a:=
                    begin
                      have base: ChurchZero ∈ Z_3051 M a f:=
                        begin
                          rw Z_3051_members,
                          rw ApZero,
                          rw ApId,
                          simp,
                          exact (zeroN M), 
                        end,
                      have step: ∀(t:M),  t ∈ Z_3051 M a f → S t ∈ Z_3051 M a f:=
                        begin
                          intros t hIH,
                          rw Z_3051_members at hIH,
                          rw Z_3051_members,
                          cases hIH with ht h400,
                          split,
                          {
                            exact successorN M t ht,
                          },
                          {   
                            unfold injection at h23,
                            rcases h23 with ⟨ honeone, hRel, hFUNC, h827, h828⟩,
                            unfold oneone at honeone,
                            rcases honeone with ⟨ hmaps, h829, h830⟩, 
                            have h401:= successorequation M X f hFUNC hRel hmaps t a ht ha,
                            rw h401,
                            rw h400,
                            have h402:= Apdef M f hFUNC a a hba,
                            symmetry,
                            exact h402,
                          }
                        end,
                      intros t ht,
                      rw N_members at ht,
                      have h5:= ht (Z_3051 M a f) ⟨base, step⟩,
                      rw Z_3051_members at h5,
                      exact h5.right, 
                    end,
                  have h307:= h3051 r hr,
                  rw← h306 at h301,
                  contradiction, 
                end,
              set g := f - single  ‹ b,a ›  ∪ single  ‹ b,c ›  ∪ single  ‹ c,a › with h50,
              have h30:= orderstep2 M k n q hk hn hNfinite hskn hkn hstem hq hqn hqnz X f a b c g hfinite hc hba hab h50 h12 h13,
              use g,
              use (S q),
              split,
              {
                rw binary_union_axiom,
                left,
                exact ha, 
              },
              {
                split,
                {
                  exact h30,
                },
                {
                  have h31:= orderstep3 M k n q hk hn hNfinite hskn hkn hstem hq hqn hqnz X f a b c g hfinite hc hba hab h50 h12 h13,
                  exact h31,
                }
              }
            }
          }
        }
      end,
    intros X hX hnonempty,
    rw finite_members at hX,
    have h5:= hX (W_finiteperm M) ⟨ base,step⟩,
    rw W_finiteperm_members at h5,
    intros a ha,
    cases h5 with hX h6,
    cases h6 with h7 h8,
    {  
      contradiction,
    },
    {  
      cases h8 with a2 h9,
      cases h9 with f h10,
      cases h10 with q h11,
      cases h11 with h12 h13,
      use a2, use f, use q,
      exact h13,
    }
  end 

#axioms_all