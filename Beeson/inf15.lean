--   Specker's Φ 
import inf14 
variables (M:Type) [Model M] (a b x y z u v w X R W κ μ ℓ : M)
-- using ℓ where the source text has λ because you can't use λ for a variable.

open Model 



lemma lessthanone: ∀ (u:M), u ∈ 𝔽 →  u < one → u = zero:=
  assume u,
  begin
    intros h h2,
    have h3:= Theorem2 M u zero h (zeroF M),
    cases h3 with h4 h5,
    cases h4 with h6 h7,
    {
      have h8:=nothinglessthanzero M u h,
      contradiction, 
    },
    {  
      cases h7 with h8 h9,
      {
        exact h8,
      },
      { 
        push_neg at h5,  
        have h10:= noinsertions M u one h (oneF M) h2,
        rw one_definition at h10,
        have h8:  ∃(u:M), u ∈ 𝕊 zero:=
          begin
            use zero,
            rw← one_definition,
            rw one_members, 
            use Λ,
            rw zero_definition, 
          end,
        have h11:= ordersuccessor M u zero h (zeroF M) h8,
        rw← h11 at h10, 
        have h15:= le_transitive2 M zero u zero (zeroF M) h (zeroF M) h9 h10, 
        have h16:= xnotlessthanx M zero (zeroF M),
        contradiction,
      }
    }
  end

lemma lessthanthree: ∀ (u:M), u ∈ 𝔽 → (u < three ↔ u = zero ∨ u = one ∨ u = two):=
  assume u,
  begin 
    intro h,
    split,
    {
      intro h2,
      rw three_definition at h2,
      rw lessthan_definition at h2,
      cases h2 with h3 h4,
      have h5:= lessthansuccessor2 M u two h (twoF M) h3,
      cases h5 with h6 h7,
      {  
        rw two_definition at h6, 
        have h8:=  lessthansuccessor2 M u one h (oneF M) h6, 
        cases h8 with h9 h10,
        {
          rw letolessthan M u one h (oneF M) at h9, 
          cases h9 with h11 h12,
          {
            have h13:= lessthanone M u h h11, 
            rw h13 at *,
            left,
            exact refl zero,
          },
          {
            right, left,
            exact h12,
          }
        },
        {
          rw two_definition,
          right, right,
          exact h10,
        }
      },
      {
        contradiction, 
      }
    },
    {
      intro h2,
      have h5:= two_lessthan_three M,
      have h6:= one_lessthan_two M,
      have h7:= lessthan_transitive M one two three (oneF M)(twoF M)(threeF M) h6 h5,
      have h8:= zero_lessthan_two M,
      have h9:= lessthan_transitive M zero two three (zeroF M)(twoF M)(threeF M) h8 h5, 
      cases h2 with h3 h4,
      {
        rw h3,
        exact h9,
      },
      {
        cases h4 with h10 h11,
        {
          rw h10, 
          exact h7,
        },
        {
          rw h11, 
          exact h5, 
        }
      }
    }
  end
 
lemma le_zero: ∀ (x:M), x ∈ 𝔽 → x ≤ zero → x = zero:=
  assume x,
  begin
    intros h h2,
    rw le_definition at h2,
    cases h2 with a h3,
    cases h3 with b h4,
    rcases h4 with ⟨ h5, h6, h7, h8⟩, 
    rw zero_definition,
    rw full_extensionality,
    intro t,
    rw singleton1 M,
    split,
    {
      intro h9,
      rw zero_definition at h6,
      rw singleton1 at h6,
      rw h6 at h7,
      have h19:= (subset_of_empty M a).mp h7,
      rw h19 at h5,
      have h10: Λ ∈ zero:=
        begin
          rw zero_definition,
          rw singleton1 M, 
        end,
      have h11: Λ ∈ x ∩ zero:=
        begin
          rw intersection_axiom, 
          exact ⟨ h5, h10⟩, 
        end,
      have h12:= cardinalsdisjoint M x zero Λ  h (zeroF M) h11, 
      rw  h12 at h9, 
      rw zero_definition at h9,
      rw singleton1 M at h9,
      exact h9, 
    },
    {
      intro h20,
      rw h20,
      have h21: Λ ∈ zero:=
        begin
          rw zero_definition,
          rw singleton1 M,
        end, 
      rw zero_definition at h6,
      rw singleton1 M at h6,
      rw h6 at h7,
      rw subset_of_empty M a at h7,
      rw h7 at h5,
      exact h5, 
    }
  end 

lemma minPhim: ∀ (m:M), (∃(u:M),u ∈ m) →  m ∈ Φ M m:=
  begin
    intros m hm,
    rw Phi_members,
    use zero,
    split,
    { 
      exact zeroF M,
    },
    {
      have h3:= tower_base_equation M m,
      rw h3,
      simp,
      exact hm,
    }
  end

lemma sixpointfour: ∀ (m n:M), m ∈ 𝔽 → n ∈ 𝔽 → n ∈ Φ M m → m ≤ n:=
  begin
    intros m n hm hn h3,
    rw Phi_members M at h3,
    cases h3 with y h6,
    cases h6 with h7 h80,
    cases h80 with h8 h81,
    rw h8 at hn,
    have h9:= mleImy M m hm y h7 hn,
    rw h8,
    exact h9, 
  end

lemma sixpointfive: ∀ (m:M), m ∈ 𝔽 → (∃ (u:M), u ∈ exp M m) → ¬ m ∈ Φ M (exp M m):=
  assume m,
  begin
    intros hm h3 h5,
    have h2:= finiteexp M m hm h3, 
    have h4:= sixpointfour M (exp M m) m h2 hm h5,
    have h6:= mlessthanexpm M m hm h3, 
    have h7:= Theorem2 M m  (exp M m) hm h2, 
    cases h7 with h8 h9,
    cases h8 with h10 h11,
    { 
      apply h9,
      split,
      {
        exact h6,
      },
      {
        rw lessthan_definition,
        split,
        {
          exact h4,
        },
        {
          intro h11,
          rw h11 at *,
          have h12:= xnotlessthanx M m h2,
          contradiction,
        }
      } 
    },
    {
      cases h11 with h12 h13,
      {
        rw← h12 at h6,
        have h14:= xnotlessthanx M m hm,
        contradiction,
      },
      {
        have h14:= lessthan_transitive M m (exp M m) m hm h2 hm h6 h13, 
        have h15:= xnotlessthanx M m hm,
        contradiction,
      }
    }
  end

lemma Isuccessor: ∀ (y:M), y ∈ 𝔽 → ∀ (m:M), m ∈ 𝔽 →  exp M m ∈ 𝔽 → 
(∃ (u:M), u ∈ 𝕊 y) → 𝕀 M m (𝕊 y) = 𝕀 M (exp M m) y:=
  begin 
    have base: zero ∈ ZIsuccessor M:=
      begin
        rw ZIsuccessor_members, 
        split,
        {
          exact zeroF M,
        },
        {
          intros m hm h30 h2,
          have h3:= tower_base_equation M m,
          have h4: ∃ (u:M), u ∈ one:=
            begin
              use (single Λ ),
              rw one_members M,
              use Λ ,
            end,
          have h5:= tower_recursion_equation M m zero (zeroF M) h2,
          rw h3 at *,
          rw h5,
          rw tower_base_equation M (exp M m),
        }
      end, 
    have step: ∀ (y:M), y ∈ ZIsuccessor M → (∃ u, u ∈ 𝕊 y) →  𝕊 y ∈ ZIsuccessor M:=
      assume y,
      begin
        intros h3 h2,
        rw ZIsuccessor_members at *,
        cases h3 with h4 h5, 
        split,
        {
          exact successorF M y h4 h2,
        },
        {
          intros m hm h30 h6,
          rw tower_recursion_equation M m (𝕊 y) (successorF M y h4 h2) h6,
          rw tower_recursion_equation M (exp M m) y h4 h2, 
          have h31:= h5 m hm h30 h2,
          rw h31, 
        }
      end,
    intros y h,
    rw F_members at h, 
    specialize h ( ZIsuccessor M),
    have h3:= h (and.intro base  step), 
    rw ( ZIsuccessor_members M) at h3, 
    cases h3 with h5 h6, 
    exact h6, 
  end

lemma ylessthanImy: ∀ (m:M), m ∈ 𝔽 → ¬ m = zero → ∀ (y:M), y∈ 𝔽 → (¬ y = zero) → (∃(u:M), u∈ 𝕀 M m y) → y < 𝕀 M m y ∧ 𝕀 M m y ∈ 𝔽 :=
  assume m hm h999,
  begin
    have base:zero ∈ Z_mlessthanImy M m:=
      begin
        rw Z_mlessthanImy_members,
        split,
        {
          exact zeroF M,
        },
        {
          intros hzero,
          have h3: (zero:M) = (zero:M) := refl (zero:M),
          contradiction,
        }
      end,
    have step: ∀(y:M), y ∈ Z_mlessthanImy M m → (∃(u:M),u ∈ 𝕊 y) → 𝕊 y ∈ Z_mlessthanImy M m :=
      begin
        intros y h4 hsy,
        have h100:= hsy,
        cases h100 with u hu,
        rw Z_mlessthanImy_members at h4,
        cases h4 with hy h5,
        rw Z_mlessthanImy_members,
        split,
        {
          exact successorF M y hy hsy,
        },
        {
          intros h6 h7,
          cases h7 with b h8,
          have h50:= FregeNdecidable M,
          rw decidable_members at h50,
          have h51:= h50 y zero ⟨ hy, zeroF M⟩,
          cases h51 with h52 h53,
          {
            -- case y = zero
            rw h52 at *,
            rw tower_recursion_equation M m zero hy hsy,
            rw tower_base_equation M m,
            rw tower_recursion_equation M m zero hy hsy at h8,
            rw tower_base_equation M m at h8,
            have h9:= finiteexp M m hm ⟨b,h8⟩, 
            split,
            {
              have h55:= mlessthanexpm M m hm ⟨ b, h8⟩, 
              have h56: 𝕊 zero ≤ m:=
                begin
                  have h60:= lessthanone M,
                  rw←  one_definition,
                  have h61:= finitetrichotomy M m hm one (oneF M),
                  cases h61 with h62 h63,
                  {
                    have h70:= h60 m hm h62,
                    rw h70 at *,
                    contradiction,
                  },
                  {
                    cases h63 with h64 h65,
                    {
                      rw h64 at *,
                      exact le_reflexive M one (oneF M),
                    },
                    {
                      rw lessthan_definition at h65,
                      cases h65 with h66 h67,
                      exact h66,
                    }
                  }
                end,  
              have h57:= le_transitive3 M (𝕊 zero) m (exp M m) (successorF M zero (zeroF M) hsy) hm h9 h56 h55,
              exact h57,
            },
            {
              exact h9,
            }
          },
          {
            -- case y ≠ zero
            have h80:= h5 h53,
            rw tower_recursion_equation M m y hy hsy at h8,
            have hb:= h8,
            rw tower_recursion_equation M m y hy hsy,
            rw exp_members at h8,
            cases h8 with a h9,
            cases h9 with h10 h11,
            have h81:= h80 ⟨ USC a, h10⟩,
            cases h81 with h82 h83,
            have h84:= noinsertions M y (𝕀 M m y) hy h83 h82,
            have h85:= mlessthanexpm M (𝕀 M m y) h83 ⟨ b, hb⟩,
            have hsyF:= successorF M y hy hsy,
            have h90:= finiteexp M (𝕀 M m y) h83 ⟨b, hb⟩, 
            have h86:= le_transitive3 M (𝕊 y) (𝕀 M m y)(exp M (𝕀 M m y)) hsyF h83 h90 h84 h85,
            exact ⟨ h86, h90⟩,
          }
        }
      end,
    intros y hy,
    rw F_members at hy,
    have h100:= hy (Z_mlessthanImy M m) ⟨base, step⟩,
    rw Z_mlessthanImy_members M at h100,
    exact h100.2, 
  end
 
lemma sixpointsix: ∀ (m:M), m ∈ 𝔽 → (∃ (u:M), u ∈ exp M m) → 
Φ M m = ((single m) ∪ Φ M (exp M m)) :=
  assume m,
  begin
    intros hm h3,
    rw full_extensionality,
    intro t,
    rw binary_union_axiom,
    rw singleton1 M,
    split,
    { --left to right
      intro h,
      rw Phi_members M at h,
      cases h with y h2,
      cases h2 with hy h5,
      --cases h5 with y h6,
      --cases h6 with h7 h8,
      have h9: y= zero ∨ ¬ y = zero:= 
        begin
          have h10:= FregeNdecidable M,
          rw decidable_members M at h10,
          exact h10 y zero ⟨ hy, (zeroF M)⟩, 
        end,
      cases h9 with h12 h13,
      {  -- y = zero
        left,
        rw h12 at *,
        rw tower_base_equation M m at h5,
        exact h5.1, 
      },
      { --  y ≠ zero
        have h14:= nonzeroissuccessor M y hy h13,
        cases h14 with p h15,
        cases h15 with h16 h17,
        rw h17 at *,
        have h18:= tower_recursion_equation M m p h16 (cardinalsinhabited M (𝕊 p) hy),
        rw h5 at *,
        right,
        rw Phi_members,
        use p,
        split,
        {
          exact h16,
        },
        { 
          have h21:= finiteexp M m hm h3,
          have h20:= Isuccessor M p h16 m hm h21 (cardinalsinhabited M (𝕊 p) hy),
          cases h5 with h5a h5b,
          split,
          {
            rw h5a at *,
            exact h20,
          },
          {
            exact h5b,
          }
        }
      }
    },
    {  --right to left 
      intro h,
      have h3copy:= h3,
      cases h3copy with u h403,
      rw exp_members at h403,
      cases h403 with a h404,
      cases h404 with h405 h406,
      cases h with h4 h5,
      { 
        rw h4,
        exact minPhim M m ⟨ USC a, h405⟩,
      },
      { 
        rw Phi_members M at *,
        cases h5 with y h200,
        cases h200 with hy h8,
        have h19: y= zero ∨ ¬ y = zero:= 
          begin
            have h20:= FregeNdecidable M,
            rw decidable_members M at h20,
            exact h20 y zero ⟨ hy, (zeroF M)⟩, 
          end,
        have h320: ∃ (u:M), u ∈ 𝕊 zero:=
          begin
            use single Λ,
            rw ← one_definition,
            rw one_members,
            use Λ,
          end,
        have h36: ∃ (u:M), u ∈ 𝕊 one:=
          begin
            rw← two_definition,
            use {zero, one},
            rw two_members M,
            use zero, use one,
            simp,
            have h35:= zero_lessthan_one M,
            rw lessthan_definition at h35,
            exact h35.right, 
          end,
        use 𝕊 y,
        have h11:= finiteexp M m hm h3,
        cases h19 with h20 h21, 
        {
          rw h20 at *,
          have h22:= tower_recursion_equation M m zero (zeroF M) h320, 
          rw tower_base_equation M m at h22, 
          rw h22, 
          rw tower_base_equation M (exp M m) at h8,
          rw ← one_definition,
          exact ⟨ oneF M, h8⟩, 
        },
        {
          have h29:= expnotzero M m,
          have h30:= FregeNdecidable M,
          rw decidable_members at h30,
          have h31:= h30 y one ⟨ hy, (oneF M)⟩,
          have h32:= h30 y two ⟨ hy, (twoF M)⟩, 
          cases h31 with h33 h34,
          {
            rw h33 at *,
            cases h8 with h8a h8b,
            rw h8a, 
            split,
            {
              rw← two_definition,
              exact twoF M,
            },
            { 
              have h38:= Isuccessor M one (oneF M)  m hm h11 h36, 
              split,
              { 
                symmetry,
                exact h38, 
              },
              {
                rw h8a at h8b,
                exact h8b,
              }
            }  
          },
          {
            cases h32 with h35 h36,
            {
              rw h35 at *,
              cases h8 with h8a h8b,
              rw h8a, 
              split,
              {
                rw← three_definition,
                exact (threeF M), 
              },
              {
                have h360: ∃ (u:M), u ∈ 𝕊 two:=
                  begin
                    rw← three_definition,
                    use {zero, one} ∪ (single two),
                    rw three_members M,
                    use zero, use one, use two, 
                    have h37:= zero_lessthan_one M,
                    rw lessthan_definition at h37,
                    cases h37 with h38 h39,
                    have h50:= one_lessthan_two M, 
                    rw lessthan_definition at h50,
                    cases h50 with h51 h52, 
                    repeat{split},
                    {
                      exact h39,
                    },
                    {
                      rw sym,
                      exact h21,
                    },
                    {
                      rw sym,
                      exact h34, 
                    },
                    {
                      intro t,
                      rw binary_union_axiom, 
                      rw [pairing_axiom, singleton1],
                      rw or_assoc,
                    }, 
                  end,
                have h38:= Isuccessor M two (twoF M)  m hm h11 h360,
                split, 
                {
                  symmetry,
                  exact h38, 
                },
                {
                  rw h8a at h8b,
                  exact h8b,
                }
              }
            },
            { 
              have h350:  ¬((y = zero ∨ y = one ∨ y = two) ∧ exp M m = zero):=
                begin
                  intro h37,
                  cases h37 with h38 h39,
                  cases h38 with h50 h51,
                  {
                    contradiction,
                  },
                  {
                    cases h51 with h52 h53,
                    {
                      contradiction,
                    },
                    {
                      contradiction,
                    }
                  }
                end, 
              cases h8 with h8a h8b,
              
              have h17: ∃(u:M), u ∈ 𝕊 y:= 
                begin
                  have h8bcopy:= h8b,
                  rw h8a at h8bcopy,
                  have h303:= expnotzero M m, 
                  have h80:= ylessthanImy M (exp M m) h11 h303 y hy h21 h8bcopy,
                  have h81:= noinsertions M y (𝕀 M (exp M m) y) hy h80.2 h80.1,
                  rw le_definition at h81,
                  cases h81 with a h82,
                  cases h82 with b h83,
                  exact ⟨ a, h83.1⟩,
                end,
              have h18:= Isuccessor M y hy m hm h11 h17, 
              rw h18, 
              rw h8a, 
              simp, 
              split,
              {
                exact successorF M y hy h17,  
              },
              { 
                rw h8a at h8b,
                exact h8b,
              }
            }
          } 
        }
      }
    }
  end
        
lemma sixpointsixA: ∀ (m:M), m ∈ 𝔽 → (∃ (u:M), u ∈ exp M m) → 
Φ M (exp M m) ∈ FINITE M → 
Nc M (Φ M m) =  Nc M ( Φ M (exp M m)) + one := 
  begin
    intros m hm h3 hfinite,
    have h4:= sixpointsix M m hm h3,
    have h5:= sixpointfive M m hm h3,
    have h6:= finite_adjoin M ( Φ M (exp M m)) m ⟨ hfinite, h5⟩,
    rw union_commutative at h4,
    rw←  h4 at h6,
    have h7:= xinNcx M (Φ M (exp M m)),
    have h8: (Φ M (exp M m)) ∪ (single m) ∈ 𝕊 (Nc M (Φ M (exp M m))):=
      begin
        rw successor_members,
        use (Φ M (exp M m)),
        use m,
        simp,
        exact ⟨ h7, h5⟩,
      end,
    have h8A:= finitecardinals3 M  ((Φ M (exp M m))) hfinite,
    have h8B:= successorF M (Nc M (Φ M (exp M m))) h8A  ⟨ (Φ M (exp M m) ∪ single m) , h8 ⟩,
    have h9:= finitecardinals3 M (Φ M m) h6,
    have h10:= finitecardinals3 M (Φ M (exp M m)) hfinite,
    have h12:= cardinalsdisjoint M (Nc M(Φ M m))(𝕊 (Nc M (Φ M (exp M m)))) ((Φ M (exp M m)) ∪ single m) h9 h8B,
    rw←  successorisplusone,
    apply h12,
    rw intersection_axiom,
    split,
    {
      rw← h4,
      exact xinNcx M (Φ M m),
    },
    {
      exact h8,
    }
  end

lemma sixpointseven: ∀ (m:M), m ∈ 𝔽 → Φ M m ∈ FINITE M → (∃ (u:M), u ∈ exp M m) → 
Nc M (Φ M m) = Nc M (Φ M (exp M m)) + one:=
  assume m,
  begin
    intros h hfinite h2,
    have h3:= sixpointsix M m h h2,
    have h4:= sixpointfive M m h h2,
    have h5:= xinNcx M (exp M m), 
    have h6: ((Φ M (exp M m)) ∪ (single m)) ∈ 𝕊 (Nc M (Φ M (exp M m))):=
      begin
        have h7:= successor_members M (Nc M (Φ M (exp M m))), 
        specialize h7 ((Φ M (exp M m)) ∪ (single m)),
        rw h7,
        have h8:= xinNcx M (Φ M (exp M m)),
        use Φ M (exp M m), use m,
        split,
        {
          exact h8,
        },
        { 
          split,
          { 
            exact h4,
          },
          {
            refl,
          }
        }
      end,
    have h7: ((Φ M (exp M m)) ∪ (single m)) ∈ (Nc M (Φ M m) ∩ 𝕊 (Nc M (Φ M (exp M m)))):=
      begin
        rw intersection_axiom, 
        split,
        {
          rw union_commutative M,
          rw← h3,
          exact xinNcx M (Φ M m), 
        },
        {
          exact h6, 
        }
      end, 
    have h8:= finitecardinals3 M (Φ M m) hfinite, 
    have h9: Φ M (exp M m) ∈ SSC (Φ M m):=
      begin
        rw ssc_members,
        split,
        {
          rw h3,
          rw union_commutative,
          have h10:= subset_union2 M (Φ M (exp M m)) (single m), 
          exact h10, 
        },
        {
          intro t,
          rw h3,
          intro h20,
          rw binary_union_axiom at h20,
          rw singleton1 M at h20,
          cases h20 with h21 h22,
          {
            rw h21 at *,
            right,
            exact h4, 
          },
          {
            left,
            exact h22, 
          }
        }
      end,
    rw ssc_members at h9,
    cases h9 with h10 h11, 
    have h12: Φ M (exp M m) ∈ FINITE M:=
      begin
        have h13:= separablefinite M (Φ M m) hfinite (Φ M (exp M m)) h10, 
        unfold separable_subset at h13,
        apply h13,     
        split,
        {
          exact h10, 
        },
        {
          rw full_extensionality,
          intro t,
          specialize h11 t,
          rw binary_union_axiom ,
          rw minus_members, 
          split,
          {
            intro h40,
            have h41:= h11 h40,
            cases h41 with h42 h43,
            {
              exact or.inl h42, 
            },
            {
              right,
              exact ⟨ h40, h43⟩,
            }
          },
          {
            intro h14,
            rw or_comm at h14,
            cases h14 with h15 h16,
            {
              exact h15.left, 
            },
            {
               exact member_subset M (Φ M (exp M m)) (Φ M m) t h10 h16,
            }
          }
        }
      end,
    have h13: (Φ M (exp M m)) ∪ (single m) ∈ 𝕊 (Nc M (Φ M (exp M m))):=
      begin
        rw successor_members,
        use Φ M (exp M m), use m,
        
        split,
        {
          exact xinNcx M (Φ M (exp M m)), 
        },
        { split,
          { 
            exact h4,
          },
          {
            refl,
          }
        }
      end, 
    have h14:  Nc M (Φ M (exp M m)) ∈ 𝔽 := finitecardinals3 M    (Φ M (exp M m)) h12,
    have h15:= successorF M (Nc M (Φ M (exp M m))) h14 ⟨ Φ M (exp M m) ∪ single m , h13⟩ ,
    have h16:= cardinalsdisjoint M (Nc M (Φ M m)) (𝕊 (Nc M (Φ M (exp M m))))
    (Φ M (exp M m) ∪ single m) h8 h15 h7 , 
    rw successorisplusone M at h16,
    exact h16, 
  end

lemma sixpointsevenB: ∀ (m:M), m ∈ 𝔽 → Φ M m ∈ FINITE M → (∃ (u:M), u ∈ exp M m) → 
 Φ M (exp M m) ∈ FINITE M:= 
  assume m,
  begin
    intros h hfinite h2,
    have h3:= sixpointsix M m h h2,
    have h4:= sixpointfive M m h h2,
    have h5:= xinNcx M (exp M m), 
    have h6: ((Φ M (exp M m)) ∪ (single m)) ∈ 𝕊 (Nc M (Φ M (exp M m))):=
      begin
        have h7:= successor_members M (Nc M (Φ M (exp M m))), 
        specialize h7 ((Φ M (exp M m)) ∪ (single m)),
        rw h7,
        have h8:= xinNcx M (Φ M (exp M m)),
        use Φ M (exp M m), use m,
        simp,
        exact ⟨ h8, h4⟩,
      end,
    have h7: ((Φ M (exp M m)) ∪ (single m)) ∈ (Nc M (Φ M m) ∩ 𝕊 (Nc M (Φ M (exp M m)))):=
      begin
        rw intersection_axiom, 
        split,
        {
          rw union_commutative M,
          rw← h3,
          exact xinNcx M (Φ M m), 
        },
        {
          exact h6, 
        }
      end, 
    have h8:= finitecardinals3 M (Φ M m) hfinite, 
    have h9: Φ M (exp M m) ∈ SSC (Φ M m):=
      begin
        rw ssc_members,
        split,
        {
          rw h3,
          rw union_commutative,
          have h10:= subset_union2 M (Φ M (exp M m)) (single m), 
          exact h10, 
        },
        {
          intro t,
          rw h3,
          intro h20,
          rw binary_union_axiom at h20,
          rw singleton1 M at h20,
          cases h20 with h21 h22,
          {
            rw h21 at *,
            right,
            exact h4, 
          },
          {
            left,
            exact h22, 
          }
        }
      end,
    rw ssc_members at h9,
    cases h9 with h10 h11, 
    have h12: Φ M (exp M m) ∈ FINITE M:=
      begin
        have h13:= separablefinite M (Φ M m) hfinite (Φ M (exp M m)) h10, 
        unfold separable_subset at h13,
        apply h13,     
        split,
        {
          exact h10, 
        },
        {
          rw full_extensionality,
          intro t,
          specialize h11 t,
          rw binary_union_axiom ,
          rw minus_members, 
          split,
          {
            intro h40,
            have h41:= h11 h40,
            cases h41 with h42 h43,
            {
              exact or.inl h42,
            },
            {
              right,
              exact ⟨ h40, h43⟩, 
            }
          },
          {
            intro h14,
            rw or_comm at h14,
            cases h14 with h15 h16,
            {
              exact h15.left, 
            },
            {
               exact member_subset M (Φ M (exp M m)) (Φ M m) t h10 h16,
            }
          }
        }
      end,
    exact h12, 
  end

lemma finiteDNS: ∀ (P:M), ∀ (B:M), B ∈ FINITE M → (∀ (x:M),(x ∈ B → ¬¬ x ∈ P)) → ¬¬ ∀ (x:M), x ∈ B → x ∈ P :=
  begin 
    have base: Λ ∈ W_finiteDNS M:=
      begin
        rw W_finiteDNS_members, 
        split,
        {
          exact lambda_finite M,
        },
        {
          intros P  h, 
          have h3: ∀ (x:M), x ∈ Λ  → x ∈ P:=
            begin
              intros x h4,
              have h5:= emptyset_axiom x,
              contradiction,
            end,
          exact double_negate (∀ (x : M), x ∈ Λ → x ∈ P) h3,
        }
      end,
    have step: adjoin_closed M (W_finiteDNS M):=
      begin
        unfold adjoin_closed, 
        intros B c h,
        rw W_finiteDNS_members at h,
        rw W_finiteDNS_members,
        cases h with h1 h2, 
        cases h1 with h3 h4,
        split,
        {
          have h5:= finite_adjoin M B c ⟨ h3, h2⟩,
          exact h5,
        },
        { have h100:=empty_or_inhabited M B h3,
          cases h100 with h101 h102,
          {  
            have h103:= base, 
            rw W_finiteDNS_members at h103, 
            cases h103 with h104 h105,
            rw h101 at *,
            intros P h106,
            have h107 := empty_union_x M (single c), 
            simp_rw h107 at *,
            simp_rw singleton1, 
            simp_rw singleton1 at h106,
            specialize h106 c,
            have h200: ¬¬ c ∈ P:=
              begin
                apply h106,
                exact refl c, 
              end,
            intro h107,
            have h108: (∀ (x:M), x = c → x ∈ P) ↔ c ∈ P:=
              begin
                split,
                { 
                  intro h109,
                  contradiction,
                },
                {
                  intro h109,
                  intros x h110,
                  rw h110,
                  exact h109,
                }
              end,
            rw h108 at h107, 
            contradiction, 
          },
          {
            cases h102 with u h103,
            intros P h10,
            have h11: ∀ (x:M), x ∈ B → ¬¬ x ∈ P:=
              assume x,
              begin
                intro h11,
                have h12:= adjoin_member2 M x c B h11, 
                have h13:= h10 x h12, 
                exact h13,
              end,
            have h12: ¬¬ c ∈ P:=
              begin
                have h13:= adjoin_member M c B,
                have h14:= h10 c h13, 
                exact h14,
              end,
            have h13: ∀ (x:M), x ∈ B →  ¬¬ (x ∈ P ∧ c ∈ P):=
              begin
                intros x hx,
                rw notnot_and, 
                split,
                {
                  exact h11 x hx, 
                },
                {
                  exact h12,
                }
              end,
            have h14: ∀ (x:M), x ∈ B ∪ (single c) →  ¬¬ (x ∈ P ∧ c ∈ P):=
              assume x,
              begin
                rw binary_union_axiom, 
                intro h15,
                cases h15 with h16 h17,
                {
                  exact h13 x h16, 
                },
                {
                  rw singleton1 at h17,
                  rw h17 at *,
                  intro h18, 
                  simp at h18, 
                  contradiction, 
                }
              end,
            set Q:= finitedns_helper M P c with h20,
            have h19: ∀(x:M), x ∈ B → ¬¬ x ∈ Q:=
              assume x,
              begin
                rw h20,
                rw finitedns_helper_members,
                exact h13 x, 
              end, 
            have h21:= h4 Q h19, 
            rw h20 at h21,
            simp_rw finitedns_helper_members at h21,
            have h22: (∀ (x : M), x ∈ B → x ∈ P ∧ c ∈ P)  
            → ∀ (x : M), x ∈ B ∪ single c → ¬¬ x ∈ P:=
              begin
                intros h t,
                specialize h t,
                rw binary_union_axiom,
                rw singleton1, intro h30,
                cases h30 with h31 h32, 
                {
                  have h33:= h h31,
                  cases h33 with h34 h35, 
                  exact double_negate (t ∈ P) h34, 
                },
                {
                  rw h32 at *,
                  exact h12, 
                }
              end,
            have h23:= notnot_imp ((∀ (x : M), x ∈ B → x ∈ P ∧ c ∈ P))( ∀ (x : M), x ∈ B ∪ single c → ¬¬x ∈ P) h22 h21,
            have h24: (∀ (x:M), (x ∈ B → x ∈ P ∧ c ∈ P)) ↔ 
                      ((∀ (x:M), (x ∈ B → x ∈ P)) ∧ c ∈ P):=
              begin
                split,
                {
                  intro h25,
                  split,
                  {
                    intro t,
                    intro h26,
                    have h27:= h25 t h26, 
                    exact h27.left, 
                  },
                  {
                    have h28:= h25 u h103, 
                    exact h28.right, 
                  }
                },
                {
                  intro h25, 
                  intro t,
                  intro h26,
                  cases h25 with h27 h28,
                  specialize h27 t,
                  exact ⟨ h27 h26, h28⟩, 
                }
              end, 
            have h1300 := h21,
            rw h24 at h1300, 
            have h25: (∀ (x:M), x∈ B → x ∈ P) ∧ c ∈ P ↔ ∀(x:M), x ∈ B ∪ (single c) → x ∈ P:=
              begin
                split,
                {
                  intro h26,
                  intro t,
                  rw binary_union_axiom,
                  rw singleton1, 
                  intro h27,
                  cases h26 with h28 h29,
                  specialize h28 t,
                  cases h27 with h30 h31,
                  {
                    exact h28 h30,
                  },
                  {
                    rw h31 at *,
                    exact h29, 
                  }
                },
                {
                  intro h25, 
                  split,
                  {
                    intro t,
                    intro h26,
                    specialize h25 t,
                    have h27:= adjoin_member2 M t c B h26,  
                    exact h25 h27, 
                  },
                  {
                    specialize h25 c,
                    have h27:= adjoin_member M c B, 
                    exact h25 h27, 
                  }
                }
              end, 
            rw h25 at h1300, 
            exact h1300,     
          }
        }
      end,
    have h90: (FINITE M)⊆ W_finiteDNS M  := (finite_conditions M) (W_finiteDNS M)  step base,
    rw subset_definition at h90, 
    intros P B,
    specialize h90 B,
    rw W_finiteDNS_members M at h90,
		intro h3,
		have h92:= h90 h3,
		cases h92 with h93 h94,
    exact h94 P, 
  end 

lemma maxintegerunique: ∀ (m n:M), m ∈ 𝔽 → n ∈ 𝔽 → 𝕊 m = Λ →  𝕊 n= Λ  → n = m:=
  assume m n,
  begin
    intros hm hn h h2,
    have h3:= Theorem2 M m n hm hn, 
    cases h3 with h4 h5,
    cases h4 with h6 h7,
    {
      have h8:= noinsertions M m n hm hn h6,
      rw le_definition at h8,
      cases h8 with a h9,
      cases h9 with b h10,
      cases h10 with h11 h12,
      rw h at h11,
      have h13:= emptyset_axiom a,
      contradiction,
    },
    {
      cases h7 with h8 h9,
      {
        symmetry,
        exact h8, 
      },
      {
        have h8:= noinsertions M n m hn hm h9,
        rw le_definition at h8,
        cases h8 with a h9,
        cases h9 with b h10,
        cases h10 with h11 h12,
        rw h2 at h11,
        have h13:= emptyset_axiom a,
        contradiction,
      }
    }
  end

lemma maxinteger: ∀ (m:M), m ∈ 𝔽 → 𝕊 m = Λ → ∀ (k:M), k ∈ 𝔽 → k ≤ m:=
  assume m,
  begin
    intros hm h2 k hk,
    have h3:=Theorem2 M k m hk hm,
    cases h3 with h4 h5,
    cases h4 with h6 h7,
    { 
      rw lessthan_definition at h6,
      exact h6.left,
    },
    { 
      rw letolessthan M k m hk hm,
      cases h7 with h8 h9,
      {
        exact or.inr h8,
      },
      {
        have h10:= noinsertions M m k hm hk h9,
        rw le_definition at h10,
        cases h10 with a h11,
        cases h11 with b h12,
        cases h12 with h13 h14,
        rw h2 at h13,
        have h15:= emptyset_axiom a,
        contradiction,
      }
    }
  end

lemma unenlargeable: ∀ (m U:M), m ∈ 𝔽 → 𝕊 m = Λ → U ∈ m → ∀ (x:M), ¬¬ (x ∈ U):=
  assume m U,
  begin
    intros hm h2 hU x hx,
    have h4: U ∪ (single x) ∈ 𝕊 m:=
      begin
        rw successor_members,
        use U, use x,
        split,
        {
          exact hU,
        },
        {
          split,
          {
            exact hx,
          },
          {
            simp,
          }
        }
      end,
    rw h2 at h4,
    have h5:= emptyset_axiom (U ∪ (single x)),
    contradiction,
  end

lemma notnotseparable: ∀ (X A:M), X ∈ FINITE M → A ⊆ X → ¬¬ X = (A ∪ (X-A)):=
  assume X A,
  begin 
    have h30: X ∈ FINITE M → A ⊆ X → ¬¬ X ⊆  (A ∪ (X-A)):=
      begin
        intros h h2,
        have h3: ∀ (t:M), t ∈ X → ¬¬ (t ∈ A ∨ ¬ t ∈ A) :=
          assume t,
          begin
            intro h4,
            exact notnotLEM (t ∈ A), 
          end,
        set P:= lem_set M A with h5, 
        have h6:= finiteDNS M P X h, 
        rw subset_definition, 
        simp_rw lem_set_members at h6, 
        have h7:= h6 h3,
        simp_rw binary_union_axiom, 
        simp_rw minus_members, 
        have h40: ( ∀ (x : M), x ∈ X → x ∈ A ∨ ¬x ∈ A ) → ∀ (z : M), z ∈ X → z ∈ A ∨ z ∈ X ∧ ¬z ∈ A:=
          begin
            intro h41,
            intro t,
            specialize h41 t,
            intro ht,
            have h42 := h41 ht,
            cases h42 with h43 h44,
            {
              left,
              exact h43,
            },
            {
              right,
              exact ⟨ ht, h44⟩, 
            }
          end,
        have h41:= double_negate ((∀ (x : M), x ∈ X → x ∈ A ∨ ¬x ∈ A) → ∀ (z : M), z ∈ X → z ∈ A ∨ z ∈ X ∧ ¬z ∈ A) h40,
        have h42:= push_double_negationNF ((∀ (x : M), x ∈ X → x ∈ A ∨ ¬x ∈ A))(∀ (z : M), z ∈ X → z ∈ A ∨ z ∈ X ∧ ¬z ∈ A) h41,
        revert h7,
        exact h42, 
      end,
    intros h h2,
    have h31:= h30 h h2, 
    revert h31,
    have h32: X ⊆ A ∪ X - A → X = (A ∪ X - A):=
      begin
        intro h33,
        rw full_extensionality,
        intro t,
        rw subset_definition at h33,
        specialize h33 t,
        split,
        {
          exact h33,
        },
        {
          rw binary_union_axiom,
          rw minus_members,
          intro h34, 
          cases h34 with h35 h36,
          {
            have h37:= member_subset M A X t h2 h35, 
            exact h37,
          },
          {
            exact h36.left,
          }
        }
      end,
    have h33:= double_negate (X ⊆ A ∪ X - A → X = (A ∪ X - A)) h32, 
    have h34:= push_double_negationNF ( X ⊆ A ∪ X - A ) (X = (A ∪ X - A)) h33,
    exact h34, 
  end

lemma notnotSSC: ∀ (X A:M), X ∈ FINITE M → A ⊆ X → ¬¬ A ∈ SSC X:=
  assume X A,
  begin
    intros h2 h3,
    have h4:= notnotseparable M X A h2 h3, 
    have h5: X = (A ∪ X - A) → A ∈ SSC X:=
      begin
        rw ssc_members,
        intro h6, 
        split,
        {
          exact h3,
        },
        {
          intros t h7,
          rw full_extensionality at h6,
          specialize h6 t,
          rw h6 at h7,
          rw binary_union_axiom at h7,
          rw minus_members at h7,
          cases h7 with h8 h9,
          {
            left,
            exact h8,
          },
          {
            right,
            exact h9.right, 
          }
        }
      end,
    have h6:= notnot_imp (X = (A ∪ X - A) )( A ∈ SSC X) h5,
    exact h6 h4, 
  end

lemma TneqexpT: ∀ (m:M), m ∈ 𝔽 → ¬ (𝕋 M m  = exp M (𝕋 M m)):=
  assume m,
  begin
    intros h h2,
    have h3: 𝕋 M m ∈ 𝔽 := Tfinite M m h, 
    have h4:= h3,
    rw h2 at h4,
    have h5:= cardinalsinhabited M (exp M (𝕋 M m)) h4,
    have h6:= mplusone_le_expm M (𝕋 M m) h3 h5,
    rw← h2 at h6, 
    have h7:∃ u, u ∈ 𝕊 (𝕋 M m):=
      begin
        rw le_definition at h6,
        cases h6 with a h7,
        cases h7 with b h8,
        rcases h8 with ⟨ h9, h10, h11,h12⟩,
        use a, 
        exact h9,
      end,
    have h8:=lessthansuccessor M (𝕋 M m) h3 h7,
    have h9: 𝕋 M m ≤ 𝕊 (𝕋 M m):=
      begin
        have h12:= h8,
        rw lessthan_definition at h12,
        cases h12 with h10 h11,
        exact h10,
      end,
    have h14: 𝕊 (𝕋 M m)∈ 𝔽 :=
      begin
        rw le_definition at h9,
        cases h9 with a h20,
        cases h20 with b h21,
        rcases h21 with ⟨ h22, h23, h24, h25⟩,
        have h26:= successorF M (𝕋 M m) h3 h7,
        exact h26,
      end,
    have h13:= finitetrichotomy2 M (𝕋 M m)(𝕊 (𝕋 M m)) h3 h14 h9 h6,
    have h20:= Theorem2 M (𝕋 M m)(𝕊 (𝕋 M m)) h3 h14,
    cases h20 with h21 h22,
    push_neg at h22,
    rw← h13 at h22,
    rw← h13 at h8,
    have h30:= h22 h8,
    contradiction,
  end



lemma expTinF: ∀(m:M), m ∈ 𝔽  → exp M (𝕋 M m) ∈ 𝔽 :=
  assume m,
  begin
    intro h,
    have h2:= expT_inhabited M m h,
    cases h2 with x h3, 
    have h3copy:= h3, 
    rw exp_members at h3,
    cases h3 with u h4,
    cases h4 with h5 h6,
    have h7:= Tfinite M m h,
    have h8:= finitecardinals1 M (𝕋 M m) (USC u) h7 h5,
    rw uscfinite at h8, 
    have h9:= finitepowerset M u h8,
    have h11: SSC u ∈ exp M (𝕋 M m):=  exp_members2 M (𝕋 M m) u h7 h5,
    have h12:= finiteexp M (𝕋 M m) h7 ⟨ SSC u, h11⟩, 
    exact h12,
  end

lemma TneqexpT2:∀ (m:M), m ∈ 𝔽 → ¬ (𝕋 M m = exp M (exp M (𝕋 M m))):=
  assume m,
  begin
    intros h h2,
    have h3:= Tfinite M m h,
    have h5:= mplusone_le_expm M (𝕋 M m) h3, 
    have h6:= h3,
    rw h2 at h6,
    have h7:= cardinalsinhabited M (exp M (exp M (𝕋 M m))) h6,
    cases h7 with x h8,
    rw exp_members at h8,
    cases h8 with a h9,
    cases h9 with h10 h11,
    have h12:= mplusone_le_expm M (𝕋 M m) h3 ⟨ USC a, h10⟩, 
    have h13:= cardinalsinhabited M m h,
    cases h13 with u h14,
    have h15: USC u ∈ 𝕋 M m:=
      begin
        rw T_members,
        use u,
        exact ⟨ h14, similar_reflexive M (USC u)⟩, 
      end,
    have h16: ∃ u, u ∈ exp M (exp M (𝕋 M m)):=
      begin
        use USC u,
        rw← h2, 
        exact h15, 
      end,
    have h17: exp M (𝕋 M m) ∈ 𝔽 := expTinF M m h, 
    have h18: 𝕊 (𝕋 M m) ∈ 𝔽 :=
      begin
        rw le_definition at h12,
        cases h12 with p h30,
        cases h30 with q h31,
        rcases h31 with ⟨ h32, h33, h34⟩,
        exact successorF M (𝕋 M m) h3 ⟨ p, h32⟩, 
      end, 
    have h20: exp M (𝕋 M m) < exp M (exp M (𝕋 M m)):=
      mlessthanexpm M (exp M (𝕋 M m)) h17 h16, 
    rw lessthan_definition at h20,
    cases h20 with h21 h22,
    rw h2 at h3, 
    have h23: 𝕊 (𝕋 M m) ≤ exp M (exp M (𝕋 M m)) := 
      le_transitive M (𝕊 (𝕋 M m)) (exp M (exp M (𝕋 M m))) (exp M (𝕋 M m)) h18 h3 h17 h12 h21,
    rw← h2 at h23,
    have h24:= successorincreasing M (𝕋 M m) (Tfinite M m h),
    contradiction, 
  end

lemma sixpointeightA: ∀ (m:M), m ∈ 𝔽 → 𝕀 M (𝕋 M m) zero = 𝕋 M m:=
  assume m,
  begin
    intro h,
    exact tower_base_equation M (𝕋 M m), 
  end

lemma sixpointeightB: ∀ (m:M), m ∈ 𝔽 → 𝕀 M (𝕋 M m) one = exp M (𝕋 M m):=
  assume m,
  begin
    intro h,
    rw one_definition,
    have h2: ∃ (u:M), u ∈ 𝕊 zero:=
      begin 
        use (single Λ ),
        rw← one_definition, 
        rw one_members, 
        use Λ ,
      end,
    have h3:= Tfinite M m h,
    have h4:= tower_recursion_equation M (𝕋 M m) zero (zeroF M) h2,
    rw sixpointeightA M m h at h4,
    exact h4, 
  end

lemma sixpointeightC: ∀(m:M), m ∈ 𝔽 → 𝕀 M (𝕋 M m) two = exp M (exp M (𝕋 M m)):=
  assume m,
  begin
    intro h,
    have h2: two ∈  𝔽 := twoF M, 
    have h3:= cardinalsinhabited M two h2, 
    have h4: ∃(u:M), u ∈ 𝕊 one:=
      begin
        cases h3 with x h5,
        rw two_definition at h5,
        use x,
        exact h5, 
      end,
    rw two_definition,
    have h5:= Tfinite M m h,
    have h6:= tower_recursion_equation M (𝕋 M m) one (oneF M) h4, 
    rw sixpointeightB M m h at h6, 
    exact h6, 
  end

lemma expempty: exp M Λ = (Λ :M) :=
  begin
    rw full_extensionality,
    intro t,
    rw exp_members,
    split,
    {
      intro h,
      cases h with b h2,  
      cases h2 with h3 h4,
      have h5:= emptyset_axiom (USC b), 
      contradiction, 
    },
    {
      intro h,
      have h3:= emptyset_axiom t,
      contradiction, 
    }
  end

lemma sixpointeightD:∀ (m y q:M), q ∈ 𝔽 →  m ∈ 𝔽 → y ∈ 𝔽 → 𝕀 M m y = Λ → y ≤ q → 𝕀 M m q = Λ:=
  assume m y q,
  begin
    intros hq hm hy h2,
    have base: zero ∈ ZsixpointeightD M m y:=
      begin  
        rw ZsixpointeightD_members M m y,
        split,
        {
          exact zeroF M, 
        },
        {
          intro h,
          rw tower_base_equation M,
          have h3: y = zero:=
            begin
              rw le_definition at h,
              cases h with a h4,
              cases h4 with b h5,
              rcases h5 with ⟨ h6, h7, h8, h9⟩,
              rw zero_definition at h7,
              rw singleton1 M at h7,
              rw h7 at h8,
              rw subset_of_empty M a at h8,
              rw h8 at *,
              have h10: y = zero ∨ ¬ y = zero:= corollary42 M y zero hy (zeroF M),
              cases h10 with h11 h12,
              {
                exact h11,
              },
              {
                have h13:= nonzeroissuccessor M y hy h12,
                cases h13 with p h14,
                cases h14 with h15 h16, 
                rw h16 at *,
                rw successor_members M p Λ at h6,
                cases h6 with x h17,
                cases h17 with q h18,
                rcases h18 with ⟨ h19, h20, h21⟩,
                rw full_extensionality at h21,
                specialize h21 q,
                have h22:= adjoin_member M q x,
                rw← h21 at h22,
                have h23:= emptyset_axiom q,
                contradiction,
              }
            end,
          rw h3 at *,
          rw tower_base_equation M m at h2,
          exact h2,
        } 
      end,
    have step: ∀ (q:M), q ∈ ZsixpointeightD M m y → (∃ u, u ∈ 𝕊 q) → 𝕊 q ∈ ZsixpointeightD M m y:=
      assume q,
      begin
        intros h h3,
        rw ZsixpointeightD_members at h,
        cases h with h4 h5,
        rw ZsixpointeightD_members,
        split,
        { 
          exact successorF M q h4 h3, 
        },
        { 
          intro h6,
          rw tower_recursion_equation M m q h4 h3,
          have h10: y =  q ∨ ¬ y = q:= corollary42 M y q hy h4,
          cases h10 with h11 h12,
          {
            rw h11 at *,
            have h12:= le_reflexive M q h4,
            have h13:= h5 h12,
            rw h13,
            exact expempty M, 
          },
          { 
            have h14: y ≤ q ∨ y = 𝕊 q:=  lessthansuccessor2 M y q hy h4 h6,  
            cases h14 with h15 h16, 
            {
              have h17:= h5 h15, 
              rw h17, 
              exact expempty M, 
            },
            {
              rw h16 at *,
              rw tower_recursion_equation M m q h4 h3 at h2,
              exact h2, 
            }
          }
        }
      end,
    rw F_members at hq,    
    specialize hq (ZsixpointeightD M m y),
    have h3:= hq (and.intro base step), 
    rw (ZsixpointeightD_members M m y) at h3, 
    cases h3 with h4 h5, 
    exact h5, 
  end

lemma log: ∀ (y:M),(∃ (u:M), u ∈ exp M y) → ∃ (u:M), u ∈ y:=
  assume y,
  begin
    intro h2,
    cases h2 with u h3,
    rw exp_members M at h3,
    cases h3 with a h4,
    cases h4 with h5 h6,
    use (USC a), 
    exact h5, 
  end

lemma sixpointeightDown: ∀ (y:M), y ∈ 𝔽 → ∀ (m x:M), m ∈ 𝔽 → x ∈ 𝔽 → (∃ (u:M), u ∈ 𝕀 M m y) → x ≤ y → ∃ (u:M), (u ∈ 𝕀 M m x):=
  begin
    have base: (zero:M) ∈ ZsixpointeightDown M,
      begin
        rw ZsixpointeightDown_members, 
        split,
        {
          exact zeroF M, 
        },
        {
          intros m x hm hx h3 h4,
          have h5: x = zero:= le_zero M x hx h4,
          have h6: 𝕀 M m zero = m:= 
            begin
              rw tower_base_equation M m, 
            end,
          have h7:= cardinalsinhabited M m hm, 
          cases h7 with u h8,
          use u,
          rw [h5, h6], 
          exact h8, 
        }
      end,
    have step: ∀ (y:M), y ∈ ZsixpointeightDown M → (exists u, u ∈ 𝕊 y) → (𝕊 y ∈ ZsixpointeightDown M):=
      assume y,
      begin
        intros h h2,
        rw ZsixpointeightDown_members at h,
        rw ZsixpointeightDown_members,
        cases h with h3 h4,
        split,
        {
          exact successorF M y h3 h2,
        },
        {
          intros m x hm hx h5 h6,
          have h8:= lessthansuccessor2 M x y hx h3 h6,
          cases h8 with h9 h10,
          {
            specialize h4 m x,
            cases h5 with u h10,
            rw tower_recursion_equation M m y h3 h2 at h10,
            have h11:= log M (𝕀 M m y) ⟨ u, h10⟩, 
            have h12:= h4 hm hx h11 h9,  
            exact h12, 
          },
          {
            rw h10,
            exact h5, 
          }
        }
      end, 
    intros y h, 
    rw F_members at h, 
    specialize h ( ZsixpointeightDown M),
    have h3:= h (and.intro base  step), 
    rw ( ZsixpointeightDown_members M) at h3, 
    cases h3 with h5 h6, 
    exact h6, 
  end

lemma unenlargeable_subsets: ∀ (m U x:M), m ∈ 𝔽 → 𝕊 m = Λ → U ∈ m → x ∈ FINITE M → ¬ ¬ (x ⊆ U):=
  assume m U x,
  begin
    intros hm hsm hU hx,
    have h4:= unenlargeable M m U hm hsm hU,
    have h5: ∀ (t:M), t ∈ x → ¬ ¬ (t ∈ U):=
      begin
        intros t ht,
        have h5:= h4 t,
        exact h5,
      end,
    have h6:= finitecardinals1 M m U hm hU, 
    have h7:= finiteDNS M U x hx h5, 
    rw subset_definition,
    exact h7, 
  end 

lemma unenlargeable_subsets2: ∀ (m U x), m ∈ 𝔽 → 𝕊 m = Λ → U ∈ m → x ∈ FINITE M → ¬¬ (x ∈ SSC U):=
  assume m U x,
  begin
    intros hm hsm hU hx,
    have h3:= unenlargeable_subsets M m U x hm hsm hU hx,
    have h4:= finitecardinals1 M m U hm hU,
    have h5:= finiteseparable M U x h4 hx, 
    rw ssc_definition, 
    rw union_commutative,
    rw notnot_and,
    split,
    {
      exact h3,
    },
    {
      have h6:= notnot_imp (x ⊆ U) (U = (U - x ∪ x)) h5 h3,
      exact h6,
    }
  end

lemma zero_members: ∀ (x:M), x ∈ zero ↔ x = Λ:=
  assume x,
  begin
    rw zero_definition,
    rw singleton1, 
  end

lemma Tmlessthanm: ∀ (m:M), m ∈ 𝔽 → 𝕊 m = Λ → 𝕋 M m < m:=
  assume m,
  begin
    intros hm hsm,
    have h1:= Tfinite M m hm,
    have h2:= Theorem2 M (𝕋 M m) m h1 hm,
    cases h2 with h3 h4,
    cases h3 with h4 h5,
    {
      exact h4,
    },
    {
      cases h5 with h6 h7,
      {
        have h8:= expTinF M m hm,
        rw h6 at h8,
        have h9:= mlessthanexpm M m hm (cardinalsinhabited M (exp M m) h8),
        have h10:= noinsertions M m (exp M m) hm h8 h9,
        rw le_definition at h10,
        cases h10 with a h11,
        cases h11 with b h12,
        cases h12 with h13 h14,
        have h15:= successorF M m hm ⟨ a, h13⟩,
        rw hsm at h15,
        have h16:= cardinalsinhabited M Λ h15, 
        cases h16 with x h17,
        have h18:= emptyset_axiom x,
        contradiction,
      },
      {
        have h8:= noinsertions M m (𝕋 M m) hm h1 h7,
        rw le_definition at h8,
        cases h8 with a h9,
        cases h9 with b h10,
        cases h10 with h11 h12,
        have h13:= successorF M m hm ⟨ a, h11⟩, 
        rw hsm at h13,
        have h14:=cardinalsinhabited M Λ h13,
        cases h14 with x h15,
        have h16:= emptyset_axiom x,
        contradiction,
      }
    } 
  end 


lemma doubleexpbase1: ∀ (m p κ :M), m ∈ 𝔽 → 𝕊 m = Λ → κ = exp M (𝕋 M m) → p = 𝕊 (𝕋 M m) → exp M (𝕋 M p) = (𝕋 M κ) + 
 (𝕋 M κ):=
  assume m p κ,
  begin
    intros hm hsm hk hp, 
    rw hp,
    have h1:= expTinF M m hm, 
    rw← hk at h1, 
    have h2:= Tfinite M κ h1,
    have h3:= Tsuccessor M (𝕋 M κ) h2, 
    have h4:= Tmlessthanm M m hm hsm,
    have h5:= Tfinite M m hm, 
    have h6:= noinsertions M (𝕋 M m) m h5 hm h4, 
    rw le_definition at h6,
    cases h6 with a h7,
    cases h7 with b h8,
    cases h8 with h9 h10,
    have h11:= successorF M (𝕋 M m) h5 ⟨ a, h9⟩, 
    have h12: exp M (𝕋 M p) = exp M (𝕋 M (𝕊 (𝕋 M m))):=
      begin
        rw hp,
      end,
    have h13:= cardinalsinhabited M (𝕊 (𝕋 M m)) h11,
    have h14:= Tsuccessor M (𝕋 M m) h5 h13,
    rw h14,
    have h15:= Tfinite M (𝕋 M m) h5,
    have h16:= expTinF M (𝕊 (𝕋 M m)) h11, 
    have h17:= Tsuccessor M (𝕋 M m) h5 h13,
    rw h17 at h16,
    rw hk at h1, 
    have h21:= cardinalsinhabited M (exp M (𝕋 M m)) h1,
    have h18:= expT M (𝕋 M m) h5 h21, 
    have h20:=exprec M (𝕋 M (𝕋 M m)) h15 h16,
    rw h20,
    rw h18,
    rw hk,
  end

lemma maxismax:  ∀ (m q:M), m ∈ 𝔽 → 𝕊 m = Λ → q ∈ 𝔽 → ¬ (m < q):=
  assume m q,
  begin
    intros hm hsm hq h4,
    have h5:= noinsertions M m q hm hq h4,
    rw le_definition at h5,
    cases h5 with a h6,
    cases h6 with b h7,
    cases h7 with h8 h9,
    rw hsm at h8,
    have h10:= emptyset_axiom a,
    contradiction, 
  end

lemma fourpointfiveB: ∀ (m q z:M), m ∈ 𝔽 → 𝕊 m = Λ → q ∈ 𝔽 → z ∈ 𝔽 → 𝕋 M m < q →
 ¬ (q = 𝕋 M z):=
  assume m q z,
  begin
    intros hm hsm hq hz h4 h5,
    have h26:= Tfinite M m hm,
    rw h5 at h4,
    have h6:= Theorem2 M m z hm hz,
    cases h6 with h7 h8,
    cases h7 with h9 h10,
    {
      have h10:= maxismax M m z hm hsm hz,
      contradiction,
    },
    {
      cases h10 with h11 h12,
      { 
        rw← h11 at *,
        have h8:= xnotlessthanx M (𝕋 M m) h26,
        contradiction,
      },
      {
        have h13:= Torder M z hz m hm h12,
        have h14:= Tfinite M z hz, 
        have h15:= Theorem2 M (𝕋 M m) (𝕋 M z) h26 h14,
        cases h15 with h16 h17,
        exact  h17 ⟨ h4, h13⟩,  
      }
    }
  end

lemma fourpointfiveE: ∀ (m q:M), m ∈ 𝔽 → 𝕊 m = Λ → q ∈ 𝔽 →  𝕋 M m < q →
 exp M q = Λ :=
  assume m q,
  begin
    intros hm hsm hq h4,
    rw full_extensionality,
    intro z,
    split,
    {
      intro h5,
      have h6:= exp_members M q z,
      rw h6 at h5,
      cases h5 with a h8,
      cases h8 with h9 h10,
      have h29:= finitecardinals1 M q (USC a) hq h9,
      have h31:= uscfinite M a,
      rw h31 at h29,
      have h30:= finitecardinals3 M a h29,
      have h12: USC a ∈ 𝕋 M (Nc M a):=
        begin
          have h20:= xinNcx M a,
          have h13:= Tmembers2 M a (Nc M a) h30,
          rw h13 at h20,
          exact h20,
        end,
      have h11: q = 𝕋 M (Nc M a):=
        begin
          have h15:  USC a ∈ q ∩ 𝕋 M (Nc M a)   :=
            begin
              rw intersection_axiom, 
              exact ⟨ h9, h12⟩, 
            end,
          have h31:= Tfinite M (Nc M a) h30,
          have h14:= cardinalsdisjoint M q (𝕋 M (Nc M a)) (USC a) hq h31 h15,
          exact h14, 
        end,
      have h40:= fourpointfiveB M m q (Nc M a) hm hsm hq h30 h4, 
      contradiction,
    },
    {
      intro h,
      have h2:= emptyset_axiom z,
      contradiction,
    }
  end


lemma fourpointfiveC:∀ (m p:M), m ∈ 𝔽 → 𝕊 m = Λ → p ∈ 𝔽 → exp M p ∈ 𝔽 → p ≤ 𝕋 M m:=
  assume m p,
  begin
    intros hm hsm hp h4,
    have h5:= Theorem2 M p (𝕋 M m) hp (Tfinite M m hm),
    cases h5 with h6 h7,
    cases h6 with h8 h9,
    {
      rw lessthan_definition at h8,
      exact h8.left,
    },
    {
      cases h9 with h10 h11,
      {
        rw h10,
        have h12:= le_reflexive M (𝕋 M m) (Tfinite M m hm),
        exact h12,
      },
      {
        have h13:= fourpointfiveE M m p hm hsm hp h11,
        rw h13 at h4,
        have h30:= cardinalsinhabited M Λ h4,
        cases h30 with x h31,
        have h32:= emptyset_axiom x,
        contradiction,
      }
    }
  end

lemma expTm: ∀ (m p κ :M), m ∈ 𝔽 → 𝕊 m = Λ → κ = exp M (𝕋 M m) → exp M κ = Λ :=
  assume m p κ,
  begin
    intros hm hsm hk,
    have h3:= Tfinite M m hm,
    have h2:= expTinF M m hm,
    have h10:= cardinalsinhabited M (exp M (𝕋 M m)) h2,
    have h4:= Tfinite M (𝕋 M m) h3,
    have h5:= expTinF M (𝕋 M m) h3,
    have h6:= expT M (𝕋 M m) h3 h10,
    have h7:= mlessthanexpm M (𝕋 M m) h3 h10,
    have h11:= fourpointfiveE M m (exp M (𝕋 M m)) hm hsm h2 h7,
    rw hk,
    exact h11, 
  end 

lemma doubleexpbase2: ∀ (m p κ :M), m ∈ 𝔽 → 𝕊 m = Λ → κ = exp M (𝕋 M m) → p = 𝕊 (𝕋 M m) → 
( exp M (exp M (𝕋 M p)) ∈ 𝔽  ↔ κ + κ ∈ 𝔽 ):=
  assume m p κ,
  begin
    intros hm hsm hk hp,
    have h20:= Tmlessthanm M m hm hsm,
    have h21:= Tfinite M m hm,
    have h22:= noinsertions M (𝕋 M m) m h21 hm h20,
    rw le_definition at h22,
    cases h22 with a h23,
    cases h23 with b h24,
    cases h24 with h25 h26,
    have h27:= successorF M (𝕋 M m) h21 ⟨ a, h25⟩, 
    rw←   hp at h27,
    have h3:= expTinF M p h27,
    have h5:= doubleexpbase1 M m p κ hm hsm hk hp,
    have h30:κ ∈ 𝔽 :=
      begin
        rw hk,
        have h31:= expTinF M m hm,
        exact h31,
      end,
    split,
    { --left to right
      intro h,
      have h4:= fourpointfiveC M m (exp M (𝕋 M p)) hm hsm h3 h,
      rw  h5 at h4,
      have h6:𝕋 M κ + 𝕋 M κ ∈ 𝔽 :=
        begin
          rw← h5,
          exact h3,
        end,
      have h7: ∃ (r:M), r ∈ 𝔽  ∧ 𝕋 M κ + 𝕋 M κ = 𝕋 M r:=
        begin
          have h20:= letolessthan M (𝕋 M κ + 𝕋 M κ) (𝕋 M m) h6 h21,
          rw h20 at h4,
          cases h4 with h22 h23,
          {
            have h24:= Tonto M (𝕋 M κ + 𝕋 M κ) m h6 hm h22,
            exact h24,
          },
          {
            use m,
            exact ⟨ hm, h23⟩, 
          }
        end,
      cases h7 with c h8,
      cases h8 with h9 h10,
      have h11:= fivepointthree_converse M κ h30 κ c h30 h9 h6 h10,
      rw h11,
      exact h9, 
    },
    {
      intro h,
      have h30:= Tsum M κ h30 κ h30 h,
      rw← h5 at h30,
      have h31: κ + κ ≤ m:= 
        begin
          have h32:= maxismax M m (κ + κ) hm hsm h,
          have h33:= Theorem2 M m (κ + κ) hm h,
          cases h33 with h34 h35, 
          cases h34 with h36 h37,
          {
            contradiction,
          },
          {
            cases h37 with h38 h39,
            {
              rw h38,
              exact le_reflexive M (κ+κ) h,
            },
            {
              rw lessthan_definition at h39,
              cases h39 with h40 h41,
              exact h40, 
            }
          }
        end,
      have h40:= letolessthan M (κ + κ) m h hm,
      have h41:= h40.mp h31,
      have h50: 𝕋 M (κ + κ) ≤ 𝕋 M m:=
        begin
          cases h41 with h43 h44,
          {
            have h45:= Torder M (κ+κ) h m hm h43,
            rw lessthan_definition at h45,
            exact h45.left, 
          },
          {
            rw h44,
            have h45:= le_reflexive M (𝕋 M m) h21,
            exact h45, 
          }
        end,
      rw h30 at h50, 
      have h60: (∃ (r : M), r ∈ 𝔽 ∧ exp M (𝕋 M p) = 𝕋 M r):=
        begin
          have h51:= letolessthan M (exp M (𝕋 M p)) (𝕋 M m) h3 h21,
          have h52:= h51.mp h50,
          cases h52 with h53 h54,
          {
            have h55:= Tonto M (exp M (𝕋 M p)) m h3 hm h53,
            exact h55, 
          },
          {
            use m,
            exact ⟨ hm, h54⟩, 
          }
        end, 
      cases h60 with u h61,
      cases h61 with h62 h63,
      have h64:= expTinF M u h62,
      rw← h63 at h64,
      exact h64,
    }
  end 

lemma expandT: ∀ (p:M), p ∈ 𝔽 → (exp M p ∈ 𝔽  ↔ ∃(q:M), q∈ 𝔽 ∧ p = 𝕋 M q):=
  assume p,
  begin
    intro hp,
    split,
    {  --left to right
      intro h2,
      have h3:= cardinalsinhabited M (exp M p) h2,
      cases h3 with u h4,
      have h5:= exp_members M p u,
      rw h5 at h4,
      cases h4 with a h6,
      cases h6 with h7 h8,
      have h9:= finitecardinals1 M p (USC a) hp h7,  
      have h10:= (uscfinite M a).mp h9, 
      have h11:= finitecardinals3 M a h10, 
      have h12:= xinNcx M a,
      have h13:= Tmembers2 M a (Nc M a) h11, 
      rw h13 at h12,
      have h14:  USC a ∈ p ∩ (𝕋 M (Nc M a)):=
        begin
          rw intersection_axiom,
          exact ⟨ h7, h12⟩, 
        end,
      have h15:= Tfinite M (Nc M a) h11, 
      have h16:= cardinalsdisjoint M p (𝕋 M (Nc M a)) (USC a) hp h15 h14, 
      use (Nc M a),
      exact ⟨ h11, h16⟩, 
    },
    {  --right to left
      intro hq,
      cases hq with q h4,
      cases h4 with hq h6,
      have h5:= cardinalsinhabited M q hq,
      cases h5 with u hu, 
      have h7: USC u ∈ 𝕋 M q:=
        begin
          have h8:= Tmembers2 M u q hq,
          rw h8 at hu,
          exact hu, 
        end,
      have h9:= Tfinite M q hq, 
      have h10: SSC u ∈ exp M (𝕋 M q):= 
        begin
          have h11:= exp_members2 M (𝕋 M q) u h9 h7,
          exact h11,
        end,
      rw h6,
      have h12:= finiteexp M (𝕋 M q) h9 ⟨ SSC u, h10⟩, 
      exact h12, 
    }
  end

lemma epluse: ∀ (e:M), e ∈ 𝔽  → e+e ∈ 𝔽 → 𝕊 e ∈ 𝔽 :=
  begin
    intros e he hee,
    have h3:= FregeNdecidable M,
    rw decidable_members at h3,
    specialize h3 e zero,
    have h4:= h3 ⟨ he, zeroF M⟩,
    cases h4 with h5 h6,
    {
      rw h5,
      rw← one_definition,
      exact oneF M,
    },
    {
      have h8:= cardinalsinhabited M (e+e) hee,
      cases h8 with z h9,
      have h10:= addition_members M e e z,
      rw h10 at h9,
      cases h9 with x h11,
      cases h11 with y h12,
      rcases h12 with ⟨h13, h14, h15, h16⟩,
      have h17:= finitecardinals1 M e y he h15,
      have h20:= empty_or_inhabited M y h17,
      cases h20 with h21 h22,
      {
        have h23: y ∈ zero:=
          begin
            rw h21 at *,
            rw zero_members M Λ,
          end,
        have h24: e = zero:=
          begin
            have h25:= cardinalsdisjoint M e zero y he (zeroF M),
            apply h25,
            rw intersection_axiom,
            exact ⟨ h15, h23⟩,
          end,
        rw h24 at *,
        rw←  one_definition,
        exact (oneF M),
      },
      {
        cases h22 with a h30,
        have h31: ¬ a ∈ x:=
          begin
            intros h31,
            have h32: a ∈ x ∩ y:=
              begin
                rw intersection_axiom,
                exact ⟨ h31, h30⟩,
              end,
            rw h16 at h32,
            have h33:= emptyset_axiom a,
            contradiction,
          end,
        have h40: x ∪ single a ∈ 𝕊 e:=
          begin
            rw successor_members,
            use x, use a,
            simp,
            exact ⟨ h14, h31⟩,
          end,
        have h50:= successorF M e he ⟨ ( x ∪ single a), h40⟩,
        exact h50,
      }
    }
  end

lemma Teven: ∀ (y:M), y ∈ 𝔽 → ∀ (x:M), x ∈ 𝔽  → 𝕋 M x = y + y → y+y ∈ 𝔽 →  ∃ (e:M), e ∈ 𝔽 ∧ x = e+e:=
  begin
    have base: zero ∈ Z_Teven M:=
      begin
        rw Z_Teven_members,
        split,
        {
          exact zeroF M,
        },
        {  
          intros x hx h3 h4,
          use zero,
          split,
          {
            exact zeroF M,
          },
          { 
            rw right_identityNF at *,
            have h4:= Tzero M, 
            have h5: 𝕋 M x = 𝕋 M zero:=
              begin
                rw [h3, h4],
              end,
            have h6:= Toneone M x zero hx (zeroF M) h5,
            exact h6,           
          }
        }
      end,
    have step: ∀ (y:M), y ∈ Z_Teven M → (∃(u:M), u ∈ 𝕊 y) → 𝕊 y ∈ Z_Teven M:=
      begin
        intros a h3 hsa,
        rw Z_Teven_members at h3,
        cases h3 with ha h5,
        rw Z_Teven_members,
        split,
        {
          exact successorF M a ha hsa,
        },
        {
          intros c hc h6 h40,
          rw  addition_equation at h6,
          rw←  successor_shift at h6,
          rw addition_equation at h6,
          have h7:= Fregesuccessoromits0 M (𝕊 (a+a)), 
          rw← h6 at h7,
          have h8: ¬ c = zero:=
            begin
              intro h9,
              have h10:= Tzero M,
              rw h9 at h7,
              contradiction, 
            end,
          have h9:= nonzeroissuccessor M c hc h8, 
          cases h9 with r h10,
          cases h10 with h11 h12,
          have h13:= Fregesuccessoromits0 M r,
          have h30:= Tfinite M c hc,
          have h31:= cardinalsinhabited M (𝕋 M c) h30,
          simp_rw h6 at h31, 
          have h60: 𝕊 a + 𝕊 a = 𝕊 (𝕊 (a+a)):=
            begin
              have h61: 𝕊 (a+a) = a + 𝕊 a :=
                begin
                  rw← addition_equation,
                end,
              rw h61,
              rw← addition_equation,
              rw successor_shift,
              rw successor_shift,
              rw successor_shift,
            end,
          have h62:= h40,
          rw h60 at h62,
          have h63:= Fregesuccessoromits0 M (𝕊 (a + a)),
          have h5019: a + a ∈ 𝔽:=
            begin
              have h64:= cardinalsinhabited M (𝕊 a + 𝕊 a) h40,
              cases h64 with x h65,
              rw addition_members at h65,
              cases h65 with u h66,
              cases h66 with v h67,
              rcases h67 with ⟨ h70, h71, h72, h73⟩,
              have h74:= inhabited_sum M a ha a ha,
              apply h74,
              rw successor_members at h71,
              rw successor_members at h72,
              cases h71 with z h73,
              cases h73 with p h74,
              cases h72 with w h75,
              cases h75 with q h76,
              use z ∪ w,
              cases h74 with hz h78,
              cases h76 with hw h79,
              rw addition_members,
              use z, use w,
              simp,
              split,
              {
                exact hz,
              },
              {
                split,
                {
                  exact hw,
                },
                {
                  rw h78.2 at *,
                  rw h79.2 at *,
                  rw full_extensionality,
                  intros t,
                  split,
                  {
                    intros h80,
                    rw intersection_axiom at h80,
                    rw← h73,
                    rw intersection_axiom,
                    rw binary_union_axiom,
                    rw binary_union_axiom,
                    split,
                    {
                      left,
                      exact h80.1,
                    },
                    {
                      left,
                      exact h80.2,
                    }
                  },
                  {
                    intros h81,
                    have h82:= emptyset_axiom t,
                    contradiction,
                  }
                }
              }
            end,
          have h50190:= successorF M a ha hsa,
          have h5020: 𝕊 (a+a) ∈ 𝔽:=
            begin
              rw←  addition_equation,
              have h100:= inhabited_sum M (𝕊 a) h50190 a ha,
              apply h100,
              have h64:= cardinalsinhabited M (𝕊 a + 𝕊 a) h40,
              cases h64 with x h65,
              rw addition_members at h65,
              cases h65 with u h66,
              cases h66 with v h67,
              rcases h67 with ⟨ h70, h71, h72, h73⟩,
              rw successor_members at h71,
              cases h71 with z h73,
              cases h73 with p h74,
              use z ∪ v,
              rw addition_members,
              use z, use v,
              simp,
              split,
              {
                exact h74.1,
              },
              {
                split,
                {
                  exact h72,
                },
                {
                  rw full_extensionality,
                  intros t,
                  split,
                  {
                    intros h200,
                    rw intersection_axiom at h200,
                    rw h74.2.2 at *,
                    rw← h73,
                    rw intersection_axiom,
                    split,
                    {
                      rw binary_union_axiom,
                      left,
                      exact h200.1,
                    },
                    {
                      exact h200.2,
                    }
                  },
                  {
                    intros h210,
                    have h211:= emptyset_axiom t,
                    contradiction,
                  }
                }
              }
            end,
          have h14: ¬ 𝕋 M c = 𝕊 zero:=
            begin
              intro h15,
              rw h6 at h15, 
              have h54:  ∃ (u:M), u ∈ (𝕊 zero):=
                begin
                  use (single Λ),
                  rw← one_definition, 
                  rw one_members,
                  use Λ,
                end,
              have h16:= successoroneone M (𝕊 (a+a)) zero h5020 (zeroF M) h31 h54,
              rw← h16 at h15,  
              have h56:= Fregesuccessoromits0 M (a+a),
              contradiction, 
            end,
          have h15: ¬ r = zero:=
            begin
              intro h55,
              have h56: 𝕋 M c = 𝕊 zero:=
                begin
                  rw h55 at h12,
                  have h56: 𝕋 M c = 𝕋 M (𝕊 zero):=
                    begin
                      rw h12,
                    end,
                  rw← one_definition at h56,
                  rw Tone at h56,
                  rw h56 at h14, 
                  rw one_definition at h14,
                  contradiction,
                end,
              contradiction,
            end,
          have h16:= nonzeroissuccessor M r h11 h15,
          cases h16 with t h17, 
          cases h17 with h18 h19, 
          rw h19 at h12, 
          have h21: 𝕋 M c = 𝕊 (𝕊 (𝕋 M t)):=
            begin
              rw h12,
              rw h19 at h11,
              have h23:= cardinalsinhabited M (𝕊 t) h11,
              rw Tsuccessor,
              rw Tsuccessor,
              exact h18,
              exact h23, 
              exact h11,
              rw h12 at hc,
              have h24:=cardinalsinhabited M (𝕊 (𝕊 t)) hc,
              exact h24,
            end,
          have h53: a+a ∈ 𝔽 := h5019,
          have h25: 𝕋 M t = a + a:=
            begin 
              rw h12 at h6,
              have h400:= Tsuccessor M, 
              rw Tsuccessor at h6,
              rw Tsuccessor at h6,
              have h30:= Tfinite M t h18, 
              have h131:= Tfinite M r h11,
              rw h19 at h131,
              rw Tsuccessor at h131, 
              have h32:= Tfinite M c hc,
              rw h21 at h32, 
              have h33:= cardinalsinhabited M (𝕊 (𝕊 (𝕋 M t))) h32,
              have h26:= successoroneone M (𝕊 (𝕋 M t)) (𝕊 (a+a)) h131 h5020 h33 h31,
              rw← h26 at h6,
              have h132:= cardinalsinhabited M (𝕊 (𝕋 M t)) h131, 
              have h133:= h132,
              simp_rw h6 at h133, 
              have h27:= successoroneone M (𝕋 M t) (a+a) h30 h53 h132 h133,
              rw h27,
              {
                exact h6, 
              },
              {
                exact h18,
              },
              {
                simp_rw← h19,
                exact cardinalsinhabited M r h11,
              },
              {
                exact h18,
              },
              {
                simp_rw← h19,
                exact cardinalsinhabited M r h11,
              },
              {
                rw← h19,
                exact h11, 
              },
              {
                rw← h12,
                exact cardinalsinhabited M c hc, 
              }
            end,
          have h20:= h5 t h18 h25 h53, 
          cases h20 with e h21,
          cases h21 with h22 h23,
          use (𝕊 e),
          have h302: 𝕊 (𝕊 t) = (𝕊 e) + (𝕊 e):=
            begin
              rw h23,
              rw addition_equation,
              rw← successor_shift, 
              rw addition_equation, 
            end,
          rw and_comm,
          split,
          {
            rw h12,
            exact h302, 
          },
          {
            rw h23 at h18, 
            have h303:= epluse M e h22 h18,
            exact h303,
          }
        }
      end,
    intros y h,
    rw F_members at h,
    specialize h (Z_Teven M),
    have h5:= h ⟨ base, step⟩,
    rw Z_Teven_members at h5,
    exact h5.right, 
  end

lemma successorT: ∀ (m:M), m ∈ 𝔽 → 𝕊 (𝕋 M m) ∈ 𝔽 :=
  assume m hm,
  begin
    have h3:= expTinF M m hm,
    have h4:= Tfinite M m hm,
    have h5:= cardinalsinhabited M (exp M (𝕋 M m)) h3,
    have h6:= mlessthanexpm M (𝕋 M m) h4 h5,
    have h7:= successorbounded M (𝕋 M m)(exp M (𝕋 M m)) h4 h3 h6,
    exact h7,
  end

#axioms_all   

 
