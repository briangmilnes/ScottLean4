-- This file develops the theory of addition in INF 

import inf8    
variables (M:Type) [Model M] (a b x y z u v w X R W κ μ ℓ : M)
-- using ℓ where the source text has λ because you can't use λ for a variable.

open Model 

lemma right_identityNF: ∀ (x:M) , x + zero = x:=
  assume x,
  begin
    rw full_extensionality,
    intro p,
    rw addition_members M,
    split,
    {
      intro h,
      cases h with u h2,
      cases h2 with v h3,
      rw zero_definition at h3,
      rw singleton1 M at h3,
      rcases h3 with ⟨ h4, h5, h6, h7⟩,
      rw h6 at *,
      rw x_union_empty M u at h4,
      rw h4,
      exact h5,
    },
    {
      intro h,
      use p, use Λ,
      repeat {split}, 
      {
        rw x_union_empty M p,
      },
      {
        exact h, 
      },
      {
        rw zero_definition,
        rw singleton1 M,
      },
      {
        rw x_intersect_empty M, 
      }
    }
  end

  lemma addition_equation: ∀(x y:M), x + 𝕊 y = 𝕊 (x+y):=
    assume x y,
    begin 
      rw full_extensionality,
      intro z,
      split,
      {
        intro h,
        rw addition_members M at h,
        cases h with u h2,
        cases h2 with v h3,
        rcases h3 with ⟨ h4, h5, h6, h7⟩,
        rw successor_members M at h6,
        cases h6 with w h8,
        cases h8 with c h9,
        rcases h9 with ⟨ h10, h11, h12⟩,
        rw successor_members M,
        use u ∪ w,
        use c,
        repeat{ split},
        {
          rw addition_members,
          use u, use w,
          repeat{ split},
          {
            exact h5, 
          },
          {
            exact h10, 
          },
          {
            rw h12 at *,
            rw full_extensionality,
            intro t,
            rw full_extensionality M at h7,
            specialize h7 t,
            rw intersection_axiom,
            rw intersection_axiom at h7,
            rw binary_union_axiom at h7,
            rw singleton1 M at h7,
            split,
            {
              intro h8,
              cases h8 with h100 h101,
              exact h7.mp ⟨ h100, or.inl h101⟩, 
            },
            {
              rw← h7,
              intro h9,
              cases h9 with h10 h11,
              cases h11 with h12 h13,
              {
                exact ⟨ h10, h12⟩, 
              },
              {
                rw h13 at *,
                have h14: ¬ (c ∈  Λ) := emptyset_axiom c, 
                split,
                {
                  exact h10,
                },
                {
                  have h20:= h7.mp ⟨ h10, or.inr (refl c) ⟩,
                  contradiction, 
                }
              }
            }
          }
        },
        {
          rw binary_union_axiom,
          have  h20: c ∈ v:=
            begin
              rw h12,
              rw binary_union_axiom,
              rw singleton1 M,
              right,
              exact refl c,
            end,
          push_neg,
          split,
          {
            intro h21,
            rw full_extensionality at h7,
            specialize h7 c,
            rw intersection_axiom at h7,
            have h22: ¬ c ∈ Λ := emptyset_axiom c,
            exact h22 (h7.mp ⟨ h21,h20⟩ ),
          },
          {
            exact h11, 
          }
        },
        {
          rw h4,
          rw h12,
          rw union_associative M, 
        } 
      },
      {
        intro h,
        rw successor_members M at h,
        cases h with w h2,
        cases h2 with c h3,
        rcases h3 with ⟨ h4, h5, h6⟩,
        rw addition_members at h4,
        cases h4 with u h5,
        cases h5 with v h6,
        rcases h6 with ⟨h7,h8,h9,h10⟩,
        rw h7 at h6,
        rw union_associative M at h6,
        have h11: ¬ c ∈ v:=
          begin
            intro h12,
            have h13: c ∈ w:=
              begin
                rw full_extensionality at h7,
                specialize h7 c,
                rw binary_union_axiom at h7,
                exact h7.mpr (or.inr h12), 
              end,
            contradiction, 
          end, 
        have h14: v ∪ (single c) ∈ 𝕊 y:=
          begin
            rw successor_members M,
            use v, use c,
            repeat{split},
            {
              exact h9,
            },
            {
              exact h11,
            },
          end,
        rw addition_members,
        use u,
        use v ∪ (single c),
        repeat{split},
        {
          exact h6, 
        },
        {
          exact h8,
        },
        {
          exact h14,
        },
        {
          rw full_extensionality,
          intro t,
          rw intersection_axiom,
          rw binary_union_axiom,
          rw singleton1 M,
          have h15: ¬ t ∈ Λ := emptyset_axiom t,
          rw full_extensionality at h10,
          specialize h10 t,
          rw intersection_axiom at h10,
          rw full_extensionality at h7,
          specialize h7 c,
          rw binary_union_axiom at h7,
          rw h7 at h5,
          push_neg at h5,
          rw← h10,
          split,
          {
            intro h19,
            cases h19 with h20 h21,
            cases h21 with h22 h23,
            {
              exact ⟨ h20, h22⟩,
            },
            {
              rw h23 at *,
              cases h5 with h24 h25,
              contradiction,
            }
          },
          {
            intro h20,
            exact ⟨ h20.left, or.inl h20.right⟩, 
          }
        }
      }
    end

lemma successor_shift: ∀(x y:M), x + 𝕊 y = 𝕊 x + y:=
  assume x y,
  begin
    rw full_extensionality,
    intro z,
    split,
    {
      intro h,
      rw addition_members M at h,
      cases h with u h2,
      cases h2 with w h3,
      rw successor_members M at h3,
      rcases h3 with ⟨ h4, h5, h6,h7⟩,
      cases h6 with v h8,
      cases h8 with c h9,
      rcases h9 with ⟨ h10, h11, h12⟩,
      have h13: ¬ c ∈ Λ := emptyset_axiom c, 
      have h14: ¬ c ∈ u:=
        begin
          rw h12 at h7,
          rw full_extensionality at h7,
          specialize h7 c,
          rw intersection_axiom at h7,
          rw binary_union_axiom at h7,
          rw singleton1 M at h7,
          simp at h7,
          rw← h7 at h13,
          exact h13, 
        end,
      rw addition_members M,
      use u ∪ (single c), use v,
      repeat{split},
      {
        rw full_extensionality,
        intro t,
        repeat {rw binary_union_axiom},
        rw (singleton1 M),
        rw h4,
        rw binary_union_axiom,
        rw h12,
        rw binary_union_axiom,
        rw singleton1 M,
        split,
        {
          intro h20,
          cases h20 with h21 h22,
          {
            left,left,
            exact h21,
          },
          {
            cases h22 with h23 h24,
            {
              right,
              exact h23,
            },
            {
              rw h24 at *,
              left,right,
              exact refl c,
            }
          }
        },
        {
          intro h20,
          cases h20 with h21 h22,
          {
            cases h21 with h23 h24,
            {
              left,
              exact h23,
            },
            {
              right,right,
              exact h24,
            }
          },
          {
            right,left,
            exact h22,
          }
        }
      },
      {
        rw successor_members,
        use u, use c,
        split,
        {
          exact h5,
        },
        {
          split,
          {
            exact h14,
          },
          {
            exact refl (u ∪ (single c)), 
          }
        }
      },
      {
        exact h10,
      },
      {
        rw full_extensionality,
        intro t,
        rw intersection_axiom,
        rw binary_union_axiom,
        rw singleton1 M,
        have h15: ¬ t ∈ Λ := emptyset_axiom t,
        rw h12 at h7,
        rw full_extensionality at h7,
        specialize h7 t,
        rw intersection_axiom at h7,
        rw binary_union_axiom at h7,
        rw singleton1 M at h7,
        rw← h7,
        split,
        {
          intro h20,
          cases h20 with h21 h22,
          cases h21 with h23 h24,
          { 
            exact ⟨ h23, or.inl h22⟩,
          },
          {
            rw h24 at *,
            contradiction,
          }
        },
        {
          intro h20, 
          cases h20 with h21 h22,
          cases h22 with h23 h24,
          {
            exact ⟨ or.inl h21, h23⟩, 
          },
          {
            rw h24 at *,
            contradiction, 
          }
        }
      }
    }, -- That completes the left-to-right direction, line 834
    {  -- right to left of successor-shift
      intro h,
      rw addition_members at h,
      cases h with w h2,
      cases h2 with v h3,
      rcases h3 with ⟨ h4,h5,h6,h7⟩,
      rw successor_members M at h5,
      cases h5 with u h6,
      cases h6 with c h7,
      rcases h7 with ⟨ h8, h9, h10⟩,
      rw addition_members M,
      use u, use v ∪ (single c),
      repeat{split},
      {
        rw full_extensionality,
        intro t,
        repeat {rw binary_union_axiom},
        rw (singleton1 M),
        rw h4,
        rw h10,
        repeat{rw binary_union_axiom},
        rw singleton1 M,
        split,
        {
          intro h20,
          cases h20 with h21 h22,
          {
            cases h21 with h23 h24,
            {
              left,
              exact h23,
            },
            {
              right,right,
              exact h24,
            }
          },
          {
            right,left,
            exact h22,
          }
        },
        {
          intro h20,
          cases h20 with h21 h22,
          {
            left, left,
            exact h21,
          },
          {
            cases h22 with h23 h24,
            {
              right, 
              exact h23,
            },
            {
              rw h24 at *,
              left,right,
              exact refl c,
            }
          }
        }
         
      },
      {
        exact h8,
      },
      {
        rw successor_members M,
        use v, use c,
        split, 
        {
          exact h6, 
        },
        {
          split,
          {
            rw h10 at h7,
            rw full_extensionality at h7,
            specialize h7 c,
            rw intersection_axiom at h7,
            rw binary_union_axiom at h7,
            rw singleton1 M at h7,
            have h11: ¬ c ∈ Λ := emptyset_axiom c,
            simp at h7,
            rw← h7 at h11, 
            exact h11,
          },
          {
            exact refl (v ∪ (single c)),  
          }
        }
      },
      {
        rw full_extensionality,
        intro t,
        rw intersection_axiom,
        rw binary_union_axiom,
        rw singleton1 M,
        have h11: ¬ t ∈ Λ := emptyset_axiom t,
        rw h10 at h7,
        rw full_extensionality at h7,
        specialize h7 t,
        rw intersection_axiom at h7,
        rw binary_union_axiom at h7,
        rw singleton1 M at h7,
        rw← h7,
        split,
        {
          intro h20,
          cases h20 with h21 h22, 
          cases h22 with h23 h24,
          {
            exact ⟨ or.inl h21, h23⟩, 
          },
          {
            rw h24 at *,
            contradiction, 
          }
        },
        {
          intro h20,
          cases h20 with h21 h22,
          cases h21 with h23 h24,
          {
            exact ⟨ h23, or.inl h22⟩, 
          },
          {
            rw h24 at *,
            have h25:= h7.mp ⟨ or.inr (refl c), h22⟩, 
            contradiction,
          }
        }
      }
    }
  end
 
lemma left_identityNF: ∀ (x:M), zero + x = x:=
  assume x,
  begin
    rw full_extensionality,
    intro z,
    rw addition_members M,
    split,
    {
      intro h,
      cases h with u h2,
      cases h2 with v h3,
      rw zero_definition at h3,
      rw singleton1 M at h3,
      rcases h3 with ⟨ h4,h5, h6, h7⟩,
      rw h5 at *,
      rw empty_intersect_x M at h7,
      rw empty_union_x at h4,
      rw h4 at *,
      exact h6, 
    },
    {
      intro h,
      use Λ, use z,
      rw empty_union_x M z,
      rw zero_definition,
      rw singleton1,
      rw empty_intersect_x M,
      simp,
      exact h,
    }
  end

lemma associativityNF: ∀ (x y z:M), (x+y)+z = (x+ (y+z)):=
  assume x y z,
  begin
    rw full_extensionality,
    intro t,
    rw addition_members,
    rw addition_members,
    split,
    {
      intro h,
      cases h with p h2,
      cases h2 with w h3,
      rw addition_members M at h3,
      rcases h3 with ⟨ h4, h5, h6⟩,
      cases h5 with u h7,
      cases h7 with v h8,
      rcases h8 with ⟨ h9, h10, h11, h12⟩,
      use u, use v ∪ w,
      rw h9 at h4,
      rw union_associative M at h4,
      split,
      {
        exact h4,
      },
      {
        repeat{split},
        {
          exact h10,
        },
        {
          rw addition_members M,
          use v, use w,
          repeat{split},
          {
            exact h11,
          },
          {
            exact h6.left, 
          },
          {
            rw full_extensionality,
            intro r,
            rw intersection_axiom,
            have h13: ¬ r ∈ Λ := emptyset_axiom r,
            rw full_extensionality at h12,
            specialize h12 r,
            rw intersection_axiom at h12,
            cases h6 with h13 h14,
            rw h9 at h14,
            rw full_extensionality at h14,
            specialize h14 r,
            rw intersection_axiom at h14,
            rw binary_union_axiom at h14,
            rw← h14,
            split,
            {
              intro h20,
              cases h20 with h21 h22,
              exact ⟨ or.inr h21, h22⟩, 
            },
            {
              intro h20,
              cases h20 with h21 h22,
              have h23:= h14.mp ⟨ h21, h22⟩, 
              contradiction,
            }
          }
        },
        {
          rw full_extensionality,
          intro r,
          rw intersection_axiom,
          rw binary_union_axiom,
          have h13: ¬ r ∈ Λ := emptyset_axiom r,
          rw h9 at h6,
          cases h6 with h14 h15,
          rw full_extensionality at h15,
          specialize h15 r,
          rw intersection_axiom at h15,
          rw binary_union_axiom at h15,
          rw full_extensionality at h12,
          specialize h12 r,
          rw intersection_axiom at h12,
          rw← h12,
          split,
          {
            intro h20,
            cases h20 with h21 h22,
            cases h22 with h23 h24,
            {
              have h25:= h12.mp ⟨ h21, h23⟩,
              contradiction,
            },
            {
              have h25:= h15.mp ⟨ or.inl h21, h24⟩,
              contradiction,
            }
          },
          {
            intro h20,
            cases h20 with h21 h22,
            exact ⟨ h21, or.inl h22⟩, 
          }
        }
      }
    },
    {
      intro h,
      cases h with u h2,
      cases h2 with q h3,
      rw addition_members M at h3,
      rcases h3 with ⟨ h4,h5,h6,h7⟩,
      cases h6 with v h8,
      cases h8 with w h9,
      use u ∪ v, use w, 
      rw h4,
      rcases h9 with ⟨ h10, h11, h12, h13⟩,
      rw h10 at *,
      repeat{split},
      {
        rw union_associative M,
      },
      {
        rw addition_members M,
        use u, use v,
        repeat{split},
        {
          exact h5, 
        },
        {
          exact h11,
        },
        {
          rw full_extensionality,
          intro r,
          rw intersection_axiom,
          have h14: ¬ r ∈ Λ:= emptyset_axiom r,
          rw full_extensionality at h13,
          specialize h13 r,
          rw intersection_axiom at h13,
          rw full_extensionality at h7,
          specialize h7 r,
          rw intersection_axiom at h7,
          rw binary_union_axiom at h7,
          rw← h7,
          split,
          {
            intro h20,
            cases h20 with h21 h22,
            exact ⟨ h21, or.inl h22⟩, 
          },
          {
            intro h20,
            cases h20 with h21 h22,
            cases h22 with h23 h24,
            {
              exact ⟨ h21, h23⟩, 
            },
            {
              have h25:= h7.mp ⟨ h21, or.inr h24⟩, 
              contradiction,
            }
          }
        }
      },
      {
        exact h12,
      },
      {
        rw full_extensionality,
        intro r,
        rw full_extensionality at h7,
        specialize h7 r,
        have h8: ¬ r ∈ Λ := emptyset_axiom r,
        rw intersection_axiom at h7,
        rw binary_union_axiom at h7,
        rw intersection_axiom,
        rw binary_union_axiom,
        rw full_extensionality at h13,
        specialize h13 r,
        rw intersection_axiom at h13,
        rw← h13,
        split,
        {
          intro h20,
          cases h20 with h21 h22,
          cases h21 with h23 h24,
          {
            have h25:= h7.mp ⟨ h23, or.inr h22⟩,
            contradiction, 
          },
          {
            exact ⟨ h24, h22⟩, 
          }
        },
        {
          intro h20,
          rw h13 at h20,
          contradiction,
        }
      } 
    }
  end 

lemma commutativityNF: ∀ (x y:M), x+y = y+x:=
  assume x y,
  begin
    rw full_extensionality,
    intro t,
    rw addition_members M,
    rw addition_members M,
    split,
    { 
      intro h,
      cases h with u h2,
      cases h2 with v h3,
      use v, use u,
      rcases h3 with ⟨ h4, h5, h6, h7⟩, 
      repeat{split},
      { 
        rw union_commutative M,
        exact h4,
      },
      { 
        exact h6, 
      },
      {  
        exact h5, 
      },
      { 
        rw intersection_commutative, 
        exact h7,
      },
    },
    {
      intro h,
      cases h with u h2,
      cases h2 with v h3,
      use v, use u,
      rcases h3 with ⟨ h4, h5, h6, h7⟩, 
      repeat{split},
      { 
        rw union_commutative M,
        exact h4,
      },
      { 
        exact h6, 
      },
      {  
        exact h5, 
      },
      { 
        rw intersection_commutative, 
        exact h7,
      },
    }
  end


lemma successorisplusone: ∀ (m:M),  𝕊 m = m + one:=
  assume m,
  begin
    rw one_definition,
    rw addition_equation M,
    rw right_identityNF M,
  end

lemma inhabited_sum: ∀ (μ :M), μ  ∈ 𝔽 →  ∀ (κ :M), κ  ∈ 𝔽 → (∃ u, u ∈ κ + μ ) → κ + μ ∈ 𝔽 :=
  begin
    have base: (zero:M) ∈ Z61 M:=
      begin
        rw Z61_members M,
        split,
        {
          exact zeroF M, 
        },
        {  
          intros κ h4 h5,
          rw right_identityNF M,
          exact h4, 
        }
      end,
    have step: ∀ μ ,  μ  ∈  Z61 M → (exists u, u ∈ 𝕊 μ ) →  𝕊 μ  ∈  Z61 M:=
      assume μ, 
      begin
        intros h h2,
        rw Z61_members at h,
        rw Z61_members, 
        cases h with h3 h4,
        split,
        {
          exact successorF M μ h3 h2, 
        },
        {
          intros κ h5 h6,
          simp_rw addition_equation M at h6, 
          have h6copy := h6,
          cases h6copy with u h7,
          rw successor_members at h7,
          cases h7 with x h8,
          cases h8 with a h9,
          cases h9 with h10 h11,
          have h12:= h4 κ h5 ⟨ x, h10 ⟩, 
          have h13:= Fclosed M (κ + μ ) h12 h6, 
          rw addition_equation M,
          exact h13,
        }
      end, 
    intros μ h, 
    rw F_members at h, 
    specialize h ( Z61 M),
    have h3:= h (and.intro base  step), 
    rw ( Z61_members M) at h3, 
    cases h3 with h5 h6, 
    exact h6, 
  end

lemma subterms: ∀ (p q r:M), p ∈ 𝔽 → q ∈ 𝔽 → r ∈ 𝔽 → p+q+r ∈ 𝔽 → p+q ∈ 𝔽 ∧ q+r∈ 𝔽 :=
  assume p q r,
  begin
    intros h h2 h3 h4,
    have h5:=cardinalsinhabited M (p+q+r) h4, 
    have h5copy:= h5, 
    cases h5 with x h6,
    rw addition_members at h6,
    cases h6 with a h7,
    cases h7 with b h8,
    rcases h8 with ⟨ h9, h10, h11, h12⟩,
    have h13:= inhabited_sum M q h2  p h ⟨ a, h10 ⟩, 
    rw addition_members at h10,
    cases h10 with e h13,
    cases h13 with f h14,
    rcases h14 with ⟨ h15, h16, h17, h18⟩,
    have h19: b ∪ f ∈ r + q:=
      begin
        rw addition_members,
        use b, use f,
        repeat{split},
        { 
          exact h11, 
        },
        { 
          exact h17,
        },
        { rw full_extensionality,
          intro t,
          rw intersection_axiom,
          have h19: ¬ t∈ Λ := emptyset_axiom t,
          rw full_extensionality at h18 h12,
          specialize h12 t,
          specialize h18 t,
          rw intersection_axiom at h18 h12,
          rw full_extensionality at h15, 
          specialize h15 t, 
          rw binary_union_axiom at h15,
          split,
          {
            intro h20,
            cases h20 with h21 h22,
            have h23:= h15.mpr (or.inr h22),
            have h24:= h12.mp ⟨ h23, h21⟩, 
            contradiction,
          },
          {
            intro h20,
            contradiction,
          }
        }
      end,
    have h20:e ∪ f ∈ p + q:=
      begin
        rw addition_members,
        use e, use f,
        simp,
        exact ⟨ h16, h17, h18⟩, 
      end,
    have h21:= inhabited_sum M q h2 p h ⟨ e ∪ f, h20⟩,
    have h22: f ∪ b ∈ q + r:=
      begin
        rw addition_members,
        use f, use b,
        repeat{split}, 
        { 
          exact h17, 
        },
        { 
          exact h11, 
        }, 
        {
          rw full_extensionality at h9 h12 h18 h15,
          rw full_extensionality,
          intro t,
          specialize h9 t,
          specialize h12 t,
          specialize h18 t,
          specialize h15 t, 
          rw binary_union_axiom at h9 h15,
          rw intersection_axiom at h12 h18,
          rw intersection_axiom,
          have h40: ¬ t∈ Λ := emptyset_axiom t,
          rw← h12,
          split,
          {
            intro h50,
            cases h50 with h51 h52,
            have h53:= h15.mpr (or.inr h51),
            have h54:= h12.mp ⟨ h53, h52⟩, 
            contradiction,
          },
          {
            intro h50,
            have h51:= h12.mp h50,
            contradiction,
          }
        },
      end, 
    have h23:= inhabited_sum M r h3 q h2  ⟨ f ∪ b, h22⟩, 
    exact ⟨ h21, h23⟩, 
  end

lemma subterms3: ∀ (p q:M), p ∈ 𝔽 → q ∈ 𝔽 → p+𝕊 q ∈ 𝔽 → p+q ∈ 𝔽:=
  assume p q,
  begin
    intros h1 h2 h3,
    have h5: p+ q + one ∈ 𝔽 :=
      begin
        rw one_definition,
        rw successor_shift M,
        rw right_identityNF,
        rw addition_equation at h3,
        exact h3, 
      end,
    have h6:= subterms M p q one h1 h2 (oneF M) h5,
    exact h6.left, 
  end

lemma lemma65b: ∀ (p q r s:M), p ∈ 𝔽 → q ∈ 𝔽 → r ∈ 𝔽 → s ∈ 𝔽  → p+q+r+s ∈ 𝔽 → p+q+r ∈ 𝔽:=
  assume p q r s,
  begin
    intros h h2 h3 h4 h5, 
    have h5:=cardinalsinhabited M (p+q+r+s) h5, 
    have h5copy:= h5, 
    cases h5 with x h6,
    rw addition_members at h6,
    cases h6 with a h7,
    cases h7 with b h8,
    rcases h8 with ⟨ h9, h10, h11, h12⟩, 
    rw addition_members M at h10,
    cases h10 with c h11,
    cases h11 with d h12,
    rcases h12 with ⟨ h13, h14, h15, h16⟩, 
    have h17: p+q ∈ 𝔽 := inhabited_sum M q h2 p h  ⟨ c, h14⟩, 
    have h18: ∃ u, u ∈ p + q + r:=
      begin
        set u:= c ∪ d with h19,
        use u,
        rw addition_members,
        use c, use d,
        exact ⟨ h19, h14, h15, h16⟩, 
      end,
    have h20:= inhabited_sum M r h3 (p+q ) h17 h18, 
    exact h20, 
  end


lemma subterms2: ∀ (p q:M), p ∈ 𝔽 → p + 𝕊 q ∈ 𝔽 → 𝕊 p ∈ 𝔽 :=
  assume p q,
  begin
    intros h h2,
    have h3:= cardinalsinhabited M (p + 𝕊 q) h2,
    cases h3 with u h4,
    rw addition_members M at h4,
    cases h4 with a h5,
    cases h5 with b h6,
    rw successor_members M at h6,
    rcases h6 with ⟨h7, h8,h9, h10⟩,
    cases h9 with x h11,
    cases h11 with c h12,
    rcases h12 with ⟨ h13, h14, h15⟩,
    rw full_extensionality at h15,
    specialize h15 c,
    rw binary_union_axiom at h15,
    rw singleton1 M at h15,
    have h16: c ∈ b := 
      begin 
        simp at h15,
        exact h15, 
      end, 
    rw full_extensionality at h10,
    specialize h10 c,
    rw intersection_axiom at h10,
    have h17: ¬ c ∈ Λ:= emptyset_axiom c,
    have h18: ¬ c ∈ a := 
      begin 
        intro h20,
        have h21:= h10.mp ⟨ h20, h16⟩, 
        contradiction,
      end, 
    have h19: a ∪ (single c) ∈ 𝕊 p:=
      begin
        rw successor_members M,
        use a, use c,
        simp,
        exact ⟨ h8, h18⟩,  
      end,
    have h20:= successorF M p h ⟨ a ∪ (single c), h19⟩,
    exact h20,
  end


lemma ppluspplusp: ∀(m:M), m ∈ 𝔽 → ((∃ p:M,  p ∈ 𝔽 ∧ m = p + p + p) ∨ (∃ p:M,  p ∈ 𝔽 ∧ m = p + p + p + one)
∨ (∃ p:M, p ∈ 𝔽 ∧ m = p + p + p+two)):=
  assume m, 
  begin
    intro h, 
    have base: (zero:M) ∈   Z62a M :=
      begin 
        rw  Z62a_members M,
        split,
        { 
          exact zeroF M, 
        },
        { 
          left,
          use zero,
          rw right_identityNF M,
          rw right_identityNF M,
          exact ⟨ zeroF M, refl zero ⟩, 
        }
      end,
    have step: ∀ k,  k ∈  Z62a M → (exists u, u ∈ 𝕊 k) →  𝕊 k ∈  Z62a M:=
      assume k,
      begin
        intros h4 h3,
        rw  Z62a_members at h4,
        rw  Z62a_members,
        cases h4 with h5 h6,
        cases h6 with h7 h8 h9,
        {
          split,
          {
            exact successorF M k h5 h3, 
          },
          {
            cases h7 with p h8,
            right,left,
            use p,
            split,
            {
              exact h8.left, 
            },
            { 
              cases h8 with h9 h10,
              rw h10,
              rw←  addition_equation M, 
              rw successorisplusone M,
              repeat { rw associativityNF },
            }
          }
        },
        {  
          cases h8 with h9 h10,
          { 
            cases h9 with p h11,
            split,
            { 
              exact successorF M k h5 h3,
            },
            { 
              right, right,
              use p,
              rw two_definition, 
              cases h11 with h12 h13,
              rw h13, 
              split,
              { 
                exact h12,
              },
              {
                rw addition_equation M,    
              } 
            }
          },
          {  
            split,
            {
              exact successorF M k h5 h3,
            },
            { 
              left,
              cases h10 with p h11, 
              have h14: 𝕊 k = 𝕊 (p+p+p+two):= 
                begin 
                  cases h11 with h40 h41,
                  rw← h41,
                end, 
              rw←  addition_equation M at h14,
              rw successor_shift M at h14,
              rw two_definition at h14,
              rw← addition_equation M at h14,
              rw successor_shift M at h14,
              rw← addition_equation M at h14,
              rw successor_shift M at h14,
              rw← addition_equation M at h14, 
              rw associativityNF  at h14, 
              rw← successorisplusone M at h14,
              rw successor_shift M at h14,
              rw← addition_equation M at h14,
              rw successor_shift M p (𝕊 p) at h14, 
              use 𝕊 p,
              split,
              {
                -- line 869, must prove 𝕊 p ∈ 𝔽, which is "not quite straightforward"
                cases h11 with h12 h13,
                rw full_extensionality at h14,
                cases h3 with u h20,
                specialize h14 u,
                rw addition_members at h14,
                cases h14 with h15 h16,
                have h17:= h15 h20,
                cases h17 with a h18,
                cases h18 with b h19,
                rcases h19 with ⟨ h21, h22, h23, h24⟩,
                have h25:= successorF M p h12 ⟨ b, h23⟩,
                exact h25, 
              },
              {
                have h20: 𝕊 k ∈ 𝔽 := Fclosed M k h5 h3,
                have h15:= h14,
                exact h15, 
              }
            }
          }
        },
      end, 
    rw F_members at h, 
    specialize h ( Z62a M),
    have h3:= h (and.intro base  step), 
    rw ( Z62a_members M) at h3, 
    cases h3 with h5 h6, 
    exact h6, 
  end 

  lemma helper62: ∀(m q:M), q∈ 𝔽 → ( ∃ (u : M), u ∈ 𝕊 m)  → 𝕊 m = 𝕊 (q + q + q) → q + q + q ∈ 𝔽 :=
    assume m q, 
    begin
      intro h7,
      intro h2, 
      intro h9,
      have h9copy:= h9, 
      rw full_extensionality at h9copy,
      have h2copy:= h2,
      cases h2copy with u h10, 
      specialize h9copy u, 
      have h11:= h9copy.mp h10, 
      have h11copy:= h11,
      rw successor_members at h11copy,
      cases h11copy with x h12,
      cases h12 with c h13,
      rcases h13 with ⟨ h14, h15, h16⟩,
      have h14copy:=h14,
      rw addition_members at h14, 
      cases h14 with a h15,
      cases h15 with b h16, 
      rcases h16 with ⟨ h17, h18,h19, h20⟩,
      have h21: q + q ∈ 𝔽:= inhabited_sum M q  h7 q h7 ⟨ a,h18 ⟩, 
      have h22: q + q + q ∈ 𝔽 := inhabited_sum M q h7 (q+q) h21 ⟨x, h14copy⟩,
      exact h22, 
    end
    
    lemma helper62b: ∀(m p:M), p∈ 𝔽 → ( ∃ (u : M), u ∈ 𝕊 m)  → 𝕊 m = p + p + p → p + p + p ∈ 𝔽 :=
    assume m p, 
    begin
      intro h6,
      intro h2, 
      intro h8,
      have h14: ¬ p = (zero:M) :=
        begin
          intro h15, 
          rw h15 at h8,
          repeat { rw right_identityNF at h8},
          have h16:= Fregesuccessoromits0 M m, 
          contradiction, 
        end,
      have h15:= nonzeroissuccessor M p h6 h14, 
      cases h15 with r h16,
      cases h16 with h17 h18,
      rw h18 at h8,
      have h19: ∃ u, u ∈ 𝕊 r:=
        begin
          rw← h18, 
          have h20:= cardinalsinhabited M p h6,
          exact h20, 
        end,
      have h8copy:= h8, 
      rw full_extensionality at h8copy,
      have h2copy:= h2,
      cases h2copy with u h10, 
      specialize h8copy u, 
      have h11:= h8copy.mp h10, 
      have h11copy:= h11,
      rw addition_equation at h11copy, 
      rw successor_members at h11copy, 
      cases h11copy with x h12,
      cases h12 with c h13, 
      rcases h13 with ⟨ h14, h15, h16⟩,
      have h14copy:=h14,
      rw addition_members at h14, 
      cases h14 with a h15,
      cases h15 with b h16, 
      rcases h16 with ⟨ h27, h28,h29, h30⟩,
      rw←  h18 at h28, 
      have h21: p+p ∈ 𝔽:= inhabited_sum M p  h6 p h6 ⟨ a,h28 ⟩, 
      rw←  h18 at h11,
      have h22:= inhabited_sum M p h6 (p+p) h21 ⟨ u, h11⟩, 
      exact h22, 
    end

 lemma helper62c: ∀(m p:M), p∈ 𝔽 → ( ∃ (u : M), u ∈ 𝕊 m)  → 𝕊 m = p + p + p →
 ∃ (r:M), p = 𝕊 r ∧  p + p + r ∈ 𝔽  ∧ r ∈ 𝔽 :=
    assume m p, 
    begin
      intro h6,
      intro h2, 
      intro h8,
      have h14: ¬ p = (zero:M) :=
        begin
          intro h15, 
          rw h15 at h8,
          repeat { rw right_identityNF at h8},
          have h16:= Fregesuccessoromits0 M m, 
          contradiction, 
        end,
      have h15:= nonzeroissuccessor M p h6 h14, 
      cases h15 with r h16,
      cases h16 with h17 h18,
      rw h18 at h8,
      have h19: ∃ u, u ∈ 𝕊 r:=
        begin
          rw← h18, 
          have h20:= cardinalsinhabited M p h6,
          exact h20, 
        end,
      have h8copy:= h8, 
      rw full_extensionality at h8copy,
      have h2copy:= h2,
      cases h2copy with u h10, 
      specialize h8copy u, 
      have h11:= h8copy.mp h10, 
      have h11copy:= h11,
      rw addition_equation at h11copy, 
      rw successor_members at h11copy, 
      cases h11copy with x h12,
      cases h12 with c h13, 
      rcases h13 with ⟨ h14, h15, h16⟩,
      have h14copy := h14, 
      have h14copy2:= h14,
      rw← h18 at h14copy,
      rw← h18 at h14copy2,
      rw addition_members at h14, 
      cases h14 with a h15,
      cases h15 with b h16, 
      rcases h16 with ⟨ h27, h28,h29, h30⟩,
      use r,
      rw associativityNF M at h14copy ,
      rw addition_members at h14copy,
      cases h14copy  with e h31,
      cases h31 with f h32, 
      rcases h32 with ⟨ h33, h34,h35,h36⟩,
      have h21: p+r ∈ 𝔽:= inhabited_sum M r h17 p  h6  ⟨ f,h35 ⟩, 
      have h22:= cardinalsinhabited M (p+r) h21,
      cases h22 with w h23,
      rw associativityNF M at h14copy2, 
      have h40:= inhabited_sum M  (p+r) h21 p h6 ⟨ x, h14copy2⟩,
      rw← associativityNF M at h40,
      exact ⟨ h18, h40, h17 ⟩, 
    end

lemma ppluspplusp2: ∀(m:M), m ∈ 𝔽 → ∀ (p q:M), p ∈ 𝔽  → q ∈ 𝔽 →
(m = p + p + p → m = q + q + q + one → false) ∧ 
(m = p + p + p → m = q + q + q + two → false) ∧
(m = p + p + p + one →  m = q + q + q + two → false):=
    assume m, 
    begin
      have base: (zero:M) ∈   Z62 M :=
        begin
          rw Z62_members M,
          split,
          { 
            exact zeroF M, 
          },
          {  
            intros p q h h2,
              repeat {split},
              {
                intros h3 h4,
                rw one_definition at h4, 
                rw addition_equation at h4, 
                have h5:= Fregesuccessoromits0 M (q + q + q + zero),
                rw sym at h5,
                contradiction,
              },
              {
                intros h3 h4,
                rw two_definition at h4,
                rw addition_equation at h4,
                have h5 := Fregesuccessoromits0 M (q + q + q + one),
                rw sym at h4,
                contradiction,
              },
              {
                intros h3 h4,
                rw two_definition at h4,
                rw addition_equation at h4,
                have h5 := Fregesuccessoromits0 M (q + q + q + one),
                rw sym at h5,
                contradiction,
              }
          }
        end,
      have step: ∀ m,  m ∈  Z62 M → (exists u, u ∈ 𝕊 m) →  𝕊 m ∈  Z62 M:=
        assume m,
        begin
          intros h h2,
          rw Z62_members at h,
          rw Z62_members,
          cases h with h3 h4,
          have h2copy:= h2,
          have h5:𝕊 m ∈ 𝔽 := successorF M m h3 h2, 
          split,
          {
            exact h5, 
          },
          {
            intros p q h6 h7, 
            repeat{split},
            {
              intros h8 h9,
              rw one_definition at h9,
              rw addition_equation at h9, 
              rw right_identityNF at h9,
              have h10:q + q + q ∈ 𝔽 := helper62 M m q h7 h2 h9, 
              cases  h2copy with u h11,
              rw h9 at h11,
              have h12:= successoroneone M m (q+q+q) h3 h10 h2 ⟨ u, h11⟩,
              have h13:= h12.mpr h9,
              have h14:= helper62c M m p h6 h2 h8,
              cases h14 with r h15,
              cases h15 with h16 h50,
              cases h50 with h17 h51, 
              rw h16 at h8,
              rw addition_equation M at h8,
              rw← h16 at h8,
              have h18:u ∈ 𝕊 (p + p + r):= 
                begin 
                  rw← h8,
                  rw h9,
                  exact h11, 
                end, 
              have h19:= successoroneone M m (p + p + r) h3 h17 h2 ⟨ u, h18 ⟩ ,
              have h20:= h19.mpr h8,
              rw h16 at h20,
              rw  commutativityNF at h20,
              rw← associativityNF at h20, 
              rw  addition_equation M at h20,
              rw  addition_equation M at h20,
              rw← successor_shift M at h20,
              rw addition_equation M at h20,
              have h21: r+r+r = r+r+r +zero :=
                begin
                  rw right_identityNF, 
                end,
              rw h21 at h20,
              rw← addition_equation M at h20,
              rw← one_definition at h20,
              rw← addition_equation M at h20,
              rw← two_definition at h20,
              have h52:= h4 q r h7 h51,
              rcases h52 with ⟨ h53, h54, h55⟩, 
              have h56:= h54 h13 h20, 
              exact h56, 
            },
            {
              intros h8 h9,
              have h14:= helper62c M m p h6 h2 h8, 
              cases h14 with r h15,
              cases h15 with h16 h50,
              cases h50 with h17 h51, 
              rw h16 at h8,
              rw addition_equation M at h8,
              rw← h16 at h8,
              have h2copy := h2,
              cases  h2copy with u h11,
              have h18:u ∈ 𝕊 (p + p + r):= 
                begin 
                  rw← h8,
                  exact h11, 
                end, 
              have h19:= successoroneone M m (p + p + r) h3 h17 h2 ⟨ u, h18 ⟩ ,
              have h20:= h19.mpr h8,
              rw h16 at h20, 
              rw  commutativityNF at h20,
              rw← associativityNF at h20, 
              rw  addition_equation M at h20,
              rw  addition_equation M at h20,
              rw← successor_shift M at h20,
              rw addition_equation M at h20,
              have h21: r+r+r = r+r+r +zero :=
                begin
                  rw right_identityNF, 
                end,
              rw h21 at h20,
              rw← addition_equation M at h20,
              rw← one_definition at h20,
              rw← addition_equation M at h20,
              rw← two_definition at h20, 
              rw two_definition at h9,
              rw addition_equation M at h9,
              cases h2copy with U h60,
              rw h9 at h60,
              rw successor_members M at h60,
              cases h60 with x h61,
              cases h61 with c h62, 
              rcases h62 with ⟨ h63, h64, h65⟩, 
              have h63copy:= h63, 
              rw addition_members M at h63,
              cases h63 with a h64,
              cases h64 with b h65, 
              rcases h65 with ⟨ h66, h67, h68, h69⟩, 
              rw addition_members at h67,
              cases h67 with e h68,
              cases h68 with f h69, 
              rcases h69 with ⟨ h70, h71, h72, h73⟩, 
              have h74:= inhabited_sum M q h7 q h7 ⟨ e, h71⟩, 
              have h75:= inhabited_sum M q h7 (q+q) h74,
              have h63copy2:= h63copy,
              rw one_definition at h63copy2,
              rw addition_equation M at h63copy2,
              rw successor_members M at h63copy2,
              cases h63copy2 with Q h64,
              cases  h64 with R h65,
              rcases h65 with ⟨ h66, h67, h68⟩,
              rw right_identityNF M at h66,
              have h76:= h75 ⟨ Q, h66⟩, 
              have h77: one ∈ 𝔽 := oneF M, 
              have h78:= inhabited_sum M one h77 (q+q+q) h76 ⟨x, h63copy⟩,
              have h80:u ∈ 𝕊 (q + q + q + one):= 
                begin 
                  rw← h9,
                  exact h11, 
                end, 
              have h79:= successoroneone M m (q+q+q+one) h3 h78 h2 ⟨ u, h80⟩ , 
              rw← h79 at h9, 
              have h81:= h4 q r h7 h51, 
              rcases h81 with ⟨ h82, h83, h84⟩, 
              have h85:= h84 h9 h20,
              exact h85,
            },
            {
              intros h8 h9,
              rw one_definition at h8,
              rw two_definition at h9,
              rw addition_equation M at h8,
              rw addition_equation M at h9, 
              rw right_identityNF M at h8,
              have h10:= helper62 M m p h6 h2 h8, 
              have h2copy:= h2,
              cases h2copy with u h11,
              have h12: u ∈ 𝕊 (p+p+p):= 
                begin 
                  rw← h8,
                  exact h11, 
                end, 
              have h13:= successoroneone M m (p+p+p) h3 h10 h2 ⟨ u, h12⟩ , 
              have h14:= h13.mpr h8,
              have h9copy := h9,
              rw full_extensionality M at h9copy,
              specialize h9copy u,
              have h15:= h9copy.mp h11,
              rw successor_members M at h15,
              cases h15 with x h16,
              cases h16 with a h17,
              rcases h17 with ⟨ h18, h19, h20⟩,
              rw addition_members at h18, 
              cases h18 with A h19,
              cases h19 with B h20,
              rcases h20 with ⟨ h21, h22, h23, h24⟩, 
              have h22copy:= h22, 
              rw addition_members at h22, 
              cases h22 with C h23,
              cases h23 with D h24, 
              rcases h24 with ⟨ h25, h26, h27, h28⟩, 
              have h29: q+q ∈ 𝔽 := inhabited_sum M q h7 q h7 ⟨ C, h26⟩, 
              have h30: q+q+q ∈ 𝔽 := inhabited_sum M q h7 (q+q) h29 ⟨ A,h22copy⟩,
              have h31:= h9copy.mp h11, 
              rw successor_members at h31,
              cases h31 with E h32,
              cases h32 with F h33,
              rcases h33 with ⟨ h34, h35, h36⟩, 
              have h37:= inhabited_sum M  one (oneF M) (q+q+q) h30  ⟨ E, h34⟩, 
              have h38: u ∈ 𝕊 (q+q+q+one):= 
                begin 
                  rw← h9copy,
                  exact h11, 
                end, 
              have h39:= successoroneone M m (q+q+q+one) h3 h37 h2copy ⟨ u, h38⟩ , 
              have h40:= h39.mpr h9,
              have h41:= h4 p q h6 h7,
              rcases h41 with ⟨ h42, h43, h44⟩,
              have h45:= h42 h14 h40,
              exact h45,
            }
          }
        end, 
      intros h,
      rw F_members at h,  
      specialize h ( Z62 M), 
      have h3:= h (and.intro base  step), 
      rw ( Z62_members M) at h3, 
      cases h3 with h5 h6, 
      exact h6, 
    end


lemma corollary42: ∀(x y:M), x ∈ 𝔽 → y ∈ 𝔽 → x = y ∨ ¬ x = y:=
  assume x y,
  begin
    have h:𝔽 ∈ DECIDABLE M:= FregeNdecidable M, 
    rw decidable_members M at h,
    specialize h x y,
    intros h3 h4,
    exact h ⟨ h3, h4⟩, 
  end 

  lemma adds_to_zero: ∀ (p q:M), (zero:M) = p + q → p= zero :=
    assume p q,
    begin
      intro h,
      rw full_extensionality M at h,
      rw full_extensionality,
      intro t,
      have h10: (zero:M) = single Λ := zero_definition, 
      rw full_extensionality at h10, 
      rw (h10 t),
      have h11: Λ ∈ p:=
        begin
          have h12:= h10 Λ,
          have h13:= h Λ,
          rw h13 at h12,
          rw singleton1 M at h12,
          have h14: Λ ∈ p + q:= 
            begin 
              exact h12.mpr (refl Λ ),
            end,
          rw addition_members at h14, 
          cases h14 with a h15,
          cases h15 with b h16,
          rcases h16 with ⟨ h17, h18, h19, h20⟩,
          have h21: a = Λ:=
            begin
              rw full_extensionality,
              intro u,
              rw full_extensionality at h17,
              specialize h17 u,
              rw binary_union_axiom at h17,
              have h18: ¬ u ∈ Λ:= emptyset_axiom u,
              rw full_extensionality at h20,
              specialize h20 u, 
              rw intersection_axiom at h20,
              rw← h20,
              split,
              {
                intro h30,
                have h31:= h17.mpr (or.inl h30),
                contradiction,
              },
              {
                intro h30,
                exact h30.left, 
              }
            end,
          rw h21 at h18,
          exact h18,
        end,
      have h31: Λ ∈ q:=
        begin
          have h12:= h10 Λ,
          have h13:= h Λ,
          rw h13 at h12,
          rw singleton1 M at h12,
          have h14: Λ ∈ p + q:= 
            begin 
              exact h12.mpr (refl Λ),
            end,
          rw addition_members at h14, 
          cases h14 with a h15,
          cases h15 with b h16,
          rcases h16 with ⟨ h17, h18, h19, h20⟩,
          have h21: b = Λ:=
            begin
              rw full_extensionality,
              intro u,
              rw full_extensionality at h17,
              specialize h17 u,
              rw binary_union_axiom at h17,
              have h18: ¬ u ∈ Λ:= emptyset_axiom u,
              rw full_extensionality at h20,
              specialize h20 u, 
              rw intersection_axiom at h20,
              rw h17,
              split,
              {
                intro h40,
                right,
                exact h40,
              },
              {
                intro h40,
                cases h40 with h41 h42,
                {
                  have h43:= h17.mpr (or.inl h41),
                  contradiction,
                },
                { 
                  exact h42, 
                }
              }
            end,
          rw h21 at h19,
          exact h19,
        end,
       -- line 868  
      rw h10 at *,
      rw singleton1 M at *,
      have h11: p = zero:=
        begin
          rw full_extensionality,
          intro a,
          split,
          { 
            intro h32,
            specialize h a,
            rw addition_members at h,
            cases h with h33 h34,
            apply h34,
            use a, use Λ,
            rw x_union_empty M a,
            rw intersection_commutative,
            rw empty_intersect_x M a, 
            simp,
            exact ⟨ h32, h31⟩, 
          },
          {
            intro h32,
            rw zero_definition at h32,
            rw singleton1 at h32,
            rw h32,
            exact h11, 
          }
        end,
      rw h11,
      rw zero_definition,
      rw singleton1 M,
    end

lemma dividebytwo: ∀(m:M), m ∈ 𝔽  → m+m ∈ 𝔽  → ∀ (n:M), n ∈ 𝔽 →  m+m = n+n → n = m:=
  begin
    have base: zero ∈ Zdividebytwo M:=
      begin
        rw Zdividetbytwo_members,
        split,
        {
          exact zeroF M,
        },
        { 
          intros h n h2 h3, 
          rw right_identityNF at h3,
          exact adds_to_zero M n n h3, 
        }
      end,
    have step: ∀ (m:M), m ∈ Zdividebytwo M → (∃ u, u ∈ 𝕊 m) → (𝕊 m ∈ Zdividebytwo M):=
      begin 
        intros m h h2,
        rw Zdividetbytwo_members at h, 
        cases h with h3 h4,
        rw Zdividetbytwo_members,
        split,
        {
          exact successorF M m h3 h2,
        },
        { 
          intros h20 n h5 h6,
          have h7:= FregeNdecidable M,
          rw decidable_members at h7,
          specialize h7 n zero,
          have h8:= h7 ⟨ h5, zeroF M⟩, 
          cases h8 with h9 h10,
          {
            rw h9 at *, 
            rw right_identityNF at h6,
            have h24: zero = 𝕊 m + 𝕊 m := 
              begin 
                symmetry,
                exact h6, 
              end,
            have h21:= adds_to_zero M (𝕊 m) (𝕊 m) h24,
            have h11:= Fregesuccessoromits0 M m,
            contradiction,
          },
          { 
            symmetry,
            have h11:= Fregesuccessoromits0 M m,
            have h12:= nonzeroissuccessor M n h5 h10, 
            cases h12 with k h13,
            cases h13 with h14 h15,
            have h20copy:= h20,
            rw h15, 
            rw h15 at h6,
            have h16: 𝕊 m + 𝕊 m = 𝕊 (𝕊 (m+m)):=
              begin
                repeat{ rw   successor_shift M},
                repeat{ rw←  addition_equation},
                rw←  successor_shift, 
                rw←  successor_shift, 
              end,
            rw h16 at h20,
            have h21: 𝕊 m + 𝕊 m = one + m + 𝕊 m:=
              begin
                rw one_definition,
                repeat{ rw←    successor_shift M},
                rw left_identityNF,
                repeat{ rw←    successor_shift M},
              end,
            have h22: 𝕊 m ∈ 𝔽 := successorF M m h3 h2,
            have h23: one + m + 𝕊 m ∈ 𝔽 := 
              begin 
                rw← h21,
                rw h16, 
                exact h20, 
              end, 
            have h24:one + m ∈ 𝔽:=
              begin
                rw one_definition,
                rw← successor_shift,
                rw left_identityNF,
                exact h22, 
              end,
            have h25:= subterms M one m (𝕊 m) (oneF M) h3 h22 h23,
            cases h25 with h26 h127, 
            have h128: 𝕊 (m+m) = m + 𝕊 m:=
              begin
                rw addition_equation, 
              end,
            have formula55A: 𝕊 (m+m) ∈ 𝔽 := 
              begin 
                rw h128,
                exact h127,
              end, 
            have h27: one + m + m = m + 𝕊 m:=
              begin
                rw one_definition, 
                rw← successor_shift,
                rw left_identityNF,
                rw successor_shift, 
              end,
            have h28: one + m + m ∈ 𝔽 := 
              begin 
                rw h27,
                exact h127,
              end,
            have h29:= subterms M one m m (oneF M) h3 h3 h28,
            cases h29 with h30 formula55B,
            have h216: 𝕊 k + 𝕊 k = 𝕊 (𝕊 (k+k)):=
              begin
                repeat{ rw   successor_shift M},
                repeat{ rw←  addition_equation},
                rw←  successor_shift, 
                rw←  successor_shift, 
              end,
            have h220: 𝕊 (𝕊 (k+k)) ∈ 𝔽:=  
              begin   
                rw← h216,
                rw← h6, 
                rw h16,
                exact h20,
              end,   
            rw←  h216 at h220,
            have h221: 𝕊 k + 𝕊 k = one + k + 𝕊 k:=
              begin 
                rw one_definition,
                repeat{ rw←    successor_shift M},
                rw left_identityNF,
                repeat{ rw←    successor_shift M},
              end, 
            have h400:∃ u, u ∈ 𝕊 k:=
              begin
                have h401: ∃ u, u ∈ n:= cardinalsinhabited M n h5,
                rw h15 at h401, 
                exact h401, 
              end,
            have h222: 𝕊 k ∈ 𝔽 := successorF M k h14 h400, 
            have h223: one + k+ 𝕊 k ∈ 𝔽 := 
              begin 
                rw← h221,
                rw← h6,
                rw h16,
                exact h20, 
              end, 
            have h224:one + k ∈ 𝔽:=
              begin
                rw one_definition,
                rw← successor_shift,
                rw left_identityNF,
                exact h222, 
              end, 
            have h225:= subterms M one k (𝕊 k) (oneF M) h14 h222 h223, 
            cases h225 with h226 h327, 
            have h328: 𝕊 (k+k) = k + 𝕊 k:=
              begin
                rw addition_equation, 
              end, 
            have formula56A: 𝕊 (k+k) ∈ 𝔽 :=
              begin 
                rw h328,
                exact h327,
              end, 
            have h227: one + k + k = k+ 𝕊 k:=
              begin
                rw one_definition, 
                rw← successor_shift,
                rw left_identityNF,
                rw successor_shift, 
              end, 
            have h228: one + k + k ∈ 𝔽 := 
              begin 
                rw h227,
                exact h327,
              end,
            have h229:= subterms M one k k (oneF M) h14 h14 h228,
            cases h229 with h230 formula56B, 

            have h31: 𝕊 k + 𝕊 k =  𝕊 (𝕊 (k+k)):=
              begin
                repeat{ rw← successor_shift}, 
                repeat{ rw←  addition_equation}, 
              end,
            have h32: 𝕊 (𝕊 (m+m)) = 𝕊 (𝕊 (k+k)):= 
              begin 
                rw← h31,
                rw← h6,
                rw h16,
              end, 
            have h420: ∃ u,u ∈ 𝕊 (𝕊 (m+m)):= cardinalsinhabited M (𝕊 (𝕊 (m+m))) h20,
            have h421: ∃ u,u ∈ 𝕊 (𝕊 (k+k)):= 
              begin 
                rw h32 at h420,
                exact h420, 
              end, 
            have h33:=  successoroneone M  (𝕊 (m+m))(𝕊 (k+k)) formula55A formula56A h420 h421,
            rw← h33 at h32,
            have h422: ∃ u, u ∈ 𝕊 (m+m):= cardinalsinhabited M (𝕊 (m+m)) formula55A,
            have h423: ∃ u, u ∈ 𝕊 (k+k):= 
              begin 
                rw h32 at h422, 
                exact h422, 
              end,
            have h424:= successoroneone M (m+m) (k+k) formula55B formula56B h422 h423,
            rw← h424 at h32,
            have h33:= h4 formula55B k h14 h32,
            rw h33, 
          }
        }
      end,
    intros m h,
    rw F_members at h,
    specialize h (Zdividebytwo M),
    have h3:= h (and.intro base  step), 
    rw Zdividetbytwo_members at h3,
    exact h3.right, 
  end


lemma cardinality_additive: ∀ (p q:M), p ∈ FINITE M → q ∈ FINITE M → p ∩ q = Λ → Nc M (p ∪ q) = Nc M p + Nc M q:=
  assume p q,
  begin
    intros hp hq h,
    have h2:(p ∪ q) ∈  Nc M (p ∪ q) := x_in_Ncx M (p ∪ q), 
    have h3: p ∈ Nc M p := x_in_Ncx M p,
    have h4: q ∈ Nc M q:= x_in_Ncx M q,
    have h5: p ∪ q ∈ Nc M p + Nc M q:=
      begin
        rw addition_members,
        use p, use q,
        exact ⟨ refl (p ∪ q), h3, h4, h⟩, 
      end,
    have h6: ¬ ( Nc M (p ∪ q) ∩ (Nc M p + Nc M q) = Λ):=
      begin
        intro h7,
        rw full_extensionality at h7,
        specialize h7 (p ∪ q),
        rw intersection_axiom at h7,
        have h8: ¬ p ∪ q ∈ Λ := emptyset_axiom (p ∪ q), 
        exact h8 (h7.mp ⟨ h2, h5⟩), 
      end,
    have h20:= finitecardinals3 M p hp, 
    have h21:= finitecardinals3 M q hq,
    have h22:  p ∪ q ∈ FINITE M :=  union M p q hp hq h, 
    have h23: Nc M (p ∪ q) ∈ 𝔽 := finitecardinals3 M (p ∪ q) h22, 
    have h24: (Nc M p + Nc M q) ∈ 𝔽 := inhabited_sum M (Nc M q) h21 (Nc M p) h20 ⟨ p ∪ q, h5⟩,
    have h9:= cardinalsdisjoint M (Nc M (p ∪ q)) (Nc M p + Nc M q) (p ∪ q) h23 h24,
    apply h9,
    rw intersection_axiom,
    exact ⟨ h2, h5⟩, 
  end

  lemma subtraction: ∀(p: M), p ∈ 𝔽  → ∀(q r:M), q ∈ 𝔽  → r ∈ 𝔽 → q+p ∈ 𝔽 → q+p = r+p → q=r:= 
    begin
      have base: zero ∈ Zsubtraction M:=
        begin
          rw Zsubtraction_members, 
          split,
          {
            exact zeroF M,
          },
          {
            intros q r hq hr h3 h4,
            repeat{ rw right_identityNF at h4},
            exact h4,
          }
        end, 
      have step: ∀ (p:M),  p ∈ Zsubtraction M → (exists u,u∈ 𝕊 p) → 𝕊 p ∈ Zsubtraction M:=
        begin
          intros p  h h2,
          rw Zsubtraction_members, 
          rw Zsubtraction_members at h,
          cases h with hp h31, 
          split,
          {
            exact successorF M p hp h2, 
          },
          {
            intros q r hq hr h3 h4,
            have h4copy := h4,
            repeat{ rw addition_equation at h4},
            have h5: q+p ∈ 𝔽:= subterms3 M q p hq hp h3,
            have h6:= cardinalsinhabited M (q+p) h5,
            have h7: r + 𝕊 p ∈ 𝔽 := 
              begin 
                rw h4copy at h3,
                exact h3, 
              end,
            have h8: r+p ∈ 𝔽 := subterms3 M r p hr hp h7,
            have h9:= cardinalsinhabited M (r+p) h8,
            have h10: 𝕊 (q+p) = q + 𝕊 p :=
              begin
                rw addition_equation,
              end,
            have h11: 𝕊 (q+p) ∈ 𝔽:= 
              begin 
                rw h10,
                exact h3,
              end,
            have h12: ∃ u, u ∈ 𝕊 (q+p):= cardinalsinhabited M (𝕊 (q+p)) h11,
            have h13: 𝕊 (r + p) = r + 𝕊 p:=
              begin
                rw addition_equation,
              end, 
            have h14: 𝕊 (r+p) ∈ 𝔽:= 
              begin 
                rw h13,
                exact h7, 
              end,
            have h15: ∃ u, u ∈ 𝕊 (r+p):= cardinalsinhabited M (𝕊 (r+p)) h14,
            have h20:= successoroneone M (q+p)(r+p)h5 h8 h12 h15,
            rw← h20 at h4,
            specialize h31 q r,
            have h32:= h31 hq hr h5 h4,
            exact h32, 
          }
        end, 
      intros p h, 
      rw F_members at h, 
      specialize h ( Zsubtraction M),
      have h3:= h (and.intro base  step), 
      rw ( Zsubtraction_members M) at h3, 
      cases h3 with h5 h6, 
      exact h6, 
    end 

lemma ssc_adjoin2: ∀ (b c:M), b ∈ FINITE M → ¬ c ∈ b → 
Nc M (SSC(b ∪ (single c))) = Nc M (SSC b) + Nc M (SSC b):=
  assume b c h2 h3,
  begin
    have h40: b ∪ (single c) ∈ FINITE M:= finite_adjoin M b c ⟨ h2, h3⟩, 
    have h41: b ∪ (single c) ∈ DECIDABLE M:= finitedecidable M (b ∪ (single c)) h40,
    rw decidable_members M at h41,
    have h42:= h41 c, 
    set f:= Wssc_adjoin2 M b c with h,
    have hcopy:= h, 
    rw full_extensionality at h, 
    have h30: Rel f:=
      begin
        rw Rel_definition,
        intros z h31,
        specialize h z,
        rw h at h31,
        rw Wssc_adjoin2_members M b c at h31,
        cases h31 with p h32,
        cases h32 with q h33,
        rcases h33 with ⟨ h34, h35, h36⟩,
        use p, use q,
        exact h34, 
      end, 
    simp_rw Wssc_adjoin2_members M b c at h,
    set R:= image M f (SSC b) with h4,
    have h5: similarity M f (SSC b) R:=
      begin
        unfold similarity,
        split,
        {
          unfold oneone,
          split,
          {
            unfold maps,
            split,
            { 
              exact h30,
            },
            {
              repeat{split},
              {
                intros x y h5,
                cases h5 with h6 h7,
                rw h4,
                rw image_members M f (SSC b) h30 y,
                use x,
                exact ⟨ h6, h7⟩, 
              },
              {
                intros x y z h5,
                rcases h5 with ⟨ h6, h7, h8⟩,
                rw hcopy at h7 h8,
                rw Wssc_adjoin2_members M b c  ‹ x,z›  at  h8, 
                rw Wssc_adjoin2_members M b c  ‹ x,y›  at  h7, 
                cases h8 with p h9,
                cases h9 with q h10,
                cases h7 with P h11,
                cases h11 with Q h12,
                rw ordered_pair_equality at h10 h12,
                rcases h12 with ⟨ h20 ,h21, h22⟩,  
                cases h20 with h23 h24,
                rcases h10 with ⟨ h25, h26,h27⟩,
                cases h25 with h28 h29, 
                rw h23 at *,
                rw h28 at *,
                rw h29 at *,
                rw h24 at *,
                rw← h21 at h26, 
                symmetry,
                exact h26,
              },
              {
                intros x h5,
                use x ∪ (single c),
                split,
                {
                  rw h4,
                  rw image_members M f (SSC b) h30,
                  use x,
                  split,
                  {
                    exact h5,
                  },
                  {
                    rw hcopy,
                    rw Wssc_adjoin2_members M b c ‹ x, x ∪ (single c) ›,
                    use x, use (x ∪ (single c)), 
                    split,
                    {
                      exact refl ‹ x, x ∪ (single c) ›, 
                    },
                    {
                      split,
                      {
                        exact refl (x ∪ (single c)),
                      },
                      {
                        exact h5, 
                      }
                    }
                  }
                },
                {
                  rw hcopy,
                  rw Wssc_adjoin2_members M b c ‹ x, x ∪ (single c) ›,
                  use x, use (x ∪ (single c)),
                  split,
                    {
                      exact refl ‹ x, x ∪ (single c) ›, 
                    },
                    {
                      split,
                      {
                        exact refl (x ∪ (single c)),
                      },
                      {
                        exact h5, 
                      }
                    }
                }
              }
            }
          },
          {
            split,
            {
              intros x y u h5,
              rcases h5 with ⟨ h6, h7, h8⟩,
              rw hcopy at h6 h7,
              rw Wssc_adjoin2_members M b c ‹ x, u › at h6,
              rw Wssc_adjoin2_members M b c ‹ y, u › at h7,
              cases h6 with p h8,
              cases h8 with q h9,
              cases h7 with P h10,
              cases h10 with Q h11,
              rw ordered_pair_equality at h9 h11,
              rcases h11 with ⟨ h12, h13, h14⟩,
              rcases h9 with ⟨ h15, h16, h17⟩, 
              cases h12 with h18 h19,
              cases h15 with h20 h21,
              rw h18 at *,
              rw h19 at *,
              rw h20 at *,
              rw h21 at *,
              have h22: (p ∪ (single c)) = (P ∪  (single c)):= 
                begin 
                  rw← h13,
                  rw← h16, 
                end,
              rw full_extensionality at h22,
              rw full_extensionality,
              intro t,
              specialize h22 t,
              repeat {rw binary_union_axiom at h22},
              repeat {rw singleton1 M at h22},
              have h43 := h42 t, 
              rw binary_union_axiom at h43,
              rw singleton1 at h43, 
              have h44: (p ∪ (single c)) = (P ∪ (single c)):= 
                begin 
                  rw← h13,
                  rw← h16, 
                end,
              rw ssc_members M at h14, 
              rw ssc_members M at h17,
              cases h14 with h18 h19,
              cases h17 with h20 h21,
              have h32: ¬ c ∈ p:=
                begin
                  intro h23,
                  have h24:= member_subset M p b c h20 h23,
                  exact h3 h24, 
                end,
              have h26: ¬ c ∈ P:=
                begin 
                  intro h27,
                  have h28:= member_subset M P b c h18 h27,
                  exact h3 h28, 
                end, 
              split, 
              { 
                intro h27, 
                have h50:= h22.mp (or.inl h27), 
                cases h50 with h51 h52,
                {
                  exact h51,
                },
                {
                  rw h52 at *,
                  contradiction,
                }
                
              },
              { 
              intro h27, 
              have h50:= h22.mpr (or.inl h27), 
              cases h50 with h51 h52,
              {
                exact h51,
              },
              {
                rw h52 at *,
                contradiction,
              }
              
            },
            },
            {
              intros x y h28,
              cases h28 with h29 h30,
              rw hcopy at h29,
              rw Wssc_adjoin2_members M b c ‹ x,y› at h29 ,
              cases h29 with u h31,
              cases h31 with v h32,
              rw ordered_pair_equality M at h32,
              rcases h32 with ⟨ h33,h34,h35⟩,
              cases h33 with h36 h37,
              rw←  h36 at *,
              rw←  h37 at *,
              exact h35, 
            }
          }
        },
        {
          unfold onto,
          intros y h36,
          rw h4 at h36,
          rw image_members M f (SSC b) h30 y at h36,
          exact h36, 
        }
      end,
    have h15: b ∈ DECIDABLE M:= finitedecidable M b h2,
    rw decidable_members M at h15,
    have h16: (b ∪ (single c)) ∈ DECIDABLE M:= finitedecidable M (b ∪ (single c)) h40,
    rw decidable_members M at h16,
    have h20:SSC (b ∪ (single c)) = ((SSC b) ∪ R) :=
      begin
        rw full_extensionality,
        intro x,
        rw binary_union_axiom,
        rw ssc_members M,
        rw ssc_members M,
        split,
        {
          intro h6,
          cases h6 with h7 h8,
          rw subset_definition at h7,
          have h8copy := h8,
          specialize h8 c,
          rw binary_union_axiom at h8,
          rw singleton1 M at h8,
          have h50:= h8copy c, 
          have h51:= adjoin_member M c b, 
          have h52:= h50 h51, 
          cases h52 with h9 h10,
          {
            right,
            rw h4,
            rw image_members M f (SSC b) h30 x,
            use x - (single c),
            split,
            {
              rw ssc_members M b,
              split,
              {
                rw subset_definition,
                intro t,
                specialize h7 t, 
                rw minus_members M,
                rw singleton1 M, 
                rw binary_union_axiom at h7,
                rw singleton1 at h7, 
                intro h40,
                cases h40 with h41 h42, 
                have h43:= h7 h41,
                cases h43 with h44 h45,
                {
                  exact h44,
                },
                {
                  contradiction,
                }
              },
              {
                intro t,
                intro h17,
                repeat{rw minus_members M},
                repeat{rw singleton1 M},
                specialize h41 t c,
                repeat{rw binary_union_axiom at h41},
                repeat{rw singleton1 M at h41}, 
                have h42: ¬ t = c := 
                  begin 
                    intro h50,
                    rw h50 at *,
                    contradiction, 
                  end,
                specialize h8copy t,
                rw binary_union_axiom at h8copy,
                rw singleton1 M at h8copy,
                have h40:= h8copy (or.inl h17), 
                cases h40 with h41 h42,
                { left, 
                  split,
                  {
                    exact h41,
                  },
                  {
                    exact h42, 
                  }
                },
                {
                  right, 
                  intro h43, 
                  cases h43 with h44 h45,
                  contradiction, 
                }
              }
            },
            {
              rw hcopy,
              rw Wssc_adjoin2_members M b c ‹ x - (single c), x ›,
              use x - (single c), use x,
              split,
              {
                exact refl ‹ x - (single c), x ›, 
              },
              {
                split,
                {
                  rw full_extensionality,
                  intro t,
                  rw binary_union_axiom,
                  rw minus_members,
                  repeat{rw singleton1 M},
                  specialize h7 t,
                  rw binary_union_axiom at h7,
                  rw singleton1 M at h7,
                  specialize h15 t c,
                  split,
                  {
                    intro h17,
                    have h18:= h7 h17,
                    cases h18 with h19 h20,
                    {
                      left,
                      split,
                      {
                        exact h17,
                      },
                      {
                        intro h31,
                        rw h31 at *,
                        contradiction,
                      }
                    },
                    {
                      right,
                      exact h20,
                    }
                  },
                  { 
                    intro h31,
                    cases h31 with h32 h33,
                    {
                      exact h32.left,
                    },
                    {
                      rw h33,
                      exact h9, 
                    }
                  }
                },
                {
                  rw ssc_members,
                  split,
                  {
                    rw subset_definition,
                    intro t,
                    rw minus_members M,
                    rw singleton1 M,
                    intro h20,
                    cases h20 with h21 h22,
                    have h23:= h7 t h21,
                    rw binary_union_axiom at h23,
                    rw singleton1 M at h23,
                    cases h23 with h33 h34,
                    {
                      exact h33,
                    },
                    {
                      contradiction,
                    }
                  },
                  {
                    intros t h17,
                    repeat { rw minus_members M},
                    repeat { rw singleton1 M},
                    have h18:= adjoin_member2 M t c b h17,
                    have h19:= h8copy t h18,
                    cases h19 with h30 h31,
                    {
                      left,
                      split,
                      {
                        exact h30,
                      },
                      {
                        intro h32, 
                        rw h32 at *, 
                        contradiction, 
                      }
                    },
                    {
                      right,
                      intro h34,
                      cases h34 with h35 h36,
                      contradiction, 
                    }
                  }
                }
              }
            }
          },
          {
            left,
            split,
            { 
              rw subset_definition, 
              intros t h11,
              have h12:= h7 t h11,
              have h13: ¬ t = c := 
                begin 
                  intro h50,
                  rw h50 at *,
                  contradiction, 
                end, 
              rw binary_union_axiom at h12,
              rw singleton1 M at h12, 
              cases h12 with h50 h51,
              {
                exact h50,
              },
              {
                contradiction,
              }
            },
            {
              intros t h17,
              have h18:= adjoin_member2 M t c b h17,
              exact h8copy t h18, 
            }
          }
        },
        {
          intro h17,
          cases h17 with h18 h19,
          {
            split,
            {
              cases h18 with h20 h21, 
              exact subset_union M x b (single c) h20, 
            },
            {
              intros t h19,
              cases h18 with h20 h21,
              rw binary_union_axiom at h19,
              rw singleton1 M at h19,
              cases h19 with h22 h23,
              {
                exact h21 t h22, 
              },
              {
                rw h23 at *,
                right,
                rw subset_definition at h20,
                specialize h20 c,
                intro h50,
                have h51:= h20 h50,
                contradiction,
              }
            }
          },
          {
            rw h4 at h19, 
            rw image_members M f (SSC b) h30 at h19, 
            cases h19 with u h20,
            cases h20 with h21 h22, 
            rw hcopy at h22, 
            rw Wssc_adjoin2_members M b c ‹ u,x › at h22,
            cases h22 with p h23,
            cases h23 with q h24,
            rw ordered_pair_equality M at h24,
            rcases h24 with ⟨ h25, h26, h27⟩,
            cases h25 with h28 h29,
            rw← h28 at *,
            rw← h29 at *,
            rw ssc_members at h27,
            cases h27 with h31 h32,
            split,
            {
              rw h26,
              rw subset_definition,
              intro t,
              rw subset_definition at h31,
              specialize h31 t,
              repeat {rw binary_union_axiom},
              repeat {rw singleton1 M},
              intro h50,
              cases h50 with h51 h53,
              { 
                have h52:= h31 h51,
                left, 
                exact h52,
              },
              {
                right,
                exact h53, 
              } 
            },
            {
              intro t,
              specialize h32 t,
              repeat {rw binary_union_axiom},
              repeat {rw singleton1 M},
              intro h33,
              cases h33 with h34 h35,
              {
                rw h26,
                repeat {rw binary_union_axiom},
                repeat {rw singleton1 M},
                have h35:= h32 h34,
                cases h35 with h50 h51,
                { 
                  left,
                  left,
                  exact h50,
                },
                {
                  right,
                  intro h52,
                  cases h52 with h53 h54,
                  {
                    contradiction,
                  },
                  {
                    rw h54 at *,
                    contradiction,
                  }
                }
              },
              {
                rw h35 at *,
                rw h26,
                repeat {rw binary_union_axiom},
                repeat {rw singleton1 M},
                left, right, 
                exact refl c, 
              }
            }
          }
        }
      end,
    have h21: similar M (SSC b) R:=
      begin
        unfold similar,
        exact ⟨ f, h5⟩, 
      end,
    have h22: Nc M (SSC b) = Nc M R:= 
      begin
        rw cardinalequality M (SSC b) R, 
        exact h21,
      end,
    have h23: ((SSC b) ∩ R) = Λ :=
      begin
        rw full_extensionality,
        intro t,
        rw intersection_axiom,
        have h24:¬ t ∈ Λ:= emptyset_axiom t,
        split,
        {
          intro h25,
          cases h25 with h26 h27,
          rw h4 at h27,
          rw image_members M f (SSC b) h30 at h27, 
          cases h27 with x h31,
          cases h31 with h32 h33,
          rw hcopy at h33, 
          rw Wssc_adjoin2_members M b c ‹ x,t › at h33,
          cases h33 with p h34,
          cases h34 with q h35,
          rw ordered_pair_equality at h35,
          rcases h35 with ⟨ h36, h37, h38⟩, 
          cases h36 with h39 h40,
          rw← h39 at *,
          rw← h40 at *,
          rw ssc_members at h38,
          cases h38 with h41 h42,
          rw h37 at *,
          rw ssc_members at h26,
          cases h26 with h43 h44,
          rw subset_definition at h43,
          specialize h43 c,
          have h45: c ∈ (x ∪ (single c)):= adjoin_member M c x,
          have h46:= h43 h45,
          contradiction, 
        },
        {
          intro h46,
          contradiction, 
        }
      end, 
    have h24: SSC b ∈ FINITE M:= finitepowerset M b h2, 
    have h25: R ∈ FINITE M:= finitesimilar M (SSC b) R h21 h24, 
    have h26: Nc M (SSC (b ∪ (single c))) = Nc M (SSC b) + Nc M R :=
      begin
        have h27:= cardinality_additive M (SSC b) R h24 h25 h23, 
        rw h20, 
        exact h27,
      end, 
    rw h22, 
    rw h22 at h26, 
    exact h26, 
  end

lemma similarity_image: ∀ (a f x b:M), similarity M f a b → x ⊆ a → similarity M f x (image M f x):=
  assume a f x b,
  begin
    intros h h2,
    unfold similarity,
    unfold similarity at h,
    cases h with h3 h4,
    unfold oneone at h3,
    rcases h3 with ⟨h5, h6, h7⟩,
    unfold onto at h4,
    unfold maps at h5,
    rcases h5 with ⟨ h16, h17, h8, h9⟩,
    
    split,
    {
      unfold oneone,
      repeat{split},
      {
        exact h16,
      },
      {
        intros t y, 
        rw image_members M f x h16 y,
        intro h10,
        cases h10 with h11 h12,
        use t,
        exact ⟨ h11, h12⟩,
      },
      {
        intros t y z h10,
        rcases h10 with ⟨ h11, h12, h13⟩, 
        have h14:t ∈ a:= member_subset M x a t h2 h11,
        have h15:= h8 t y z ⟨ h14, h12, h13⟩, 
        exact h15,
      },
      {
        intros t h10,
        have h14:t ∈ a:= member_subset M x a t h2 h10, 
        have h15:= h9 t h14,
        cases h15 with y h18,
        use y,
        rw image_members M f x h16 y, 
        split,
        { use t, 
          exact ⟨ h10, h18.right⟩, 
        },
        {
          exact h18.right, 
        } 
      },
      {
        intros t u y h10,
        rcases h10 with ⟨ h11, h12, h13⟩,
        have h14:t ∈ a:= member_subset M x a t h2 h13, 
        exact h6 t u y ⟨ h11, h12, h14⟩, 
      },
      {
        intros t y h10,
        cases h10 with h11 h12,
        rw image_members M f x h16 y at h12,
        cases h12 with u h13,
        cases h13 with h14 h15,
        have h20: u∈ a:= member_subset M x a u h2 h14,
        have h21:= h6 u t y ⟨ h15, h11, h20⟩, 
        rw h21 at *, 
        exact h14, 
      }
    },
    {
      unfold onto,
      intros y h10,
      rw image_members M f x h16 y at h10,
      cases h10 with t h11,
      use t,
      exact h11, 
    }
  end

lemma xlessthan_xplusy: ∀(x y:M), x ∈ 𝔽 → y ∈ 𝔽 → x+y ∈ 𝔽 → x ≤ x + y:=
  assume x y,
  begin
    intros hx hy h30,
    rw le_definition,
    have h2:= cardinalsinhabited M x hx,
    have h3:= cardinalsinhabited M y hy,
    have h31:= cardinalsinhabited M (x+y) h30, 
    cases h2 with a h4,
    cases h3 with b h5,
    cases h31 with c h6, 
    have h6copy := h6, 
    rw addition_members M at h6,
    cases h6 with u h7,
    cases h7 with v h8,
    rcases h8 with ⟨ h9, h10, h11, h12⟩,
    use u, use c, 
    repeat{split}, 
    {
      exact h10,
    },
    {  
      exact h6copy,
    },
    {
      rw h9,
      rw subset_definition,
      intro t,
      rw binary_union_axiom,
      intro h13,
      left,
      exact h13,
    },
    {
      rw full_extensionality,
      intro t,
      rw binary_union_axiom,
      rw minus_members,
      split,
      {
        intro h13,
        rw full_extensionality at h9,
        specialize h9 t,
        have h13copy:= h13,
        rw h9 at h13,
        rw binary_union_axiom at h13,
        cases h13 with h14 h15,
        {
          left,
          exact h14,
        },
        {
          right,
          rw full_extensionality at h12,
          specialize h12 t, 
          rw intersection_axiom at h12,
          split,
          {
            exact h13copy,
          },
          {
            intro h13,
            have h14:= h12.mp ⟨ h13, h15⟩,
            have h15:= emptyset_axiom t,
            contradiction, 
          }
        }
      },
      {
        intro h13,
        cases h13 with h14 h15,
        {
          rw full_extensionality at h9,
          specialize h9 t,
          rw binary_union_axiom at h9,
          apply h9.mpr,
          left,
          exact h14,
        },
        {
          cases h15 with h16 h17,
          exact h16, 
        }
      }
    }
  end

lemma successorbounded: ∀ (a b:M), a ∈ 𝔽 → b ∈ 𝔽 → a < b → 𝕊 a ∈ 𝔽:=
  assume a b,
  begin
    intros ha hb h3,
    rw lessthan_definition at h3,
    cases h3 with h4 h5,
    rw le_definition at h4,
    cases h4 with u h5,
    cases h5 with v h6,
    rcases h6 with ⟨ h7, h8, h9, h10⟩,
    have h11: v ∈ FINITE M := finitecardinals1 M  b v hb h8,
    have h12: u ∈ FINITE M := finitecardinals1 M  a u ha h7,
    have h13:= finitedif M v u h11 h12 h9,
    have h14:= empty_or_inhabited M (v-u) h13, 
    cases h14 with h15 h16,
    {
      have h17: u=v:=
        begin
          rw full_extensionality,
          intro t,
          rw full_extensionality at h15,
          specialize h15 t,
          rw minus_members M at h15,
          have h16:= emptyset_axiom t,
          have h16copy:= h16, 
          rw← h15 at h16, 
          split,
          {
            intro h17,
            exact member_subset M u v t h9 h17, 
          },
          { intro h50,
            have h51: t ∈ u ∨ ¬ t ∈ u:=
              begin
                rw full_extensionality at h10, 
                specialize h10 t,
                rw h10 at h50,
                rw binary_union_axiom at h50,
                rw minus_members at h50,
                cases h50 with h53 h52,
                {
                  left,
                  exact h53,
                },
                {
                  right,
                  exact h52.right, 
                }
              end, 
            cases h51 with h54 h55,
            {
              exact h54,
            },
            {
              have h56:= h16 ⟨ h50, h55⟩, 
              contradiction, 
            }
          }
        end,
      rw h17 at *,
      have h18:= (intersection_axiom a b v).mpr ⟨ h7, h8⟩, 
      have h19:= cardinalsdisjoint M a b v ha hb h18, 
      contradiction,
    },
    {
      cases h16 with c h17,
      have h18: u ∪ (single c) ∈ 𝕊 a:=
        begin
          rw successor_members,
          use u, use c,
          rw minus_members at h17,
          cases h17 with h18 h19,
          simp, 
          exact ⟨ h7, h19⟩, 
        end,
      have h20:=  successorF M a ha ⟨u ∪ (single c), h18⟩,
      exact h20, 
    }
  end


lemma exprec: ∀ (m:M), m ∈ 𝔽 → exp M (𝕊 m) ∈ 𝔽 → exp M (𝕊 m) = exp M m + exp M m:=
  assume m,
  begin
    intros h h2,
    have h3:=cardinalsinhabited M (exp M (𝕊 m)) h2,
    cases h3 with x h4,
    have h4copy:= h4,
    rw exp_members M (𝕊 m) x  at h4, 
    cases h4 with a h5,
    cases h5 with h6 h7,
    have h300:= finitecardinals0 M (exp M (𝕊 m)) x (SSC a) h2 h4copy h7,
    have h60:= successorF M m h ⟨ USC a, h6⟩,  
    have h30:= successorinhabited M m h ⟨ USC a, h6⟩ ,
    cases h30 with u h31,
    cases h31 with h32 h33,
    cases h33 with p h34,
    have h35:= finitecardinals2 M u (USC a) (𝕊 m) h60 h32 h6, 
    have h36:= similarinhabited M u (USC a) h35 ⟨ p , h34⟩, 
    cases h36 with w h37, 
    rw usc M at h37, 
    cases h37 with c h38,
    cases h38 with h39 h40,
    have h41:= finitecardinals1 M (𝕊 m) (USC a) h60 h6, 
    have h41copy:= h41,
    rw uscfinite M a at h41, 
    have h42:= finitedecidable M a h41, 
    rw decidable_members M at h42, 
    set b:= a - (single c) with h24, 
    have h25: a = (b ∪ (single c)):= 
        begin
          rw full_extensionality M,
          intro t,
          rw binary_union_axiom,
          rw singleton1, 
          rw h24,
          rw minus_members,
          rw singleton1, 
          have h26:= h42 t c,
          split,
          {
            intro h27,
            have h28:= h26 ⟨ h27, h39⟩,
            cases h28 with h29 h30,
            {
              rw h29 at *,
              right,
              exact refl c,
            },
            {
              left,
              exact ⟨ h27, h30⟩, 
            }
          },
          {
            intro h27,
            cases h27 with h28 h29, 
            {
              exact h28.left,
            },
            {
              rw h29 at *,
              exact h39, 
            }
          }
        end,
      have h26: ¬ (c ∈ b):=
        begin
          rw h24, 
          rw minus_members,
          rw singleton1,
          intro h50,
          cases h50 with h51 h52,
          contradiction,
        end,
      have h27:= usc_successor M b c h26, 
      have h28: SSC(b ∪ (single c)) ∈ exp M (𝕊 m):=
        begin
          have h29:= exp_members2 M (𝕊 m) a h60 h6, 
          rw h25 at h29,
          exact h29, 
        end,
      have h29: b ∈ FINITE M:=
        begin
          apply separablefinite M a h41 b,
          {
            rw h25,
            exact subset_union2 M b (single c), 
          },
          {
            unfold separable_subset,
            rw h25,
            split,
            {
              exact subset_union2 M b (single c),
            },
            {
              rw full_extensionality,
              intro t,
              repeat{rw binary_union_axiom},
              repeat{ rw minus_members} ,
              repeat{ rw singleton1}, 
              rw binary_union_axiom,
              rw singleton1,
              split,
              { 
                intro h30,
                cases h30 with h31 h32,
                { 
                  cases h31 with h33 h34,
                  left,
                  exact ⟨ h33, h34⟩, 
                },
                { 
                  rw h32 at *,
                  right,
                  simp,
                }
              },
              {
                intro h30,
                cases h30 with h31 h32,
                {
                  left,
                  exact h31,
                },
                {
                  cases h32 with h33 h34, 
                  rw h25, 
                  rw binary_union_axiom,
                  rw singleton1,
                  cases h33 with h34 h36,
                  {
                    left,
                    split,
                    {
                      left,
                      exact h34,
                    },
                    {
                      intro h35,
                      rw h35 at *,
                      contradiction, 
                    }
                  },
                  {
                    rw h36 at *,
                    simp, 
                  }
                }
              } 
            }
          }
        end, 
      have formula54:= ssc_adjoin2 M b c h29 h26, 
      have h50:= finitedecidable M (USC a) h41copy, 
      rw decidable_members at h50,
      have h51: single c ∈ USC a:=
        begin
          rw usc M a (single c),
          use c,
          simp,
          exact h39,  
        end,
      have h52: USC b = (USC a) - (single (single c)):=
        begin
          rw h25, 
          rw h27,
          rw full_extensionality,
          intro t,
          rw minus_members,
          rw singleton1,
          rw binary_union_axiom,
          rw singleton1,
          have h54:= h50 t (single c), 
          split,
          {
            intro h53, 
            have h55:= usc_dif M a c h39,
            rw← h24 at h55, 
            rw h55 at h53,
            rw minus_members at h53,
            cases h53 with h56 h57, 
            have h58:= h54 ⟨ h56, h51⟩, 
            rw singleton1 at h57,
            rw and_comm,
            split,
            {
              exact h57,
            },
            {
              left,
              rw h55,
              rw minus_members,
              rw singleton1,
              exact ⟨ h56, h57⟩, 
            }
          },
          {
            intro h55,
            cases h55 with h56 h57,
            cases h56 with h58 h59,
            {
              exact h58,
            },
            {
              contradiction, 
            }
          } 
        end,
      have h53:= cardinalpredecessor M m (USC a) (single c) h h6 h51, 
      rw← h52 at h53,
      have h54:= exp_members2 M m b h h53, 
      have h55:= xinNcx M (SSC b), 
      have h56:= finitepowerset M a h41, 
      have h57:= finitecardinals3 M (SSC a) h56, 
      have h58:= expdef M m b h h53, 
      rw h58,
      rw← formula54,
      rw← h25, 
      have h59: SSC a ∈ ((exp M (𝕊 m))  ∩ (Nc M (SSC a))):=
        begin
          rw intersection_axiom,
          split,
          { 
            exact h300, 
          },
          { 
            exact xinNcx M (SSC a), 
          }    
        end, 
      have h60:= cardinalsdisjoint M (exp M (𝕊 m)) (Nc M (SSC a)) (SSC a) h2 h57 h59, 
      exact h60,
  end 

lemma union2: ∀ (a:M), a ∈ FINITE M → ∀ (b:M), b ∈ FINITE M → ¬¬ a ∪ b ∈ FINITE M:=
  assume x hx,
  begin
    have base: Λ ∈ Z_union2 M x:=
      begin
        rw Z_union2_members M x,
        split,
        {
          exact lambda_finite M,
        },
        {
          have h4:= empty_union_x M x,
          have h5:= union_commutative M Λ x,
          rw h5 at h4,
          rw← h4 at hx,
          intro h,
          contradiction,
        }
      end,
    have step: ∀(y c:M),  (¬ (c ∈ y)  ∧ y ∈ Z_union2 M x) → y ∪ (single c) ∈ Z_union2 M x:=
      begin
        intros y c h101,
        cases h101 with hcy hy,
        rw Z_union2_members M x at hy,
        cases hy with h3 h4,
        rw Z_union2_members M x,
        split,
        { 
          exact finite_adjoin M y c ⟨ h3, hcy⟩,
        },
        {
          have h10: ¬ c ∈ x → x ∪ y ∈ FINITE M → (x ∪ y) ∪ (single c) ∈ FINITE M:=
            begin
              intros hc h11,
              have h12: ¬ c ∈ x ∪ y:=
                begin
                  intro h13,
                  rw binary_union_axiom at h13,
                  cases h13 with h14 h15,
                  {
                    contradiction,
                  },
                  {
                    contradiction,
                  }
                end,
              exact finite_adjoin M (x ∪ y) c ⟨ h11, h12⟩, 
            end,
          have h11: c ∈ x → x ∪ y ∈ FINITE M → (x ∪ y) ∪ (single c) ∈ FINITE M:=
            begin
              intros hc h12,
              have h13:  x ∪ y = ((x ∪ y ) ∪ (single c)):=
                begin
                  rw full_extensionality,
                  intro t,
                  repeat{rw binary_union_axiom},
                  rw singleton1,
                  split,
                  {
                    intro h,
                    left,
                    exact h,
                  },
                  {
                    intro h,
                    cases h with h14 h15,
                    {
                      exact h14,
                    },
                    {
                      rw h15,
                      left,
                      exact hc,
                    }
                  }
                end,
              rw h13 at h12,
              exact h12,
            end,
          have h12: c ∈ x ∨ ¬ c ∈ x → x ∪ y ∈ FINITE M → x ∪ y ∪ single c ∈ FINITE M:=
            begin
              intro h,
              cases h with h13 h14,
              {
                exact h11 h13,
              },
              {
                exact h10 h14,
              }
            end,
          have h33: ¬¬ (c ∈ x ∨ ¬ c ∈ x):= notnotLEM (c ∈ x),
          have h34:= double_negate (c ∈ x ∨ ¬c ∈ x → x ∪ y ∈ FINITE M → x ∪ y ∪ single c ∈ FINITE M) h12,
          have h35:= push_double_negationNF ( c ∈ x ∨ ¬c ∈ x )(x ∪ y ∈ FINITE M → x ∪ y ∪ single c ∈ FINITE M) h34 h33,
          have h36:= push_double_negationNF (x ∪ y ∈ FINITE M )( x ∪ y ∪ single c ∈ FINITE M) h35 h4,
          have h37:= union_associative M x y (single c),
          rw← h37,
          exact h36,
        }
      end,
    intros y hy,
    rw finite_members at hy,
    have h5:= hy (Z_union2 M x) ⟨ base,step⟩, 
    rw Z_union2_members M x at h5,
    exact h5.right,
  end



#axioms_all? --This file is clean    


