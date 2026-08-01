 -- cardinal exponentiation

import inf7 

variables (M:Type) [Model M] (a b x y z u v w X R W κ μ ℓ : M)
-- using ℓ where the source text has λ because you can't use λ for a variable.

open Model 

lemma xnotequalsuccessorx: ∀ (x:M), x ∈ 𝔽 → ¬( x = 𝕊 x):=
  assume x,
  begin
    intros h h2,
    have h3:= h,
    rw h2 at h3,
    have h4:= cardinalsinhabited M (𝕊 x) h3, 
    cases h4 with z h5,
    have h5copy:= h5,
    rw successor_members M at h5, 
    cases h5 with u h6,
    cases h6 with c h7, 
    rcases h7 with ⟨ h8, h9, h10⟩, 
    rw h10 at *, 
    have h11:= h5copy,
    rw← h2 at h11,
    have h12:= finitecardinals1 M x (u ∪ (single c)) h h11, 
    have h13:= finitecardinals2 M u (u ∪ single c) x h h8 h11, 
    have h14: ¬ (u ∪ (single c) = u):=
      begin
        intro h15,
        rw full_extensionality at h15, 
        specialize h15 c,
        rw binary_union_axiom at h15,
        rw singleton1 M at h15, 
        simp at h15, 
        contradiction, 
      end,
    have h16:= subset_union2 M u (single c), 
    have h15:= finiteimpliesnotinfinite M (u ∪ (single c)) h12, 
    unfold infinite at h15,
    push_neg at h15, 
    have h17:= h15 u h16 h14, 
    rw similar_symmetric M at h13,
    contradiction, 
  end

lemma one_members: ∀(x:M), x ∈ one  ↔ ∃ a, x = single a :=
  assume x,
  begin
    rw one_definition, 
    rw successor_members,
    split,
    {
      intro h,
      cases h with z h2,
      cases h2 with a h3,
      cases h3 with h4 h5,
      cases h5 with h6 h7,
      rw zero_definition at h4,
      have h8: z = Λ:=
        begin
          rw singleton1 M at h4,
          exact h4,
        end,
      rw h8 at *,
      use a,
      rw empty_union_x at h7,
      exact h7,
    },
    {
      intro h,
      cases h with a h2,
      use Λ, use a,
      rw empty_union_x,
      rw zero_definition,
      rw singleton1 M,
      exact ⟨ refl Λ , emptyset_axiom a, h2⟩, 
    },
  end

lemma two_members: ∀ (x:M), x ∈ two ↔ ∃(a b:M), ¬ a = b ∧ x = pair a b :=
  assume x,
  begin
    rw two_definition, 
    rw successor_members,
    split,
    {
      intro h,
      cases h with a h2,
      cases h2 with c h3,
      rcases h3 with ⟨ h4,h5,h6⟩,
      rw one_members at h4,
      cases h4 with e h7,
      rw h7 at *,
      use e, use c,
      rw singleton1 at h5,
      split,
      {
        rw sym,
        exact h5, 
      },
      {
        rw full_extensionality,
        intro t,
        rw full_extensionality at h6,
        specialize h6 t,
        rw h6,
        rw binary_union_axiom,
        rw singleton1 M,
        rw singleton1 M,
        rw pairing_axiom,
      }
    },
    {
      intro h,
      cases h with a h2,
      cases h2 with b h3,
      cases h3 with h4 h5,
      use single a, use b,
      rw one_members,
      use a,
      rw singleton1 M,
      split,
      {
        rw sym,
        exact h4,
      },
      {
        rw full_extensionality,
        intro t,
        rw binary_union_axiom,
        rw singleton1 M,
        rw singleton1 M,
        rw full_extensionality at h5,
        specialize h5 t,
        rw pairing_axiom at h5,
        exact h5, 
      }
    }
  end

lemma lessthantwo: ∀ (m:M), m ∈ 𝔽 → ( m < two ↔ m = zero ∨ m = one):=
  assume m,
  begin
    intro h,
    split,
    {
      intro h2,
      have h3: ¬ zero = one:=
        begin
          intro h4,
          rw one_definition at h4,
          have h5:= xnotequalsuccessorx M zero (zeroF M),
          contradiction,
        end,
      have h4: {zero,one} ∈ two:=
        begin
          rw two_members M,
          use zero, use one,
          split,
          {
            exact h3,
          },
          {
            refl, 
          }
        end,
      have h2copy:= h2,
      rw lessthan_definition m two at h2copy,
      cases h2copy with h5 h6,
      have h7:= le2 M m two h (twoF M) ⟨ {zero,one}, h4⟩,
      rw h7 at h5,
      specialize h5 {zero,one},
      have h6:= h5 h4, 
      cases h6 with a h9,
      rcases h9 with ⟨ h10, h11, h12⟩, 
      have h13: ¬ a = {zero,one}:=
        begin
          intro h14, 
          rw← h14 at h4,
          have h15:a ∈ (m ∩ two):=
            begin
              rw intersection_axiom,
              exact ⟨ h10, h4⟩, 
            end,
          have h16:= cardinalsdisjoint M m two a h (twoF M) h15,
          contradiction,
        end,
      have h12copy := h12,
      rw full_extensionality at h12,
      have h14:= h12 zero,
      rw pairing_axiom at h14,
      simp at h14, 
      rw binary_union_axiom  at h14,
      rw minus_members at h14,
      rw pairing_axiom at h14,
      simp at h14, 
 
      rw full_extensionality at h12copy,
      have h15:= h12copy one,
      rw pairing_axiom at h15,
      simp at h15, 
      rw binary_union_axiom  at h15,
      rw minus_members at h15,
      rw pairing_axiom at h15,
      simp at h15, 
      cases h14 with h16 h17,
      {
        cases h15 with h18 h19,
        {
          have h20: a = {zero,one}:=
            begin
              rw full_extensionality,
              intro t,
              split,
              {
                intro h21,
                have h22:= member_subset M a {zero,one} t h11 h21,
                exact h22,
              },
              {
                rw pairing_axiom,
                intro h21,
                cases h21 with h22 h23,
                {
                  rw h22 at *,
                  exact h16,
                },
                {
                  rw h23 at *,
                  exact h18,
                }
              }
            end,
          contradiction,
        },
        {
          right,
          have h20: a = single zero:=
            begin
              rw full_extensionality,
              intro t,
              rw singleton1,
              split,
              {
                intro h20,
                have h21:= member_subset M a {zero,one} t h11 h20, 
                rw pairing_axiom at h21, 
                cases h21 with h22 h23,
                {
                  exact h22, 
                },
                {
                  rw h23 at *,
                  contradiction, 
                }
              },
              {
                intro h20,
                rw h20 at *,
                exact h16, 
              }
            end,
          have h21:  a ∈ one:=
            begin
              rw one_members, 
              use zero,
              exact h20,
            end,
          apply cardinalsdisjoint M m one a h (oneF M), 
          rw intersection_axiom,
          exact ⟨ h10, h21⟩, 
        }
      },
      {
        cases h15 with h18 h19,
        {
          right,
          have h21: a = single one:=
            begin
              rw full_extensionality, 
              intro t,
              rw singleton1,
              split,
              {
                intro h22,
                have h23:= member_subset M a {zero,one} t h11 h22, 
                rw pairing_axiom at h23, 
                cases h23 with h24 h25,
                {
                  rw h24 at *,
                  contradiction, 
                },
                {
                  exact h25, 
                }
              },
              {
                intro h20,
                rw h20 at *,
                exact h18, 
              }
            end,
          have h22: a ∈ one:=
            begin
              rw one_members, 
              use one, 
              exact h21, 
            end,
           apply cardinalsdisjoint M m one a h (oneF M), 
           rw intersection_axiom, 
           exact ⟨ h10, h22⟩, 
        },
        {
          left,
          rw zero_definition,
          have h20: a = Λ:=
            begin
              rw full_extensionality,
              intro t,
              split,
              {
                 intro h21,
                 have h22:= member_subset M a {zero,one} t h11 h21,
                 rw pairing_axiom at h22, 
                 cases h22 with h23 h24,
                 {
                   rw h23 at *,
                   contradiction, 
                 },
                 {
                   rw h24 at *,
                   contradiction,
                 }
              },
              {
                intro h20,
                have h21:= emptyset_axiom t,
                contradiction, 
              }
            end,
          rw h20 at *,
          have h21: (Λ:M) ∈ single Λ := 
            begin
              rw singleton1 M,
            end, 
          have h22: Λ ∈ (m ∩ zero):=
            begin
              rw intersection_axiom,
              split,
              {
                exact h10, 
              },
              {
                rw zero_definition,
                exact h21, 
              }
            end,
          have h23:= cardinalsdisjoint M m zero Λ h (zeroF M) h22, 
          rw h23 at *,
          rw zero_definition,  
        }
      }
    },
    {
      intro h2,
      cases h2 with h3 h4,
      {
        rw h3,
        exact zero_lessthan_two M, 
      },
      {
        rw h4,
        exact one_lessthan_two M, 
      }
    }
  end

lemma expdef: ∀ (m a:M), m ∈ 𝔽  → USC a ∈ m → exp M m = Nc M (SSC a):=
  assume m a,
  begin
    intros h1 h2,
    rw full_extensionality,
    intro x,
    rw Nc_members,
    rw exp_members,
    split,
    { 
      intro h3,
      cases h3 with b h4,
      cases h4 with h5 h6,
      rw h6 at *,
      have h7: similar M (USC a) (USC b):= finitecardinals2 M (USC a)(USC b) m h1 h2 h5, 
      rw← uscsimilar at h7, 
      have h8:= sscsimilar M a b h7, 
      rw similar_symmetric at h8,
      exact similar_transitive M x (SSC b) (SSC a) h6 h8, 
    },
    {
      intro h3,
      use a,
      exact ⟨ h2, h3⟩, 
    }
  end 

lemma NCexpdef: ∀ (m a:M), m ∈ NC M  → USC a ∈ m → exp M m = Nc M (SSC a):=
  assume m a,
  begin
    intros h1 h2,
    rw full_extensionality,
    intro x,
    rw Nc_members,
    rw exp_members,
    split,
    { 
      intro h3,
      cases h3 with b h4,
      cases h4 with h5 h6,
      rw h6 at *,
      have h7: similar M (USC a) (USC b):= cardinals2 M m (USC a)(USC b) h1 h2 h5, 
      rw← uscsimilar at h7, 
      have h8:= sscsimilar M a b h7, 
      rw similar_symmetric at h8,
      exact similar_transitive M x (SSC b) (SSC a) h6 h8, 
    },
    {
      intro h3,
      use a,
      exact ⟨ h2, h3⟩, 
    }
  end 

lemma finiteexp:  ∀ (m:M), m ∈ 𝔽 → (∃(y:M), y ∈ exp M m) → exp M m ∈ 𝔽:=
  assume m,
  begin
    intros h1 h2,
    cases h2 with y h3,
    rw exp_members at h3,
    cases h3 with a h4,
    cases h4 with h5 h6, 
    have h10: USC a ∈ FINITE M := finitecardinals1 M m (USC a) h1 h5, --line 641
    rw uscfinite at h10, 
    have h11: SSC a ∈ FINITE M:= finitepowerset M a h10, 
    have h12: SSC a ∈ exp M m:=
      begin
        rw exp_members M, 
        use a,
        exact ⟨ h5, similar_reflexive M (SSC a)⟩, 
      end,
    have h13:= finitecardinals3 M (SSC a) h11,
    have h14: exp M m = Nc M (SSC a):= expdef M m a h1 h5,
    have h15: Nc M (SSC a) ∈ 𝔽 := finitecardinals3 M (SSC a) h11, 
    rw h14,
    exact h13, 
  end

lemma NCexp:  ∀ (m:M), m ∈ NC M → (∃(y:M), y ∈ exp M m) → exp M m ∈ NC M:=
  assume m,
  begin
    intros h1 h2,
    cases h2 with y h3,
    rw exp_members at h3,
    cases h3 with a h4,
    cases h4 with h5 h6, 
    have h12: SSC a ∈ exp M m:=
      begin
        rw exp_members M, 
        use a,
        exact ⟨ h5, similar_reflexive M (SSC a)⟩, 
      end,
    have h14: exp M m = Nc M (SSC a):= NCexpdef M m a h1 h5,
    rw h14 at *,
    rw NC_members,
    use SSC a, 
  end

lemma exp_inhabited: ∀(m:M),  ((∃ a, (USC a ∈ m))  ↔ ∃ b, (b ∈ exp M m)):=
  assume m,
  begin
    split,
    {
      intro h2,
      cases h2 with a h3,
      use SSC a,
      rw exp_members M,
      use a,
      exact ⟨ h3, similar_reflexive M (SSC a)⟩,
    },
    {
      intro h2,
      cases h2 with b h3,
      rw exp_members at h3,
      cases h3 with a h4,
      cases h4 with h5 h6,
      use a,
      exact h5,
    }
  end

lemma similar_to_singleton: ∀(x b:M), similar M x (single b) → (∃(a:M), x = single a):=
  assume x b,
  begin
    intro h,
    unfold similar at h,
    cases h with f h2,
    unfold similarity at h2,
    cases h2 with h3 h4,
    unfold onto at h4,
    specialize h4 b,
    rw singleton1 M b at h4,
    have h5:= h4 (refl b),
    cases h5 with a h6,
    cases h6 with h7 h8,
    use a,
    rw full_extensionality,
    intro z,
    rw (singleton1 M),
    unfold oneone at h3,
    rcases h3 with ⟨ h9,h10,h11⟩, 
    specialize h10  a z b,
    split,
    {
      intro h11,
      unfold maps at h9,
      cases h9 with h12 h13,
      rcases h13 with ⟨ h14, h15, h16⟩,
      have h17:= h16 z h11,
      cases h17 with y h18,
      rw singleton1 M at h18,
      cases h18 with h19 h20,
      rw h19 at *,
      have h21:= h10 ⟨ h8, h20, h7⟩,
      symmetry,
      exact h21, 
    },
    {
      intro h12,
      rw h12 at *,
      exact h7,
    }
  end 

lemma any_singleton_similar: ∀ (a:M), similar M (single a) (single Λ ):=
  assume a,
  begin 
    set f:= single ‹ a, Λ › with h30,
    unfold similar,
    use f,
    unfold similarity,
    split,
    {
      unfold oneone,
      unfold maps,
      repeat {split},
      {
        rw Rel_definition, 
        intros z h3,
        rw h30 at h3,
        rw singleton1 M at h3,
        use a, use Λ, 
        exact h3,
      },
      {
        intros u y h6,
        rw singleton1 M,
        cases h6 with h7 h8,
        rw singleton1 M at h7,
        rw h7 at *,
        rw h30 at h8,
        rw singleton1 M at h8,
        rw ordered_pair_equality at h8,
        exact h8.right, 
      },
      {
        intros u y w h9,
        rcases h9 with ⟨ h10, h11, h12 ⟩, 
        rw h30 at h11,
        rw h30 at h12,
        rw singleton1 M at h11 h12,
        rw ordered_pair_equality at h11 h12,
        rw h12.right,
        rw h11.right, 
      },
      {
        intros u h6,
        use Λ, 
        rw h30,
        rw singleton1 M, 
        rw singleton1 M,
        rw ordered_pair_equality,
        rw singleton1 M at h6,
        exact ⟨ refl Λ, h6, refl Λ ⟩,
      },
      {
        intros x u y h8,
        rw h30 at *, 
        repeat { rw singleton1 M at h8}, 
        repeat { rw ordered_pair_equality at h8}, 
        rw h8.left.left,
        rw h8.right.left.left, 
      },
      {
        intros x y h,
        rw h30 at *,
        repeat {rw singleton1 M at h },
        rw ordered_pair_equality at h,
        rw singleton1 M,
        exact h.left.left, 
      }
    },
    {
      unfold onto,
      intros y h,
      rw singleton1 M at h,
      rw h at *,
      use a,
      rw h30,
      repeat {rw singleton1 M},
      exact ⟨ refl a, refl ‹ a, Λ › ⟩, 
    },
  end 
 
lemma exp_zero:  (exp M zero) = (one:M) :=
  begin
    rw one_definition, 
    rw full_extensionality,
    intro x,
    rw exp_members,
    rw successor_members,
    split,
    {
      intro h,
      cases h with a h2,
      cases h2 with h3 h4,
      rw zero_definition at h3,
      rw singleton1 M at h3,
      rw full_extensionality at h3,
      use Λ, 
      have h5: ∀ z, ¬ z ∈ a:=
        assume z,
        begin
          intro h6,
          specialize h3 (single z),
          rw usc_members at h3,
          rw h3 at h6,
          have h7:= emptyset_axiom (single z),
          contradiction, 
        end,
      have h6: a = Λ:=
        begin
          rw full_extensionality,
          intro u,
          specialize h5 u,
          have h7:= emptyset_axiom u,
          split,
          {
            intro h8,
            contradiction,
          },
          {
            intro h8,
            contradiction, 
          }
        end,
      have h7: SSC a = single Λ:=
        begin
          rw full_extensionality,
          intro u,
          rw ssc_members,
          rw singleton1 M, 
          rw h6 at *,
          split,
          {
            intro h6,
            cases h6 with h7 h8,
            rw subset_of_empty M u at h7,
            exact h7,
          },
          {
            intro h6,
            rw h6 at *,
            rw subset_of_empty M Λ,
            split,
            { 
              exact refl Λ, 
            },
            {
              intro y,
              intro h7,
              left,
              exact h7,
            }
          }
        end,
      rw h6 at *,
      rw ssc_empty M at h4,
      have h8:= similar_to_singleton M x Λ  h4,
      cases h8 with b h9,
      use b,
      rw lambda_cup M (single b),
      rw zero_definition,
      rw singleton1 M,
      exact ⟨ refl Λ, emptyset_axiom b, h9⟩, 
   },
   {
     intro h,
     cases h with z h1,
     cases h1 with a h2,
     rcases h2 with ⟨h3,h4,h5⟩,
     rw zero_definition at h3,
     rw singleton1 M at h3,
     rw h3 at *,
     rw empty_union_x at h5,
     use Λ, 
     rw usc_lambda,
     rw zero_definition,
     rw singleton1 M,
     rw ssc_empty,
     split,
     {
       exact (refl Λ ),
     },
     {  
       rw h5, 
       exact (any_singleton_similar M a),
     }
   },
  end



lemma usc_zero: USC(zero:M) = single (zero:M):=
  begin
    rw full_extensionality,
    intro x,
    rw usc,
    split,
    {
      intro h,
      cases h with a h2,
      rw zero_definition at h2,
      rw singleton1 M at h2,
      cases h2 with h3 h4,
      rw h3 at *,
      rw h4 at *,
      rw zero_definition,
      rw singleton1 M,
    },
    {
      intro h,
      use Λ ,
      rw singleton1 M at h,
      rw zero_definition at h,
      rw zero_definition,
      rw singleton1 M,
      exact ⟨ refl Λ, h ⟩,
    }
  end 

lemma exp_one: exp M (one:M) = (two:M)  :=
  begin
    have line666: USC zero ∈ one:=
      begin
        rw usc_zero,
        rw (one_members M (single zero)),
        use zero, 
      end,
    have line667: SSC(zero) ∈ exp M one:=
      begin
        rw exp_members,
        use zero,
        exact ⟨ line666, similar_reflexive M (SSC zero) ⟩, 
      end,
    have line668: SSC(zero:M) = { Λ, single Λ }:=
      begin 
        rw full_extensionality,
        intro x,
        rw ssc_members,
        split,
        {
          intro h,
          cases h with h2 h3,
          rw subset_definition at h2, 
          rw pairing_axiom, 
          specialize h3 Λ,
          rw zero_definition at h3,
          rw singleton1 M at h3,
          have h4:= h3 (refl Λ ),
          cases h4 with h5 h6,
          {
            right,
            rw full_extensionality,
            intro u,
            rw singleton1 M,
            split,
            {
              intro h6,
              have h7:= h2 u h6,
              rw zero_definition at h7,
              rw singleton1 M at h7,
              exact h7,
            },
            {
              intro h6,
              rw h6 at *,
              exact h5, 
            }
          },
          { 
            left,
            rw full_extensionality,
            intro u,
            specialize h2 u,
            rw zero_definition at h2,
            rw singleton1 M at h2,
            split,
            {
              intro h7,
              have h8:= h2 h7, 
              rw h8 at *, 
              contradiction,
            },
            {
              intro h7,
              have h8:= emptyset_axiom u h7,
              contradiction, 
            }
          }, 
        },
        {
          intro h,
          rw pairing_axiom at h,
          split,
          {
            rw subset_definition, 
            intro z,
            intro h3,
            rw zero_definition,
            rw singleton1 M,
            cases h with h4 h5,
            {
              rw h4 at *,
              have h5:= emptyset_axiom z h3,
              contradiction,
            },
            {
              rw h5 at *,
              rw singleton1 M at h3,
              exact h3,
            }
          },
          {
            intros y h2,
            rw zero_definition at h2,
            rw singleton1 M at h2,
            rw h2 at *,
            cases h with h3 h4,
            {
              rw h3 at *,
              right,
              exact (emptyset_axiom Λ), 
            },
            {
              rw h4,
              left,
              rw singleton1 M, 
            }
          }
        },
      end,
    have line669: SSC(zero) ∈ exp M one:=
      begin
        rw exp_members,
        use zero,
        exact ⟨ line666, similar_reflexive M (SSC zero) ⟩, 
      end, 
    have line669b: SSC(zero:M) ∈ two:=
      begin 
        rw two_definition,
        rw line668,
        rw successor_members,
        use zero, use zero,
        repeat {split}, 
        {
          exact  zeroinone M,  
        },
        {
          rw zero_definition,
          rw singleton1 M,
          intro h,
          rw full_extensionality at h,
          specialize h Λ ,
          rw singleton1 M at h,
          have h3:= emptyset_axiom Λ ,
          cases h with h4 h5,
          have h6:= h4 (refl Λ ),
          contradiction, 
        },
        { 
          rw full_extensionality,
          intro x,
          rw pairing_axiom,
          rw binary_union_axiom,
          rw singleton1 M,
          rw zero_definition,
          rw singleton1 M,
        }
      end,
    have line671: exp M one ∈ 𝔽 := finiteexp M one (oneF M) ⟨ SSC zero, line669 ⟩,
    have line671b: SSC zero ∈ (exp M one) ∩ two :=
      begin
        rw intersection_axiom, 
        exact ⟨line669, line669b⟩, 
      end, 
    have line672:= cardinalsdisjoint M (exp M one) two (SSC zero) line671 (twoF M) line671b,
    exact line672, 
  end





lemma usc_subset_ssc: ∀(a:M), a ∈ DECIDABLE M →  USC a ⊆ SSC a :=  --lemma 43
  assume a,
  begin
    intro h,
    rw subset_definition,
    intros z h2,
    rw usc at h2,
    cases h2 with x h3,
    cases h3 with h4 h5, 
    rw ssc_members,
    split,
    {
      rw subset_definition,
      intro u,
      intro h6,
      rw h5 at *,
      rw singleton1 M at h6,
      rw h6 at *,
      exact h4, 
    },
    {
      intro u,
      rw decidable_members at h,
      specialize h u x,
      rw h5,
      rw singleton1 M,
      intro h3,
      exact h ⟨ h3, h4⟩, 
    }
  end 
  
lemma usc_unitclass: ∀ (a:M),(( ∃(x:M), a = single x) ↔ ∃ u,( USC a = single u)):=
  assume a, 
  begin
    split,
    {
      intro h,
      cases h with x h2,
      use a,
      rw full_extensionality,
      intro u,
      rw usc,
      split,
      {
        intro h3,
        cases h3 with t h4,
        cases h4 with h5 h6,
        rw h2 at *,
        rw singleton1 M at h5, 
        rw h5 at *,
        rw h6 at *,
        rw singleton1 M,
      },
      {
        intro h3,
        rw singleton1 M at h3,
        rw h3 at *,
        use x,
        rw h2,
        rw singleton1 M,
        exact ⟨ refl x, refl (single x)⟩, 
      }
    },
    {
      intro h,
      cases h with u h2,
      rw full_extensionality at h2,
      have h2copy := h2,
      specialize h2 u,
      rw singleton1 M at h2, 
      cases h2 with h3 h4,
      have h5:= h4 (refl u), 
      rw usc at h5,
      cases h5 with t h6,
      cases h6 with h7 h8,
      use t,
      rw full_extensionality,
      intro x,
      split,
      {
        intro h9,
        rw singleton1 M,
        have h10: single x ∈ USC a:=
          begin
            rw usc,
            use x,
            exact ⟨ h9, refl (single x)⟩, 
          end,
        have h11:= h2copy (single x), 
        rw h11 at h10,
        rw singleton1 M at h10,
        have h12:    single x = single t := 
          begin 
            rw h10,
            rw← h8, 
          end,
        exact (single_oneone M x t h12),  
      },
      {
        rw singleton1 M,
        intro h9,
        rw h9 at *,
        exact h7, 
      }
    },
  end 

lemma unit_classes_similar_zero: ∀(a:M), (exists (x:M), a = single x) → similar M a zero:=
  assume a,
    begin
      unfold similar, 
      intro h,
      cases h with u h11,
      use single ‹ u, Λ ›,
      rw zero_definition,
      unfold similarity,
      unfold oneone,
      unfold onto,
      repeat{split},
      { 
        rw Rel_definition,
        intros z h3,
        rw singleton1 M at h3, 
        use u, use Λ ,
        exact h3, 
      },
      {
        intros x y h4,
        rw singleton1 M at *,
        rw ordered_pair_equality M at h4,
        exact h4.right.right,
      },
      {
        intros x y z h4,
        rw singleton1 M at h4,
        rw singleton1 M at h4,
        repeat {rw ordered_pair_equality M at h4}, 
        rcases h4 with ⟨ h5, h6, h7, h8⟩, 
        rw h6.right,
        rw h8,

      },
      {
        intros x h4,
        rw h11 at h4,
        rw singleton1 M at h4,
        rw h4 at *,
        use Λ, 
        repeat {rw singleton1},
        exact ⟨ refl Λ, refl ‹ u, Λ › ⟩,
      },
      {
        intros x v y h4,
        repeat {rw singleton1 M at h4},
        repeat {rw ordered_pair_equality M at h4},
        rcases h4 with ⟨ h5, h6, h7⟩, 
        rw h5.left,
        rw h6.left,  
      },
      { 
        intros x y h4,
        repeat {rw singleton1 M at h4}, 
        repeat {rw ordered_pair_equality M at h4},
        rw h11,
        rw singleton1,
        exact h4.left.left, 
      },
      {
        intros y h4,
        rw singleton1 M at h4,
        use u,
        rw h11,
        repeat { rw singleton1 M },
        rw h4, 
        exact ⟨ refl u, refl ‹ u, Λ › ⟩, 
      },               
    end

lemma xinSSCx: ∀ (x:M), x ∈ SSC x:=
  assume x,
    begin
      rw ssc_members M,
      split,
      {
        exact subset_reflexive M x,
      },
      {
        intro y,
        intro h,
        left,
        exact h,
      }
    end

lemma  mlessthanexpm: ∀ (m:M), ( m ∈ 𝔽 → (∃ u, u ∈ exp M m) → m < exp M m) :=
  -- Specker Lemma 5.6 
  assume m,
  begin
    intros h2 h3,
    have line674: 𝔽 ∈  DECIDABLE M :=  FregeNdecidable M, 
    have line674copy:= line674,
    have line675: m = zero ∨ m = one ∨ (¬ m = zero ∧ ¬ m = one):=
      begin       
        rw decidable_members at line674,
        have h4:= line674 m zero  ⟨ h2 , (zeroF M)⟩ , 
        have h20:= line674 m one ⟨ h2, (oneF M)⟩, 
        cases h4 with h5 h6,
        {
          left,  exact h5, 
        },
        {  
          right,
          cases h20 with h7 h8,
          {
            left,
            exact h7, 
          },
          {
            right,
            exact ⟨ h6, h8⟩, 
          }
        }
      end,
    cases line675 with case1 cases2and3,
    {   
      have line676: exp M zero = one:= exp_zero M, 
      have line677: (zero:M) < one:= zerolessthanone M, 
      rw case1,
      rw line676,
      exact line677, 
    },
    {
      cases cases2and3 with case2 case3,
      {
        have line679: exp M one = two:= exp_one M,
        have line680: (one:M) < two := one_lessthan_two M, 
        rw case2,
        rw line679,
        exact line680, 
      },
      {
        have line684: ∃(a:M), USC a ∈ m:= (exp_inhabited M m).mpr h3, 
        cases line684 with a line684a,
        have line684b: USC a ∈ FINITE M:= finitecardinals1 M m (USC a) h2 line684a,
        have line684c: a ∈ FINITE M:= (uscfinite M a).mp  line684b,
        have line684d: SSC a ∈ FINITE M:= finitepowerset M a line684c,
        have line685: USC a ⊆ SSC a:= usc_subset_ssc M a (finitedecidable M a line684c),
        have line688: USC a ∈ SSC (SSC a):= 
          begin
            rw ssc_members,
            split,
            {
              exact line685, 
            },
            {
              intros y h4,
              have h5:= finiteseparable M (SSC a) (USC a) line684d line684b line685,
              rw full_extensionality at h5,
              specialize h5 y,
              rw h5 at h4,
              rw binary_union_axiom at h4,
              cases h4 with h6 h7,
              {
                rw (minus_members M) at h6,
                cases h6 with h7 h8,
                right,
                exact h8, 
              },
              {
                left,
                exact h7, 
              }
            }
          end,
        have line696: (m:M) ≤ exp M m:=
          begin
            have h10:= le_definition  m (exp M m),
            rw h10,
            set u:= USC a with h11,
            set v := SSC a with h12,
            use u, use v,
            repeat {split} ,
            { 
              exact line684a,
            },
            {
              rw exp_members M m v,
              use a,
              split,
              {
                exact line684a,
              },
              {
                rw h12,
                exact similar_reflexive M (SSC a), 
              }
            },
            {
              exact line685, 
            },
            {
              rw ssc_members M at line688,
              cases line688 with h20 h21,
              rw full_extensionality,
              intro x,
              specialize h21 x,
              rw binary_union_axiom,
              rw minus_members M, 
              split,
              {
                intro h22,
                have h23:= h21 h22, 
                cases h23 with h24 h25,
                {
                  left,
                  exact h24,
                },
                {
                  right,
                  exact ⟨ h22, h25⟩, 
                }
              },
              {
                intro h22,
                cases h22 with h23 h24,
                {
                  exact member_subset M u v x h20 h23,
                },
                {
                  exact h24.left, 
                }
              }
            }
          end, 
        have line700: ¬ (m:M) = exp M m:=
          begin
            intro h4,  -- suppose m = exp M m
            have line698: SSC(a) ∈ exp M m:=
              begin
                rw exp_members,
                use a,
                exact ⟨ line684a, similar_reflexive M (SSC a)⟩, 
              end,
            have line695d:a ∈ DECIDABLE M:= finitedecidable M a line684c,
            have line701: ¬ (USC a = SSC a):=
              begin
                intro h5,
                rw full_extensionality at h5,
                specialize h5 a,
                have line703: a ∈ SSC a:= xinSSCx M a,
                have line704:¬ a ∈ USC a:=
                  begin
                    intro h6,
                    rw usc at h6,
                    cases h6 with x h7,
                    cases h7 with h8 h9,
                    have h10: ∃ x, a = single x :=
                      begin
                        use x, 
                        exact h9, 
                      end,
                    rw (usc_unitclass M a) at h10,
                    have line705: exists u, USC a = single u:= h10,
                    have line706:similar M (USC a) zero := unit_classes_similar_zero M (USC a) line705, 
                    rw similar_symmetric M at line706,
                    have line706b: USC a ∈ one:=  finitecardinals0 M one zero (USC a) (oneF M) (zeroinone M)  line706,
                    have line707: USC a ∈ m ∩ one:=
                      begin
                        rw intersection_axiom, 
                        exact ⟨ line684a, line706b⟩, 
                      end,
                    have line707b: m = one:= cardinalsdisjoint M m one (USC a) h2 (oneF M) line707,
                    exact case3.right line707b, 
                  end,
                rw← h5 at line703,
                contradiction,  
              end,
            have line708:  USC a ⊂ SSC a:=
              begin
                rw proper_subset_definition,
                exact ⟨ line685, line701⟩, 
              end,
            rw← h4 at line698, 
            have line709b: similar M (USC a) (SSC a) := 
                 finitecardinals2 M (USC a)(SSC a) m h2 line684a line698, 
            rw (similar_symmetric M) at line709b, 
            have line709d: ¬ (SSC a ∈ FINITE M):=
              begin
                intro h5,
                have h6:= Theorem1 M (SSC a) h5 (USC a) line685 line709b, 
                rw sym at h6,
                contradiction, 
              end, 
            have line709e: SSC a ∈ FINITE M:= finitepowerset M a line684c, 
            contradiction, 
          end,
        rw lessthan_definition, 
        exact ⟨ line696, line700⟩, 
      }
    }
  end 


lemma  mplusone_le_expm: ∀ (m:M),  m ∈ 𝔽 → (∃ (u:M), u ∈ exp M m) →((𝕊 m) ≤  exp M m)  :=
  assume m,
  begin
    intros h2 h3,
    have h:= mlessthanexpm M m h2 h3,
    have h4:= finiteexp M m h2 h3, 
    exact  noinsertions M m (exp M m) h2 h4 h,
  end

lemma expuscssc: ∀(m a:M), m ∈ 𝔽 → USC a ∈ m → SSC a ∈ exp M m:=
  assume m a,
  begin
    intros h1 h2,
    rw exp_members,
    use a, 
    split,
    {
      exact h2,
    },
    {
      exact similar_reflexive M (SSC a), 
    }
  end 


lemma exporder: ∀(m n:M), m∈ 𝔽 → n ∈ 𝔽 → m ≤ n → ( (∃ u, u ∈ exp M n) → ((∃ u, u ∈ exp M m) ∧ exp M m ≤ exp M n)):=
  assume m n,
  begin
    intros h1 h2 h3 h4, 
    have h4copy := h4, 
    rw←  exp_inhabited M n at h4,
    rw←  exp_inhabited M m, 
    cases h4 with b h5,
    have h6: ∃ u, u ∈ n:= cardinalsinhabited M n h2,
    have h7:= le2  M m n h1 h2 h6, 
    rw h7 at h3, 
    specialize h3 (USC b),
    have h8:= h3 h5,
    cases h8 with x line714,
    rcases line714 with ⟨  h20, h21, h22⟩, 
    set A:= union x with h9,
    have line789: x = USC A:=
      begin
        rw full_extensionality,
        intro t,
        rw usc M, 
        split,
        {
          intro h10,
          simp_rw h9,
          rw subset_definition at h21,
          have h23:= h21 t h10, 
          rw usc M at h23,
          cases h23 with c h24,
          use c,
          cases h24 with h25 h26,
          rw union_axiom, 
          split,
          { 
            use t,
            split,
            { 
              exact h10,
            },
            { 
              rw h26,
              rw singleton1 M,
            }
          },
          {
            exact h26,
          }
        },
        {
          intro h30,
          cases h30 with c h31,
          cases h31 with h32 h33,
          rw h33,
          rw h9 at h32,
          rw union_axiom at h32,
          cases h32 with z h33,
          cases h33 with h34 h35,
          have h36:= member_subset M x (USC b) z h21 h34,
          rw usc at h36,
          cases h36 with p h37,
          cases h37 with h38 h39,
          rw h39 at h35,
          rw singleton1 M at h35,
          rw← h35 at *,
          rw h39 at h34,
          exact h34, 
        }
      end,
    rw line789 at h20, 
    have h23:= exp_inhabited M m,
    have h24:∃ (A:M), USC A ∈ m:= ⟨ A , h20⟩,
    have bFinite: b ∈ FINITE M:=
      begin
        have h100:=  finitecardinals1 M n  (USC b) h2 h5,
        rw uscfinite M at h100, 
        exact h100,
      end, 
  
    have xFinite: USC A ∈ FINITE M:= finitecardinals1 M m (USC A) h1 h20, 
      have h40: ∀(u:M), u ∈ USC A → u ∈ FINITE M:=
        begin 
          intros u h41,
          rw usc at h41,
          cases h41 with t h42,
          cases h42 with h43 h44,
          rw h44, 
          exact (singleton_finite M t), 
        end, 
     have disjointMembers: ∀ (p q:M), p ∈ USC A → q ∈ USC A → ¬ p = q → (p ∩ q = Λ ) := 
      begin 
        intros p q h51 h52 h53, 
        rw (usc  M) at h51 h52,
        cases h51 with t h53,
        cases h52 with r h54,
        cases h53 with h55 h56,
        cases h54 with h57 h58,
        rw full_extensionality,
        intro w,
        split,
        {
          intro h60,
          rw intersection_axiom at h60,
          cases h60 with h60 h61,
          rw h56 at h60,
          rw h58 at h61,
          rw singleton1 M at h60 h61,
          rw← h60 at *,
          rw← h61 at *,
          rw h56 at h53,
          rw h58 at h53,
          contradiction, 
        },
        {
          intro h60,
          have h61:= emptyset_axiom w h60, 
          contradiction, 
        }
      end,
    have aFinite: A ∈ FINITE M:=
      begin
        have h50:= finiteunion M (USC A) xFinite h40 disjointMembers,
        rw← line789 at h50,
        rw← h9 at h50,
        exact h50, 
      end,
    split,
    { 
      exact h24,
    },
    {
      rw le_definition,
      use (SSC A), use (SSC b),
      rw line789 at h21,
      have h30: x ∈ SSC(USC b):=
        begin
          rw ssc_members,
          rw line789,
          split,
          {
            exact h21,
          },
          {
            intro y,
            intro h22,
            rw usc at h22,
            cases h22 with t h23,
            cases h23 with h24 h25,
            rw h25 at *,
            rw←  usc_up_down,
            rw full_extensionality at h22, 
            specialize h22 (single t),
            rw binary_union_axiom at h22,
            rw minus_members M at h22,
            rw line789 at h22,
            repeat {rw← usc_up_down at h22},
            have h26:= h22.mp h24, 
            cases h26 with h27 h28,
            {
              left,
              exact h27,
            },
            {
              right,
              exact h28.right, 
            }
          }
        end, 
      repeat {split},
      {
        exact (expuscssc M m A h1 h20), 
      },
      {
        exact (expuscssc M n b h2 h5),
      },
      { 
        rw line789 at h30,
        rw← ssc_subset1 at h30,
        rw ssc_subset2 at h30,
        exact h30,
      },
      { 
        rw line789 at h30, 
        rw← ssc_subset1 at h30, 
        rw ssc_subset2 at h30, 
        have h36:= ssc_subset3 M A b aFinite bFinite,
        have h37: A ∈ SSC A:=  xinSSCx M A, 
        have h38: A ∈ SSC b:= member_subset M (SSC A)( SSC b) A h30 h37,
        have h39:= h36 h38,
        rw (ssc_definition (SSC b)) at h39,
        cases h39 with h40 h41,
        exact h41,
      },
    },
  end

lemma similarity_restriction: ∀ (A B b f:M), similarity M f B b → A ⊆ B → similarity M f A (image M f A):=
  -- unfortunately a duplicate of similarity_subset 
  begin
    intros A B b f h3 h4,
    unfold similarity,
    unfold similarity at h3,
    cases h3 with h5 h6,
    unfold oneone at h5,
    rcases h5 with ⟨ h7, h8, h9⟩,
    unfold maps at h7,
    rcases h7 with ⟨ h10, h11, h12⟩,
    cases h12 with h14 h15,
    split,
    {
      unfold oneone,
      split,
      {
        unfold maps,
        split,
        {
          exact h10,
        },
        {
          split,
          {
            intros x y h13,
            rw image_members,
            use x,
            exact h13,
            exact h10,
          },
          {
            split,
            {
              intros x y z h16,
              apply h14 x y z,
              cases h16 with h17 h18 h19,
              split,
              {
                exact member_subset M A B x h4 h17,
              },
              {
                exact h18,
              }
            },
            {
              intros x hx,
              have h19:= member_subset M A B x h4 hx,
              have h20:= h15 x h19,
              cases h20 with y h21,
              use y,
              split,
              {
                rw image_members,
                use x,
                exact ⟨ hx, h21.2⟩,
                exact h10,
              },
              {
                exact h21.2,
              }
            }
          }
        }
      },
      {
        split,
        {
          intros x u y h30,
          rcases h30 with⟨ h31, h32, h33⟩,
          have h34:= member_subset M A B x h4 h33,
          exact h8 x u y ⟨ h31, h32, h34⟩,
        },
        {
          intros x y h35,
          cases h35 with h36 h37,
          rw image_members at h37,
          cases h37 with z h38,
          cases h38 with h39 h40,
          have h34:= member_subset M A B z h4 h39,
          have h45:= h11 z y ⟨ h34, h40⟩,
          have h46:= h9 x y ⟨ h36, h45⟩,
          have h41:= h8 x z y ⟨ h36, h40, h46⟩, 
          rw← h41 at *,
          exact h39,
          exact h10,
        }
      }
    },
    {
      unfold onto,
      intros y h50,
      rw image_members at h50,
      exact h50,
      exact h10,
    }
  end

lemma le2NC: ∀ (κ μ:M),κ ∈ NC M → μ ∈ NC M → κ ⪯ μ → b ∈ μ → ∃(a:M), a ∈ κ ∧ a ⊆ b:=
  begin
    intros κ μ hkappa hmu hle hb,
    rw ledot_definition at hle,
    cases hle with A h3,
    cases h3 with B h4,
    rcases h4 with ⟨ h5, h6, h7⟩,
    have h9:= cardinals2 M μ B b hmu h6 hb, 
    have h9copy:= h9,
    unfold similar at h9copy,
    cases h9 with f h10,
    set a:= image M f A with adef,
    use a,
    have h11:= similarity_restriction M A B b f h10 h7,
    rw←adef at h11,
    have h12: similar M A a:=
      begin
        unfold similar,
        use f,
        exact h11,
      end, 
    have h13:= cardinals0 M κ A a hkappa h5 h12,
    split,
    {
      exact h13,
    },
    {
      have h95:= h11,
      unfold similarity at h95,
      cases h95 with h96 h970,
      unfold oneone at h96,
      cases h96 with hmaps h97,
      unfold maps at hmaps,
      rcases hmaps with ⟨h120, h121,h122,h123⟩,
       have h90: ∀(y:M), y ∈ b ↔ ∃(x:M), x ∈ B ∧ ‹x,y› ∈ f:=
        begin
          intros y,
          split,
          {
            intros hy,
            unfold similarity at h10,
            cases h10 with h140 h141,
            unfold onto at h141,
            exact h141 y hy,
          },
          {
            intros h143,
            cases h143 with x h144,
            cases h144 with h145 h146,
            unfold similarity at h10,
            cases h10 with h147 h148,
            unfold oneone at h147,
            cases h147 with h148 h149,
            unfold maps at h148,
            have h150:= h148.2.1,
            apply h150 x y,
            exact ⟨ h145, h146⟩,
          }
        end,
      have h190: ∀(y:M), y ∈ a ↔ ∃(x:M), x ∈ A ∧ ‹x,y› ∈ f:=
        begin
          intros y,
          unfold similarity at h11,
          cases h11 with h200 h201,
          split,
          {
            unfold onto at h201,
            exact h201 y,
          },
          {
            unfold oneone at h200,
            cases h200 with h202 h203,
            unfold maps at h202,
            rcases h202 with ⟨ h205, h206, h207, h208⟩,
            intros h210,
            cases h210 with x h211,
            exact h206 x y h211,
          }
        end,
      rw subset_definition,
      intros y hy,
      rw h90 y,
      rw h190 y at hy,
      cases hy with x h200,
      use x,
      cases h200 with h201 h202,
      exact ⟨ member_subset M A B x h7 h201, h202 ⟩,
    }
  end

lemma unionusc: ∀ (x:M), x = union (USC x):=
  begin
    intros x,
    rw full_extensionality,
    intros t,
    rw union_axiom,
    split,
    {
      intros ht,
      use single t,
      rw usc_members,
      rw singleton1,
      simp,
      exact ht,
    },
    {
      intros h,
      cases h with z h2,
      cases h2 with h3 h4,
      have h5:= usc M x z,
      rw h5 at h3,
      cases h3 with a h6,
      cases h6 with h7 h8,
      rw h8 at *,
      rw singleton1 at h4,
      rw h4 at *,
      exact h7,
    }
  end

lemma uscunion: ∀(a x:M), x ⊆ USC a → USC (union x) = x:=
  begin
    intros a x h3,
    rw full_extensionality,
    intros t,
    split,
    {
      intros h4,
      rw usc at h4,
      cases h4 with p h5,
      cases h5 with h6 h7,
      rw h7 at *,
      rw union_axiom at h6,
      cases h6 with z h7,
      cases h7 with h8 h9,
      have h10:=member_subset M x (USC a) z h3 h8,
      rw usc at h10,
      cases h10 with s h11,
      cases h11 with h12 h13,
      rw h13 at *,
      rw singleton1 at h9,
      rw h9 at *,
      rw← h13 at *,
      rw← h9 at *,
      exact h8,
    },
    {
      intros h20,
      have h21:= member_subset M x (USC a) t h3 h20,
      rw usc at h21,
      cases h21 with p h22,
      cases h22 with h23 h24,
      rw h24 at *,
      rw usc,
      use p,
      simp,
      have h25:p ∈ t:=
        begin
          rw h24,
          rw singleton1,
        end,
      rw union_axiom,
      have h26: p ∈ union x:=
        begin
          rw union_axiom,
          use t,
          rw h24 at *,
          exact ⟨ h20, h25⟩,
        end, 
      use t,
      split,
      {
        rw h24,
        exact h20,
      },
      {
        exact h25,
      }
    }
  end 


lemma threeF: (three:M) ∈ 𝔽 :=
  begin
    rw three_definition,
    have h3:= successorF M two (twoF M), 
    apply h3,
    have h4:= (twoF M), 
    have h5:= cardinalsinhabited M two (twoF M),
    have h0: (Λ:M) ∈ zero:=
      begin 
        rw zero_definition,
        rw singleton1,
      end, 
    have h1: single Λ ∈ one:=
      begin
        rw one_definition, 
        rw successor_members M,
        use Λ, use Λ,
        rw empty_union_x M (single Λ ),
        repeat{split},
        {
          exact h0,
        },
        {
          exact emptyset_axiom Λ,
        }
      end,
    have h2: {Λ, (single Λ )} ∈ two:=
      begin
        rw two_members M,
        use Λ, use (single Λ ),
        split,
        {
          rw full_extensionality,
          intro h8,
          specialize h8 Λ ,
          rw singleton1 at h8,
          simp at h8,
          have h9:= emptyset_axiom Λ ,
          contradiction,
        },
        {
          refl, 
        }
      end, 
    use { Λ, (single Λ )} ∪ (single (single (single Λ ))),
    rw successor_members,
    use {Λ,single Λ}, use (single (single Λ )),
    repeat{split},
    { 
      exact h2,
    },
    {
      rw pairing_axiom,
      intro h8,
      cases h8 with h9 h10,
      {
        rw full_extensionality M at h9,
        specialize h9 (single Λ ),
        rw singleton1 M at h9,
        simp at h9,
        have h11:= emptyset_axiom (single Λ ),
        contradiction, 
      },
      {
        rw full_extensionality at h10,
        specialize h10 (single Λ ),
        rw singleton1 M at h10,
        simp at h10,
        rw singleton1 M at h10,
        rw full_extensionality at h10,
        specialize h10 Λ ,
        rw singleton1 M at h10,
        simp at h10,
        have h11:= emptyset_axiom Λ,
        contradiction,
      }
    }
  end   

lemma three_members: ∀ (u:M), u ∈ three ↔ ∃ (a b c:M),
¬ (a = b) ∧ ¬ (a=c) ∧ ¬ (b=c) ∧ ∀(z:M), z ∈ u ↔ z = a ∨ z = b ∨ z = c:=
  assume u,
  begin 
    split,
    {
      intro h,
      rw three_definition at h,
      rw successor_members at h,
      cases h with v h2,
      cases h2 with c h3,
      rcases h3 with ⟨ h4, h5, h6⟩,
      rw two_members at h4,
      cases h4 with a h7,
      cases h7 with b h8,
      cases h8 with h9 h10,
      use a, use b, use c,
      split,
      {
        exact h9,
      },
      {
        rw h10 at *,
        rw pairing_axiom at h5,
        push_neg at h5,
        cases h5 with h11 h12,
        split,
        {
          rw sym,
          exact h11, 
        },
        {
          split,
          {
            rw sym,
            exact h12, 
          },
          {
            intro z,
            rw full_extensionality at h6,
            specialize h6 z,
            rw binary_union_axiom at h6,
            rw pairing_axiom at h6,
            rw singleton1 M at h6,
            rw h6, 
            rw or_assoc,
          }
        }
      }
    },
    {
      intro h,
      cases h with a h2,
      cases h2 with b h3,
      cases h3 with c h4,
      rcases h4 with ⟨ h5, h6, h7, h8⟩,
      rw three_definition,
      rw successor_members,
      use {a,b}, use c,
      split,
      {
        rw two_members,
        use a, use b,
        simp,
        exact h5,
      },
      {
        split,
        {
          rw pairing_axiom,
          push_neg,
          rw sym at h6,
          rw sym at h7,
          exact ⟨ h6, h7⟩, 
        },
        {
          rw full_extensionality,
          intro t,
          specialize h8 t,
          rw [binary_union_axiom, pairing_axiom, singleton1 M],
          rw h8,
          rw or_assoc,
        }
      }
    }
  end

lemma two_lessthan_three: (two:M) < (three:M):=
  begin
    have h2:= cardinalsinhabited M two (twoF M),
    have h3:= cardinalsinhabited M three (threeF M),
    rw two_definition,
    rw three_definition,
    rw two_definition at h2,
    rw three_definition at h3,
    rw← strictordersuccessor M one two (oneF M) (twoF M) h2 h3,
    exact one_lessthan_two M,
  end

lemma fourF: (four:M) ∈ 𝔽 :=
  begin
    rw four_definition, 
    have h:= threeF M,
    have h2: ∃ (u:M), u ∈ 𝕊 three:=
      begin
        use ({zero,one} ∪ (single two)) ∪ (single  three),
        rw successor_members,
        use ({zero,one} ∪ (single two)),
        use three,
        split,
        {
          rw three_members,
          use zero, use one, use two,
          repeat {split},
          {
            have h3:=zero_lessthan_one M,
            rw lessthan_definition at h3,
            exact h3.right,
          },
          {
            have h3:=zero_lessthan_two M,
            rw lessthan_definition at h3,
            exact h3.right,
          },
          {
            have h3:= one_lessthan_two M,
            rw lessthan_definition at h3,
            exact h3.right,
          },
          {
            intro t,
            rw binary_union_axiom,
            rw pairing_axiom,
            rw singleton1 M, 
            rw or_assoc, 
          }
        },
        {
          split,
          {
            rw binary_union_axiom,
            rw pairing_axiom,
            rw singleton1, 
            intro h2,
            cases h2 with h3 h4,
            {
              cases h3 with h5 h6,
              {
                rw three_definition at h5,
                have h6:=successor_omits_zero M two,
                contradiction,
              },
              {
                have h7:= cardinalsinhabited M three (threeF M),
                have h8:= cardinalsinhabited M two (twoF M),
                rw three_definition at h7 h6,
                rw two_definition at h8,
                have h10:= cardinalsinhabited M one (oneF M),
                rw one_definition at h10 h6, 
                have h9:= successoroneone M two zero (twoF M)(zeroF M) h7 h10,
                rw← h9 at h6,
                have h11:= zero_lessthan_two M,
                rw lessthan_definition at h11,
                cases h11 with h12 h13,
                rw sym at h6,
                contradiction,
              }
            },
            {
              have h3:= two_lessthan_three M,
              rw lessthan_definition at h3,
              cases h3 with h6 h5,
              rw sym at h4,
              contradiction,
            }
          },
          { 
            refl, 
          }
        }
      end,
    have h20:= successorF M three h h2,
    exact h20,   
  end

lemma three_lessthan_four: (three:M) < four:=
  begin
    have h:= cardinalsinhabited M four (fourF M),
    rw four_definition at h, 
    have h2:= successorF M three (threeF M) h,
    have h3:= lessthansuccessor M three (threeF M) h,
    rw four_definition,
    exact h3, 
  end

lemma two_lessthan_four: (two:M) < four:=
  begin  
    have h:= three_lessthan_four M,
    have h2:= two_lessthan_three M,
    have h3:= lessthan_transitive M two three four (twoF M) (threeF M) (fourF M) h2 h,
    exact h3, 
  end

lemma one_lessthan_three: (one:M) < three:=
  begin
    have h:= one_lessthan_two M,
    have h2:= two_lessthan_three M,
     have h3:= lessthan_transitive M one two three (oneF M) (twoF M) (threeF M) h h2,
    exact h3, 
  end

lemma one_lessthan_four: (one:M) < four:=
  begin  
    have h:= three_lessthan_four M,
    have h2:= one_lessthan_three M,
    have h3:= lessthan_transitive M one three four (oneF M) (threeF M) (fourF M) h2 h,
    exact h3, 
  end

lemma exp_members2: ∀ (m x:M), m ∈ 𝔽 → USC x ∈ m → SSC x ∈ exp M m:=
  assume m x,
  begin
    intros h h2,
    rw exp_members, 
    use x,
    exact ⟨ h2, similar_reflexive M  (SSC x) ⟩, 
  end

lemma x_in_Ncx: ∀ (x:M), x ∈ Nc M x:=
  assume x,
  begin
    have h2:similar M x x:= similar_reflexive M x,
    rw←  (Nc_members M x x) at h2,
    exact h2,
  end



#axioms_all  --This file is clean. 

  
    
