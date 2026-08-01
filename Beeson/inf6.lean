 -- Section 6 of the paper,  USC, SSC, and similarity 

import inf5    
import IntuitionisticLogic 

variables (M:Type) [Model M] (a b x y z u v w X R W κ μ ℓ : M)
-- using ℓ where the source text has λ because you can't use λ for a variable.

open Model 


lemma subset_usc: ∀ (a y:M), y ∈ SSC (USC a) → 
∃ z, z ∈ SSC a ∧ y = USC z:=   --line 625 
  assume a y,
  begin
    intro h,
    rw ssc_members M at h, 
    cases h with h1 h2,
    have h1copy:= h1, 
    rw subset_definition at h1,
    use (W39 M y),
    split,
    {
      rw ssc_members,
      split,
      {
        rw subset_definition,
        intros z h3,
        rw W39_members at h3,
        specialize h1 (single z),
        have h4:= h1 h3,
        rw usc at h4,
        cases h4 with b h5,
        cases h5 with h6 h7,
        have h8:= single_oneone M z b h7,
        rw h8 at *,
        exact h6, 
      },
      {
        intros u h3,
        rw W39_members,
        specialize h2 (single u),
        specialize h1 u,
        have h4: (single u) ∈ USC a:=
          begin
            rw usc,
            use u,
            exact ⟨ h3, refl (single u)⟩,
          end,
        exact (h2 h4),
      }
    },
    {
      rw full_extensionality,
      intro x,
      rw usc,
      specialize h1 x,
      split,
      {
        intro h4,
        have h5:= h1 h4,
        rw usc at h5, 
        cases h5 with b h6,
        use b,
        rw W39_members,
        cases h6 with h7 h8,
        rw h8 at *,
        exact ⟨ h4, refl (single b)⟩, 
      },
      {
        intro h3,
        cases h3 with b h4,
        cases h4 with h5 h6,
        rw W39_members at h5,
        rw h6 at *,
        exact h5, 
      }
    }   
  end 

lemma usc_oneone: ∀ (a b:M), USC a = USC b → a = b:=
  assume a b,
  begin
    intro h,
    rw full_extensionality at h,
    rw full_extensionality,
    intro x,
    specialize h (single x),
    rw usc at h,
    cases h with h2 h3,
    split,
    {
      intro h4,
      specialize h2 ⟨ x, h4, (refl (single x))⟩, 
      have h5:= h3 h2, 
      cases h5 with w h6, 
      cases h6 with h7 h8,
      have h9:= single_oneone M x w h8,
      rw h9 at *,
      rw usc at h2,
      cases h2 with u h10,
      cases h10 with h11 h12,
      have h13:= single_oneone M w u h12, 
      rw h13 at *, 
      exact h11, 
    },
    {
      intro h4,
      have h5: single x ∈ USC b:=
        begin
          rw usc,
          use x,
          exact ⟨ h4, refl (single x)⟩, 
        end,
      have h6:= h3 h5, 
      cases h6 with u h7,
      cases h7 with h8 h9,
      have h10:= single_oneone M x u h9,
      rw h10 at *,
      exact h8, 
    }
  end

lemma usc_solution: ∀(y z:M), y = USC z → z = union y:=
  assume y z,
  begin
    intro h,
    have hcopy:= h, 
    rw full_extensionality at h,
    rw full_extensionality,
    intro x,
    specialize h (single x),
    rw union_axiom, 
    split,
    {
      intro h2,
      rw usc at h,
      cases h with h3 h4,
      have h5:= h4 ⟨ x,h2, (refl (single x)) ⟩, 
      use (single x),
      rw singleton1 M,
      exact ⟨ h5, refl x⟩,
    },
    {
      intro h2,
      cases h2 with w h3,
      cases h3 with h4 h5,
      cases h with h6 h7, 
      rw full_extensionality at hcopy,
      specialize hcopy w,
      rw hcopy at h4,
      rw usc at h4,
      cases h4 with a h8,
      cases h8 with h9 h10,
      rw h10 at *,
      rw singleton1 at h5,
      rw h5 at *,
      exact h9, 
    }
  end 

lemma sscusc: ∀ (a:M), Nc M (SSC (USC  a)) = Nc M (USC (SSC a)):=
-- Specker 2.6, line 616 of the paper
  assume a,
  begin
    have h1:= W38_members M,
    cases h1 with h2 h3,
    have h4: maps M (W38 M) (USC (SSC a)) (SSC (USC a)) :=
      begin
        unfold maps, 
        repeat {split}, 
        {
          exact h2,
        },
        {
          intros x y,
          specialize h3 x y,
          intro h4,
          rw h3 at h4,
          cases h4 with h5 h6,
          cases h6 with z h7,
          cases h7 with h8 h9,
          rw ssc_definition,
          split,
          {
            rw subset_definition,
            intro u,
            rw full_extensionality at h9,
            specialize h9 u,
            intro h10,
            rw h9 at h10,
            rw h8 at h5,
            rw usc at h5,
            cases h5 with v h11,
            cases h11 with h12 h13,
            rw usc, 
            rw usc at h10,
            cases h10 with b h14,
            use b,
            rw ssc_members at h12,
            cases h12 with h15 h16,
            have h17:= single_oneone M  z v h13,
            rw h17 at *,
            cases h14 with h18 h19,
            exact ⟨ member_subset M v a b h15 h18, h19 ⟩, 
          },
          {
            rw full_extensionality,
            intro u,
            rw usc,
            split,
            {
              intro h10,
              cases h10 with b h11,
              cases h11 with h12 h13,
              rw binary_union_axiom,
              rw usc at h5,
              cases h5 with v h14,
              cases h14 with h15 h16,
              have h17: single z = single v:=  
                begin 
                  rw h16 at *, 
                  rw sym,
                  exact h8, 
                end, 
              have h18:= single_oneone M z v h17,
              rw h18 at *,
              rw ssc_members at h15,
              cases h15 with h19 h20,
              specialize h20 b,
              have h21:= h20 h12,
              cases h21 with h22 h23,
              {
                rw h13,
                left,
                rw h9,
                rw usc,
                use b,
                exact ⟨ h22, refl (single b) ⟩,
              },
              {
                right,
                rw minus_members M,
                rw usc, 
                split,
                {  
                   use b,
                   exact ⟨ h12, h13⟩, 
                },
                {
                  intro h24,
                  rw h13 at h24,
                  rw h9 at h24,
                  rw usc at h24,
                  cases h24 with w h25,
                  cases h25 with h26 h27,
                  have h28:= single_oneone M b w h27,
                  rw← h28 at *,
                  contradiction, 
                }
              }
            },
            {
              intro h10,
              rw binary_union_axiom at h10,
              cases h10 with h11 h12,
              {
                rw h9 at h11,
                rw usc at h11,
                cases h11 with b h12,
                use b,
                cases h12 with h13 h14,
                rw usc at h5,
                cases h5 with w h15,
                cases h15 with h16 h17,
                have h18: single z = single w := 
                  begin  
                    rw h17 at *,
                    rw sym,
                    exact h8, 
                  end,
                have h19:= single_oneone M z w h18, 
                rw h19 at *,
                rw ssc_members at h16,
                cases h16 with h20 h21,
                have h22:= member_subset M w a b h20 h13, 
                exact ⟨ h22, h14⟩,
              },
              {
                rw usc at h5,
                cases h5 with b h6,
                cases h6 with h13 h14,
                have h15: single z = single b:= 
                  begin 
                    rw h14 at *,
                    rw sym,
                    exact h8,
                  end,
                have h16:= single_oneone M z b h15,
                rw h16 at *,
                rw minus_members at h12,
                cases h12 with h17 h18,
                rw usc at h17,
                cases h17 with w h18,
                use w,
                exact h18, 
              }
            }
          }
        },
        {
          intros x y z,
          intro h4,
          rcases h4 with ⟨ h5, h6, h7⟩,
          rw (h3 x y) at h6,
          rw (h3 x z) at h7,
          cases h6 with u h8,
          cases h7 with v h9,
          cases h8 with h10 h11,
          cases h9 with h12 h13,
          have h14: single u = single v := 
            begin 
              rw h12 at *,
              rw sym,
              exact h10,
            end,
          have h15:= single_oneone M u v h14,
          rw h15 at *,
          rw h13,
          rw h11,
        },
        {
          intro x,
          intro h4,
          rw usc at h4,
          cases h4 with b h5, 
          cases h5 with h6 h7,
          rw ssc_members at h6,
          cases h6 with h8 h9,
          simp_rw h3,
          use (USC b),
          split,
          {
            rw (ssc_members M),
            split,
            {
              rw subset_definition,
              intros z h10,
              rw usc,
              rw usc at h10,
              cases h10 with u h11,
              use u,
              split,
              {
                exact member_subset M b a u h8 h11.left, 
              },
              {
                exact h11.right, 
              }
            },
            {
              intros y h10,
              rw usc at h10,
              cases h10 with u h11,
              cases h11 with h12 h13,
              have h14:= h9 u h12,
              cases h14 with h15 h16,
              {
                left,
                rw h13,
                rw usc,
                use u,
                exact ⟨ h15, refl (single u) ⟩,
              },
              {
                right,
                intro h17,
                rw usc at h17,
                cases h17 with w h18,
                cases h18 with h19 h20,
                have h21: single u = single w:= 
                  begin 
                    rw h20 at *,
                    rw sym,
                    exact h13,
                  end,
                have h22:= single_oneone M u w h21,
                rw h22 at *,
                contradiction, 
              }
            }
          },
          {
            use b,
            exact ⟨ h7, refl (USC b) ⟩, 
          }
        }
      end,
    have h5:onto M (W38 M) (USC (SSC a)) (SSC (USC a)),
      begin
        unfold onto,
        intros y h5,
        have h10:= subset_usc M a y h5,
        cases h10 with z h11,
        cases h11 with h12 h13,  -- line 627
        use (single z),
        split,
        {
          rw usc,
          use z,
          exact ⟨ h12, refl (single z)⟩, 
        },
        {
          rw (W38_members M).right, 
          use z,
          exact ⟨ refl (single z), h13⟩, 
        }
      end,
    have h6: oneone M (W38 M) (USC (SSC a)) (SSC (USC a)):=
      begin
        rw oneone,
        repeat {split},
        {
          exact h2, 
        },
        {
          intros x y h7,
          cases h7 with h8 h9,
          unfold maps at h4,
          rcases h4 with ⟨ h10, h11, h12⟩,
          have h13:= h11 x y ⟨ h8, h9⟩ ,
          exact h13,
        },
        {
          unfold maps at h4,
          rcases h4 with ⟨ h10, h11, h12, h14⟩,
          exact h12, 
        },
        {
          unfold maps at h4,
          rcases h4 with ⟨ h10, h11, h12, h14⟩,
          exact h14, 
        },
        {
          intros x u y h15,
          rcases h15 with ⟨h16, h17, h18⟩,
          rw (W38_members M).right at h16 h17, 
          cases h16 with z h19,
          cases h17 with w h20,
          cases h19 with h21 h22,
          cases h20 with h23 h24,
          have h25: USC z = USC w:= 
            begin 
              rw h24 at *,
              rw sym,
              exact h22, 
            end,
          have h26:= usc_oneone M z w h25,
          rw h26 at *,
          have h27:u = x:= 
            begin 
              rw h21 at *,
              rw h23 at *, 
            end, 
          symmetry, 
          exact h27, 
        },
        {
          intros x y h6,
          cases h6 with h7 h8,
          rw h3 at h7,
          cases h7 with z h9,
          cases h9 with h10 h11,
          rw h10,
          rw usc,
          use z,
          split,
          {
            rw ssc_members,
            rw ssc_members at h8,
            cases h8 with h12 h13,
            rw h11 at h12,
            split,
            {
              rw subset_definition at h12,
              rw subset_definition,
              intro u,
              specialize h12 (single u), 
              intro h14,
              have h15: single u ∈ USC z:=
                begin
                  rw usc,
                  use u,
                  exact ⟨ h14, refl (single u)⟩, 
                end,
              have h16:= h12 h15,
              rw usc at h16,
              cases h16 with w h17,
              have h18:= single_oneone M u w h17.right,
              rw h18 at *,
              exact h17.left, 
            },
            {
              intros y h14, 
              have h20:= h13 (single z),  
              have h15: single y ∈ USC a:=
                begin
                  rw usc,
                  use y,
                  exact ⟨ h14, refl (single y)⟩, 
                end,
              simp_rw h11 at h13,
              have h16:= h13 (single y) h15,
              rw usc at h16,
              cases h16 with h17 h18,
              {
                cases h17 with w h19,
                left,
                cases h19 with h20 h21,
                have h22:= single_oneone M y w h21,
                rw h22 at *,
                exact h20,
              },
              {
                right,
                intro h19,
                exact h18 ⟨ y, h19, (refl (single y))⟩, 
              }
            }
          },
          { 
            exact (refl (single z)),
          }
        }
      end,    --line 629 
    have h7: similar M (USC (SSC a)) (SSC (USC a)) :=
      begin
        unfold similar,
        use (W38 M),
        unfold similarity,
        exact ⟨ h6, h5⟩, 
      end,
    rw full_extensionality,
    intro x,
    rw Nc_members M,
    rw Nc_members M,
    split,
    {
      intro h8,
      have h9:= h7,
      rw similar_symmetric at h9, 
      exact similar_transitive M x (SSC (USC a)) (USC (SSC a)) h8 h9, 
    },
    {
      intro h8,
      exact similar_transitive M x (USC (SSC a)) (SSC (USC a)) h8 h7, 
    }
  end

lemma inhabited_exp: ∀(m:M), m ∈ 𝔽 → (∃(y:M), y ∈ exp M m) →
∃(a:M), USC a ∈ m ∧ SSC a ∈ exp M m := 
assume m,
  begin
    intros h h2,
    cases h2 with y h3,
    rw exp_members at h3,
    cases h3 with a h4,
    cases h4 with h5 h6,
    use a,
    split,
    {
      exact h5,
    },
    {
      rw exp_members,
      use a,
      exact ⟨ h5, similar_reflexive M (SSC a) ⟩, 
    }  
  end 

lemma usc_up_down: ∀(x a:M), x ∈ a ↔ (single x) ∈ USC a:=
  assume x a,
  begin
    rw usc_members,
  end 




lemma uscsimilar: ∀ (a b:M), similar M a b ↔  similar M (USC a)(USC b):=
  assume a b,
  begin
    split,
    {   --left to right, line 628
      intro h,
      unfold similar at h,
      cases h with f h2,
      set g:= SI f with h3,
      unfold similar,
      use g,
      unfold similarity,
      unfold similarity at h2,
      cases h2 with h4 h5,
      unfold oneone at h4,
      rcases h4 with ⟨ h6, h7, h8⟩,
      unfold maps at h6,
      rcases h6 with ⟨ h9, h10, h11, h12⟩,
      have h13:= singleton_image_axiom1 f h9,
      have h14:= singleton_image_axiom2 f h9,
      split,
      {
        unfold oneone,
        rw h3,
        split,
       {
          unfold maps,
          repeat {split},
          {
            exact h13,
          },
          {
            intros x y h15,
            cases h15 with h16 h17,
            specialize h14 x y,
            have h18:= h14.mp h17,
            cases h18 with u h19,
            cases h19 with v h20,
            have h21: ‹ x,y › ∈  SI f:=
              begin
                rw h14,
                use u, use v, 
                exact h20,
              end,
            rcases h20 with ⟨ h22, h23, h24⟩, 
            rw usc,
            use v,
            rw usc at h16,
            cases h16 with w h25,
            have h26: single u = single w:= 
              begin 
                rw← h22,
                rw← h25.right, 
              end,
            have h27:u=w:= single_oneone M u w h26,
            rw h27 at *,
            cases h25 with h28 h29,
            have h30:= h10 w v ⟨ h28, h24⟩, 
            exact ⟨ h30, h23⟩,         
          },
          {
            intros x y z h15,
            rcases h15 with ⟨ h16, h17, h18⟩,
            rw h14 x y at h17,
            rw h14 x z at h18,
            cases h17 with p h19,
            cases h19 with q h20,
            cases h18 with u h21,
            cases h21 with v h22,
            rcases h20 with ⟨ h23, h24, h25⟩,
            rcases h22 with ⟨ h26, h27, h28⟩,
            have h29: single p = single u:= 
              begin 
                rw← h26,
                rw← h23, 
              end,
            have h30:p=u:= single_oneone M p u h29,
            rw h30 at *,
            rw usc at h16,
            cases h16 with c h31,
            cases h31 with h32 h33,
            have h34: single u = single c:= 
              begin
                rw← h33,
                rw← h23,
              end,
            have h35: u=c:= single_oneone M u c h34,
            rw←  h35 at *,
            have h36:= h11 u v q ⟨ h32, h28, h25⟩,
            rw← h36 at *, 
            symmetry, 
            rw h27,
            rw h24, 
          },
          {
            intros x h15,
            rw usc at h15,
            cases h15 with u h16,
            cases h16 with h17 h18,
            have h19:= h12 u h17,
            cases h19 with v h20,
            use (single v),
            rw usc, 
            split,
            { use v, 
              exact ⟨ h20.left, refl (single v)⟩,
            },
            {
              rw (h14 x (single v)),
              use u, use v,
              exact ⟨ h18, refl (single v), h20.right⟩, 
            }
          }
        },
        {
          split,
          {
            intros x u y h15,
            rcases h15 with ⟨ h16, h17, h18⟩,
            rw h14 x y at h16,
            rw h14 u y at h17,
            cases h16 with p h18,
            cases h18 with q h19,
            cases h17 with w h20,
            cases h20 with v h21,
            rcases h19 with ⟨ h22, h23, h24⟩,
            rcases h21 with ⟨ h25, h26, h27⟩,
            have h28: single q = single v := 
              begin 
                rw← h26,
                rw← h23, 
              end,
            have h29:= single_oneone M q v h28,
            rw h29 at *,
            rw h22 at h18,
            rw usc at h18,
            cases h18 with r h30,
            cases h30 with h31 h32,
            have h33:= single_oneone M p r h32,
            rw←  h33 at *,
            have h34:= h7 p w v ⟨ h24, h27, h31⟩, 
            rw h34 at *,
            rw h22,
            rw h25, 
          },
          {
            intros x y h15,
            cases h15 with h16 h17,
            rw h14 x y at h16,
            cases h16 with u h18,
            cases h18 with v h19,
            rw usc,
            use u,
            rw usc at h17,
            cases h17 with p h20,
            rcases h19 with ⟨ h21, h22, h23⟩,
            cases h20 with h24 h25,
            have h26: single p = single v:= 
              begin  
                rw← h25,
                rw← h22, 
              end,
            have h27:= single_oneone M p v h26,
            rw h27 at *,
            have h28:= h8 u v ⟨ h23, h24⟩, 
            exact ⟨ h28, h21⟩, 
          }
        }
      },
      {
        unfold onto,
        intros y h15,
        rw usc at h15,
        cases h15 with u h16,
        unfold onto at h5,
        specialize h5 u,
        cases h16 with h17 h18,
        have h19:= h5 h17,
        cases h19 with x h20,
        cases h20 with h21 h22,
        use (single x),
        rw usc,
        split,
        {
          use x,
          exact ⟨ h21, refl (single x)⟩, 
        },
        {
          rw h18,
          rw h3,
          rw h14,
          use x, use u, 
          simp,
          exact h22, 
        }
      }
    },
    {  -- right to left, line 630 
      unfold similar,
      intro h,
      cases h with g h2,
      use (W41 M g),
      unfold similarity,
      have h3:= W41_members M, 
      specialize h3 g,
      set f:= W41 M g with h30, 
      cases h3 with h4 h5,
      unfold similarity at h2,
      cases h2 with h6 h7,
      unfold oneone at h6,
      unfold maps at h6,
      cases h6 with h9 h10, 
      rcases h9 with ⟨ h11, h12, h13, h14⟩, 
      cases h10 with h15 h16,
      split,
      {
        unfold oneone,
        unfold maps,
        repeat{ split} ,
        {
          exact h4, 
        },
        {
          intros u v, 
          intro h17,
          cases h17 with h18 h19,
          have h20:= (usc M a (single u)).mpr ⟨ u, h18, (refl (single u))⟩, 
          have h21:= (h5 u v).mp h19,
          have h22:= h12 (single u) (single v) ⟨ h20, h21⟩,
          rw← usc_up_down at h22,
          exact h22,
        },
        {
          intros u v w h17,
          cases h17 with h18 h19,
          rw h5 at h19,
          rw h5 at h19,
          rw usc_up_down at h18, 
          cases h19 with h20 h21,
          have h22:= h13 (single u) (single v) (single w) ⟨h18, h20, h21 ⟩,
          exact single_oneone M v w h22, 
        },
        {
          intro u,
          intro h17,
          rw usc_up_down at h17,
          have h18:= h14 (single u) h17,
          cases h18 with y h19,
          cases h19 with h20 h21,
          rw usc at h20,
          cases h20 with p h21,
          cases h21 with h22 h23,
          rw h23 at *,
          have h24:= h12 (single u) (single p) ⟨ h17, h21⟩, 
          rw← usc_up_down at h24,
          use p,
          have h25:= (h5 u p).mpr h21,
          exact ⟨ h22, h25⟩, 
        },
        {
          intros u w v,
          intro h17,
          repeat { rw h5 at h17 },
          rcases h17 with ⟨ h18, h19, h20 ⟩,
          rw usc_up_down at h20,
          have h21:= h15 (single u) (single w) (single v) ⟨ h18, h19, h20⟩,
          exact single_oneone M u w h21, 
        },
        {
          intros u v h17,
          cases h17 with h18 h19,
          rw usc_up_down,
          rw usc_up_down at h19,
          rw h5 at h18,
          unfold onto at h7,
          specialize h7 (single v), 
          have h20:= h7 h19,
          cases h20 with p h21,
          cases h21 with h22 h23,
          rw usc at h22,
          cases h22 with q h24,
          cases h24 with h25 h26,
          rw h26 at *,
          have h27:= h16 (single u) (single v) ⟨ h18, h19⟩,
          exact h27, 
        }
      },
      {
        unfold onto,
        intros v h17,
        rw usc_up_down at h17,
        unfold onto at h7,
        specialize h7 (single v),
        have h18:= h7 h17,
        cases h18 with p h19,
        cases h19 with h20 h21,
        rw usc at h20,
        cases h20 with q h21,
        cases h21 with h22 h23,
        rw h23 at *,
        use q,
        rw h5,
        exact ⟨ h22, h21⟩,
      },
    }
  end 

lemma sscsimilar: ∀ (a b:M), similar M a b →  similar M (SSC a)(SSC b):= 
  assume a b,
  begin
    intro h,
    unfold similar at h,
    cases h with f h2,
    have h2copy:= h2,
    have h200: Rel f:=
      begin 
        unfold similarity at h2copy,
        unfold oneone at h2copy,
        cases h2copy with h201 h202,
        cases h201 with h203 h204,
        unfold maps at h203,
        cases h203 with h205 h206,
        exact h205, 
      end, 
    have h300: ∀(x:M),  Rel (restrict f x):=
      assume x,
      begin
        rw Rel_definition,
        intro z,
        rw restrict_definition, 
        rw intersection_axiom,
        rw product_axiom,
        intro h43,
        cases h43 with h44 h45,
        cases h45 with p h46,
        cases h46 with q h47,
        use p, use q,
        exact h47.right.right, 
      end,
    set g := Z42 M f a with h3,
    unfold similar,
    use g,
    unfold similarity,
    unfold oneone,
    unfold maps,
    repeat{split}, 
    { 
      rw Rel_definition,
      intro z,
      rw h3,
      rw Z42_members M,
      intro h4,
      cases h4 with u h5,
      cases h5 with v h6,
      use u, use v,
      exact h6.left, 
    },
    {
      intros  x y h4,
      cases h4 with h5 h6,
      rw Z42_members at h6,
      cases h6 with u h7,
      cases h7 with v h8,
      cases h8 with h9 h10,
      rw ordered_pair_equality at h9,
      cases h9 with h11 h12,
      rw h11 at *,
      rw h12 at *,
      cases h10 with h13 h14,
      rw ssc_members,
      split,
      {
        rw subset_definition, 
        intro z,
        rw full_extensionality at h14,
        specialize h14 z,
        rw h14,
        intro h15,
        rw range_axiom at h15,
        simp_rw restrict_definition at h15, 
        rw h11 at *,
        rw h12 at *,
        unfold similarity at h2,
        {
          cases h2 with h20 h21,
          unfold oneone at h20,
          cases h20 with h22 h23, 
          cases h15 with p h24,
          rw intersection_axiom at h24,
          cases h24 with h25 h26,
          rw product_axiom at h26, 
          cases h26 with r h27,
          cases h27 with s h28,
          rw ordered_pair_equality at h28,
          rcases h28 with ⟨ h29, h30,h31,h32⟩,
          rw h31 at *,
          rw h32 at *,
          unfold maps at h22,
          cases h22 with h33 h34,
          rcases h34 with ⟨ h35, h36, h37⟩,
          specialize h35 r s,
          rw ssc_members at h5,
          cases h5 with h38 h39,
          have h40:= member_subset M u a r h38 h29,
          exact h35 ⟨ h40, h25⟩, 
        },
        {
          rw Rel_definition,
          intros z h20,
          rw restrict_definition f u at h20,
          rw intersection_axiom at h20,
          cases h20 with h21 h22,
          rw product_axiom at h22,
          cases h22 with p h23,
          cases h23 with q h24,
          rcases h24 with ⟨ h25, h26,h27⟩,
          use p, use q,
          exact h27,
        },
      },
      {  
        intros t h20,
        rw full_extensionality at h14,
        specialize h14 t,
        rw range_axiom at h14,
        { 
          simp_rw restriction at h14,
          rw ssc_members at h5,
          cases h5 with h21 h22,
          unfold similarity at h2,
          cases h2 with h23 h24,
          unfold onto at h24,
          specialize h24 t,
          have h25:= h24 h20,
          cases h25 with p h26,
          cases h26 with h27  h28,
          have h29:= h22 p h27,
          cases h29 with h30 h31,
          {
            left,
            rw h14,
            use p,
            exact ⟨ h28, h30⟩, 
          },
          {
            right, 
            rw h14,
            intro h29,
            cases h29 with q h32,
            cases h32 with h33 h34,
            unfold oneone at h23,
            rcases h23 with ⟨ h35, h36, h37⟩,
            have h38:= h36 p q t ⟨ h28, h33, h27⟩,
            rw h38 at *,
            contradiction, 
          },
        },
        { 
          rw Rel_definition,
          intros z h21,
          rw restrict_definition at h21,
          rw intersection_axiom at h21,
          cases h21 with h22 h23,
          rw product_axiom at h23,
          cases h23 with p h24,
          cases h24 with q h25,
          rcases h25 with ⟨ h26, h27, h28⟩,
          use p, use q,
          exact h28, 
        }
      },
    },
    {
      intros x y z h20,
      rcases h20 with ⟨ h21, h22, h23⟩,
      rw h3 at h22 h23,
      rw Z42_members at h22 h23,
      cases h23 with u h24,
      cases h24 with v h25,
      cases h22 with p  h26,
      cases h26 with q h27,
      cases h25 with h28 h29,
      cases h27 with h30 h31,
      rw ordered_pair_equality at h28 h30,
      cases h30 with h32 h33,
      cases h28 with h34 h35,
      rw← h32 at *,
      rw← h34 at *,
      rw← h33 at *,
      rw← h35 at *,
      cases h31 with h40 h41,
      cases h29 with h42 h43,
      rw h41,
      rw h43, 
    },
    { have h100: Rel (f ∩ (a × 𝕍)):=
          begin
            rw Rel_definition,
            intros z h21,
            rw intersection_axiom at h21,
            cases h21 with h22 h23,
            rw product_axiom at h23,
            cases h23 with p h24,
            cases h24 with q h25,
            rcases h25 with ⟨ h26, h27, h28⟩,
            use p, use q,
            exact h28, 
          end, 
      intros x h20,
      rw h3,
      set y:= image M f x with h21,
      use y,
      rw ssc_members at h20,
      cases h20 with h40 h41,
      have h42: a =  (x ∪ (a-x)):=
        begin
          rw full_extensionality,
          simp_rw binary_union_axiom,
          simp_rw minus_members M,
          intro t,
          specialize h41 t,
          rw subset_definition at h40,
          specialize h40 t,
          split,
          {
            intro h42,
            have h43:= h41 h42, 
            cases h43 with h44 h45,
            {
              left,
              exact h44,
            },
            {
              right,
              exact ⟨ h42, h45⟩, 
            }
          },
          {
            intro h42,
            cases h42 with h43 h44,
            {
              exact h40 h43,
            },
            {
              exact h44.left, 
            }
          },
        end,
      have h101:= separable_similarity M f x a b y h2 h40 h21 h42, 
      rw Z42_members M f a,
     
      split,
      { rw ssc_members,
        split,
        { unfold similarity at h2,
          cases h2 with h50 h51,
          unfold oneone at h50,
          cases h50 with h52 h53,
          have h102:= image_subset M f a b x h52 h40, 
          rw← h21 at h102, 
          exact h102,
        },
        {
          intro t,
          rw full_extensionality at h101, 
          specialize h101 t,
          rw binary_union_axiom at h101,
          rw minus_members M at h101,
          intro h102,
          have h103:= h101.mp h102,
          cases h103 with h104 h105,
          {
            left, 
            exact h104,
          },
          {
            right,
            exact h105.right,
          }
        },
      },
      {  
         use x, use y,
         repeat{split},
         { 
           rw ssc_members,
           exact ⟨ h40, h41 ⟩,
         },
         {
           rw full_extensionality,
           intro t,
           rw range_axiom,
           { 
             simp_rw restriction M f x,
             rw h21,
             rw image_members M,
             split,
             {
               intro h22,
               cases h22 with u h23,
               use u,
               exact ⟨ h23.right, h23.left⟩, 
             },
             {
               intro h22,
               cases h22 with u h23,
               use u,
               exact ⟨ h23.right, h23.left⟩,
             },
             {
               exact h200, 
             }
           },
           { 
             exact h300 x, 
           }
         },
      },
    }, 
    {
      intros x u y h4,
      rw h3 at h4,
      rw (Z42_members M ) at h4,
      rw (Z42_members M ) at h4,
      rcases h4 with ⟨ h5, h6,h7⟩,
      cases h5 with w h8,
      cases h8 with v h9,
      cases h6 with p h10,
      cases h10 with q h11,
      rw ordered_pair_equality at h9 h11,
      rcases h11 with ⟨ h12, h13, h14⟩,
      rcases h9 with ⟨ h15, h16, h17⟩, 
      cases h12 with h18 h19,
      cases h15 with h20 h21,
      rw h18 at *,
      rw h19 at *,
      rw h20 at *,
      rw h21 at *,
      have h22: range (restrict f p) = range (restrict f w) := 
        begin 
          rw← h17,
          rw← h14, 
        end,
      rw full_extensionality at h22,
      simp_rw (range_axiom (restrict f p)  (h300 p)) at h22, 
      simp_rw (range_axiom (restrict f w)  (h300 w)) at h22, 
      simp_rw restriction M at h22,
      rw full_extensionality, 
      intro t,
      unfold similarity at h2,
      cases h2 with h90 h91,
      cases h90 with h92 h93,
      cases h92 with h94 h95,
      rcases h95 with ⟨ h96, h97, h98⟩,
      specialize h98 t,
      rw ssc_members at h13 h16,
      cases h16 with h30 h31, 
      cases h13 with h32 h33,
      split,
      {
        intro h34,
        have h35:t ∈ a:= member_subset M w a t h30 h34,
        have h36:= h98 h35,
        cases h36 with q h37,
        have h38:= h22 q,
        have h39: exists (u:M), ( ‹ u, q › ∈ f ∧ u ∈ w) := 
          begin
            use t,
            exact ⟨ h37.right, h34⟩, 
          end, 
        rw← h38 at h39,
        cases h39 with r h40,
        cases h40 with h41 h42,
        cases h37 with h43 h44,
        cases h93 with h45 h46,
        have h94:= h45 t r q ⟨ h44, h41, h35⟩,
        rw h94 at *,
        exact h42, 
      },
      {
        intro h34,
        have h35:t ∈ a:= member_subset M p a t h32 h34, 
        have h36:= h98 h35,
        cases h36 with q h37,
        have h38:= h22 q,
        have h39: exists (u:M), ( ‹ u, q › ∈ f ∧ u ∈ p) := 
          begin
            use t, 
            exact ⟨ h37.right, h34⟩, 
          end, 
        rw h38 at h39,
        cases h39 with r h40,
        cases h40 with h41 h42,
        cases h37 with h43 h44,
        cases h93 with h45 h46,
        have h94:= h45 t r q ⟨ h44, h41, h35⟩,
        rw h94 at *,
        exact h42, 
      }
    },
    {
      intros x y h20,
      rw h3 at h20,
      rw Z42_members at h20,
      cases h20 with h21 h22,
      cases h21 with u h23,
      cases h23 with v h24, 
      rcases h24 with ⟨ h25, h26, h27⟩,
      rw ordered_pair_equality at h25,
      cases h25 with h36 h37,
      rw h36 at *,
      rw h37 at *,
      rw ssc_members, 
      rw ssc_members at h22,
      cases h22 with h28 h29,
      split,
      {
        rw subset_definition,
        intro t,
        rw (ssc_members M) at h26,
        cases h26 with h38 h39,
        rw subset_definition at h38,
        specialize h38 t,
        exact h38, 
      },
      {
        intros p h40,
        unfold similarity at h2,
        cases h2 with h41 h42,
        unfold oneone at h41, 
        rcases h41 with ⟨ h43, h44, h45⟩, 
        unfold maps at h43,
        rcases h43 with ⟨ h46, h47, h48, h49⟩, 
        specialize h49 p,
        have h50:= h49 h40,
        cases h50 with q h51,
        cases h51 with h52 h53,
        have h54:= h29 q h52,
        cases h54 with h55 h56,
        {
          left,
          rw h27 at h55,
          have h56:= range_axiom (restrict f u) (h300 u),
          specialize h56 q,
          rw h56 at h55,
          cases h55 with r h57,
          rw restriction at h57,
          cases h57 with h58 h59,
          have h60:= h44 p r q ⟨ h53, h58, h40⟩,
          rw h60 at *,
          exact h59, 
        },
        {
          right,
          intro h61,
          rw h27 at h56,
          have h66:= range_axiom (restrict f u) (h300 u),
          specialize h66 q,
          rw h66 at h56,
          apply h56,
          use p,
          rw restriction,
          exact ⟨h53, h61 ⟩,
        },
      }
    },
    {
      rw onto,
      intros y h4,
      set x:= dom ((𝕍 × y)∩ f) with h10,
      use x,
      have hRel: Rel ((𝕍 × y) ∩ f):=
        begin
          rw Rel_definition,
          intros z h11,
          rw intersection_axiom at h11,
          rw product_axiom at h11,
          cases h11 with h12 h13,
          cases h12 with u h14, 
          cases h14 with v h15,
          use u, use v, 
          exact h15.right.right, 
        end,
      have h400: x ∈ SSC a:=
        begin    
          rw ssc_members,
          split,
          {
            rw subset_definition,
            intro t,
            rw full_extensionality at h10,
            specialize h10 t,
            rw h10,
            rw (domain_axiom  ((𝕍 × y) ∩ f) hRel), 
            intro h11, 
            cases h11 with q h12,
            rw intersection_axiom at h12,
            rw pair_in_product M at h12,
            cases h12 with h13 h14,
            cases h13 with h15 h16,
            unfold similarity at h2,
            cases h2 with h17 h18,
            unfold oneone at h17,
            rcases h17 with ⟨ h19, h20, h21⟩,
            rw ssc_members at h4,
            cases h4 with h22 h23,
            have h24:= member_subset M y b q h22, 
            have h25:= h21 t q ⟨ h14, (h24 h16) ⟩,
            exact h25, 
          },
          { 
            intros t h5,
            rw ssc_members at h4,
            cases h4 with h11 h12,
            unfold similarity at h2,
            cases h2 with h41 h42,
            unfold oneone at h41, 
            rcases h41 with ⟨ h43, h44, h45⟩, 
            unfold maps at h43,
            rcases h43 with ⟨ h46, h47, h48, h49⟩, 
            have h50:= h49 t h5,
            cases h50 with q h51,
            cases h51 with h52 h53,
            have h54:= h12 q h52,
            cases h54 with h55 h56,
            {
              left,
              rw h10,
              rw domain_axiom ((𝕍 × y) ∩ f) hRel,
              use q, 
              rw intersection_axiom, 
              rw product_axiom, 
              split,
              { 
                use t, use q, 
                have h56:=  V_definition t, 
                exact ⟨ h56, h55, (refl ‹ t,q› )⟩, 
              },
              {
                exact h53,
              }
            },
            {
              right,
              intro h60,
              rw h10 at h60, 
              rw domain_axiom ((𝕍 × y) ∩ f) hRel  at h60, 
              cases h60 with r h61,
              rw intersection_axiom at h61, 
              rw product_axiom at h61, 
              cases h61 with h62 h63,
              cases h62 with u h64,
              cases h64 with v h65,
              rw ordered_pair_equality at h65,
              rcases h65 with ⟨ h66, h67, h68, h69⟩,
              rw←  h69 at *,
              rw←  h68 at *, 
              have h69:= h45 t q ⟨ h53, h52⟩,
              have h70:= h48 t q r ⟨ h69, h53, h63⟩,
              rw h70 at *, 
              contradiction, 
            },
          },
        end,

        split,
        { 
           exact h400, 
        },
        {
          rw h3,
          rw Z42_members,
          use x, use y,
          split,
          {
            exact (refl ‹ x,y › ),
          },
          {
            split,
            { 
              exact h400,
            },
            {
              rw full_extensionality,
              intro t,
              have h66:= range_axiom (restrict f x) (h300 x) t,
              rw h66,
              simp_rw restriction, 
              unfold similarity at h2,
              cases h2 with h20 h21,
              unfold onto at h21,
              have h30: Rel (𝕍 × y ∩ f):=
                begin
                  rw Rel_definition,
                  intros z h31,
                  rw intersection_axiom at h31,
                  rw product_axiom at h31,
                  cases h31 with h32 h33,
                  cases h32 with r h34,
                  cases h34 with q h35,
                  use r,use q, 
                  exact h35.right.right, 
                end,
              split,
              {
                intro h22,
                specialize h21 t,
                rw ssc_members at h4,
                cases h4 with h23 h24,
                have h25:= member_subset M y b t h23 h22,
                have h26:= h21 h25,
                cases h26 with p h27,
                use p,
                split,
                { 
                  exact h27.right,
                },
                {
                  rw h10,
                 
                  rw domain_axiom (𝕍 × y ∩ f) h30,
                  use t,
                  rw intersection_axiom,
                  rw pair_in_product,
                  split,
                  {
                    exact ⟨ V_definition p , h22 ⟩, 
                  },
                  {
                    exact h27.right,
                  }               
                }
              },
              {
                intro h22,
                cases h22 with p h23,
                cases h23 with h24 h25,
                have h25copy := h25,
                rw h10 at h25, 
                rw domain_axiom (𝕍 × y ∩ f) h30 at h25,
                cases h25 with q h26,
                rw intersection_axiom at h26,
                rw pair_in_product at h26,
                cases h26 with h27 h28, 
                unfold oneone at h20,
                cases h20 with h29 h30,
                unfold maps at h29,
                rcases h29 with ⟨ h31, h32, h33, h34⟩,
                cases h30 with h35 h36,
                rw ssc_members at h4,
                cases h4 with h37 h38,
                have h39:= member_subset M y b q h37 h27.right, 
                cases h27 with h50 h51,  
                have h40:= h36 p q ⟨ h28, h39⟩ , 
                have h41:= h33 p q t ⟨ h40, h28, h24⟩, 
                rw h41 at *, 
                exact h51, 
              }
            }
          }
        }
    }, 
  end 

lemma usc_subset: ∀ (a b:M), a ⊆ b ↔ USC a ⊆ USC b:=
  assume a b,
  begin
    rw subset_definition,
    rw subset_definition,
    split,
    {
      intro h,
      intro z,
      intro h2,
      rw usc at h2,
      cases h2 with u h3,
      cases h3 with h4 h5,
      rw h5,
      rw usc,
      use u,
      exact ⟨ h u h4, refl (single u)⟩, 
    },
    {
      intro h,
      intros z h3,
      specialize h (single z),
      rw usc at h,
      rw usc at h,
      have h4:= h ⟨ z, h3, refl(single z)⟩,
      cases h4 with p h5,
      cases h5 with h6 h7,
      have h8:= single_oneone M z p h7,
      rw h8 at *,
      exact h6,
    }
  end

lemma ssc_subset1: ∀ (a b:M), a ∈ SSC b ↔ USC a ∈ SSC ( USC b):=
  assume a b,
  begin
    rw ssc_members,
    rw ssc_members, 
    split,
    { intro h,
      cases h with h20 h21,
      split,
      {
        exact (usc_subset M a b).mp h20, 
      },
      {
        intro z,
        intro h2,
        rw usc at h2,
        cases h2 with u h3,
        cases h3 with h4 h5,
        rw h5,
        repeat{ rw←  usc_up_down},
        exact (h21 u h4), 
      }
    },
    {
      intro h,
      cases h with h20 h21, 
      split,
      {
        exact (usc_subset M a b).mpr h20,
      },
      {
        intros z h3,
        specialize h21 (single z),
        repeat{ rw← usc_up_down at h21}, 
        exact (h21 h3),
      }
    }
  end

lemma ssc_subset2:∀ (a b :M), a ∈ SSC b ↔ SSC a ⊆ SSC b:=
  assume a b,
  begin
    split,
    { 
      intro h,
      rw ssc_members at h, 
      cases h with h2 h3,
      have h2copy:= h2,
      rw subset_definition at h2,
      rw subset_definition,
      intros z h4,
      rw ssc_members at h4,
      cases h4 with h5 h6,
      rw ssc_members,
      split,
      {
        exact subset_transitive M z a b h5 h2copy, 
      },
      {
        intros y h,
        have h7:= h3 y h, 
        cases h7 with h8 h9,
        {
          exact h6 y h8, 
        },
        {
          right,
          intro h10,
          have h11:= member_subset M z a y h5 h10, 
          contradiction,
        }
      }
    },
    {
      intro h,
      rw ssc_members,
      have h4:a ∈ SSC a:=
        begin
          rw ssc_members,
          split,
          {
            exact (subset_reflexive M a),
          },
          {
            intros y h5,
            left,
            exact h5, 
          }
        end,
      have h6:= member_subset M (SSC a)(SSC b) a h h4,
      rw ssc_members at h6,
      exact h6, 
    },  
  end

lemma ssc_subset4: ∀(b:M), b ∈ FINITE M → ∀ (y :M),
 y ∈ SSC b → ∀ x,x ∈ SSC b→  (x ⊆ y ∨ ¬ x ⊆ y):=
  assume b,
  begin
    intro h, 
    have line673: SSC b ∈ FINITE M:= finitepowerset M b h, 
    have formula41:  SSC b ∈ DECIDABLE M:= finitedecidable M (SSC b) line673,
    have bDecidable: b ∈ DECIDABLE M:= finitedecidable M b h, 
    have base: Λ ∈ W48 M b:=
      begin 
        rw W48_members,
        intros h2 x h3,
        rw (subset_of_empty M x),
        rw decidable_members at formula41, 
        have h8: Λ ∈ SSC b:=
          begin
            rw ssc_members,
            split,
            {
              exact (empty_always_subset M b),
            },
            {
              intros y h9,
              right,
              exact (emptyset_axiom y),
            }
          end,
        exact ( formula41 x Λ ⟨ h3, h8⟩), 
      end,
    have step: adjoin_closed M (W48 M b):=
      begin
        unfold adjoin_closed,
        intros z c h4,
        rw (W48_members M  b),
        rw (W48_members M  b) at h4,
        cases h4 with formula43 h6,
        intros h3 x h20, 
        have line682: c ∈ x ∨ ¬ c ∈ x:=
          begin
            rw ssc_members M at h3,
            cases h3 with h9 h10,
            specialize h10 c, 
            rw (union_commutative M) at h9,
            have h12:= union_subset M (single c) z b h9,
            rw subset_definition at h12,
            specialize h12 c,
            rw singleton1 M at h12,
            have h13:= h12 (refl c),
            have h14:= h10 h13,
            rw ssc_members at h20,
            cases h20 with h21 h22,
            have h23:= h22 c h13,
            exact h23, 
          end,
        have line683: z ∈ SSC b:=
          begin
            rw ssc_members M at h3,
            cases h3 with h30 h31,
            rw ssc_members M,
            have h32:= union_subset M z (single c) b h30,
            split,
            { 
              exact h32,
            },
            {
              intro y,
              specialize h31 y,
              intro h33,
              have h34:= h31 h33,
              rw binary_union_axiom at h34,
              cases h34 with h35 h36,
              {
                cases h35 with h37 h38,
                {
                  exact or.inl h37, 
                },
                {
                  rw singleton1 M at h38, 
                  rw h38,
                  right,
                  exact h6, 
                }
              },
              { rw not_orNF at h36, 
                cases h36 with h37 h38,
                right,
                exact h37, 
              }
            }
          end, 
        have line684: x-(single c) ∈ SSC b:=
          begin
            rw ssc_members M at h20, 
            cases h20 with h30 h31,
            rw ssc_members M,
            rw decidable_members at bDecidable,
            split,
            { 
              have h32:= minus_subset M x (single c),
              have h32:= subset_transitive M (x - (single c)) x b h32 h30,
              exact h32, 
            },
            { 
              intro y,
              specialize h31 y,
              intro h33,
              have h34:= h31 h33,
              rw minus_members M,
              rw (singleton1 M),
              have h40: c ∈ b:=
                begin
                  rw ssc_members M at h3,
                  cases h3 with h41 h42,
                  rw union_commutative M at h41,
                  have h43:= union_subset M (single c) z b h41, 
                  rw subset_definition at h43,
                  specialize h43 c,
                  rw singleton1 M at h43,
                  exact h43 (refl c), 
                end,
              have h45:= bDecidable y c ⟨ h33, h40⟩, 
              cases h45 with h46 h47,
              {  
                 rw h46 at *,
                 right,
                 intro h48,
                 cases h48 with h49 h50,
                 contradiction, 
              },
              { 
                cases h34 with h51 h52,
                {
                  left,
                  exact  ⟨ h51, h47⟩, 
                },
                {
                  right,
                  intros h53,
                  cases h53 with h54 h55,
                  contradiction, 
                }
              }
            }
          end, 
        have formula45:∀ (x : M), x ∈ SSC b → x ⊆ z ∨ ¬x ⊆ z:= formula43 line683, 
        cases line682 with case1 case2,
        {
          have h50:= formula45 (x-(single c)) line684,
          cases h50 with h51 h52,
          {
            left,
            rw subset_definition,
            intros t h53,
            rw subset_definition at h51,
            specialize h51 t, 
            rw minus_members at h51,
            rw binary_union_axiom,
            rw singleton1 M,
            rw singleton1 at h51,
            rw ssc_members at h20,
            cases h20 with h55 h56,
            have h57: t ∈ b:= member_subset M x b t h55 h53,
            have h58: c ∈ b:= member_subset M x b c h55 case1,
            rw (decidable_members M) at bDecidable, 
            have h59:=  bDecidable t c ⟨ h57, h58⟩ , 
            cases h59 with h60 h61,
            {
              right,
              exact h60,
            },
            {
              left,
              exact h51 ⟨ h53, h61⟩, 
            }
          },
          {
            right,
            intro h70,
            rw subset_definition at h70,
            rw subset_definition at h52,
            apply h52,
            intro t,
            specialize h70 t,
            rw minus_members M,
            rw binary_union_axiom at h70,
            rw (singleton1 M) at h70,
            rw singleton1, 
            intro h71, 
            cases h71 with h72 h73, 
            have h74:= h70 h72,
            cases h74 with h75 h76,
            {
              exact h75,
            },
            {
              contradiction, 
            }
          } 
        },
        { 
          have h80:= formula45 x h20,
          cases h80 with h81 h82,
          {
            left,
            exact subset_union M x z (single c) h81,
          },
          {
            right,
            rw subset_definition,
            rw subset_definition at h82,
            intro h100,
            apply h82,
            intro t,
            intro h101,
            have h102:= h100 t h101,
            rw binary_union_axiom at h102,
            rw singleton1 at h102,
            cases h102 with h103 h104,
            {
              exact h103,
            },
            {
              rw h104 at *,
              contradiction, 
            },
          }
        }
      end, 
    have h90: (FINITE M)⊆ W48 M b := (finite_conditions M) (W48 M b)  step base,
    rw subset_definition at h90, 
    intro z,
    specialize h90 z,
    rw W48_members M b at h90,
    intro h91,
    have h91copy := h91, 
    rw ssc_members at h91,
    cases h91 with h92 h93,
    have h94:= separablefinite M b h z h92,
    unfold separable_subset at h94,
    have h95:z ∈ FINITE M:=
      begin
        rw full_extensionality M at h94,
        rw subset_definition at h94,
        apply h94,
        split,
        {
          intros t h95,
          specialize h93 t,
          exact (member_subset M z b t h92 h95), 
        },
        {
          intro t,
          rw binary_union_axiom,
          rw (minus_members M),
          specialize h93 t,
          split,
          {
            intro h94,
            have h95:= h93 h94,
            cases h95 with h100 h101,
            {
              left,
              exact h100,
            },
            {
              right,
              exact ⟨ h94, h101⟩, 
            } 
          },
          {
            intro h96,
            cases h96 with h97 h98,
            {
              exact (member_subset M z b t h92 h97), 
            },
            {
              exact h98.left, 
            }
          }
        }
      end, 
    exact h90 h95 h91copy, 
  end

  lemma ssc_subset3:∀ (a b :M), a ∈ FINITE M → b ∈ FINITE M → a ∈ SSC b → SSC a ∈ SSC (SSC b):=
    assume a b,
    begin
      intros h1 h2 line677,
      have formula46: SSC a ⊆ SSC b:= (ssc_subset2 M a b).mp line677,
      rw ssc_members,
      split,
      {
        exact formula46,
      },
      {  
        intro t,
        intro h3,
        have h3copy := h3,
        have formula48: t ⊆ a ∨ ¬ t ⊆ a:= ssc_subset4 M b h2 a line677 t h3, 
        cases formula48 with case1 case2,
        {
          left,
          rw ssc_members,
          split,
          {
            exact case1, 
          },
          {
            rw ssc_members at h3,
            cases h3 with h4 h5,
            intros y h6,
            specialize h5 y,
            rw ssc_members at line677,
            cases line677 with h8 h9, 
            have h7: y ∈ b := member_subset M a b y h8 h6,
            exact h5 h7, 
          }
        },
        { 
          right,
          rw ssc_members,
          intro h20,
          cases h20 with h21 h22, 
          contradiction, 
        }    
      }
    end

lemma usc_successor: ∀ (a c:M), ¬ c ∈ a → USC (a ∪ (single c)) = ((USC a) ∪ single (single c)):=
  assume a c,
  begin
    intro h,
    rw full_extensionality,
    intro x,
    rw usc, 
    split,
    {
      intro h2,
      cases h2 with u h3,
      cases h3 with h4 h5,
      rw binary_union_axiom,
      rw binary_union_axiom at h4,
      cases h4 with h6 h7,
      {
        left,
        rw usc_up_down at h6,
        rw h5 at *,
        exact h6,
      },
      {
        right,
        rw singleton1 M, 
        rw h5,
        rw singleton1 M at h7,
        rw h7 at *, 
      }
    },
    {
      intro h2,
      rw binary_union_axiom at h2,
      rw usc M at h2,
      cases h2 with h3 h4,
      {
        cases h3 with t h5,
        use t,
        rw binary_union_axiom,
        split,
        {
          left,
          exact h5.left,
        },
        {
          exact h5.right,
        }
      },
      {
        rw singleton1 M at h4,
        use c,
        rw binary_union_axiom,
        rw singleton1 M,
        split,
        {
          right,
          exact refl c,
        },
        {
          exact h4, 
        }
      }
    }
  end 
    
lemma usc_intersection: ∀(a b:M), USC (a ∩ b) = ((USC a) ∩ (USC b)):=
  assume a b,
  begin
    rw full_extensionality,
    intro t,
    rw usc,
    split,
    { 
      intro h,
      cases h with p h2,
      rw intersection_axiom at h2,
      cases h2 with h3 h4,
      rw h4 at *,
      cases h3 with h5 h6,
      rw intersection_axiom,
      rw usc,
      split,
      { 
        use p,
        simp,
        exact h5,
      },
      {
        rw usc,
        use p,
        exact ⟨ h6, refl (single p)⟩, 
      }
    },
    {
      intro h,
      rw intersection_axiom at h,
      rw usc at h,
      cases h with h2 h3,
      cases h2 with p h4,
      cases h4 with h5 h6,
      rw usc at h3,
      cases h3 with q h7,
      cases h7 with h8 h9,
      have h10: single p = single q:= 
        begin 
          rw← h6,
          rw← h9,
        end,
      have h11: p=q:= single_oneone M p q h10,
      rw h11 at *,
      use q,
      rw intersection_axiom,
      exact ⟨ ⟨ h5,h8⟩, h6⟩, 
    }
  end

  lemma similar_singletons1: ∀ (a b:M), similar M (single a)(single b):=
    assume a b,
    begin
      set f:= single (‹ a,b › ) with h2,
      have h3:similarity M f (single a) (single b):=
        begin
          unfold similarity,
          split,
          {
            unfold oneone,
            repeat {split},
            {
              rw Rel_definition,
              intro z,
              intro h3,
              use a, use b,
              rw h2 at h3,
              rw singleton1 M at h3,
              exact h3, 
            },
            {
              intros x y,
              rw singleton1 M,
              rw singleton1 M,
              rw ordered_pair_equality,
              rw singleton1 M,
              intros h4,
              exact h4.right.right,
            },
            {
              intros x y z,
              rw singleton1 M,
              intro h3,
              rcases h3 with ⟨ h4, h5, h6⟩,
              rw h4 at *,
              rw h2 at *,
              rw singleton1 M at h5 h6,
              rw ordered_pair_equality at h5 h6,
              rw h6.right,
              rw h5.right, 
            },
            {
              intros x h3,
              rw singleton1 M at h3,
              rw h3 at *,
              use b,
              rw singleton1 M,
              rw h2,
              rw singleton1 M,
              exact ⟨ refl b, refl ‹ a, b› ⟩, 
            },
            {
              intros x u y,
              rw h2,
              repeat{rw singleton1 M},
              repeat{rw ordered_pair_equality M},
              intros h3,
              rw h3.right.right,
              rw h3.right.left.left,
            },
            {
              intros x y,
              rw h2,
              repeat{rw singleton1 M},
              repeat{rw ordered_pair_equality M},
              intros h4,
              exact h4.left.left,
            }
          },
          {
            unfold onto,
            intros y,
            rw h2,
            intro h3,
            use a,
            rw singleton1 M at h3, 
            rw h3 at *,
            repeat{rw singleton1 M},
            repeat{rw ordered_pair_equality M},
            exact ⟨ refl a, refl a, refl b⟩,
          }
        end,
      unfold similar,
      use f,
      exact h3, 
    end
 

lemma usc_dif2: ∀(a b:M), USC (a-b) = (USC a) - USC b:=
  assume a b,
  begin
    rw full_extensionality,
    intro t,
    rw minus_members, 
    repeat{rw usc},
    split,
    {
      intro h,
      cases h with p h2,
      rw minus_members  at h2,
      cases h2 with h3 h4,
      cases h3 with h5 h6,
      split,
      {
        use p,
        exact ⟨ h5, h4⟩, 
      },
      {
        intro h7,
        cases h7 with q h8,
        cases h8 with h9 h10,
        have h11: single p = single q:= 
          begin 
            rw← h4,
            rw← h10,  
          end,
        have h12:= single_oneone M p q h11,
        rw h12 at *,
        contradiction, 
      }
    },
    {
      intro h2,
      cases h2 with h3 h4,
      cases h3 with p h5,
      cases h5 with h6 h7,
      use p,
      rw minus_members,
      split,
      {
        split,
        {
          exact h6,
        },
        {
          intro h9,
          exact h4 ⟨ p, ⟨ h9, h7⟩ ⟩,
        }
      },
      {
        exact h7, 
      }
    }
  end

lemma similarinhabited: ∀ (a b:M), similar M a b → (∃ (u:M), u ∈ a) → ∃ (u:M), u ∈ b:=
  assume a b,
  begin
    intros h h2,
    unfold similar at h,
    cases h with f h3,
    unfold similarity at h3,
    cases h2 with c h4,
    cases h3 with h5 h6,
    unfold oneone at h5,
    cases h5 with h6 h7,
    unfold maps at h6,
    cases h6 with h7 h8,
    rcases h8 with ⟨ h9 , h10, h11⟩, 
    have h12:= h11 c h4,
    cases h12 with y h13,
    exact ⟨ y, h13.left⟩, 
  end
  
#axioms_all   --This file is clean.

