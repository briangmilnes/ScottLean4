 -- Section 5 of the paper,  order on the cardinals
import inf4       
variables (M:Type) [Model M] (a b x y z u v w X R W κ μ ℓ : M)
-- using ℓ where the source text has λ because you can't use λ for a variable.

open Model 

def image:= λ(f a:M), (range (f ∩ (a × 𝕍) ))

lemma image_members: ∀ (f a:M), Rel f → ∀ y, (y ∈ image M f a ↔ ∃ (x:M),(x∈ a ∧ ‹ x,y › ∈ f)):=
  assume f a, 
  begin 
    intros h y, 
    unfold image, 
    rw (range_axiom ),
    {
      split,
      { 
        intro h2, 
        cases h2 with x h3,
        use x,
        rw intersection_axiom at h3,
        cases h3 with h4 h5,
        rw product_axiom at h5,
        cases h5 with u h6,
        cases h6 with v h7,
        rw (ordered_pair_equality M) at h7,
        rcases h7 with ⟨ h8, h9, h10, h11⟩,
        rw← h10 at *, 
        rw← h11 at *, 
        exact ⟨ h8, h4⟩, 
      },
      {
        intro h2, 
        cases h2 with x h3,
        use x, 
        rw intersection_axiom,
        rw product_axiom, 
        split,
        {
          exact h3.right,
        },
        {
          use x, use y,
          repeat { split }, 
          {
            exact h3.left,
          },
          {
            exact (V_definition y),
          },
        }
      }
    },
    {
      rw Rel_definition at *, 
      intro z,
      specialize h z,
      intro h2,
      rw intersection_axiom at h2,
      cases h2 with h3 h4,
      rw product_axiom at h4,
      cases h4 with u h5,
      cases h5 with v h6,
      use u, use v,
      exact h6.right.right, 
    }
  end

lemma similarity_implies_Rel: ∀ (f x y:M), similarity M f x y → Rel f:=
  assume f x y,
  begin
    unfold similarity,
    intro h,
    cases h with h1 h2,
    unfold oneone at h1,
    rcases h1 with ⟨ h3, h4, h5⟩,
    unfold maps at h3,
    cases h3 with h6 h78,
    exact h6, 
  end

lemma image_subset: ∀ (f x y a:M), maps M f x y → a ⊆ x → image M f a ⊆ y:=
  assume f x y a,
  begin
    intros h1 h2,
    unfold maps at h1,
    cases h1 with h3 h4,
    rcases h4 with ⟨ h5,h6,h7⟩,
    rw subset_definition at h2,
    rw subset_definition,
    intro z,
    rw (image_members M f a h3),
    intro h8,
    cases h8 with u h9,
    cases h9 with h10 h11,
    have h12:= h2 u h10,
    have h13:= h5 u z ⟨ h12, h11⟩,
    exact h13, 
  end

lemma similarity_subset: ∀ (f a b c:M), similarity M f b c → a ⊆ b → similarity M f a (image M f a):=
  assume f a b c,
  begin
    intros h h2,
    have h3: Rel f:= (similarity_implies_Rel M f b c h),
    unfold similarity,
    split,
    {
      unfold oneone,
      rw subset_definition at h2,
      unfold similarity at h,
      cases h with h10 h11,
      unfold oneone at h10,
      cases h10 with h12 h13,
      unfold maps at h12,
      rcases h12 with ⟨ h14,h15,h16,h17⟩,
      repeat {split},
      {
        exact h3,
      },
      {
        intros x y h4,
        specialize h2 x,
        rw (image_members M),
        use x,
        exact h4,
        exact h3, 
      },
      {
        intros x y z,
        intro h5,
        rcases h5 with ⟨ h6,h7,h8⟩,
        have h9:= h2 x h6,
        exact h16 x y z ⟨ h9, h7, h8⟩,
      },
      {
        intros x h4,
        have h5:= h2 x h4, 
        have h20:= h17 x h5,
        cases h20 with y h21,
        use y,
        split,
        {
          rw (image_members M f a h3),
          use x,
          exact ⟨ h4, h21.right⟩, 
        },
        { 
          exact h21.right,
        }
      },
      {
        intros x u y h30,
        rcases h30 with ⟨ h31, h32, h33⟩,
        cases h13 with h34 h35,
        exact (h34 x u y ⟨ h31, h32, h2 x h33⟩), 
      },
      { 
        intros x y h40,
        cases h40 with h41 h42,
        rw (image_members M f a h3 y) at h42,
        cases h42 with u h44,
        cases h44 with h45 h46,
        cases h13 with h47 h48,
        have h49:= h47 u x y ⟨ h46,h41, h2 u h45⟩,
        rw h49 at *,
        exact h45,   
      }
    },
    {
      unfold similarity at h,
      cases h with h50 h51,
      unfold onto at h51,
      unfold onto,
      intros y h52, 
      specialize h51 y,
      rw (image_members M f a h3 y) at h52,
      cases h52 with x h53,
      use x,
      exact h53, 
    }
  end

lemma base19: (zero:M) ∈ Z19 M:= 
  begin
    rw (Z19_members M),
    split,
    {
      exact (zeroF M), 
    },
    {
      intros x y h,
      rw (in_zero M) at h,
      rw h,
      rw (in_zero M),
      intro h2,
      rw (similar_symmetric M) at h2, 
      exact (similar_to_empty2 M y h2),   -- line 366 
    }
  end 
 
lemma step19:  ∀(κ:M), κ ∈ Z19 M → (∃ u, u ∈ 𝕊 κ ) → 𝕊 κ ∈ Z19 M:=
  assume κ, 
  begin 
    repeat{ rw (Z19_members M)}, 
    intros h h10, 
    cases h with h2 h3,

    split,
    {
      exact (successorF M κ h2 h10),
    },
    { 
      intros x y h4 h5,
      have h4copy := h4, 
      unfold similar at h5,
      cases h5 with f h6,
      rw (successor_members M) at h4,
      cases h4 with u h7,
      cases h7 with a h8,
      rcases h8 with ⟨ h11, h12, h13⟩, 
      have h9: Rel f := similarity_implies_Rel M f x y h6,
      have h6copy:= h6,
      unfold similarity at h6, 
      cases h6 with h14 h15,
      unfold oneone at h14,
      cases h14 with h16 h17,
      unfold maps at h16,
      cases h16 with h18 h19,
      cases h19 with h20 h21,
      cases h21 with h22 h23,
      specialize h23 a,
      have h24:=adjoin_member M a u,
      rw← h13 at h24, 
      have h25:= h23 h24, 
      cases h25 with b h26,
      cases h26 with h27 h28,  -- line 370, let b = f(a).
      set v:= image M f u with h29,  --line 369
      have h30: ¬ b ∈ v:=   -- line 370
        begin
          intro h31, 
          rw (full_extensionality M) at h29,
          specialize h29 b, 
          have h30:= h29.mp h31,
          rw ( image_members M f u h9) at h31,
          cases h31 with w h32,
          cases h17 with h33 h34,
          have h35:= adjoin_member2 M w a u h32.left,
          rw← h13 at h35,
          have h36:= h33 w a b ⟨ h32.right, h28, h35⟩,
          rw h36 at *,
          cases h32 with h40 h41,
          contradiction, 
        end,
      have h40: u ⊆ x:= 
        begin
          rw subset_definition,
          intro z,
          rw h13,
          exact (adjoin_member2 M z a u),
        end,
      have h45:= similarity_subset M f u x y h6copy h40, 
      rw← h29 at h45,
      have h46: similar M u v:=
        begin
          unfold similar,
          use f,
          exact h45, 
        end,
      have h47: v ∈ κ := h3 u v h11 h46,   --line 370 
      have h50: v ∪ (single b) ∈  𝕊 κ:=   --line 371
        begin
          rw ( successor_members M),
          use v, use b,
          exact ⟨ h47, h30, refl (v ∪ (single b))⟩,
        end, 
      have h55: v ⊆ y:=
        begin
          rw h29,
          have h6copy2:= h6copy,
          unfold similarity at h6copy2,
          cases h6copy2 with h56 h57,
          unfold oneone at h56,
          cases h56 with h58 h59,
          have h70:= image_subset M f x y u h58 h40,
          exact h70,
        end, 
      have h80: x ∈ FINITE M:=
        begin
          have h81:= finitecardinals1 M (𝕊 κ ) x,
          have h82: 𝕊 κ  ∈ 𝔽 := successorF M κ h2 h10, 
          exact (h81 h82 h4copy),
        end,
      have h83: x ∈ DECIDABLE M:=   -- line 373
        begin 
          exact (finitedecidable M x h80), 
        end,   
      have h60: v ∪ (single b) = y:=  --line 372
        begin
          rw ( full_extensionality M),
          intro p,
          split,
          {
            intro h61,
            rw binary_union_axiom at h61,
            rw subset_definition at h55,
            specialize h55 p,
            cases h61 with h62 h63,
            {
              exact h55 h62, 
            },
            {
              rw (singleton1 M) at h63,
              rw h63,
              exact h27, 
            }
          },
          {
            intro h70,
            unfold onto at h15,
            specialize h15 p,
            have h71:= h15 h70,
            cases h71 with q h72,
            cases h72 with h73 h74,
            rw (decidable_members M) at h83,
            have h75: q = a ∨ ¬ q = a:= h83 q a ⟨ h73,h24⟩, 
            cases h75 with h76 h77,
            {
              rw h76 at *,
              cases h17 with h78 h79,
              have h90:= h22 a p b ⟨  h73, h74, h28⟩ , 
              rw h90,
              exact (adjoin_member M b v),
            },
            {
              have h91:q∈ u:=   --line 375
                begin
                  rw h13 at h73,
                  rw binary_union_axiom at h73,
                  rw (singleton1 M) at h73,
                  cases h73 with h74 h75,
                  { 
                    exact h74,
                  },
                  {
                    rw h75 at *,
                    contradiction, 
                  }
                end,
              have h92: p∈ v:=   --line 376
                begin
                  rw h29,
                  rw (image_members M f u h9), 
                  use q,
                  exact ⟨ h91, h74⟩, 
                end,
              exact (adjoin_member2 M p b v h92),
            }
          }
        end, 
      rw (successor_members M),
      use v, use b,
      repeat {split},
      {
        exact h47, 
      },
      {
        exact h30,
      },
      {
        symmetry, 
        exact h60, 
      }
    },
  end 

lemma finitecardinals0:  ∀(κ x y:M), (κ ∈ 𝔽 → x ∈ κ → similar M x y → y ∈ κ )  :=   
  assume κ x y, 
  begin  
    intro h, 
    rw F_members at h,    
    specialize h (Z19 M),
    have h3:= h (and.intro (base19 M) (step19 M)), 
    rw (Z19_members M) at h3, 
    cases h3 with h4 h5,
    specialize h5 x y,
    exact h5,  
  end


lemma separable_similarity: ∀ (f a b c e:M),
-- the image of a separable subset is a separable subset.
-- Lemma 26 in the paper, line 453 
similarity M f b c →
a ⊆ b → 
e = image M f a → 
b = (a ∪ (b-a)) → 
c = (e ∪ (c-e)):=
  
  assume f a b c e,
  begin 
    intros h1 h2 h3 h4,
    have h1copy := h1,
    have h50: Rel f:= similarity_implies_Rel M f b c h1,
    unfold similarity at h1,
    cases h1 with h5 h6, 
    unfold oneone at h5,
    rcases h5 with ⟨ h7, h8, h9⟩, 
    rw full_extensionality,
    intro y,
    have h10:= image_subset M f b c a h7 h2,
    rw← h3 at h10,
    rw subset_definition at h10,
    specialize h10 y,
    split,
    {
      intro h11,
      unfold onto at h6,
      specialize h6 y,
      have h12:= h6 h11,
      cases h12 with x h13,
      cases h13 with h14 h15,
      rw h4 at h14,
      rw binary_union_axiom at h14,
      rw binary_union_axiom,
      cases h14 with h16 h17,
      {
        left,
        rw h3,
        rw (image_members M f a h50),
        use x,
        exact ⟨ h16, h15 ⟩, 
      },
      {
        right,
        rw (minus_members M),
        split,
        {
          exact h11,
        },
        {
          intro h18,
          have h3copy:= h3,
          rw (full_extensionality M) at h3copy,
          specialize h3copy y,
          have h19 := h3copy.mp h18, 
          rw (image_members M f a h50) at h19, 
          cases h19 with w h20,
          cases h20 with h21 h22,
          rw (minus_members M) at h17,
          cases h17 with h23 h24,
          have h25:= h8 x w y ⟨ h15, h22, h23⟩,
          rw← h25 at *,
          contradiction,  
        }
      },
    },
    {
      intro h11,
      rw binary_union_axiom at h11,
      cases h11 with h12 h13,
      {
        exact h10 h12, 
      },
      {
        rw (minus_members M) at h13,
        exact h13.left, 
      }
    }
  end

lemma union_minus: ∀ (p q r:M), (p ∪  q) - r = ((p-r) ∪ (q-r)):=
  assume p q r,
  begin
    rw full_extensionality,
    intro x,
    rw minus_members M,
    rw binary_union_axiom,
    rw binary_union_axiom,
    rw minus_members M,
    rw minus_members M,
    split,
    {
      intro h,
      cases h with h1 h2,
      cases h1 with h3 h4,
      {
        left,
        exact ⟨ h3,h2⟩,
      },
      {
        right,
        exact ⟨ h4,h2⟩,
      }
    },
    {
      intro h,
      split,
      {
        cases h with h2 h3,
        {
          left,
          exact h2.left, 
        },
        {
          right,
          exact h3.left, 
        }
      },
      {
        cases h with h1 h2,
        {
          exact h1.right,
        },
        {
          exact h2.right, 
        }
      }
    }
  end 

--Lemma 30 in the paper, line 460 
lemma le_transitive: ∀ (κ μ ℓ : M), κ ∈ 𝔽 → μ ∈ 𝔽 → ℓ ∈ 𝔽 → 
κ ≤ ℓ  → ℓ ≤ μ  → κ ≤ μ  := 
  assume κ μ ℓ ,
  begin
    intros h1 h2 h3 h4 h5,
    rw le_definition at *,
    cases h4 with a h6,
    cases h6 with b h7,
    cases h5 with c h8,
    cases h8 with d h9,
    rcases h7 with ⟨ h10, h11, h12, h13 ⟩,
    rcases h9 with ⟨ h14, h15, h16, h17⟩, 
    have h18: similar M b c:= finitecardinals2 M b c ℓ h3 h11 h14,
    unfold similar at h18,
    cases h18 with f h19,
    have h50: Rel f:= similarity_implies_Rel M f b c h19, 
    set e:= (image M f a) with h20,
    have h21:  e ⊆ c:=   --line 446
      begin
        rw subset_definition,
        intro z,
        rw h20,
        rw (image_members M f a h50 ),
        intro h22,
        cases h22 with x h23,
        cases h23 with h24 h25,
        unfold similarity at h19,
        cases h19 with h26 h27,
        unfold oneone at h26,
        rcases h26 with ⟨ h27, h28, h29⟩,
        unfold maps at h27,
        cases h27 with h30 h31,
        rcases h31 with ⟨ h32, h33, h34⟩,
        specialize h32 x z,
        rw subset_definition at h12,
        have h35:= h12 x h24,
        have h36:= h32 ⟨ h35, h25⟩,
        exact h36, 
      end,
    have h22: similar M a e:=   -- line 446 
      begin
        unfold similar,
        use f,
        exact (similarity_subset M f a b c h19 h12),
      end,
    have h23: similar M e a:= similar_symmetric_left_right M a e h22,
    have h24: e ∈ κ := (finitecardinals0 M κ a e h1 h10 h22), --line 446 
    have h25: e ⊆ d:= subset_transitive M e c d h21 h16, --line 447
    have h26: c = (e ∪ (c-e)):=  -- formula (22), line 447b
      separable_similarity M f a b c e h19 h12 h20 h13,
    have h27: ((d-c)-e) = d-c :=
      begin
        rw full_extensionality,
        intro x,
        rw minus_members M,
        split,
        {
          intro h30,
          exact h30.left,
        },
        {
          intro h32,
          split,
          {
            exact h32,
          },
          {
            intro h33,
            rw subset_definition at h21,
            have h34:= h21 x h33,
            rw minus_members at h32,
            cases h32 with h34 h35,
            contradiction, 
          }
        }
      end, 
    have h28: d = (e ∪ (d-e)):=    --line 448 
      begin
        symmetry,
        rw h17,
        rw union_minus M c (d-c) e,
        rw← union_associative,
        rw← h26,
        rw h27,
      end,
    use e, use d,
    exact ⟨ h24, h15, h25, h28⟩,
  end
 
lemma cardinalsdisjoint: ∀(κ μ x:M), κ ∈ 𝔽 → μ ∈ 𝔽 → x∈ κ ∩ μ → κ = μ := --line 450 
  assume κ μ x,
  begin
    intros h1 h2 h3,
    rw intersection_axiom at h3,
    cases h3 with h4 h5,
    rw full_extensionality,
    intro y,
    split,
    {
      intro h6, 
      have h7: similar M y x:= finitecardinals2 M y x κ h1 h6 h4, 
      rw similar_symmetric at h7, 
      exact finitecardinals0 M μ x y h2 h5 h7, 
    },
    {
      intro h6,
      have h7: similar M y x:= finitecardinals2 M y x μ h2 h6 h5,
      rw similar_symmetric at h7,
      exact finitecardinals0 M κ x y h1 h4 h7, 
    }
  end

lemma lessthan2: ∀(κ μ:M), κ ∈ 𝔽 → μ ∈ 𝔽 →  
(κ < μ ↔ ∃(x y:M),(x ∈ κ ∧ y ∈ μ ∧ x ⊂ y ∧  y = (x ∪ (y-x)))):= --line 475
  assume κ μ,
  begin
    intros h1 h2,
    split,
    {  -- left-to-right, line 455 
      intro h3,
      rw lessthan_definition at h3,
      cases h3 with h4 h5,
      rw le_definition at h4,
      cases h4 with x h5,
      cases h5 with y h6,
      rcases h6 with ⟨ h7, h8, h9, h10⟩,
      use x, use y, 
      have h11: ¬ x = y:=
        begin
          intro h12,
          rw h12 at *, 
          have h13: x ∈ κ ∩ μ := 
            begin
              rw intersection_axiom, 
              rw h12, 
              exact ⟨ h7, h8 ⟩, 
            end,
          have h14:= cardinalsdisjoint M κ μ x h1 h2 h13, 
          contradiction, 
        end,
      repeat {split},
      {
        exact h7,
      },
      {
        exact h8,
      },
      {
        rw proper_subset_definition, 
        exact ⟨ h9, h11⟩,
      },
      {
        exact h10,
      }
    },
    {   -- right-to-left, line 459
      intro h3,
      cases h3 with x h4,
      cases h4 with y h5,
      rcases h5 with ⟨ h6,h7, h8, h9⟩,   -- line 459 
      rw lessthan_definition,
      have h10: x ⊆ y:=
        begin
          rw proper_subset_definition at h8,
          cases h8 with h11 h12,
          exact h11, 
        end,
      split,
      {
        rw le_definition,
        use x, use y,
        exact ⟨ h6, h7, h10, h9 ⟩, 
      },
      {
        intro h11, 
        rw← h11 at *, 
        have h12:similar M y x:= finitecardinals2 M y x κ h1 h7 h6, 
        have h13: y ∈ FINITE M:= finitecardinals1 M κ y h1 h7,
        have h14:= Theorem1 M y h13 x h10 h12,
        rw proper_subset_definition at h8, 
        cases h8 with h20 h21,
        rw h14 at *,
        contradiction,
      }
    }
  end

lemma le2: ∀(κ μ:M), κ ∈ 𝔽 → μ ∈ 𝔽 → (∃ w,(w ∈ μ )) → 
(κ ≤ μ ↔ ∀ b,(b ∈ μ → ∃ a,(a ∈ κ ∧ a ⊆ b ∧ b = (a ∪ (b-a))))):=
  assume κ μ,
  begin
    intros h1 h2 h80, 
    split,
    {
      intro h3,
      rw le_definition at h3,
      cases h3 with x h4,
      cases h4 with y h5,
      intros b h6,
      rcases h5 with ⟨ h7, h8, h9, h10⟩, 
      have h11: similar M b y:= finitecardinals2 M b y μ h2 h6 h8,
      rw (similar_symmetric M b y) at h11,
      unfold similar at h11,
      cases h11 with f h12,
      have h12copy:= h12,
      set a:= image M f x with h51,
      have h50: Rel f:= similarity_implies_Rel M f y b h12,
      unfold similarity at h12,
      cases h12 with h13 h14,
      unfold oneone at h13,
      cases h13 with h15 h16, 
      have h14: image M f x ⊆ b:= image_subset M f y b x h15 h9,
      rw← h51 at h14,   -- a ⊆ b,  line 469
      have h20:= similarity_subset M f x y b h12copy h9,
      rw← h51 at h20,
      have h21: similar M x a:=
        begin
          unfold similar,
          use f,
          exact h20, 
        end,
      have h22: a ∈ κ := finitecardinals0 M κ x a h1 h7 h21,  --line 469 
      have h23:= separable_similarity M f x y b a h12copy h9 h51 h10, 
      use a,
      exact ⟨ h22, h14, h23⟩,
    },
    {   -- right to left, line 472
      cases h80 with b h81,
      intro h3,
      specialize h3 b,
      have h4:= h3 h81, 
      rw le_definition, 
      cases h4 with a h5,
      use a, use b,
      rcases h5 with ⟨ h6,h7,h8⟩, 
      split,
      {
        exact h6,
      },
      {
        split,
        {
          exact h81,
        },
        {
          exact ⟨ h7, h8⟩, 
        }
      }
    }
  end

lemma successor_inhabited: ∀(κ :M), κ ∈ 𝔽 → (∃ w, w ∈ 𝕊 κ ) → ∃ w, w ∈ κ :=
  assume κ,
  begin
    intros h1 h2, 
    cases h2 with w h3,
    rw (successor_members M) at h3,
    cases h3 with x h4, 
    cases h4 with a h5,
    rcases h5 with ⟨ h6,h7,h8⟩,
    use x,
    exact h6, 
  end

lemma in_successor: ∀(κ x c:M), κ ∈ 𝔽 → x ∈ κ → ¬ c ∈ x → (x ∪ single c) ∈ 𝕊 κ :=
  assume κ x c,
  begin
    intros h1 h2 h3,
    rw successor_members,
    use x, use c, 
    exact ⟨ h2, h3, (refl (x ∪ single c))⟩,
  end  

lemma not_in_implies_not_in_subset: ∀ (c x y:M), ¬ (c ∈ y) → x ⊆ y → ¬ c ∈ x:=
  assume c x y,
  begin
    intros h1 h2,
    rw subset_definition at h2,
    specialize h2 c,
    intro h3,
    have h4:= h2 h3,
    contradiction, 
  end 

lemma cardinalpredecessor: ∀ (κ x c:M), κ ∈ 𝔽 → x ∈ 𝕊 κ → c ∈ x → x - (single c) ∈ κ :=
  assume κ x c,
  begin
    intros h1 h2 h3,
    have h2copy := h2, 
    rw (successor_members M) at h2,
    cases h2 with z h4,
    cases h4 with a h5,
    rcases h5 with ⟨ h6, h7, h8⟩,
    have h9:= addsubtract M z a h7,
    have h10: similar M (z ∪ single a)(z ∪ single a):= similar_reflexive M (z ∪ single a),
    rw h8 at h3,
    rw binary_union_axiom at h3,
    have h20: ∃ u, u ∈ 𝕊 κ :=
      begin 
        use x, 
        exact h2copy, 
      end, 
    have h13:x ∈ FINITE M:= finitecardinals1 M (𝕊 κ) x (successorF M κ h1 h20) h2copy,
    have h14:x ∈ DECIDABLE M:=  finitedecidable M x h13,
    have h15: z⊆ x:=
      begin
        rw subset_definition,
        intro w,
        intro h20, 
        rw full_extensionality at h8,
        specialize h8 w,
        have h21:= adjoin_member2 M w a z h20,
        rw← h8 at h21,
        exact h21,
      end, 
    have h16:= adjoin_member M a z, 
    rw← h8 at h16, 
    cases h3 with h11 h12,
    {
      have h21: ¬ a = c:=
        begin
          intro h22,
          rw h22 at *,
          contradiction,
        end,
      have h17: similar M z ((z-(single c) ∪ (single a))):=
         swap_similarity M x z c a h14 h15  h7 h11 h16, 
      have h18:= finitecardinals0 M κ z (z - single c ∪ single a) h1 h6 h17,
      have h19: (z- single c ∪ single a) = (z ∪ single a) - single c:=
        begin
          rewrite full_extensionality,
          intro u, 
          rw binary_union_axiom,
          rw (minus_members M),
          rw (minus_members M),
          rw binary_union_axiom,
          repeat { rw (singleton1 M)},
          split,
          {
            intro h22,
            cases h22 with h23 h24,
            {
              cases h23 with h25 h26,
              exact ⟨ or.inl h25, h26⟩,
            },
            {
              rw h24 at *,
              exact ⟨ or.inr (refl a), h21⟩,
            }
          },
          {
            intro h22,
            cases h22 with h24 h25,
            cases h24 with h26 h27,
            {
              left,
              exact ⟨ h26, h25⟩,
            },
            {
              rw h27 at *,
              right,
              exact (refl a), 
            }
          }
        end,
      rw←  h8 at h19,
      rw h19 at h18,
      exact h18, 
    },
    {
      rw (singleton1 M) at h12,
      rw h12 at *,
      have h30: z = x - (single a):=
        begin
          rw full_extensionality,
          intro u,
          rw h8,
          rw (minus_members M),
          rw binary_union_axiom,
          repeat {rw (singleton1 M)},
          split,
          {
            intro h30,
            split,
            {
              left, 
              exact h30,
            },
            {
              intro h31,
              rw h31 at *,
              contradiction, 
            }
          },
          {
            intro h30,
            cases h30 with h31 h32,
            cases h31 with h33 h34,
            {
              exact h33,
            },
            {
              rw h34,
              contradiction,
            }
          }
        end,
      rw←  h30,
      exact h6, 
    }
  end 

lemma ordersuccessor: ∀ (κ μ:M), (κ ∈ 𝔽 → μ ∈ 𝔽 → (∃ w, w ∈ 𝕊 μ ) → 
(κ ≤ μ ↔ 𝕊 κ ≤ 𝕊 μ )):=
  assume κ μ,
  begin
    intros h1 h2  h4,
    have h4copy:= h4,
    split,
    {  -- left to right, line 475
      intro h5,
      cases h4 with w h5, 
      rw (successor_members M) at h5,
      cases h5 with y h6,
      cases h6 with c h7,
      rcases h7 with ⟨ h8, h9, h10⟩,
      have h11:= le2 M κ μ h1 h2 (successor_inhabited M μ h2 h4copy),
      have h12:= h11.mp h5 y h8,
      cases h12 with x h13,    --line 476
      rcases h13 with ⟨ h14, h15, h16 ⟩,
      have h17: (y ∪ (single c)) ∈ 𝕊 μ :=   -- line 476
         in_successor M μ y c h2 h8 h9,
      have h23: ¬ c ∈ x := not_in_implies_not_in_subset M c x y h9 h15, 
      have h24: (x ∪ single c) ∈ 𝕊 κ := in_successor M κ x c h1 h14 h23,  -- line 477
      rw le_definition,
      use (x ∪ single c),
      use (y ∪ single c),
      repeat {split},
      {
        exact h24,
      },
      {
        exact h17,
      },
      {
        rw subset_definition,
        intro z,
        rw binary_union_axiom,
        rw binary_union_axiom,
        intro h25,
        cases h25 with h26 h27,
        {
          left,
          rw subset_definition at h15,
          exact (h15 z h26), 
        },
        {
          right,
          exact h27,
        }
      },
      {   -- now the goal is (24), line 484
        rw full_extensionality,
        intro u,
        have h25: y ∈ FINITE M:=  finitecardinals1 M μ  y h2 h8,
        have h26: y ∪ (single c) ∈ FINITE M:= finite_adjoin M y c ⟨ h25, h9 ⟩, 
        have h27: y ∪ (single c) ∈ DECIDABLE M:= finitedecidable M (y ∪ single c) h26,
        have h28: c ∈ y ∪ (single c):= adjoin_member M c y, 
        rw (decidable_members M) at h27,
        specialize h27 u c,
        split,
        {
          intro h29,
          have h30:= h27 ⟨ h29, h28⟩,
          cases h30 with h31 h32,
          {
            rw h31,
            rw (binary_union_axiom),
            rw (minus_members M),
            left,
            exact (adjoin_member M c x), 
          },
          {
            rw binary_union_axiom,
            rw binary_union_axiom at h29,
            rw (singleton1 M) at h29,
            rw h16 at h29,
            cases h29 with h30 h31,
            { 
              rw binary_union_axiom at h30,
              cases h30 with h32 h33,
              {
                left, 
                have h33:= adjoin_member2 M u c x h32, 
                exact h33, 
              },
              {
                right,
                rw (minus_members M),
                repeat{ rw (binary_union_axiom)},
                repeat{ rw (singleton1 M)}, 
                rw (minus_members M) at h33,
                cases h33 with h34 h35,
                split,
                {
                  left,
                  exact h34,
                },
                {
                  intro h36, 
                  cases h36 with h37 h38,
                  {
                    contradiction,
                  },
                  {
                    contradiction,
                  }
                }
              }
            },
            { 
              contradiction, 
            }
          }
        },
        {  -- right to left of (24), line 491
           intro h28,
           rw binary_union_axiom at h28,
           cases h28 with h29 h30,
           {
             rw binary_union_axiom at h29,
             cases h29 with h31 h32,
             {
               rw subset_definition at h15,
               have h20:= h15 u h31,
               exact (adjoin_member2 M u c y h20),
             },
             {
               rw binary_union_axiom,
               right,
               exact h32,
             }
           },
           {
             rw (minus_members M) at h30,
             cases h30 with h33 h34,
             exact h33, 
           }
        }
      }
    },
    {   -- right-to-left direction of lemma 31
      intro h5,
      rw le_definition at h5,
      cases h5 with x h6,
      cases h6 with y h7,
      rcases h7 with ⟨ h8, h9, h10, h11⟩,
      have h60: 𝕊 μ  ∈ 𝔽 := successorF M μ  h2 h4,
      have h61: y ∈ FINITE M:= 
        finitecardinals1 M (𝕊 μ ) y h60 h9,
      have h62: y ∈ DECIDABLE M:= finitedecidable M y h61, 
      have h63: ∀ (u v:M),   u ∈ y → v ∈ y → u=v ∨ ¬ (u = v) :=
         begin
           rw (decidable_members M) at h62, 
           exact λ (u v hu hv),( (h62 u v ⟨ hu, hv⟩ )), 
         end,
      have h12:= lemma25b M κ x h1 h8,
      cases h12 with c h13, 
      have h86: c ∈ y:= 
        begin
          rw subset_definition at h10,
          exact h10 c h13, 
        end,
      have h17:= cardinalpredecessor M κ x c h1 h8 h13, 
      have h18:= cardinalpredecessor M μ y c h2 h9 h86, 
      have h63copy := h63,
      specialize h63copy c, 
      have h64: ∀ (u : M), u ∈ y → c = u ∨ ¬c = u := λ  (u:M), (h63copy u  h86),  -- formula (28) of the paper
      have h65: ∀ (u: M), u ∈ y → u ∈ x ∨ ¬ u ∈ x:=  -- formula (29) of the paper
        assume u,
        begin
          rw full_extensionality at h11,
          specialize h11 u,
          intro h66,
          rw h11 at h66,
          rw binary_union_axiom at h66,
          cases h66 with h67 h68,
          {
            left,
            exact h67,
          },
          {
            right,
            rw (minus_members M) at h68,
            exact h68.right, 
          }
        end,
      have h66: ∀ (u:M), u ∈ y → u ∈ (x - (single c)) ∨ ¬ u ∈ (x - (single c)):=
        assume u,
        begin
          intro h67,
          have h68: c = u ∨ ¬ c = u:= h64 u h67, 
          cases h68 with h69 h70,
          {
            rw← h69 at *,
            right,
            intro h71,
            rw (minus_members M) at h71,
            rw (singleton1 M) at h71,
            cases h71 with h80 h81,
            contradiction, 
          },
          {
            have h72:= h65 u h67,
            cases h72 with h73 h74,
            {
              left,
              rw (minus_members M),
              rw (singleton1 M),
              split,
              {
                exact h73,
              },
              {
                rw sym, 
                exact h70,
              }
            },
            {
              right,
              rw (minus_members M),
              rw (singleton1 M),
              intro h75,
              cases h75 with h76 h77,
              contradiction, 
            }
          }
        end, 
      have h29: y - (single c) = (((y - (single c))- (x- (single c))) ∪ (x - (single c))):=
        begin
          rw full_extensionality,
          intro z,
          split,
          {
            intro h80,
            rw (minus_members M) at h80,
            cases h80 with h81 h82,
            have h83:= h66 z h81,
            cases h83 with h84 h85,
            {
              rw binary_union_axiom,
              right,
              exact h84,
            },
            {
              rw binary_union_axiom,
              left,
              repeat { rw (minus_members M)} ,
              rw (minus_members M) at h85,
              split,
              {
                split,
                {
                  exact h81,
                },
                {
                  exact h82,
                }
              },
              {
                exact h85, 
              }
            }
          },
          {
            intro h90,
            rw binary_union_axiom at h90,
            rw (minus_members M) at h90,
            rw and_or_distrib_right at h90,
            cases h90 with h91 h92,
            cases h91 with h93 h94,
            {
              exact h93,
            },
            {  
              rw (minus_members M), 
              rw (minus_members M) at h94,
              rw (singleton1 M) at h94,
              rw (singleton1 M),
              cases h94 with h95 h96,
              split,
              {
                rw subset_definition at h10,
                exact h10 z h95, 
              },
              {
                exact h96, 
              }
            }
          }
        end,
      rw le_definition,
      use x-(single c), 
      use y-(single c),
      repeat { split},
      {
        exact h17,
      },
      {
        exact h18, 
      },
      {
        rw subset_definition,
        intro z,
        repeat { rw (minus_members M)},
        repeat { rw (singleton1 M)},
        intro h30,
        cases h30 with h31 h32,
        rw subset_definition at h10,
        exact ⟨ h10 z h31, h32⟩,  
      },
      {
        rw (union_commutative M) at h29, 
        exact h29, 
      }     
    }
  end

lemma empty_is_not_inhabited: ∀(x:M), x = Λ ↔ ¬ ∃(u:M), u ∈ x:=
    assume x,
    begin
      split,
      {
        intros h1 h2,
        cases h2 with u h3,
        rw  h1 at h3, 
        exact emptyset_axiom u h3, 
      },
      {
        intro h,
        rw not_exists at h, 
        rw full_extensionality,
        intro u,
        split,
        {
          intro h3,
          specialize h u,
          contradiction, 
        },
        {
          intro h3,
          have h4:= emptyset_axiom u,
          contradiction, 
        }
      }
    end 

lemma nonempty_is_notnot_inhabited: ∀(z:M), ¬ z = Λ ↔ ¬¬ ∃ (u:M), u ∈ z:=
  assume z,
  begin
    have h10: z = Λ ↔ ¬ ∃ (u:M), u ∈ z:=
      begin
        split,
        {
          intro h11,
          rw full_extensionality at h11,
          intro h12,
          cases h12 with t h13,
          specialize h11 t,
          rw h11 at h13,
          have h14:= emptyset_axiom t,
          contradiction,
        },
        {
          intro h3,
          rw full_extensionality,
          intro t,
          split,
          {
            intro h4,
            have h5:∃ (u:M), u ∈ z:= ⟨ t,h4⟩, 
            contradiction,
          },
          { 
            intro h4,
            have h5:=emptyset_axiom t,
            contradiction, 
          }
        }
      end,
    cases h10 with h11 h12,
    split,
    {
      intro h13,
      intro h14,
      have h15:= h12 h14,
      contradiction,
    },
    {
      intro h13,
      intro h14,
      have h15:= h11 h14,
      contradiction, 
    } 
  end

lemma successoroneone: ∀ (κ μ:M), κ ∈ 𝔽 → μ ∈ 𝔽 → (∃ u, u ∈ 𝕊 κ ) → (∃ u, u ∈ 𝕊 μ ) → 
(κ = μ ↔ 𝕊 κ = 𝕊 μ) :=
  assume κ μ,
  begin
    intros h1 h2 h3 h4, 
    cases h3 with y h5,
    have h5copy := h5, 
    rw successor_members M at h5,
    cases h5 with x h6,
    cases h6 with a h7,
    split,
    {
      intro h8,
      rw h8,
    },
    {
      intro h9,
      rw full_extensionality M at h9,
      cases h7 with h10 h11,
      specialize h9 y,
      have h12: y ∈ 𝕊 μ := h9.mp h5copy,   --line 519
      have h13: a ∈ y:=
        begin
          rw h11.right, 
          exact (adjoin_member M a x), 
        end,
      have h14: y - single a ∈ μ := cardinalpredecessor M μ  y a h2 h12 h13, 
      rw h11.right at h14,  --line 520
      have h15:= successorF M μ h2 h4, 
      have h16:= finitecardinals1 M (𝕊 μ) y h15 h12,
      have h17:= finitedecidable M y h16,
      have h18: y - (single a) = x:=
        begin
          rw full_extensionality M,
          intro u,
          rw decidable_members at h17,
          specialize h17 u a, 
          split,
          {
            intro h18,
            rw minus_members M at h18,
            rw singleton1 at h18,
            cases h18 with h19 h20,
            have h21:= h17 ⟨ h19, h13 ⟩, 
            rw h11.right at h19,
            rw binary_union_axiom at h19,
            cases h19 with h20 h21,
            {
              exact h20,
            },
            {
              rw singleton1 at h21,
              contradiction, 
            }
          },
          {
            rw minus_members,
            intro h22,
            rw singleton1,
            split,
            {
              rw h11.right,
              exact adjoin_member2 M u a x h22, 
            },
            {
              intro h23,
              rw h23 at *,
              cases h11 with h24 h25,
              contradiction, 
            }
          }
        end,
      rw h11.right at h18,
      rw h18 at h14,
      have h30: x ∈ κ ∩ μ:= (intersection_axiom κ μ x).mpr ⟨ h10, h14⟩, 
      exact( cardinalsdisjoint M κ μ x h1 h2 h30 ),
    }
  end
  
lemma strictordersuccessor: ∀ (κ μ:M), (κ ∈ 𝔽 → μ ∈ 𝔽 → (∃ w, w ∈ 𝕊 κ )→ (∃ w, w ∈ 𝕊 μ ) → 
(κ < μ ↔ 𝕊 κ < 𝕊 μ )):=
  assume κ μ,
  begin
    intros h h2 h3 h4,
    have h5:= ordersuccessor M κ μ h h2  h4,
    split,
    {
      intro h6, 
      cases h5 with h7 h8,
      have h9: κ ≤ μ:= 
        begin
          rw lessthan_definition at h6,
          exact h6.left, 
        end,
      have h10:= h7 h9,
      rw lessthan_definition,
      split,
      {
        exact h10,
      },
      {
        intro h11,
        have h12:= successoroneone M κ μ h h2 h3 h4,
        rw← h12 at h11,
        rw lessthan_definition at h6,
        cases h6 with h13 h14,
        contradiction, 
      }
    },
    {
      intro h6,
      rw lessthan_definition,
      rw lessthan_definition at h6,
      rw← h5 at h6,
      cases h6 with h7 h8,
      split,
      {
        exact h7,
      },
      {
        intro h9,
        rw h9 at *,
        contradiction, 
      }
    }
  end 

lemma difference_nonempty: ∀ (x y:M), (x ⊆ y →   --Lemma 37 in the paper 
y = (x ∪ (y-x)) → (y - x = Λ ↔ y = x)):=
    assume x y,
    begin
      intro h,
      rw subset_definition at h,
      intro h3,
      split,
      { 
        intro h2, 
        rw (full_extensionality M),  
        intro u,
        split,
        {
          intro h4,
          rw full_extensionality at h2,
          specialize h2 u,
          rw minus_members at h2,
          have h5: u ∈ x ∨ ¬ u ∈ x:=
            begin
              rw full_extensionality at h3,
              specialize h3 u, 
              rw binary_union_axiom  at h3,
              cases h3 with h6 h8, 
              {
                have h9:= h6 h4,
                cases h9 with h10 h11,
                {
                  exact or.inl h10, 
                },
                {
                  right,
                  rw minus_members at h11,
                  exact h11.right, 
                }
              },
            end,
          cases h5 with h6 h7,
          { 
            exact h6,
          },
          {
            have h8:= h2.mp ⟨ h4, h7⟩,
            have h9:= emptyset_axiom u,
            contradiction, 
          }
        },
        {
          specialize h u,
          exact h, 
        }
      },
      {
        intro h4, 
        rw h4 at *,
        rw full_extensionality,
        intro u,
        rw minus_members M,
        split,
        {
          intro h6,
          cases h6 with h7 h8,
          contradiction,
        },
        {
          intro h6,
          have h7:= emptyset_axiom u,
          contradiction, 
        }
      }
    end

lemma successorstrict: ∀ (κ μ:M), κ ∈ 𝔽 → μ ∈ 𝔽 → (∃ (u:M), u ∈ 𝕊 κ ) → 
  (∃(u:M), u ∈ 𝕊 μ ) → (κ < μ ↔ 𝕊 κ < 𝕊 μ ):=
    assume κ μ,
    begin
      intros h1 h2 h3 h4,
      split,
      {
        intro h5,
        rw lessthan_definition at h5,
        cases h5 with h6 h7,
        have h8:𝕊 κ ≤ 𝕊 μ := (ordersuccessor M κ μ h1 h2 h4).mp h6, 
        rw lessthan_definition,
        split,
        {
          exact h8,
        },
        {
          intro h9,
          have h4copy:= h4,
          cases h4copy with p h10,
          have h10copy := h10, 
          rw successor_members at h10, 
          cases h10 with y h11,
          cases h11 with c h12,
          rcases h12 with ⟨ h13, h14, h15 ⟩, 
          rw h15 at h10copy,
          have h16:= h10copy,
          rw← h9 at h10copy,
          have h17: y ∈ FINITE M:= finitecardinals1 M μ y h2 h13,  --line 521
          have h18: (exists u, u ∈ μ ):= successor_inhabited M μ h2 h4, 
          have h19:= (le2 M κ μ h1 h2 h18).mp h6 y h13, 
          cases h19 with x h20, 
          rcases h20 with ⟨ h21, h22, h23⟩,   -- line 521 
          have h117: x ∈ FINITE M:= finitecardinals1 M κ x h1 h21,  --line 521
          have h24: ¬ x = y :=   -- line 522
            begin
              intro h25,
              rw h25 at *,
              have h30:y ∈ κ ∩ μ:= (intersection_axiom κ μ y).mpr ⟨ h21, h13⟩,  
              have h26: κ = μ:= cardinalsdisjoint M κ μ y h1 h2 h30, 
              contradiction, 
            end, 
          have h25: y-x  ∈ FINITE M:= finitedif M y x h17 h117 h22,  --line 522
          have h26: ¬ (y-x = Λ ):=
            begin
              have h27:= difference_nonempty M x y h22 h23, 
              intro h,
              rw h27 at h, 
              rw sym at h,
              contradiction, 
            end,
          have h28:= empty_or_inhabited M (y-x) h25,
          cases h28 with h29 h30,
          { 
            contradiction, 
          },
          {
            cases h30 with b h31,
            rw minus_members at h31,
            cases h31 with h32 h33,
            have h34: (x ∪ (single b)) ∈ 𝕊 κ:=
              begin
                rw successor_members,
                use x, use b,
                exact ⟨ h21, h33, (refl (x ∪ single b))⟩,
              end,
              -- line 525
            have h35: 𝕊 κ ∈ 𝔽:= (successorF M κ h1 h3),
            have h36: 𝕊 μ ∈ 𝔽:= (successorF M μ h2 h4), 
            have h37: (x ∪ (single b)) ∈ FINITE M:= finitecardinals1 M (𝕊 κ ) (x ∪ (single b)) h35 h34,
            have h38: (y ∪ (single c)) ∈ FINITE M:= finitecardinals1 M (𝕊 μ )(y ∪ (single c)) h36 h16, --line 526
            have h39: (x ∪ (single b)) ∈ DECIDABLE M:= finitedecidable M (x ∪ (single b)) h37,
            have h40: (y ∪ (single c)) ∈ DECIDABLE M:= finitedecidable M (y ∪ (single c)) h38,
            rw decidable_members at h40, 

            have h41: y = (y ∪ (single c)) - (single c):=
              begin
                rw full_extensionality,
                intro u,
                split,
                {
                  intro h42, 
                  specialize h40 u c,
                  have h43:= adjoin_member2 M u c y h42,
                  have h44:= adjoin_member M c y, 
                  have h45:= h40 ⟨ h43, h44⟩,
                  cases h45 with h46 h47,
                  {
                    rw h46, 
                    rw h46 at *,
                    contradiction, 
                  },
                  {
                    rw minus_members,
                    rw binary_union_axiom,
                    repeat { rw (singleton1 M)},
                    exact ⟨ or.inl h42 , h47⟩, 
                  },
                },
                {
                  rw minus_members,
                  intro h41,
                  cases h41 with h42 h43,
                  rw binary_union_axiom at h42,
                  cases h42 with h43 h44,
                  {
                    exact h43,
                  },
                  {
                    contradiction, 
                  }
                }
              end,
            -- line 527
            have h42:= cardinalpredecessor M κ (y ∪ (single c)) c h1 h10copy (adjoin_member M c y), 
            rw← h41 at h42,  -- y ∈ κ, line 528
            have h43: y ∈ κ ∩ μ := 
              begin
                rw intersection_axiom,
                exact ⟨ h42, h13⟩,
              end,
            have h44:= cardinalsdisjoint M κ μ y h1 h2 h43,
            contradiction, 
          },  
        }
      },
      {   -- right-to-left, line 532
        intro h,
        rw lessthan_definition at h,
        cases h with h5 h6,
        have h7:= ordersuccessor M κ μ h1 h2 h4,
        rw← h7 at h5,
        rw lessthan_definition,
        split,
        {
          exact h5,
        },
        {
          intro h8,
          rw h8 at *,
          contradiction, 
        }
      }
    end



lemma notlezero: ∀ μ:M, μ ∈ 𝔽 →  μ ≤  zero → μ  = zero:=
  begin
    intros μ h h4, 
    rw le_definition at h4,
    cases h4 with x h5,
    cases h5 with y h6,
    rcases h6 with ⟨ h7, h8, h9, h10⟩,
    rw zero_definition at h8,
    rw (singleton1 M) at h8,
    rw h8 at *,
    rw subset_of_empty at h9,
    rw h9 at *,
    rw zero_definition, 
    rw full_extensionality,
    intro z,
    rw (singleton1 M),
    split,
    {
      intro h11,
      have h12: Λ ∈ μ  ∩ zero:=
        begin
          rw intersection_axiom,
          rw zero_definition,
          rw singleton1 M,
          split,
          {
            exact h7,
          },
          {
            exact refl Λ,
          }
        end,
      have h13: μ = zero:= cardinalsdisjoint M μ zero Λ h (zeroF M) h12, 
      rw full_extensionality at h13,
      rw h13 z at h11,
      rw zero_definition at h11,
      rw singleton1 at h11,
      exact h11,
    },
    {
      intro h12,
      rw h12 at *,
      exact h7, 
    }     
  end
      
lemma zero_or_not_zero: ∀ (κ:M), κ ∈ 𝔽 →  (κ = zero ∨ ¬ κ = zero) := 
  begin
    set W:M := 𝔽 ∩ ((𝔽 - (single zero)) ∪ (single zero)) with h,
    have base: zero ∈ W:=
      begin
        rw h,
        rw intersection_axiom,
        rw binary_union_axiom,
        split,
        {
          exact zeroF M, 
        },
        { 
          right,
          rw singleton1 M,
        }
      end,
    have step: ∀ κ:M, κ ∈ W → (∃ u:M, u ∈ 𝕊 κ) → 𝕊 κ ∈ W:=
      begin 
        intros  κ h2 h30,
        rw h at *,
        rw intersection_axiom,
        rw intersection_axiom at h2, 
        cases h2 with h3 h4,
        split,
        {
          exact successorF M κ h3 h30, 
        },
        {  
          rw binary_union_axiom, 
          left,
          rw minus_members M,
          rw singleton1 M,
          rw binary_union_axiom at h4,
          split,
          { 
            exact successorF M κ h3 h30,  
          },
          { 
            exact successor_omits_zero M κ,   
          },
        },
      end,
    intros κ h30,
    rw F_members at h30,    
    specialize h30 W,
    have h3:= h30 ⟨ base, step⟩ , 
    rw h at h3, 
    rw intersection_axiom at h3, 
    cases h3 with h4 h5,
    rw binary_union_axiom at h5, 
    cases h5 with h6 h7,
    {
      right,
      intro h8,
      rw h8 at *,
      rw minus_members at h6,
      cases h6 with h9 h10,
      rw singleton1 at h10, 
      contradiction,
    },
    {
      rw singleton1 M at h7,
      left,
      exact h7,
    } 
  end 

lemma zero_le_kappa: ∀(κ:M), κ ∈ 𝔽 → zero ≤ κ:=
  assume κ,
  begin
    intro h,
    rw le_definition,
    have h4:= cardinalsinhabited M κ h, 
    cases h4 with x h5,
    use Λ, use x,
    repeat { split},
    {
      rw zero_definition,
      rw singleton1 M,
    },
    {
      exact h5, 
    },
    {
      exact empty_always_subset M x, 
    },
    {
      rw x_minus_empty M x,
      rw empty_union_x M x,
    }
  end

lemma baseTheorem2: (zero:M) ∈ (Z2 M):=
  begin
    rw Z2_members,
    split,
    {
      exact zeroF M, 
    },
    { intros μ h2,
      have h3:  μ ≤  zero → μ  = zero:= notlezero M μ h2, 
      have h4: μ = zero ∨ ¬ μ = zero:= zero_or_not_zero M μ h2,   -- line 550 
      cases h4 with h5 h6,
      {
        rw h5 at *,
        split,
        {
          right,
          left,
          exact (refl zero), 
        },
        {
          intro h4,
          cases h4 with h5 h6,
          rw lessthan_definition zero zero at h5,
          cases h5 with h6 h7,
          contradiction, 
        }
      },
      {
        split,
        {
          left,
          rw lessthan_definition,
          split,
          {
             exact (zero_le_kappa M μ h2), 
          },
          {
            rw sym,
            exact h6, 
          }
        },
        {
          intro h8,
          cases h8 with h8 h10,
          rw lessthan_definition at h10,
          cases h10 with h11 h12,
          have h13:= notlezero M μ h2 h11,
          contradiction,
        }
      },
    }
  end

lemma zeroorsuccessor: ∀ κ:M, κ ∈ 𝔽 → κ = zero ∨ ∃ μ, (μ ∈ 𝔽 ∧ κ = 𝕊 μ ):=
  assume κ,
    begin 
      have hbase: zero ∈ Z24 M:=
        begin
          rw Z24_members M,
          split,
          {
            exact zeroF M, 
          },
          {
            left,
            exact (refl zero),
          }
        end,
      have hstep: ∀ κ:M, κ ∈ Z24 M → (∃ u, u ∈ 𝕊 κ ) → 𝕊 κ ∈ Z24 M:=
        begin
          intros κ h h2,
          rw Z24_members M  at h,
          rw Z24_members,
          cases h with h3 h4,
          have h5:= successorF M κ h3 h2,
          split,
          {
            exact h5,
          },
          {
            right,
            use κ,
            exact ⟨ h3, refl (𝕊 κ ) ⟩,
          }
      end,
    intros h,
    rw F_members at h,    
    /-
    M : Type,
    _inst_1 : Model M,
    κ : M,
    hbase : zero ∈ Z24 M,
    hstep : ∀ (κ : M), κ ∈ Z24 M → (∃ (u : M), u ∈ 𝕊 κ) → 𝕊 κ ∈ Z24 M,
    h : ∀ (w : M), (zero ∈ w ∧ ∀ (u : M), u ∈ w → (∃ (v : M), v ∈ 𝕊 u) → 𝕊 u ∈ w) → κ ∈ w
    ⊢ κ = zero ∨ ∃ (μ : M), μ ∈ 𝔽 ∧ κ = 𝕊 μ
    -/
    
    specialize h (Z24 M),
    have h3:= h ⟨ hbase, hstep⟩, 
    rw Z24_members at h3,
    cases h3 with h4 h5,
    exact h5,
  end

lemma nonzeroissuccessor: ∀ κ:M, κ ∈ 𝔽 → ¬ κ = zero → ∃ μ, (μ ∈ 𝔽 ∧ κ = 𝕊 μ ):=
  assume κ,
  begin 
    have hbase: zero ∈ Z24 M:=
      begin
        rw Z24_members M,
        split,
        {
          exact zeroF M, 
        },
        {
          left,
          exact (refl zero),
        }
      end,
    have hstep: ∀ κ:M, κ ∈ Z24 M → (∃ u, u ∈ 𝕊 κ ) → 𝕊 κ ∈ Z24 M:=
      begin
        intros κ h h2,
        rw Z24_members M  at h,
        rw Z24_members,
        cases h with h3 h4,
        have h5:= successorF M κ h3 h2,
        split,
        {
          exact h5,
        },
        {
          right,
          use κ,
          exact ⟨ h3, refl (𝕊 κ ) ⟩,
        }
      end,
    intros h h2,
    rw F_members at h,    
    specialize h (Z24 M),
    have h3:= h ⟨ hbase, hstep⟩, 
    rw (Z24_members M) at h3, 
    cases h3 with h4 h5,
    cases h5 with h6 h7,
    {
      contradiction, 
    },
    {
      cases h7 with μ h8,
      use μ, 
      exact h8, 
    },  
  end

lemma zero_lessthan_successor: ∀(κ: M), κ ∈ 𝔽 → (∃ u,(u ∈ 𝕊 κ)) →  zero < 𝕊 κ:=
  assume κ, 
  begin
    intros h h2,  
    rw lessthan_definition,
    split,
    { 
      exact (zero_le_kappa M  (𝕊  κ ) (successorF M κ h  h2)), 
    },
    {
      intro h3,
      cases h2 with u h4,
      rw←  h3 at h4,
      rw zero_definition at h4,
      rw singleton1 M at h4,
      rw full_extensionality at h3,
      specialize h3 Λ,
      rw zero_definition at h3,
      rw singleton1 at h3,
      have h5:= h3.mp (refl Λ ),
      rw successor_members at h5,
      cases h5 with x h6,
      cases h6 with a h7,
      rcases h7 with ⟨ h8, h9, h10⟩,
      rw full_extensionality at h10,
      specialize h10 a,
      have h11:= emptyset_axiom a,
      have h12:= adjoin_member M a x,
      rw← h10 at h12,
      contradiction,
    }
  end 

lemma stepTheorem2: ∀(κ:M),  κ ∈ Z2 M → (∃ u, u ∈ 𝕊 κ) → 𝕊 κ ∈ Z2 M:=
  assume κ,
  begin
    intros h2 h3,
    rw Z2_members M at *,
    cases h2 with h h5,
    split,
    {
      exact successorF M κ h h3,
    },
    {
      intros μ h6,
      have h5copy := h5, 
      specialize h5 μ,
      have h7:= h5 h6,
      have h8: ¬ μ = zero →  ∃ (ℓ:M), (ℓ ∈ 𝔽 ∧ μ = 𝕊 ℓ ):= nonzeroissuccessor M μ  h6,  
      have h9: μ = zero ∨ ¬ μ = zero:= zero_or_not_zero M μ h6,
      cases h9 with h10 h11, 
      { 
        rw h10 at *,
        split,
        {
          right,
          right,
          exact zero_lessthan_successor M κ h h3,
        },
        {
          intro h11,
          cases h11 with h12 h13,
          rw lessthan_definition at h13,
          cases h13 with h14 h15,
          have h16:= baseTheorem2 M,
          rw Z2_members at h16,
          cases h16 with h17 h18,
          have h19:= h18 (𝕊 κ ) (successorF M κ h h3),
          cases h19 with h20 h21,
          have h22: zero < 𝕊 κ  :=
            begin
              rw lessthan_definition,
              split,
              {
                exact h14, 
              },
              {
                exact h15, 
              }
            end,
          simp at h21,
          have h30:= h21 h22,
          contradiction, 
        } 
      },
      {
        have h12:= h8 h11,
        cases h12 with ℓ h13,
        cases h13 with h14 h15,
        rw h15 at *,
        have h16:= h5copy ℓ h14, 
        have h17:= cardinalsinhabited M (𝕊 ℓ ) h6, 
        have h18:= successorstrict M κ ℓ h h14 h3 h17, 
        have h19:= successorstrict M ℓ κ h14 h h17 h3,
        have h20:= successoroneone M κ ℓ h h14 h3 h17, 
        rw h18 at h16,
        rw h19 at h16,
        rw h20 at h16,
        exact h16, 
      },
    }
  end 

lemma  Theorem2helper: ∀ (κ:M), κ ∈ 𝔽 → κ ∈ 𝔽 ∧ ∀ (μ:M),   μ ∈ 𝔽 → 
((κ < μ ∨ κ = μ ∨ μ < κ) ∧ (¬ ( κ < μ ∧ μ < κ ))):=
  assume κ, 
  begin
    intro h,
    have hcopy := h, 
    rw F_members at h,
    specialize h (Z2 M),
    have h3:= h ⟨ (baseTheorem2 M), (stepTheorem2 M )  ⟩ , 
    rw (Z2_members M) at h3,
    exact h3, 
  end

theorem Theorem2: ∀ (κ μ : M), κ ∈ 𝔽 → μ ∈ 𝔽 → 
((κ < μ ∨ κ = μ ∨ μ < κ) ∧ (¬ ( κ < μ ∧ μ < κ ))):=
assume κ μ,
begin
  intros h2 h3,
  exact ((Theorem2helper M κ h2).right μ h3), 
end 

lemma lessthansuccessor: ∀ (κ:M), κ ∈ 𝔽 → (∃ (u:M), u ∈ 𝕊 κ ) → κ < 𝕊 κ :=
  assume κ, 
  begin
    intros h h2,
    have h2copy:= h2,
    cases h2 with x h3,
    have h3copy:= h3,
    rw successor_members M at h3, 
    cases h3 with y h4,
    cases h4 with c h5,
    rcases h5 with ⟨ h6,h7,h8⟩,
    have h9: x ∈ FINITE M:= finitecardinals1 M  (𝕊 κ) x (successorF M κ h h2copy) h3copy, 
    have h10: x ∈ DECIDABLE M:= finitedecidable M x h9,  --line 576
    have h11: x-y = single c:= 
      begin
        rw h8,
        rw full_extensionality,
        intro u,
        rw minus_members,
        rw binary_union_axiom,
        rw singleton1,
        split,
        {
          intro h11,
          cases h11 with h12 h13,
          cases h12 with h14 h15,
          {
            contradiction,
          },
          {
            exact h15, 
          }
        },
        {
          intro h16,
          rw h16 at *,
          exact ⟨ or.inr (refl c), h7 ⟩,
        }
      end,
    have h20: c ∈ x := 
      begin
        rw h8,
        exact adjoin_member M c y,
      end,
    have h16: x = (y ∪ (x-y)):=
      begin
        rw full_extensionality,
        intro u,
        rw binary_union_axiom,
        rw minus_members,
        have h17:= (decidable_members M x).mp h10 u c,
        split,
        {
          intro h18,
          have h19:= h17 ⟨ h18, h20 ⟩, 
          cases h19 with h20 h21,
          {
            rw h20 at *,
            right,
            exact ⟨ h18, h7 ⟩,
          },
          {
            left,
            rw h8 at h18,
            rw binary_union_axiom at h18,
            rw singleton1 at h18,
            cases h18 with h21 h22,
            { 
              exact h21,
            },
            {
              contradiction, 
            },
          }
        },
        {
          intro h30,
          cases h30 with h31 h32,
          {
            rw h8,
            rw binary_union_axiom,
            exact (or.inl h31),
          },
          {
            exact h32.left, 
          }
        }
      end,
    have h50:= lessthan2 M κ (𝕊 κ) h (successorF M κ h h2copy), 
    rw h50,
    use y, use x,
    have h41: y ⊆ x:=
      begin
        rw h8,
        exact (subset_union2 M y (single c)),
      end,
    have h42: ¬ y=x:=
      begin
        intro h43,
        rw full_extensionality at h43,
        specialize h43 c,
        rw h8 at h43,
        rw binary_union_axiom at h43,
        rw singleton1 at h43,
        simp at h43, 
        contradiction, 
      end, 
    have h45: y ⊂ x:=
      begin
        rw proper_subset_definition, 
        exact ⟨ h41, h42⟩, 
      end,
    exact ⟨ h6, h3copy, h45, h16⟩, 
  end



lemma le_transitive2: ∀ (κ ℓ μ:M), κ ∈ 𝔽 → ℓ ∈ 𝔽 → μ ∈ 𝔽 → κ < ℓ → ℓ ≤ μ → κ < μ :=
  assume κ ℓ μ,
  begin
    intros h1 h2 h3 h4 h5,
    have h6: κ ≤ μ :=
      begin
        rw lessthan_definition at h4, 
        cases h4 with h6 h7,
        exact le_transitive M κ μ ℓ h1 h3 h2 h6 h5,
      end,
    have h7: ¬ κ = μ :=
      begin
        intro h8,
        rw h8 at *,
        have h9:= Theorem2 M μ ℓ h3 h2,
        cases h9 with h10 h11,
        have h20:μ < ℓ → ¬ ℓ < μ:=
          begin
            intro h21,
            intro h22, 
            have h23: μ < ℓ ∧ ℓ < μ :=
              begin
                exact ⟨ h21, h22⟩, 
              end,
            contradiction, 
          end,
        have h12:= h20 h4,
        rw lessthan_definition at h12,
        have h30: ℓ ≤ μ → ℓ = μ:=
          begin
            intro h31,
            have h32: ¬ ℓ = μ:=
              begin
                intro h33,
                rw h33 at *,
                rw lessthan_definition at h4,
                cases h4 with h34 h35,
                contradiction, 
              end,
            have h33: ℓ≤ μ ∧ ¬ ℓ = μ := ⟨ h31, h32⟩, 
            contradiction, 
          end,
        have h13 := h30 h5,
        rw h13 at *, 
        simp at h11, 
        contradiction,
      end,
    rw lessthan_definition,
    exact ⟨ h6, h7⟩, 
  end

lemma le_reflexive:  ∀ (κ :M), κ ∈ 𝔽 → κ ≤ κ :=
  assume κ hk,
  begin
    have h2:= cardinalsinhabited M κ hk, 
    cases h2 with a h3,
    have h4:a = (a ∪ (a - Λ )):=
      begin
        rw x_minus_empty M a,
        rw x_union_x M, 
      end,
    rw le_definition, 
    use a, use a,
    have h5: a ⊆ a:= subset_reflexive M a,
    rw x_minus_x M,
    rw x_union_empty M a,
    simp,
    exact ⟨ h3, h5⟩, 
  end

lemma le_reflexive2:  ∀ (κ :M), κ ∈ NC M  → κ ≤ κ :=
  assume κ hk,
  begin
    have h2:= cardinalsinhabited2 M κ hk, 
    cases h2 with a h3,
    have h4:a = (a ∪ (a - Λ )):=
      begin
        rw x_minus_empty M a,
        rw x_union_x M, 
      end,
    rw le_definition, 
    use a, use a,
    have h5: a ⊆ a:= subset_reflexive M a,
    rw x_minus_x M,
    rw x_union_empty M a,
    simp,
    exact ⟨ h3, h5⟩, 
  end

lemma noinsertions: ∀ (κ μ : M), κ ∈ 𝔽 → μ ∈ 𝔽 → κ < μ → 𝕊 κ ≤ μ :=
  assume κ μ,
  begin
    intros h1 h2 h3,
    rw le_definition,
    rw lessthan_definition at h3,
    cases h3 with h4 h5,
    rw le_definition at h4,
    cases h4 with a h6,
    cases h6 with b h7,
    rcases h7 with ⟨ h8, h9, h10, h11⟩,
    have h12: b ∈ FINITE M:= finitecardinals1 M μ b h2 h9, 
    have h13: a ∈ FINITE M:= finitecardinals1 M κ a h1 h8,
    have h14: b-a ∈ FINITE M:= finitedif M b a h12 h13 h10,
    have h15:= empty_or_inhabited M (b-a) h14, 
    cases h15 with h16 h17,
    {   -- case 1, line 614
      have h18:b=a:=
        begin
          rw full_extensionality,
          intro t,
          rw full_extensionality at h16,
          specialize h16 t,
          rw minus_members M at h16,
          have h17:= emptyset_axiom t,
          rw← h16 at h17,  
          rw full_extensionality at h11,
          have h12:= h11 t,
          rw binary_union_axiom at h12,
          rw minus_members at h12,
          rw h12,
          split,
          { 
            intro h20,
            cases h20 with h21 h22,
            {
              exact h21,
            },
            {
              cases h22 with h23 h24,
              have h24: t∈ b ∧ ¬ t ∈ a:=
                begin
                  exact ⟨ h23, h24⟩, 
                end,
              contradiction, 
            }
          },
          { 
            intro h20,
            left,
            exact h20,   
          } 
        end,
      have h19: a ∈ κ ∩ μ:=
        begin
           rw intersection_axiom,
           rw h18 at *,
           exact ⟨ h8, h9⟩,
        end,
      have h20:= cardinalsdisjoint M κ μ a h1 h2 h19,
      contradiction,
    },
    {   --case 2, line 616
      cases h17 with c h18,
      rw minus_members M at h18,
      cases h18 with h19 h20,
      have h21: a ∪ (single c) ∈ 𝕊 κ :=
        begin
          rw successor_members,
          use a, use c,
          split,
          {
            exact h8,
          },
          {
            exact ⟨ h20, refl (a ∪ (single c))⟩, 
          } 
        end,
      have h22: a ∪ (single c) ⊆ b :=
        begin
          rw subset_definition,
          intro t,
          rw binary_union_axiom,
          rw singleton1 M,
          intro h23,
          rw subset_definition at h10,
          specialize h10 t,
          cases h23 with h50 h51,
          {
            exact h10 h50, 
          },
          {
            rw h51 at *,
            exact h19, 
          }
        end,
      have h23: b = ((a ∪ (single c))  ∪  ( b - (a ∪ (single c)))):=
        begin 
          rw full_extensionality,
          intro t,
          rw subset_definition at h10,
          specialize h10 t,
          rw binary_union_axiom,
          rw minus_members M,
          rw binary_union_axiom,
          rw singleton1 M,
          rw full_extensionality at h11,
          specialize h11 t,
          rw binary_union_axiom at h11,
          have h40: b ∈ DECIDABLE M:= finitedecidable M b h12,
          have h41: ∀(x:M), x∈ b → x = c ∨ ¬ x = c:=
            begin
              rw decidable_members M at h40,
              intro x,
              specialize h40 x c,
              intro h50,
              have h51:= h40 ⟨ h50, h19⟩, 
              exact h51,
            end,
          split,
          {
            intro h12,
            have h42:= h41 t h12,
            cases h42 with h43 h44, 
            {
              rw h43 at *,
              simp, 
            },
            { rw h11 at h12,
              cases h12 with h13 h14,
              {  
                left,
                left,
                exact h13,
              },
              {
                right,
                rw minus_members M at h14,
                cases h14 with h50 h51, 
                split,
                {
                  exact h50,
                },
                {
                  intro h52,
                  cases h52 with h53 h54,
                  {
                    contradiction,
                  },
                  {
                    contradiction, 
                  }
                }
              }
            }
          },
          {
            intro h50,
            cases h50 with h51 h52,
            {
              cases h51 with h53 h54,
              {
                exact h10 h53, 
              },
              {
                rw h54 at *,
                exact h19,
              }
            },
            {
              cases h52 with h53 h54,
              exact h53,
            }
          }
        end, 
      use a ∪ (single c),
      use b, 
      split,
      {
        exact h21,
      },
      {
        split,
        {
          exact h9,
        },
        {
          exact ⟨ h22, h23⟩, 
        }
      }
    } 
  end

lemma letolessthan: ∀ (κ μ :M), κ ∈ 𝔽 → μ ∈ 𝔽 → (κ ≤ μ ↔ κ < μ ∨ κ = μ ):=
  assume κ μ,
  begin
    intros h2 h3,
    split,
    {
      intro h4, 
      rw le_definition at h4, 
      cases h4 with a h5,
      cases h5 with b h6,
      rcases h6 with ⟨ h7, h8, h9, h10⟩,
      have h11:= finitecardinals1 M κ a h2 h7,
      have h12:= finitecardinals1 M μ b h3 h8,
      have h13:= finitedif M b a h12 h11 h9,
      have h14:= empty_or_inhabited M (b-a) h13,
      cases h14 with h15 h16,
      {
        have h17:b=a:=
          begin
            rw full_extensionality,
            intro t,
            split,
            {
              intro h16,
              rw full_extensionality at h10,
              specialize h10 t, 
              rw binary_union_axiom at h10,
              rw h15 at h10, 
              have h17:= emptyset_axiom t,
              have h18:= h10.mp h16,
              cases h18 with h19 h20,
              {
                exact h19,
              },
              {
                contradiction,
              }
            },
            {
              intro h16, 
              exact  member_subset M a b t h9 h16,
            } 
          end,
        have h18: a ∈ κ ∩ μ:=
          begin
            rw intersection_axiom,
            rw h17 at *,
            exact ⟨ h7, h8⟩, 
          end,
        have h19:= cardinalsdisjoint M κ μ a h2 h3 h18,
        right,
        exact h19, 
      },
      {
        cases h16 with u h17,
        have h18: κ < μ :=
          begin
            have h19:= (lessthan2 M κ μ h2 h3).mpr,
            apply h19,
            use a, use b,
            repeat {split}, 
            {
              exact h7,
            },
            {
              exact h8, 
            },
            {
              rw proper_subset_definition, 
              split,
              {
                exact h9,
              },
              { 
                intro h20,
                rw h20 at *,
                rw x_minus_x M at h17,
                exact emptyset_axiom u h17,
              },
            },
            {
              exact h10, 
            }        
          end,
        left,
        exact h18, 
      }
    },
    {
      rw lessthan_definition,
      intro h4,
      cases h4 with h5 h6,
      {
        exact h5.left, 
      },
      {
        rw h6 at *,
        exact le_reflexive M μ h3,
      }
    }
  end

lemma finitetrichotomy2: ∀ (κ μ :M), κ ∈ 𝔽 → μ ∈ 𝔽 → κ ≤ μ → μ ≤ κ → κ = μ :=
  assume κ μ,
  begin 
    intros h h2,
    rw letolessthan M κ μ h h2,
    rw letolessthan M μ κ h2 h, 
    have h3:= Theorem2 M κ μ h h2,
    cases h3 with h4 h5,
    intros h6 h7,
    cases h6 with h8 h9,
    {
      cases h7 with h10 h11,
      {
        have h12:= h5 ⟨ h8, h10⟩, 
        contradiction,
      },
      {
        rw h11 at *,
      }
    },
    {
      cases h7 with h10 h11,
      {
        rw h9 at *, 
      },
      {
        rw sym,
        exact h11, 
      }
    }
  end

lemma le_transitive3: ∀ (κ ℓ μ:M), κ ∈ 𝔽 → ℓ ∈ 𝔽 → μ ∈ 𝔽 → κ ≤  ℓ → ℓ < μ → κ < μ :=
  assume κ ℓ μ,
  begin
    intros h1 h2 h3 h4 h5,
    have h6: κ ≤ μ :=
      begin 
        rw lessthan_definition at h5, 
        cases h5 with h6 h7,
        exact le_transitive M κ μ ℓ h1 h3 h2 h4 h6,
      end,
    have h7: ¬ κ = μ :=
      begin
        intro h8,
        rw h8 at *,
        have h9:= Theorem2 M μ ℓ h3 h2,
        cases h9 with h10 h11,
        push_neg at h11,
        cases h10 with h12 h13,
        {
          have h20:= h11 h12, 
          contradiction,
        },
        {
          cases h13 with h14 h15,
          {
            rw h14 at *,
            have h20:= h11 h5, 
            contradiction,
          },
          {
            rw lessthan_definition at h5,
            cases h5 with h16 h17,
            have h18:= finitetrichotomy2 M ℓ μ h2 h3 h16 h4,
            rw h18 at *,
            contradiction,       
          }
        }
      end,
    rw lessthan_definition,
    exact ⟨ h6, h7⟩, 
  end

lemma lessthan_transitive: ∀ (x y z:M), x ∈ 𝔽 → y ∈ 𝔽 → z ∈ 𝔽 → x < y → y < z → x < z:=
   assume x y z,
   begin
     intros h1 h2 h3 h4 h5,
     rw lessthan_definition at h4,
     cases h4 with h6 h7,
     exact le_transitive3 M x y z h1 h2 h3 h6 h5, 
   end 
 
lemma lessthansuccessor2: ∀ (m n:M), m ∈ 𝔽 → n ∈ 𝔽 →  m ≤ 𝕊 n →  m ≤ n ∨ m = 𝕊 n:=
  assume m n,
  begin
    intros hm hn,
    intro h2,
    have h2copy:= h2,
    rw le_definition at h2copy,
    cases h2copy with a h3,
    cases h3 with b h4,
    rcases h4 with ⟨ h5, h6, h7, h8⟩,
    have h9: 𝕊 n ∈ 𝔽 := successorF M n hn ⟨ b,h6⟩ , 
    rw letolessthan M m (𝕊 n) hm h9 at h2, 
    cases h2 with h10 h11,
    {
      have h12:= noinsertions M m (𝕊 n) hm h9 h10,
      have h12copy:= h12,
      rw le_definition at h12copy,
      cases h12copy with p h20,
      cases h20 with q h21,
      rcases h21 with ⟨ h22, h23,h24, h25⟩, 
      rw← ordersuccessor M m n hm hn  ⟨ q,h23⟩ at h12,
      left,
      exact h12,
    },
    {
      right,
      exact h11,
    }
  end

lemma lessthansuccessor2b: ∀ (m n:M), m ∈ 𝔽 → n ∈ 𝔽 →  (∃(u:M), u ∈ 𝕊 n)→( m ≤ 𝕊 n ↔   m ≤ n ∨ m = 𝕊 n):=
  assume m n,
  begin
    intros hm hn h3,
    split,
    {
      exact lessthansuccessor2 M m n hm hn, 
    },
    {
      intro h4,
      cases h4 with h5 h6,
      {
        have h7:= lessthansuccessor M n hn h3,
        have h8:= le_transitive3 M m n (𝕊 n) hm hn (successorF M n hn h3) h5 h7,
        rw lessthan_definition at h8,
        exact h8.left, 
      },
      {
        rw h6,
        exact le_reflexive M (𝕊 n) (successorF M n hn h3),
      }
    }
  end

lemma FregeNdecidable: (𝔽:M) ∈ DECIDABLE M:=
  begin
    rw decidable_members,
    intros κ μ  h,
    cases h with h1 h2, 
    have h3:= Theorem2 M κ μ h1 h2,
    cases h3 with h4 h5,
    cases h4 with h6 h7,
    {
      right,
      intro h8,
      rw h8 at *,
      simp at h5,
      contradiction,
    },
    {
     cases h7 with h8 h9,
     {
       left,
       exact h8,
     },
     {
       right,
       intro h10,
       rw h10 at *,
       simp at h5,
       contradiction,
     }  
    }
  end

lemma finitetrichotomy: ∀ (κ:M), κ ∈ 𝔽 → ∀ (μ:M), μ ∈ 𝔽 → κ < μ ∨ κ = μ ∨ μ < κ:=
  begin
    intros κ hkappa μ hmu,
    have h3:= Theorem2 M κ μ hkappa hmu,
    exact h3.left,
  end 

#axioms_all   -- This file is clean now 
