 -- Section 4 of the paper, Frege cardinals
import inf3       
variables (M:Type) [Model M] (a b x y z u v w X R W: M)

open Model 

lemma zeroF: (zero:M) ∈ 𝔽:=
  begin
    rw F_members, 
    intros w h, 
    exact h.left,
  end

lemma zero_finite: (zero:M) ∈ FINITE M:=
  begin
    rw zero_definition,
    rw (finite_members M),
    intro w,
    intro h,
    cases h with h2 h3,
    specialize h3 Λ  Λ,
    rw empty_union_x at h3, 
    have h4: ¬ (Λ:M) ∈ (Λ:M) := emptyset_axiom (Λ:M), 
    exact h3 ⟨ h4, h2⟩, 
  end

lemma empty_finite: (Λ :M) ∈ FINITE M:=
  begin
    rw (finite_members M),
    intro w,
    intro h,
    cases h with h3 h4,
    exact h3, 
  end

lemma successorF: ∀(u:M), u ∈ 𝔽 → (∃ x,(x ∈ 𝕊 u)) → 𝕊 u ∈ 𝔽 :=
  assume u,
  begin
    repeat{ rw F_members},
    intros h h1,
    intro w,
    specialize h w,
    intro h2,
    have h3:= h h2,
    cases h2 with h4 h5,
    have h6:= h5 u h3 h1,
    exact h6, 
  end
    
lemma base17: zero ∈ Z17 M:=
  begin
    rw Z16_members,
    split,
    {  
      exact (zeroF M),    
    },
    {
      intros y h3,
      rw zero_definition at h3,
      rw (singleton1 M) at h3,
      rw h3,
      exact empty_finite M,
    }
  end 

lemma step17: ∀ (u:M), u ∈ Z17 M → (∃ x,x ∈ 𝕊 u) → 𝕊 u ∈ Z17 M:=
  assume u,
  begin
    repeat {rw Z16_members},
    intros h h1,
    cases h with h2 h3,
    split,
    { 
        exact (successorF M u h2 h1),
    },
    {
        intros y h4,
        rw (successor_members M) at h4,
        cases h4 with x h5,
        cases h5 with a h6,
        cases h6 with h7 h8,
        rw (F_members) at h2,
        have h9:= h3 x h7,
        have h10:= finite_adjoin M x a,
        have h11:= h10 (and.intro h9 h8.left), 
        rw h8.right,
        exact h11,
    },
  end

lemma finitecardinals1: ∀(κ x:M), (κ ∈ 𝔽 → x ∈ κ → x ∈ FINITE M)  :=   
  assume κ x, 
  begin  
    intro h, 
    rw F_members at h,    
    specialize h (Z17 M),
    have h3:= h (and.intro (base17 M) (step17 M)), 
    rw (Z16_members M) at h3, 
    cases h3 with h5 h6,
    specialize h6 x, 
    exact h6,
  end

lemma base18: zero ∈ Z18 M:= 
  begin
    rw (Z18_members M),
    split,
    {
         exact (zeroF M),
    },
    { 
      use Λ,
      rw zero_definition,
      rw (singleton1 M),
    }
  end

lemma step18: ∀(κ:M), κ ∈ Z18 M → (∃ u, u ∈ 𝕊 κ ) → 𝕊 κ ∈ Z18 M:=
  assume κ, 
  begin 
    repeat{ rw (Z18_members M)}, 
    intros h h10, 
    cases h with h2 h3,

    split,
    { 
      exact (successorF M κ h2 h10), 
    },
    {
      cases h3 with u h4, 
      exact h10, 
    },
  end 


lemma cardinalsinhabited: ∀ (κ:M), κ ∈ 𝔽 → ∃ x, x ∈ κ :=
  assume κ, 
  begin 
    intro h, 
    rw F_members at h, 
    specialize h (Z18 M),
    have h3:= h (and.intro (base18 M) (step18 M)), 
    rw (Z18_members M) at h3, 
    cases h3 with h5 h6, 
    exact h6, 
  end

lemma xinNcx: ∀(x:M), x ∈ Nc M x:=
  assume x,
  begin
    rw (Nc_members M),
    exact similar_reflexive M x, 
  end

lemma cardinalsinhabited2: ∀ (κ:M), κ ∈ NC M → ∃ x, x ∈ κ :=
  begin
    intros κ h3,
    rw NC_members at h3,
    cases h3 with y h4,
    have h5:= xinNcx M y,
    rw← h4 at h5,
    use y,
    exact h5,
  end

lemma cardinals2: ∀(κ x y:M), κ ∈ NC M → x ∈ κ → y ∈ κ → similar M x y:=
  begin
    intros κ x y hk hx hy,
    rw NC_members at hk,
    cases hk with a h4,
    rw h4 at *,
    rw Nc_members at hx hy,
    have h5:= similar_symmetric M y a,
    rw h5 at hy,
    have h6:= similar_transitive M x a y hx hy,
    exact h6,
  end 

lemma cardinals0: ∀ (κ x y:M), κ ∈ NC M → x ∈ κ → similar M x y → y ∈ κ:=
  begin
    intros κ x y hk hx hsim,
    have hk2:= hk,
    rw NC_members at hk,
    cases hk with a h3,
    have h4:= xinNcx M a,
    have h5:= h4,
    rw←h3 at h5,
    rw h3 at hx,
    rw Nc_members at hx,
    have h8:= (similar_symmetric M x y).1 hsim,
    have h9:= similar_transitive M y x a h8 hx,
    have h10: y ∈ Nc M a:=
      begin
        rw Nc_members,
        exact h9,
      end, 
    rw h3,
    exact h10,
  end 

lemma cardinalsdisjoint2: ∀ (n m x:M), n ∈ NC M → m ∈ NC M → x ∈ n → x ∈ m → n = m:=
  begin
    intros n m x hn hm hx hx2,
    rw full_extensionality,
    intros y,
    split,
    {
      intros hy,
      have h3:= cardinals2 M n x y hn hx hy,
      have h4:= cardinals0 M m x y hm hx2 h3,
      exact h4,
    },
    {
      intros hy,
      have h13:= cardinals2 M m y x hm hy hx2,
      have h14:= cardinals0 M n x y hn hx,
      apply h14,
      exact (similar_symmetric M y x).1 h13,
    }
  end

lemma in_zero: ∀ (x:M), x ∈ zero ↔ x = Λ:=
  assume x,
  begin
    rw zero_definition,
    rw (singleton1 M),
  end
  
lemma base20: (zero:M) ∈ Z20 M:=
  begin
    rw (Z20_members M),
    intros x y h1 h2,
    rw (in_zero M) at h1,
    rw (in_zero M) at h2,
    rw h1,
    rw h2, 
    exact (similar_reflexive M Λ),  
  end

lemma restriction: ∀(f x u v:M), ‹ u,v › ∈ restrict f x ↔ ‹ u,v › ∈ f ∧ u ∈ x:=
  assume f x u v,
  begin
    rw (restrict_definition f x),
    rw (intersection_axiom),
    rw (product_axiom), 
    split,
    {
      intro h,
      cases h with h1 h2,
      cases h2 with a h3,
      cases h3 with b h4,
      rw (ordered_pair_equality M) at h4,
      split,
      { 
        exact h1,
      },
      { 
        rcases h4 with ⟨ h5, h6, h7, h8⟩, 
        rw h7 at *,
        exact h5, 
      },
    },
    { 
      intro h,
      cases h with h1 h2,
      split,
      { 
        exact h1,
      },
      {
        use u, use v,
        split,
         {
           exact h2,
         },
         {
           split,
           {
            exact (V_definition v),
           },
           { 
             exact (refl (‹ u,v › )), 
           }
         }
      }
    }
  end

lemma extend_function: ∀ (x y a b g:M),
(maps M g x y  → ¬ (a ∈ x) → ¬ (b ∈ y) → 
maps M ((restrict g x) ∪ (single ‹ a,b› ) ) (x ∪ (single a)) (y ∪ (single b))):=
  assume x y a b g,
  begin
    repeat{ unfold maps},
    intros h1 h2 h3,
    rcases h1 with ⟨ h4, h5, h6⟩,
    repeat{split},
    {
      rw restrict_definition, 
      rw Rel_definition, 
      intro z,
      intro h16,
      rw binary_union_axiom at h16, 
      cases h16 with h7 h8, 
      {
        rw intersection_axiom at h7,
        cases h7 with h8 h9,
        rw (product_axiom) at h9, 
        cases h9 with a h10, 
        cases h10 with b h11, 
        use a, use b, 
        exact  (h11.right.right),  
      },
      { 
        rw (singleton1 M) at h8, 
        use a, use b,
        exact h8,
      }  
    },
    {
      cases h6 with h7 h8,
      intros u v,
      intro h9,
      cases h9 with h10 h11,
      rw binary_union_axiom at h10,
      cases h10 with h12 h13,
      {
        rw binary_union_axiom at h11,
        cases h11 with h14 h15,
        {
          rw (restriction M) at h14,
          cases h14 with h16 h17,
          specialize h5 u v,
          have h18:= h5 ⟨ h17, h16 ⟩, 
          rw binary_union_axiom,
          left, 
          exact h18,  
        },
        {
          rw (singleton1 M) at h15,
          rw binary_union_axiom,
          rw (ordered_pair_equality M) at h15,
          right,
          rw (singleton1 M),
          exact h15.right, 
        }
      },
      {
        rw (singleton1 M) at h13,
        rw h13 at *,
        rw (binary_union_axiom) at h11,
        cases h11 with h14 h15,
        {
          rw (restriction M) at h14,
          cases h14 with h16 h17,
          specialize h5 a v,
          have h18:= h5 ⟨ h17, h16⟩,
          rw binary_union_axiom,
          left,
          exact h18, 
        },
        {
          rw (singleton1 M) at h15,
          rw (ordered_pair_equality M) at h15,
          cases h15 with h16 h17,
          rw binary_union_axiom,
          right,
          rw (singleton1 M),
          exact h17,
        }
      }
    },
    {
      intros u y z h,
      rcases h with ⟨ h7, h8, h9⟩,
      rw binary_union_axiom at h7 h8 h9,
      rw (singleton1 M) at h7,
      cases h7 with h10 h11,
      {
        rw (restriction M) at *,
        cases h6 with h12 h13,
        have h14:= h12  u y z,
        cases h9 with h16 h17,
        {
          cases h8 with h18 h19,
          {
            apply h14,
            split,
            {
              exact h10,
            },
            {
              exact ⟨ h18.left, h16.left⟩, 
            }
          },
          {
            rw (singleton1 M) at h19,
            rw (ordered_pair_equality M) at h19, 
            cases h19 with h20 h21, 
            rw h20 at *, 
            contradiction, 
          }
        },
        {
          rw (singleton1 M) at h17, 
          rw (ordered_pair_equality M) at h17, 
          cases h17 with h18 h19,
          rw h18 at *, 
          rw h19 at *,
          contradiction, 
        } 
      },
      {
        rw (restriction M) at *,
        cases h9 with h20 h21,
        {
          cases h6 with h22 h23,
          rw h11 at *,
          cases h8 with h24 h25,
          {
            have h26:= h22 a y z,
            cases h20 with h27 h28,
            contradiction, 
          },
          {
            rw (singleton1 M) at h25, 
            rw (ordered_pair_equality M) at h25, 
            cases h20 with h27 h28,
            contradiction, 
          }
        },
        {
          rw (singleton1 M) at h21, 
          rw (ordered_pair_equality M) at h21, 
          cases h21 with h22 h23,
          rw h22 at *,
          rw h23 at *,
          rw (singleton1 M) at h8, 
          rw (ordered_pair_equality M) at h8,
          cases h8 with h30 h31,
          {
            cases h30 with h32 h33,
            contradiction, 
          },
          {
            simp at h31,
            exact h31, 
          }
        }
      }
    },
    {
      intros u h,
      rw binary_union_axiom at h,
      rw (singleton1 M) at h, 
      cases h6 with h7 h8, 
      have h9:= h8 u, 
      cases h with h30 h31,
      {
        have h10:= h9 h30,
        cases h10 with w h11,
        cases h11 with h12 h13,
        use w, 
        split,
        {
          rw binary_union_axiom,
          left,
          exact h12, 
        },
        {
          rw binary_union_axiom,
          rw (restriction M), 
          left,
          exact ⟨ h13, h30⟩, 
        }
      },
      {
        rw h31 at *,
        use b,
        split,
        {
          exact (adjoin_member M b y),
        },
        {
          rw binary_union_axiom,
          right,
          rw (singleton1 M), 
        }
      }
    }
  end 

lemma extend_onto: ∀ (x y a b g:M),
(onto M g x y  → ¬ (a ∈ x) → ¬ (b ∈ y) → 
onto  M ((restrict g x) ∪ (single ‹ a,b› ) ) (x ∪ (single a)) (y ∪ (single b))):=
  assume x y a b g,
  begin
    intros h1 h2 h3,
    rw onto at h1,
    rw onto,
    intros v h4,
    rw binary_union_axiom at h4,
    cases h4 with h5 h6,
    {
      specialize h1 v,
      have h6:= h1 h5,
      cases h6 with u h7, 
      cases h7 with h8 h9,
      use u,
      split,
      {
        exact (adjoin_member2 M u a x h8), 
      },
      {
        rw binary_union_axiom, 
        left, 
        rw (restriction M), 
        exact (and.intro h9 h8), 
      }
    },
    {
      rw (singleton1 M) at h6,
      rw h6 at *,
      use a,
      split,
      { 
        exact (adjoin_member M a x), 
      },
      {
        rw binary_union_axiom,
        right,
        rw (singleton1 M), 
      }
    }
  end 

lemma extend_oneone: ∀ (x y a b g:M),
(oneone M g x y  → ¬ (a ∈ x) → ¬ (b ∈ y) → 
oneone  M ((restrict g x) ∪ (single ‹ a,b› ) ) (x ∪ (single a)) (y ∪ (single b))):=
  assume x y a b g,
  begin
    intros h1 h2 h3, 
    unfold oneone at *, 
    cases h1 with h4 h5,
    split,
    {
      exact (extend_function M x y a b g h4 h2 h3), 
    },
    { 
      cases h5 with h6 h7, 
      split,
      {
        intros u v y,
        intro h8,
        rcases h8 with ⟨ h9, h10, h11⟩,
        rw binary_union_axiom at h9 h10,
        specialize h6 u v y,
        have h12:= h7 u v,
        cases h10 with h20 h21,
        { 
          cases h9 with h22 h23,
          {
            rw (restriction M) at h20 h22, 
            exact (h6 ⟨ h22.left ,⟨ h20.left , h22.right ⟩ ⟩), 
          },
          { 
            rw (singleton1 M) at h23, 
            rw (ordered_pair_equality M) at h23,
            cases h23 with h24 h25,
            rw h24 at *,
            rw h25 at *,
            rw (restriction M) at h20,
            unfold maps at h4,
            rcases h4 with ⟨ h30, h31, h32⟩,
            specialize h31 v b,
            cases h20 with h32 h33,
            have h34:= h31 ⟨ h33, h32⟩, 
            contradiction,
          }
        },
        {
          cases h9 with h22 h23,
          {
            rw (singleton1 M) at h21,
            rw (ordered_pair_equality M) at h21,
            cases h21 with h24 h25,
            rw h24 at *,
            rw h25 at *,
            unfold maps at h4,
            rcases h4 with ⟨ h30, h31, h32⟩,
            specialize h31 u b,
            rw (restriction M) at h22,
            cases h22 with h33 h34,
            have h35:= h31 ⟨ h34, h33⟩,
            contradiction, 
          },
          {
            rw (singleton1 M) at h21 h23,
            rw (ordered_pair_equality M) at h21 h23,
            cases h23 with h30 h31,
            cases h21 with h32 h33,
            rw h30 at *,
            rw h31 at *,
            rw h32 at *, 
          }
        }
      },
      {
        intros u v h, 
        cases h with h8 h9,
        rw binary_union_axiom at h8 h9,
        cases h9 with h10 h11,
        { cases h8 with h12 h13, 
          {
            rw (restriction M) at h12,
            cases h12 with h14 h15,
            exact (adjoin_member2 M u a x h15),
          },
          {
            rw (singleton1 M) at h13,
            rw (ordered_pair_equality M) at h13,
            cases h13 with h14 h15,
            rw h14 at *,
            rw h15 at *,
            exact (adjoin_member M a x),
          }

        },
        {
          cases h8 with h12 h13,
          {
            rw (restriction M) at h12,
            cases h12 with h14 h15,
            exact (adjoin_member2 M u a x h15),
          },
          {
            rw (singleton1 M) at h13,
            rw (ordered_pair_equality M) at h13,
            cases h13 with h15 h16,
            rw h15 at *,
            rw h16 at *,
            exact (adjoin_member M a x), 
          }
        },
      }
    }
  end


lemma extend_similarity: ∀ (x y a b g:M),
(similarity M g x y → ¬ (a ∈ x) → ¬ (b ∈ y) → 
∃ f:M, similarity M f (x ∪ (single a)) (y ∪ (single b))):=
  assume x y a b g,
  begin 
    intros h1 h2 h3,
    set G:= restrict g x with h4,
    set f:= G ∪ (single ‹ a, b› ) with h5, 
    use f,
    rw h5,
    rw h4,
    unfold similarity at *,
    cases h1 with h6 h7, 
    split,
    { 
      exact (extend_oneone M x y a b g h6 h2 h3),
    },
    {
      exact (extend_onto M x y a b g h7 h2 h3),
    }
  end 

lemma extend_similar: ∀ (x y a b:M), (similar M x y → ¬ (a ∈ x) → ¬ (b ∈ y) → 
(similar M (x ∪ (single a)) (y ∪ (single b)))):=
  assume x y a b,
  begin
    intros h h1 h2,
    unfold similar at *,
    cases h with g h3, 
    exact (extend_similarity M x y a b g h3 h1 h2),
  end 


lemma step20:  ∀(κ:M), κ ∈ Z20 M → (∃ u, u ∈ 𝕊 κ ) → 𝕊 κ ∈ Z20 M:=
assume κ,
  begin
    rw (Z20_members M),
    intro h,
    rw (Z20_members M),
    intro h2,
    intros x y,
    intros h3 h4,
    rw (successor_members M κ x) at h3,
    rw (successor_members M κ y) at h4,
    cases h3 with u h5,
    cases h4 with v h6,
    cases h5 with a h7,
    cases h6 with b h8,
    rcases h7 with ⟨h9, h10, h11⟩,
    rcases h8 with ⟨h12, h13, h14⟩,
    have h15:= h u v h9 h12,
    have h16:= extend_similar M u v a b h15 h10 h13,
    rw h11,
    rw h14,
    exact h16,
  end

lemma finitecardinals2: ∀ (x y κ :M), ( κ  ∈ 𝔽 →   x ∈ κ → y ∈ κ → similar M  x y) := --line 382 
  assume x y κ , 
  begin 
    intros h h1 h2, 
    rw F_members at h, 
    specialize h (Z20 M),
    have h3:= h (and.intro (base20 M) (step20 M)), 
    rw (Z20_members M) at h3,  
    exact h3 x y h1 h2,  
  end

lemma cardinalequality: ∀ (x y:M), Nc M x = Nc M y ↔ similar M x y:=  --line 395
  assume x y,
  begin
    split,
    {
      intro h,
      rw (full_extensionality M) at h,
      specialize h x,
      rw (Nc_members M) at h,
      have h4:= h.mp (similar_reflexive M x),
      rw (Nc_members M) at h4,
      exact h4, 
    },
    {
      intro h,
      rw (full_extensionality M), 
      intro u, 
      repeat { rw (Nc_members M)},
      split,
      {
        intro h2, 
        exact (similar_transitive M u x y h2 h), 
      },
      {
        intro h2,
        rw (similar_symmetric M x y) at h,
        exact (similar_transitive M u y x h2 h), 
      }
    }
  end 

lemma Nc_Lambda: Nc M Λ = zero:= 
  begin
    rw (full_extensionality M),
    intro x, 
    rw (Nc_members M),
    rw (similar_to_empty  M x), 
    rw  zero_definition,
    rw (singleton1 M),
  end 

lemma lemma23base: Λ ∈ W23 M :=   --line 399 
  begin
    rw (W23_members M),
    split,
    { 
      exact (lambda_finite M),
    },
    { 
      rw (Nc_Lambda M),
      exact (zeroF M), 
    }
  end 

lemma similarity_minus_one: ∀ (f x y a b:M), (similarity M f x y → a ∈ x → 
‹ a, b› ∈ f → similarity M f (x-(single a)) (y-(single b))):=
assume f x y a b,
begin
  intros h1 h2 h3,
  unfold similarity at *,
  cases h1 with h4 h5,
  split,
  {
    unfold oneone at *,
    rcases h4 with ⟨ h6,h7,h8⟩,
    unfold maps at *,
    cases h6 with h9 h10,
    cases h10 with h11 h12, 
    cases h12 with h13 h14, 
    repeat{ split}, 
    {
      exact h9, 
    },
    {
      intros u v,
      intro h15, 
      cases h15 with h16 h17,
      have h18:= h11 u v,
      rw (minus_members M) at h16, 
      cases h16 with h19 h20,
      rw (singleton1 M) at h20,
      have h21:= h18 ⟨ h19, h17⟩,
      rw (minus_members M),
      split,
      { 
        exact h21,
      },
      {
        rw (singleton1 M),
        intro h22,
        rw h22 at *,
        have h23:= h7 u a b, 
        have h24:= h23 ⟨ h17, h3, h19⟩,
        rw h24 at *,
        contradiction,
      }
    },
    {
      intros u v w,
      intro h15,
      rcases h15 with ⟨ h16,h17,h18⟩,
      rw (minus_members M) at h16,
      cases h16 with h19 h20,
      have h21:= h13 u v w,
      have h22:= h21 ⟨ h19, h17, h18⟩,
      exact h22, 
    },
    {
      intro u,
      intro h15, 
      rw (minus_members M) at h15,
      cases h15 with h16 h17,
      have h18:= h14 u h16,
      cases h18 with v h19,
      cases h19 with h20 h21,
      use v,
      split,
      {
        rw (minus_members M),
        split,
        {
          exact h20,
        },
        {
          rw (singleton1 M),
          intro h22,
          rw h22 at *,
          have h23:= h7 u a b,
          have h24:= h23 ⟨ h21, h3, h16⟩,
          rw h24 at *,
          rw (singleton1 M) at h17,
          contradiction,
        }
      },
      {
        exact h21,
      }
    },
    {
      intros u v y,
      intro h15,
      rcases h15 with ⟨ h16, h17, h18⟩,
      rw (minus_members M) at h18,
      cases h18 with h19 h20,
      rw (singleton1 M) at h20,
      have h21:= h7 u v y,
      have h22:= h21 ⟨ h16, h17, h19 ⟩, 
      exact h22, 
    },
    {
      intros u v,
      intro h15,
      cases h15 with h16 h17,
      rw (minus_members M),
      rw (minus_members M) at h17,
      cases h17 with h17 h19,
      rw (singleton1 M) at *,
      have h20:= h8 u v,
      have h21:= h20 ⟨ h16, h17⟩,
      split,
      {
        exact h21, 
      },
      {
        intro h22,
        rw h22 at *,
        have h23:= h13 a b v,
        have h24:= h23 ⟨ h21, h3, h16⟩,
        rw← h24 at *,
        contradiction, 
      }
    },
  },
  {
    unfold onto at *,
    intros v h6,
    specialize h5 v,
    rw (minus_members M) at h6,
    cases h6 with h7 h8,
    rw (singleton1 M) at h8,
    have h9:= h5 h7,
    cases h9 with u h10,
    cases h10 with h11 h12,
    use u,
    split,
    {
      rw (minus_members M),
      rw (singleton1 M),
      split,
      {
        exact h11,
      },
      {
        intro h13, 
        rw h13 at *, 
        unfold oneone at h4, 
        cases h4 with h14 h15,
        unfold maps at h14,
        rcases h14 with ⟨ h16, h17, h18, h19⟩,
        have h20:= h18 a v b, 
        have h21:= h20 ⟨ h2, h12, h3⟩,
        rw h21 at *,
        contradiction,
      } 
    },
    exact h12, 
  }, 
end 

lemma addsubtract: ∀ (x c:M), ¬ c ∈ x → x = (x ∪ (single c))- (single c) :=
  assume x c, 
  begin
    intro h, 
    rw (full_extensionality M),
    intro u,
    rw (minus_members M),
    rw (binary_union_axiom),
    rw (singleton1 M), 
    split,
    { 
      intro h11,
      split,
      { 
        left,
        exact h11,
      },
      {
        intro h12,
        rw h12 at *,
        exact h h11, 
      }
    },
    {
      intro h11,
      cases h11 with h12 h13,
      cases h12 with h14 h15,
        {
          exact h14, 
        },
        {
          contradiction, 
        }
    }        
  end  

lemma subtractadd: ∀(u b:M), u ∈ DECIDABLE M → b ∈ u → u = ((u- (single b)) ∪ (single b)):=
  assume u b, 
  begin
    intros h h2,
    rw (full_extensionality M),
    intro z, 
    rw binary_union_axiom, 
    rw (minus_members M), 
    rw (singleton1 M), 
    split,
    { 
      intro h4, 
      rw  (decidable_members M ) at h, 
      specialize h z b,
      have h5:= h ⟨ h4,h2 ⟩,
      cases h5 with h6 h7, 
      { 
        rw h6 at *,
        right,
        exact (refl b), 
      },
      {  
        left,
        exact ⟨ h4, h7⟩, 
      }, 
    },
    {
      intro h10,
      cases h10 with h11 h12,
      {
        exact h11.left, 
      },
      {
        rw h12 at *,
        exact h2, 
      }
    }
  end

--lemma 22, line 397 
lemma Ncsuccessor: ∀ (x c: M), ¬ c ∈ x → (Nc M (x ∪ (single c))) = 𝕊 (Nc M x) :=
  begin 
    intros x c h, 
    rw (full_extensionality M),
    intro u,
    rw (Nc_members M),
    rw (successor_members M), 
    split,
    { 
      intro h2,
      unfold similar at h2,
      cases h2 with f h3,
      -- we need to find b = f^{-1}(c)
      have h3copy := h3,
      unfold similarity at h3,
      cases h3 with h4 h5,
      have h5copy := h5, 
      unfold onto at h5,
      specialize h5 c,
      have h6:= h5 (adjoin_member M c x),
      cases h6 with b h7,  -- here's Waldo, that is b 
      cases h7 with h8 h9,
      have h10:= similarity_minus_one M  f u (x ∪ (single c)) b c h3copy h8 h9,
      have h13: ¬ (b ∈ u - (single b)):= 
        begin
          intro h14,
          rw (minus_members M) at h14, 
          cases h14 with h15 h16, 
          rw (singleton1 M) at h16,
          contradiction, 
        end, 
      use u - (single b), use b, 
      have h11: x = (x ∪ (single c))- (single c) := addsubtract M x c h, 
      rw←  h11 at h10, 
      repeat {split},
      {
        rw (Nc_members M),
        unfold similar,
        use f,
        exact h10, 
      },
      {
        intro h11,
        contradiction, 
      },
      {
        rw (full_extensionality M),
        intro z, 
        unfold oneone at h4,
        rcases h4 with ⟨ h20, h21, h22⟩,
        unfold maps at h20,
        rcases h20 with ⟨ h23, h24, h25, h26⟩,
        specialize h26 z,
        split,
        {
          intro h30,
          have h31:= h26 h30,
          cases h31 with y h32,
          cases h32 with h33 h34,
          specialize h24 z y,
          have h34:= h24 ⟨ h30, h34⟩,
          rw binary_union_axiom at h34,
          rw (singleton1 M) at h34,
          cases h34 with h35 h36,
          {
            rw binary_union_axiom,
            left,
            have h10copy:= h10,
            unfold similarity at h10,
            cases h10 with h40 h41,
            unfold onto at h41,
            have h42:= h41 y h35,
            cases h42 with w h43,
            cases h43 with h50 h51,
            unfold oneone at h40,
            rcases h40 with ⟨ h41, h42, h43⟩,
            have h44:= h42 w z y ⟨ h51, h34, h50⟩,
            rw h44 at h50,
            exact h50, 
          },
          {
            rw h36 at *,
            unfold similarity at h3copy,
            rcases h3copy with ⟨ h40, h41⟩,
            unfold oneone at h40, 
            rcases h40 with ⟨h42, h43, h44⟩,
            have h45:= h43 b z c ⟨ h9, h34, h8 ⟩, 
            rw← h45 at *,
            rw binary_union_axiom,
            right,
            rw (singleton1 M), 
          }
        },
        {
          intro h30,
          rw binary_union_axiom at h30,
          rw (minus_members M) at h30,
          rw (singleton1 M) at h30,
          cases h30 with h31 h32,
          { 
            exact h31.left, 
          },
          {
            rw h32 at *,
            exact h8, 
          }
        }
      }
    },
    { 
      intro h2,
      cases h2 with v h3,
      cases h3 with b h4,
      rcases h4 with ⟨ h5, h6, h7⟩,
      rw (Nc_members M) at h5,
      unfold similar at h5,
      cases h5 with f h8,
      have h9:= extend_similarity M v x b c f  h8 h6  h, 
      rw h7, 
      unfold similar, 
      exact h9, 
    }
  end 



lemma lemma23step:  adjoin_closed M (W23 M):=  --line 408 
  begin
    unfold adjoin_closed,
    intros x c,
    rw (W23_members M), 
    intro h,
    cases h with h2 h3,
    cases h2 with h4 h5,
    rw (W23_members M),
    split,
    {
      exact (finite_adjoin M x c ⟨ h4, h3 ⟩ ), 
    },
    {
      rw (Ncsuccessor M x c h3),
      have h4:= successorF M (Nc M x) h5,
      apply h4,
      use x ∪ (single c),
      rw (successor_members M),
      use x, use c,
      exact ⟨ xinNcx M x, h3, refl (x ∪ (single c))⟩,
    }
  end

lemma finitecardinals3: ∀ (x:M), x ∈ FINITE M → Nc M x ∈ 𝔽  := --line 409
  assume x, 
  begin
    have h2: (FINITE M)⊆ W23 M := (finite_conditions M) (W23 M)   (lemma23step M) (lemma23base M), 
    rw subset_definition at h2, 
    specialize h2 x,
    rw (W23_members M) at h2,  
    intro h3,
    have h4:= h2 h3, 
    cases h4 with h5 h6, 
    exact h6, 
  end

lemma successorinhabited: ∀ (κ ∈ 𝔽), ((∃(u:M) , u ∈ 𝕊 κ) → ∃ x, ( x ∈ 𝕊 κ ∧ (∃ y, y ∈ x))):=
  assume κ, 
  begin
    intros h h2,
    cases h2 with u h3,
    rw (successor_members M) at h3,
    cases h3 with x h4,
    cases h4 with c h5,
    use x ∪ (single c),
    split,
    { 
      rw (successor_members M),
      use x,
      use c,
      rcases h5 with ⟨ h6, h7, h8⟩,
      exact ⟨ h6, h7, (refl (x ∪ (single c)))⟩,
    },
    {
      use c,
      exact (adjoin_member M c x),
    }
  end

lemma lemma25b: ∀ (κ u:M), κ ∈ 𝔽 → u ∈ 𝕊 κ → ∃ x, ( x ∈ u):=
  assume κ u, 
  begin
    intros h h3,
    rw (successor_members M) at h3,
    cases h3 with x h4,
    cases h4 with c h5,
    rcases h5 with ⟨ h6, h7, h8⟩, 
    use c, 
    rw h8,
    exact adjoin_member M c x, 
  end 

lemma lemma25c: ∀(κ  u:M), u ∈ 𝕊 κ → ∃(v:M),v ∈ 𝕊 κ ∧ ∃ (w:M), w ∈ v:=
  --without assuming κ ∈ 𝔽, 
  assume κ u,
  begin
    intro h,
    have hcopy := h, 
    rw successor_members M at h,
    cases h with x h2,
    cases h2 with a h3,
    use u,
    split,
    {
      exact hcopy,
    },
    {
      use a,
      rcases h3 with ⟨ h4, h5, h6⟩, 
      rw h6,
      rw binary_union_axiom,
      rw singleton1 M,
      simp,
    }
  end

lemma Fregesuccessoromits0: ∀ (x:M), ¬ (𝕊 x = (zero:M)) :=
  assume x,
  begin
    intros  h2,
    rw zero_definition at h2, 
    have h3: Λ ∈ 𝕊 x:=
      begin
        rw h2,
        rw singleton1 M,
      end,
    have h4:= lemma25c M x Λ  h3, 
    cases h4 with t h5,
    cases h5 with h6 h7,
    rw h2 at h6,
    rw singleton1 M at h6,
    cases h7 with w h8,
    rw h6 at h8,
    exact emptyset_axiom w h8,
  end

lemma successor_omits_zero: ∀ (κ:M),   ¬ 𝕊 κ = zero:=
    assume κ, 
    begin
      intro h2,
      rw h2 at *,
      rw full_extensionality at h2,
      specialize h2 Λ,
      rw zero_definition at h2,
      rw singleton1 M at h2,
      have h3:= h2.mpr (refl Λ), 
      rw successor_members M at h3, 
      cases h3 with x h4,
      cases h4 with c h5,
      rcases h5 with ⟨ h6, h7, h8⟩,
      rw full_extensionality M at h8,
      specialize h8 c,
      rw binary_union_axiom at h8,
      rw singleton1 M at h8,
      have h9:= emptyset_axiom c,
      simp at h8, 
      contradiction, 
    end 

lemma Fclosed: ∀ (κ :M), κ ∈ 𝔽 → (∃ u, u ∈ 𝕊 κ ) → 𝕊 κ ∈ 𝔽:=
  assume κ,
  begin
    intros h h2,
    have h3:= F_members  (𝕊 κ),
    rw h3,
    intro W,
    intro h4,
    have h5: κ ∈ W:=
      begin
        have base: zero ∈ W:= h4.left, 
        have step: ∀ u, (u ∈ W → (∃ v, v ∈ 𝕊 u) → 𝕊 u ∈ W):=
           h4.right, 
        have h6: 𝔽 ⊆ W:= 
          begin
            rw subset_definition,
            intro t,
            rw F_members t, 
            intro h7,
            specialize h7 W,
            exact h7 ⟨ base,step⟩, 
          end,
        exact member_subset M 𝔽 W κ h6 h,
      end,
    cases h4 with h6 h7,
    specialize h7 κ, 
    exact h7 h5 h2, 
  end

lemma Nc_empty: Nc M Λ = zero:=
  begin
    rw zero_definition, 
    rw full_extensionality,
    intro t,
    rw Nc_members,
    rw similar_to_empty,
    rw singleton1 M,
  end

#axioms_all  --This file is clean
  
