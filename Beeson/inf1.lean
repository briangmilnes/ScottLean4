
import inf

variables (M:Type) [Model M] (a b x y z u v w X R W: M)

open Model 

def adjoin_closed(x:M) := 
    ∀ (u a :M), ((u ∈ x ∧ ¬ (a ∈ u)) → u ∪ (single a) ∈ x)   

lemma lambda_finite :  Λ ∈ (FINITE M) :=
   begin
    rw (finite_members M),
    intros w h, 
    cases h with h1 h2,
    assumption,
  end 

lemma finite_adjoin_closed: (adjoin_closed M) (FINITE M):=
  begin
   rw adjoin_closed,
   simp_rw finite_members,
   rintro u a h1 w h2,
   cases h1 with h3 h4,
   have h5:u∈ w:= h3 w h2,
   cases h2 with h6 h7,
   exact (h7 u a  (and.intro h4 h5) ), 
  end

lemma finite_adjoin: ∀ x c:M, (x ∈ FINITE M ∧  ¬ (c ∈ x) → x ∪ (single c) ∈ FINITE M):=
  assume x c,
  begin 
    exact finite_adjoin_closed M x c,
  end 

lemma lambda_cup: ∀(x:M), Λ ∪ x = x:=
  assume x,
  begin
    rw (full_extensionality M (Λ ∪ x) x),
    intro z,
    rw ( binary_union_axiom Λ x z),
    have h:= emptyset_axiom z,
    split,
    {
      intro h2,
      cases h2 with h3 h4,
      {
        contradiction,
      },
      {
        exact h4,
      }
    },
    {
      intro h4,
      right,
      exact h4, 
    }
  end

lemma singleton_finite: ∀ (a:M), (single a ∈ FINITE M):=
  assume a,
  begin
   have h:= lambda_finite M,
   have h2:= finite_adjoin M Λ a ,
   have h3:= h2 (and.intro h (emptyset_axiom a)), 
   rw (lambda_cup M (single a)) at h3,
   exact h3, 
  end

lemma lambda_decidable: (Λ ∈ (DECIDABLE M)):=
  begin
    simp_rw decidable_members,
    intros u v h,
    cases h with h4 h5,
    have h2: ¬ (u ∈ Λ ) := (emptyset_axiom u),
    have h3: ¬ (v ∈ Λ ) := (emptyset_axiom v),
    contradiction, 
  end

lemma decidable_adjoin_closed: (adjoin_closed M) (DECIDABLE M):=
  begin
   rw adjoin_closed,
   rintro u a h,
   rw decidable_members,
   rintro p q,  
   rw (binary_union_axiom u (single a) p),
   rw (binary_union_axiom u (single a) q),
   rw (singleton1 M  p a), 
   rw (singleton1 M q a),
   cases h with h4 h5,
   rw (decidable_members M) at h4,
   specialize h4 p q,
   rintros h6,
   cases h6 with h7 h8,
   cases h7 with h9 h10,
   cases h8 with h11 h12,
     {  
       apply h4,
       exact ⟨ h9, h11⟩, 
     },
     { have h13: a ≠ p,
         begin 
          intro h14,
          rw h14 at h5,
          exact (h5 h9),
         end, 
        rw h12,
        replace h13 := h13.symm,
        exact  (or.intro_right (p=a) h13),    
     },
     { rw h10,
       cases h8 with h20 h21,
       have h22: q ≠ a,
         begin
           intro h23,
           rw h23 at h20,
           exact (h5 h20),
         end,
       replace h22 := h22.symm,
       exact (or.intro_right(a=q) h22),
       replace h21 := h21.symm,
       exact (or.intro_left (a ≠ q) h21),
     },
  end

lemma finite_conditions: ∀ x:M, ((adjoin_closed M x) →  Λ ∈ x → (FINITE M) ⊆ x) :=
  assume x,
  begin
    rintros h1 h2,
    rw subset_definition,
    intro z,
    rw finite_members,
    intro h3,
    specialize h3 x,
    rw adjoin_closed at h1,
    /- simp_rw and_comm at h1,   doesn't work, don't know why not  -/ 
    have h6: ∀ (u a:M), ¬ a ∈ u ∧ u ∈ x → u ∪ single a ∈ x:=
      begin
        intros u a,
        specialize h1 u a,
        intro h4,
        cases h4 with h5 h6,
        exact h1 ⟨ h6, h5⟩, 
      end,
    exact (h3  (and.intro h2 h6)),
  end

lemma finitedecidable: ∀ (x:M), (x ∈ FINITE M →  x ∈ DECIDABLE M ):=
  have  h:(FINITE M) ⊆ (DECIDABLE M):=
    ((finite_conditions M)(DECIDABLE M) (decidable_adjoin_closed M) ( lambda_decidable M)),
  begin 
    assume x,
    rw (subset_definition (FINITE M)(DECIDABLE M)) at h,
    exact (h x),
  end

lemma finite_decidable2: ∀ (x a b :M), (x ∈ FINITE M → a ∈ x → b ∈ x → a = b ∨ ¬ (a = b)):=
  assume x a b,
  begin
    intro h, 
    have h2: x ∈ DECIDABLE M :=  (finitedecidable M x h),
    rw (decidable_members M x) at h2,
    specialize h2 a b,
    intros h4 h5,
    exact h2 ⟨ h4, h5⟩, 
  end

lemma empty_or_inhabited: ∀ (x:M), (x ∈ FINITE M → x = Λ ∨ ∃ u, u ∈ x):=
  begin
    have h: Λ ∈ (EMPTY_OR_INHABITED M):=
      begin
        unfold EMPTY_OR_INHABITED,
        rw comprehension,
        left,
        exact refl Λ, 
      end,
    have h2: (adjoin_closed M)(EMPTY_OR_INHABITED M):=
      begin
        rw adjoin_closed,
        assume u a,
        intro h3,
        cases h3 with h4 h5,
        unfold EMPTY_OR_INHABITED at h4,
        rw comprehension at h4,
        unfold EMPTY_OR_INHABITED,
        rw comprehension,
        right,
        use a,
        rw ( binary_union_axiom u (single a) a),
        rw (singleton1 M),
        right,
        exact refl a, 
      end,
    have h6:(FINITE M) ⊆ (EMPTY_OR_INHABITED M):=
      ((finite_conditions M)(EMPTY_OR_INHABITED M) h2 h),
      rw (subset_definition (FINITE M)(EMPTY_OR_INHABITED M)) at h6,
      unfold EMPTY_OR_INHABITED at h6,
      assume x,
      specialize h6 x,
      rw comprehension at h6,
      exact h6,
  end


lemma finverse_maps:  ∀ (f X Y:M), (oneone M f X Y ∧ onto M f X Y  → maps  M (inv f) Y X) :=
  assume f X Y,
  begin
    intro h1,
    cases h1 with h2 h3,
    unfold maps,
    unfold oneone at h2,
    cases h2 with h50 h51,
    unfold maps at h50,
    cases h50 with h52 h53,
    cases h51 with h68 h69,
    split,
      { 
        exact (inverse_axiom1 f h52),
      },
      { split,
      { 
        assume x y,
        rw  (inverse_axiom2 f h52 x y),
        intro h63,
        cases h63 with h64 h65,
        cases h53 with h66 h67,
        specialize h69 y x,
        apply h69,
        exact ⟨ h65, h64⟩,
      },
      { 
        split,
          { 
            assume x y z,
            rw (inverse_axiom2 f h52 x y),
            rw (inverse_axiom2 f h52 x z),
            intro h70,
            cases h70 with h71 h72,
            cases h72 with h73 h74,
            specialize h68 y z x, 
            specialize h69 y x,
            apply h68,
            have h80:= h69 ⟨ h73, h71⟩, 
            exact ⟨ h73, h74, h80⟩, 
          },
          { 
            assume x,
            intro h80,
            unfold onto at h3,
            specialize h3 x, 
            have h81: (∃  (x_1 : M), x_1 ∈ X ∧ ‹ x_1,x › ∈ f) := (h3 h80), 
            cases h81 with y h82,
            use y,
            rw (inverse_axiom2 f h52 x y),
            exact h82, 
          }
      }
      },
   end

lemma finverse_oneone: ∀ (f X Y:M), (oneone M f X Y ∧ onto M f X Y  → oneone M (inv f) Y X) :=
  assume f X Y, 
  begin
    intro h,
    cases h with h2 h3, 
    have h82 := h2, 
    unfold oneone at h2,
    cases h2 with h10 h11,
    unfold maps at h10,
    cases h10 with h12 h13,
    rw oneone,
    split,
      {  exact (finverse_maps M f X Y (and.intro h82 h3)), 
      },
      { 
        split,
          { 
            assume x u y,
            rw (inverse_axiom2 f h12 x y),
            rw (inverse_axiom2 f h12 u y),
            cases h11 with h7 h8,
            intro h9,
            cases h9 with h10 h11,
            cases h11 with h42 h43,
            specialize h8 y x,
            have h14:y ∈ X := h8 (and.intro h10 h43), 
            cases h13 with h15 h16, 
            cases h16 with h17 h18, 
            specialize h17 y x u, 
            apply h17,
            exact ⟨ h14, h10, h42⟩, 
          },
          { 
            assume x y,
            rw (inverse_axiom2 f h12 x y ), 
            intro h33,
            cases h13 with h60 h61, 
            specialize h60 y x, 
            apply h60,
            exact ⟨ h33.right, h33.left⟩, 
          }
      }
  end  

lemma lemma3d: ∀ (f X Y:M), (oneone M f X Y ∧ onto M f X Y  → onto M (inv f) Y X) :=
  assume f X Y,
  begin
    intro h,
    cases h with h2 h3,
    unfold onto,
    intro y,
    intro h4,
    unfold oneone at h2,
    cases h2 with h5 h6,
    unfold maps at h5,
    cases h5 with h7 h8,
    cases h8 with h9 h10,
    cases h10 with h11 h12,
    specialize h12 y,
    have h13:∃ (y1 : M), (y1 ∈ Y ∧ ‹ y,y1 › ∈ f):=  (h12 h4),
    cases h13 with y1 h14,
    use y1,
    rw (inverse_axiom2 f h7 y1 y),
    exact h14, 
  end

lemma lemma4a: ∀ x:M, (maps M (IDENTITY M x) x x) :=
  begin
    intro x,
    unfold maps,
    split,
      {
        rw (Rel_definition (IDENTITY M x)), 
        intro z,
        intro h1,
        rw (identity_members M x z) at h1,
        cases h1 with u h2,
        use u,
        use u,
        exact h2.left, 
      },
      {
        split,
          { intro x1,
            intro y,
            rw (identity_members M x ‹ x1,y › ),
            intro h3,
            cases h3 with h4 h5,
            cases h5 with u h6,
            rw (ordered_pair_equality M u u x1 y) at h6,
            cases h6 with h7 h8,
            cases h7 with h9 h10,
            rw h10,
            exact h8, 
          },
          { split,
              {
                intros x1 y z h7,
                cases h7 with h8 h9,
                cases h9 with h10 h11,
                rw (identity_members M x ‹ x1,y › ) at h10,
                rw (identity_members M x ‹ x1,z › ) at h11,
                cases h10 with u h12,
                cases h11 with v h13,
                rw (ordered_pair_equality M u u x1 y) at h12,
                rw (ordered_pair_equality M v v x1 z) at h13,
                cases h12 with h15 h14,
                cases h15 with h16 h17,
                cases h13 with h18 h19,
                cases h18 with h20 h21,
                rw h16 at *,
                rw h17 at *,
                rw h21 at *,
                exact h20,
              },
              { 
                intros x1 h,
                use x1,
                rw (identity_members M x ‹ x1,x1› ),
                split,
                  { exact h,
                  },
                  {
                    use x1,
                    exact ⟨ refl ‹ x1,x1› , h⟩,
                  }
              }
          }
      }
  end
   
lemma lemma4b: ∀ x:M, (oneone M (IDENTITY M x) x x) :=
  assume x,
  begin
    unfold oneone,
    split,
      {
        exact (lemma4a M x), 
      },
      { 
        split,
          {
            intros x1 u y h,
            cases h with h2 h3,
            rw (identity_members M x ‹ x1,y› ) at h2,
            rw (identity_members M x ‹ u,y› ) at h3,
            cases h2 with p h4,
            cases h3 with h5 h6,
            cases h5 with q h7,
            rw (ordered_pair_equality M p p x1 y) at h4,
            rw (ordered_pair_equality M q q u y) at h7,
            cases h4 with h8 h9,
            cases h7 with h10 h11,
            rw h10.left at *,
            rw h10.right at *,
            rw h8.left at *,
            rw h8.right at *,
          },
          { 
            intros x1 y h,
            cases h with h8 h9,
            rw (identity_members M x ‹ x1,y› ) at h8,
            cases h8 with u h9,
            rw (ordered_pair_equality M u u x1 y) at h9,
            cases h9 with h10 h11,
            rw h10.left at *,
            exact h11, 
          }
      }
  end

lemma lemma4c: ∀ x:M, (onto M (IDENTITY M x) x x) :=
  assume x,
  begin
    unfold onto,
    intro y,
    intro h,
    use y,
    rw (identity_members M x ‹ y,y › ),
    split,
      {
        exact h,
      },
      {
        use y,
        exact ⟨ refl ‹ y,y › , h⟩, 
      }
  end

lemma lemma4d: ∀ x:M, (similarity M (IDENTITY M x) x x) :=
  assume x,
  begin
    unfold similarity,
    split,
      {
        exact (lemma4b M x),
      },
      {
        exact (lemma4c M x),
      }
  end

lemma similar_reflexive: ∀ x:M, (similar M x x):=
  assume x,
  begin
   unfold similar,
   use (IDENTITY M x),
   exact (lemma4d M x), 
  end

lemma similar_symmetric_left_right: ∀ x y:M,  similar M x y →  similar M y x := 
   assume x y,
   begin
     intro h,
     unfold similar at h,
     unfold similar,
     cases h with f h2,
     use (inv f),
     unfold similarity at h2,
     unfold similarity,
     exact (and.intro (finverse_oneone M f x y h2)(lemma3d M f x y h2)),
   end

lemma similar_symmetric: ∀ x y:M,  similar M x y ↔  similar M y x := 
   assume x y,
   begin
     split,
     { intro h, 
       exact (similar_symmetric_left_right M x y h),
     },
     { intro h2,
       exact (similar_symmetric_left_right M y x h2),
     }
   end


lemma lemma4g: ∀ x y z f g:M, maps M f x y → maps M g y z → maps M (join f g) x z:=
  assume x y z f g,
  begin
    intros h1 h2,
    unfold maps at *,
    cases h1 with h3 h4,
    cases h2 with h5 h6,
    cases h4 with h7 h8,
    cases h6 with h9 h10,
    cases h10 with h11 h12,
    split,
    { 
      rw (Rel_definition (join f g)),
      intros z h13,
      rw (join_axiom f g h3 h5) at h13,
      cases h13 with a h14,
      cases h14 with b h15,
      cases h15 with c h16,
      use a,
      use c,
      exact h16.left, 
    },
    { split,
        { assume x1 y1,
          intro h17,
          cases h17 with h18 h19,
          rw (join_axiom f g h3 h5) at h19,
          cases h19 with a h20,
          cases h20 with b h21,
          cases h21 with c h22,
          cases h22 with h23 h24,
          cases h24 with h25 h26,
          rw (ordered_pair_equality M a c x1 y1) at h23,
          cases h23 with h27 h28,
          specialize h7 a b,
          rw h27 at *,
          cases h8 with h29 h30,
          specialize h9 b c,
          rw h28 at *,
          apply h9,
          split,
          {
            apply h7,
            exact ⟨ h18, h25⟩, 
          },
          {
            exact h26, 
          }
        },
        { split,
          { intros a b c h30,
            rw (join_axiom f g h3 h5) at h30,
            rw (join_axiom f g h3 h5) at h30,
            cases h30 with h31 h32;
            cases h32 with h33 h34,
            cases h33 with p h35,
            cases h35 with q h36,
            cases h36 with r h37,
            cases h34 with P h38,
            cases h38 with Q h39,
            cases h39 with R h40,
            rw (ordered_pair_equality M P R a c) at h40,
            rw (ordered_pair_equality M p r a b) at h37,
            cases h40 with h41 h42,
            cases h37 with h43 h44,
            cases h41 with h45 h46,
            cases h43 with h47 h48,
            rw← h45 at *,
            rw← h46 at *,
            rw← h47 at *,
            rw← h48 at *,
            cases h8 with h49 h50,
            cases h42 with h51 h52,
            cases h44 with h53 h54,
            specialize h49 a Q q,
            have h55: Q = q := 
              begin 
                apply h49,
                exact ⟨ h31, h51, h53⟩,
              end, 
            rw h55 at *,
            specialize h11 q b c,
            specialize h7 a q,
            apply h11,
            have h60:= h7 ⟨ h31, h53⟩,
            exact ⟨ h60, h54, h52⟩, 
          },
          { intros a h,
            cases h8 with h60 h61,
            specialize h61 a,
            have h62: (∃ (y_1 : M), y_1 ∈ y ∧ ‹ a,y_1 › ∈ f) := (h61 h),
            cases h62 with b h63,
            cases h63 with h64 h65,
            specialize h12 b,
            have h66: (∃ (y : M), y ∈ z ∧ ‹ b,y › ∈ g) := (h12 h64),
            cases h66 with c h67,
            cases h67 with h68 h69,
            use c,
            rw (join_axiom f g h3 h5 ‹ a,c› ),
            split,
                { exact h68,
                },
                { 
                  use a, use b, use c,
                  exact ⟨ refl ‹ a,c › , h65, h69⟩, 
                }
          }
        }
     }
  end 

lemma lemma4h: ∀ x y z f g:M, oneone M f x y → oneone M g y z → oneone M (join f g) x z:=
  assume x y z f g,
  begin
    intros h1 h2,
    unfold oneone at *,
    cases h1 with h3 h4,
    have h3a:= h3,
    cases h2 with h5 h6,
    have h5a:= h5,
    unfold maps at h3a,
    unfold maps at h5a,
    cases h3a with h10 h11,
    cases h5a with h12 h13,
    split,
      { exact (lemma4g M x y z f g h3 h5),
      },
      { split,
         { cases h6 with h7 h8,
           intros x1 u1 y1 h9,
           rw (join_axiom f g h10 h12 ‹ x1,y1 ›) at h9,
           rw (join_axiom f g h10 h12 ‹ u1, y1›) at h9, 
           cases h9 with h14 h15, 
           cases h11 with h18 h19,
           cases h4 with h20 h21,
           cases h13 with h22 h23,
           cases h19 with h26 h27,
           cases h23 with h28 h29,
           cases h14 with a h32,
           cases h32 with b h33,
           cases h33 with c h34,
           cases h34 with h35 h36,
           cases h36 with h37 h38,
           cases h15 with  h39 h40,
           cases h39 with p h40,
           cases h40 with q h41,
           cases h41 with r h42,
           cases h42 with h43 h44,
           cases h44 with h45 h46,
           rw (ordered_pair_equality M p r u1 y1) at h43,
           cases h43 with h47 h48,
           rw (ordered_pair_equality M a c x1 y1) at h35,
           cases h35 with h49 h50,
           rw h50 at *,
           rw h49 at *,
           rw h47 at *,
           rw h48 at *,
           specialize h7 b q r,
           specialize h8 b r,
           specialize h22 b r,
           specialize h18 a b,
           have h53:b∈ y := (h18 (and.intro h40 h37)),
           have h52:r ∈ z:= (h22 (and.intro h53 h38)), 
           have h51:b=q := (h7 ((and.intro h38 (and.intro h46 h53)))),
           rw← h51 at *,
           specialize h20 a p b,
           apply h20,
           exact ⟨ h37, h45, h40⟩, 
          
         },
         { intros a c h60,
           cases h60 with h61 h62,
           rw (join_axiom f g h10 h12 ‹ a,c › ) at h61,
           cases h61 with p h62,
           cases h62 with q h63,
           cases h63 with r h64,
           cases h64 with h65 h66,
           cases h66 with h67 h68,
           rw (ordered_pair_equality M p r a c ) at h65,
           cases h65 with h66 h69,
           rw← h66 at *,
           rw← h69 at *,
           cases h6 with h70 h71,
           specialize h71 q c,
           cases h4 with h72 h73,
           specialize h73 a q,
           apply h73, 
           have h74:= h71 ⟨ h68, h62⟩, 
           exact ⟨ h67, h74⟩, 
         }
      }
  end 

lemma lemma4i:  ∀ x y z f g:M, Rel f → Rel g → onto M f x y → onto M g y z → onto M (join f g) x z:=
  assume x y z f g,
  begin
   intros h20 h21 h1 h2,
   unfold onto at *,
   intros r h3,
   specialize h2 r,
   have h4: (∃ (x : M), x ∈ y ∧ ‹ x,r › ∈ g):= (h2 h3),
   cases h4 with q h5,
   cases h5 with h6 h7,
   specialize h1 q,
   have h8: (∃ (x2 : M), x2 ∈ x ∧ ‹ x2,q › ∈ f) := (h1 h6),
   cases h8 with p h9,
   cases h9 with h10 h11,
   use p,
   split,
     {  
       exact h10,
     },
     { rw (join_axiom f g h20 h21 ‹ p,r › ),
       use p, use q, use r,
       exact ⟨ refl ‹ p,r ›, h11, h7⟩, 
     }
  end
lemma similar_transitive: ∀ x y z:M, similar M x y → similar M y z → similar M x z:=
   assume x y z,
   begin
    rintros h1 h2,
    unfold similar at *,
    cases h1 with f h3,
    cases h2 with g h4,
    use (join f g),
    unfold similarity at *,
    have h5:=h3,
    unfold oneone at h3,
    cases h3 with h6 h7,
    cases h6 with h8 h9,
    unfold maps at h8,
    cases h8 with h10 h11,
    cases h4 with h16 h17,
    cases h5 with h22 h23, 
    have h16a := h16,
    unfold oneone at h16a,
    unfold maps at h16a,
    cases h16a with h24 h25,
    cases h24 with h26 h27,
    split,
      { 
        exact (lemma4h M x y z f g h22 h16),
      },
      {
        exact (lemma4i M x y z f g h10 h26 h23 h17), 
      }
   end

-- Now we've proved similar is reflexive, symmetric, and transitive,  that's Lemma 4 in the paper. 

lemma usc_cup: ∀ x a:M, ((¬ (a ∈ x))  → (USC (x ∪ (single a))  = ((USC x) ∪ (single (single a))))):=  
   assume x a, 
   begin
     intro h1, 
     suffices h3: ∀ p:M,(p ∈ USC (x ∪ (single a)))↔ (p ∈((USC x) ∪ (single (single a))) ), from
        ( extensionality_axiom (USC (x ∪ (single a))) ((USC x) ∪ (single (single a))) h3),
     assume p,
     rw (binary_union_axiom (USC x) (single (single a)) p), 
     rw (usc),
     rw (usc),  
     split,
      {
        intro h4,
        cases h4 with b h5,
        rw (binary_union_axiom x (single a) b) at h5,
        cases h5 with h6 h7, 
        cases h6,
          { 
            use b,
            exact ⟨ h6, h7⟩, 
          },
          {
            right,
            rw (singleton1 M b a) at h6,
            rw (singleton1 M p (single a)),
            rw h6 at *, 
            exact h7,
          }
      },
      {
        intro h7,
        cases h7 with h8 h9,
          { 
            cases h8 with b h9,
            use b,
            rw (binary_union_axiom x (single a) b),
            split,
            {
              left,
              exact h9.left, 
            },
            {
              exact h9.right, 
            }

          },
          { 
            use a,
            rw (singleton1 M p (single a)) at h9,
            rw (binary_union_axiom x (single a) a),
            rw (singleton1 M a a),
            split,
            {
              right,
              exact refl a,
            },
            {
              exact h9,
            }
          }
      }
   end

lemma lemma5b: ∀ a b:M, (single a = single b → a = b):=
  assume a b,
  begin
    intro h,
    have h2:∀ x:M, (x ∈ single a ↔ x ∈ single b):=
       assume x,
       begin
         rw h, 
       end,
   simp_rw (singleton1 M) at h2,
   specialize h2 a,
   cases h2 with h3 h4,
   apply h3,
   exact refl a,  
  end

lemma usc_dif: ∀ x a:M, ((a ∈ x)  → (USC (x - (single a))  = ((USC x) - (single (single a))))):=  
   assume x a, 
   begin
     intro h1, 
     suffices h3: ∀ p:M,(p ∈ USC (x - (single a)))↔ (p ∈((USC x) - (single (single a))) ), from
        ( extensionality_axiom (USC (x - (single a))) ((USC x) - (single (single a))) h3),
     assume p,
     rw (minus_members M (USC x) (single (single a)) p), 
     rw (usc),
     rw (usc),  
     split,
      {
        intro h4,
        cases h4 with b h5,
        rw (minus_members M  x (single a) b) at h5,
        cases h5 with h6 h7, 
        cases h6 with h20 h21, 
        split,
             { use b,
               exact ⟨ h20, h7⟩, 
             },
             {
               rw (singleton1 M p (single a)),
               rw (singleton1 M b a) at h21,
               rw h7,
               intro h22,
               exact (h21 (lemma5b M b a  h22)),  
             }  
      },
      { 
        intro h7,
        cases h7 with h8 h9,
          { 
            cases h8 with b h9,
            use b,
            rw (minus_members M x (single a) b), 
            cases h9 with h10 h11, 
            rw h11,
            rw (singleton1 M p (single a)) at h9,
            rw (singleton1 M b a), 
            split,
              {
                split,
                {
                  exact h10,
                },
                {
                  intro h13,
                  rw h13 at *,
                  contradiction,
                }
              },
              { 
                exact refl (single b), 
              }
          },
      }
   end


lemma singleton_subset_usc: ∀ w x:M, (single w ⊆ USC x → ∃ c:M, (c ∈ x ∧ w = single c)):=
  assume w x,
  begin
    rw (subset_definition (single w)(USC x)),
    intro h,
    simp_rw(singleton1 M) at h,
    specialize h w,
    simp at h, 
    rw (usc M x w) at h,
    cases h with c h2,
    use c,
    exact h2,
  end 

lemma cupminus:∀ z w:M, (¬(w ∈ z) → z = (z ∪ single w)- single w):=
  assume z w,
  begin
    intro h,
    rw (full_extensionality M),
    intro x,
    rw (minus_members M),
    rw (binary_union_axiom),
    rw (singleton1 M), 
    split,
     {
       intro h2,
       split,
        {
          left,
          exact h2,
        },
        {
          intro h3,
          rw h3 at *,
          exact (h h2),
        }
     },
     {
       intros h3,
       cases h3 with h4 h5,
       cases h4 with h6 h7,
       {
         exact h6,
       },
       {
         contradiction, 
       }
     }
  end

lemma single_equality: ∀ a b:M,(single a = single b ↔ a = b):=
  assume a b,
  begin
   rw (full_extensionality M (single a) (single b)),
   simp_rw (singleton1 M), 
   split,
   {
     intros h,
     specialize h a,
     apply h.mp,
     exact refl a,
   },
   {
     intros h,
     rw h at *,
     intros x,
     split,
     {
       intro h4,
       exact h4,
     },
     {
       intro h4,
       exact h4, 
     }
   }
  end

lemma usc_members: ∀ u x:M,(single u ∈ USC x ↔ u ∈ x):=
  assume u x,
  begin
    have h3:= usc M x, 
    specialize h3 (single u),
    rw h3,
    split,
      {
        intro h4,
        cases h4 with a h5,
        rw (single_equality M) at h5,
        cases h5 with h6 h7,
        rw h7,
        exact h6,
      },
      {
        intro h4,
        use u,
        rw (single_equality M),
        split,
          {exact h4,
          },
          {
            refl, 
          }
      }
  end

lemma lemma5d: ∀ x:M,((USC x) ∈ DECIDABLE M → x ∈ DECIDABLE M):=
  assume x h,
  begin
   rw (decidable_members M) at *,
   intros u v h2,
   specialize h (single u) (single v),
   repeat{ rw (usc_members M) at h },
   repeat{ rw (single_equality M) at h},
   exact (h h2),
  end

lemma lemma5e: ∀ x c:M,(x ∈ DECIDABLE M →  c ∈ x → (x - single c) ∪ single c = x):=
  assume x c h h2,
  begin
    rw (full_extensionality M),
    intro z,
    rw binary_union_axiom,
    rw (minus_members M),
    rw (singleton1 M),
    split,
     { 
       intro h4, 
       cases h4,
        {
          exact h4.left, 
        },
        {
          rw h4,
          exact h2,
        },
     },
     { 
       intro h3,
       rw (decidable_members M) at h,
       specialize h z c,
       have h4:= h ⟨ h3, h2⟩, 
       cases h4 with h5 h6,
       {
         right,
         exact h5, 
       },
       {
         left,
         exact ⟨ h3, h6⟩, 
       }
     }
  end

lemma lemma5f: adjoin_closed M (W5 M):=
    begin
      unfold adjoin_closed,
      intros z w,
      rw (W5_members M z),
      rw (W5_members M (z ∪ (single w))), 
      intro h2, 
      cases h2 with h3 h4, 
      cases h3 with h5 h6, 
      have h6copy2:=h6, 
      have h7: (adjoin_closed M) (FINITE M) := finite_adjoin_closed M,
      unfold adjoin_closed at h7,
      split,
        { 
          exact h7 z w ⟨ h5, h4⟩, 
        },
        { 
          intro x,
          intro h8,
          have h9: single w ⊆ USC x :=
            begin 
              rw (subset_definition   (single w)  (USC x)),
              intros p h10,
              rw (singleton1 M p w) at h10,
              rw (full_extensionality M (z ∪ (single w))(USC x)) at h8,
              specialize h8 p,
              rw (binary_union_axiom z (single w) p) at h8,
              rw (singleton1 M p w) at h8,
              apply h8.mp,
              right, 
              exact h10, 
            end,
          have h10:∃ c:M,(c ∈ x ∧ w = single c):= singleton_subset_usc M w x h9,
          cases h10 with c h11, 
          cases h11 with h12 h13,
          specialize h6 (x-w),
          have h6copy := h6,
          rw h13 at h6,
          rw (usc_dif M x c h12) at h6,
          rw← h13 at h6,  
          have h14:z = USC x - single w :=
            begin 
              rw← h8, 
              rw←  (cupminus M z w h4), 
            end,
          have h15: x - w ∈ FINITE M:= (h6 h14),
          rw h13 at h15,
          have h16: ¬(c ∈ (x- single c)):=
            begin
              intro h17,
              rw (minus_members M x (single c) c) at h17,
              rw (singleton1 M c c) at h17,
              cases h17 with h18 h19,
              contradiction,
            end,
          have h19: (x - single c) ∪ single c ∈ FINITE M:=
            begin
              exact (finite_adjoin M (x-single c) c (and.intro h15 h16)),
            end,
          rw h13 at h14, 
          rw← (usc_dif M x c h12) at h14, 
          have h80: (USC x ∈ DECIDABLE M):=
            begin
               have h81:= finite_adjoin M z w (and.intro h5 h4), 
               rw h8 at h81,
               have h82:= finitedecidable M (USC x) h81, 
               exact h82, 
            end,
          have h83: x ∈ DECIDABLE M:= lemma5d M x h80,
          have h84: (x - single c) ∪ single c = x:= lemma5e M x c h83 h12,
          have h85:= finite_adjoin M (x - (single c)) c (and.intro h15 h16),
          rw (lemma5e M x c h83 h12) at h85,
          exact h85,
        }
    end

lemma usc_is_empty:∀ x:M, (USC x = Λ ↔ x = Λ):=
  assume x,
  begin
    split,
    {
      intro h,
      rw (full_extensionality M) at *,
      intro z, 
      specialize h (single z), 
      rw (usc_members M z x) at h,
      rw h,
      have h2:= emptyset_axiom z ,
      have h3:= emptyset_axiom (single z),
      split,
      {
        intro h4,
        contradiction,
      },
      {
        intro h4,
        contradiction,
      }
    },
    {  intro h, 
      rw (full_extensionality M),
      intro z, 
       rw (usc M x z), 
       rw h,
       split,
       {
         intro h3,
         cases h3 with a h4,
         have h24:= emptyset_axiom a,
         cases h4 with h5 h6,
         contradiction,
       },
       {  intro h7,
          have h25:= emptyset_axiom z,
          contradiction,
       }
    }
  end

lemma symmetry_test: ∀ a b:M, (a=b → b = a):=
 begin 
  intros a b h,
  symmetry,
  exact h,
 end

lemma lemma5g: Λ ∈ (W5 M):=
  begin
    rw (W5_members M),
    split,
    {
      exact (lambda_finite M), 
    },
    {
      intros x h,
      have h4:= symmetry_test M Λ (USC x) h,
      rw (usc_is_empty M x) at h4,
      rw h4,
      exact (lambda_finite M),
    }
  end

lemma lemma5h: ∀ y:M, (y ∈ FINITE M → y∈ FINITE M ∧ ∀ x:M,(y = (USC x) → x ∈ FINITE M)) :=
   assume y,
   begin
      intro h,
      rw← (W5_members M y), 
      have h2: FINITE M ⊆ W5 M  := finite_conditions M (W5 M) (lemma5f M)(lemma5g M),
      rw (subset_definition (FINITE M) (W5 M)) at h2,
      specialize h2 y,
      exact (h2 h),  
   end 

lemma lemma5_left_to_right: ∀ x:M,(USC x ∈ FINITE M → x ∈ FINITE M):=
  assume x h,
  begin
   have h2:= lemma5h M (USC x) h,
   cases h2 with h3 h4,
   specialize h4 x,
   apply h4,
   reflexivity,
  end

lemma lemma5i: adjoin_closed M (W5b M):=
  begin
    unfold adjoin_closed,
    intros x c, 
    rw (W5b_members M x),
    intro h,
    rw (W5b_members M (x ∪ single c)),
    cases h with h2 h3,
    cases h2 with h4 h5,
    split,
      {
       exact finite_adjoin M  x c (and.intro h4 h3), 
      },
      { 
        rw (usc_cup M x c h3), 
        apply (finite_adjoin M),
        split,
         { exact h5,
         },
         {
           intro h6,
           rw (usc_members M c x) at h6, 
           contradiction,
         }
      }
  end

lemma usc_lambda:  ((USC Λ) = (Λ:M)):=
  begin 
    rw (usc_is_empty M Λ),
  end

lemma lemma5j: Λ ∈ W5b M :=
  begin
    rw (W5b_members M),
    split,
      { exact (lambda_finite M),
      },
      {
        rw (usc_lambda M), 
        exact (lambda_finite  M), 
      },
  end 

lemma lemma5_right_to_left:∀ x:M,( x ∈ FINITE M → USC x ∈ FINITE M):=
  assume x,
  begin
    have h: (FINITE M)⊆ W5b M := (finite_conditions M) (W5b M)   (lemma5i M) (lemma5j M),
    rw (subset_definition) at h,
    specialize h x,
    rw (W5b_members M) at h, 
    intro h3,
    exact (h h3).right, 
  end 

lemma uscfinite: ∀ x:M,(  USC x ∈ FINITE M ↔ x ∈ FINITE M):=
  assume x,
   begin
     split,
     {
       exact (lemma5_left_to_right M x),
     },
     {
      exact (lemma5_right_to_left M x),
     }
   end

lemma union_associative: ∀ (a b c:M), ((a ∪ b) ∪ c) = (a ∪ (b ∪ c)):= 
  assume a b c,
  begin
    rw (full_extensionality M), 
    intro x,
    repeat{rw binary_union_axiom,},
    rw or_assoc, 
  end

lemma intersection_associative: ∀ (a b c:M), ((a ∩  b) ∩  c) = (a ∩  (b ∩  c)):= 
  assume a b c,
  begin
    rw (full_extensionality M), 
    intro x,
    repeat{rw intersection_axiom,},
    rw and_assoc,
  end


lemma union_commutative: ∀ (a b:M), ((a ∪ b) = (b ∪ a)) :=
  assume a b,
  begin
    rw (full_extensionality M),
    intro x,
    repeat{rw binary_union_axiom},
    rw or_comm,
  end 

lemma intersection_commutative: ∀ (a b:M), ((a ∩  b) = (b ∩  a)) :=
  assume a b,
  begin
    rw (full_extensionality M),
    intro x,
    repeat{ rw intersection_axiom}, 
    rw and_comm,
  end 

lemma lemma6a: Λ ∈ (W6 M):=   -- line 160 of the paper
  begin
   rw (W6_members M Λ),
   split,
    { exact (lambda_finite M),
    },
    {
      intros y h h2,
      rw (lambda_cup M y),
      exact h,
    }
  end 

lemma lemma6b: adjoin_closed M (W6 M):=
  begin
    unfold adjoin_closed,
    intro Z,
    rw (W6_members M Z),
    intro b,
    rw (W6_members M (Z ∪ single b)),
    intro h,
    cases h with h2 h3,
    cases h2 with h4 h5,
    split,
     {
       exact (finite_adjoin M Z b (and.intro h4 h3)), 
     },
     { intros Y h6 h7,
       have h5copy := h5,
       specialize h5 (single b),
       have h8:= singleton_finite M b,
       have h9:= (h5 h8), 
       specialize h5copy (Y ∪ single b),
       have h10: ¬ (b ∈ Y):=        --line 162 of the paper 
         begin
           have h7copy:= h7,
           rw (full_extensionality M) at h7copy,
           specialize h7copy b, 
           rw (intersection_axiom (Z ∪ single b) Y b) at h7copy, 
           rw (binary_union_axiom Z (single b) b) at h7copy,  
           rw (singleton1 M b b) at h7copy,
           simp at h7copy,
           rw h7copy,
           exact (emptyset_axiom b), 
         end,
       have h11:= finite_adjoin M Y b (and.intro h6 h10),   -- line 162 of the paper
       have h12:= (h5copy h11), 
       have h13:= union_associative M Z Y (single b), 
       have h14: ((Z ∪ single b) ∩ Y) = (Z ∩ (Y ∪ single b)) :=  
          begin
            rw (full_extensionality M),
            intro x,
            split,
              { repeat{ rw intersection_axiom},
                repeat{ rw binary_union_axiom},
                rw (singleton1 M x b),
                intro h14,
                cases h14 with h15 h16,
                split,
                  {
                    cases h15 with h18 h19,
                    {
                      exact h18,
                    },
                    {
                      rw h19 at *,
                      contradiction,
                    }
                  },
                  {
                    left,
                    exact h16,
                  }
              },
              { repeat{ rw intersection_axiom},
                repeat{ rw binary_union_axiom},
                repeat{ rw (singleton1 M)},
                intro h17,
                split,
                {
                  left,
                  exact h17.left,
                },
                {
                  cases h17 with h18 h19,
                  cases h19 with h20 h21,
                  {
                    exact h20,
                  },
                  {
                    rw h21 at *,
                    contradiction,
                  }
                }
              }
          end,    
        rw h14 at h7,
        have h18:= (h12 h7),
        rw (union_associative M),
        rw (union_commutative M (single b) Y),
        exact h18,
     },
  end

lemma union:(∀ (X Y:M), X∈ FINITE M → Y ∈ FINITE M → X ∩ Y = Λ → X ∪ Y ∈ FINITE M):=
  assume X Y,
  begin
    have h: (FINITE M)⊆ W6 M := (finite_conditions M) (W6 M)   (lemma6b M) (lemma6a M),
    rw (subset_definition) at h, 
    specialize h X,
    rw (W6_members M) at h, 
    intros h30,
    exact (h h30).right Y, 
  end 

lemma maps_to_empty: ∀ (f y:M), maps M f y Λ → y = Λ :=
   assume f y h,
   begin
     unfold maps at h,
     cases h with h2 h3,
     cases h3 with h4 h5,
     cases h5 with h6 h7,
     rw (full_extensionality M),
     intro x,
     split,
       {
         intro h8,
         specialize h7 x,
         have h9:=  (h7 h8),
         cases h9 with p h10,
         cases h10 with h11 h12,
         have h13:= emptyset_axiom p,
         contradiction,
       },
       {
         intro h14,
         have h15:= emptyset_axiom x,
         contradiction,
       }
   end

lemma lemma9a: Λ ∈ (W9 M):=   -- line 160 of the paper
  begin
   rw (W9_members M Λ),
   split,
    { exact (lambda_finite M),
    },
    { 
      intros y h, 
      unfold similar at h, 
      cases h with f h2,
      unfold similarity at h2,
      cases h2 with h3 h4,
      unfold oneone at h3,
      cases h3 with h5 h6,
      have h7:= maps_to_empty M f y h5, 
      rw h7,
      exact (lambda_finite M),
    }
  end 

lemma similar_decidable: ∀ x y:M,  similar M x y → x ∈ DECIDABLE M → y ∈ DECIDABLE M:= 
-- Lemma 7 in the paper 
  assume x y,
  begin
    intros h1 h2,
    unfold similar at h1,
    cases h1 with f h3,
    unfold similarity at h3,
    cases h3 with h4 h5,
    rw (decidable_members M),
    rw (decidable_members M) at h2,
    intros u v,
    unfold onto at h5,
    have h5copy := h5,
    specialize h5 u,
    specialize h5copy v,
    intro h6,
    cases h6 with h7 h8,
    have h9:= (h5 h7),
    have h10:= (h5copy h8),
    cases h9 with p h11,
    cases h10 with q h12,
    specialize h2 p q,
    have h13:= h2 (and.intro h11.left h12.left),
    unfold oneone at h4,
    cases h4 with h14 h15,
    unfold maps at h14,
    cases h14 with h16 h17,
    cases h17 with h18 h19,
    cases h19 with h20 h21,
    cases h13,
      {
        rw h13 at *,
        left,
        specialize h20 q u v,
        apply h20,
        cases h12 with h21 h22,
        exact ⟨ h11.left, h11.right, h22⟩, 
      },
      { 
        right,
        intro h21,
        rw h21 at *,
        cases h15 with h22 h23,
        specialize h22 p q v,
        cases h11 with h25 h26, 
        cases h12 with h27 h28,
        have h29:= h22 ⟨ h26,h28,h25⟩,
        contradiction,
      }  
  end

lemma use_symmetry:∀ (a b:M), a=b → b = a:=
  assume a b,
  begin
    intro h,
    symmetry,
    exact h, 
  end

lemma cinzcupsinglec: ∀(c z:M), c ∈ z ∪ single c:=
   assume c z,
   begin
     rw binary_union_axiom,
     rw (singleton1 M),
     right,
     refl, 
   end

lemma lemma8:∀ (z y c q f:M), ¬ c ∈ z → ‹ c,q› ∈ f → similarity M f (z ∪ single c) y → similarity M f z (y- single q):=
  assume z y c q f,
  begin
    rintros h90 h3 h51, 
    unfold similarity at h51,
    cases h51 with h11 h52,
    unfold oneone at h11,
    rcases h11 with ⟨ h53, h54, h55⟩,
    unfold similarity,
    split,
      {
        unfold oneone,
        unfold maps,
        unfold maps at h53,
        unfold onto at h52,
        rcases h53 with ⟨h154,h155,h56⟩,
        repeat{split},
          { exact h154,},
          { 
            intros u v h24,
            cases h24 with h25 h26,
            rw (minus_members),
            cases h56 with h17 h18,
            split, 
              { specialize h18 u,
                rw binary_union_axiom at h18,
                  have h27: u ∈ z ∨ u ∈ (single c):=
                    begin
                      left,
                      exact h25,
                    end,
                  have h28:= h18 h27,
                  cases h28 with v1 h29,
                  cases h29 with h30 h31,
                  rw← binary_union_axiom at h27,
                  have h32:= h17 u v v1 (and.intro h27 (and.intro h26 h31)),
                  rw h32,
                  exact h30,
              },
              {
                rw singleton1 M,
                intro h33,
                rw h33 at *, 
                specialize h54 c u q, 
                have h36: c=u :=
                  begin
                  rw binary_union_axiom at h54,
                  rw (singleton1 M) at h54,
                  apply h54, 
                  split,
                  {
                    exact h3,
                  },
                  {
                    exact ⟨ h26, or.inr (refl c)⟩, 
                  }
                  end,
                rw h36 at *,
                 contradiction, 
              }
          },
          {
            intros p q r, 
            cases h56 with h57 h58,
            specialize h57 p q r, 
            rw binary_union_axiom at h57,
            intros h60,
            apply h57,
            split,
            {
              left,
              exact h60.left, 
            },
            {
              exact h60.right, 
            }
          },
          {
            intros u h60,
            cases h56 with h57 h58,
            specialize h58 u,
            have h59:(u ∈ z ∪ single c):=
              begin
                rw (binary_union_axiom),
                left,
                exact h60,
              end,
            have h61:= (h58 h59),
            cases h61 with fu h62,
            cases h62 with h63 h64,
            use fu,
            split,
            { 
              rw (minus_members M),
              split,
              { 
                exact h63,
              },
              {
                rw (singleton1 M),
                intro h65,
                rw h65 at *,
                have h66:c ∈ z ∪ (single c):=
                  begin
                    rw binary_union_axiom,
                    right,
                    rw (singleton1 M),
                  end,
                specialize h54 u c q,
                have h70:= h54 ⟨ h64, h3, h59⟩,
                rw h70 at *,
                contradiction,
              }
            },
            { 
              exact h64, 
            },

          },
          {
            intros p q r h70,
            specialize h54 p q r,
            rcases h70 with ⟨ h71, h72, h73 ⟩,
            have h74: p ∈ z ∪  (single c):=
              begin
                rw binary_union_axiom,
                left, 
                exact h73,
              end,
            apply h54, 
            exact ⟨ h71, h72, h74⟩, 
          },
          { 
            intros p r h80,
            specialize h55 p r,
            rw binary_union_axiom at h55,
            rw (singleton1 M) at h55,
            cases h80 with h81 h82,
            rw (minus_members M) at h82,
            rw (singleton1 M) at h82,
            cases h82 with h83 h84,
            have h85:= h52 r h83,
            cases h85 with b h86,
            specialize h54 b p r,
            cases h86 with h87 h88,
            have h89: b=p :=
              begin
                apply h54,
                exact ⟨ h88, h81, h87⟩,  
              end,
            rw binary_union_axiom at h87,
            rw h89 at *,
            rw (singleton1 M) at h87,
            cases h87 with h95 h96,
              {
                exact h95,
              },
              {
                rw h96 at *,
                cases h56 with h100 h101,
                specialize h100 c q r,
                rw binary_union_axiom at h100,
                rw (singleton1 M) at h100,
                simp at h100,
                have h102:= h100 h3 h81,
                have h108:= use_symmetry M q r h102,
                contradiction,
              }
          }          
      },
      {
        unfold onto at h52,
        unfold onto,
        intro v,
        specialize h52 v,
        rw (minus_members M),
        rw (singleton1 M),
        intro h60,
        cases h60 with h61 h62,
        have h63:= h52 h61,
        cases h63 with u h64,
        cases h64 with h65 h66,
        use u,
        rw binary_union_axiom at h65,
        rw (singleton1 M) at h65,
        split,
        {
          cases h65 with h70 h71,
          {
            exact h70,
          },
          {
            rw h71 at *,
            unfold maps at h53,
            rcases h53 with ⟨ h72, h73, h74, h75⟩,
            specialize h74 c q v,
            have h76:= cinzcupsinglec M c z,
            have h62: ¬(q=v):=
              begin
                intro h200,
                have h201:= use_symmetry M q v h200,
                contradiction, 
              end,
            have h80:= h74 ⟨ h76, h3, h66⟩, 
            contradiction,   
          }
        },
        { exact h66,
        }
      }
  end


lemma lemma9b: ∀(y q:M),  y ∈ DECIDABLE M → q ∈ y → y = (y-(single q) ∪ (single q)):=
  assume y q, 
  begin 
    intro h,
    intro h1,
    rw full_extensionality,
    assume x,
    rw binary_union_axiom,
    rw (singleton1 M),
    rw (minus_members M),
    rw (singleton1 M),
    rw (decidable_members M) at h,
     specialize h x q,
     split,
     {
       intro h2,
       have h3:= h (and.intro h2 h1),
       rw or_comm at h3,
       cases h3 with h5 h6,
         {
           left,
           exact (and.intro h2 h5),
         },
         { 
           right,
           exact h6,
         }   
     },
     {
       intro h7,
       cases h7 with h8 h9,
        {
          exact h8.left, 
        },
        {
          rw h9,
          exact h1,
        }
     }
  end

lemma singletons_finite: ∀ (x:M), single x ∈ FINITE M:=
  begin
    intro x,
    have h4:=finite_adjoin M Λ x,
    have h5:= lambda_cup M (single x),
    rw h5 at h4,
    apply h4,
    have h6:= emptyset_axiom x,
    exact ⟨ lambda_finite M, h6⟩, 
  end

lemma finite_structure: ∀ (z:M), z ∈ FINITE M →  z = Λ ∨ (∃ (x c:M), x ∈ FINITE M ∧ ¬ c ∈ x ∧ z = (x ∪ (single c))):=
  begin
    have base: Λ ∈ W_finite_structure M:=
      begin
        rw W_finite_structure_members,
        split,
        {
          exact lambda_finite M,
        },
        {
          left,
          refl,
        }
      end,
    have step: adjoin_closed M (W_finite_structure M):=
      begin
        unfold adjoin_closed,
        intros x c h,
        cases h with h2 h3,
        rw W_finite_structure_members at h2,
        rw W_finite_structure_members,
        cases h2 with h4 h5,
        cases h5 with h6 h7,
        {
          rw h6 at *,
          split,
          {
            have h8:= lambda_cup M (single c),
            rw h8,
            exact singleton_finite M c,
          },
          {
            right,
            use x, use c,
            rw h6 at *,
            simp,
            exact ⟨ h4, h3⟩, 
          }
        },
        {
          split,
          {
            have h10:= finite_adjoin M x c ⟨ h4, h3⟩,
            exact h10,
          },
          {
            right,
            use x, use c,
            simp,
            exact ⟨ h4, h3⟩, 
          }
        }
      end,
    have h:= finite_conditions M (W_finite_structure M) step base,
    rw subset_definition at h, 
    intros X h2, 
    specialize h X,
    rw (W_finite_structure_members M) at h, 
    have h5:= h h2, 
		cases h5 with h6 h7, 
    exact h7, 
  end

#axioms_all   --this file is clean.



      
 


  
