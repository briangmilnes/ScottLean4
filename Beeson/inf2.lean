import inf1 
variables (M:Type) [Model M] (a b x y z u v w X R W: M)

open Model 


lemma lemma9c: adjoin_closed M (W9 M):=
  begin
    unfold adjoin_closed, 
    intros z c,
    rw (W9_members M),
    intro h,
    cases h with h2 h3,
    cases h2 with h4 h5,
    rw (W9_members M),
    have h6:= finite_adjoin M z c (and.intro h4 h3),
    split,
      { exact h6,
      },
      {
        have h7:= finitedecidable M (z ∪ single c) h6,
        intros y h8,
        have h9:=  similar_symmetric_left_right  M y (z ∪ single c) h8,
        have h10:= similar_decidable M (z ∪ single c) y h9 h7,  -- Y ∈ DECIDABLE M, line 172
        unfold similar at h9,
        cases h9 with f h10,
        have h110:= h10, 
        unfold similarity at h10,
        cases h10 with h11 h12,
        unfold oneone at h11,
        cases h11 with h13 h14,
        unfold maps at h13,
        rcases h13 with ⟨ h15, h16, h17, h18 ⟩,
        have h19:= h18,
        specialize h19 c,
        rw binary_union_axiom at h19,
        rw (singleton1 M c) at h19,
        simp at h19,
        cases h19 with q h20,
        cases h20 with h21 h22, 
        have h23: similarity M f z (y- (single q)):= lemma8 M z y c q f h3 h22 h110,
        have h24: y-single q ∈ FINITE M:=  --line 182 page 7
           begin
             specialize h5 (y- single q), 
             apply h5,
             apply similar_symmetric_left_right M z (y-single q),
             unfold similar,
             use f,
             exact h23,
           end,
        have h25:= lemma9b M y q h10 h21,
        have h26:= finite_adjoin M (y- (single q)) q,
        rw← h25 at h26,
        have h27: ¬ (q ∈ y - (single q)):=
          begin
            intro h28,
            rw (minus_members M) at h28,
            rw (singleton1 M) at h28,
            cases h28 with h29 h30,
            exact (h30 (refl q)),
          end ,
        apply h26,
        exact ⟨ h24, h27⟩,       
      }
  end

lemma finitesimilar: ∀ (x y:M), (similar M x y) → x ∈ FINITE M → y ∈ FINITE M:=
  assume x y,
  begin
    have h: (FINITE M)⊆ W9 M := (finite_conditions M) (W9 M)   (lemma9c M) (lemma9a M),
    rw (subset_definition) at h, 
    specialize h x,
    rw (W9_members M) at h,
    intros h2 h3,
    have h4:= (similar_symmetric_left_right M x y h2),
    have h5:= h h3,
    cases h5 with h6 h7,
    specialize h7 y,
    exact (h7 h4), 
  end

lemma separable_subset_to_separable: ∀ (x y:M), separable_subset M x y ↔ x ⊆ y ∧ separable M x y:=
  assume x y,
  begin
   unfold separable_subset,
   unfold separable,
  end

lemma separable1: ∀ (u x:M), u ⊆ x → ( separable M u x ↔  ∀ z, (z ∈ x → z ∈ u ∨  ¬ (z ∈  u))):=
  assume u x,
  begin 
    intro h,
    unfold separable, 
     rw full_extensionality, 
     simp_rw  binary_union_axiom, 
     simp_rw minus_members M, 
     split,
     {
       intros h2 z,
       specialize h2 z,
       rw subset_definition at h,
       specialize h z,
       intro h3, 
       have h4:= h2.mp h3,
       cases h4 with h5 h6,
       {
         left,
         exact h5,
       },
       {
         cases h6 with h7 h8,
         right,
         exact h8, 
       }
     },
     { intros h2 z,
       specialize h2 z,
       rw subset_definition at h,
       specialize h z,
       split,
         {
           intro h4,
           have h5 := h2 h4,
           cases h5 with h6 h7,
           left,
            { exact h6,
            },
            {
              right,
              exact (and.intro h4 h7),
            }
         },
         {
           intro h3,
           cases h3 with h4 h5,
           { 
             exact h h4,
           },
           {
             exact h5.left, 
           }
         }
     }  
  end 

lemma ssc_members: ∀ (x u:M),( u ∈ SSC  x ↔ u ⊆ x ∧  ∀ y,(y ∈ x → y∈ u ∨ ¬ (y ∈ u))) := 
  assume x u,
  begin 
     rw ssc_definition,
     split,
     {
       intro h,
       cases h with h10 h11,
       split,
        { exact h10,
        },
        { 
          rw subset_definition at h10,
          rw full_extensionality at h11,
          intro y,
          specialize h11 y,
          specialize h10 y,
          rw binary_union_axiom at h11,
          rw minus_members M at h11,
          intro h12, 
          have h13:= h11.mp h12,
          cases h13 with h14 h15,
          {
            left,
            exact h14,
          },
          {
            right,
            exact h15.right, 
          }
        }
     },
     { intro h,
       cases h with h10 h11, 
       split,
       { 
         exact h10, 
       },
       {
         rw full_extensionality, 
         intro z,
         specialize h11 z,
         rw binary_union_axiom,
         rw minus_members M,
         rw subset_definition at h10,
         specialize h10 z,
         split,
         {
           intro h20,
           have h21:= h11 h20,
           cases h21 with h22 h23,
             {
               left,
               exact h22,
             },
             {
               right,
               exact (and.intro h20 h23),
             }
         },
         {
           intro h30, 
           cases h30 with h31 h32,
             {
               exact h10 h31,
             },
             { exact h32.left,
             }
         }
       }
     }
  end

lemma sc_members: ∀ (x u:M), u ∈ SC  x ↔ u ⊆ x := 
  assume x u,
  begin 
    rw sc_definition,
  end

lemma subset_of_empty: ∀ x:M, x ⊆ Λ ↔ x = Λ:= 
  assume x,
  begin
    rw subset_definition,
    rw full_extensionality,
    split,
     {
       intros h z,
       specialize h z,
       split,
         { 
           exact h,
         },
         {
           intro h1,
           have h2:= emptyset_axiom z,
           contradiction,
         }
     },
     { intro h,
       intro z,
       specialize h z,
       cases h with h2 h3,
       exact h2,
     }
  end

lemma ssc_empty: SSC Λ = single (Λ:M)   := 
  begin 
    rw full_extensionality,
    intro x,
    rw ssc_members,
    rw (subset_of_empty M x),
    split,
      {
        intro h,
        cases h with h2 h3,
        rw h2 at *,
        rw (singleton1 M Λ), 
      },
      {
        rw (singleton1 M x Λ ),
        intro h,
        rw h,
        simp,
        intros y,
        intro h3,
        left,
        exact h3,
      }
  end

lemma lemma10a: Λ ∈ W10 M:=
  begin
    rw (W10_members),
    rw ssc_empty, 
    exact (and.intro (lambda_finite M) (singleton_finite M Λ )), 
  end

lemma adjoin_oneone: ∀(c u v:M), (u ∪ (single c)) = (v ∪ (single c)) → ¬ (c ∈ u) → ¬ (c ∈ v) → u = v:=
  assume c u v,
  begin
    intros h1 h2 h3,
    rw (full_extensionality M) at h1,
    rw full_extensionality,
    intro x,
    specialize h1 x,
    repeat{ rw binary_union_axiom at h1},
    repeat{ rw (singleton1 M x c)  at h1},
    split,
      {
        intro h4,
        have h5: ¬ (x=c):= 
          begin
            intro h6,
            rw h6 at h4,
            exact (h2 h4), 
          end,
        cases h1 with h6 h7,
        have h8:= h6 (or.inl h4),
        cases h8 with h9 h10,
        {
          exact h9,
        },
        {
          contradiction,
        }
      },
      {
         intro h4,
        have h5: ¬ (x=c):= 
          begin
            intro h6,
            rw h6 at h4,
            exact (h3 h4), 
          end,
        cases h1 with h6 h7,
        have h8:= h7 (or.inl h4), 
        cases h8 with h9 h10,
        {
          exact h9,
        },
        {
          contradiction, 
        }
      },
  end

lemma subset_decidable: ∀(v x:M), v ⊆ x → x ∈ DECIDABLE M → v ∈ DECIDABLE M:=
  assume v x,
  begin
    intros h1 h2,
    rw subset_definition at h1,
    rw decidable_members M,
    intros p q,
    intro h3,
    cases h3 with h4 h5,
    have h6:= h1 p h4,
    have h7:= h1 q h5,
    rw decidable_members M at h2,
    specialize h2 p q,
    exact h2 (and.intro h6 h7),
  end

lemma minuscup:∀ (v c:M), c ∈ v →  v ∈ DECIDABLE M → v = ((v - (single c)) ∪ (single c)):=
  assume v c,
  begin
    intros h1 h2,
    rw decidable_members at h2,
    rw full_extensionality,
    intro x,
    specialize h2 x c,
    rw binary_union_axiom,
    rw minus_members M,
    rw (singleton1 M x c),
    split,
    {
      intro h3,
      have h4:= h2 (and.intro h3 h1),
      cases h4 with h5 h6,
      {
        right,
        exact h5, 
      },
      {
        left,
        exact (and.intro h3 h6), 
      },
    },
    {
      intro h3,
      cases h3 with h4 h5,
      {
        exact h4.left, 
      },
      {
        rw h5,
        exact h1, 
      }
    }
  end 

lemma subset_union: ∀ (x a b:M), x ⊆ a → x ⊆ (a ∪ b) :=
  assume x a b,
  begin 
    intro h,
    rw subset_definition at h,
    rw subset_definition,
    intro z,
    intro h2,
    specialize h z,
    rw binary_union_axiom,
    have h3:= h h2,
    left,
    exact h3,
  end

lemma subset_reflexive: ∀ a:M, a ⊆ a:=
  assume a,
  begin
    rw subset_definition,
    intro z,
    intro h,
    exact h,
  end

lemma subset_transitive: ∀ (a b c:M), a ⊆ b → b ⊆ c → a ⊆ c:=
  assume a b c,
  begin
    intros h1 h2,
    rw subset_definition at *,
    intro z,
    specialize h1 z,
    specialize h2 z,
    intro h4,
    exact (h2 (h1 h4)),
  end

lemma subset_union2: ∀ (a b:M), a ⊆ a ∪ b:=
  λ a b, subset_union M a a b (subset_reflexive M a)

lemma ssc_adjoin: ∀ (x c:M), ¬ (c ∈ x) → (SSC x) ⊆ (SSC (x ∪ (single c))):=
  assume x c,
  begin
    intro h,
    rw subset_definition,
    intro z,
    repeat{ rw ssc_members M},
    intro h2,
    cases h2 with h3 h4,
    split,
    { 
      exact (subset_union M z x (single c) h3), 
    },
    { 
      intros y h5, 
      specialize h4 y,
      rw binary_union_axiom at h5,
      rw (singleton1 M) at h5,
      cases h5 with h6 h7,
      {
        exact (h4 h6), 
      },
      {
        rw h7 at *,
        right,
        rw subset_definition at h3,
        specialize h3 c,
        intro h5,
        have h6:=  h3 h5, 
        contradiction,
      },   
    }
  end

lemma cap_comm: ∀ (a b:M), ((a ∩ b) = (b ∩ a)):=
  assume a b,
  begin
    rw full_extensionality,
    intro t,
    repeat{ rw intersection_axiom},
    split,
    {
      intro h,
      exact ⟨ h.right, h.left ⟩, 
    },
    {
      intro h,
      exact ⟨ h.right, h.left⟩, 
    }
     
  end 

lemma lemma10b: adjoin_closed M (W10 M):=
  begin
    rw adjoin_closed,
    intros x c h,
    cases h with h2 h3,
    rw (W10_members M) at *,
    cases h2 with h4 h5,
    set f:M :=  f10 M x c with h6,
    set A:M := range f with h7, 
    split,
    {
      exact (finite_adjoin M x c (and.intro h4 h3)),
    },
    { 
      have h100: maps M f (SSC x) A:=
        begin
          unfold maps,
          have h20:Rel f:=
            begin
              rw Rel_definition,
              intro z,
              intro h8,
              rw h6 at h8,
              rw (f10_members M) at h8,
              cases h8 with u h9,
              cases h9 with y h10,
              cases h10 with h11 h12,
              use u, use y,
              exact h11,    
            end, 
          repeat{ split} , 
            { 
              exact h20,
            },
            { 
              intros u y,
              rw h7,
              rw h6,
              rw range_axiom,
                { intro h8,
                  use u,
                  exact h8.right, 
                },
                { 
                  rw h6 at h20,
                  exact h20,
                }
            },
            {
              intros u y z,
              rw h6,
              rw f10_members,
              intro h30,
              rcases h30 with ⟨ h31, h32,h33⟩,
              rw (f10_members) at h33, 
              cases h32 with u1 h34,
              cases h34 with y1 h35,
              cases h33 with u2 h36,
              cases h36 with y2 h37,
              rw (ordered_pair_equality M) at h35,
              rw (ordered_pair_equality M) at h37,
              rcases h35 with ⟨ h38, h39, h40⟩,
              cases h38 with h41 h42,
              rw← h41 at *,
              rw← h42 at *,
              rcases h37 with ⟨ h43, h44, h45⟩,
              cases h43 with h46 h47,
              rw← h46 at *,
              rw← h47 at *,  
              rw h45,
              rw h40, 
            },
            { 
              intros u h50,
              rw h7,
              rw full_extensionality at h7,
              rw h6 at h7,
              use u ∪ (single c),
              rw range_axiom,
                { use u,
                    { 
                      rw h6,
                      rw f10_members,
                      use u,
                      use u ∪ (single c), 
                      split,
                      {
                        exact refl  ‹ u,u ∪ single c ›,
                      },
                      { 
                        split,
                        {
                          exact h50,
                        },
                        {
                          exact refl (u ∪ (single c)), 
                        }
                      }
                     
                    },
                    { rw h6,
                      rw f10_members,
                      use u,
                      use u ∪ (single c), 
                      split,
                      {
                        exact refl ‹ u, u ∪ (single c)›,
                      },
                      {
                        split,
                        { 
                          exact h50, 
                        },
                        {
                          exact refl (u ∪ (single c)), 
                        }
                      }
                    }
                },
                { 
                  exact h20,
                }
            }        
        end, 
      have h101: (oneone M f (SSC x) A):=
        begin
          have h8:= h100,
          rw maps at h8,
          rcases h8 with ⟨ h9, h10, h11, h12⟩,
          rw oneone,
          repeat{split},
            { 
              exact h9,         
            },
            { exact h10,
            },
            {
              exact h11,
            },
            {
              exact h12,
            },
            { 
              intros p q y,
              rw h6,
              rw (f10_members),
              intro h13, 
              rcases h13 with  ⟨ h14, h15, h16⟩, 
              cases h14 with u h17, 
              cases h17 with y1 h18,
              rcases h18 with ⟨ h19, h20, h21⟩, 
              rw (ordered_pair_equality M u y1 p y) at h19,
              cases h19 with h22 h23,
              rw← h22 at *,
              rw← h23 at *,
              rw (f10_members) at h15, 
              rcases h15 with ⟨ u,y1, h24, h25, h26⟩,
              rw (ordered_pair_equality M u y1 q y) at h24,
              cases h24 with h27 h28,
              rw← h27 at *,
              rw← h28 at *,
              rw ssc_members at h16,
              cases h16 with h29 h30,
              rw subset_definition at h29,
              specialize h29 c,
              have h30: ¬ (c ∈ p):= λ h, (h3 (h29 h)),
              rw ssc_members at h25,
              cases h25 with h32 h33,
              rw subset_definition at h32,
              specialize h32 c,
              have h31: ¬ (c ∈ q):= λ h, (h3 (h32 h)),
              rw h21 at h26,
              exact (adjoin_oneone M c p q h26 h30 h31),
            },
            {
              intros p y h40,
              cases h40 with h41 h42,
              rw h6 at h41,
              rw f10_members at h41,
              cases h41 with h h43,
              cases h43 with z h44,
              rcases h44 with ⟨ h45, h46, h47⟩,
              rw (ordered_pair_equality M h z p y) at h45,
              cases h45 with h48 h49,
              rw←  h48 at h46,
              exact h46,
            },
        end, 
      have h102:(onto M f (SSC x) A):=
        begin
          rw onto,
          intro y,
          intro h8,
          rw h7 at h8,
          rw range_axiom at h8,
          cases h8 with u h9,
          use u, 
          { split, 
            {
              rw h6 at h9,
              rw (f10_members M) at h9,
              rcases h9 with ⟨ u1, y1, h10, h11 ⟩,
              rw (ordered_pair_equality M u1 y1 u y) at h10,
              cases h10 with h12 h13,
              rw← h12 at *,
              rw← h13 at *,
              exact h11.left, 
            }, 
            {
              exact h9, 
            }
          },
          {
            unfold maps at h100,
            cases h100 with h39 h40,
            exact h39,
          }, 
        end, 

      have h103:(similar M (SSC x) A):=      --line 204 of the paper 
        begin
          unfold similar,
          use f,
          unfold similarity,
          exact (and.intro h101 h102), 
        end,
      
      have h104: (SSC x) ∈ DECIDABLE M:=  finitedecidable M (SSC x) h5, -- line 205  
      have h105: A ∈ DECIDABLE M:=  similar_decidable M (SSC x) A h103 h104, --  line 206  
      have h106: A ∈ FINITE M:=  finitesimilar M (SSC x) A h103 h5, --  line 207 of the paper 
      have h107: SSC (x ∪ (single c)) = (A ∪ (SSC x)):=  -- equation (8), line 208 
        begin 
          rw full_extensionality, 
          intro v,
          rw (ssc_members M),
          split,
          {   -- line 210 
            intro h8,   --starting the left-to-right direction, line 211 
            cases h8 with h9 h10, 
            have h10copy := h10, 
            specialize h10 c, 
            have h11:= h10 (cinzcupsinglec M c x), 
            cases h11 with h12 h13, 
            { --the case c ∈ v 
              rw binary_union_axiom, 
              left,  -- we will show v ∈ A
              have h13:x ∪ (single c) ∈ FINITE M:= finite_adjoin M x c (and.intro h4 h3),
              have h14:x ∪ (single c) ∈ DECIDABLE M:= finitedecidable M (x ∪ single c) h13,
              have h15:v ∈ DECIDABLE M:= subset_decidable M v (x ∪ single c) h9 h14, 
              have h24:v = ((v- (single c)) ∪ (single c)):=   -- line 212 
                begin
                  rw full_extensionality,
                  intro u,
                  rw decidable_members M at h15, 
                  specialize h15 u c,
                  split,
                  {
                    rw binary_union_axiom,
                    rw (minus_members M),
                    rw (singleton1 M),
                    intro h16,
                    have h17:= h15 (and.intro h16 h12),
                    rw or_comm at h17,
                    cases h17 with h18 h19,
                    {
                      left, 
                      exact (and.intro h16 h18), 
                    },
                    {
                      right, 
                      exact h19, 
                    },
                      
                  }, 
                  {
                    rw binary_union_axiom,
                    rw (minus_members M),
                    rw (singleton1 M u c),
                    intro h16,
                    cases h16 with h17 h18, 
                      { cases h17 with h19 h20,
                        exact h19, 
                      },
                      { 
                        rw h18 at *,
                        exact h12, 
                      },
                  }, 
                end, 
              have h25: v-(single c) ∈ SSC x:=  -- line 213
                begin 
                  rw (ssc_members M x (v-(single c))), 
                  split,
                  { rw subset_definition,
                    intro z,
                    rw (minus_members M),
                    rw (singleton1 M z c),
                    rw subset_definition at h9, 
                    specialize h9 z,
                    rw binary_union_axiom at h9,
                    rw (singleton1 M z c) at h9,
                    intro h30,
                    cases h30 with h31 h32,
                    have h33:= h9 h31,
                    cases h33 with h34 h35,
                    {
                      exact h34,
                    },
                    {
                      contradiction, 
                    }
                  },
                  { 
                    intro y, 
                    intro h25,
                    have h30:=h10copy y,
                    rw (binary_union_axiom) at h30,
                    rw (singleton1 M y c) at h30,
                    rw (minus_members M),
                    rw (singleton1 M y c), 
                    rw (decidable_members M) at h15, 
                    specialize h15 y c,
                    repeat { rw binary_union_axiom at h15}, 
                    have h20: y ∈ v ∨ ¬ y ∈ v:=
                      begin
                        exact h30 (or.inl h25), 
                      end,
                    cases h20 with h21 h22,
                    {
                      have h16:= h15 ⟨ h21, h12⟩, 
                      cases h16 with h23 h24,
                      {
                        right,
                        intro h25,
                        cases h25 with h26 h27,
                        contradiction,
                      },
                      {
                        left,
                        exact ⟨ h21, h24⟩, 
                      }
                    },
                    {
                      right,
                      intro h26,
                      cases h26 with h27 h28,
                      contradiction, 
                    } 
                  }
                end,
              rw h7,
              rw h6,
              rw range_axiom,
              { use (v - (single c)), 
                rw (f10_members M),
                use v - (single c), use v,
                repeat{split},
                 {
                   exact h25,
                 },
                 {
                   exact (minuscup M v c h12 h15), 
                 },
              }, 
              {
                rw Rel_definition,
                intro z,
                rw (f10_members M),
                intro h26,
                cases h26 with u h27,
                cases h27 with y h28,
                use u, use y,
                rcases h28 with ⟨ h29, h30, h31⟩, 
                exact h29,
              },
            },
            {  -- the case ¬ c ∈ v 
              rw binary_union_axiom,
              right,
              rw (ssc_members M),
              split,
              { 
                rw subset_definition,
                intro z,
                rw subset_definition at h9, 
                specialize h9 z, 
                rw binary_union_axiom at h9, 
                rw (singleton1 M ) at h9, 
                intro h20,
                have h21:= h9 h20,
                cases h21 with h22 h23,
                {
                  exact h22,
                },
                {
                  rw h23 at *,
                  contradiction,
                },

              },
              {
                intro y,
                intro h20,
                specialize h10copy y,
                rw binary_union_axiom at h10copy,
                exact (h10copy (or.inl h20)), 
              },
            },   
          },
          {  -- starting right-to-left direction, line 217 of the paper 
            intro h20, 
            rw binary_union_axiom at h20, 
            cases h20 with h21 h22,
            { -- the case v ∈ A,  line 218
               rw h7 at h21,
               rw range_axiom at h21, 
               rw h6 at h21, 
               cases h21 with p h22,
               rw (f10_members M) at h22,
               cases h22 with u h23,
               cases h23 with y h24,
               rcases h24 with ⟨ h25, h26, h27 ⟩, 
               have h26copy:=h26,
               rw (ordered_pair_equality M u y p v) at h25,
               cases h25 with h28 h29,
               rw h28 at *,
               rw h29 at *,
               { split,
                 {
                   rw (ssc_members M) at h26,
                   rw h27,
                   cases h26 with h30 h31,
                   rw subset_definition at h30,
                   rw subset_definition,
                   intro z,
                   specialize h30 z,
                   repeat{ rw binary_union_axiom},
                   repeat{ rw (singleton1 M z c)},
                   intro h32,
                   cases h32 with h33 h34,
                   {
                     left,
                     exact h30 h33, 
                   },
                   {
                     right,
                     exact h34,
                   }
                 },
                 {
                   intro z,
                   rw binary_union_axiom,
                   rw (singleton1 M z c),
                   intro h30,
                   rw (ssc_members M) at h26,
                   cases h26 with h31 h32,
                   rw h27,
                   specialize h32 z,
                   rw subset_definition at h31,
                   specialize h31 z,
                   repeat { rw binary_union_axiom},
                   repeat { rw (singleton1 M z c)},
                   cases h30 with h33 h34,
                   {
                     have h35: ¬ (z = c):= 
                       begin
                         intro h36,
                         rw← h36 at h3,
                         exact (h3 h33), 
                       end,
                    have h37:= h32 h33,
                    cases h37 with h38 h39, 
                    {
                      left,
                      exact (or.inl h38), 
                    },
                    { 
                      right,
                      intro h40,
                      cases h40 with h41 h42,
                      {
                        contradiction,
                      },
                      {
                        exact (h35 h42),
                      },
                    },
                   },
                   {
                     rw h34 at *,
                     left,
                     right,
                     refl, 
                   },
                 },
               },
               {
                 unfold maps at h100,
                 cases h100 with h101 h102, 
                 exact h101,
               },
            },
            { -- the case v ∈ SSC(x), line 220 
              have h107: (SSC x) ⊆ (SSC (x ∪ (single c))):= ssc_adjoin M x c h3, --line 220b
              rw subset_definition at h107, 
              specialize h107 v,
              have h23:= h107 h22,
              rw (ssc_members M) at h23,
              exact h23,       --line 222
            },
          },
        end,
      rw h107,
      have h8:= union M A (SSC x) h106 h5,
      have h9: (SSC x) ∩ A = Λ :=
       begin 
        rw (full_extensionality M),
        intro u,
        rw intersection_axiom,
        split,
        { 
          intro h38, 
          cases h38 with h39 h10,
          rw h7 at h10, 
          rw range_axiom at h10, 
          { rw h6 at h10,
            rw (ssc_members M) at h39,
            cases h39 with h11 h12, 
            cases h10 with p h13, 
            rw (f10_members M) at h13, 
            cases h13 with q h14,
            cases h14 with y h15,
            rcases h15 with ⟨ h16, h17, h18 ⟩,
            rw (ordered_pair_equality M q y p u) at h16,
            cases h16 with h19 h20,
            rw← h19 at *,
            rw← h20 at *,
            rw full_extensionality at h18,
            specialize h18 c,
            rw  binary_union_axiom at h18,
            rw (singleton1 M c c) at h18,
            cases h18 with h21 h22,
            have h23:= h22 (or.inr (refl c)),
            rw subset_definition at h11,
            specialize h11 c,
            have h24:= h11 h23, 
            contradiction,
          },
          {
            unfold maps at h100,
            cases h100 with h25 h26,
            exact h25, 
          }
        },
        {
          intro h40,
          have h41:= emptyset_axiom u,
          contradiction, 
        },
      end,
    rw cap_comm at h9,
    exact (h8 h9),
    }
  end

lemma finitepowerset: ∀ (x:M), x ∈ FINITE M →  SSC x ∈ FINITE M:=
  assume x,
  begin
    have h: (FINITE M)⊆ W10 M := (finite_conditions M) (W10 M)   (lemma10b M) (lemma10a M),
    rw (subset_definition) at h, 
    intro h2, 
    specialize h x,
    have h3:= h h2, 
    rw (W10_members M) at h3, 
    exact h3.right, 
  end
lemma subsets_to_equal: ∀(a b: M), a⊆b → b ⊆ a → a = b:=
  assume a b h1 h2,
  begin
    rw full_extensionality,
    rw subset_definition at h1 h2,
    intros x,
    have h3:= h1 x,
    have h4:= h2 x,
    split,
    {
      exact h3,
    },
    {
      exact h4,
    }
  end 

lemma subsets_to_equal2: ∀(a b: M), a⊆b ∧  b ⊆ a ↔ a = b:=
  begin
    intros a b,
    split,
    { intro  h,
      cases h with h2 h3,
      have h4:= subsets_to_equal M a b h2 h3,
      exact h4,
    },
    {
      intros h5,
      rw h5,
      have h6:= subset_reflexive M b,
      exact ⟨ h6, h6⟩,
    }
  end

#axioms_all  --This file is clean



