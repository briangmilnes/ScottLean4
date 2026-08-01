
import inf2
variables (M:Type) [Model M] (a b x y z u v w X R W: M)

open Model 



lemma empty_union_empty:((( Λ:M) ∪  (Λ:M)) = (Λ:M)):=
   begin
     rw (full_extensionality M),
     intro x,
     rw binary_union_axiom, 
     simp, 
   end

lemma empty_union_x: ∀ (x:M), (Λ ∪ x = x):=
  assume x,
  begin 
    rw full_extensionality,
    intro z,
    rw binary_union_axiom,
    have h:= (emptyset_axiom z), 
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

lemma x_union_empty: ∀ (x:M), (x ∪ Λ = x):=
  assume x,
  begin
    rw full_extensionality,
    intro z,
    rw binary_union_axiom,
    have h:= (emptyset_axiom z), 
    split,
    {
      intro h3,
      cases h3 with h4 h5,
      {
        exact h4,
      },
      {
        contradiction,
      }
    },
    {
      intro h5,
      left,
      exact h5, 
    }
  end

lemma x_union_x: ∀ (x:M), (x ∪ x) = x:=
  assume x,
  begin
    rw full_extensionality,
    intro t,
    rw binary_union_axiom, 
    simp, 
  end

lemma x_intersect_empty: ∀(x:M), (x ∩ Λ = Λ ):=
  assume x,
  begin
    rw full_extensionality,
    intro z,
    rw intersection_axiom,
    have h:= (emptyset_axiom z), 
    simp, 
    intro h3,
    contradiction,
  end

lemma empty_intersect_x: ∀(x:M), ( Λ ∩ x = Λ ):=
  assume x,
  begin
    rw full_extensionality,
    intro z,
    rw intersection_axiom,
    have h:= (emptyset_axiom z), 
    split,
    {
      intro h3,
      exact h3.left,
    },
    {
      intro h3,
      contradiction,
    }
  end

lemma x_minus_empty: ∀ (x:M), x-Λ = x:=
  assume x, 
  begin
    rw (full_extensionality M),
    intro z,
    rw (minus_members M), 
    have h:= (emptyset_axiom z), 
    split,
    {
      intro h3,
      exact h3.left,
    },
    {
      intro h3,
      exact ⟨ h3, h⟩, 
    }
  end

lemma x_minus_x: ∀ (x:M), x-x = Λ :=
  assume x,
  begin
    rw (full_extensionality M),
    intro z,
    rw (minus_members M), 
    have h2: ¬ z ∈ Λ := emptyset_axiom z,
    split,
    {
      intro h4,
      cases h4 with h5 h6,
      contradiction,
    },
    {
      intro h4,
      contradiction,
    }
  end

lemma empty_always_subset:∀ (x:M), Λ ⊆  x:=
  assume x,
  begin
    rw subset_definition,
    intro z,
    intro h,
    have h2:= emptyset_axiom z h,
    contradiction, 
  end

lemma minus_subset: ∀ (x a:M), x-a ⊆  x:=
  assume x a, 
  begin 
    rw subset_definition, 
    intro z, 
    rw (minus_members M),
    exact λ h, and.left h, 
  end


lemma union_subset: ∀ (a b c:M), (a ∪ b) ⊆ c → a ⊆ c  :=
  assume a b c,
  begin
    repeat{rw subset_definition}, 
    intro h,
    intro z,
    specialize h z,
    rw (binary_union_axiom) at h,
    intro h3,
    exact h (or.inl h3), 
  end

lemma my_subset_reflexive: ∀ (x:M), x ⊆ x:=
  assume x,
  begin
    rw subset_definition,
    intro z,
    exact λ h, h,
  end 

lemma empty_separable: ∀ x:M, separable_subset M Λ x:=
  assume x,
  begin
    unfold separable_subset,
    split,
    { exact (empty_always_subset M x),
    },
    { 
      rw empty_union_x,
      rw x_minus_empty M x,
    }
  end


lemma lemma11a: (Λ :M) ∈ (W11 M):=  --line 229
   begin
     rw (W11_members),
     split,
     { 
       exact (lambda_finite M),
     },
     { 
       intros  X h1 h2,
       rw separable_subset, 
       split,
       {
         exact h1, 
       },
       { rw empty_union_x, 
         rw x_minus_empty, 
       }
     },
   end

lemma lemma11c: adjoin_closed M (W11 M):=   -- line 231
  begin
    unfold adjoin_closed, 
    intros b c, 
    rw (W11_members M),
    intro h,
    cases h with h2 h3,
    cases h2 with h4 h5,
    rw (W11_members M),
  
    split,
    { 
      exact (finite_adjoin M b c (and.intro h4 h3)), 
    },
    { 
      intro a,
      intro h6,
      specialize h5 a,
      intro h7,
      unfold separable_subset,
      split,
      { exact h6,
      },
      {
          --line 231
        rw full_extensionality,
        intro x,
        have h8:a ∈ DECIDABLE M:= finitedecidable M a h7, 
        split, 
        {    --left-to-right, line 234
          intro h9,
          rw decidable_members M at h8,
          have h6copy := h6,
          rw subset_definition at h6,
          specialize h6 c,
          rw (binary_union_axiom b (single c) c) at h6,
          rw (singleton1 M) at h6,
          have h10: c ∈ a:=  (h6 (or.inr (refl c))), 
          repeat{rw (binary_union_axiom)}, 
          rw (minus_members M),
          repeat{ rw (singleton1 M)},
           rw binary_union_axiom,
           rw (singleton1 M),
           specialize h8 x c,
           have h11:= h8 (and.intro h9 h10),
           cases h11 with h12 h13,
           {
             rw h12 at *,
             left,right,
             exact (refl c), 
           },
           { 
             have h15:= union_subset M b (single c) a h6copy,
             have h16:= h5 h15 h7,
             unfold separable_subset at h16, 
             cases h16 with h17 h18, 
             have h19:= h8 (and.intro h9 h10),
             rw full_extensionality at h18,
             specialize h18 x,
             cases h18 with h20 h21,
             have h22:= h20 h9,
             rw binary_union_axiom at h22, 
             rw (minus_members M) at h22, 
             have h23: x ∈ b ∨ ¬ (x ∈ b) :=
               begin
                 cases h22 with h24 h25,
                 { 
                   left,
                   exact h24, 
                 },
                 { 
                   right,
                   exact (and.right h25),
                 }
               end,
            cases h23 with h30 h31,
            {
              left, left, exact h30,
            },
            {
              right,
              split,
              { exact h9},
              { 
                intro h32,
                cases h32 with h33 h34,
                {
                  contradiction, 
                },
                {
                  contradiction, 
                }
              }
            }
           }
        },  -- end of left-to-right, line 237  
        {   -- right-to-left, line 237
          intro h9,
          rw (binary_union_axiom) at h9,
          cases h9 with h10 h11,
          {
            rw subset_definition at h6,
            exact (h6 x h10), 
          },
          {
            rw (minus_members M) at h11,
            exact (and.left h11), 
          }
        }    -- line 239 
      }
    },
  end


lemma finiteseparable: ∀ (a b:M), (a ∈ FINITE M → b ∈ FINITE M → b ⊆ a → a = ((a-b) ∪ b)) :=
  assume a b,
  begin 
    intro h50, 
    have h: (FINITE M)⊆ W11 M := (finite_conditions M) (W11 M)   (lemma11c M) (lemma11a M),
    rw (subset_definition) at h, 
    specialize h b,
    rw (W11_members M) at h,
    intros h2 h3,
    have h4:= h h2,
    cases h4 with h5 h6,
    specialize h6 a,
    have h7:= h6 h3 h50,
    unfold separable_subset at h7,
    rw (union_commutative M), 
    exact (and.right h7),
  end

--line 240 of the paper 

lemma lemma12a:(Λ:M) ∈ W12 M:=
  begin
    rw (W12_members),
    split,
      {
         exact (lambda_finite M),
      },
      {
        intro Y,
        intro h2,
        rw subset_of_empty at h2,
        rw h2 at *,
        intro h3,
        exact (lambda_finite M),
      }
  end


lemma lemma12b: adjoin_closed M (W12 M):=
  begin
    unfold adjoin_closed,
    assume Y a,
    repeat{ rw W12_members},
    intro h,
    cases h with h1 h2,
    cases h1 with h3 h4, 
    have h4copy := h4, 
    split, 
    { 
      exact (finite_adjoin M Y a (and.intro h3 h2)),
    }, 
    {  
      intro U,
      intro h5,
      intro h6,
      specialize h4 U,
      set V:= U - (single a) with h13,   -- line 248
      have h60:= h4copy V, 
      have h70:= separable_subset_to_separable M U (Y ∪ (single a)),
      have h71:= iff.elim_left h70,
      have h72:= h71 h6,
      cases h72 with h73 h74,
      have h75:= separable1 M U (Y ∪ (single a)) h5,
      rw h75 at  h74, 
      have h8:= h74, 
      have h8copy := h8, 
      specialize h8 a,
      have h9: a ∈ Y ∪ (single a):=
        begin
          rw binary_union_axiom, 
          right,
          rw singleton1, 
        end,
      have h10:= h8 h9,   -- a ∈ U ∨ ¬ (a ∈ U) , line 245
      have h19:= finite_adjoin M Y a (and.intro h3 h2),  
      have h20: Y ∪ (single a) ∈ DECIDABLE M:= finitedecidable M (Y ∪ (single a)) h19, 
      have h14: V ⊆ Y :=
        begin
          rw subset_definition,
          intro z,
          rw h13,
          rw (minus_members M), 
          intro h14,
          cases h14 with h15 h16,
          rw (singleton1 M) at h16,
          rw (subset_definition) at h5,
          specialize h5 z,
          have h17:= h5 h15,
          rw binary_union_axiom at h17,
          rw (singleton1 M) at h17,
          cases h17 with h80 h81,
            {
              exact h80,
            },
            {
               rw h81 at *,
               contradiction, 
            } 
        end, 
      have h18: separable_subset M V Y:=  -- line 249
        begin
          rw (separable_subset_to_separable M), 
          split,
            { 
              exact h14,
            },
            { 
              rw (separable1 M),
              { intro z,
                intro h21,
                rw h13,
                rw (minus_members M), 
                rw (singleton1 M),
                rw (decidable_members M (Y ∪ (single a))) at h20,
                specialize h20 z a,
                have h22: Y ⊆ Y ∪ (single a) := subset_union2 M Y ( single a),
                rw subset_definition at h22,
                specialize h22 z,
                have h23:= h22 h21,
                have h24:= h20 (and.intro h23 h9),  -- z= a ∨ ¬ z = a,  line 251
                specialize h8copy z,
                have h25: z ∈ Y ∪ (single a):=
                  begin
                    rw binary_union_axiom,
                    left,
                    exact h21,
                  end,
                have h26:= h8copy h25,     --line 250 
                cases h26 with h27 h28,
                cases h24 with h29 h30,
                {
                  right,
                  intro h31,
                  cases h31 with h32 h33,
                  contradiction, 
                },
                {
                  left,
                  exact (and.intro h27 h30),
                },
                {
                  right,
                  intro h30,
                  cases h30 with h31 h32,
                  contradiction, 
                },
              },
              { exact h14,
              }
            }
        end,
        have h61:= h60 h14 h18,  -- V ∈ FINITE,  line 252 
      cases h10 with h11 h12, 
      {       
        have h62: (U = (V ∪ (single a))):=  -- line 253 claimed 
          begin
            rw full_extensionality,
            intro x,
            split,
            { 
              intro h30,
              have h31:= h5,
              rw subset_definition at h31,
              have h32:= h31 x h30, 
              rw (decidable_members M) at h20, 
              specialize h20 x a,
              have h33: x=a ∨ ¬ (x=a):= h20 (and.intro h32 h9),   -- line 254
              cases h33 with h34 h35,
              {
                rw binary_union_axiom,
                right,
                rw (singleton1 M),
                exact h34, 
              },
              {
                rw binary_union_axiom,
                left,
                rw h13,
                rw (minus_members M),
                split,
                {
                  exact h30,
                },
                {
                  rw (singleton1 M),
                  exact h35, 
                }
              },  
            },
            {
              intro h40,
              rw h13 at h40,
              rw binary_union_axiom at h40,
              rw (singleton1 M) at h40,
              rw (minus_members M) at h40,
              cases h40 with h41 h42,
              { 
                exact (and.left h41),
              },
              {
                rw h42 at *,
                exact h11, 
              },
            },
          end,
        -- proving V ∪ (single a) = U, line 256 of the paper
        have h63: ¬ a ∈ V:=
          begin
            rw h13,
            rw (minus_members M),
            rw (singleton1 M),
            intro h63, 
            cases h63 with h64 h65, 
            exact h65 (refl a),
          end, 
        have h66:= finite_adjoin M V a (and.intro h61 h63),
        rw← h62 at h66,
        exact h66,  
      }, 
      {
        have h90:V=U:=
          begin
            rw (full_extensionality M),
            intro x,
            rw h13,
            rw (minus_members M),
            rw (singleton1 M),
            split,
            {
              intro h93,
              exact (and.left h93),
            },
            {
              intro h94,
              split,
              { exact h94,
              },
              {
                intro h95,
                rw h95 at *,
                contradiction, 
              }
            }
          end,
        rw h90 at *,
        exact h61, 
      }
    } 
  end


lemma separablefinite: ∀ X, X ∈ FINITE M →  ∀ Y,(Y ⊆ X → separable_subset M Y X → Y ∈ FINITE M) :=
  assume X, 
  begin 
    intro h50, 
    have h: (FINITE M)⊆ W12 M := (finite_conditions M) (W12 M)   (lemma12b M) (lemma12a M), 
    rw (subset_definition) at h, 
    specialize h X,
    rw (W12_members M) at h, 
    have h51:= h h50,
    cases h51 with h52 h53,
    exact h53,
  end

lemma lemma13a: ∀ (a c:M), (a ∈ FINITE M → c ∈ a → a - (single c) ∈ FINITE M):=
    -- line 260, formula (16) of the paper 
  assume a c,
  begin 
    intros h h3,
    have h1:a ∈ DECIDABLE M:= (finitedecidable M a h ), 
    have h2: separable_subset M ( a- (single c)) a:=
      begin
        unfold separable_subset,
        rw (decidable_members M) at h1,
        split,
          { exact minus_subset M a (single c), 
          },
          { 
            rw (full_extensionality M),
            intro z,
            rw binary_union_axiom,
            repeat {rw (minus_members M) },
            repeat {rw (singleton1 M)},
            specialize h1 z c,
            split, 
            { 
              intro h4, 
              have h5:= h1 (and.intro h4 h3),               
              cases h5 with h6 h7, 
              { right, 
                rw h6 at *,
                split,
                { exact h4,
                },
                { intro h8,
                  cases h8 with h9 h10,
                  contradiction,
                }
              },
              { left,
                exact (and.intro h4 h7),
              }
            },
            {
              intro h3,
              cases h3 with h4 h5,
              {
                exact h4.left,
              },
              {
                exact h5.left, 
              }
            },
          }
      end,
    have h20:a- single c ⊆ a :=
      begin
        rw subset_definition,
        intro z,
        rw (minus_members M), 
        exact λ h, (and.left h), 
      end,  
    exact (separablefinite M a h (a- (single c)) h20 h2), 
  end 

lemma lemma13b: (Λ :M) ∈ (W13 M):=   --line 260
  begin
    rw (W13_members M),
    split,
      {
        exact (lambda_finite M),  
      },
      {
        intros y h h2,
        rw subset_of_empty at h2,
        rw h2 at *, 
        rw (x_minus_empty M Λ ),
        exact lambda_finite M, 
      }
  end

lemma lemma13c: adjoin_closed M (W13 M):=
  begin
    unfold adjoin_closed,
    intros p c,
    repeat{ rw (W13_members M)},
    intro h2,     
    cases h2 with h3 h4,
    cases h3 with h5 h6,   
    split,
      { 
        exact (finite_adjoin M p c (and.intro h5 h4)), 
      },
      {
        intros b h7 h8, 
        have h9: p ∪ (single c) ∈ FINITE M:=
           finite_adjoin M p c (and.intro h5 h4), 
        have h10:= finiteseparable M (p ∪ (single c)) b h9 h7 h8,
        have h11: c ∈ b ∨ ¬ (c ∈ b):=   -- line 265
           begin
             rw (full_extensionality M) at h10,
             specialize h10 c,
             rw binary_union_axiom at h10,
             rw (singleton1 M) at h10,
             rw binary_union_axiom at h10,
             rw (minus_members M) at h10,
             rw binary_union_axiom at h10,
             rw (singleton1 M) at h10,
             simp at h10, 
             rw or_comm,
             exact h10,
           end, 
        cases h11 with h12 h13,
        {  -- the case c ∈ b, line 266 
          have h14: (p ∪ (single c))- b = p-b :=  --line 266
            begin
              rw (full_extensionality M), 
              intro x,
              repeat{ rw (minus_members M)},
              rw binary_union_axiom,
              rw (singleton1 M),
              rw subset_definition at h8,
              have h20: (p ∪ (single c)) ∈ DECIDABLE M:= finitedecidable M (p ∪ (single c)) h9,
              rw (decidable_members M)  at h20, 
              specialize h20 x c,
              have h30: c ∈ p ∪ (single c):= 
                begin
                  rw binary_union_axiom,
                  rw (singleton1 M),
                  right,
                  exact (refl c),
                end,
              have h31: x ∈ p ∪ (single c) → x = c ∨ ¬ (x=c):=
                λ h, h20 (and.intro h h30),
              rw binary_union_axiom at h31,
              rw (singleton1 M) at h31, 

              split,
              {  -- left-to-right 
                intro h21,
                cases h21 with h22 h23,
                have h24:= h31 h22, 
                cases h24 with h25 h26,
                {
                  rw h25 at *,
                  contradiction,
                },
                {
                  cases h22 with h50 h51,
                  {
                    exact ⟨ h50, h23⟩, 
                  },
                  {
                    contradiction,
                  }
                },
              },
              {  -- right-to-left
                intro h40,
                split,
                {
                  left,
                  exact h40.left, 
                },
                {
                  exact h40.right, 
                }
              },
            end,  --finishes proving line 266
          rw h14,         
          have h16: b - (single c) ⊆ p:=
            begin 
              rw subset_definition,
              intro z,
              intro h18,
              rw subset_definition at h8,
              specialize h8 z,  
              rw binary_union_axiom at h8, 
              rw (minus_members M) at h18,
              rw (singleton1 M) at h8, 
              rw (singleton1 M) at h18,  
              cases h18 with h19 h20, 
              have h21:= h8 h19, 
              cases h21 with h22 h23,
              {
                exact h22,
              },
              {
                contradiction, 
              }
            end,
          have h17:= (minus_subset M p (b - (single c))), 
          have h18:= lemma13a M b c h7 h12,  --line 266e
          have h15:= h6 (b-single c) h18  h16,   -- line 266f
          have h20: p-(b-(single c)) = p-b:=  --line 266d
            begin
              rw (full_extensionality M),
              intro z, 
              repeat{ rw (minus_members M)},
              rw (singleton1 M), 
              split,
              {
                intro h40,
                cases h40 with h41 h42,
                split,
                 {
                   exact h41,
                 },
                 {
                   intro h43,
                   have h44:¬ (z=c):=
                     begin
                       intro h45,
                       rw h45 at *,
                       contradiction, 
                     end, 
                   exact h42 (and.intro h43 h44),  
                 }
              },
              {
                intro h50,
                cases h50 with h51 h52,
                split,
                { 
                  exact h51,
                },
                {
                  intro h53,
                  cases h53 with h54 h55,
                  contradiction, 
                },
              },
            end,
          rw h20 at h15, 
          exact h15,     
        }, 
        {   -- the case ¬ c ∈ b,  line 268 
          have h20: b ⊆ p:=   --line 268
            begin
              rw subset_definition,
              intro z,
              intro h40,
              rw subset_definition at h8,
              specialize h8 z,
              have h9:= h8 h40,
              rw binary_union_axiom at h9,
              rw (singleton1 M) at h9,
              cases h9 with h10 h11,
              {
                exact h10,
              },
              {
                rw h11 at *,
                contradiction, 
              }
            end,
          have h50: p-b ∈ FINITE M:= h6 b h7 h20, --line 268 
          have h51:¬( c ∈  (p-b)):=
            begin
              intro h,
              rw (minus_members M) at h,
              cases h with h51 h52,
              contradiction, 
            end,
          have h52:= finite_adjoin M (p-b) c (and.intro h50 h51), --line 269b
          have h53: (p- b) ∪ (single c) = (p ∪ (single c))-b:=  -- line 269c
            begin 
              rw (full_extensionality M),
              intro z, 
              rw binary_union_axiom,
              repeat{ rw (minus_members M)},
              rw (singleton1 M),
              rw binary_union_axiom,
              rw (singleton1 M),
              rw subset_definition at h20,
              specialize h20 z,
              rw (minus_members M) at h51,
              split,
              {
                intro h60,
                cases h60 with h61 h62,
                {
                  cases h61 with h63 h64,
                  exact (and.intro (or.inl h63) h64), 
                },
                {
                  rw h62 at *,
                  simp, 
                  exact h13, 
                }
              },
              {
                intro h65,
                cases h65 with  h66 h67,
                cases h66 with h68 h69,
                {
                  left,
                  exact (and.intro h68 h67),
                },
                {
                  rw h69 at *,
                  right,
                  exact (refl c), 
                },
              },
            end,
          rw h53 at h52,
          exact h52,  
        },
      }
  end  

lemma finitedif: ∀ (a b:M), a ∈ FINITE M→ b ∈ FINITE M → b ⊆ a → a-b ∈ FINITE M:=
  assume a b,
  begin
    intro h,
    have h2: (FINITE M)⊆ W13 M := (finite_conditions M) (W13 M)   (lemma13c M) (lemma13b M), 
    rw subset_definition at h2,
    specialize h2 a, 
    rw (W13_members M) at h2,
    intro h3,
    have h4:= h2 h,
    cases h4 with h5 h6,
    specialize h6 b,
    exact h6 h3,
  end

lemma finite_minus_singleton: ∀ (x c:M),  ¬ c ∈ x → x ∪ (single c) ∈ FINITE M → x ∈ FINITE M:=
  assume x c,
  begin
    intros h1 h2,
    have h3:= finitedecidable M (x ∪ single c) h2,
    have h4: x = (x ∪ (single c))- (single c) :=
      begin
        rw (full_extensionality M), 
        intro z,
        rw (minus_members M),
        rw (binary_union_axiom),
        rw (singleton1 M),
        split,
        { 
          intro h4, 
          split,
          { 
            exact (or.inl h4),
          },
          {
            intro h5,
            rw h5 at *,
            contradiction, 
          }
        },
        { intro h4, 
          cases h4 with h5 h6,
          cases h5 with h7 h8,
          {
            exact h7,
          },
          {
            contradiction, 
          } 
        },
      end,
    have h8: (single c) ∈ FINITE M:= singleton_finite M c,
    have h9:= finitedif M (x ∪ (single c))  (single c) h2 h8 , 
    have h10:= (subset_union2 M (single c) x),
    rw union_commutative M at h10,
    have h11:= h9 h10,
    rw← h4 at h11,
    exact h11,
  end

lemma lemma14a: ∀ (R X:M), (Λ:M) ∈ (W14 M R X) :=  --base case, line 275
  assume R X, 
  begin
    rw (W14_members M), 
    intro h,
    intros z h2,
    right,
    intro h3,
    cases h3 with u h4,
    exact (emptyset_axiom u (and.left h4)), 
  end 

lemma lemma115a:
∀ (R X Y:M), (Λ:M) ∈ (W115 M R X Y) :=  --base case, line 275
  assume R X Y, 
  begin
    rw (W115_members M), 
    intro h,
    intros z h2,
    right,
    intro h3,
    cases h3 with u h4,
    exact (emptyset_axiom u (and.left h4)), 
  end 

lemma lemma14b: 
  (
    ∀ (Z Y B:M), 
      ( ∀ (z : M), ( z ∈ Y ↔ z ∈ X ∧ ∃ (u : M), u ∈ B ∧  ‹ u,z ›  ∈ R) )→ 
     ( separable_subset M Y X  ↔ 
     ∀ z, (z ∈ X → (∃ u, u ∈ B ∧ ‹ u,z › ∈ R) ∨ ¬ ∃ u, u ∈ B ∧ ‹ u,z› ∈ R))
  ) :=
  assume Z Y B,
  begin
    intro h2, 
    rw separable_subset_to_separable,
    unfold separable,
    split,
    {
      intro h3,
      cases h3 with h4 h5,
      intro z,
      intro h6, 
      rw full_extensionality at h5,
      specialize h5 z,
      specialize h2 z,
      rw binary_union_axiom at h5, 
      rw (minus_members M) at h5,
      rw h2 at h5,
      cases h5 with h7 h8,
      have h9:= h7 h6,
      simp [iff_of_true h6 trivial] at *,   -- Thanks to Kyle Miller! 
      exact h9, 
    },
    {
      intro h3,
      split,
      { 
       rw subset_definition,
       intro z,
       specialize h2 z, 
       intro h3,
       simp [iff_of_true h3 trivial] at *,
       exact (and.left h2),
      },
      {
        rw full_extensionality,
        intro z, 
        rw binary_union_axiom,
        rw (minus_members M),
        specialize h2 z,
        specialize h3 z,
        split,
        {
          intro h4,
          simp [iff_of_true h4 trivial] at *, 
          rw h2,
          cases h3 with h5 h6,
          {
            left,
            exact h5, 
          },
          {
            right,
            intro h7,
            cases h7 with u h8,
            specialize h6 u,
            cases h8 with h10 h11, 
            have h12:= h6 h10,
            contradiction,
          },
        },
        {
          intro h4,
          cases h4 with h5 h6,
          {
            cases h2 with h7 h8,
            exact (and.left (h7 h5)),
          },
          {
            exact (and.left h6), 
          }
        }
      }
    }
  end

lemma adjoin_member: ∀ (c x:M), c ∈ x ∪ (single c):=
  assume c x,
  begin 
    rw binary_union_axiom,
    rw (singleton1 M),
    right,
    exact (refl c),
  end

lemma adjoin_member2: ∀ (u c x:M), u ∈ x → u ∈ x ∪ (single c):=
  assume u c x,
  begin
    intro h,
    rw binary_union_axiom,
    left,
    exact h, 
  end

lemma lemma14c: ∀ (R X:M), adjoin_closed M (W14 M R X):=
  assume R X,
  begin
    unfold adjoin_closed,
    intro A,
    intro c, 
    repeat{ rw W14_members M R X }, 
    intro h,
    cases h with h1 h2,
    intro h3,
    rcases h3 with ⟨ h4, h5, h6, h7 ⟩, 
    have h8:=    iff.mp (decidable_members M X) h6, 
    set B:= (A ∪ (single c)) with hB,
    have h102: A ∈ FINITE M:= finite_minus_singleton M A c h2 h4, 
    have h104:A⊆B:= 
      begin
        rw hB,
        exact (subset_union M A A (single c) (subset_reflexive M A)), 
      end,
    have h103: A ⊆ X:= 
      begin
        exact (subset_transitive M A B X h104 h5), 
      end, 
    have hBcopy := hB, 
    have h20: c∈ B :=
      begin 
        rw (full_extensionality M) at hBcopy,
        specialize hBcopy c, 
        apply hBcopy.mpr, 
        exact adjoin_member M c A,   
      end,
    have h4: ∀ z,(z ∈ X → ((∃ u, u ∈ B ∧ ‹ u,z › ∈ R) ↔ ((∃ u, u∈ A ∧ ‹ u,z › ∈ R) ∨ ‹ c,z› ∈ R))):=
       --  line 278a of the paper, formula (17)
      begin 
        intros z h4,
        split,  -- left-to-right of (17)
        { 
          intro h9,
          cases h9 with u h10,
          have h11:= h8 u c,
          rw subset_definition at h5,
          cases h10 with h12 h13,
          have h14:= h5 u h12, 
          have h15:= h11 (and.intro h14 (h5  c h20)), 
          cases h15 with h16 h17,
          {
            right,
            rw h16 at *,
            exact h13, 
          },
          {
            use u,
            split,
            {
              rw hB at h12,
              rw binary_union_axiom at h12,
              rw (singleton1 M) at h12,
              cases h12 with h20 h21,
              {
                exact h20,
              },
              {
                contradiction, 
              }
            },
            {
              exact h13, 
            }
          }, 
        },
        {      -- right-to-left of (17)
          intro h30,
          cases h30 with h31 h32,
          {
            cases h31 with u h34,
            use u,
            rw hB,
            cases h34 with h35 h36,
            rw binary_union_axiom,
            exact (and.intro (or.inl h35) h36),
          },
          {
            use c,
            rw hB,
            rw binary_union_axiom,
            rw (singleton1 M),
            split,
            { exact (or.inr (refl c)),},
            { exact h32,},
          }
        }
      end,
    intros z h40,
          --  now the goal is formula (18), line 279
    rw h4,
    { 
      rw not_or_distrib, 
      rw or_and_distrib_left,   --reaching line 280d
      repeat{ rw← or_assoc },
      split,
      {
        rw or_comm,
        rw←  or_assoc,
        left,
        rw or_comm,
        -- now the goal is line 280f so we have to use the induction hypothesis h1
        exact (h1 (and.intro h102
                     (and.intro h103
                        (and.intro h6 h7)
                     )
                  ) z h40
                 
              ), 
      },
      {
        specialize h7 c z,
        rw subset_definition at h5,
        specialize h5 c,
        have h6:= h5 h20, 
        have h9:= h7 h6 h40,
        cases h9 with h140 h141,
        {
          left,right,
          exact h140, 
        },
        {
          right,
          exact h141, 
        }
      }
    },
    {
      exact h40, 
    }
  end 

lemma lemma115c: ∀ (R X Y:M), adjoin_closed M (W115 M R X Y):=
  assume R X Y,
  begin
    unfold adjoin_closed,
    intro A,
    intro c, 
    repeat{ rw W115_members M R X Y}, 
    intro h,
    cases h with h1 h2,
    intro h3,
    rcases h3 with ⟨ h4, h5, h6, h7 ⟩, 
    have h8:=    iff.mp (decidable_members M X) h6, 
    set B:= (A ∪ (single c)) with hB,
    have h102: A ∈ FINITE M:= finite_minus_singleton M A c h2 h4, 
    have h104:A⊆B:= 
      begin
        rw hB,
        exact (subset_union M A A (single c) (subset_reflexive M A)), 
      end,
    have h103: A ⊆ X:= 
      begin
        exact (subset_transitive M A B X h104 h5), 
      end, 
    have hBcopy := hB, 
    have h20: c∈ B :=
      begin 
        rw (full_extensionality M) at hBcopy,
        specialize hBcopy c, 
        apply hBcopy.mpr, 
        exact adjoin_member M c A,   
      end,
    have h104: ∀ z,(z ∈ Y → ((∃ u, u ∈ B ∧ ‹ u,z › ∈ R) ↔ ((∃ u, u∈ A ∧ ‹ u,z › ∈ R) ∨ ‹ c,z› ∈ R))):=
      begin 
        intros z h4,
        split,  -- left-to-right of (17)
        { 
          intro h9,
          cases h9 with u h10,
          have h11:= h8 u c,
          rw subset_definition at h5,
          cases h10 with h12 h13,
          have h14:= h5 u h12, 
          have h15:= h11 (and.intro h14 (h5  c h20)), 
          cases h15 with h16 h17,
          {
            right,
            rw h16 at *,
            exact h13, 
          },
          {
            use u,
            split,
            {
              rw hB at h12,
              rw binary_union_axiom at h12,
              rw (singleton1 M) at h12,
              cases h12 with h20 h21,
              {
                exact h20,
              },
              {
                contradiction, 
              }
            },
            {
              exact h13, 
            }
          }, 
        },
        {      -- right-to-left of (17)
          intro h30,
          cases h30 with h31 h32,
          {
            cases h31 with u h34,
            use u,
            rw hB,
            cases h34 with h35 h36,
            rw binary_union_axiom,
            exact (and.intro (or.inl h35) h36),
          },
          {
            use c,
            rw hB,
            rw binary_union_axiom,
            rw (singleton1 M),
            split,
            { exact (or.inr (refl c)),},
            { exact h32,},
          }
        }
      end,
    intros z h40,
    rw h104,
    { 
      rw not_or_distrib, 
      rw or_and_distrib_left,   --reaching line 280d
      repeat{ rw← or_assoc },
      split,
      {
        rw or_comm,
        rw←  or_assoc,
        left,
        rw or_comm,
        -- now the goal is line 280f so we have to use the induction hypothesis h1
        exact (h1 (and.intro h102
                     (and.intro h103
                        (and.intro h6 h7)
                     )
                  ) z h40
                 
              ), 
      },
      {
        specialize h7 c z,
        rw subset_definition at h5,
        specialize h5 c,
        have h6:= h5 h20, 
        have h9:= h7 h6 h40,
        cases h9 with h140 h141,
        {
          left,right,
          exact h140, 
        },
        {
          right,
          exact h141, 
        }
      }
    },
    { 
      exact h40, 
    }
  end 


lemma member_subset: ∀ (a b x:M), a ⊆ b → x ∈ a → x ∈ b:=
  assume a b x,
  begin
    intros h1 h2,
    rw subset_definition at h1,
    specialize h1 x,
    exact h1 h2, 
  end


lemma boundedquantification: ∀ (R X B:M),   -- line 272 of the paper 
 B ∈ FINITE M ∧  B ⊆ X ∧ X ∈ DECIDABLE M ∧  
            ( ∀ (u z:M),(u ∈ X → z ∈ X → (‹u,z› ∈ R ∨ ¬ ‹ u,z › ∈ R))) →
            ∀ (z:M), (z ∈ X → (∃ u,(u ∈ B ∧ ‹ u,z› ∈ R)) ∨ ¬ ∃ u,(u ∈ B ∧ ‹ u,z› ∈ R) ):=
  assume R X B,
  begin
    intro h,
    have h2: (FINITE M)⊆ W14 M R X := (finite_conditions M) (W14 M R X)   (lemma14c M R X) (lemma14a M R X), 
    rw subset_definition at h2,
    specialize h2 B, 
    rw (W14_members M) at h2,
    intros z h3,
    cases h with h10 h11,
    have h4:= h2 h10 (and.intro h10 h11), 
    specialize h4 z,
    exact (h4 h3),
  end 

lemma boundedquantification2: ∀ (R X Y B:M),   
 B ∈ FINITE M ∧  B ⊆ X ∧ X ∈ DECIDABLE M ∧  
            ( ∀ (u z:M),(u ∈ X → z ∈ Y → (‹u,z› ∈ R ∨ ¬ ‹ u,z › ∈ R))) →
            ∀ (z:M), (z ∈ Y → (∃ u,(u ∈ B ∧ ‹ u,z› ∈ R)) ∨ ¬ ∃ u,(u ∈ B ∧ ‹ u,z› ∈ R) ):=
  assume R X Y B,
  begin
    intro h,
    have h2: (FINITE M)⊆ W115 M R X Y := (finite_conditions M) (W115 M R X Y)   (lemma115c M R X Y) (lemma115a M R X Y), 
    rw subset_definition at h2,
    specialize h2 B, 
    rw (W115_members M) at h2,
    intros z h3,
    cases h with h10 h11,
    have h4:= h2 h10 (and.intro h10 h11), 
    specialize h4 z,
    exact (h4 h3),
  end 

lemma similar_to_empty2: ∀(x:M), similar M x Λ →  x = Λ :=
  assume y,
  begin
    intro h,
    unfold similar at h,
    cases h with f h2,
    unfold similarity at h2,
    cases h2 with h3 h4,
    unfold oneone at h3,
    cases h3 with h5 h6,
    cases h6 with h7 h8,
    rw (full_extensionality M),
    unfold maps at h5,
    rcases h5 with ⟨ h10, h11, h12, h13 ⟩, 
    intro z,
    specialize h13 z, 
    split,
    { 
      intro h9,
      have h14:= h13 h9, 
      cases h14 with x h16, 
      cases h16 with h17 h18,
      have h19:= emptyset_axiom x,
      contradiction,  
    },
    {
      intro h20,
      have h21:= emptyset_axiom z, 
      contradiction,    
    },
  end 

lemma similar_to_empty:  ∀(x:M), similar M x Λ ↔  x = Λ :=
  assume x,
  begin
    split,
    { 
      exact (similar_to_empty2 M x),
    },
    {
      intro h,
      rw h,
      exact (similar_reflexive M Λ),
    }
  end
  
lemma lemma15a: (Λ :M) ∈ W15 M:=  -- line 289
  begin
    rw (W15_members M),
    split,
      {
        exact (lambda_finite M),  
      },
      {
        intros y h h2,
        rw similar_symmetric M at h2, 
        have h3:= (similar_to_empty2 M y h2), 
        symmetry,
        exact h3,
      }
  end

lemma swap_similarity:∀ (X U b c:M), X ∈ DECIDABLE M → U ⊆ X → ¬ (c ∈ U) → b ∈ U → c ∈ X → 
(similar M U (U-(single b) ∪ (single c))):=
  assume X U b c,
  begin
    set h:= ((IDENTITY M U)-(single ‹ b,b ›)) ∪ (single ‹ b,c ›) with h2, 
    intros h3 h4 h5 h6 hcX, 
    rw (decidable_members M) at h3,
    rw subset_definition at h4,  
    unfold similar,
    use h,
    unfold similarity, 
    split,
    {  -- have to prove h is one-to-one
      unfold oneone, 
      unfold maps,
      repeat {split}, 
      {
        unfold Rel_definition,
        intro z,
        intro h7,
        rw h2 at h7,
        rw binary_union_axiom at h7,
        rw (minus_members M) at h7,
        rw (identity_members M) at h7, 
        cases h7 with h8 h9,
        { 
          cases h8 with h10 h11,
          cases h10 with u h12,
          use u, use u,
          exact (and.left h12), 
        },
        {
          use b, use c,
          rw (singleton1 M) at h9,
          exact h9,
        }
      },
      { 
        intros x y h13,
        cases h13 with h14 h15, 
        rw h2 at h15,
        rw (binary_union_axiom) at h15,
        rw (minus_members M) at h15,
        rw (identity_members M) at h15,
        cases h15 with h16 h17,
        { 
          cases h16 with h18 h19,
          cases h18 with u h20,
          rw (ordered_pair_equality M) at h20,
          cases h20 with h21 h22,
          cases h21 with h23 h24,
          rw h23 at *,
          rw h24 at *,
          rw binary_union_axiom,
          rw (minus_members M),
          repeat{ rw (singleton1 M)}, 
          left, 
          split,
          {
            exact h14,
          },
          {
            intro h25, 
            rw h25 at *,
            rw (singleton1 M) at h19,
            rw (ordered_pair_equality M) at h19,
            simp at h19,
            exact h19,   
          }
        },
        {
          rw binary_union_axiom,
          rw (minus_members M),
          repeat{ rw (singleton1 M)},
          rw (singleton1 M) at h17,
          rw (ordered_pair_equality M) at h17,
          cases h17 with h28 h29,
          rw h28 at *,
          rw h29 at *,
          simp,
        }, 
      },
      {
        intros x y z,
        intro h30,
        rcases h30 with ⟨ h31, h32, h33⟩ ,
        rw (full_extensionality M) at h2, 
        have h34:= h2  ‹ x,y ›,
        have h35:= h2  ‹ x,z ›, 
        rw h34 at h32,
        rw h35 at h33, 
        rw binary_union_axiom at h32,
        rw (minus_members M) at h32,
        rw (singleton1 M) at h32, 
        rw (singleton1 M) at h32,
        rw (ordered_pair_equality M) at h32,
        rw (identity_members M) at h32, 
        rw binary_union_axiom at h33,
        rw (minus_members M) at h33,
        rw (singleton1 M) at h33, 
        rw (singleton1 M) at h33,
        rw (ordered_pair_equality M) at h33,
        rw (identity_members M) at h33, 
        cases h32 with h36 h37,
        {
          cases h36 with h38 h39,
          cases h38 with u h40,
          rw (ordered_pair_equality M) at h40,
          cases h40 with h41 h42,
          cases h41 with h43 h44,
          rw h43 at *,
          rw h44 at *,
          cases h33 with h45 h46,
          {
            cases h45 with h47 h48,
            cases h47 with u1 h49,
            rw (ordered_pair_equality M) at h49,
            cases h49 with h50 h51,
            cases h50 with h52 h53,
            rw h52,
            rw h53,
          },
          {
            rw (ordered_pair_equality M) at h46,
            cases h46 with h54 h55,
            rw h54 at *,
            rw h55 at *,
            simp at h39, 
            contradiction, 
          },
        },
        {
          rw (ordered_pair_equality M) at h37,
          cases h37 with h56 h57,
          rw h56 at *,
          rw h57 at *,
          cases h33 with h58 h59,
          { 
            cases h58 with h60 h61,
            cases h60 with u h62,
            rw (ordered_pair_equality M) at h62,
            cases h62 with h63 h64,
            cases h63 with h65 h66,
            rw h65 at *,
            rw h66 at *,
            rw h57 at *, 
            simp at h61, 
            contradiction,
          },
          {
            rw (ordered_pair_equality M) at h59, 
            simp at h59, 
            symmetry,
            exact h59, 
          },
        },
      },
      {
        intro x,
        intro h70,
        have h71: x = b ∨ ¬ (x=b):= h3 x b (and.intro (h4 x h70)   (h4 b h6)),  
        rw (full_extensionality M) at h2,
        cases h71 with h72 h73, 
        {
          use c,
          rw h72, 
          rw binary_union_axiom,
          rw (minus_members M),
          repeat{ rw (singleton1 M)},
          split,
          {
            exact (or.inr (refl c)),
          },
          {
            rw (h2 ‹ b,c› ),
            rw binary_union_axiom,
            rw (minus_members M),
            repeat{ rw (singleton1 M)},
            right,
            exact (refl ‹ b,c › ),
          }
        },
        {
          use x,
          rw binary_union_axiom,
          rw (minus_members M),
          repeat{ rw (singleton1 M)}, 
          split,
          {
            left,
            exact (and.intro h70 h73), 
          },
          {
            rw (h2 ‹ x,x › ), 
            rw binary_union_axiom,
            rw (minus_members M),
            repeat{ rw (singleton1 M)}, 
            left,
            rw (identity_members M),
            split,
            { 
              use x,
              exact (and.intro (refl ‹ x,x › ) h70), 
            },
            {
              rw (ordered_pair_equality M),
              simp,
              exact h73,
            }
          },
        },
      },
      { 
        intros x u y h80, 
        rcases h80 with ⟨ h81, h82, h83⟩, 
        rw (full_extensionality M) at h2, 
        rw h2 at h81, 
        rw h2 at h82,
        rw binary_union_axiom  at h81 h82, 
        rw (minus_members M) at h81 h82,
        rw (singleton1 M) at h81 h82, 
        rw (singleton1 M) at h81 h82,
        rw (identity_members M) at h81 h82, 
        have h200: y ∈ X:=
          begin 
            cases h82 with h201 h202,
            {
              cases h201 with h203 h204,
              cases h203 with u1 h205,
              rw (ordered_pair_equality M) at h205,
              cases h205 with h206 h207,
              cases h206 with h208 h209,
              rw← h209 at *,
              exact (h4 y h207), 
            },
            {
              rw (ordered_pair_equality M) at h202,
              cases h202 with h203 h204,
              rw h204,
              exact hcX, 
            },
          end,
        have h100: y = c ∨ ¬ (y=c):= h3 y c (and.intro h200 hcX), 
        have h103: ¬ (b = c):=
          begin
            intro h104,
            rw h104 at *,
            contradiction, 
          end,        
        cases h100 with h101 h102, 
        { 
          cases h82 with h84 h85,
          {
            cases h84 with h86 h87,
            cases h86 with u1 h88,
            rw (ordered_pair_equality M) at h88,
            cases h88 with h89 h90,
            cases h89 with h91 h92,
            
            rw h91 at *, 
            rw h92 at *,
            rw h101 at *,
            cases h81 with h93 h94,
            { 
              cases h93 with h95 h96,
              cases h95 with v h97,
              rw (ordered_pair_equality M) at h97,
              cases h97 with h98 h99,
              cases h98 with h100 h101,
              rw h100,
              rw h101, 
            },
            {
              rw (ordered_pair_equality M) at h94,
              simp at h94, 
              contradiction, 
            }
          },
          {
            rw (ordered_pair_equality M) at h85, 
            cases h81 with h90 h91,
            {
              cases h90 with h92 h93,
              cases h92 with v h94, 
              rw (ordered_pair_equality M) at h94,
              cases h94 with h95 h96,
              cases h95 with h97 h98,
              cases h85 with h99 h100,
              rw h98 at *,
              rw h101 at *,
              rw ordered_pair_equality at h93,
              rw h99 at *, 
              rw h97 at *,
              contradiction, 
            },
            {
              rw (ordered_pair_equality M) at h91,
              cases h85 with h100 h105,
              cases h91 with h102 h103,
              rw h101 at *,
              rw h100 at *,
              rw h105 at *,
              rw h102 at *, 
            }
          }
        },
        {  cases h81 with h90 h91, 
            { 
              cases h90 with h92 h93,
              cases h92 with v h94, 
              rw (ordered_pair_equality M) at h94, 
              cases h82 with h95 h96,
              cases h95 with h97 h98,
              cases h97 with w h99,
              { rw (ordered_pair_equality M) at h99, 
                cases h94 with h110 h111,
                cases h110 with h112 h113,
                cases h99 with h114 h115,
                cases h114 with h116 h117,
                rw h112 at *,
                rw h113 at *,
                rw h116 at *,
                rw h117 at *, 
              },
              {
                rw (ordered_pair_equality M) at h96,
                cases h94 with h110 h111,
                cases h110 with h112 h113,
                rw h112 at *,
                rw h112 at *,
                cases h96 with h114 h115,
                rw h114 at *,
                rw h115 at *,
                contradiction, 
              }    
            },
            {
              rw (ordered_pair_equality M) at h91, 
              cases h91 with h110 h111,
              rw h110 at *,
              rw h111 at *, 
              contradiction,
            }       
        }
      },
      {
        intros x y h102,
        rw (full_extensionality M) at h2,
        specialize h2 ‹ x ,y ›,
        cases h102 with h103 h104,

        rw binary_union_axiom at h103,
        rw (minus_members M) at h103,
        rw (identity_members M) at h103,
        cases h103 with h104 h105,
        {
          cases h104 with h106 h107,
          cases h106 with u h108,
          rw (ordered_pair_equality M) at h108,
          cases h108 with h110 h111,
          cases h110 with h112 h113,
          rw h112 at *,
          rw h113 at *,
          exact h111,
        },
        {
          rw (singleton1 M) at h105,
          rw (ordered_pair_equality M) at h105,
          cases h105 with h110 h111,
          rw h110 at *,
          rw h111 at *,
          exact h6,
        }
      },
    },
    {  -- have to prove h is onto
      unfold onto, 
      intros y h10,
      rw binary_union_axiom at h10,
      rw (minus_members M) at h10,
      rw (singleton1 M) at h10, 
      cases h10 with h11 h12,
      {
        use y,
        cases h11 with h13 h14,
        split,
         {
           exact h13,
         },
         { 
           rw h2,
           rw binary_union_axiom,
           rw (minus_members M),
           rw (singleton1 M),
           rw (identity_members M), 
           left, 
           split,
           {
             use y,
             exact ⟨ refl ‹ y,y › , h13⟩, 
           },
           {
             rw (ordered_pair_equality M),
             intro h15,
             cases h15 with h16 h17,
             rw h16 at *,
             rw h17 at *, 
             contradiction,
           }
         }
      },
      {
        rw (singleton1 M) at h12, 
        use b,
        rw h12 at *,
        split,
        { 
          exact h6,
        },
        {
          rw h2,
          rw binary_union_axiom,
          right,
          rw (singleton1 M), 
        }
      }
    },
  end

lemma lemma15b: adjoin_closed M (W15 M):=
  begin
    unfold adjoin_closed,
    intros A b h,
    cases h with h1 h2, 
    rw (W15_members M) at *,
    cases h1 with h3 h4, 
    have h5:= finite_adjoin M A b (and.intro h3 h2),
    split,
    { 
       exact h5,
    },
    { 
      have h6: A ∪ (single b) ∈ DECIDABLE M :=  (finitedecidable M (A ∪ (single b)) h5), --line 291
      have h6copy := h6,
      intros Y h10 h7,  
      have h9: Y ∈ FINITE M:= finitesimilar M (A ∪ (single b))  Y h7 h5,   --line 293
      unfold similar at h7,  
      cases h7 with f h8,   --line 292
      have h11: Y ∈ DECIDABLE M:= finitedecidable M Y h9,  -- line 294 
      unfold similarity at h8,
      cases h8 with h12 h13,
      unfold oneone at h12,
      cases h12 with h14 h15,
      unfold maps at h14,
      rcases h14 with ⟨ h16, h17, h18, h19⟩, 
      have h19copy := h19,
      specialize h19 b,
      have h20:= adjoin_member M b A, 
      have h21:= h19 h20,
      cases h21 with c h22,
      cases h22 with h23 h24,   --  let c = f(b), line 296
      set U:= Y - (single c) with h25,   -- line 296
      rw decidable_members at h11,
      cases h15 with h40 h41, 

      have h26: similar M A U:=    -- line 297 
        begin
          unfold similar,
          use f,
          unfold similarity,
          unfold oneone,
          unfold onto,
          unfold maps,
          repeat {split},
          {
            exact h16, 
          },
          {  
            intros x y h27,
            cases h27 with h28 h29,
            rw h25,
            have h30:= adjoin_member2 M x b A h28,
            have h31:= h19copy x h30,
            cases h31 with y1 h32,
            cases h32 with h33 h34,
            have h35:= h18 x y y1 (and.intro h30 (and.intro h29 h34)), 
            rw← h35 at *,
            have h36:= h11 y c (and.intro h33 h23), 
            cases h36 with h37 h38, 
            {  rw h37 at *, 
               rw← h35 at *,
               have h42:=  h40 x b c (and.intro h29 (and.intro h24 h30)), 
               rw h42 at *,
               contradiction, 
            },
            { 
              rw (minus_members M),
              rw (singleton1 M),
              exact ⟨ h33, h38⟩,
            }
          },
          {
            intros x y z,
            intro h42,
            rcases h42 with ⟨ h43, h44, h45 ⟩,
            have h46: x ∈ A ∪ (single b):= adjoin_member2 M x b A h43,
            exact (h18 x y z (and.intro h46 (and.intro h44 h45))), 
          },
          {
            intros x h47,
            have h46: x ∈ A ∪ (single b):= adjoin_member2 M x b A h47,
            have h48:= h19copy x h46,
            cases h48 with y  h49,
            use y,
            cases h49 with h50 h51,
            split, 
            {
              rw h25,
              rw (minus_members M),
              rw (singleton1 M), 
              split,
               { exact h50,
               },
               {
                 intro h52,
                 rw h52 at *,
                 have h53:= h40 x b c (and.intro h51 (and.intro h24 h46)),
                 rw h53 at *,
                 contradiction, 
               }
            },
            {
              exact h51, 
            }
          },
          {
            intros x u y h54,
            rcases h54 with ⟨ h55, h56, h57⟩,
            have h58:= adjoin_member2 M x b A h57,
            exact h40 x u y (and.intro h55 (and.intro h56 h58)), 
          },
          {
            intros x y h59,
            cases h59 with h60 h61,
            rw h25 at h61,
            rw (minus_members M) at h61,
            rw (singleton1 M) at h61,
            cases h61 with h62 h63,
            have h64:= h41 x y (and.intro h60 h62), 
            rw binary_union_axiom at h64,
            rw (singleton1 M) at h64,
            cases h64 with h65 h66,
            { 
              exact h65,
            },
            {
              rw h66 at *,
              have h67:b ∈ A ∪ (single b):= adjoin_member M b A,
              have h68:= h18 b y c (and.intro h67 (and.intro h60 h24)),
              rw h68 at *,
              contradiction, 
            },
          },
          intro y,
          intro h70,
          rw h25 at h70,
          rw (minus_members M) at h70,
          cases h70 with h71 h72,
          rw (singleton1 M) at h72,
          unfold onto at h13,
          have h73:= h13 y h71, 
          cases h73 with x h74,
          use x,
          cases h74 with h75 h76,
          split,
          {
            rw binary_union_axiom at h75, 
            rw (singleton1 M) at h75,
            cases h75 with h76 h77,
            {
              exact h76,
            },
            {
              rw h77 at *,
              have h78: b ∈ A ∪ (single b):= adjoin_member M b A,
              have h79:= h18 b c y (and.intro h78 (and.intro h24 h76)),  
              rw h79 at *,
              contradiction, 
            }
          },
          {
            exact h76,
          },
        end,
      set S:= (U - (single c)) ∪ (single b) with h300,
      have h301: U ⊆ A ∪ (single b):=
        begin
          rw h25,
          have h302:= minus_subset M Y (single c),
          have h303:= subset_transitive M (Y - (single c)) Y (A ∪ (single b)) h302 h10, 
          exact h303,
        end, 
      have h305: c ∈ A ∪ (single b):=
        begin
          rw subset_definition at h10,
          exact (h10 c h23), 
        end,
      rw (decidable_members M) at h6,
      have h306:= h6 b c (and.intro h20 h305), 
      have h457: A ∪ (single b) ∈ DECIDABLE M:= finitedecidable M (A ∪ (single b)) h5, 
      cases h306 with h307 h308,
      { -- the case b = c, line 308 of the paper
        have h310: U ⊆ A:=
          begin
            rw h25,
            have h311:= (minus_subset M Y (single c)),
            rw subset_definition,
            intro z,
            rw (minus_members M),
            rw (singleton1 M),
            rw (subset_definition) at h10,
            specialize h10 z,
            intro h312,
            cases h312 with h313 h314,
            have h315:= h10 h313,
            rw (binary_union_axiom) at h315,
            cases h315 with h316 h317,
            {
              exact h316,
            },
            { rw (singleton1 M) at h317,
              rw h317 at *,
              contradiction,
            }
          end,
        have h311:= h4 U h310 h26,
        rw h311, 
        rw h25,
        rw (full_extensionality M),
        intro x,
        rw binary_union_axiom,
        rw (minus_members M),
        repeat{ rw (singleton1 M)},
        rw h307,
        have h320:= h11 x c,
        split,
        {
          intro h321,
          cases h321 with h322 h323,
          {
            exact (and.left h322), 
          },
          {
            rw h323,
            exact h23, 
          },
        },
        {
          intro h330,
          have h331:= h320 (and.intro h330 h23), 
          cases h331 with h332 h333,
          {
            right,
            exact h332, 
          },
          {
            left,
            exact (and.intro h330 h333), 
          }
        } 
      },
      { -- the case b ≠ c,  line 309 of the paper 
        have h450: ∀ y, y ∈ U ↔ ∃ x,(x ∈ A ∧ ‹ x,y › ∈ f):=   -- line 311 
          assume y,
          begin
            rw h25,
            split,
            {
              intro h451,
              rw ( minus_members M) at h451,
              cases h451 with h452 h453,
              rw (singleton1 M) at h453, 
              unfold onto at h13,
              have h454:= h13 y h452,
              cases h454 with x h456, 
              use x,
              cases h456 with h457 h458,
              rw [binary_union_axiom, (singleton1 M)] at h457,
              cases h457 with h459 h460,
              {
                exact (and.intro h459 h458), 
              },
              {
                rw h460 at *,
                have h461:= h18 b c y (and.intro (adjoin_member M b A) (and.intro h24 h458)), 
                rw h460 at *,
                rw h461 at *,
                contradiction,
              }
            },
            {
              intro h470,
              cases h470 with x h471,
              cases h471 with h472 h473,
              have h474:= adjoin_member2 M x b A h472,
              have h475:= h17 x y (and.intro h474 h473),
              rw (minus_members M),
              rw (singleton1 M), 
              split,
              { 
                exact h475
              },
              {
                intro h476,
                rw h476 at *,
                have h477:= h40 x b c (and.intro h473 (and.intro h24 h474)),
                rw h476 at *,
                rw h477 at *,
                contradiction, 
              }
            },
          end,
        
        have h499:∀ (x y:M), (x ∈ A ∪ (single b) → y ∈ A ∪ (single b) → ‹ x,y › ∈ f ∨ ¬ (‹ x,y › ∈ f)):=
        --line 309d 
          assume x y,
          begin
            intros h490 h491,
            have h492:= (decidable_members M (A ∪ (single b))).mp h457,
            have h493:= h19copy x h490,
            cases h493 with p h494,
            cases h494 with h495 h496,
            have h497:p ∈ A ∪ (single b):=
              begin
                rw subset_definition at h10,
                exact h10 p h495, 
              end,
            have h498:= h492 y p (and.intro h491 h497 ),   -- y = p ∨ y ≠ p,  line 309a
            cases h498 with h480 h481,
            {
              left,
              rw h480 at *, 
              exact h496, 
            },
            {
              right,
              intro h482, 
              exact (h481 (h18 x y p (and.intro h490 (and.intro h482 h496)))), 
            },
          end,
        have h500: ∀ (y:M), y ∈ A ∪ (single b)  → y ∈ U ∨ ¬ (y ∈ U):=  -- line 312 
          assume y,
          begin
             intro h501,             
             have h458: A ⊆ A ∪ (single b):= subset_union M A A (single b) (subset_reflexive M A),  
             have h502:= boundedquantification M f (A ∪ (single b)) A,
             have h503:= h502 (and.intro  h3 (and.intro h458 (and.intro h457 h499))) y h501, 
             rw (h450 y), 
             exact h503, 
          end,

        have h400: ¬ (c ∈ U):=
          begin
            rw h25,
            rw (minus_members M),
            intro h401,
            cases h401 with h402 h403,
            rw (singleton1 M) at h403,
            contradiction,
          end,
        have h420: b ∈ A ∪ (single b):=
          begin
            rw binary_union_axiom,
            rw (singleton1 M),
            right,
            exact (refl b), 
          end,
        
        have h421:= h500 b h420,  -- b ∈ U ∨ ¬ (b ∈ U)   line 313
        have h406:= h17 b c (and.intro h420 h24),   -- c ∈ Y 
        cases h421 with h422 h423,
        {  -- case 2a, b ≠ c ∧ b ∈ U
          have h405: b ∈ Y:=
            begin 
              rw h25 at h422,
              rw (minus_members M) at h422,
              exact (and.left h422), 
            end,
          have h410:= swap_similarity M (A ∪ (single b)) U b c h6copy h301 h400 h422 h305, 
          have line314: U - (single b) ∪ (single c) ⊆ A:=  -- S ⊆ A 
            begin
              rw h25,
              rw subset_definition,
              intro z,
              repeat { rw [ binary_union_axiom, (minus_members M)]},
              repeat { rw (singleton1 M)},
              rw (minus_members M),
              rw (singleton1 M),
              intro h411,
              cases h411 with h412 h413, 
              {    -- z ∈ Y ∧ z ≠ c 
                cases h412 with h414 h415,
                cases h414 with h416 h417, 
                rw subset_definition at h10, 
                have h418 := h10 z h416,
                rw binary_union_axiom at h418,
                cases h418 with h419 h420a,
                {
                  exact h419,
                },
                {
                  rw (singleton1 M) at  h420a, 
                  rw h420a at *,
                  contradiction, 
                },
              }, 
              {  -- z = c
                 rw h413 at *,
                 rw binary_union_axiom at h305,
                 cases h305 with h510 h511,
                 {
                   exact h510,  
                 },
                 {
                   rw (singleton1 M) at h511,
                   rw h511 at *,
                   contradiction, 
                 },
              },
            end, 
          have line314b:= similar_transitive M A U (U - single b ∪ single c) h26 h410,   -- A ~ S
          have line315:= h4 (U - single b ∪ single c) line314 line314b,   -- line 315, A = S
          rw line315,
          rw h25,
          rw (full_extensionality M),
          intro z,
          -- repeat { rw [binary_union_axiom, (minus_members M), (singleton1 M)]},
          rw binary_union_axiom,
          rw binary_union_axiom,
          repeat { rw (minus_members M)},
          repeat { rw (singleton1 M)},
          split,
          {
             rw and_or_distrib_right,
             intro h700,
             cases h700 with h701 h702,
             {
               cases h701 with h703 h704, 
               cases h704 with h705 h706, 
               {
                 cases h703 with h707 h708,
                 {
                   exact (and.left h707),
                 },
                 {
                   rw h708 at *,
                   exact h23, 
                 },
               },
               {
                 rw h706 at *,
                 exact h23, 
               },
             },
             {
               rw h702 at *,
               exact h405, 
             },
          },
          {
            intro h600,
            have h601:= h11 z b (and.intro h600  h405), 
            cases h601 with h602 h603, 
            {
              right,
              exact h602, 
            },
            {
              left,
              have h604:= h11 z c (and.intro h600  h23), 
              cases h604 with h605 h606,
              {
                right,
                exact h605,
              },
              {
                left,
                split,
                { 
                  exact (and.intro h600 h606)
                },
                {
                  exact h603,
                }
              }
            },

          },
        },
        { -- case 2b, b ≠ c ∧ ¬ b ∈ U,  line 315f
          have h600: similar M A U:=
            begin
              unfold similar,
              use f,
              unfold similarity,
              unfold oneone,
              unfold maps,
              repeat{ split},   -- 7 goals
              {
                exact h16,
              },
              {
                intros x y h424,
                rw h25,
                rw (minus_members M),
                rw (singleton1 M),
                split,  
                {
                  cases h424 with h425 h426,
                  have h525:= adjoin_member2 M x b A h425,
                  exact( h17 x y (and.intro h525 h426)), 
                },
                {
                  intro h526,
                  rw h526 at *,
                  cases h424 with h527 h528,
                  have h529:= h40 b x c (and.intro h24 (and.intro h528 h420)),
                  rw← h529 at *,
                  contradiction, 
                },
              },
              {
                intros x y z h530,
                cases h530 with h531 h532, 
                have h533:= adjoin_member2 M x b A h531,
                exact ( h18 x y z (and.intro h533 h532)), 
              },
              {
                intros x h534,
                have h535:= adjoin_member2 M x b A h534,
                have h536:= h19copy x h535,
                cases h536 with y h537,
                cases h537 with h538 h539,
                use y,
                split,
                {
                  rw h25,
                  rw (minus_members M),
                  rw (singleton1 M),
                  split,
                  { 
                    exact h538,
                  },
                  {
                    intro h540,
                    rw h540 at *,
                    have h541:= h40 b x c (and.intro h24 (and.intro h539 h420)),
                    rw← h541 at *,
                    contradiction, 
                  }
                },
                { 
                  exact h539, 
                }
              },
              {
                intros x u y h550,
                cases h550 with h551 h552,
                cases h552 with h553 h554,
                have h555:= adjoin_member2 M x b A h554,
                exact (h40 x u y (and.intro h551 (and.intro h553 h555))),
              },
              {  
                intros x y h556,
                cases h556 with h557 h558, 
                rw h25 at h558,
                rw (minus_members M) at h558,
                cases h558 with h559 h560, 
                rw (singleton1 M) at h560,
                have h561:= h41 x y (and.intro h557 h559),
                rw binary_union_axiom at h561,
                cases h561 with h562 h563, 
                {
                  exact h562, 
                },
                {  
                  rw (singleton1 M) at h563,
                  rw h563 at *,
                  have h564:= h18 b c y (and.intro h420 (and.intro h24 h557)), 
                  rw← h564 at *, 
                  contradiction,  
                } 
              },
              {
                unfold onto,
                intros y h565,
                rw subset_definition at h301, 
                have h566:= h301 y h565, 
                unfold onto at h13, 
                rw h25 at h565, 
                rw (minus_members M) at h565,
                rw (singleton1 M) at h565,
                cases h565 with h566 h567,
                have h568:= h13 y h566,
                cases h568 with x h569,
                cases h569 with h570 h571,
                use x,
                rw binary_union_axiom at h570,
                rw (singleton1 M) at h570, 
                cases h570 with h572 h573, 
                { 
                  exact (and.intro h572 h571),
                },
                {
                  rw h573 at *,
                  have h574:= h18 b c y (and.intro h420 (and.intro h24 h571)),
                  rw← h574 at *,
                  contradiction, 
                },
              },
            end,
          have h800:U ⊆ A:=   --line 315h
            begin
              rw subset_definition,
              intros z h801,
              rw h25 at h801,
              rw subset_definition at h10,
              specialize h10 z,
              rw (minus_members M) at h801,
              cases h801 with h802 h803, 
              have h804:= h10 h802, 
              rw binary_union_axiom at h804,
              cases h804 with h805 h806,
              {
                exact h805,
              },
              {
                rw (singleton1 M) at h803,
                rw (singleton1 M) at h806, 
                rw h806 at *,
                have h807: b ∈ U:=
                  begin
                    rw h25,
                    rw (minus_members M),
                    rw (singleton1 M),
                    exact (and.intro h802 h803),
                  end,
                contradiction, 
              },
            end,
          have h810:= h4 U h800 h600,   -- A=U, by the induction hypothesis h4, line 318g
          have h810copy := h810, 
          rw h25 at h810, 
          have h811: U ∪ (single c) = Y:=   -- line 318c
            begin
              rw (full_extensionality M), 
              intro x,
              rw (binary_union_axiom), 
              rw (singleton1 M), 
              have h812: x ∈ Y →  x = c ∨ x ≠ c:=  λ h, h11 x c (and.intro h h23), 
              split,
              {
                intro h813, 
                cases h813 with h814 h815,
                {
                  rw h25 at h814, 
                  rw (minus_members M) at h814, 
                  exact (and.left h814), 
                },
                {
                  rw h815 at *,
                  exact h23, 
                },
              },
              {
                intro h816,
                have h817:= h812 h816,
                cases h817 with h818 h819,
                {
                  right,
                  exact h818,
                },
                {
                  left,
                  rw h25, 
                  rw (minus_members M),
                  rw (singleton1 M), 
                  exact (and.intro h816 h819),
                }
              }, 
            end,
          have h820: U ∪ (single c) ⊆ A ∪ (single b):=   -- line 318e 
            begin
              rw← h811 at h10,
              exact h10, 
            end,
          have h820copy := h820,
          have h821: U ∪ (single c) ⊆ A :=     --line 318f
            begin
              rw (subset_definition),
              intro x,
              rw subset_definition at h820,
              specialize h820 x,
              intro h822,
              have h823:= h820 h822,
              rw binary_union_axiom at h823,
              cases h823 with h824 h825,
              {
                exact h824,
              },
              {
                rw (singleton1 M) at h825,
                rw h825 at *,
                rw binary_union_axiom at h822,
                cases h822 with h826 h827,
                {
                  contradiction,
                },
                {
                  rw (singleton1 M) at h827, 
                  contradiction,
                },
              },
            end,
          rw  h810copy at h821,
          rw subset_definition at h821,
          specialize h821 c,
          have h822:= h821 (adjoin_member M c U),
          rw h25 at h822,
          rw (minus_members M) at h822,
          rw (singleton1 M) at h822,
          cases h822 with h823 h824,
          contradiction, 
        },
      },
    }
  end

theorem Theorem1: ∀ (x:M), x ∈ FINITE M →  ∀ y, (y ⊆ x → (similar M x y) → x=y ):=  --line 293 
  assume x,
  begin
    have h2: (FINITE M)⊆ W15 M := (finite_conditions M) (W15 M)   (lemma15b M) (lemma15a M), 
    rw subset_definition at h2, 
    specialize h2 x,
    rw (W15_members M) at h2,  
    intro h3,
    have h4:= h2 h3, 
    cases h4 with h5 h6, 
    exact h6, 
  end

lemma empty_union: union (Λ:M) = (Λ:M):=
  begin
    rw full_extensionality M,
    intro x,
    rw union_axiom,
    split,
    {
      intro h,
      cases h with z h2,
      cases h2 with h3 h4,
      have h5:= emptyset_axiom z,
      contradiction, 
    },
    {
      intro h,
      have h5:= emptyset_axiom x,
      contradiction, 
    }
  end 

lemma union_adjoin: ∀(y c:M), ¬ c ∈ y → union (y ∪ (single c)) = ((union y) ∪  c):=
  assume y c,
  begin
    intro h,
    rw full_extensionality,
    intro x,
    rw binary_union_axiom,
    rw union_axiom,
    rw union_axiom, 
    split,
    {
      intro h2,
      cases h2 with z h3,
      cases h3 with h4 h5,
      rw binary_union_axiom at h4,
      cases h4 with h6 h7,
      {
        left,
        use z, 
        exact ⟨ h6, h5⟩,
      },
      {
        rw singleton1 M at h7,
        rw h7 at *,
        right, 
        exact h5, 
      }
    },
    {
      intro h2,
      cases h2 with h3 h4,
      {
        cases h3 with z h5,
        cases h5 with h6 h7,
        use z,
        split,
        {
          rw binary_union_axiom,
          left,
          exact h6,
        },
        {
          exact h7, 
        }
      },
      {
        use c,
        rw binary_union_axiom,
        rw singleton1 M,
        simp, 
        exact h4,
      }
    }
  end 

lemma finiteunion_base: (Λ:M) ∈ W16 M:=
  begin
    rw W16_members,
    split,
    {
      exact lambda_finite M, 
    },
    {
      intros h3 h4, 
      rw empty_union, 
      exact lambda_finite M, 
    } 
  end

lemma finiteunion_step:  adjoin_closed M (W16 M) :=
  begin
    unfold adjoin_closed, 
    intros y c,
    rw W16_members, 
    intro h,
    cases h with h3 h4,
    cases h3 with h5 h6,
    rw W16_members,
    split,
    {
      exact finite_adjoin M y c ⟨ h5, h4⟩, 
    },
    {
      intros h h99, 
      rw (union_adjoin M y c h4), 
      have hcopy := h, 
      specialize h c,
      have cFinite:= h( adjoin_member M c y), 
      have h7: union y ∈ FINITE M:=
        begin 
          apply h6,
          { 
            intros u h9,
            apply hcopy,
            rw binary_union_axiom,
            left,
            exact h9, 
          },
          {
            intros u v h10 h11 h12,
            specialize h99 u v,
            apply h99,
            {
              exact adjoin_member2 M u c y h10, 
            },
            {
              exact adjoin_member2 M v c y h11, 
            },
            {
              exact h12, 
            }
          }
        end, 
      have line328: union y ∩ c = Λ :=
        begin
          rw full_extensionality,
          intro p, 
          rw intersection_axiom,
          rw union_axiom, 
          split,
          {
            intro h20,
            cases h20 with h21 h22,
            cases h21 with w h22,
            cases h22 with h23 h24,
            have h25:= h99  w c, 
            rw binary_union_axiom at h25,
            rw singleton1 at h25, 
            rw binary_union_axiom at h25,
            rw singleton1 at h25, 
            have h26: p ∈ w ∩ c:= 
              begin 
                rw intersection_axiom, 
                exact ⟨ h24, h22⟩, 
              end, 
            have h27: ¬ w ∩ c = Λ:=
              begin
                rw full_extensionality,
                intro h100,
                specialize h100 p, 
                rw h100  at h26,
                have h101:= emptyset_axiom p,
                contradiction, 
              end,
            have h30: w ∈ y ∨ w = c → ¬w = c → w ∩ c = Λ:=
              begin
                intros h31 h32,
                have h33:= h25 h31, 
                have h34:= h33 (or.inr (refl c)) h32, 
                exact h34, 
              end,
            have h26:= h30 (or.inl h23), 
            have h27: ¬ w = c :=
              begin
                intro h28,
                rw h28 at *,
                contradiction, 
              end,
            have h28:= h26 h27,
            contradiction,
          },
          {
            intro h8,
            have h9:= emptyset_axiom p h8,
            contradiction, 
          }
        end, 
      exact union M (union y) c h7 cFinite line328, 
    }
  end

lemma finiteunion: ∀ (x:M), x ∈ FINITE M → ( ∀(u:M), (u ∈ x → u ∈ FINITE M)) →
(∀(u v:M), u ∈ x → v ∈ x → ¬ u = v → u ∩ v = Λ) → 
 union x ∈ FINITE M:=
  begin
    have base:= finiteunion_base M,
    have step:= finiteunion_step M,
    have h: (FINITE M) ⊆ W16 M:= finite_conditions M (W16 M) step base, 
    rw subset_definition at h,
    intros x h1, 
    specialize h x,
    rw (W16_members M) at h, 
    have h5:= h h1, 
    cases h5 with h6 h7,
    exact h7, 
  end

#axioms_all   -- This file is clean