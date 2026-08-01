 --   iterated exponentiation 
import inf12
variables (M:Type) [Model M] (a b x y z u v w X R W κ μ ℓ : M)
-- using ℓ where the source text has λ because you can't use λ for a variable.

open Model 


lemma towergraph1:  --towergraph satisfies the first equation 
   ∀ (m:M), triple m zero m ∈ towergraph M := 
  begin
    intro m,
    rw towergraph_members,
    split,
    {
      exact zeroF M,
    },
    { 
      intro Z,
      intro h,
      cases h with h2 h3,
      specialize h2 m, 
      exact h2, 
    }
  end

lemma towergraph2:  --towergraph satisfies the second equation
  ∀ (m y z:M), triple m y z ∈ towergraph M → (∃ u, u ∈ 𝕊 y) → 
  triple m (𝕊 y) ( exp M z) ∈ towergraph M :=
  begin
    intros m y z h20,
    have hcopy := h20, 
    intro h22, 
    rw towergraph_members M,  
    rw towergraph_members at h20,
    cases h20 with h21 h23, 
    split,
    { 
      exact successorF M y h21 h22, 
    },
    { intro Z, 
      intro h, 
      have h24:= h23 Z h,
      cases h with h25 h26,
      specialize h26 m y z, 
      exact h26 h24 h22, 
    }
  end

lemma towergraphimpliesyinF: ∀ (m y z:M), triple m y z ∈ towergraph M → y ∈ 𝔽 :=
  assume m y z,
  begin
    intro h,
    rw towergraph_members M at h,
    cases h with h2 h3,
    exact h2,
  end
  
lemma towerhelper: ∀ (m y z:M),  triple m y z ∈ towergraph M → (y=zero ∧ z = m) ∨
∃ (u v w:M), y = 𝕊 u ∧ v ∈ y ∧ triple m u w ∈ towergraph M ∧ z = exp M w :=

  begin 
    have base: ∀(m:M), triple m zero m ∈ W81 M:=    
      assume m, 
      begin
        rw W81_members,
        use m , use zero, use m,
        split, 
        {
          exact refl (triple m zero m),
        },
        {
          split,
          {
            exact towergraph1 M m,
          },
          {
            left,
            simp, 
          }
        }
      end,
    have step: ∀ (m y z:M), triple m y z ∈ W81 M → (∃ u, u ∈ 𝕊 y) → triple m  (𝕊 y)  (exp M z) ∈ W81 M :=
      begin 
        assume m y z,
        intro h2,
        rw W81_members at h2,
        cases h2 with p h3,
        cases h3 with q h4,
        cases h4 with r h5,
        cases h5 with h6 h7,
        rw triple_equality at h6,
        rcases h6 with ⟨ h8,h9, h10⟩,
        rw← h8 at *,
        rw← h9 at *,
        rw← h10 at *,
        cases h7 with h11 h12,
        cases h12 with h13 h14,
        {
          cases h13 with h15 h16,
          rw h15 at *,
          rw h16 at *,
          intro h17,
          rw W81_members M,
          use m,
          use 𝕊 zero,
          use exp M m,
          split,
          { 
            exact refl (triple m (𝕊 zero) (exp M m)),
          },
          {
            split,
            {
              rw towergraph_members M,
              split,
              {
                exact successorF M zero (zeroF M) h17, 
              },
              intros Z h18,
              cases h18 with h19 h20,
              specialize h20 m zero m,
              apply h20,
              {
                exact h19 m, 
              },
              {
                exact h17,
              },
            },
            {
              right,
              use zero, 
              cases h17 with u h18,
              use u,
              use m,
              simp,
              exact ⟨ h18, h11⟩, 
            }
          }
        },
        {
          cases h14 with u h15,
          cases h15 with v h16,
          cases h16 with w h17,
          rcases h17 with ⟨ h18, h19, h20, h21⟩,
          intro h22,
          rw W81_members M,
          use m, use 𝕊 y, use exp M z,
          split,
          { 
            simp,
          },
          {
            split,
            {
              exact towergraph2 M m y z h11 h22, 
            },
            {
              right,
              use y,
              cases h22 with v h23,
              use v,
              use exp M w,
              rw← h21, 
              simp,
              exact ⟨ h23, h11⟩,
            }
          }
        }
      end,
    have conclusion: towergraph M ⊆ W81 M:=
      begin
        rw subset_definition,
        intro t,
        intro h,
        have h2:= towergraph_members2 M t h,
        cases h2 with m h3,
        cases h3 with y h4,
        cases h4 with z h5,
        rw h5 at *,
        rw towergraph_members M at h,
        cases h with h6 h7,
        specialize h7 (W81 M),
        apply h7,
        split,
        {
          exact base,
        },
        {
          exact step, 
        }
      end,
    
    intros m y z h2,
    have h1: y ∈ 𝔽 := towergraphimpliesyinF M m y z h2, 
    have h3:= member_subset M (towergraph M) (W81 M) (triple m y z) conclusion h2,
    have h4:= step m y z h3,
    have h5: y = zero ∨ ¬ y = zero:= corollary42 M y zero h1 (zeroF M), 
    cases h5 with h6 h7,
    {
      rw h6 at *,
      left,
      split,
      {
        exact (refl zero),
      },
      {
        rw W81_members at h3,
        cases h3 with p h4,
        cases h4 with q h5,
        cases h5 with r h6,
        cases h6 with h7 h8,
        rw triple_equality at h7,
        rcases h7 with ⟨ h9, h10, h11⟩, 
        rw← h9 at *,
        rw← h10 at *,
        rw← h11 at *,
        cases h8 with h9 h10,
        cases h10 with h11 h12,
        {
          exact h11.right, 
        },
        {
          cases h12 with a h13,
          cases h13 with b h14,
          cases h14 with c h15,
          cases h15 with h16 h17,
          have h18:= Fregesuccessoromits0 M a,
          rw sym at h16,
          contradiction, 
        }
      }
    },
    {
      right,
      have h8:= nonzeroissuccessor M y h1 h7,
      cases h8 with u h9,
      cases h9 with h10 h11,
      rw W81_members at h3,
      cases h3 with p h34,
      cases h34 with q h35,
      cases h35 with r h36,
      cases h36 with h37 h38,
      rw triple_equality at h37,
      rcases h37 with ⟨ h39, h40, h41⟩, 
      cases h38 with h42 h43,
      cases h43 with h44 h45,
      {
        cases h44 with h46 h47,
        rw h46 at *,
        rw h47 at *,
        rw h40 at *,
        contradiction,
      },
      {
        simp_rw h39,
        simp_rw h40,
        simp_rw h41,
        exact h45,  
      }
    }
  end 


lemma towermaps: ∀ (m y:M), y ∈ 𝔽 → ∃(z:M), triple m y z ∈ towergraph M:=
  begin
    have base: (zero:M) ∈ Z_tower_defined M:=
      begin
        rw Z_tower_defined_members M,
        split,
        {
          exact (zeroF M),
        },
        {
          intro m,
          use m,
          rw towergraph_members,
          split,
          {
            exact zeroF M,
          },
          {
            intros Z h,
            cases h with h2 h3,
            exact h2 m, 
          }
        }
      end,
    have step: ∀(y:M), y ∈ Z_tower_defined M → (∃(u:M), u ∈ 𝕊 y) → 𝕊 y ∈ Z_tower_defined M:=
      assume y,
      begin
        intros h1 h2,
        rw Z_tower_defined_members,
        rw Z_tower_defined_members at h1,
        cases h1 with h3 h4,
        split,
        {
          exact successorF M y h3 h2, 
        },
        {
          intro m,
          specialize h4 m,
          cases h4 with z h5, 
          use exp M z,
          exact towergraph2 M m y z h5 h2,
        }
      end, 
    intros m y h, 
    rw F_members at h, 
    specialize h ( Z_tower_defined M),
    have h3:= h (and.intro base  step), 
    rw ( Z_tower_defined_members M) at h3, 
    cases h3 with h5 h6, 
    exact h6 m, 
  end 

 

lemma tower_singlevalued: ∀ (y x z w:M ), triple x y z ∈ towergraph M → 
triple x y w ∈ towergraph M → z = w := 
  begin 
    have base: zero ∈ Z82 M:=
      begin
        rw Z82_members,
        split,
        { 
          exact zeroF M,
        },
        { 
          intros m z w,
          intro h,
          intro h7,
          have h2:= towerhelper M m zero z h, 
          have h12:= towerhelper M m zero w h7, 
          cases h2 with h3 h4,
          {
            cases h3 with h5 h6,
            rw h6 at *,
            cases h12 with h8 h9,
            { 
              cases h8 with h10 h11,
              rw h11 at *,
            },
            {
              cases h9 with u h30,
              cases h30 with v h31,
              cases h31 with p h32,
              cases h32 with h33 h34,
              have h35:= Fregesuccessoromits0 M u,
              rw sym at h33,
              contradiction,
            }
          },
          {
            cases h12 with h8 h9,
            { cases h8 with h10 h11,
              rw h11 at *,
              have h2:= towerhelper M m zero z h, 
              cases h2 with h40 h41,
              { 
                exact h40.right, 
              },
              {
                cases h41 with u h42,
                cases h42 with v h43,
                cases h43 with p h34,
                cases h34 with h35 h36,
                have h37:= Fregesuccessoromits0 M u,
                rw sym at h35,
                contradiction,
              }
            },
            {
              cases h4 with u h5,
              cases h5 with v h6,
              cases h6 with p h7,
              cases h7 with h8 h9,
              have h10:= Fregesuccessoromits0 M u,
              rw sym at h8,
              contradiction,
            }
          } 
        }
      end,

    have step: ∀(y:M),  y ∈ Z82 M → (∃ u, u ∈ 𝕊 y) → 𝕊 y ∈ Z82 M:=
      assume y,
      begin 
        intros  h1 h2,
        rw Z82_members M at h1,
        have h135:= h1,
        cases h135 with h136 h137,
        have h := h136,
        rw Z82_members M,
        split,
        {
          exact successorF M y h h2,
        },
        {  
          intros m z Z,
          cases h1 with h3 h4,
          --specialize h4 m z Z,
          intro h5,
          have h6:= towerhelper M m (𝕊 y) z h5, 
          cases h6 with h7 h8,
          { 
            cases h7 with h9 h10,
            have h11:= Fregesuccessoromits0 M y,
            contradiction, 
          },
          {
            cases h8 with p h9,
            cases h9 with q h10,
            cases h10 with r h11,
            rcases h11 with ⟨ h12, h13,h14,h15⟩,
            intro h16,
            have h26:= towerhelper M m (𝕊 y) Z h16,
            cases h26 with h27 h28,
            {
              have h29:= Fregesuccessoromits0 M y,
              cases h27 with h30 h31,
              contradiction,
            },
            {
              cases h28 with u h30,
              cases h30 with v h31,
              cases h31 with w h32,
              rcases h32 with ⟨ h33, h34, h35, h36⟩,
              -- need to get u ∈ 𝔽 
              have h35copy := h35,
              have h40: u ∈ 𝔽:=
                begin
                  rw towergraph_members at h35copy,
                  cases h35copy with h50 h51,
                  exact h50,
                end,
              have h37:y = u:=
                begin
                  have h39:= h2,
                  cases h39 with r h50,
                  rw  h33 at h50,
                  exact (successoroneone M y u h h40 h2 ⟨r, h50⟩).mpr h33 ,
                end,
              rw← h37 at *,  
              -- need to get p ∈ 𝔽 
              have h14copy := h14,
              have h60: p ∈ 𝔽:=
                begin 
                  rw towergraph_members at h14copy,
                  cases h14copy with h61 h62,
                  exact h61, 
                end,
              have h65:= h2,
              rw h12 at h65, 
              have h51:= (successoroneone M y p h h60 h2 h65).mpr h12, 
              rw← h51 at *, 
              have h120:= h4 m w r h35 h14,
              rw← h120 at *, 
              rw [h36, h15], 
            }
          }
        }
      end,
    intros y x z w h2,
    have hcopy:= h2, 
    rw towergraph_members at hcopy, 
    cases hcopy with h h4,
    rw F_members y at h,
    specialize h (Z82 M), 
    have h20:= h ⟨ base, step⟩,
    rw Z82_members at h20,
    cases h20 with h21 h22,
    have h23:= h22 x z w h2,
    exact h23, 
  end 


lemma tower_base_equation: ∀( m:M),   𝕀 M m zero = m  := 
  assume  m,
  begin
    rw full_extensionality,
    intro t,
    rw I_members M, 
    split,
    { 
      intro h2,
      cases h2 with z h3,
      cases h3 with h4 h5,
      have h6:=  towerhelper M m zero z  h4, 
      cases h6 with h7 h8,
      {
        simp at h7,
        rw h7 at h5,
        exact h5, 
      },
      {
        cases h8 with u h9,
        cases h9 with v h10,
        cases h10 with w h11,
        cases h11 with h12 h13,
        have h14: 𝕊 u = zero:= 
          begin 
            rw sym,
            exact h12,
          end, 
        have h15:= Fregesuccessoromits0 M u h14, 
        contradiction, 
      },
    },
    {
      intro h2,
      use m,
      exact ⟨ towergraph1 M m, h2⟩, 
    }
  end

lemma I_introduction: ∀ (m z y:M), y∈ 𝔽 → ( triple m y z ∈ towergraph M ↔ z = 𝕀 M m y):=
  begin 
    have base: (zero:M) ∈ Z83 M:=
      begin 
        rw Z83_members M,
        split,
        {
          exact zeroF M, 
        },
        {
          intros m z,
          rw tower_base_equation M m,
          split,
          {
            intro h,
            have h2:= towerhelper M m zero z h,
            cases h2 with h3 h4,
            {
               exact h3.right, 
            },
            {
              cases h4 with p h5,
              cases h5 with q h6,
              cases h6 with r h7,
              rcases h7 with ⟨ h8, h9, h10, h11⟩,
              have h12: p ∈ 𝔽 := towergraphimpliesyinF M m p r  h10, 
              have h13: 𝕊 p = zero := 
                begin  
                  rw sym,
                  exact h8,
                end, 
              have h14:= Fregesuccessoromits0 M p h13, 
              contradiction,
            }
          },
          {
            intro h,
            rw h at *,
            exact towergraph1 M m,
          }
        }
      end, 
    have step: ∀(y:M), y ∈ Z83 M → (∃ u, u ∈ 𝕊 y) → 𝕊 y ∈ Z83 M:=
      assume y,
      begin
        intros h h2,
        rw Z83_members M at h,
        rw Z83_members M,
        cases h with h3 h4,
        split,
        {
          exact successorF M y h3 h2,
        },
        { 
          intros m w,   -- formula (54) in the paper 
          have h5: triple m (𝕊 y) w ∈ towergraph M ↔ w = exp M (𝕀 M m y):=
            begin
              split,
              {
                intro h6,
                have h7:= towerhelper M m (𝕊 y) w h6,
                cases h7 with h8 h9,
                {
                  cases h8 with h10 h11,
                  have h12:= Fregesuccessoromits0 M y h10,
                  contradiction,
                },
                {
                  cases h9 with u h10,
                  cases h10 with v h11,
                  cases h11 with p h12,
                  rcases h12 with ⟨ h13, h14, h15, h16⟩,
                  rw h13 at h14,
                  have h18:= towergraphimpliesyinF M m u p h15,
                  have h116:= (successoroneone M y u h3 h18 h2 ⟨ v, h14⟩).mpr h13,
                  rw← h116 at *,
                  rw h4 m p  at h15, 
                  rw← h15,
                  exact h16,
                }
              },
              {
                intro h5,
                have h6:= towergraph2 M m y (𝕀 M m y),
                specialize h4 m (𝕀 M m y),
                simp at h4,
                have h7:= h6 h4 h2,
                rw h5, 
                exact h7, 
              }
            end,
          have h6: w = 𝕀 M m (𝕊 y) ↔ w = exp M (𝕀 M m y):=
            begin
              set p:= exp M (𝕀 M m y) with h8,
              have h9:  triple m (𝕊 y) p ∈ towergraph M:=
                begin 
                  specialize h4 m (𝕀 M m y),
                  simp at h4, 
                  have h10:= towergraph2 M m y (𝕀 M m y) h4 h2,
                  rw h8,
                  exact h10, 
                end, 
              split,
              {
                intro h7,
                rw full_extensionality at h7,
                simp_rw I_members at h7,
                rw full_extensionality,
                intro t,
                split,
                {
                  specialize h7 t,
                  intro h10,
                  rw h7 at h10,
                  cases h10 with q h11,
                  cases h11 with h12 h13,
                  have h14:= tower_singlevalued M (𝕊 y) m p q h9 h12,
                  rw h14 at *,
                  exact h13,
                },
                {
                  intro h8,
                  specialize h7 t,
                  rw h7,
                  use p,
                  exact ⟨ h9, h8⟩,
                }
              },
              {
                intro h10,
                rw h10 at *,
                simp at h5,
                rw full_extensionality,
                intro t,
                split,
                {
                  intro h11, 
                  rw I_members M,
                  use p,
                  exact ⟨ h5, h11⟩, 
                },
                {
                  intro h11, 
                  rw I_members at h11,
                  cases h11 with z h12,
                  cases h12 with h13 h14,
                  have h15:= tower_singlevalued M (𝕊 y) m p z h5 h13,
                  rw h15 at *,
                  exact h14, 
                } 
              }, 
            end,
          rw h6,
          exact h5, 
        }
      end,
    have h100: ∀(y:M), y ∈ 𝔽 → y ∈ Z83 M:=
      assume y,
      begin
        intro h,
        rw F_members y at h, 
        specialize h  (Z83 M),
        have h2:= h ⟨ base, step⟩, 
        exact h2,
      end,
    intros m z y,
    specialize h100 y,
    rw Z83_members at h100,
    intro h300,
    have h301:= h100 h300, 
    cases h301 with h302 h303,
    specialize h303 m z,
    exact h303,
  end 

lemma tower_recursion_equation: ∀(m y:M),  y ∈ 𝔽 → (∃ u, u ∈ (𝕊 y)) → 𝕀 M m (𝕊 y) = exp M (𝕀 M m y) :=
  assume m y,
  begin
    intros h1 h2, 
    have h3: triple m (𝕊 y) (𝕀 M m (𝕊 y)) ∈ towergraph M:=  --line 1101 of the paper
      begin
        rw I_introduction M m (𝕀 M m (𝕊 y)) (𝕊 y) (successorF M y h1 h2),        
      end,
    have h4:= towerhelper M m (𝕊 y) (𝕀 M m (𝕊 y)) h3,
    cases h4 with h5 h6,
    {
      cases h5 with h7 h8,
      have h9:= Fregesuccessoromits0 M y  h7, 
      contradiction,
    },
    {
      cases h6 with u h7,
      cases h7 with v h8,
      cases h8 with w h9,
      rcases h9 with ⟨ h10, h11, h12,h13⟩,
      rw h10 at h11,
      have h14:= towergraphimpliesyinF M m u w h12,
      have h113:= (successoroneone M y u h1 h14 h2 ⟨ v, h11⟩).mpr h10,
      rw← h113 at *,
      rw I_introduction M m w y h1 at h12,   --line 1102 of the paper
      rw← h12,
      exact h13,
    }
  end

lemma towerF: ∀ (m:M), m ∈ 𝔽 → ∀ (y:M), y ∈ 𝔽 → (∃ u, u ∈ 𝕀 M m y) → 𝕀 M m y ∈ 𝔽 :=
  assume  m,
  begin 
    intro h2,
    have base: zero ∈ Z86 M m:=
      begin 
        rw Z86_members, 
        split,
        {
          exact zeroF M,
        },
        { 
          intro h3,
          cases h3 with u h4,
          rw tower_base_equation,
          exact h2,
        }
      end,
    have step: ∀(y:M),  y ∈ Z86 M m → (∃ u, u ∈ 𝕊 y) → 𝕊 y ∈ Z86 M m :=
      begin 
        intros y h3 h4, 
        rw Z86_members at h3, 
        cases h3 with h5 h6,
        have h7: 𝕀 M m (𝕊 y) = exp M (𝕀 M m y):= tower_recursion_equation M m y h5 h4, 
        rw Z86_members,
        split,
        {
          exact successorF M y h5 h4, 
        },
        {
          intro h8,
          simp_rw h7 at h8,  -- line 1106b
          cases h8 with u h9,
          rw exp_members M at h9,
          cases h9 with a h10,
          cases h10 with h11 h12,
          have h13: exists u, u ∈ 𝕀 M m y:= ⟨ USC a, h11 ⟩, 
          have h14:= h6 h13,
          have h15: SSC a ∈ exp M (𝕀 M m y):=
            begin
              rw exp_members M,
              use a,
              exact ⟨ h11, similar_reflexive M (SSC a)⟩, 
            end,
          have h16:= finiteexp M (𝕀 M m y) h14 ⟨ SSC a, h15⟩, 
          have h17:= tower_recursion_equation M  m y h5 h4,
          rw h17,
          exact h16,  
        }  
      end,
    intros y h,
    rw F_members y at h,
    specialize h (Z86 M m),
    have h200:= h ⟨ base, step⟩,
    rw Z86_members at h200,
    exact h200.right,   
  end

lemma towerNC:  ∀ (m:M), m ∈ NC M → ∀ (y:M), y ∈ 𝔽 →  (∃ (u:M), u ∈ 𝕀 M m y) → 𝕀 M m y ∈ NC M := 
  assume m, 
  begin
    intro hm, 
    have base: (zero:M) ∈ Z_towerNC M m:=
      begin
        rw Z_towerNC_members,
        split,
        {
          exact zeroF M,
        },
        {
          intros h2,
          cases h2 with u h3,
          rw tower_base_equation M m at *,
          exact hm, 
        }
      end,
    have step: ∀ (y:M), y ∈ Z_towerNC M m → (∃ u, u ∈ 𝕊 y) → 𝕊 y ∈ Z_towerNC M m:=
      assume y,
      begin
        intros h2 h, 
        rw Z_towerNC_members at *,
        have hsy:= successorF M y h2.1 h,
        cases h2 with h3 h4,
        split,
        {
          exact hsy,
        },
        {  
          intros h6, 
          cases h6 with u h8,
          have h9:= tower_recursion_equation M m y h3 h,
          rw h9 at h8,
          have h8copy:= h8,
          rw exp_members at h8,
          cases h8 with a h10,
          cases h10 with h11 h12,
          have h13:= h4 ⟨ USC a, h11⟩, 
          rw h9,
          have h14:= NCexp M (𝕀 M m y) h13 ⟨ u, h8copy⟩ , 
          exact h14,
        }
      end,
    intros y h,  
    rw F_members at h, 
    specialize h ( Z_towerNC M m),
    have h3:= h (and.intro base  step), 
    rw ( Z_towerNC_members M m) at h3, 
    cases h3 with h5 h6, 
    exact h6, 
  end


lemma zero_le_x: ∀ (x:M), x ∈ 𝔽 → zero ≤ x:=
  assume x,
  begin
    intro h,
    rw le_definition,
    use Λ,
    have h2:=cardinalsinhabited M x h,
    cases h2 with b h3,
    use b,
    repeat{split},
    {
      rw zero_definition, 
      rw singleton1 M,
    },
    {
      exact h3,
    },
    {
      exact empty_always_subset M b,
    },
    {
      have h5:=  empty_separable M b,
      unfold separable_subset at h5,
      cases h5 with h6 h7,
      exact h7,
    }
  end

lemma zero_le_xNC: ∀ (x:M), x ∈ NC M → zero ≤ x:=
  assume x,
  begin
    intro h,
    rw le_definition,
    use Λ,
    have h2:=cardinalsinhabited2 M x h,
    cases h2 with b h3,
    use b,
    repeat{split},
    {
      rw zero_definition, 
      rw singleton1 M,
    },
    {
      exact h3,
    },
    {
      exact empty_always_subset M b,
    },
    {
      have h5:=  empty_separable M b,
      unfold separable_subset at h5,
      cases h5 with h6 h7,
      exact h7,
    }
  end

lemma towerincreasing: ∀ (m:M), m ∈ 𝔽  → ∀ (y:M), y ∈ 𝔽 → (∃ u, u ∈ 𝕀 M m y) → y ≤ 𝕀 M m y:=
  assume m,
  begin
    have base:zero ∈  Z87F M m:=
      begin
        rw Z87F_members,
        split,
        {
          exact zeroF M,
        },
        {
          intros h h2,
          rw tower_base_equation M,
          exact zero_le_x M m h,
        }
      end,
    have step: ∀(y:M),  y ∈ Z87F M m → (∃ u, u ∈ 𝕊 y) → 𝕊 y ∈ Z87F M m :=
      begin
        intros y h3 h4,
        rw Z87F_members M,
        rw Z87F_members at h3, 
        cases h3 with h5 h6, 
        split,
        {
          exact successorF M y h5 h4, 
        },
        {
          intro h7,
          have h8:= h6 h7,
          intro h9,
          have h9copy:= h9,
          cases h9 with u h10,
          rw tower_recursion_equation M m y h5 h4 at h10,
          have h10copy:= h10,
          rw exp_members at h10,
          cases h10 with a h11,
          cases h11 with h12 h13,
          have h14: ∃ u, u ∈ 𝕀 M m y:= ⟨ USC a, h12⟩, 
          have h15:= h6 h7 h14,
          have h16:= towerF M m h7 y h5 h14, 
          have h17:= exporder M y (𝕀 M m y) h5 h16 h15 ⟨ u, h10copy⟩,
          cases h17 with h18 h19,
          have h38: 𝕀 M m y ∈ 𝔽 := towerF M m h7 y h5 h14,
          have h20:= exporder M y (𝕀 M m y) h5 h38 h15 ⟨ u, h10copy⟩, 
          cases h20 with h21 h22, 
          have h23:= cardinalsinhabited M (𝕀 M m y) h38,
          have h24:= mlessthanexpm M y h5 h21,
          have h25: exp M y ∈ 𝔽 := finiteexp M y h5 h21,
          have h27:= successorF M y h5 h4,
          have h28:= towerF M m h7 (𝕊 y) h27 h9copy,
          have h29:= tower_recursion_equation M m y h5 h4,
          rw h29 at h28,
          have h30: 𝕊 y ≤ exp M y:= mplusone_le_expm M y h5 h18, 
          have h32:= le_transitive M (𝕊 y) (exp M (𝕀 M m y)) (exp M y) h27 h28 h25 h30 h22,
          rw h29,
          exact h32, 
        }
      end, 
    intros h2 y h, 
    rw F_members y at h,
    specialize h (Z87F M m),
    have h200:= h ⟨ base, step⟩,
    rw Z87F_members at h200,
    cases h200 with h201 h202,
    exact h202 h2,   
  end

lemma towerstrictlyincreasing: ∀ (y:M), y ∈ 𝔽 →  ∀ (m:M), m ∈ 𝔽 → (∃ (u:M), u ∈ 𝕀 M m y)→ (¬ ((y = zero ∨ y = one ∨ y = two) ∧ m = zero)) → y < 𝕀 M m y:=
  begin
    have base: zero ∈ Z_towerstrictlyincreasing M:=
      begin
        rw Z_towerstrictlyincreasing_members,
        split,
        {
          exact zeroF M,
        },
        {
          intros m h h2 h3,
          rw tower_base_equation M,
          simp at h3, 
          rw lessthan_definition,
          split,
          {
            exact zero_le_x M m h, 
          },
          { 
            rw sym,
            exact h3, 
          }
        }
      end,
    have step: ∀(y:M), y ∈ Z_towerstrictlyincreasing M → (∃(u:M), u ∈ 𝕊 y) → 𝕊 y ∈ Z_towerstrictlyincreasing M:=
      begin 
        intro y, 
        rw Z_towerstrictlyincreasing_members M, 
        intros  h h2,
        cases h with h3 h4, 
        rw Z_towerstrictlyincreasing_members M, 
        split,
        {
          exact successorF M y h3 h2, 
        },
        intros m h5 h6 h7,  
        have h40:= h4 m h5, 
        cases h6 with u h9,
        have h9copy:= h9, 
        rw tower_recursion_equation M m y h3 h2 at h9, 
        have h90 := h9, 
        have h42:= mlessthanexpm M y h3, 
        rw exp_members at h9,
        cases h9 with a h10,
        cases h10 with h11 h12,
        have h13:= h4 m h5 ⟨ USC a, h11⟩, 
        have h14:= towerincreasing M m h5 y h3 ⟨ USC a, h11⟩, 
        have h38: 𝕀 M m y ∈ 𝔽 := towerF M m h5 y h3 ⟨ USC a, h11⟩, 
        have h17:= exporder M y (𝕀 M m y) h3 h38 h14 ⟨ u, h90⟩,
        cases h17 with h18 h19, 
        have h15:= FregeNdecidable M,
        rw decidable_members M at h15, 
        have h16 := h15 y zero ⟨ h3 ,(zeroF M)⟩ ,
        have h17 := h15 m zero ⟨ h5, (zeroF M)⟩, 
        have h20 := successorF M y h3 h2, 
        have h21 := h15 (𝕊 y) zero ⟨ h20, zeroF M⟩, 
        have h22 := h15 (𝕊 y) one  ⟨ h20, oneF M⟩, 
        have h23 := h15 y one ⟨ h3, (oneF M)⟩, 
        have h24 := h15 (𝕊 y) two  ⟨ h20, twoF M⟩, 
        have h35 := h15 y two ⟨ h3, (twoF M)⟩, 
        have h219: ∃(u:M), u ∈ 𝕊 zero:=
          begin
            rw← one_definition,
            use zero,
            rw one_members, 
            use Λ,
            rw zero_definition, 
          end,
        have h91: ((𝕊 y = zero ∨ 𝕊 y = one ∨ 𝕊 y = two) ∧ m = zero) ∨ ¬ (((𝕊 y = zero ∨ 𝕊 y = one ∨ 𝕊 y = two) ∧ m = zero)):=
          begin
            cases h17 with h100 h101,
            {
              cases h21 with h102 h103,
              {
                left,
                exact ⟨ or.inl h102, h100⟩,
              },
              {
                cases h22 with h104 h105,
                {
                  left,
                  exact ⟨ or.inr (or.inl h104), h100⟩,
                },
                {
                  cases h24 with h106 h107,
                  {
                    left,
                    exact ⟨ or.inr (or.inr h106), h100⟩,
                  },
                  {
                    right,
                    intro h108,
                    cases h108 with h109 h110,
                    cases h109 with h111 h112,
                    {
                      contradiction, 
                    },
                    {
                      cases h112 with h113 h114,
                      {
                        contradiction,
                      },
                      {
                        contradiction, 
                      }
                    }
                  }
                }
              }
            },
            {
              right,
              intro h102,
              cases h102 with h103 h104,
              contradiction,
            }   
          end, 
        cases h91 with h92 h93,
        {  
            contradiction, 
        },
        {   
          rw tower_recursion_equation M m y  h3 h2,
          have h8:= mlessthanexpm M (𝕊 y) (successorF M y h3 h2),
          push_neg at h93, 
          rw exp_members at h90,
          have h90copy:= h90,
          cases h90 with a h10,
          cases h10 with h11 h12,
          have h13:= h4 m h5 ⟨ USC a, h11⟩, 
          have h14:= towerincreasing M m h5 y h3 ⟨ USC a, h11⟩, 
          have h15:= towerF M m h5 y h3 ⟨ USC a, h11⟩, 
          have h116:= h42 h18,
          have h110: ((y = zero ∨ y = one ∨ y = two) ∧ m = zero) ∨ ¬((y = zero ∨ y = one ∨ y = two) ∧ m = zero) :=
            begin
              cases h17 with h200 h201,
              { 
                cases h16 with h202 h203,
                {
                  left,
                  exact ⟨ or.inl h202, h200 ⟩, 
                },
                {
                  cases h23 with h204 h205,
                  {
                    left,
                    exact ⟨ or.inr (or.inl h204), h200⟩,
                  },
                  {
                    cases h35 with h206 h207,
                    {
                      left,
                      exact ⟨ or.inr (or.inr h206), h200⟩,
                    },
                    {
                      right,
                      intro h208,
                      cases h208 with h209 h210,
                      cases h209 with h211 h212,
                      {
                        contradiction,
                      },
                      {
                        cases h212 with h213 h214,
                        {
                          contradiction,
                        },
                        {
                          contradiction,
                        }
                      }
                    }
                  }
                }
              },
              {
                right,
                intro h202,
                cases h202 with h203 h204,
                contradiction, 
              }
            end, 
          cases h110 with h111 h112,
          {  --the exceptional cases y=1,2,3 and m = 0
            cases h111 with h113 h114, 
            rw h114 at *,
            cases h113 with h115 h116, 
            {  
              rw h115 at *,
              simp at h13, 
              rw tower_base_equation M zero at *,
              rw one_definition at h93, 
              simp at h93, 
              contradiction, 
            },
            { cases h116 with h117 h118,
              {
                  rw h117 at *,
                  rw two_definition at h7,
                  simp at h7,
                  contradiction,  
              },
              {
                rw h118 at *,
                rw← three_definition,
                rw two_definition,
                have h119:= cardinalsinhabited M two (twoF M),
                rw two_definition at h119,
                have h120:= tower_recursion_equation M zero one  (oneF M) h119, 
                rw h120,
                rw one_definition,
                have h121:= cardinalsinhabited M one (oneF M),
                rw one_definition at h121,
                rw tower_recursion_equation M zero zero (zeroF M) h121,
                rw tower_base_equation M zero,
                rw exp_zero M,
                rw exp_one M,
                rw exp_two M, 
                exact three_lessthan_four M, 
              }
            }
          },
          { --the non-exceptional cases
            have h114:= h13 h112,
            have h115:= noinsertions M y ( 𝕀 M m y) h3 h15 h114,
            have h116:= le_definition (exp M y) (exp M (𝕀 M m y)),
            have h117:= h116.mp  h19,  
            cases h117 with r h118,
            cases h118 with s h119,
            rcases h119 with ⟨ h120, h121, h122⟩, 
            have h130:= mlessthanexpm M (𝕀 M m y) h15 ⟨ s, h121⟩,
            have h131:= finiteexp M (𝕀 M m y) h15 ⟨ s, h121⟩ ,
            have h132:= le_transitive3 M (𝕊 y)(𝕀 M m y)(exp M (𝕀 M m y)) 
                h20 h15 h131  h115 h130, 
            exact h132, 
          }
        }
      end,
    intros y h m h2, 
    rw F_members y at h,
    specialize h (Z_towerstrictlyincreasing M),
    have h200:= h ⟨ base, step⟩,
    rw Z_towerstrictlyincreasing_members at h200,
    cases h200 with h201 h202,
    exact h202 m h2, 
  end

lemma IinF: ∀ (m:M), m ∈ 𝔽 → ∀(y:M),y ∈ 𝔽 → (∃(u:M), u ∈ 𝕀 M m y) → 𝕀 M m y ∈ 𝔽:=
  begin
    intros m hm,
    have base: zero  ∈ ZIinF M m:=
      begin
        rw ZIinF_members,
        split,
        {
          exact zeroF M,
        },
        {
          intros h3 h4,
          rw tower_base_equation,
          exact hm,
        }
      end,
    have step: ∀( y:M), y ∈ ZIinF M m → (∃(u:M), u ∈ 𝕊 y) → 𝕊 y ∈ ZIinF M m:=
      begin
        intros  y h5 h6,
        rw ZIinF_members M m,
        rw ZIinF_members M m at h5,
        cases h5 with h7 h8,
        split,
        {
          exact successorF M y h7 h6,
        },
        {
          intros h9 h10,
          have h11:= h8 h9,
          cases h10 with u h12,
          rw tower_recursion_equation M m y h7 h6 at h12,
          rw tower_recursion_equation M m y h7 h6,
          have h13:= (exp_inhabited M (𝕀 M m y)).2 ⟨ u, h12⟩ ,
          cases h13 with a h14,
          have h15:= h11 ⟨ USC a, h14⟩,
          have h16:= expdef M (𝕀 M m y) a h15 h14,
          rw h16,
          have h17:= finitecardinals3 M,
          apply h17,
          have h18:= finitepowerset M a,
          apply h18,
          have h19:= finitecardinals1 M (𝕀 M m y) (USC a) h15 h14,
          have h20:= uscfinite M a,
          rw h20 at h19,
          exact h19,
        }
      end, 
    intros y hy,
    rw F_members at hy,
    specialize hy (ZIinF M m),
    have h12:= hy ⟨base,step⟩,
    rw ZIinF_members at h12,
    cases h12 with h13 h14,
    have h15:= h14 hm,
    exact h15, 
  end  
  
lemma mleImy: ∀ (m:M), m ∈ 𝔽 → ∀ (y:M), y ∈ 𝔽  → 𝕀 M m y ∈ 𝔽  → m ≤ 𝕀 M m y:=
  assume m hm, 
  begin 
    have base: (zero:M) ∈ Zsixpointfour M m, 
      begin 
        rw Zsixpointfour_members M, 
        split,
        { 
          exact (zeroF M),
        },
        {   
          rw tower_base_equation,
          intros h3,
          exact le_reflexive M m hm , 
        }
      end, 
    have step: ∀(y:M),  y ∈ Zsixpointfour M m →(∃ u, u ∈ 𝕊 y) → 𝕊 y ∈ Zsixpointfour M m:=
      begin
        intros y h2 h,
        rw Zsixpointfour_members at h2,
        rw Zsixpointfour_members,
        cases h2 with h3 h4, 
        split,
        {
          exact successorF M y h3 h, 
        },
        { 
          intros h8,
          have h9:= cardinalsinhabited M (𝕀 M m (𝕊 y)) h8, 
          rw tower_recursion_equation M m y h3 h, 
          rw tower_recursion_equation M m y h3 h at h8,
          rw tower_recursion_equation M m y h3 h at h9, 
          have h10:= h9,
          cases h10 with x h12,
          rw exp_members M at h12, 
          cases h12 with a h13,
          cases h13 with h14 h15, 
          have h30:= IinF M m hm y h3 ⟨ USC a, h14⟩, 
          have h6 := mlessthanexpm M (𝕀 M m y) h30 h9, 
          rw  lessthan_definition at h6, 
          cases h6 with h20 h21,
          have h22: m ≤ 𝕀 M m y:= h4 h30, 
          have h23:= le_transitive M m  (exp M (𝕀 M m y)) (𝕀 M m y) hm  h8 h30 h22 h20, 
          exact h23,
        }
      end, 
    intros y hy,  
    rw F_members at hy, 
    specialize hy ( Zsixpointfour M m),
    have h3:= hy (and.intro base  step), 
    rw ( Zsixpointfour_members M m) at h3, 
    cases h3 with h5 h6, 
    exact h6, 
  end

lemma Iorder: ∀(y:M), y ∈ 𝔽 → ∀ (x m:M), x ∈ 𝔽 → m ∈ 𝔽 → 𝕀 M m y ∈ 𝔽 → x < y →  𝕀 M m x < 𝕀 M m y :=
  begin
    have base: zero ∈ Z_Iorder M:=
      begin
        rw Z_Iorder_members M,
        split,
        {
          exact zeroF M,
        },
        {
          intros x m hx hm h3 h4,
          have h5:= xnotlessthanzero M x hx, 
          contradiction,
        }
      end,
    have step: ∀(y:M), y ∈ Z_Iorder M → (∃(u:M), u ∈ 𝕊 y) → 𝕊 y ∈ Z_Iorder M:=
      begin
        intros y h h2, 
        rw Z_Iorder_members M at h,
        rw Z_Iorder_members M,
        cases h with h3 h4,
        split,
        {
          exact successorF M y h3 h2, 
        },
        {
          intros x m hx hm h5 h6, 
          have h7:= tower_recursion_equation M m y h3 h2,
          have h9:= cardinalsinhabited M (𝕀 M m (𝕊 y)) h5, 
          have h8:= mlessthanexpm M (𝕀 M m y), 
          cases h9 with u h10,
          rw h7 at h10, 
          rw exp_members at h10, 
          cases h10 with a h11, 
          cases h11 with h12 h13, 
          have h14:= towerF M m hm y h3 ⟨ USC a, h12⟩,
          have h15:= cardinalsinhabited M (𝕀 M m (𝕊 y)) h5,
          simp_rw h7 at h15, 
          have h18:= mlessthanexpm M (𝕀 M m y) h14 h15, 
          have h19:= FregeNdecidable M, 
          rw decidable_members M at h19,
          have h20:= h19 x zero ⟨ hx, (zeroF M)⟩,
          cases h20 with h21 h22,
          {  -- Case 1, x = zero
            rw h21 at *,
            rw tower_base_equation M,
            have h22:= tower_recursion_equation M m y h3 h2, 
            rw h22, 
            have h23:= mleImy M m hm y h3 h14, 
            have h24: exp M (𝕀 M m y) ∈ 𝔽 := finiteexp M (𝕀 M m y) h14 h15, 
            have h25:= le_transitive3 M m (𝕀 M m y) (exp M (𝕀 M m y)) hm h14 h24 h23 h18, 
            exact h25,
          },
          {  -- Case 2, x ≠ zero
            have h23:= nonzeroissuccessor M x hx h22, 
            cases h23 with r h24,
            cases h24 with h25 h26, 
            rw h26 at *,
            have h6copy := h6,
            rw lessthan_definition at h6,
            cases h6 with h27 h28,
            rw le_definition at h27,
            cases h27 with a h28,
            cases h28 with b h29, 
            rcases h29 with ⟨ h30, h31, h32, h33⟩, 
            have h34:= strictordersuccessor M r y h25 h3 ⟨ a, h30⟩ h2, 
            have h35:= h34.mpr h6copy, 
            have h36:= h4 r m h25 hm h14 h35, 
            have h37:= tower_recursion_equation M m y h3 h2, 
            have h38: exists u, u ∈ 𝕀 M m r:=
              begin
                rw lessthan_definition at h36, 
                cases h36 with h37 h38,
                rw le_definition at h37,
                cases h37 with a h38,
                cases h38 with b h39,
                rcases h39 with ⟨ h40,h41,h42,h43⟩, 
                use a, 
                exact h40, 
              end, 
            have h39:= towerF M m hm r h25 h38, 
            have h40:= exporderstrict M (𝕀 M m r) (𝕀 M m y) h39 h14 h36 h15, 
            cases h40 with h41 h42, 
            rw h7,
            have h43:= tower_recursion_equation M m r h25 ⟨ a, h30⟩,
            rw h43, 
            exact h42,  
          }
        }
      end, 
    intros  y h,  
    rw F_members at h, 
    specialize h ( Z_Iorder M ),
    have h3:= h (and.intro base  step), 
    rw ( Z_Iorder_members M ) at h3, 
    cases h3 with h5 h6, 
    exact h6, 
  end 

lemma Iorderle: ∀(y:M), y ∈ 𝔽 → ∀ (x m:M), x ∈ 𝔽 → m ∈ 𝔽 → 𝕀 M m y ∈ 𝔽 → x ≤  y →  𝕀 M m x ≤  𝕀 M m y :=
  begin
    intros y hy x m hx hm h3 h4,
    rw letolessthan M x y hx hy at h4,
    cases h4 with h5 h6,
    {
      have h7:= Iorder M y hy x m hx hm h3 h5,
      rw lessthan_definition at h7,
      exact h7.1,
    },
    {
      rw h6 at *,
      exact le_reflexive M  (𝕀 M m y) h3,
    }
  end

lemma Ioneone: ∀ (m x y:M), m ∈ 𝔽 → x ∈ 𝔽 → y ∈ 𝔽 → 𝕀 M m x ∈ 𝔽 → 𝕀 M m x = 𝕀 M m y → x = y:=
  assume m x y,
  begin
    intros hm hx hy h2 h3,
    have h4:= Theorem2 M x y hx hy,
    cases h4 with h5 h6,
    have h9:= cardinalsinhabited M (𝕀 M m x) h2, 
    cases h5 with h7 h8,
    { 
      have h2copy:= h2,
      rw h3 at h2, 
      have h10:= Iorder  M y hy x m hx hm h2 h7,  
      have h11:= Theorem2 M (𝕀 M m x) (𝕀 M m y) h2copy h2, 
      cases h11 with h12 h13,
      rw h3 at *, 
      simp at h13,
      contradiction, 
    },
    {
      cases h8 with h10 h11,
      {
        exact h10,
      },
      {
        have h2copy:= h2,
        rw h3 at h2, 
        have h10:= Iorder  M x hx y m hy hm h2copy h11,  
        have h11:= Theorem2 M (𝕀 M m y) (𝕀 M m x) h2 h2copy, 
        cases h11 with h12 h13,
        rw h3 at *,
        simp at h13,
        contradiction,  
      }
    }
  end

 #axioms_all  --This file is clean 