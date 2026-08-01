 -- Theory of multiplication
import inf9
variables (M:Type) [Model M] (a b x y z u v w X R W κ μ ℓ : M)
-- using ℓ where the source text has λ because you can't use λ for a variable.

open Model 

lemma successorSF: ∀ (x:M), x ∈ SF M → 𝕊 x ∈ SF M:=
  begin
    intros x h,
    rw SF_members at h,
    rw SF_members,
    intros w h2 h3,
    have h4:= h w h2 h3,
    exact h3 x h4, 
  end 

lemma FsubsetSF: 𝔽 ⊆ SF M:=
  begin
    rw subset_definition,
    intro m,
    intro h,
    rw SF_members,
    intros w base h5,
    have step:  ∀ (u : M), u ∈ w → (∃ (v : M), v ∈ 𝕊 u) → 𝕊 u ∈ w:=
      begin
        intros u h30 h31,
        exact h5 u h30,
      end,
    rw F_members at h, 
    specialize h w, 
    have h3:= h (and.intro base  step), 
    exact h3, 
  end

lemma zeroSF: zero ∈ SF M:=
  begin
    have h:= member_subset M 𝔽 (SF M) zero (FsubsetSF M) (zeroF M),
    exact h,
  end

lemma zero_or_successor: ∀ (x:M), x ∈ SF M → x = zero ∨ ∃(u:M), u ∈ SF M ∧ 𝕊 u = x:=
  begin
    have base: zero ∈ Z_zero_or_successor M:=
      begin
        rw Z_zero_or_successor_members,
        split,
        {
          exact zeroSF M,
        },
        {
          left,
          exact refl zero,
        }
      end,
    have step: ∀ (x:M), x ∈ Z_zero_or_successor M → 𝕊 x ∈ Z_zero_or_successor M:=
      assume x,
      begin
        intro h,
        rw Z_zero_or_successor_members,
        rw Z_zero_or_successor_members at h,
        cases h with h3 h4,
        split,
        {
          exact successorSF M x h3,
        },
        {
          right,
          cases h4 with h5 h6,
          {
            rw h5 at *,
            use zero,
            exact ⟨ h3, refl (𝕊 zero)⟩,
          },
          {   
            use x,
            exact ⟨ h3, refl (𝕊 x)⟩,
          }
        }
      end,
    intros x h,
    rw SF_members at h,   
    specialize h (Z_zero_or_successor M), 
    have h3:= h   base  step, 
    rw Z_zero_or_successor_members at h3,
    cases h3 with h4 h5,
    exact h5,
  end 

lemma additionSF: ∀(y:M), y ∈ (SF M) → ∀ (x:M), x∈ (SF M) → x+y ∈ (SF M):=
  begin
    have base: zero ∈ Z_additionSF M:=
      begin
        rw Z_additionSF_members,
        split,
        {
          exact zeroSF M, 
        },
        {
          intros  x h,
          rw right_identityNF,
          exact h,
        }
      end,
    have step: ∀(y:M), y ∈ Z_additionSF M → 𝕊 y ∈ Z_additionSF M:=
      begin
        intros y h,
        rw Z_additionSF_members at h,
        rw Z_additionSF_members,
        cases h with h2 h3,
        split,
        {
          exact (successorSF M y h2), 
        },
        {
          intros x h,
          have h4:= h3 x h,
          rw addition_equation,
          exact successorSF M (x+y) h4, 
        }
      end,
    intros y h,
    rw SF_members at h,   
    specialize h (Z_additionSF M), 
    have h3:= h   base  step, 
    rw Z_additionSF_members at h3,
    cases h3 with h4 h5,
    exact h5,
  end

lemma multiplication2a: ∀ (u:M), u ∈ SF M → triple u zero zero ∈ multiplication_graph M ∧ triple zero u zero ∈ multiplication_graph M:=
  assume u,
  begin
    intro hu,
    repeat{ rw multiplication_graph_members},
    split,
    { use u, use zero, use zero,
      split,
      {
        exact refl (triple u zero zero), 
      },
      {
        intros w h h2,
        have h3:= h u hu,
        exact h3.left,
      }
    },
    {
      use zero, use u, use zero,
      split,
      {
        exact refl (triple zero u zero),
      },
      {
        intros w h h2,
        have h3:= h u hu,
        exact h3.right, 
      }
    }
  end

lemma multiplication2b: 
∀ (x y z:M), triple x y z ∈ multiplication_graph M → triple x (𝕊 y) (z+ x) ∈ multiplication_graph M:=
  assume x y z,
  begin
    intro h,
    rw multiplication_graph_members at h,
    rw multiplication_graph_members,
    cases h with p h2,
    cases h2 with q h3,
    cases h3 with r h4,
    cases h4 with h5 h16,
    use x,
    use (𝕊 y),
    use z+ x,
    rw triple_equality at h5,
    rcases h5 with ⟨ h6, h7, h8⟩, 
    rw← h6 at *,
    rw← h7 at *,
    rw← h8 at *,
    split,
    { 
       exact refl (triple x (𝕊 y)(z+  x)), 
    },
    { 
      intros w h20 h21,
      have h22:= h21 x y z, 
      apply h22,
      have h23:= h16 w h20 h21,
      exact h23, 
    }  
  end 

lemma multiplicationSF: ∀ (x y z:M), triple x y z ∈ multiplication_graph M → x ∈ 
SF M ∧ y ∈ SF M ∧ z ∈ SF M:=
  assume x y z,
  begin
    rw multiplication_graph_members,
    intro h,
    cases h with p h2,
    cases h2 with q h3,
    cases h3 with r h4,
    cases h4 with h5 h6,
    rw triple_equality at h5,
    rcases h5 with ⟨ h7, h8, h9⟩,
    rw← h7 at *,
    rw← h8 at *,
    rw← h9 at *,
    specialize h6 (W_multiplicationSF M),
    have base: (∀ (u : M), u ∈ SF M → triple u zero zero ∈ W_multiplicationSF M ∧ triple zero u zero ∈ W_multiplicationSF M):=
      assume u,
      begin
        intro hu,
        rw W_multiplicationSF_members,
        rw W_multiplicationSF_members,
        split,
        {
          use u, use zero, use zero,
          simp,
          split,
          {
            exact hu,
          },
          { 
            have h10:= FsubsetSF M,
            have h11:= member_subset M 𝔽 (SF M) zero h10 (zeroF M), 
            exact h11, 
          }
        },
        {
          use zero, use u, use zero,
          simp,
          rw and_comm, 
          rw and_assoc,
          simp,
          split,
          {
            exact hu,
          },
          {
            have h10:= FsubsetSF M,
            have h11:= member_subset M 𝔽 (SF M) zero h10 (zeroF M), 
            exact h11, 
          }
        }
      end,
    have step:∀ (u v t : M), triple u v t ∈ W_multiplicationSF M → triple u (𝕊 v) (t +  u) ∈ W_multiplicationSF M:=
      assume u v t,
      begin
        intros h10,
        rw W_multiplicationSF_members at h10,
        rw W_multiplicationSF_members,
        cases h10 with p h11,
        cases h11 with q h12,
        cases h12 with r h13,
        cases h13 with h14 h15,
        rw triple_equality at h14,
        rcases h14 with ⟨ h16, h17, h18⟩, 
        rw← h16 at *,
        rw← h17 at *,
        rw← h18 at *,
        rcases h15 with ⟨h19, h20, h21⟩, 
        use u, use (𝕊 v), use (t+ u),
        simp,
        split,
        {
          exact h19,
        },
        {
          split,
          {
            have h22:= successorSF M v h20,
            exact h22, 
          },
          {  
            have h22:= additionSF M  u  h19 t h21, 
            exact h22, 
          }
        }
      end,
    have h7:= h6 base step , 
    rw W_multiplicationSF_members at h7,
    cases h7 with a h8,
    cases h8 with b h9, 
    cases h9 with c h10,
    cases h10 with h11 h12,
    rw triple_equality at h11,
    rcases h11 with⟨ h13, h14, h15⟩, 
    rw h13 at *,
    rw h14 at *,
    rw h15 at *,
    exact h12, 
  end

lemma addstozero: ∀ (y:M), y ∈ SF M → ∀(x:M), x ∈ SF M → x + y = zero → x = zero ∧ y = zero :=
  begin
    have base: zero ∈ Z_addstozero M:=
      begin
        rw Z_addstozero_members,
        split,
        {
          exact zeroSF M,
        },
        {
          intros x h h2,
          rw right_identityNF at h2,
          exact ⟨ h2, refl zero⟩,
        }
      end,
    have step: ∀(y:M), y ∈ Z_addstozero M → 𝕊 y ∈ Z_addstozero M:=
      assume y,
      begin
        intro h,
        rw Z_addstozero_members,
        rw Z_addstozero_members at h,
        cases h with h2 h3,
        split,
        {
          exact successorSF M y h2, 
        },
        {
          intros x h h4,
          rw addition_equation at h4,
          have h5:= Fregesuccessoromits0 M (x+y),
          contradiction,
        }
      end,
    intros y h,
    rw SF_members at h,
    specialize h (Z_addstozero M),
    have h3:= h base step,
    rw Z_addstozero_members at h3,
    exact h3.right,
  end
  
lemma multiplication3helper: ∀ (y z:M), triple zero y z ∈ multiplication_graph M → z = zero:=
  assume y z,
  begin
    intro h,
    rw multiplication_graph_members at h,
    cases h with p h2,
    cases h2 with q h3,
    cases h3 with r h4,
    cases h4 with h5 h6,
    rw triple_equality at h5,
    rcases h5 with ⟨ h7, h8, h9⟩, 
    rw← h7 at *,
    rw← h8 at *,
    rw← h9 at *,
    specialize h6 (W_multiplication3helper M),
    have base: ∀ (u : M), u ∈ SF M → triple u zero zero ∈ W_multiplication3helper M ∧ triple zero u zero ∈ W_multiplication3helper M:=
      assume u,
      begin
        intro h7,
        rw W_multiplication3helper_members,
        rw W_multiplication3helper_members,
        split,
        {
          split,
          {
            have h8:= multiplication2a M u h7,
            exact h8.left,
          },
          {
            have h8:= multiplication2a M u h7,
            intros y z h9,
            rw triple_equality at h9,
            symmetry,
            exact h9.right.right, 
          }
        },
        {
          split,
          {
            have h8:=  multiplication2a M u h7,
            exact h8.right,
          },
          {
            have h8:= multiplication2a M u h7,
            intros y z h9,
            rw triple_equality at h9,
            symmetry,
            exact h9.right.right, 
          }
        }
      end,
    have step: ∀ (x y z:M), triple x y z ∈ W_multiplication3helper M → triple x (𝕊 y) (z + x) ∈ W_multiplication3helper M:=
      assume x y z,
      begin
        repeat{rw W_multiplication3helper_members},
        intro h10,
        cases h10 with h11 h12,
        split,
        {
          have h11:= multiplication2b M x y z h11,
          exact h11,
        },
        {
          intros p q  h13,
          rw triple_equality at h13,
          rcases h13 with ⟨ h14, h15, h16⟩,
          rw h14 at *,
          rw← h15 at *,
          rw← h16 at *,
          rw right_identityNF at *,
          have h17:= h12 y z (refl (triple zero y z)),
          exact h17,
        }
      end,
    have h7:= h6 base step,
    rw W_multiplication3helper_members at h7,
    cases h7 with h8 h9,
    have h10:= h9 y z (refl (triple zero y z)),
    exact h10,
  end
    
lemma multiplication3: ∀ (x y z), triple x y z ∈ multiplication_graph M →
(z = zero → x = zero ∨ y = zero) ∧
(¬ z = zero → ∃ (p q r:M), x = 𝕊 p ∧ y = 𝕊 q ∧ z = 𝕊 (r+p) ∧ triple x q r ∈ multiplication_graph M):=
  assume x y z,
  begin 
    intro h, 
    set w:= W_multiplication3 M with hw,
    have h4459: ∀ (y:M), y ∈ SF M →  triple y zero zero ∈ w ∧  triple zero y  zero ∈ w:=
      assume y, 
      begin 
        intro hy, 
        rw and_comm, 
        rw hw, 
        rw W_multiplication3_members, 
        repeat{ split}, 
        {
          rw multiplication_graph_members,
          use zero, use y, use zero,
          split,
          {
            exact refl (triple zero y zero),
          },
          {
            intro Q,
            intros h5 h6,
            have h7:= h5 y hy,
            exact h7.right, 
          }
        },
        { 
          simp,
        },
        {
          intro h3,
          contradiction,  
        },
        { 
          rw W_multiplication3_members,
          repeat{split},
          {
            rw multiplication_graph_members,
            use y, use zero, use zero,
            split,
            {
              exact refl (triple y zero zero),
            },
            { 
              intro Q,
              intros h5 h6,
              have h7:= h5 y hy,
              exact h7.left, 
            }
          },
          {
            simp,
          },
          { 
            intros h4,
            contradiction, 
          }
        }
      end,
    have h4464:∀(u v t:M), triple u v t ∈ w → triple u (𝕊 v) (t + u) ∈ w:=
      begin
        intros u v t h3,
        have h3copy:= h3, 
        rw hw at h3,
        rw W_multiplication3_members at h3,
        cases h3 with h4 h5,
        have h6:= multiplication2b M u v t h4,
        have h4678: t+u = zero → u = zero ∨ 𝕊 v = zero:=
          begin
            intro h7,
            left,
            have h8:= multiplicationSF M u v t h4,
            rcases h8 with ⟨ h9, h10, h11⟩, 
            have h9:= addstozero M u h9 t h11 h7, 
            exact h9.right,
          end,
        have h7: triple u (𝕊 v) (t +  u) ∈ w:=
          begin
            rw hw,
            rw W_multiplication3_members,
            split,
            {
              exact h6,
            },
            {  
              use u, use (𝕊 v), use (t+ u),
              split,
              {
                exact refl (triple u (𝕊 v) (t + u)), 
              },
              {
                split,
                { 
                  exact h4678,
                },
                { 
                  intro h7,
                  have h20:= multiplicationSF M u v t h4,
                  rcases h20 with ⟨ h21, h22, h23⟩, 
                  have h24:= zero_or_successor M u h21,  
                  cases h24 with h25 h26,
                  {
                    rw h25 at *,
                    rw right_identityNF at h7,
                    have h27:= multiplication2a M v h22, 
                    cases h27 with h28 h29,
                    have h30:= multiplication3helper M v t h4,
                    rw h30 at *,
                    contradiction,
                  },
                  {
                    cases h26 with p h27,
                    cases h27 with h29 h30,
                    use p, use v, use t,
                    rw sym at h30,
                    rw←  addition_equation, 
                    rw h30,
                    simp,
                    rw← h30,
                    exact h4,   
                  }
                }
              }
            }
          end,
        exact h7, 
      end,
    have h2: multiplication_graph M ⊆ w:=
      begin 
        rw subset_definition,
        intros p h4,
        rw multiplication_graph_members at h4,
        cases h4 with a h5,
        cases h5 with b h6,
        cases h6 with c h7,
        cases h7 with h8 h9,
        rw h8 at *,
        have h10:= h9 w h4459 h4464, 
        exact h10, 
      end,
    have h3:= member_subset M (multiplication_graph M) w (triple x y z) h2 h,
    rw hw at h3,
    rw W_multiplication3_members  at h3,
    cases h3 with h4 h5,
    cases h5 with p h6,
    cases h6 with q h7, 
    cases h7 with r h8,
    cases h8 with h9 h10,
    rw triple_equality at h9,
    rcases h9 with ⟨ h11, h12, h13⟩, 
    rw← h11 at *,
    rw← h12 at *,
    rw← h13 at *,
    exact h10, 
  end
 
lemma deleteone: ∀ (x u c:M), x ∈ DC M → 𝕊 x  ∈ DC M → u ∈ 𝕊 x → c ∈ u → u - (single c) ∈ x:= 
  assume x u c,
  begin
    intros hxDC hsx hu hc,
    have h30:= hu, 
    rw successor_members at hu,
    cases hu with v h2,
    cases h2 with a h3,
    rcases h3 with ⟨ h4 , h5, h6⟩, 
    rw DC_members at hsx,
    have h7:= hsx u h30,
    cases h7 with h8 h9,
    rw decidable_members at h8,
    have h8copy:= h8,
    specialize h8 a c,
    have h10: a ∈ u:=
      begin
        rw full_extensionality at h6,
        specialize h6 a,
        have h7:= adjoin_member M a v,
        rw← h6 at h7,
        exact h7,
      end,
    have h11:= h8 ⟨ h10,hc⟩, 
    set f:= ((identityNF M u - ( single ‹ a,a› ) - (single ‹ c,c› )) ∪ (single ‹ a,c › ) ∪ (single ‹c,a› )) with h300,
    have h12: similarity M f (u - (single a)) (u - (single c)):=
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
              rw Rel_definition,
              intros t h13,
              rw h300 at h13,
              repeat{rw binary_union_axiom at h13}, 
              repeat{rw minus_members at h13}, 
              cases h13 with h14 h15,
              {
                cases h14 with h16 h17,
                {
                  cases h16 with h18 h19,
                  cases h18 with h20 h21,
                  rw identity_membersNF at h20,
                  cases h20 with p h21,
                  use p, use p,
                  exact h21.left,
                },
                {
                  rw singleton1 at h17,
                  use a, use c, 
                  exact h17, 
                }
              },
              {
                rw singleton1 at h15,
                use c, use a, 
                exact h15, 
              }
            },
            { 
              split,
              {
                intros p q h12,
                cases h12 with h13 h14,
                rw [minus_members,singleton1] at h13,
                cases h13 with h15 h16,
                rw [minus_members,singleton1],
                rw h300 at h14, 
                repeat{rw binary_union_axiom at h14}, 
                repeat{rw minus_members at h14}, 
                cases h14 with h17 h18, 
                { cases h17 with h19 h20,
                  {
                    cases h19 with h21 h22,
                    cases h21 with h23 h24,
                    rw identity_membersNF at h23,
                    cases h23 with r h25,
                    cases h25 with h26 h27,
                    rw ordered_pair_equality at h26,
                    cases h26 with h27 h28,
                    rw h27 at *,
                    rw h28 at *,
                    rw [singleton1, ordered_pair_equality] at h22,
                    simp at h22,
                    exact ⟨ h15, h22⟩, 
                  },
                  {
                    rw [singleton1, ordered_pair_equality] at h20,
                    cases h20 with h21 h22,
                    rw h21 at *,
                    rw h22 at *,
                    contradiction, 
                  }
                },
                { 
                  rw singleton1 at h18,
                  rw ordered_pair_equality at h18,
                  cases h18 with h19 h20,
                  rw h19 at *,
                  rw h20 at *,
                  rw sym at h16,
                  exact ⟨ h10, h16⟩, 
                }
              },
              { 
                split,
                {   -- prove f is single-valued 
                  intros x2 y z,
                  intro h20,
                  rcases h20 with ⟨ h21, h22, h23⟩, 
                  rw minus_members at h21,
                  rw singleton1 at h21,
                  cases h21 with h24 h25,
                  rw h300 at h22 h23,
                  repeat{ rw binary_union_axiom at h23 h22},
                  repeat{ rw minus_members at h23 h22}, 
                  repeat{ rw singleton1 at h23 h22},
                  repeat{ rw ordered_pair_equality at h23 h22},
                  repeat{ rw identity_membersNF at h23 h22},
                  cases h22 with h24 h45,
                  {
                    cases h24 with h26 h27,
                    {
                      cases h23 with h28 h29,
                      {
                        cases h28 with h30 h31,
                        {
                          cases h30 with h32 h33,
                          cases h32 with h34 h35,
                          cases h26 with h36 h37,
                          cases h36 with h38 h39,
                          cases h34 with p h40,
                          cases h38 with q h41,
                          cases h40 with h42 h43,
                          cases h41 with h44 h45,
                          rw ordered_pair_equality at h42 h44,
                          cases h44 with h47 h46,
                          cases h42 with h49 h48,
                          rw h46 at *, 
                          rw h47 at *,
                          rw h49 at *,
                          rw h48 at *,
                        },
                        {
                          cases h31 with h32 h33,
                          cases h26 with h36 h37,
                          cases h36 with h38 h39,
                          cases h38 with p h35,
                          cases h35 with h40 h41, 
                          rw ordered_pair_equality at h40,
                          cases h40 with h47 h46,
                          rw h32 at *, 
                          contradiction, 
                        }
                      },
                      {
                        cases h26 with h30 h31,
                        cases h30 with h32 h33,
                        cases h32 with p h34,
                        cases h34 with h35 h36,
                        rw ordered_pair_equality at h35,
                        cases h35 with h36 h37,
                        rw h36 at *,
                        rw h37 at *,
                        cases h29 with h38 h39,
                        rw h38 at *,
                        rw h39 at *,
                        simp at h31,
                        contradiction, 
                      }
                    },
                    {
                      cases h23 with h30 h31,
                      {
                        cases h30 with h32 h33,
                        {
                          cases h32 with h34 h35,
                          cases h34 with h36 h37,
                          cases h36 with p h38,
                          cases h38 with h39 h40,
                          rw ordered_pair_equality at h39,
                          cases h39 with h41 h42,
                          rw h41 at *,
                          rw h42 at *,
                          cases h27 with h43 h44,
                          contradiction, 
                        },
                        {
                          rw h27.right,
                          rw h33.right, 
                        }
                      },
                      {
                        rw h27.left at *,
                        rw h27.right at *,
                        rw h31.left at *,
                        rw h31.right at *,
                        symmetry,
                        exact h31.left, 
                      }
                    }
                  },
                  {
                    rw h45.left at *,
                    rw h45.right at *,
                    cases h23 with h30 h31,
                    {
                      cases h30 with h32 h33,
                      {
                        cases h32 with h33 h34,
                        cases h33 with h35 h36,
                        cases h35 with p h37,
                        cases h37 with h38 h39,
                        rw ordered_pair_equality at h38,
                        rw h38.left at *,
                        rw h38.right at *,
                        have h39:= h34 ⟨ refl p, refl p⟩,
                        contradiction,
                      },
                      {
                        cases h33 with h34 h35,
                        contradiction, 
                      }
                    },
                    {
                      symmetry, 
                      exact h31.right, 
                    }
                  }
                },
                { -- prove f maps (u - single a)  into (u - single c)
                  intros x h20,
                  rw minus_members at h20,
                  rw singleton1 at h20,
                  cases h20 with h21 h22,
                  have h23:= h8copy x c ⟨ h21, hc⟩,
                  cases h23 with h24 h25,
                  {
                    rw h24 at *,
                    use a,
                    split,
                    {
                      rw minus_members,
                      rw singleton1,
                      rw sym,
                      exact ⟨ h10, h22⟩, 
                    },
                    {
                      rw h300,
                      rw binary_union_axiom,
                      right,
                      rw singleton1,
                    }
                  },
                  {
                    use x,
                    rw minus_members,
                    rw singleton1,
                    split,
                    {
                      exact ⟨ h21, h25⟩,
                    },
                    {
                      rw h300,
                      repeat{rw binary_union_axiom},
                      repeat{rw minus_members},
                      repeat{rw singleton1},
                      left, left,
                      split,
                      {
                        split,
                        {
                          rw identity_membersNF,
                          use x,
                          exact ⟨ refl ‹ x,x›, h21⟩, 
                        },
                        {
                          rw ordered_pair_equality,
                          simp,
                          exact h22, 
                        }
                      },
                      {
                        rw ordered_pair_equality,
                        simp,
                        exact h25,
                      }
                    }
                  }
                }
              }
            }
          },
          { 
            split,
            {  -- prove f is one-to-one
              intros x w y h20,
              rcases h20 with ⟨ h21,h22,h23⟩,
              rw [minus_members, singleton1] at h23,
              cases h23 with h24 h25,
              have h26:= h8copy x c ⟨ h24, hc⟩, 
              cases h26 with h27 h28,
              {  --  the case x = c
                rw h27 at *,
                rw h300 at h22 h21,
                repeat{rw binary_union_axiom  at h22 h21},
                repeat{rw minus_members at h22 h21},
                repeat{rw singleton1 at h22 h21}, 
                cases h22 with h24 h25,
                {
                  cases h24 with h26 h27,
                  {
                    cases h26 with h28 h29,
                    cases h28 with h30 h31,
                    rw ordered_pair_equality at h29 h31,
                    rw identity_membersNF at h30,
                    cases h30 with p h31,
                    cases h31 with h32 h33,
                    rw ordered_pair_equality at h32,
                    cases h32 with h33 h34,
                    rw h33 at *,
                    rw h34 at *,
                    simp at h31,
                    simp at h29,
                    cases h21 with h35 h36, 
                    {
                      cases h35 with h37 h38,
                      {
                        cases h37 with h39 h40,
                        rw ordered_pair_equality at h40,
                        simp at h40,
                        cases h39 with h41 h42,
                        rw identity_membersNF at h41,
                        cases h41 with q h42,
                        rw ordered_pair_equality at h42,
                        cases h42 with h43 h44,
                        rw h43.left,
                        rw h43.right,
                      },
                      {
                        rw ordered_pair_equality at h38,
                        symmetry,
                        exact h38.right,
                      }
                    },
                    {
                      rw ordered_pair_equality at h36,
                      cases h36 with h37 h38,
                      contradiction, 
                    }
                  },
                  {
                    rw ordered_pair_equality at h27,
                    cases h27 with h28 h29,
                    rw h28 at *,
                    rw h29 at *,
                    cases h21 with h30 h31,
                    {
                      cases h30 with h32 h33,
                      {
                        cases h32 with h34 h35,
                        rw ordered_pair_equality at h35,
                        simp at h35,
                        contradiction,
                      },
                      {
                        rw ordered_pair_equality at h33,
                        exact h33.left,
                      }
                    },
                    {
                      rw ordered_pair_equality at h31,
                      exact h31.right,
                    }
                  }
                },
                {
                  rw ordered_pair_equality at h25,
                  symmetry,
                  exact h25.left, 
                }
              },
              {  -- the case x ≠ c 
                rw h300 at h22,
                repeat{rw binary_union_axiom at h22 h21},
                repeat{rw minus_members at h22 h21},
                repeat{rw singleton1 at h22 h21}, 
                cases h21 with h50 h51,
                {
                  cases h50 with h52 h53,
                  {
                    cases h52 with h54 h55,
                    cases h54 with h56 h57,
                    rw identity_membersNF at h56,
                    cases h56 with q h57,
                    rw ordered_pair_equality at h57,
                    cases h57 with h58 h59,
                    rw h58.left at *,
                    rw h58.right at *,
                    cases h22 with h60 h61,
                    {
                      cases h60 with h62 h63,
                      {
                        cases h62 with h64 h65,
                        cases h64 with h66 h67,
                        rw identity_membersNF at h66,
                        cases h66 with p h68,
                        cases h68 with h69 h70,
                        rw ordered_pair_equality at h69,
                        rw h69.left at *,
                        rw h69.right at *, 
                      },
                      {
                        rw ordered_pair_equality at h63,
                        rw h63.left at *,
                        rw h63.right at *,
                        rw ordered_pair_equality at h55,
                        simp at h55,
                        contradiction, 
                      }
                    },
                    { 
                      rw ordered_pair_equality at h61,
                      rw h61.left at *,
                      rw h61.right at *,
                      contradiction, 
                    },
                  },
                  {
                    rw ordered_pair_equality at h53,
                    rw h53.left at *,
                    rw h53.right at *,
                    contradiction, 
                  }
                },
                {
                  rw ordered_pair_equality at h51,
                  rw h51.left at *,
                  rw h51.right at *,
                  contradiction, 
                }
              }
            },
            {  --prove f inverse maps back correctly
              intros x y h12,
              cases h12 with h13 h14,
              rw [minus_members, singleton1] at h14,
              cases h14 with h15 h16,
              rw minus_members,
              rw singleton1, 
              rw h300 at h13,
              repeat{rw binary_union_axiom at h13},
              repeat{rw minus_members at h13},
              repeat{rw singleton1 at h13},
              cases h13 with h24 h25,
              {
                cases h24 with h28 h27,
                {
                  cases h28 with h29 h30,
                  cases h29 with h31 h32,
                  rw identity_membersNF at h31,
                  cases h31 with p h33,
                  cases h33 with h34 h35,
                  rw ordered_pair_equality at h34,
                  rw h34.left at *,
                  rw h34.right at *,
                  rw ordered_pair_equality at h32,
                  simp at h32,
                  exact ⟨ h35, h32⟩, 
                },
                {
                  rw ordered_pair_equality at h27,
                  cases h27 with h18 h19,
                  contradiction, 
                }
              },
              { 
                rw ordered_pair_equality at h25,
                rw h25.left at *,
                rw h25.right at *,
                cases h11 with h17 h18,
                {
                  rw h17 at *,
                  contradiction,
                },
                {
                  rw sym at h18,
                  exact ⟨ hc, h18⟩, 
                }
              }
            }
          }
        },
        {  -- prove f is onto
          unfold onto,
          intros y h12,
          rw minus_members at h12,
          rw singleton1 at h12,
          cases h12 with h14 h15, 
          have h13:= adjoin_member M a v, 
          rw← h6 at h13, 
          have h16:= h8copy y a ⟨ h14, h13⟩, 
          cases h16 with h17 h18,
          {
            rw h17 at *,
            use c,
            split,
            {
              rw minus_members,
              rw singleton1,
              rw sym,
              exact ⟨ hc, h15⟩,
            },
            {
              rw h300,
              rw binary_union_axiom,
              right,
              rw singleton1,
            }
          },
          { 
            use y,
            split,
            {
              rw minus_members,
              rw singleton1,
              exact ⟨ h14, h18⟩,
            },
            {
              rw h300,
              rw binary_union_axiom,
              left,
              rw binary_union_axiom,
              left,
              rw minus_members,
              rw minus_members,
              split,
              {
                split,
                { 
                  rw identity_membersNF,
                  use y,
                  simp,
                  exact h14,
                },
                {
                  rw singleton1,
                  rw ordered_pair_equality,
                  intro h19,
                  simp at h19,
                  contradiction,
                }
              },
              {
                rw singleton1,
                rw ordered_pair_equality,
                simp,
                exact h15, 
              }
            }
          }
        }
      end,
    have h13: v = u - (single a):=
      begin
        rw full_extensionality,
        intro t,
        rw h6,
        rw minus_members,
        rw binary_union_axiom,
        split,
        {
          intro h14, 
          have h15:= adjoin_member2 M t a v h14,
          rw← h6 at h15, 
          have h16:= adjoin_member M a v, 
          rw← h6 at h16, 
          have h17:= h8copy t a ⟨ h15, h16⟩, 
          cases h17 with h18 h19,
          {
            rw h18 at *,
            contradiction,
          },
          {
            split,
            {
              left,
              exact h14,
            },
            {
              rw singleton1,
              exact h19, 
            }
          }
        },
        {
          intro h13,
          cases h13 with h14 h15,
          cases h14 with h16 h17,
          {
            exact h16,
          },
          {
            contradiction, 
          }
        }
      end,
    have h14: similar M v (u - (single c)):=
      begin
        rw← h13 at h12,
        unfold similar,
        use f,
        exact h12, 
      end,
    rw DC_members at hxDC,
    specialize hxDC (u - (single a)),
    rw← h13 at hxDC,
    have h15:= hxDC h4, 
    cases h15 with h16 h17,
    have h18:= (h17 (u - (single c))).mpr,
    rw similar_symmetric at h14, 
    exact h18 h14, 
  end

lemma inhabitedSF: ∀ (m:M), m ∈ SF M → (∃ (u:M), u ∈ m)→ m ∈ 𝔽 :=
  begin
    have base: zero ∈ Z_inhabitedSF M:=
      begin
        rw Z_inhabitedSF_members,
        split,
        {
          exact zeroSF M,
        },
        {
          intros h,
          cases h with u h2,
          exact zeroF M,
        }
      end,
    have step: ∀ (m:M), m ∈ Z_inhabitedSF M → 𝕊 m ∈ Z_inhabitedSF M:=
      assume m,
      begin 
        repeat{rw Z_inhabitedSF_members},
        intro h,
        cases h with h2 h3,
        split,
        {
           exact successorSF M m h2, 
        },
        {
          intros h4,
          cases h4 with u h5,
          have h5copy:= h5,
          rw successor_members at h5,
          cases h5 with x h6,
          cases h6 with c h7,
          rcases h7 with ⟨ h8, h9, h10⟩, 
          have h11 := h3 ⟨ x, h8⟩, 
          exact successorF M m h11 ⟨ u, h5copy⟩, 
        }
      end,
    intros m h,
    rw SF_members at h,
    specialize h (Z_inhabitedSF M),
    have h4:= h base step,
    rw Z_inhabitedSF_members at h4,
    exact h4.right,
  end 
 
 lemma successorSFF: ∀(x:M), x ∈ SF M →   𝕊 x ∈ 𝔽  →  x ∈ 𝔽:=
   assume x,
   begin
     intros h h2,
     have h3:= cardinalsinhabited M (𝕊 x) h2,
     cases h3 with u h4,
     rw successor_members at h4,
     cases h4 with p h5,
     cases h5 with c h6,
     rcases h6 with ⟨ h7, h8, h9⟩,
     have h10:= inhabitedSF M x h ⟨ p, h7 ⟩, 
     exact h10,
   end

lemma multiplication4: ∀(y:M), y ∈ 𝔽 → ∀ (x z t:M), triple x y z ∈ multiplication_graph M →
triple x y t ∈ multiplication_graph M → z = t:=
  begin
    have base: zero ∈ Z_multiplication4 M:=
      begin
        rw Z_multiplication4_members, 
        split,
        {
          exact zeroF M,
        },
        {
          intros x z t hz ht,
          have h1:= multiplicationSF M x zero z hz, 
          rcases h1 with ⟨ h2, h3, h4⟩,
          have h5:= zero_or_successor M z h4, 
          have h7: z = zero:=
            begin
              cases h5 with h8 h9, 
              { 
                exact h8,
              },
              { 
                cases h9 with p h20,
                cases h20 with h31 h10,
                have h11:= multiplication3 M x zero z hz,
                cases h11 with h12 h13,
                have h14:= Fregesuccessoromits0 M p,
                rw h10 at h14,
                have h15:= h13 h14, 
                cases h15 with r h16,
                cases h16 with b h17,
                cases h17 with c h18,
                rcases h18 with ⟨ h19, h20, h21, h22⟩, 
                have h23:= Fregesuccessoromits0 M b,
                rw sym at h20,
                contradiction,
              }
            end,
          have h20:= multiplicationSF M x zero t ht,
          rcases h20 with ⟨ h21, h22, h23⟩, 
          have h25:= zero_or_successor M t h23, 
          have h27: t = zero:=
            begin
              cases h25 with h28 h29,
              {
                exact h28,
              },
              { 
                cases h29 with p h10,
                have h11:= multiplication3 M x zero t ht,
                cases h11 with h12 h13,
                have h14:= Fregesuccessoromits0 M p,
                cases h10 with h15 h16,
                rw h16 at h14,
                have h15:= h13 h14, 
                cases h15 with r h16,
                cases h16 with b h17,
                cases h17 with c h18,
                rcases h18 with ⟨ h19, h20, h21, h22⟩, 
                have h23:= Fregesuccessoromits0 M b,
                rw sym at h20,
                contradiction, 
              }
            end,
          have h28: z=t:= 
            begin
              rw← h27 at h7,
              exact h7, 
            end,
          exact h28,
        }
      end, 
    have step: ∀ (y:M), y ∈ Z_multiplication4 M → (∃ (u:M), u ∈ 𝕊 y) → (𝕊 y ∈ Z_multiplication4 M):=
      assume y,
      begin
        intros h h4,
        rw Z_multiplication4_members at h,
        rw Z_multiplication4_members, 
        cases h with h2 h3,
        split,
        {
         exact successorF M y h2 h4, 
        },
        {
          intros x z t,
          intros hz ht,
          have h6:= multiplication3 M x (𝕊 y) z hz,
          have h30:= multiplicationSF M x (𝕊 y) t ht,
          rcases h30 with ⟨ h31, h32, h33⟩, 
          have h16:= multiplication3 M x (𝕊 y) t ht, 
          have h26:= multiplicationSF M x (𝕊 y) z hz,
          rcases h26 with ⟨ h27, h28, h29⟩,
          have h7:= zero_or_successor M z h29, 
          have h17:= zero_or_successor M t h33, 
          cases h7 with h8 h9,
          { 
            rw h8 at *,
            cases h17 with h18 h19,
            {  -- z = t = 0
              rw h18 at *, 
            },
            {  --z = 0 and t ≠ 0  
              have h30:= multiplication3 M x (𝕊 y) zero hz,
              cases h30 with h31 h32,
              have h33:= h31 (refl zero),
              have h34: x = zero:=
                begin
                  cases h33 with h34 h35,
                  {
                    exact h34,
                  },
                  {
                    have h36:= Fregesuccessoromits0 M y,
                    contradiction, 
                  }
                end,
              have h35: ¬ x = zero:=
                begin
                  have h36:= multiplication3 M x (𝕊 y) t ht,
                  cases h19 with u h37,
                  have h38:=Fregesuccessoromits0 M u, 
                  rw h37.right at h38,
                  have h39:= h16.right h38, 
                  cases h39 with p h40,
                  cases h40 with q h41,
                  cases h41 with r h42,
                  cases h42 with h43 h44,
                  have h45:= Fregesuccessoromits0 M p,
                  rw←  h43 at h45,
                  exact h45, 
                end,
              contradiction, 
            }
          },
          { 
            cases h17 with h18 h19,
            {  --t = 0  and z ≠ 0
              rw h18 at *,
              cases h9 with u h10,
              have h11:= Fregesuccessoromits0 M u,
              rw h10.right at h11,  
              have h30:= multiplication3 M x (𝕊 y) z hz, 
              have h31:= h30.right h11, 
              cases h31 with p h32,
              cases h32 with q h33,
              cases h33 with r h34,
              cases h34 with h35 h36,
              have h37:= Fregesuccessoromits0 M p,
              rw← h35 at h37,   --  x ≠ 0
              have h38:= multiplication3 M x (𝕊 y) zero ht, 
              cases h38 with h39 h40,
              have h41:= h39 (refl zero),
              have h42: x = zero:=
                begin
                  cases h41 with h43 h44,
                  {
                    exact h43,
                  },
                  {
                    have h45:= Fregesuccessoromits0 M y,
                    contradiction,
                  }
                end,
              contradiction,    
            },
            {  --z ≠  0 and t ≠ 0  
              cases h9 with u h10,
              cases h19 with v h20,
              have h11:= Fregesuccessoromits0 M u,
              have h21:= Fregesuccessoromits0 M v,
              rw h10.right  at h11,
              rw h20.right  at h21,
              have h12:= multiplication3 M x (𝕊 y) z hz,
              have h22:= multiplication3 M x (𝕊 y) t ht,
              have h13:= h12.right h11,
              have h23:= h22.right h21,
              cases h13 with p h14,
              cases h14 with q h15,
              cases h15 with r h16,
              rcases h16 with ⟨  h17, h18, h19, h30⟩, 
              cases h23 with a h24,
              cases h24 with b h25,
              cases h25 with c h26,
              rcases h26 with ⟨ h27, h28, h29, h39⟩, 
              rw h18 at h28,
              have h129:= successorF M y h2 h4,
              have h40:= multiplicationSF M x b c h39,
              have  h50: 𝕊 q ∈ 𝔽:=
                begin
                  rw h18 at h129, 
                  exact h129,
                end,
              have h51:= multiplicationSF M x q r h30,
              rcases h51 with ⟨ h52, h53, h54⟩,
              have h51:= successorSFF M q h53 h50,
              have h52:= cardinalsinhabited M (𝕊 q) h50,
              have h153:= cardinalsinhabited M (𝕊 y) h129,
              rcases h40 with ⟨ h154, h55, h56⟩, 
              have h57: 𝕊 b ∈ 𝔽 :=
                begin
                  rw h28 at h50,
                  exact h50,
                end,
              have h58:= successorSFF M b h55 h57, 
              have h59:= cardinalsinhabited M (𝕊 b) h57, 
              have h43:= successoroneone M y q h2 h51 h153 h52, 
              have h18copy:= h18, 
              rw←  h43 at h18, 
              have h44:= successoroneone M y b h2 h58 h153 h59,
              rw← h18copy at h28,
              rw← h28 at h44,
              simp at h44, 
              rw← h18 at *,
              rw← h44 at *, 
              have h49:= h3 x r c h30 h39, 
              rw h19,
              rw←  addition_equation,
              rw h49 at *,
              rw h29,
              rw← addition_equation,
              rw← h17,
              rw← h27, 
            }
          }
        }
      end,
    intros y h,
    rw F_members at h, 
    specialize h ( Z_multiplication4 M),
    have h3:= h (and.intro base  step), 
    rw ( Z_multiplication4_members M) at h3, 
    cases h3 with h5 h6, 
    exact h6, 
  end


lemma zero_mulNF: ∀ (x:M), x ∈ 𝔽  → zero * x = zero:=
  begin
    intros x h,
    rw full_extensionality,
    intro t,
    have h2 := multiplication_members2 M  zero x t,
    rw h2,
    split,
    {
      intro h3,
      cases h3 with z h4,
      cases h4 with h5 h6,
      have h7:= multiplication3 M zero x z h5, 
      cases h7 with h8 h9,
      have h10:= multiplicationSF M zero x z h5,
      rcases h10 with ⟨ h11,h12,h13⟩,
      have h14:= zero_or_successor M z h13,
      cases h14 with h15 h16,
      {
        rw h15 at h6,
        exact h6,
      },
      {
        cases h16 with u h17,
        cases h17 with h18 h19,
        have h20:= Fregesuccessoromits0 M u,
        rw h19 at h20,
        have h21:= h9 h20,
        have h22:= multiplication2a M x h12,
        have h23:= multiplication4 M x h zero z zero h5 h22.right,
        rw h23 at *,
        exact h6, 
      },
    },
    {
      intro h3,
      use zero,
      rw and_comm,
      split,
      {
        exact h3,
      },
      {
        have h10:= member_subset M 𝔽 (SF M) x (FsubsetSF M) h,
        have h4:= multiplication2a M x h10,
        cases h4 with h5 h6,
        exact h6,
      }
    }
  end


lemma multhelper: ∀ (x y:M), x ∈ SF M   → y ∈ 𝔽 → (𝕊 y ∈ 𝔽 ) → x * y ∈ SF M → 
(∀(z:M), (z ∈ SF M → (triple x y z ∈ multiplication_graph M ↔ z = x*y))) → x*(𝕊 y) = (x*y) + x:=
  assume x  y,
  begin
    intros hx  hy hsy hdot h3,
    rw full_extensionality,
    intro u,
    rw multiplication_members2,
    split,
    {
      intros h4,
      cases h4 with z h5,
      cases h5 with h6 h7,
      have h8:= multiplication3 M x (𝕊 y) z h6, 
      cases h8 with h9 h10,
      have h11:= multiplicationSF M x (𝕊 y) z h6,
      rcases h11 with ⟨ h12, h13, h14⟩, 
      have h15:= zero_or_successor M z h14,
      cases h15 with h16 h17,
      {
        have h18:= h9 h16,
        cases h18 with h19 h20,
        {
          rw h19 at *,
          rw right_identityNF,
          rw zero_mulNF M y hy,
          rw h16 at *, 
          exact h7,
        },
        {
          have h21:= Fregesuccessoromits0 M y,
          contradiction,
        }
      },
      {
        cases h17 with b h18,
        cases h18 with h19 h20,
        have h21:= Fregesuccessoromits0 M b,
        rw h20 at h21,
        have h22:= h10 h21,
        cases h22 with c h23,
        cases h23 with q h24,
        cases h24 with p h25, 
        rcases h25 with ⟨ h26,h27, h28, h29⟩,
        have h30:= multiplicationSF M x q p h29,
        rcases h30 with ⟨ h31, h32, h33⟩,  
        have h34:= hsy,
        rw h27 at h34, 
        have h40:= successorSFF M q h32 h34, 
        have h41:= successoroneone M y q hy h40 (cardinalsinhabited M (𝕊 y) hsy) (cardinalsinhabited M (𝕊 q) h34),
        rw← h41 at h27,
        rw← h27 at *,
        have h50:= multiplicationSF M x y p h29,
        rcases h50 with ⟨ h50, h51, h52⟩,
        have h42:= (h3 p h52).mp h29,
        rw← h42,
        rw h26 at *,
        rw addition_equation,
        rw← h28,
        exact h7,
      }
    },
    {
      intro h4,
      use (x*y) + x,
      rw and_comm,
      split,
      {
        exact h4,
      },
      { 
        have h10:= h3 (x * y) hdot,
        simp at h10,
        have h5:= multiplication2b M x y (x*y) h10,
        exact h5, 
      }
    }  
  end

lemma mul_zeroNF: ∀ (x:M), x ∈ SF M → x * zero  = zero:=
  begin
    intros x hx,
    rw full_extensionality,
    intro t,
    split,
    {
      intro h3,
      rw multiplication_members2 at h3,
      cases h3 with z h4,
      cases h4 with h5 h6,
      have h7:= zero_or_successor M x hx,
      cases h7 with h8 h9,
      {
        rw h8 at *,
        have h9:= multiplication3helper M zero z h5,
        rw h9 at *,
        exact h6,
      },
      {
        cases h9 with u h10,
        cases h10 with h11 h12,
        rw← h12 at *,
        have h13:= multiplication3 M (𝕊 u) zero z h5,
        cases h13 with h14 h15, 
        have h16:= multiplicationSF M (𝕊 u) zero z h5, 
        rcases h16 with ⟨ h17, h18, h19⟩,
        have h20:= zero_or_successor M z h19,
        cases h20 with h21 h22,
        {
          rw h21 at *, 
          exact h6,
        },
        {
          cases h22 with p h23,
          cases h23 with h24 h25,
          have h26:= Fregesuccessoromits0 M p,
          rw h25 at h26,
          have h27:= h15 h26,
          cases h27 with a h28,
          cases h28 with b h29,
          cases h29 with c h30,
          rcases h30 with ⟨ h31, h32, h33⟩,
          have h34:= Fregesuccessoromits0 M b,
          rw sym at h32,
          contradiction,
        }
      }
    },
    {
      intro ht,
      rw multiplication_members2,
      use zero,
      rw and_comm,
      split,
      {
        exact ht,
      },
      {
        have h4:= multiplication2a M x hx,
        exact h4.left, 
      }
    }
  end

lemma multhelper2: ∀ (x y:M), x  ∈ SF M → y ∈ 𝔽  → (𝕊 y ∈ 𝔽 )
→ x*y ∈ SF M → ( ∀ (z:M), z ∈ SF M → 
(triple x y z ∈ multiplication_graph M ↔ z = x * y ))→
(x*(𝕊 y) ∈ SF M ∧ ∀ (z:M), z ∈ SF M → (triple x (𝕊 y) z ∈ multiplication_graph M ↔ 
z = x * (𝕊 y))):=
  assume x y,
  begin
    intros hx hy hsy h3 hIH,
    have h2:= multhelper M x y hx hy hsy h3,  
    rw and_comm,
    have h100:∀ (z : M), z ∈ SF M → (triple x (𝕊 y) z ∈ multiplication_graph M ↔ z = x * 𝕊 y):=
    begin 
      intros z hz,
      split,
      { --left to right,
        intro h5, 
        have h4:= multiplication3 M x (𝕊 y) z h5, 
        cases h4 with h6 h7, 
        have h8:= zero_or_successor M z hz, 
        cases h8 with h9 h10,
        {
          rw h9 at *,
          have h11:= h6 (refl zero),
          cases h11 with h12 h13,
          { 
            rw h12 at *,
            have h14:= zero_mulNF M (𝕊 y) hsy,  
            symmetry,
            exact h14, 
          },
          {
            rw h13 at *,
            have h14: x * zero = zero :=  mul_zeroNF M x hx, 
            symmetry,
            exact h14, 
          }
        },
        { 
          cases h10 with u h11, 
          cases h11 with h12 h13,
          have h14:= Fregesuccessoromits0 M u,
          rw h13 at *,
          have h15:= h7 h14,
          cases h15 with r h16,
          cases h16 with q h17,
          cases h17 with p h18,
          rcases h18 with ⟨ h19, h20, h21, h22⟩, 
          rw← h19 at *,
          rw h20 at *, 
          have h23:= multiplicationSF M x q p h22,
          rcases h23 with ⟨ h24, h25, h26⟩, 
          have h30:= successorSFF M q h25 hsy, 
          have h27:= cardinalsinhabited M (𝕊 q) hsy, 
          have h28:= h27,
          rw← h20 at h28, 
          have h31:= successoroneone M y q hy h30 h28 h27,
          rw← h31 at h20,
          rw← h20 at *,
          have h33:= hIH p h26, 
          have h34:= h33.mp h22, 
          have h35: z = p+x:=
            begin
              rw h19,
              rw h21,
              rw addition_equation, 
            end, 
          rw h35,
          rw h34,
          symmetry,
          apply h2,
          intros t ht,
          have h36:= hIH t ht,
          exact h36,
        }
      },
      {
        intro h10,
        rw h10 at *,
        have h11:= h2 hIH,
        have h12:= multiplication2b M x y (x*y),
        have h13:= hIH (x*y) h3,
        simp at h13,
        have h14:= h12 h13,
        rw h11,
        exact h14, 
      }
    end, 
    split,
    { 
      exact h100,
    },
    {
      have h101:= hIH (x*y) h3,
      simp at h101,
      have h102:= multiplication2b M x y (x*y) h101, 
      have h103:= multiplicationSF M x (𝕊 y)(x*y+x) h102,
      rcases h103 with ⟨ h104, h105, h106⟩,
      have h107:= h2 hIH,
      rw h107,
      exact h106, 
    }
  end

lemma multiplication5: ∀ (y:M), y ∈ 𝔽 →  ∀ (x :M), x ∈ 𝔽 → 
x*y ∈ SF M ∧ ∀ (z:M), z ∈ SF M → (triple x y z ∈ multiplication_graph M ↔ z = x * y ) :=
  begin
    have base: zero ∈ Z_multiplication5 M:=
      begin
        rw Z_multiplication5_members,
        split,
        {
          exact zeroF M,
        },
        {
          intros x hx,
          have h1:x ∈ SF M:=
          begin
            have h3:= FsubsetSF M,
            have h4:= member_subset M 𝔽 (SF M)x h3 hx,
            exact h4, 
          end,
          split,
          {
            have h2:= mul_zeroNF M x h1,
            rw h2,
            exact zeroSF M,
          },
          {
            intros z h2,
            have h5:= (multiplication2a M x h1).left,
            have h6:=  mul_zeroNF M x h1, 
            rw h6, 
            split,
            {
              intro h7,
              have h8:= zero_or_successor M z h2,
              cases h8 with h9 h10,
              {
                exact h9,
              },
              {
                cases h10 with u h11,
                cases h11 with h12 h13,
                have h14: ¬ z = zero:=
                  begin
                    intro h15,
                    rw h15 at *,
                    have h16:= Fregesuccessoromits0 M u,
                    contradiction,
                  end,
                have h15:= multiplication3 M x zero z h7,
                cases h15 with h16 h17,
                have h18:= h17 h14, 
                cases h18 with p h19,
                cases h19 with q h20,
                cases h20 with r h21,
                rcases h21 with ⟨ h22, h23, h24⟩, 
                have h25:= Fregesuccessoromits0 M q,
                rw sym at h23,
                contradiction, 
              }
            },
            {
              intro h7,
              rw h7 at *,
              have h8:= multiplication2a M x h1,
              exact h8.left, 
            }
          }
        }
      end,
    have step: ∀ (y:M), y ∈ Z_multiplication5 M → (∃ (u:M), u ∈ (𝕊 y)) → 𝕊 y ∈ Z_multiplication5 M:=
      begin
        have h3:= multhelper2 M,
        intros y h4,
        rw Z_multiplication5_members at h4,
        rw Z_multiplication5_members,
        intros hsy,
        have h5:= successorF M y h4.left hsy,
        split,
        {
          exact h5, 
        },
        {
          cases h4 with h6 h7,
          intros x hx,
          have h30: x ∈ SF M:=
            begin
              have h31:= FsubsetSF M,
              exact member_subset M 𝔽 (SF M) x h31 hx,
            end,
          have h8:= h3 x y h30 h6 h5,
          have h9:= h7 x hx,
          cases h9 with h10 h11, 
          have h12:= h8 h10 h11, 
          exact h12, 
        }
      end,
    intros y h,
    rw F_members at h,
    specialize h (Z_multiplication5 M),
    have h3:= h ⟨ base, step⟩, 
    rw Z_multiplication5_members at h3,
    exact h3.right,
  end

theorem multiplication: ∀(x y:M), x∈ 𝔽 → y ∈ 𝔽 → (𝕊 y ∈ 𝔽 ) → x* (𝕊 y) = x * y + x:=
  begin
    have h2:= multiplication5 M,
    have h3:= multhelper M,
    intros x y hx hy hsy,
    have h4:x ∈ SF M:=
      begin
        have h5:= FsubsetSF M,
        exact member_subset M 𝔽 (SF M) x h5 hx, 
      end,
    have h6:= h3 x y h4 hy hsy, 
    have h7:= h2 y hy x hx,
    cases h7 with h8 h9,
    have h10:= h6 h8 h9, 
    exact h10, 
  end

lemma right_distributiveNF: ∀ (z:M), z ∈ 𝔽 → ∀ (x y: M), x ∈ 𝔽 → y ∈ 𝔽 → y+z ∈ 𝔽 → 
x * (y+z) = x * y + x * z:=
  begin
    have base: zero ∈ Z_right_distributiveNF M:=
      begin
        rw Z_right_distributiveNF_members,
        split,
        {
          exact zeroF M,
        },
        {
          intros x y hx hy h100,
          rw right_identityNF,
          have h3:x ∈ SF M:=
             member_subset M 𝔽 (SF M) x (FsubsetSF M) hx,
          rw (mul_zeroNF M x h3),
          rw right_identityNF,
        }
      end,
    have step: ∀ (z:M), z ∈ Z_right_distributiveNF M →
      (∃ (u:M), u ∈ (𝕊 z)) → 𝕊 z ∈ Z_right_distributiveNF M:=
      begin
        intros z h2 hsz,
        rw Z_right_distributiveNF_members at h2,
        cases h2 with h3 h4,
        rw Z_right_distributiveNF_members,
        have h5:z ∈ SF M:=
             member_subset M 𝔽 (SF M) z (FsubsetSF M) h3,
        split,
        { 
          exact successorF M z h3 hsz, 
        },
        {
          intros x y hx hy h100,
          have h30:=  successorF M z h3 hsz,
          have h6:= multiplication M x z hx h3 h30, 
          rw h6,
          rw←  associativityNF,
        
          rw addition_equation,
          rw addition_equation at h100,
          have h200: y + z ∈ 𝔽 :=
            begin
              have h190: y ∈ SF M := 
                member_subset M 𝔽 (SF M) y (FsubsetSF M) hy, 
              have h191: z ∈ SF M :=
                member_subset M 𝔽 (SF M) z (FsubsetSF M) h3,
              have h192:= additionSF M z h191 y h190,
              have h193:= successorSFF M (y+z) h192 h100,
              exact h193,
            end,
          have h7:= h4 x y hx hy h200,
          rw← h7,
          have h8:= multiplication M x (y+z) hx,
          have h9:= h8 h200 h100, 
          exact h9, 
        }
      end,
    intros z h,
    rw F_members at h,
    specialize h (Z_right_distributiveNF M),
    have h3:= h ⟨ base, step⟩, 
    rw Z_right_distributiveNF_members at h3,
    exact h3.right, 
  end

lemma subtractionF: ∀(u:M), u ∈ 𝔽 → ∀(x:M), x ∈ SF M → x+u ∈ 𝔽 → x ∈ 𝔽 :=
  begin
    have base: zero ∈ Z_subtractionF M:=
      begin
        rw Z_subtractionF_members,
        split,
        {
          exact zeroF M,
        },
        {
          intros x hx h3,
          rw right_identityNF at h3,
          exact h3,
        }
      end,
    have step: ∀ (u:M), u ∈ Z_subtractionF M → (∃ (p:M),p ∈ 𝕊 u) → 𝕊 u ∈ Z_subtractionF M:=
      assume u,
      begin
        intros  hIH  hsu, 
        rw Z_subtractionF_members at hIH,
        rw Z_subtractionF_members,
        split,
        {
          exact successorF M u hIH.left hsu,
        },
        {
          intros x hx h4,
          have h5:= successorF M u hIH.left hsu,
          cases hIH with h6 h7,
          have h8:= h7 x hx, 
          rw addition_equation at h4,
          have h9:u∈ SF M:=
            member_subset M 𝔽 (SF M) u (FsubsetSF M) h6,
          have h10:= additionSF M u h9 x hx, 
          have h11:= successorSFF M (x+u) h10 h4,
          exact h7 x hx h11,
        }
      end,
    intros u h,
    rw F_members at h,
    specialize h (Z_subtractionF M),
    have h4:= h ⟨ base,step⟩, 
    rw Z_subtractionF_members at h4,
    exact h4.right,
  end

lemma multiplicationSF2: ∀ (x y:M), x ∈ 𝔽  → y ∈ 𝔽 → x * y ∈ SF M:=
  assume x y,
  begin
    intros hx hy,
    have h4:= multiplication5 M y hy x hx,
    exact h4.left, 
  end

lemma assoc_helper: ∀(y z:M), y ∈ 𝔽  → z ∈ 𝔽 → 𝕊 z ∈ 𝔽 → y*(𝕊 z) ∈ 𝔽 → y*z ∈ 𝔽:=
  assume y z,
  begin
    intros hy hz hsz hysz,
    have h3:= multiplication M y z hy hz hsz,
    rw h3 at hysz,
    have h4:= subtractionF M y hy, 
    have h20: y ∈ SF M:= 
      member_subset M 𝔽 (SF M) y (FsubsetSF M) hy,
    have h21: z ∈ SF M:= 
      member_subset M 𝔽 (SF M) z (FsubsetSF M) hz,
    have h22:= multiplicationSF2 M y z hy hz,
    have h5:= h4 (y*z) h22 hysz,
    exact h5, 
  end

lemma multiplication_associative: ∀ (z:M), z ∈ 𝔽 → 
∀ (x y:M), x ∈ 𝔽 → y ∈ 𝔽 → x * y ∈ 𝔽 → y*z ∈ 𝔽 → x * (y* z) = (x * y) * z:=
  begin
    have base: zero ∈ Z_multiplication_associative M:=
      begin
        rw Z_multiplication_associative_members,
        split,
        {
          exact zeroF M,
        },
        {
          intros x y hx hy hxy hyz, 
          have h3: y ∈ SF M:= 
            member_subset M 𝔽 (SF M) y (FsubsetSF M) hy,
          have h4:= mul_zeroNF M y h3,
          have h5: x ∈ SF M:= 
            member_subset M 𝔽 (SF M) x (FsubsetSF M) hx,
          have h6:= mul_zeroNF M x h5,
          rw h4,
          rw h6,
          have h7: x*y ∈ SF M:=
            member_subset M 𝔽 (SF M) (x*y) (FsubsetSF M) hxy,
          have h8:= mul_zeroNF M (x*y) h7,
          rw h8,
        }
      end,
    have step: ∀(z:M), z ∈ Z_multiplication_associative M →
      (∃ (u:M), u ∈ 𝕊 z) → 𝕊 z ∈ Z_multiplication_associative M :=
      assume z,
      begin
        intros hIH hsz,
        rw Z_multiplication_associative_members at hIH,
        rw Z_multiplication_associative_members,
        split,
        {
          exact successorF M z (hIH.left) hsz,
        },
        {
          cases hIH with hz h3,
          intros x y hx hy hxy hysz,
          have h40:= successorF M z hz hsz,
          have h4:= assoc_helper M y z hy hz h40 hysz,
          have h5:= multiplication M y z hy hz h40, 
          rw h5 at hysz,
          have h6:= multiplication M (x*y) z hxy hz h40,
          have h7:= h3 x y hx hy hxy h4, 
          rw← h7 at h6, 
          have h26:= right_distributiveNF M y hy x (y*z) hx h4 hysz,
          rw h6,
          rw← h26,
          rw h5,
        }
      end,
    intros z h,
    rw F_members at h,
    specialize h (Z_multiplication_associative M),
    have h4:= h ⟨ base, step⟩, 
    rw Z_multiplication_associative_members at h4,
    exact h4.right,
  end 

lemma multiplication_associativeNF: ∀ (z:M), z ∈ 𝔽 → 
∀ (x y:M), x ∈ 𝔽 → y ∈ 𝔽 → x * y ∈ 𝔽 → y*z ∈ 𝔽 → x * (y* z) = (x * y) * z:=
  begin
    have base: zero ∈ Z_multiplication_associative M:=
      begin
        rw Z_multiplication_associative_members,
        split,
        {
          exact zeroF M,
        },
        {
          intros x y hx hy hxy hyz, 
          have h3: y ∈ SF M:= 
            member_subset M 𝔽 (SF M) y (FsubsetSF M) hy,
          have h4:= mul_zeroNF M y h3,
          have h5: x ∈ SF M:= 
            member_subset M 𝔽 (SF M) x (FsubsetSF M) hx,
          have h6:= mul_zeroNF M x h5,
          rw h4,
          rw h6,
          have h7: x*y ∈ SF M:=
            member_subset M 𝔽 (SF M) (x*y) (FsubsetSF M) hxy,
          have h8:= mul_zeroNF M (x*y) h7,
          rw h8,
        }
      end,
    have step: ∀(z:M), z ∈ Z_multiplication_associative M →
      (∃ (u:M), u ∈ 𝕊 z) → 𝕊 z ∈ Z_multiplication_associative M :=
      assume z,
      begin
        intros hIH hsz,
        rw Z_multiplication_associative_members at hIH,
        rw Z_multiplication_associative_members,
        split,
        {
          exact successorF M z (hIH.left) hsz,
        },
        {
          cases hIH with hz h3,
          intros x y hx hy hxy hysz,
          have h40:= successorF M z hz hsz,
          have h4:= assoc_helper M y z hy hz h40 hysz,
          have h5:= multiplication M y z hy hz h40, 
          rw h5 at hysz,
          have h6:= multiplication M (x*y) z hxy hz h40,
          have h7:= h3 x y hx hy hxy h4, 
          rw← h7 at h6, 
          have h26:= right_distributiveNF M y hy x (y*z) hx h4 hysz,
          rw h6,
          rw← h26,
          rw h5,
        }
      end,
    intros z h,
    rw F_members at h,
    specialize h (Z_multiplication_associative M),
    have h4:= h ⟨ base, step⟩, 
    rw Z_multiplication_associative_members at h4,
    exact h4.right,
  end 

lemma mul_oneNF: ∀ (x:M), x ∈ 𝔽  → x* one = x:=
  assume x,
  begin
    intro hx,
    rw one_definition,
    have h2:= oneF M,
    rw one_definition at h2, 
    have h3:= multiplication M x zero hx (zeroF M) h2,
    rw h3,
    have h5:x ∈ SF M := member_subset M 𝔽 (SF M) x (FsubsetSF M) hx,
    have h4:= mul_zeroNF M x h5,
    rw h4,
    rw left_identityNF,
  end

lemma twoequalsoneplusone: (two:M) = one + one:=
  begin
    rw two_definition,
    rw one_definition,
    rw addition_equation,
    rw right_identityNF,
  end

lemma timestwo: ∀ (x:M), x ∈ 𝔽  → x + x = x * two:=
  assume x,
  begin
    intro hx,
    have h3:= mul_oneNF M x hx,
    rw twoequalsoneplusone,
    have h2:= twoF M,
    rw twoequalsoneplusone at h2,
    have h4:= right_distributiveNF M one (oneF M) x one hx (oneF M) h2,
    rw h4,
    rw (mul_oneNF M x hx),
  end 

lemma xlessthansuccessorx: ∀(x:M), x ∈ 𝔽 → 𝕊 x ∈ 𝔽 → x < 𝕊 x:=
  assume x,
  begin
    intros h h2,
    have h3:= cardinalsinhabited M (𝕊 x) h2,
    cases h3 with w h4,
    have h4copy := h4,
    rw successor_members M at h4,
    cases h4 with u h5,
    cases h5 with c h6,
    rcases h6 with ⟨ h7, h8, h9⟩,
    have h10: x ≤ 𝕊 x:=
      begin
        rw le_definition, 
        use u,
        use w,
        repeat{ split},
        {
          exact h7,
        },
        {
          exact h4copy,
        },
        {
          rw h9, 
          exact subset_union2 M u (single c),
        },
        {
          rw h9,
          rw full_extensionality,
          intro t,
          repeat{rw binary_union_axiom},
          rw minus_members,
          rw binary_union_axiom,
          repeat{rw singleton1 M}, 
          split,
          {
            intro h10,
            cases h10 with h11,
            {
              left,
              exact h11,
            },
            {
              rw h10 at *,
              simp,
              exact or.inr h8,
            }
          },
          {
            intro h10,
            cases h10 with h11 h12,
            {
              exact or.inl h11,
            },
            {
              cases h12 with h13 h14,
              exact h13,
            }
          }
        }
      end,
    rw lessthan_definition,
    split,
    {
      exact h10,
    },
    {
      have h11:= xnotequalsuccessorx M x h,
      exact h11, 
    }
  end

 
lemma one_mulNF: ∀ (x:M), x ∈ 𝔽 → one *x = x:=
  begin
    have base: zero ∈ Z_one_mulNF M:=
      begin
        rw Z_one_mulNF_members, 
        have h4:= member_subset M 𝔽 (SF M) one (FsubsetSF M)  (oneF M), 
        have h5:= mul_zeroNF M one h4,
        exact ⟨ zeroF M, h5⟩,
      end,
    have step: ∀ (x:M), x ∈ Z_one_mulNF M → (∃(u:M), u ∈ 𝕊 x) → 𝕊 x ∈ Z_one_mulNF M:=
      begin
        intros x hIH hsx,
        rw Z_one_mulNF_members at hIH,
        cases hIH with hx h3,
        have h4:= successorF M x hx hsx, 
        rw Z_one_mulNF_members,
        split,
        {
          exact h4,
        },
        {
          have h5:= multiplication M one x (oneF M) hx h4,
          rw h5,
          rw one_definition,
          rw addition_equation,
          rw right_identityNF,
          rw← one_definition,
          rw h3,
        }
      end,
    intros x h,
    rw F_members at h,
    specialize h (Z_one_mulNF M),
    have h4:= h ⟨ base,step⟩, 
    rw Z_one_mulNF_members at h4,
    exact h4.right,
  end 

lemma left_distributiveNF: ∀ (z:M), z ∈ 𝔽 → ∀ (x y:M),
x ∈ 𝔽 → y ∈ 𝔽 → x + y ∈ 𝔽 → (x+y)*z = x * z + y * z:=
  begin
    have base: zero ∈ Z_left_distributive M:=
      begin
        rw Z_left_distributive_members, 
        split,
        {
          exact zeroF M,
        },
        {
          intros x y hx hy h,
          have h3:= member_subset M 𝔽 (SF M) x (FsubsetSF M) hx,
          have h4:= member_subset M 𝔽 (SF M) y (FsubsetSF M) hy,
          have h5:= additionSF M y h4 x h3,
          rw mul_zeroNF M (x+y) h5,
          rw mul_zeroNF M x h3,
          rw mul_zeroNF M y h4,
          rw right_identityNF,
        }
      end, 
    have step: ∀(z:M), z ∈ Z_left_distributive M → 
       (exists (u:M), u ∈ 𝕊 z) → 𝕊 z ∈ Z_left_distributive M:=
      begin
        intros z hIH hsz,
        rw Z_left_distributive_members,
        rw Z_left_distributive_members at hIH,
        cases hIH with hz h3,
        split,
        {
          exact successorF M z hz hsz,
        },
        {
          intros x y hx hy hsxy,
          have h7:= hsxy,
          have h4:= successorF M z hz hsz, 
          have h5:= multiplication M (x+y) z h7 hz h4, 
          rw h5, 
          have h6:= h3 x y hx hy h7, 
          rw h6, 
          have h11:= multiplication M x z hx hz h4, 
          rw h11,
          have h12:= multiplication M y z hy hz h4, 
          rw h12,
          have h13:  y * z + (x + y) =   x + (y * z + y) :=
            begin
              rw commutativityNF,
              rw← associativityNF,
              symmetry,
              rw commutativityNF,
              rw←  associativityNF,
              rw commutativityNF M y x,   
            end,
          rw associativityNF,
          rw h13,
          rw associativityNF,
        }
      end,
    intros z h,
    rw F_members at h,
    specialize h (Z_left_distributive M),
    have h4:= h ⟨ base, step⟩, 
    rw Z_left_distributive_members at h4,
    exact h4.right, 
  end 

lemma multiplication_commutative: ∀ (y:M), y ∈ 𝔽 → ∀ (x:M), x ∈ 𝔽 → x* y = y * x:=
  begin
    have base: zero ∈ Z_multiplication_commutative M:=
      begin
        rw Z_multiplication_commutative_members,
        split,
        {
          exact zeroF M,
        },
        { 
          intros x hx,
          rw zero_mulNF M x hx,
          have h4:= member_subset M 𝔽 (SF M) x (FsubsetSF M) hx,
          rw mul_zeroNF M x h4,
        }
      end,
    have step: ∀(y:M), y ∈ Z_multiplication_commutative M →
    (∃(u:M), u ∈ 𝕊 y) → 𝕊 y ∈ Z_multiplication_commutative M:=
      begin
        intros y h3 hsy,
        rw Z_multiplication_commutative_members at h3,
        rw Z_multiplication_commutative_members,
        cases h3 with hy h5,
        split,
        {
          exact successorF M y hy hsy,
        },
        {
          intros x hx,
          have h6:= successorF M y hy hsy,
          have h7:= multiplication M x y hx hy h6,
          rw h7,
          have h8:= h5 x hx,
          rw h8,
          have h9:= one_mulNF M x hx, 
          have h10: y*x + x = y*x + one*x:=
            begin
              rw h9,
            end,
          rw h10,
          have h11: y + one ∈ 𝔽:=
            begin
              rw one_definition,
              rw addition_equation,
              rw right_identityNF,
              exact h6, 
            end,
          rw← (left_distributiveNF M x hx y one hy (oneF M) h11), 
          rw one_definition,
          rw addition_equation,
          rw right_identityNF,
        }
      end,
    intros y h,
    rw F_members at h,
    specialize h (Z_multiplication_commutative M),
    have h4:= h ⟨ base, step⟩,
    rw Z_multiplication_commutative_members at h4,
    exact h4.right, 
  end

 
lemma addorder: ∀ (a b p q:M), a ∈ 𝔽 → b ∈ 𝔽 → p ∈ 𝔽 → q ∈ 𝔽 → b + q ∈ 𝔽 → 
a ≤ b → p ≤ q → a+p ≤ b + q:=
  assume a b p q,
  begin
    intros ha hb hp hq h5 h6 h7,
    have h8:= cardinalsinhabited M (b+q) h5, 
    cases h8 with w h9,
    rw addition_members M at h9,
    cases h9 with u h10,
    cases h10 with v h11,
    rcases h11 with ⟨ h12, h13, h14, h15⟩,
    have h12:= le2 M a b ha hb ⟨ u, h13⟩, 
    rw h12 at h6,
    have h16:= h6 u h13,
    cases h16 with r h17,
    rcases h17 with ⟨ h18, h19, h20⟩, 
    have h21:= le2 M p q hp hq ⟨ v, h14⟩, 
    rw h21 at h7,
    have h22:= h7 v h14,
    cases h22 with s h23,
    rcases h23 with ⟨ h24, h25, h26⟩, 
    have h27: (r ∪ s) ∈ a + p:=
      begin
        rw addition_members M,
        use r, use s,
        simp,
        split,
        {
          exact h18,
        },
        {
          split,
          {
            exact h24,
          },
          {
            rw full_extensionality,
            intro x,
            rw subset_definition at h19,
            specialize h19 x,
            rw subset_definition at h25,
            specialize h25 x,
            rw intersection_axiom, 
            have h26:= emptyset_axiom x,
            rw full_extensionality at h15,
            specialize h15 x, 
            rw intersection_axiom at h15,
            split,
            {
              intro h50,
              cases h50 with h51 h52,
              have h53:= h19 h51,
              have h54:= h25 h52,
              have h55:= (h15.mp) ⟨ h53, h54⟩, 
              contradiction, 
            },
            {
              intro h50,
              contradiction, 
            }
    
          }
        }
      end,
    rw le_definition,
    use (r ∪ s), use (u ∪ v),
    repeat{split},
    {
      exact h27,
    },
    {
      rw addition_members,
      use u, use v,
      simp,
      repeat{split},
      {
        exact h13,
      },
      {
        exact h14,
      },
      {
        exact h15, 
      }
    },
    {
      rw subset_definition,
      intro t,
      rw binary_union_axiom,
      rw binary_union_axiom,
      rw subset_definition  at h19 h25,
      specialize h19 t,
      specialize h25 t,
      intro h50,
      cases h50 with h51 h52,
      {
        left,
        exact h19 h51, 
      },
      {
        right,
        exact h25 h52, 
      }
    },
    {
      rw full_extensionality,
      intro t,
      repeat {rw binary_union_axiom},
      rw minus_members,
      repeat {rw binary_union_axiom},
      rw subset_definition  at h19 h25,
      specialize h19 t,
      specialize h25 t,
      rw full_extensionality at h15,
      specialize h15 t,
      rw intersection_axiom at h15, 
      have h27:= emptyset_axiom t,
      rw←  h15 at h27,
      rw full_extensionality at h20 h26,
      specialize h20 t,
      specialize h26 t,
      rw binary_union_axiom at h20 h26,
      rw minus_members at h20 h26,
      split,
      {
        intro h28,
        cases h28 with h29 h30,
        {
          rw h20 at h29,
          cases h29 with h30 h31,
          {
            left,
            left,
            exact h30, 
          },
          {
            cases h31 with h32 h33,
            rw  h20 at h32, 
            cases h32 with h34 h35,
            {
              contradiction,
            },
            {
              cases h35 with h36 h37,
              push_neg at h27,
              have h37:= h27 h36,
              right,
              split,
              {
                left, 
                exact h36,
              },
              {
                intro h38,
                cases h38 with h39 h40,
                {
                  contradiction,
                },
                {
                  have h41:= h25 h40,
                  contradiction, 
                }
              }
            }
          }
        },
        {
          have h40:= h26.mp h30,
          cases h40 with h41 h42,
          {
            left,
            exact or.inr h41,
          },
          {
            cases h42 with h43 h44,
            right,
            split,
            {
              exact or.inr h43,
            },
            {
              intro h45,
              cases h45 with h46 h47,
              {
                have h48:= h19 h46, 
                have h49:= h27 ⟨ h48, h43⟩, 
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
        intro h40,
        cases h40 with h41 h42,
        {
          cases h41 with h43 h44,
          {
            exact or.inl (h19 h43),
          },
          {
            exact or.inr (h25 h44),
          }
        },
        {
          cases h42 with h45 h46,
          exact h45,
        }
      }
    } 
  end 



lemma exp_sum: ∀ (q:M), q ∈ 𝔽 → ∀ (p:M),p ∈ 𝔽  → p+q ∈ 𝔽 → exp M (p+q) ∈ 𝔽 → 
exp M p ∈ 𝔽 ∧ exp M q ∈ 𝔽 ∧ (exp M p)*(exp M q) ∈ 𝔽 ∧ 
exp M (p+q) = (exp M p)*(exp M q):=
  begin
    have base: zero ∈ Z_exp_sum M:=
      begin
        rw Z_exp_sum_members,
        split,
        {
          exact zeroF M,
        },
        {
          intros p hp h2 h3,
          rw right_identityNF at *,
          split,
          {
            exact h3,
          },
          {
            split,
            {
              rw exp_zero,
              exact oneF M,
            },
            {
              split,
              {
                rw exp_zero, 
                rw mul_oneNF M (exp M p) h3,
                exact h3, 
              },
              {
                rw exp_zero,
                rw mul_oneNF,
                exact h3,
              }
            }
          }
        }
      end,
    have step: ∀ (q:M), q ∈ Z_exp_sum M → (∃(u:M), u ∈ 𝕊 q)→ 𝕊 q ∈ Z_exp_sum M:=
      assume q,
      begin
        intros hIH hsq,
        rw Z_exp_sum_members  at hIH,
        rw Z_exp_sum_members, 
        cases hIH with hq h3,
        split,
        {
          exact successorF M q hq hsq,
        },
        {
          intros p hp  h4 h5,
          have h6:= subterms3 M p q hp hq h4,
          have hsqF:= successorF M q hq hsq,
          have h4copy := h4, 
          have h5copy := h5, 
          rw addition_equation at h4 h5,
          have h8:= exprec M (p+q) h6 h5,
          rw h8 at h5, 
          have h9: p + q ≤  p + 𝕊 q:=
            begin
              rw addition_equation,
              have h10:= xlessthansuccessorx M (p+q) h6 h4, 
              rw lessthan_definition at h10,
              exact h10.left,  
            end,
          have h10:= exporder M (p+q) (p + 𝕊 q) h6 h4copy h9 (cardinalsinhabited M (exp M (p+𝕊 q)) h5copy),
          cases h10 with h11 h12, 
          have h13:= finiteexp M (p+q) h6 h11,   
          have h20:= timestwo M (exp M (p+ q)) h13,
          rw← h8 at h20,
          have h69:= h6,
          rw  commutativityNF at h69, 
          have h37:= xlessthan_xplusy M q p hq hp h69,
          rw commutativityNF at h37,
          have h39:= exporder M q (p+q) hq h6 h37 h11,
          cases h39 with h40 h41,
          have h16:= finiteexp M q hq h40,
          have h35: (exp M q)* two ∈ 𝔽:= 
            begin
              have h36:= timestwo M (exp M (p+q)) h13,
              rw← h8 at h36,
              have h5copy2:= h5copy,
              rw← addition_equation at h36, 
              rw h36 at h5copy2, 
              have h42:= addorder M (exp M q) (exp M (p+q)) (exp M q) (exp M (p+q)) h16 h13 h16 h13 h5 h41 h41,
              have h43:= timestwo M (exp M q) h16, 
              rw h43 at h42, 
              rw le_definition at h42, 
              cases h42 with a h43,
              cases h43 with b h44,
              cases h44 with h45 h46,
              have h47:= timestwo M (exp M q) h16,
              rw←  h47,
              rw← h47 at h45, 
              have h48:= inhabited_sum M (exp M q) h16 (exp M q) h16 ⟨ a, h45⟩,
              exact h48,
            end, 
          have h51: p ≤ p+q := xlessthan_xplusy M p q hp hq h6,
          have h52:= exporder M p (p+q) hp h6 h51 h11,
          cases h52 with h52 h54, 
          have h15:= finiteexp M p hp h52, 
          have h60:= h3 p hp h6 h13,
          rcases h60 with ⟨ h61, h62, h63, h64⟩,
          have h40:= multiplication_associativeNF M two (twoF M) (exp M p) (exp M q) h15 h16 h63 h35, 
          rw h64 at h20, 
          rw←  h40 at h20,
          have h21:= timestwo M (exp M q) h16, 
          rw← h21 at h20, 
          have hsqF:= successorF M q hq hsq,
          have h22: exp M (𝕊 q) ∈ 𝔽 := 
            begin
              have h23: 𝕊 q ≤   𝕊 q + p:=
                begin
                  have h24:= xlessthan_xplusy M (𝕊 q) p hsqF hp,
                  apply h24,
                  rw commutativityNF,
                  exact h4copy,
                end,
              rw commutativityNF at h4copy,
              have h25:= exporder M (𝕊 q) (𝕊 q + p) hsqF h4copy h23,
              rw commutativityNF at h5copy,
              have h26:= cardinalsinhabited M (exp M (𝕊 q + p)) h5copy,
              have h27:= h25 h26,
              cases h27 with h28 h29,
              have h30:= finiteexp M (𝕊 q) (successorF M q hq hsq) h28,
              exact h30, 
            end,
          have h30:= exprec M q hq h22, 
          rw← h30 at h20, 
          rw← addition_equation at h20,
          repeat{split},
          {
            exact h15,
          },
          {
            exact h22,
          },
          {
            rw← h20,
            exact h5copy,
          },
          {
            exact h20,
          }
        }
      end,
    intros q h,
    rw F_members at h,
    specialize h (Z_exp_sum M),
    have h3:= h ⟨ base, step⟩, 
    rw Z_exp_sum_members at h3,
    exact h3.right,
  end


lemma xcrossempty: ∀ (x:M), x × Λ = Λ:=
  assume x,
  begin
    rw full_extensionality,
    intro t,
    rw product_axiom, 
    split,
    {
      intro h,
      cases h with a h2,
      cases h2 with b h3,
      rcases h3 with ⟨ h4, h5, h6⟩, 
      have h7:= emptyset_axiom b,
      contradiction,
    },
    {
      intro h,
      have h3:=emptyset_axiom t,
      contradiction, 
    }
  end

lemma emptycrossx: ∀ (x:M), Λ × x = Λ:=
  assume x,
  begin
    rw full_extensionality,
    intro t,
    rw product_axiom, 
    split,
    {
      intro h,
      cases h with a h2,
      cases h2 with b h3,
      rcases h3 with ⟨ h4, h5, h6⟩, 
      have h7:= emptyset_axiom a,
      contradiction,
    },
    {
      intro h,
      have h3:=emptyset_axiom t,
      contradiction, 
    }
  end

lemma product_adjoin: ∀ (a b B:M), (single a) × (B  ∪ (single b)) = (((single a) × B) ∪ (single ‹ a,b › )):=
  assume a b B,
  begin
    rw full_extensionality,
    intro t,
    split,
    {
      intro h,
      rw product_axiom at h,
      cases h with p h2,
      cases h2 with q h3,
      rcases h3 with ⟨ h4, h5, h6⟩,
      rw singleton1 at h4,
      rw h4 at *,
      rw h6 at *,
      have h7:= pair_in_product M a q (single a) B,
      rw binary_union_axiom,
      rw h7,
      rw singleton1,
      rw singleton1,
      rw ordered_pair_equality,
      simp,
      rw binary_union_axiom at h5,
      rw singleton1 at h5,
      exact h5, 
    },
    {
      intro h,
      rw binary_union_axiom at h,
      cases h with h2 h3,
      {
        rw product_axiom at h2,
        cases h2 with p h3,
        cases h3 with q h4,
        rcases h4 with ⟨ h5, h6, h7⟩,
        rw h7,
        have h8:= pair_in_product M p q (single a) (B ∪ (single b)),
        rw h8,
        split,
        {
          exact h5,
        },
        {
          rw binary_union_axiom,
          exact or.inl h6, 
        }
      },
      {
        rw singleton1 at h3,
        rw h3,
        rw pair_in_product,
        rw singleton1,
        simp,
        rw binary_union_axiom,
        rw singleton1,
        simp,
      }
    }
  end

lemma productfinite_helper: ∀ (Y:M), Y ∈ FINITE M → ∀ (A a:M), A ∈ DECIDABLE M → Y ⊆ A → single a × Y ∈ FINITE M:=
  begin
    have base: Λ ∈ W_finiteproduct_helper M:=
      begin
        rw W_finiteproduct_helper_members,
        split,
        {
          exact lambda_finite M,
        },
        { 
          intros A a hA h3,
          rw xcrossempty M (single a),
          exact lambda_finite M,
        }
      end,
    have step: adjoin_closed M (W_finiteproduct_helper M):=
      begin
        unfold adjoin_closed,
        intros B b h,
        cases h with h3 h4,
        rw W_finiteproduct_helper_members at h3,
        rw W_finiteproduct_helper_members,
        cases h3 with h5 h6, 
        split,
        {
          have h7:= finite_adjoin M B b ⟨ h5, h4⟩, 
          exact h7, 
        },
        {
          intros A a h8 h9,
          have h10:= h6 A a h8,
          have h11: B ⊆ A:=
            begin
              rw subset_definition,
              intros t h12,
              have h13:= adjoin_member2 M t b B h12,
              have h14:= member_subset M (B ∪ (single b)) A t h9 h13,
              exact h14, 
            end,
          have h15:= h10 h11,
          have h16:= product_adjoin M a b B,
          rw h16,
          have h17:= finite_adjoin M (single a × B) ‹ a,b›,
          apply h17,
          split,
          {
            exact h15,
          },
          {
            rw pair_in_product,
            rw singleton1,
            simp,
            exact h4,
          }
        }
      end,
    have h: (FINITE M) ⊆ W_finiteproduct_helper M:= finite_conditions M (W_finiteproduct_helper M) step base, 
    rw subset_definition at h, 
    intros X h2, 
    specialize h X,
    rw (W_finiteproduct_helper_members M) at h, 
    have h5:= h h2, 
		cases h5 with h6 h7, 
    exact h7, 
  end 

lemma productofunion: ∀ (X Y Z:M), (X ∪ Y) × Z = ((X × Z) ∪ (Y × Z)):=
  begin
    intros X Y Z,
    rw full_extensionality,
    intros t,
    rw binary_union_axiom,
    rw product_axiom,
    split,
    {
      intros h3,
      cases h3 with a h4,
      cases h4 with b h5,
      cases h5 with h6 h7,
      cases h7 with hb ht,
      rw ht at *,
      rw binary_union_axiom at h6,
      cases h6 with ha h9,
      {
        left,
        rw product_axiom,
        use a, use b,
        simp,
        exact ⟨ ha, hb⟩,

      },
      {
        right,
        rw product_axiom,
        use a, use b,
        simp,
        exact ⟨ h9, hb⟩,
      }
    },
    {
      intros h10,
      cases h10 with h11 h12,
      {
        rw product_axiom at h11,
        cases h11 with a h12,
        cases h12 with b h13,
        use a, use b,
        cases h13 with h14 h15,
        cases h15 with h16 h17,
        rw h17 at *,
        simp,
        rw binary_union_axiom,
        split,
        {
          left,
          exact h14,
        },
        {
          exact h16,
        }
      },
      {
        rw product_axiom at h12,
        cases h12 with a h20 h21,
        cases h20 with b h22 h23,
        use a, use b,
        cases h22 with ha h24,
        cases h24 with h25 h26,
        rw h26 at *,
        simp,
        split,
        {
          rw binary_union_axiom,
          right,
          exact ha,
        },
        {
          exact h25,
        }
      }
    }
  end

lemma productfinite_helper2: ∀ (a Y:M), Y ∈ FINITE M → (single a) × Y ∈ FINITE M:=
  begin
    intros a Y,
    set f:= W_productfinite_helper2 M a Y with fdef,
    have h4: similarity M f (USC (USC Y)) ((single a) × Y) :=
      begin
        unfold similarity,
        split,
        {
          unfold oneone,
          split,
          {
            unfold maps,
            repeat{split},
            {
              rw Rel_definition,
              intros z hz,
              rw fdef at hz,
              rw W_productfinite_helper2_members at hz,
              cases hz with y h4,
              use single (single y),
              use ‹ a,y ›,
              exact h4.1,
            },
            {
              intros x y h10,
              cases h10 with h11 h12,
              rw usc at h11,
              cases h11 with A h13,
              cases h13 with h14 h15,
              rw usc at h14,
              cases h14 with b h16,
              cases h16 with hb h17,
              rw h17 at *,
              rw h15 at *,
              rw fdef at h12,
              rw W_productfinite_helper2_members at h12,
              cases h12 with c h20,
              cases h20 with h21 hc,
              rw ordered_pair_equality at h21,
              cases h21 with h22 h23,
              have h24:= single_oneone M (single b) (single c) h22,
              have h25:= single_oneone M b c h24,
              rw h25 at *,
              rw h23 at *,
              rw product_axiom,
              use a, use c,
              rw singleton1,
              simp,
              exact hb,
            },
            {
              intros x y z h3,
              cases h3 with h4 h5,
              cases h5 with h6 h7,
              rw fdef at h6 h7,
              rw W_productfinite_helper2_members at h6 h7,
              cases h7 with p h8,
              cases h6 with q h9,
              rw usc at h4,
              cases h4 with r h10,
              cases h10 with h11 h12,
              rw usc at h11,
              cases h11 with s h13,
              cases h13 with h14 h15,
              rw h12 at *,
              rw h15 at *,
              rw ordered_pair_equality at h8,
              rw ordered_pair_equality at h9,
              cases h8 with h16 h17,
              cases h16 with h18 h19,
              cases h9 with h20 h21,
              cases h20 with h22 h23,
              have h24:= single_oneone M (single s) (single p ) h18,
              have h25:= single_oneone M s p h24,
              have h26:= single_oneone M (single s) (single q) h22,
              have h27:= single_oneone M s q h26,
              rw h27 at *,
              rw h25 at *,
              rw h19 at *,
              rw h23 at *,
            },
            {
              intros x h40,
              rw usc at h40,
              cases h40 with p h41,
              cases h41 with h42 h43,
              rw usc at h42,
              cases h42 with q h43,
              cases h43 with h44 h45,
              rw h43 at *,
              rw h45 at *,
              use ‹a,q›,
              split,
              {
                rw product_axiom,
                use a, use q,
                rw singleton1,
                simp,
                exact h44,
              },
              {
                rw fdef,
                rw W_productfinite_helper2_members,
                use q,
                simp,
                exact h44,
              }
            }
          },
          {
            split,
            {
              intros x u y h50,
              cases h50 with h51 h52,
              cases h52 with h53 h54,
              rw fdef at h51 h53,
              rw W_productfinite_helper2_members at h51 h53,
              cases h53 with A h55,
              cases h51 with B h56,
              cases h55 with h57 h58,
              cases h56 with h59 h60,
              rw ordered_pair_equality at h57 h59,
              rw h59.1 at *,
              rw h59.2 at *,
              rw h57.1 at *,
              rw h57.2 at *,
              cases h57 with h61 h62,
              rw ordered_pair_equality at h62,
              rw h62.2 at *,
            },
            {
              intros x y h70,
              cases h70 with h71 h72,
              rw fdef at h71,
              rw W_productfinite_helper2_members at h71,
              cases h71 with p h73,
              cases h73 with h74 h75,
              rw ordered_pair_equality at h74,
              rw h74.1 at *,
              rw h74.2 at *,
              rw usc,
              use single p,
              simp,
              rw usc,
              use p,
              simp,
              exact h75,
            }
          }
        },
        {
          unfold onto,
          intros y hy,
          rw product_axiom at hy,
          cases hy with A h80,
          cases h80 with B h81,
          cases h81 with h82 h83,
          cases h83 with h84 h85,
          rw singleton1 at h82,
          rw h82 at *,
          rw h85 at *,
          use single (single B),
          split,
          {
            rw usc,
            use single B,
            simp,
            rw usc,
            use B,
            simp,
            exact h84,
          },
          {
            rw fdef,
            rw W_productfinite_helper2_members,
            use B,
            simp,
            exact h84,
          }
        }
      end,
    intros hY,
    have h90: similar M (USC (USC Y)) ((single a) × Y):=
      begin
        unfold similar,
        use f,
        exact h4,
      end,
    have h91:= finitesimilar M (USC (USC Y)) ((single a) × Y) h90,
    apply h91,
    have h92:= uscfinite M Y,
    have h93:= h92.2 hY,
    have h94:= uscfinite M (USC Y),
    have h95:= h94.2 h93,
    exact h95,
  end

lemma productfinite2: ∀ (X:M), X ∈ FINITE M → ∀ (Y:M), Y ∈ FINITE M → X × Y ∈ FINITE M:=
  begin
    have base: Λ ∈ W_productfinite2 M:=
      begin
        rw W_productfinite2_members,
        split,
        {
          exact lambda_finite M,
        },
        {
          intros Y hY,
          have h3: Λ × Y = Λ:=
            begin
              rw full_extensionality,
              intros x,
              split,
              {
                intros h,
                rw product_axiom Λ Y at h,
                cases h with a h4,
                cases h4 with b h5,
                cases h5 with h6 h7,
                have h8:= emptyset_axiom a,
                contradiction,
              },
              {
                intros h,
                have h3:= emptyset_axiom x,
                contradiction,
              }
            end,
          rw h3,
          exact lambda_finite M,
        }
      end,
    have step:∀ (u a : M), ¬a ∈ u ∧ u ∈ W_productfinite2 M → u ∪ single a ∈ W_productfinite2 M:=
      begin
        intros X a h4,
        cases h4 with ha h6,
        rw W_productfinite2_members at h6,
        cases h6 with hX h7,
        rw W_productfinite2_members,
        split,
        {
          exact finite_adjoin M X a ⟨ hX, ha⟩,
        },
        {
          intros Y hY,
          have h20:= productofunion M X (single a) Y,
          rw h20,
          have h21:= h7 Y hY,
          have h22:= productfinite_helper2 M a Y hY,
          have h23: (X  × Y) ∩ ((single a) × Y) = Λ :=
            begin
              rw full_extensionality,
              intros t,
              split,
              {
                intros h,
                rw intersection_axiom at h,
                cases h with h24 h25,
                rw product_axiom at h24,
                cases h24 with p h26,
                cases h26 with q h27,
                cases h27 with h28 h29,
                cases h29 with h30 h31,
                rw h31 at *,
                rw product_axiom at h25,
                cases h25 with P h32,
                cases h32 with Q h33,
                cases h33 with h34 h35,
                cases h35 with h36 h37,
                rw ordered_pair_equality at h37,
                rw h37.1 at *,
                rw h37.2 at *,
                rw singleton1 at h34,
                rw h34 at *,
                contradiction,
              },
              {
                intros h,
                have h2:= emptyset_axiom t,
                contradiction,
              }
            end,
          have h40:= union M (X × Y) (single a × Y) h21 h22 h23,
          exact h40,
        }
      end,
    intros X hX,
    have h400:= (finite_members M X).1 hX (W_productfinite2 M) ⟨ base, step⟩,
    rw W_productfinite2_members at h400,
    exact h400.2,
  end 

lemma productfinite: ∀ (X:M), X ∈ FINITE M → ∀ (A Y:M), A ∈ DECIDABLE M → Y ∈ FINITE M → X ⊆ A → Y ⊆ A → X × Y ∈ FINITE M:=
  begin
    have base: Λ ∈ W_productfinite M:=
      begin
        rw W_productfinite_members,
        split,
        {
          exact lambda_finite M,
        },
        {
          intros A Y hA hY h21 h22,
          rw emptycrossx M Y,
          exact lambda_finite M, 
        }
      end,
    have step: adjoin_closed M (W_productfinite M):=
      begin
        unfold adjoin_closed,
        intros X a h,
        rw W_productfinite_members at h,
        rw W_productfinite_members,
        cases h with h2 h4, 
        cases h2 with h6 hIH,
        split,
        {
          have h5:= finite_adjoin M X a ⟨h6, h4⟩,
          exact h5,  
        },
        {
          intros A Y hA hY h40 h41,
          have h3: (X ∪ (single a)) × Y = ((X × Y) ∪ ((single a) × Y)):=
            begin
              rw full_extensionality, 
              intro t,
              split,
              { 
                intro h7,
                rw product_axiom at h7,
                cases h7 with p h8,
                cases h8 with q h9,
                rcases h9 with ⟨ h10, h11, h12⟩, 
                rw h12 at *,
                rw binary_union_axiom,
                rw binary_union_axiom at h10,
                cases h10 with h13 h14,
                {
                  left,
                  rw pair_in_product,
                  exact ⟨ h13, h11⟩, 
                },
                {
                  right,
                  rw pair_in_product,
                  rw singleton1,
                  rw singleton1 at h14,
                  exact ⟨ h14, h11⟩, 
                }
              },
              {
                intro h7,
                rw binary_union_axiom at h7,
                cases h7 with h8 h9,
                {
                  rw product_axiom at h8,
                  cases h8 with p h9,
                  cases h9 with q h10,
                  rcases h10 with ⟨ h11, h12, h13⟩,
                  rw h13,
                  rw pair_in_product,
                  rw binary_union_axiom,
                  exact ⟨ or.inl h11, h12⟩, 
                },
                {
                  rw product_axiom at h9,
                  cases h9 with p h10,
                  cases h10 with q h11,
                  rcases h11 with ⟨ h12, h13, h14⟩, 
                  rw h14,
                  rw pair_in_product,
                  rw singleton1 at h12,
                  rw h12 at *,
                  have h15:= adjoin_member M a X,
                  exact ⟨ h15, h13⟩,
                }
              }
            end,
          rw h3,
          have h8:= productfinite_helper M Y hY A a hA h41,
          have h43: X ⊆ A:=
            begin
              rw subset_definition, 
              intros t h44,
              have h42:= member_subset M (X ∪ (single a)) A t h40,
              rw binary_union_axiom at h42,
              exact h42 (or.inl h44),
            end,
          have h9:= hIH A Y hA hY h43 h41,
          have h10:= union M (X × Y) ((single a) × Y) h9 h8,
          apply h10,
          rw full_extensionality,
          intro t,
          rw intersection_axiom,
          split,
          {
            intro h11, 
            cases h11 with h12 h13,
            rw product_axiom at h12,
            cases h12 with p h13,
            cases h13 with q h14,
            rcases h14 with ⟨ h15, h16, h17⟩, 
            rw h17 at *,
            rw pair_in_product at h13,
            rw singleton1 at h13,
            cases h13 with h14 h15,
            rw h14 at *,
            contradiction, 
          },
          {
            intro ht,
            have h20:= emptyset_axiom t,
            contradiction,
          }
        }
      end,
    have h: (FINITE M) ⊆ W_productfinite M:= finite_conditions M (W_productfinite M) step base, 
    rw subset_definition at h, 
    intros X h2, 
    specialize h X,
    rw (W_productfinite_members M) at h, 
    have h5:= h h2, 
		cases h5 with h6 h7, 
    exact h7, 
  end
 

#axioms_all 