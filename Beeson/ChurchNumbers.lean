import inf17

variables (M:Type) [Model M] (a b x y z u v w X R W κ μ ℓ : M)
-- using ℓ where the source text has λ because you can't use λ for a variable.

open Model 

lemma sfunction1: ChurchSuccessorGraph M ∈ FUNC:=
  begin
    rw FUNC_members,
    intros x y z,
    rw ChurchSuccessorGraph_members,
    rw ChurchSuccessorGraph_members,
    intros h3 h4,
    cases h3 with p h5,
    cases h4 with q h6,
    rw ordered_pair_equality at h5,
    rw ordered_pair_equality at h6,
    cases h5 with h7 h8,
    cases h6 with h9 h10,
    rw h7 at *,
    rw h9 at *,
    rw [h8, h10],
  end
 

lemma szf_relation: ∀ (z f:M), z ∈ FUNC → f ∈ FUNC → Rel z → Rel f → Rel (Ap (S z) f):=
  assume z f,
  begin
    intros hz hf hzrel hfrel,
    rw Rel_definition,
    intros x h3,
    rw Ap_members at h3,
    cases h3 with y h4,
    cases h4 with h5 h6, 
    have h7:=  ChurchSuccessor4 M f z hz hf,
    cases h7 with y2 h8,
    cases h8 with h9 h10,
    have h11:= sfunction2 M z,
    rw FUNC_members at h11,
    have h12:= h11 f y y2 h5 h9,
    rw h12 at *,
    rw Rel_definition at h10,
    have h13:= h10 x h6,
    exact h13,
  end



lemma zeroFUNC: (ChurchZero:M) ∈ (FUNC:M):=
  begin
    rw FUNC_members,
    intros x y z h h2,
    rw ChurchZero_definition at h2,
    rw ChurchZero_definition at h,
    cases h with f h3,
    cases h2 with g h4,
    rw ordered_pair_equality at h3,
    rw ordered_pair_equality at h4,
    cases h3 with h5 h6,
    cases h4 with h7 h8,
    rw h6,
    rw h8,
  end

lemma zeroAp: ∀ (f x:M), Ap (Ap ChurchZero f) x = x :=
  assume f x,
  begin
    have h3:= Apdef M ChurchZero (zeroFUNC M),
    rw full_extensionality,
    intro t,
    rw Ap_members,
    split,
    {
      intro h,
      cases h with y h2,
      cases h2 with h4 h5,
      rw Ap_members at h4,
      cases h4 with u h6,
      cases h6 with h7 h8,
      rw ChurchZero_definition at h7,
      cases h7 with g h9,
      rw ordered_pair_equality at h9,
      cases h9 with h10 h11,
      rw h11 at *,
      rw identity_definition at h8,
      cases h8 with p h12,
      rw ordered_pair_equality at h12,
      rw h12.left at *,
      rw h12.right at *,
      exact h5, 
    },
    {
      intro ht,
      use x,
      rw and_comm,
      split,
      {
        exact ht,
      },
      {
        rw Ap_members,
        use id,
        split,
        {
          rw ChurchZero_definition,
          use f,
        },
        {
          rw identity_definition,
          use x,
        }
      }
    }
  end

lemma successorN: ∀ (n:M), n ∈ ℕℕ → S n ∈ ℕℕ := 
  begin
    have base: ChurchZero ∈ Z_ChurchSuccessorMaps M:=
      begin
        rw Z_ChurchSuccessorMaps_members,
        rw N_members,
        intros w h,
        cases h with h2 h3,
        have h4:= h3 ChurchZero h2,
        exact h4,
      end,
    have step: ∀ (n:M), n ∈ Z_ChurchSuccessorMaps M → S n ∈ Z_ChurchSuccessorMaps M:=
      begin
        intros n h,
        rw Z_ChurchSuccessorMaps_members at h,
        rw Z_ChurchSuccessorMaps_members,
        rw N_members,
        intros w h3,
        cases h3 with h4 h5,
        have h6:= h5 (S n),
        apply h6,
        rw N_members at h,
        exact h w ⟨ h4, h5⟩, 
      end,
    intros n h,
    rw N_members at h, 
    specialize h ( Z_ChurchSuccessorMaps M),
    have h3:= h (and.intro base  step), 
    rw ( Z_ChurchSuccessorMaps_members M) at h3, 
    exact h3,
  end 

lemma Churchnumbersarefunctions: ∀ (n:M), n ∈ ℕℕ → n ∈ FUNC:=
  begin
    have base:= zeroFUNC M, 
    have step: ∀ (n:M), n ∈ FUNC → S n ∈ FUNC:=
      begin
        have h:= sfunction2 M,
        intros n h2,
        exact h n,
      end,
    intros n h,
    rw N_members at h,
    specialize h FUNC,
    have h3:= h (and.intro base step),
    exact h3, 
  end

lemma Churchnumbersarerelations: ∀ (n:M), n ∈ ℕℕ → Rel n:=
  begin
    have base: ChurchZero ∈ Z_Rel M:= 
      begin
        rw Z_Rel_members, 
        rw Rel_definition,
        intros t h,
        have h3:= ChurchZero_definition t,
        rw h3 at h,
        cases h with a h4,
        use a, use id,
        exact h4,
      end,
    have step: ∀ (n:M), n ∈ Z_Rel M →  (S n) ∈ Z_Rel M :=
      begin
        intros n h,
        rw Z_Rel_members at *,
        rw Rel_definition at h,
        rw Rel_definition,
        intros t h3,
        have h4:= srelation2 M n,
        rw Rel_definition at h4,
        exact h4 t h3,
      end,
    intros n h,
    rw N_members at h,
    specialize h (Z_Rel M),
    have h3:= h (and.intro base step), 
    rw Z_Rel_members at h3,
    exact h3, 
  end

lemma zeroN: (ChurchZero:M) ∈ ℕℕ:=
  begin
    rw N_members,
    intros w h,
    exact h.left, 
  end

lemma ApZero: ∀ (x:M), Ap ChurchZero x = id:=
  begin
    intro x,
    rw full_extensionality,
    intro t,
    rw Ap_members,
    rw identity_definition,
    simp_rw ChurchZero_definition,
    split,
    {
      intro h,
      cases h with y h2,
      cases h2 with h3 h4,
      cases h3 with a h5,
      rw ordered_pair_equality at h5,
      cases h5 with h6 h7,
      rw h6 at *,
      rw h7 at *,
      rw identity_definition at h4,
      cases h4 with x h8,
      use x,
      exact h8,
    },
    {
      intro h,
      cases h with p h2,
      use id,
      split,
      {
        use x,
      },
      {
        rw identity_definition,
        use p,
        exact h2,
      }
    }
  end

lemma nfFUNC: ∀ (n:M), n ∈ ℕℕ → ∀ (f:M), f ∈ FUNC → Rel f → ((Ap n f) ∈ FUNC ∧ Rel (Ap n f) ):=
  begin
    have base: ChurchZero ∈ Z_nfFUNC M:=
      begin
        rw Z_nfFUNC_members,
        split,
        {
          exact zeroN M,   
        },     
        {
          intros f hf hrel,
          rw FUNC_members,
          repeat {split},
          {
            intros x y z h2 h3,
            rw Ap_members at h2,
            rw Ap_members at h3,
            cases h2 with p h4,
            cases h3 with q h5,
            rw ChurchZero_definition at h4,
            rw ChurchZero_definition at h5,
            cases h4 with h6 h7,
            cases h5 with h8 h9,
            cases h6 with a h10,
            cases h8 with b h11,
            rw ordered_pair_equality at h10 h11,
            cases h11 with h12 h13,
            cases h10 with h14 h15,
            rw h13 at *,
            rw h15 at *,
            rw identity_definition at h9 h7,
            cases h7 with a h16,
            cases h9 with b h17,
            rw ordered_pair_equality at h16 h17,
            rw h16.right,
            rw h17.right,
            rw← h17.left,
            rw← h16.left,
          },
          {
            rw ApZero,
            rw Rel_definition,
            intros z hz,
            rw identity_definition at hz,
            cases hz with x h3,
            use x, use x,
            exact h3,
          }
        }
      end,
    have step: ∀ (n:M), n ∈ Z_nfFUNC M → S n ∈ Z_nfFUNC M:=
      assume n,
      begin
        intro h,
        rw Z_nfFUNC_members at h,
        rw Z_nfFUNC_members,
        cases h with h2 h3,
        split,
        {
          exact successorN M n h2,
        },
        { 
          intros f hf hrel,
          specialize h3 f,
          rw FUNC_members,
          split,
          {
            intros x y z h10 h11,
            have h12:= Churchnumbersarefunctions M n h2,
            have h13:=  ChurchSuccessor2 M n f hf h12,
            have h14:= (h13 x y).mp h10,
            have h15:= (h13 x z).mp h11,
            cases h14 with t h16,
            cases h16 with q h17,
            rcases h17 with ⟨ h18, h19, h20, h21⟩,
            cases h15 with t2 h22,
            cases h22 with q2 h23,
            rcases h23 with ⟨ h24, h25, h26, h27⟩,
            rw FUNC_members at h12,
            have h30:= h12 f t t2 h19 h25,
            rw← h30 at *,
            rw FUNC_members at h18,
            have h31:= h18 x q q2 h20 h26, 
            rw← h31 at *,
            rw FUNC_members at hf,
            have h32:= hf q y z h21 h27,
            exact h32, 
          },
          {
            have h4:= h3 hf hrel,
            cases h4 with h5 h6,
            have h12:= Churchnumbersarefunctions M n h2,
            have h13:=  ChurchSuccessor4 M f n h12 hf,
            cases h13 with y h14,
            cases h14 with h15 h16, 
            rw Rel_definition,
            intros z h8,
            have h9:= Churchnumbersarerelations M n h2,
            have h10:= szf_relation M n f h12 hf h9 hrel,
            rw Rel_definition at h10,
            have h11:= h10 z h8,
            exact h11, 
          }
        }
      end,
    intros n h, 
    rw N_members at h, 
    specialize h ( Z_nfFUNC M),
    have h3:= h (and.intro base  step), 
    rw ( Z_nfFUNC_members M) at h3, 
    exact h3.right,
  end 

lemma iteration: ∀ (n:M), n ∈ ℕℕ → ∀ (X f:M), f ∈ FUNC → Rel f →  maps M f X X→ maps M (Ap n f) X X ∧  ‹ f,Ap n f ›  ∈ n:=
  begin
    have base: ChurchZero ∈ Z_iteration M:=
      begin
        rw Z_iteration_members,
        split,
        {
          exact zeroN M,
        },
        {
          intros X f hf hrel h,
          unfold maps at *,
          rcases h with ⟨ h3, h4, h5, h6⟩,
          repeat{split},
          {
            rw Rel_definition,
            intro z,
            rw Ap_members,
            intro h,
            cases h with y h10,
            cases h10 with h11 h12,
            rw ChurchZero_definition at h11,
            cases h11 with p h12,
            rw ordered_pair_equality at h12,
            cases h12 with h13 h14,
            rw← h13 at *,
            rw h14 at *,
            rw identity_definition at h12,
            cases h12 with x h15,
            rw h15 at *,
            use x, use x,
          },
          {
            intros x y,
            intro h,
            cases h with h8 h9,
            rw ApZero at h9,
            rw identity_definition at h9,
            cases h9 with t h10,
            rw ordered_pair_equality at h10,
            cases h10 with h11 h12,
            rw h11 at *,
            rw h12 at *,
            exact h8,
          },
          {
            intros x y z h,
            rcases h with ⟨ h8, h9, h10⟩, 
            rw ApZero at h9 h10,
            rw identity_definition at h9 h10,
            cases h10 with t h11,
            cases h9 with s h12,
            rw ordered_pair_equality at h11 h12,
            cases h11 with h13 h14,
            cases h12 with h15 h16,
            rw h13 at *,
            rw h14 at *,
            rw h16 at *,
            symmetry,
            exact h15,
          },
          {
            intros x h,
            use x,
            rw ApZero,
            rw identity_definition,
            split,
            {
              exact h,
            },
            {
              use x,
            }
          },
          {
            have h8:= ApZero M f,
            rw h8,
            rw ChurchZero_definition,
            use f,
          }
        }
      end,
    have step: ∀ (n:M), n ∈ Z_iteration M → S n ∈ Z_iteration M:=
      begin
        intros n h,
        rw Z_iteration_members at h,
        cases h with h2 h3,
        rw Z_iteration_members,
        split,
        {
          exact successorN M n h2,
        },
        {
          intros X f hf hrel h,
          have h4:= h3 X f hf hrel h,
          unfold maps at h4, 
          cases h4 with h44 h45,
          rcases h44 with ⟨ h5,h6,h7,h8⟩, 
          unfold maps,
          repeat{split},
          { 
            rw Rel_definition,
            intros z h9,
            rw Rel_definition at h5,
            rw Ap_members at h9,
            cases h9 with y h10,
            have h11:= Churchnumbersarefunctions M n h2,
            have h12:= ChurchSuccessor2 M n f hf h11,
            have h13:= successorN M n h2,
            have h14:= Churchnumbersarefunctions M (S n) h13,
            have h15:= nfFUNC M (S n) h13 f hf,
            cases h10 with h16 h17,
            have h18:= Apdef M (S n) h14 f y h16, 
            rw← h18 at h15,
            rw FUNC_members at h15,
            have h19:= Churchnumbersarerelations M (S n) h13,
            have h20:= ChurchSuccessor3 M n f hf h11,
            rw← h18 at h20,
            rw Rel_definition at h20,
            exact h20 z h17,
          },
          { 
            intros x y h10,
            cases h10 with h11 h12,
            rw Ap_members at h12,
            cases h12 with p h13,
            cases h13 with h14 h15,
            have h16:= Churchnumbersarefunctions M n h2,
            have h17:= ChurchSuccessor2 M n f hf h16, 
            have h18:= successorN M n h2,
            have h19:= Churchnumbersarefunctions M (S n) h18,
            have h20:= Apdef M (S n) h19 f p h14,
            have h21:= h17 x y,
            rw←  h20 at h21,
            have h40:= h15,
            rw h21 at h15,
            cases h15 with t h22,
            cases h22 with q h23,
            rcases h23 with ⟨ h24, h25, h26,h27⟩, 
            unfold maps at h,
            rcases h with ⟨ h28, h29, h30, h31⟩, 
            have h32:= h29 q y,
            have h33:= h8 x h11,
            cases h33 with y2 h34,
            cases h34 with h35 h36, 
            have h37:= h7 x y y2,
            rw Ap_members at h36,
            cases h36 with t2 h37,
            cases h37 with h38 h39,
            have h41:= (FUNC_members M n).mp h16 f t t2 h25 h38,
            rw← h41 at *,
            have h42:= (FUNC_members M t).mp h24 x q y2 h26 h39,
            rw← h42 at *,
            have h43:= h29 q y,
            have h44:= h43 ⟨ h35, h27⟩,
            exact h44,
          },
          { 
            have h10:= successorN M n h2,
            have h9:= nfFUNC M (S n) h10 f hf,
            rw FUNC_members at h9,
            intros x y z h20,
            rcases h20 with ⟨ h21, h22, h23⟩, 
            have h40:= h9 hrel,
            have h24:= h40.left x y z h22 h23,
            exact h24,  
          },
          { 
            intros x h9,
            have h10:= h8 x h9,
            cases h10 with y h11,
            cases h11 with h12 h13,
            use (Ap f y),
            unfold maps at h,
            rcases h with ⟨ h110, h111, h112, h113⟩,
            have h114:= h111 y (Ap f y),
            split,
            { 
              apply h114,
              split,
              {
                exact h12,
              },
              {
                have h115:= h113 y h12, 
                cases h115 with q h116,
                have h117:= Apdef M f hf,
                cases h116 with h118 h119,
                have h120:= h117 y q h119,
                rw h120 at *,
                exact h119,
              }
            },
            { 
              have h21:= Churchnumbersarefunctions M n h2,
              have h22:= ChurchSuccessor2 M n f hf h21,
              specialize h22 x (Ap f y), 
              rw h22,
              use (Ap n f), use y,
              repeat{split},
              {
                have h30:= nfFUNC M n h2 f hf hrel,
                exact h30.left,
              },
              {
                exact h45,
              },
              {
                exact h13,
              },
              {
                have h30:= h113 y h12,
                cases h30 with p h31,
                cases h31 with h32 h33,
                have h34:= Apdef M f hf y p h33,
                rw h34 at h33,
                exact h33,
              }
            }
          },
          {
            have h20:= Churchnumbersarefunctions M n h2, 
            have h21:= sfunction2 M n,
            have h22:= srelation2 M n,
            have h23:= ChurchSuccessor2 M n f hf h20,
            have h24:= ChurchSuccessor4 M f n h20 hf,
            cases h24 with y h25, 
            cases h25 with h26 h27,
            have h27:= Apdef M (S n) h21 f y h26,
            rw← h27,
            exact h26,
          }
        }
      end,
    intros n hn,
    rw N_members at hn,
    specialize hn (Z_iteration M),
    have h3:= hn (and.intro base step),
    rw Z_iteration_members at h3,
    intros X f hf h4,
    cases h3 with h5 h6,
    have h7:= h6 X f hf h4,
    exact h7,
  end

lemma nf_defined: ∀ (n:M), n ∈ ℕℕ → ∀ (f:M), f ∈ FUNC → ∃ (y:M), ‹ f,y› ∈ n ∧ Rel y :=
  begin
    have base: ChurchZero ∈ Z_nf_defined M:=
      begin
        rw Z_nf_defined_members,
        split,
        {
          exact zeroN M,
        },
        {
          intros f hf,
          simp_rw ChurchZero_definition,
          use id, use f,
          rw Rel_definition,
          intros z h,
          rw identity_definition at h,
          cases h with x h2,
          use x, use x,
          exact h2,
        }
      end,
    have step: ∀ (n:M), n ∈ Z_nf_defined M → S n ∈ Z_nf_defined M:=
      assume n,
      begin
        intro h,
        rw Z_nf_defined_members at h,
        rw Z_nf_defined_members,
        cases h with h2 h3,
        split,
        {
          exact successorN M n h2,
        },
        {
          intros f hf,
          have h4:= Churchnumbersarefunctions M n h2,
          have h5:= ChurchSuccessor4 M f n h4 hf,
          exact h5,
        }
      end,
    intros n hn,
    rw N_members at hn,
    specialize hn (Z_nf_defined M),
    have h3:= hn (and.intro base step),
    rw Z_nf_defined_members at h3,
    exact h3.right,
  end

theorem successorequation: ∀ (X f:M), f ∈ FUNC → Rel f → maps M f X X → ∀ (n x:M), n ∈ ℕℕ → x ∈ X→ 
Ap( Ap (S n) f) x = Ap f (Ap (Ap n f) x):=
  assume X f,
  begin
    intros hf hrel h2f n x hn hx,
    have h0:= zeroFUNC M,
    have h2:= nfFUNC M n hn f hf,
    have h12:= Churchnumbersarefunctions M n hn,
    have h13:=  ChurchSuccessor2 M n f hf h12,
    rw full_extensionality,
    intro u,
    rw Ap_members,
    rw Ap_members,
    split,
    {
      intro h,
      cases h with y h20,
      cases h20 with h21 h22,
      have h14:= (h13 x y).mp h21,
      cases h14 with t h23,
      cases h23 with q h24,
      rcases h24 with ⟨ h25, h26, h27, h28⟩,
      use y,
      rw and_comm,
      split,
      {
        exact h22,
      },
      {
        have h30:= Apdef M n h12 f t h26,
        rw← h30,
        have h31:= Apdef M f hf q y h28,
        have h32:= Apdef M t h25 x q h27,
        rw← h32,
        exact h28,
      }
    },
    {
      intro h,
      cases h with y h40,
      cases h40 with h41 h42,
      use y,
      rw and_comm,
      split,
      {
        exact h42,
      },
      {
        specialize h13 x y,
        rw h13,
        use (Ap n f), use (Ap (Ap n f) x),
        repeat{split},
        {
          have h50:= nfFUNC M n hn f hf hrel,
          exact h50.left,
        },
        {
          have h14:= nf_defined M n hn f hf,
          cases h14 with y h15,
          have h16:= Apdef M n h12 f y h15.left, 
          rw h16 at *,
          exact h15.left, 
        },
        {
          rw Ap_members,
          have h14:= nf_defined M n hn f hf,
          cases h14 with y2 h15,
          use y2,
          split,
          { 
            exact h15.left,
          },
          { 
            have h16:= Apdef M n h12 f y2 h15.left,
            rw← h16 at *,
            have h17:= Apdef M y2 ((h2 hrel).left), 
            have h18:= iteration M n hn X f hf hrel h2f,
            unfold maps at h18,
            cases h18 with h19 h200,
            cases h19 with h201 h20, 
            rcases h20 with ⟨ h21, h22, h23⟩,
            have h24:= h23 x hx,
            cases h24 with p h25,
            cases h25 with h26 h27,
            rw← h16 at *,
            have h28:= Apdef M y2 (h2 hrel).left x p h27, 
            rw h28 at *, 
            exact h27,
          }
        },
        {
          exact h41,
        }
      }
    }
  end

lemma idFUNC: (id:M) ∈ FUNC:=
  begin
    rw FUNC_members,
    intros x y z h h2,
    rw identity_definition at h,
    rw identity_definition at h2,
    cases h with p h3,
    cases h2 with q h4,
    rw ordered_pair_equality at h3,
    rw ordered_pair_equality at h4,
    cases h3 with h5 h6,
    cases h4 with h7 h8,
    rw h6, 
    rw h8,
    rw← h5,
    rw← h7,
  end


lemma Church1notequal0: ¬ S (ChurchZero:M) = ChurchZero:=
  begin
    intro h,
    have h2:= zeroN M,
    have h6: ∀ (z f x w:M), f ∈ FUNC → z ∈ FUNC → Rel f → Rel z → 
      (‹ x,w› ∈ Ap( S z) f ↔ 
      ∃(t q:M), t ∈ FUNC ∧ ‹ f,t› ∈ z ∧ ‹ x,q› ∈ t ∧ ‹ q,w› ∈ f):=
      assume z f x w,
      begin
        intros hf hz hrelf hrelz, 
        have h4:= ChurchSuccessor3 M z f hf hz,
        have h5:= ChurchSuccessor2 M z f hf hz x w,
        split,
        {
          intro h3,    
          rw h5 at h3,
          exact h3,
        },
        {
          intro h7,
          rw← h5 at h7,
          exact h7,
        }
      end,
    specialize h6 ChurchZero,
    have h7:= Churchnumbersarefunctions M ChurchZero (zeroN M),
    have h7rel:= Churchnumbersarerelations M ChurchZero (zeroN M),
    have h8: ∀ (f x w:M), f ∈ FUNC → Rel f → (‹ x,w › ∈ Ap(S ChurchZero) f ↔ ‹ x,w › ∈ f):=
      assume f x w,
      begin 
        intros hf hrelf,
        have h9:= h6 f x w hf h7 hrelf h7rel, 
        split,
        {
          intro h10,
          rw h9 at h10,
          cases h10 with t h11,
          cases h11 with q h12,
          rcases h12 with ⟨ h13,h14, h15,h16⟩,
          have h17:= Apdef M f hf q w h16,
          rw ChurchZero_definition at h14,
          cases h14 with g h18, 
          rw ordered_pair_equality at h18,
          cases h18 with h19 h20,
          rw ← h19 at *,
          rw h20 at *,
          rw identity_definition at h15,
          cases h15 with p h21,
          rw ordered_pair_equality at h21,
          rw h21.left at *,
          rw h21.right at *,
          exact h16,
        },
        {
          intro h10,
          rw h9,
          use id, use x,
          repeat{split},
          {
            exact idFUNC M,
          },
          {
            rw ChurchZero_definition,
            use f,
          },
          {
            rw identity_definition,
            use x,
          },
          {
            exact h10,
          }
        }  
      end,
    have hcopy := h,
    rw full_extensionality at h,
    have h18:= Churchnumbersarerelations M (S ChurchZero) (successorN M ChurchZero h2),
    rw Rel_definition at h7rel h18,
    have h20: ∀(u f:M), f ∈ FUNC → Rel f → ( u ∈ Ap (S ChurchZero) f ↔ u ∈ f):=
      assume u f,
      begin
        intros hf hrelf,
        have h17:= successorN M ChurchZero h2,
        have h21:= Churchnumbersarefunctions M  (S ChurchZero) h17,
        have h22:= ChurchSuccessor4 M f ChurchZero h7 hf,
        cases h22 with y h23,
        cases h23 with h33 h34, 
        have h24:= Apdef M (S ChurchZero) h21 f y h33,
        have h25:= Churchnumbersarerelations M  (S ChurchZero) h17,
        have h26: Rel (Ap (S ChurchZero) f):=
          begin
            rw Rel_definition,
            intros z h27,
            rw Ap_members at h27,
            cases h27 with y2 h28,
            cases h28 with h29 h30,
            rw full_extensionality at h24,
            specialize h24 z,
            rw FUNC_members at h21,
            have h31:= h21 f y y2 h33 h29,
            rw← h31 at *,
            rw Rel_definition at h34,
            have h35:= h34 z h30,
            exact h35,
          end,
        have h40:= hrelf, 
        rw Rel_definition at hrelf,
        rw Rel_definition at h26,
        split,
        {
          intro h27,
          have h28:= h26 u h27,
          cases h28 with a h29,
          cases h29 with b h30,
          rw h30 at *,
          have h31:= h8 f a b hf h40,
          rw h31 at h27,
          exact h27,
        },
        {
          intro h27,
          have h28:= hrelf u h27,
          cases h28 with a h29,
          cases h29 with b h30, 
          rw h30 at *,
          have h31:= h8 f a b hf h40,
          rw←  h31 at h27,
          exact h27,
        }
      end,
    have h21: ∀ (f:M), f ∈ FUNC → Rel f → Ap (S ChurchZero) f = f:=
      assume f,
      begin
        intros hf hrelf,
        rw full_extensionality,
        intro u,
        exact h20 u f hf hrelf, 
      end,
    have h22:= Churchnumbersarerelations M ChurchZero (zeroN M),
    have h23:=  λ (f:M), ApZero M f,
    set f:= single ‹ (Λ:M) , single Λ › with h24,
    have h25: Rel f:=
      begin
        rw Rel_definition,
        intros z,
        rw h24,
        rw singleton1, 
        intro h26,
        use Λ, use single Λ,
        exact h26,
      end,
    have h26: f ∈ FUNC:=
      begin
        rw FUNC_members,
        intros x y z hy hz,
        rw h24 at hy hz,
        rw singleton1 at hy hz,
        rw ordered_pair_equality at hy hz,
        rw hz.right,
        rw hy.right,
      end,
    have h27:= h21 f h26 h25,
    have h28:= h23 f,
    rw hcopy at h27,
    rw h27 at h28,
    rw h24 at h28,
    rw full_extensionality at h28,
    have h29:= h28 ‹ Λ, single Λ›,
    rw singleton1 at h29,
    simp at h29,
    rw identity_definition at h29,
    cases h29 with x h30,
    rw ordered_pair_equality at h30,
    cases h30 with h31 h32,
    rw← h31 at h32,
    rw full_extensionality at h32,
    specialize h32 Λ,
    rw singleton1 at h32,
    simp at h32,
    have h33:= emptyset_axiom Λ,
    contradiction,
  end

theorem successoromitszero: ∀ (x:M), x ∈ ℕℕ → ¬ (S x = ChurchZero):=
  begin
    set a:= S ChurchZero  with ha,
    set b:=   ChurchZero with hb,
    have h3: ¬ a = b:= 
      begin
        rw [ha, hb],
        exact Church1notequal0 M,
      end,
    set f:= 𝕍 × (single a) with hf,
    have h4: Rel f:=
      begin
        rw Rel_definition,
        intros t ht,
        rw hf at ht,
        rw product_axiom at ht,
        cases ht with p h5,
        cases h5 with q h6,
        rcases h6 with ⟨ h7,h8, h9⟩,
        use p, use q,
        exact h9,
      end,
    have h5: f ∈ FUNC:=
      begin
        rw FUNC_members,
        intros x y z hy hz,
        rw hf at hy hz,
        rw product_axiom at hy hz,
        cases hz with p h6,
        cases h6 with q h7,
        rcases h7 with ⟨ h8, h9, h10⟩,
        rw ordered_pair_equality at h10,
        rw← h10.left at *,
        rw← h10.right at *,
        rw singleton1 at h9,
        rw h9 at *,
        cases hy with s h12,
        cases h12 with t h13,
        rcases h13 with ⟨ h14, h15, h16⟩, 
        rw ordered_pair_equality at h16,
        rw←  h16.left at *,
        rw←  h16.right at *,
        rw singleton1 at h15,
        exact h15,
      end,
    have h10: maps M f ℕℕ ℕℕ:=
      begin
        unfold maps,
        repeat{split},
        {
          exact h4,
        },
        {
          intros x y h,
          cases h with h6 h7,
          rw hf at h7,
          rw product_axiom at h7,
          cases h7 with p h8,
          cases h8 with q h9,
          rw ordered_pair_equality at h9,
          rcases h9 with ⟨ h10, h11, h12, h13⟩, 
          rw← h12 at *,
          rw← h13 at *,
          rw singleton1 at h11,
          rw h11 at *,
          rw ha,
          exact successorN M ChurchZero (zeroN M),
        },
        {
          rw FUNC_members at h5,
          intros x y z h,
          specialize h5 x y z,
          cases h with h6 h7 h8,
          cases h7 with h9 h10,
          exact h5 h9 h10,
        },
        {
          intros x hx,
          use a,
          split,
          {
            rw ha,
            exact successorN M ChurchZero (zeroN M),
          },
          {
            rw hf,
            rw product_axiom,
            use x, use a,
            rw singleton1, 
            simp,
            exact V_definition x,
          }
        }
      end,
    intros z hz h ,
    have h11: Ap (Ap (S z) f) b = Ap (Ap ChurchZero f) b:=
      begin
        rw h,
      end,
    have h12:= successorequation M ℕℕ f h5 h4 h10 z b hz,
    rw hb at h12,
    have h13:= h12 (zeroN M),
    rw h11 at h13,
    rw ApZero at h13,
    have h14: Ap (id:M) b = b:=
      begin
        rw full_extensionality,
        intro t,
        rw Ap_members,
        split,
        {
          intro h20,
          cases h20 with c h21,
          rw identity_definition at h21,
          cases h21 with h22 h23,
          cases h22 with x h24,
          rw ordered_pair_equality at h24,
          rw h24.left at *,
          rw h24.right at *,
          exact h23,
        },
        {
          intro h20,
          use b,
          rw identity_definition,
          split,
          {
            use b,
          },
          {
            exact h20,
          }
        }
      end,
    rw h14 at h13,
    have h15: ∀ (x:M), Ap f x = a:=
      begin
        intros x,
        rw hf,
        rw full_extensionality,
        intro t,
        rw Ap_members,
        split,
        {
          intros h20,
          cases h20 with y h21,
          cases h21 with h22 h23,
          rw product_axiom at h22,
          cases h22 with p h24,
          cases h24 with q h25,
          rcases h25 with ⟨ h26, h27, h28⟩,
          rw ordered_pair_equality at h28,
          cases h28 with h29 h30,
          rw← h29 at *,
          rw← h30 at *,
          rw singleton1 at h27,
          rw h27 at *,
          exact h23,
        },
        {
          intro h20,
          use a,
          split,
          {
            rw product_axiom,
            use x, use a,
            rw singleton1,
            simp,
            exact V_definition x,
          },
          {
            exact h20,
          }
        }
      end,
    specialize h15 (Ap (Ap z f) ChurchZero),
    rw h15 at h13,
    rw sym at h13,
    contradiction,
  end 

lemma predecessor:∀ (x:M), x ∈ ℕℕ →  ¬ x = ChurchZero → ∃ (y:M), y ∈ ℕℕ ∧ S y = x:=
  begin
    have base: ChurchZero ∈ Z_predecessor M:=
      begin
        rw Z_predecessor_members,
        split,
        {
          exact zeroN M,
        },
        {
          intro h,
          contradiction,
        }
      end,
    have step: ∀ (x:M), x ∈ Z_predecessor M → S x ∈ Z_predecessor M:=
      begin
        intros x h,
        rw Z_predecessor_members at h,
        rw Z_predecessor_members,
        cases h with h2 h3,
        split,
        {
          exact successorN M x h2,
        },
        {
          intro h4,
          use x,
          simp,
          exact h2,
        }
      end,
    intros n hn,
    rw N_members at hn,
    specialize hn (Z_predecessor M),
    have h3:= hn (and.intro base step),
    rw Z_predecessor_members at h3,
    exact h3.right,
  end

lemma decidable0: ∀ (n:M), n ∈ ℕℕ → n = ChurchZero ∨ ¬ n = ChurchZero:=
  begin
    have base: ChurchZero ∈ Z_decidable0 M:=
      begin
        rw Z_decidable0_members,
        split,
        {
          exact zeroN M,
        },
        {
          left,
          refl,
        }
      end,
    have step: ∀ (n:M), n ∈ Z_decidable0 M → S n ∈ Z_decidable0 M:=
      begin
        intros n h,
        rw Z_decidable0_members at h,
        rw Z_decidable0_members,
        cases h with h2 h3,
        split,
        { 
          exact successorN M n h2,
        },
        {
          right,
          exact successoromitszero M n h2,
        }
      end,
    intros n hn,
    rw N_members at hn,
    specialize hn (Z_decidable0 M),
    have h3:= hn (and.intro base step),
    rw Z_decidable0_members at h3,
    exact h3.right,
  end 

lemma zeroplusx: ∀ (x:M), x ∈ ℕℕ → ChurchZero ⊕ x = x:=
  begin
    have base: ChurchZero ∈ Z_zeroplusx M:=
      begin
        rw Z_zeroplusx_members,
        split,
        {
          exact zeroN M,
        },
        {
          rw ChurchZero_equation,
          exact zeroN M,
        }
      end,
    have step: ∀ (x:M), x ∈ Z_zeroplusx M → S x ∈ Z_zeroplusx M:=
      begin
        intros x h,
        rw Z_zeroplusx_members at h,
        rw Z_zeroplusx_members,
        cases h with h2 h3,
        split,
        {
          exact successorN M x h2,
        },
        {
          rw ChurchAddition_equation ChurchZero x (zeroN M) h2,
          rw h3,
        }
      end,
    intros n hn,
    rw N_members at hn,
    specialize hn (Z_zeroplusx M),
    have h3:= hn (and.intro base step),
    rw Z_zeroplusx_members at h3,
    exact h3.right,
  end 

lemma ChurchAdditionMaps: ∀ (y:M), y ∈ ℕℕ → ∀ (x:M), x ∈ ℕℕ → x ⊕ y ∈ ℕℕ:=
  begin
    have base: ChurchZero ∈ Z_ChurchAdditionMaps M:=
      begin
        rw Z_ChurchAdditionMaps_members,
        split,
        {
          exact zeroN M,
        },
        {
          intros x hx,
          rw ChurchZero_equation x hx,
          exact hx,
        }
      end,
    have step: ∀ (y:M), y ∈ Z_ChurchAdditionMaps M → S y ∈ Z_ChurchAdditionMaps M:=
      assume y,
      begin
        rw Z_ChurchAdditionMaps_members,
        intro h,
        cases h with h2 h3,
        rw Z_ChurchAdditionMaps_members,
        split,
        {
          exact successorN M y h2,
        },
        {
          intros x hx,
          have h4:= h3 x hx,
          rw ChurchAddition_equation x y hx h2,
          exact successorN M (x ⊕ y) h4,
        }
      end,
     intros n hn,
    rw N_members at hn,
    specialize hn (Z_ChurchAdditionMaps M),
    have h3:= hn (and.intro base step),
    rw Z_ChurchAdditionMaps_members at h3,
    exact h3.right,
  end

lemma ChurchSuccessorShift: ∀ (n:M), n ∈ ℕℕ →  ∀(x:M), x ∈ ℕℕ → x ⊕ S n = (S x) ⊕ n:=
  begin
    have base: ChurchZero ∈ Z_ChurchSuccessorShift M:=
      begin
        rw Z_ChurchSuccessorShift_members,
        split,
        {
          exact zeroN M,
        },
        {
          intros x hx,
          rw ChurchAddition_equation x ChurchZero hx (zeroN M), 
          rw ChurchZero_equation x hx,
          rw ChurchZero_equation (S x) (successorN M x hx),
        }
      end,
    have step: ∀ (n:M), n ∈ Z_ChurchSuccessorShift M → S n ∈ Z_ChurchSuccessorShift M:=
      assume n,
      begin
        intro h,
        rw Z_ChurchSuccessorShift_members at h,
        rw Z_ChurchSuccessorShift_members,
        cases h with h2 h3,
        split,
        {
          exact (successorN M n h2),
        },
        {
          intros x h4,
          rw ChurchAddition_equation x (S n) h4 (successorN M n h2),
          rw h3 x h4,
          rw ChurchAddition_equation (S x) n (successorN M x h4) h2,
        }
      end,
    intros n hn,
    rw N_members at hn,
    specialize hn (Z_ChurchSuccessorShift M),
    have h3:= hn (and.intro base step),
    rw Z_ChurchSuccessorShift_members at h3,
    exact h3.right,
  end 

lemma ChurchAdditionAssociative: ∀ (y:M), y ∈ ℕℕ →  ∀ (x z:M), x ∈ ℕℕ → z ∈ ℕℕ → (x⊕y)⊕z = x ⊕ (y⊕z):=
  begin
    have base: ChurchZero ∈ Z_ChurchAdditionAssociative M:=
      begin
        rw Z_ChurchAdditionAssociative_members,
        split,
        {
          exact zeroN M,
        },
        {
          intros x z hx hz,
          rw ChurchZero_equation,
          rw zeroplusx M z hz,
          exact hx,
        }
      end,
    have step: ∀(y:M), y ∈ Z_ChurchAdditionAssociative M → S y ∈ Z_ChurchAdditionAssociative M:=
      begin
        intros y h,
        rw Z_ChurchAdditionAssociative_members at h,
        rw Z_ChurchAdditionAssociative_members,
        cases h with h2 h3,
        split,
        {
          exact successorN M y h2,
        },
        intros x z hx hz,
        rw ChurchAddition_equation x y hx h2,
        have h4:= ChurchAdditionMaps M y h2 x hx,
        have h5:= ChurchSuccessorShift M z hz (x ⊕ y) h4,
        rw← h5,
        have h6:= ChurchAddition_equation (x ⊕ y) z h4 hz,
        rw h6,
        rw h3 x z hx hz,
        have h7:= ChurchAdditionMaps M z hz y h2,
        have h8:= ChurchAddition_equation  x (y ⊕ z) hx h7,
        rw← h8,
        rw← ChurchAddition_equation y z h2 hz,
        have h9:= ChurchSuccessorShift M z hz y h2,
        rw← h9, 
      end,
    intros n hn,
    rw N_members at hn,
    specialize hn (Z_ChurchAdditionAssociative M),
    have h3:= hn (and.intro base step),
    rw Z_ChurchAdditionAssociative_members at h3,
    exact h3.right, 
  end

lemma ChurchAdditionCommutative: ∀ (y:M), y ∈ ℕℕ → ∀ (x:M), x ∈ ℕℕ →  x ⊕ y = y⊕ x:=
  begin
    have base: ChurchZero ∈ Z_ChurchAdditionCommutative M:=
      begin
        rw Z_ChurchAdditionCommutative_members,
        split,
        {
          exact zeroN M,
        },
        {
          intros x hx,
          rw ChurchZero_equation x hx,
          rw zeroplusx,
          exact hx,
        }
      end,
    have step: ∀ (y:M), y ∈ Z_ChurchAdditionCommutative M → S y ∈ Z_ChurchAdditionCommutative M:=
      begin
        intros y h,
        rw Z_ChurchAdditionCommutative_members at h,
        rw Z_ChurchAdditionCommutative_members,
        cases h with hy h3,
        split,
        {
          exact successorN M y hy,
        },
        {
          intros x hx,
          have h4:= h3 x hx,
          rw←  ChurchSuccessorShift M x hx y hy, 
          rw  ChurchAddition_equation x y hx hy,
          rw ChurchAddition_equation y x hy hx,
          rw h4,
        }
      end,
    intros n hn,
    rw N_members at hn,
    specialize hn (Z_ChurchAdditionCommutative M),
    have h3:= hn (and.intro base step),
    rw Z_ChurchAdditionCommutative_members at h3,
    exact h3.right, 
  end

lemma ApId: ∀ (x:M), Ap (id:M) x = x:=
  assume x,
  begin
    have h2:= idFUNC M,
    have h3:= Apdef M id h2 x x,
    rw identity_definition at h3,
    symmetry,
    apply h3,
    use x,
  end

lemma ApOne: ∀ (f:M),   f ∈ FUNC → Rel f   → Ap (S ChurchZero) f = f:=
  assume f,
  begin
    intros hf  hrel,
    have h2:= Churchnumbersarefunctions M ChurchZero (zeroN M),
    have h3:= ChurchSuccessor2 M ChurchZero f hf h2,
    rw full_extensionality,
    intro u,
    rw Rel_definition at hrel,
    have h4:= Apdef M f hf,
    have h5:= successorN M ChurchZero (zeroN M),
    have h6:= Churchnumbersarerelations M (S ChurchZero) h5,
    have h7: ∀ (t:M), ‹ f,t ›∈ ChurchZero ↔ t = id:=
      begin
        intro t,
        rw ChurchZero_definition, 
        split,
        {
          intro h8,
          cases h8 with p h9,
          rw ordered_pair_equality at h9,
          cases h9 with h10 h11,
          exact h11,
        },
        {
          intro h7,
          rw h7 at *,
          use f,
        }
      end,
    have h20: ∀ (x w:M), ‹ x,w ›  ∈ Ap (S ChurchZero) f ↔ ‹x,w› ∈ f:=
      assume x w,
      begin
        rw h3 x w,
        split,
        {
          intro h8,
          cases h8 with t h9,
          cases h9 with q h10,
          rcases h10 with ⟨ h11, h12, h13, h14 ⟩,
          rw h7 t at h12,
          rw h12 at *,
          rw identity_definition at h13,
          cases h13 with p h14,
          rw ordered_pair_equality at h14,
          cases h14 with h15 h16,
          rw h15 at *,
          rw h16 at *,
          exact h14, 
        },
        {
          intro h8,
          use id, use x,
          repeat{split},
          {
            exact idFUNC M,
          },
          {
            rw ChurchZero_definition ‹ f, id ›, 
            use f,
          },
          {
            rw identity_definition,
            use x,
          },
          {
            exact h8,
          }
        }
      end,
    have h21:= ChurchSuccessor3 M ChurchZero f hf h2,
    rw Rel_definition at h21,
    specialize h21 u,
    specialize hrel u,
    split,
    {
      intro h22,
      have h23:= h21 h22,
      cases h23 with a h24,
      cases h24 with b h25,
      rw h25 at *,
      specialize h20 a b,
      rw h20 at h22,
      exact h22,
    },
    {
      intro h23,
      have h24:= hrel h23,
      cases h24 with a h25,
      cases h25 with b h26,
      rw h26 at *,
      specialize h20 a b,
      rw h20,
      exact h23,
    }  
  end 

lemma iterationFUNC: ∀ (n:M), n ∈ ℕℕ → ∀ (f X  :M), maps M f X X → f ∈ FUNC → Rel f → dom f ⊆ X → ¬ n = ChurchZero → dom (Ap n f) ⊆ X:=
  begin
    have base: ChurchZero ∈ Z_iterationFUNC M:=
      begin
        rw Z_iterationFUNC_members,
        split,
        {
          exact zeroN M,
        },
        {
          intros f X hf hfunc hrel hdom h4,
          contradiction,
        }
      end,
    have step: ∀ (n:M), n ∈ Z_iterationFUNC M → S n ∈ Z_iterationFUNC M:=
      begin
        intros n h,
        rw Z_iterationFUNC_members at h,
        rw Z_iterationFUNC_members,
        cases h with hn h3,
        split,
        {
          exact successorN M n hn,
        },
        {
          intros f X hmaps hfunc hrel hdom h4,
          have h5:= h3 f X hmaps hfunc hrel hdom,
          have h6:= decidable0 M n hn,
          cases h6 with h7 h8,
          { 
            rw h7 at *,
            rw subset_definition,
            intros x h8,
            have h9:= ApOne M f hfunc hrel,
            rw h9 at *,
            have h10:= member_subset M (dom f) X x hdom h8,
            exact h10,
          },
          { 
            have h9:= h5 h8,
            have h10:= nfFUNC M n hn f hfunc hrel,
            cases h10 with h11 h12,
            have h13:= successorN M n hn,
            have h14:= nfFUNC M (S n) h13 f hfunc hrel,
            cases h14 with h15 h16,
            rw subset_definition,
            intros x h17,
            rw domain_axiom (Ap (S n) f) h16 at h17,
            cases h17 with y h18,
            have h19:= Apdef M (Ap (S n) f) h15 x y h18,
            have h20:= Churchnumbersarefunctions M n hn,
            have h21:= ChurchSuccessor2 M n f hfunc h20 x y,
            rw h21 at h18,
            cases h18 with t h22,
            cases h22 with q h23,
            rcases h23 with ⟨ h24, h25, h26, h27⟩, 
            have h28: t = Ap n f:= Apdef M n h20 f t h25,
            have h29:= Apdef M f hfunc q y h27,
            have h30: x ∈ dom (Ap n f):=
              begin
                rw domain_axiom (Ap n f) h12,
                use q,
                rw h28 at h26,
                exact h26,
              end,  
            have h31:= h5 h8,
            have h32:= member_subset M (dom (Ap n f)) X x h31 h30,
            exact h32,
          }
        }
      end,
    intros n hn,
    rw N_members at hn,
    specialize hn (Z_iterationFUNC M),
    have h3:= hn (and.intro base step),
    rw Z_iterationFUNC_members at h3,
    exact h3.right, 
  end

lemma iterationRel: ∀ (n:M), n ∈ ℕℕ → ∀ (f X  :M), maps M f X X → f ∈ FUNC → Rel f → dom f ⊆ X → ¬ n = ChurchZero → Rel (Ap n f) :=
  begin
    have base: ChurchZero ∈ Z_iterationRel M:=
      begin
        rw Z_iterationRel_members,
        split,
        {
          exact zeroN M,
        },
        {
          intros f X hf hfunc hrel hdom h4,
          contradiction,
        }
      end,
    have step: ∀ (n:M), n ∈ Z_iterationRel M → S n ∈ Z_iterationRel M:=
      begin
        intros n h,
        rw Z_iterationRel_members at h,
        rw Z_iterationRel_members,
        cases h with hn h3,
        split,
        {
          exact successorN M n hn,
        },
        {
          intros f X hmaps hfunc hrel hdom h4,
          have h5:= h3 f X hmaps hfunc hrel hdom,
          have h6:= decidable0 M n hn,
          cases h6 with h7 h8,
          { 
            rw h7 at *,
            rw Rel_definition,
            intros z h8,
            have h9:= ApOne M f hfunc hrel,
            rw h9 at *,
            rw Rel_definition at hrel,
            exact hrel z h8,
          },
          { 
            have h9:= h5 h8,
            have h10:= nfFUNC M n hn f hfunc hrel,
            cases h10 with h11 h12,
            have h13:= successorN M n hn,
            have h14:= nfFUNC M (S n) h13 f hfunc hrel,
            cases h14 with h15 h16,
            exact h16,
          }
        }
      end,
    intros n hn,
    rw N_members at hn,
    specialize hn (Z_iterationRel M),
    have h3:= hn (and.intro base step),
    rw Z_iterationRel_members at h3,
    exact h3.right, 
  end

lemma iterationRange: ∀ (n:M), n ∈ ℕℕ → ∀ (f X  :M), maps M f X X → f ∈ FUNC → Rel f → dom f ⊆ X → ¬ n = ChurchZero → range (Ap n f) ⊆ X:=
  begin
    have base: ChurchZero ∈ Z_iterationRange M:=
      begin
        rw Z_iterationRange_members,
        split,
        {
          exact zeroN M,
        },
        {
          intros f X hf hfunc hrel hdom h4,
          contradiction,
        }
      end,
    have step: ∀ (n:M), n ∈ Z_iterationRange M → S n ∈ Z_iterationRange M:=
      begin
        intros n h,
        rw Z_iterationRange_members at h,
        rw Z_iterationRange_members,
        cases h with hn h3,
        split,
        {
          exact successorN M n hn,
        },
        {
          intros f X hmaps hfunc hrel hdom h4,
          have h5:= h3 f X hmaps hfunc hrel hdom,
          have h6:= decidable0 M n hn,
          cases h6 with h7 h8,
          { 
            rw h7 at *,
            rw subset_definition,
            intros y h8,
            have h9:= ApOne M f hfunc hrel,
            rw h9 at *,
            rw range_axiom f hrel at h8,
            cases h8 with x h9,
            rw subset_definition at hdom,
            specialize hdom x,
            have h20: x ∈ dom f:=
              begin
                rw domain_axiom f hrel,
                use y,
                exact h9, 
              end,
            have h21:= hdom h20,
            unfold maps at hmaps,
            rcases hmaps with ⟨ h22, h23, h24, h25⟩, 
            exact h23 x y ⟨ h21, h9⟩, 
          },
          { 
            have h9:= h5 h8,
            have h10:= nfFUNC M n hn f hfunc hrel,
            cases h10 with h11 h12,
            have h13:= successorN M n hn,
            have h14:= nfFUNC M (S n) h13 f hfunc hrel,
            cases h14 with h15 h16,
            rw subset_definition,
            intros y h17,
            rw range_axiom (Ap (S n) f) h16 at h17,
            cases h17 with x h18,
            have h19:= Apdef M (Ap (S n) f) h15 x y h18,
            have h20:= Churchnumbersarefunctions M n hn,
            have h21:= ChurchSuccessor2 M n f hfunc h20 x y,
            rw h21 at h18,
            cases h18 with t h22,
            cases h22 with q h23,
            rcases h23 with ⟨ h24, h25, h26, h27⟩, 
            have h28: t = Ap n f:= Apdef M n h20 f t h25,
            have h29:= Apdef M f hfunc q y h27,
            have h30: range f ⊆ X:=
              begin
                rw subset_definition,
                intros z h31,
                rw range_axiom f hrel at h31,
                cases h31 with p h32,
                unfold maps at hmaps,
                rcases hmaps with ⟨ h33, h34, h35, h36⟩,
                rw subset_definition at hdom,
                specialize hdom p,
                have h37: p ∈ dom f:=
                  begin
                    rw domain_axiom f hrel,
                    use z,
                    exact h32,
                  end,
                have h38:= hdom h37,
                exact h34 p z ⟨ h38, h32⟩, 
              end,  
            have h31:= h5 h8,
            have h32: y ∈ range f:=
              begin
                rw range_axiom f hrel,
                use q,
                exact h27,
              end,
            have h33:= member_subset M (range f) X y h30 h32,
            exact h33,
          }
        }
      end,
    intros n hn,
    rw N_members at hn,
    specialize hn (Z_iterationRange M),
    have h3:= hn (and.intro base step),
    rw Z_iterationRange_members at h3,
    exact h3.right, 
  end

lemma doubleiteration: ∀ (j:M), j ∈ ℕℕ → ∀ (X f ℓ x:M), f ∈ FUNC →  maps M f X X → ℓ ∈ ℕℕ → x ∈ X → 
Ap (Ap j f)(Ap (Ap ℓ f) x) = Ap (Ap (j ⊕ ℓ) f) x:=
  begin
    have base: ChurchZero ∈ Z_doubleiteration M:=
      begin
        rw Z_doubleiteration_members,
        split,
        {
          exact zeroN M,
        },
        {
          intros  X f ℓ x hfunc hf hl hx,
          rw zeroplusx M ℓ hl,
          rw  ApZero M f,
          rw ApId,
        }
      end,
    have step: ∀(j:M), j ∈ Z_doubleiteration M → S j ∈ Z_doubleiteration M:=
      assume j,
      begin
        rw Z_doubleiteration_members,
        rw Z_doubleiteration_members,
        intro h,
        cases h with h2 h3,
        split,
        {
          exact successorN M j h2,
        },
        {
          intros X f ℓ x hfunc hf hl hx,
          have h4:= h3 X f ℓ x hfunc hf hl hx,
          have hfcopy:= hf,
          unfold maps at hf,
          rcases hf with ⟨ h5, h6, h7, h8⟩,
          rw←  ChurchSuccessorShift M ℓ hl j h2, 
          have h11:= ChurchAddition_equation j ℓ h2 hl,
          rw h11,
          have h9:= ChurchAdditionMaps M ℓ hl j h2,
          have h10:= successorequation M X f hfunc h5 hfcopy (j ⊕ ℓ) x h9 hx,
          rw h10,
          rw← h4,
          have h12:= successorequation M X f hfunc h5 hfcopy j (Ap (Ap ℓ f) x) h2,
          apply h12,
          have h13:= iteration M ℓ hl X f hfunc h5 hfcopy,
          cases h13 with h14 h15,
          unfold maps at h14,
          rcases h14 with ⟨ h16, h17, h18, h19⟩, 
          have h20:= h17 x  (Ap (Ap ℓ f) x), 
          apply h20,
          split,
          {
            exact hx,
          },
          {
            have h22:= h19 x hx,
            cases h22 with y h23,
            cases h23 with h24 h25,
            have h26:= nfFUNC M ℓ hl f hfunc h5,
            cases h26 with h27 h28,
            have h27:= Apdef M (Ap ℓ f) h27 x y h25,
            rw← h27,
            exact h25,
          } 
        }
      end,
    intros n hn,
    rw N_members at hn,
    specialize hn (Z_doubleiteration  M),
    have h3:= hn (and.intro base step),
    rw Z_doubleiteration_members at h3,
    exact h3.right, 
  end

lemma mapsid: ∀ (X:M), maps M id X X:=
  assume X,
  begin
    unfold maps,
    split,
    {
      rw Rel_definition,
      intros z h,
      rw identity_definition at h,
      cases h with x h3,
      use x, use x,
      exact h3,
    },
    {
      split,
      {
        intros x y h,
        cases h with h2 h3,
        rw identity_definition at h3,
        cases h3 with t h4,
        rw ordered_pair_equality at h4,
        rw h4.left at *,
        rw h4.right at *,
        exact h2,
      },
      {
        split,
        {
          intros x y z h,
          rcases h with ⟨ h2, h3, h4⟩, 
          rw identity_definition at h3 h4,
          cases h3 with p h5,
          cases h4 with q h6,
          rw ordered_pair_equality at h5 h6,
          rw h6.left at *,
          rw h5.left at *,
          rw h5.right,
          rw h6.right,
        },
        {
          intros x h,
          use x,
          rw identity_definition,
          split,
          {
            exact h,
          },
          {
            use x,
          }
        }
      }
    }
  end

lemma oneoneid:  ∀ (X:M), oneone M id X X:=
  assume X,
  begin
    unfold oneone,
    split,
    {
      exact mapsid M X,
    },
    {
      split,
      {
        intros x u y,
        rw identity_definition,
        rw identity_definition,
        intro h,
        cases h with h2 h3,
        cases h2 with p h4,
        cases h3 with h5 h6,
        cases h5 with q h7,
        rw ordered_pair_equality at h4 h7,
        rw h7.right at *,
        rw h4.right at *,
        rw h4.left,
        rw h7.left,     
      },
      {
        intros x y h,
        cases h with h2 h3,
        rw identity_definition at h2,
        cases h2 with p h5,
        rw ordered_pair_equality at h5,
        rw h5.left,
        rw h5.right at h3,
        exact h3,
      }
    }
  end

lemma Apmaps: ∀ (X f x:M), maps M f X X → f ∈ FUNC → x ∈ X → ‹ x, Ap f x› ∈ f:=
  begin
    intros X f x hmaps hf hx,
    unfold maps at hmaps,
    rcases hmaps with ⟨h2,h3,h4,h5⟩,
    have h6:= h5 x hx,
    cases h6 with y h7,
    cases h7 with h8 h9,
    have h10:= Apdef M f hf x y h9,
    rw h10 at h9,
    exact h9, 
  end

lemma Apmaps2: ∀ (X Y f x:M), maps M f X Y → f ∈ FUNC → x ∈ X → ‹ x, Ap f x› ∈ f:=
  begin
    intros X Y f x hmaps hf hx,
    unfold maps at hmaps,
    rcases hmaps with ⟨h2,h3,h4,h5⟩,
    have h6:= h5 x hx,
    cases h6 with y h7,
    cases h7 with h8 h9,
    have h10:= Apdef M f hf x y h9,
    rw h10 at h9,
    exact h9, 
  end

lemma oneoneiteration_helper: ∀ (X f m:M), m ∈ ℕℕ → f ∈ FUNC → Rel f → maps M f X X → oneone M f X X → dom f ⊆ X → oneone M (Ap m f) X X → oneone M (Ap (S m) f) X X:=
  assume X f m,
  begin
    intros hm hf hrel hmaps honeone hdom hmaps2,
    have h3:= successorequation M X f hf hrel hmaps m,
    unfold oneone,
    have h4:= successoromitszero M m hm,
    have h50:= iterationFUNC M (S m) (successorN M m hm) f X hmaps hf hrel hdom h4,
    have h52:= iterationRel M (S m) (successorN M m hm) f X hmaps hf hrel hdom h4,
    have h53:= iterationRange M (S m) (successorN M m hm) f X hmaps hf hrel hdom h4, 
    repeat{split},
    {
      exact h52,
    },
    {
      rw subset_definition at h53,
      intros x y h5,
      specialize h53 y,
      rw range_axiom (Ap (S m) f) h52 y at h53,
      apply h53,
      use x,
      exact h5.right,
    },
    {
      intros x y z h5,
      rcases h5 with ⟨ h6, h7, h8⟩,
      have h9:= h3 x hm h6, 
      have h11:= nfFUNC M (S m) (successorN M m hm) f hf hrel,
      cases h11 with h12 h13,
      have h10:= Apdef M (Ap (S m) f) h12,
      have h14:= h10 x y h7,
      have h15:= h10 x z h8,
      rw h14,
      rw h15,  
    },
    {
      intros x hx,
      have h11:= iteration M (S m) (successorN M m hm) X f hf hrel hmaps,
      cases h11 with h12 h13,
      unfold maps at h12,
      rcases h12 with ⟨h14, h15, h16,h17⟩,
      have h18:= h17 x hx,
      exact h18,
    },
    {
      intros x u y h10,
      rcases h10 with ⟨ h11, h12, h13⟩, 
      have hsm:= successorN M m hm,
      have h20:= nfFUNC M (S m) hsm f hf hrel,
      cases h20 with h21 h22,
      have h14:= Apdef M (Ap (S m) f) h21,
      have h15:= h14 x y h11,
      have h16:= h14 u y h12,
      rw h3 x hm h13 at h15,
      have h17: u ∈ X:=
        begin
          rw subset_definition at h50,
          have h17:= h50 u,
          rw domain_axiom (Ap (S m) f) h52 at h17,
          apply h17,
          exact ⟨ y, h12⟩, 
        end,
      rw h3 u hm h17 at h16,
      unfold oneone at honeone,
      rcases honeone with ⟨ h30, h31, h32⟩,
      have h33:  Ap (Ap m f) x = Ap (Ap m f) u:=
        begin
          have h34:= h31 (Ap (Ap m f) x) (Ap (Ap m f) u) y,
          apply h34, 
          repeat{split},
          { 
           rw h15,
           have h35:= Apmaps M X f (Ap (Ap m f) x) hmaps hf,
           apply h35,
           unfold oneone at hmaps2,
           cases hmaps2 with h36 h37,
           unfold maps at h36,
           rcases h36 with ⟨ h137, h38, h39, h40⟩,
           have h41:= h40 x h13,
           cases h41 with p h42,
           cases h42 with h43 h44,
           have h46:= nfFUNC M m hm f hf hrel,
           have h45:= Apdef M (Ap m f) h46.left x p h44,
           rw h45 at h44,
           have h46:= h38 x (Ap (Ap m f) x) ⟨ h13, h44⟩, 
           exact h46, 
          },
          {
            rw h16,
            have h35:= Apmaps M X f (Ap (Ap m f) u) hmaps hf,
            apply h35,
            unfold oneone at hmaps2,
            cases hmaps2 with h36 h37,
            unfold maps at h36,
            rcases h36 with ⟨ h37, h38, h39, h40⟩,
            have h41:= h40 u h17,
            cases h41 with p h42,
            cases h42 with h43 h44,
            have h46:= nfFUNC M m hm f hf hrel,
            have h45:= Apdef M (Ap m f) h46.left u p h44,
            rw h45 at h44,
            have h46:= h38 u (Ap (Ap m f) u) ⟨ h17, h44⟩, 
            exact h46, 
          },
          {
            unfold oneone at hmaps2, 
            cases hmaps2 with h40 h41,
            have h60:= (nfFUNC M m hm f hf hrel).left,
            have h42:= Apmaps M X (Ap m f) x h40 h60 h13,
            unfold maps at h40,
            rcases h40 with ⟨ h43, h44, h45, h46⟩,
            have h47:= h44 x (Ap (Ap m f) x) ⟨ h13, h42⟩, 
            exact h47,
          }
        end,
      rw← h33 at *,
      unfold oneone at hmaps2,
      cases hmaps2 with h36 h37,
      cases h37 with   h38 h39,  
      have h40:= h38 x u (Ap (Ap m f) x ),
      have h60:= (nfFUNC M m hm f hf hrel).left,
      have h41:= Apmaps M X (Ap m f) x h36 h60 h13,
      have h42:= Apmaps M X (Ap m f) u h36 h60 h17,
      rw← h33 at h42,
      exact h40 ⟨ h41, ⟨ h42, h13⟩ ⟩, 
    },
    {
      intros x y h54,
      cases h54 with h55 h56,
      rw subset_definition at h50,
      specialize h50 x,
      apply h50,
      rw domain_axiom (Ap (S m) f) h52,
      use y,
      exact h55,
    } 
  end

lemma oneoneiteration: ∀(m:M), m ∈ ℕℕ → ∀ (X f:M), f∈ FUNC → Rel f → dom f ⊆ X → range f ⊆ X → maps M f X X → oneone M f X X →
maps M (Ap m f) X X ∧ oneone M (Ap m f) X X ∧ (¬ m = ChurchZero → range (Ap m f) ⊆ X ∧ dom (Ap m f) ⊆ X):=
  begin
    have base: ChurchZero ∈ Z_oneoneiteration M:=
      begin
        rw Z_oneoneiteration_members,
        split,
        {
          exact zeroN M,
        },
        {
          intros X f hf hrel hdom hrange hmaps honeone,
          have h3:= ApZero M f,
          rw h3 at *,
          split,
          {
            exact mapsid M X,
          },
          {
            split,
            {
              exact oneoneid M X,
            },
            {
              intro h,
              contradiction,
            }
          } 
        }
      end,
    have step: ∀(m:M), m ∈ Z_oneoneiteration M → S m ∈ Z_oneoneiteration M:=
      assume m,
      begin
        intros h,
        rw Z_oneoneiteration_members,
        rw Z_oneoneiteration_members at h,
        cases h with hm h3,
        split,
        {
          exact successorN M m hm,
        },
        {
          intros X f hf hrel hdom hrange hmaps honeone,
          have h4:= h3 X f hf hrel hdom hrange  hmaps honeone,
          rcases h4 with ⟨ h5, h6, h7⟩, 
          have h90:= iteration M (S m) (successorN M m hm) X f hf hrel hmaps,
          split,
          { 
            exact h90.left,
          },
          {
            split,
            {
               exact oneoneiteration_helper  M X f m hm hf hrel hmaps honeone hdom h6,
            },
            {
              intro h4,
              have h10:= decidable0 M m hm,
              cases h10 with h11 h12,
              {
                rw h11 at *,
                have h12:= ApOne M f hf hrel,
                rw h12,
                unfold maps at hmaps,
                rcases hmaps with ⟨ h15, h16, h17, h18⟩,
                unfold oneone at honeone,
                rcases honeone with ⟨ h20, h21, h22⟩, 
                split,
                {
                  rw subset_definition,
                  intros t h13,
                  rw range_axiom f hrel at h13,
                  cases h13 with x h14,
                  have h23: x ∈ X:=
                    begin
                      rw subset_definition at hdom,
                      specialize hdom x,
                      have h24:= domain_axiom f hrel x,
                      rw h24 at hdom,
                      apply hdom,
                      use t,
                      exact h14,
                    end,
                  have h19:= h16 x t ⟨ h23, h14⟩, 
                  exact h19,
                },
                { 
                  rw subset_definition,
                  intros x h13,
                  rw domain_axiom f hrel at h13,
                  cases h13 with y h14,
                  have h23: y ∈ X:=
                    begin
                      rw subset_definition at hrange,
                      have h24:= hrange y,
                      rw range_axiom f hrel at h24,
                      apply h24,
                      use x,
                      exact h14,
                    end,
                  exact h22 x y ⟨ h14, h23⟩, 
                }
              },
              { 
                have h30:= h7 h12,
                cases h30 with h31 h32, 
                have h50:= iterationFUNC M (S m) (successorN M m hm) f X hmaps hf hrel hdom (successoromitszero M m hm),
                have h52:= iterationRel M (S m) (successorN M m hm) f X hmaps hf hrel hdom (successoromitszero M m hm),
                have h53:= iterationRange M (S m) (successorN M m hm) f X hmaps hf hrel hdom (successoromitszero M m hm), 
                split,
                { 
                  rw subset_definition,
                  intros t h18,
                  have h22:= h90.left,
                  unfold maps at h22,
                  cases h22 with h19 h23, 
                  have h20:= range_axiom (Ap (S m) f) h19 t,
                  rw h20 at h18,
                  cases h18 with x h21,
                  have h51:= domain_axiom (Ap (S m) f) h52 x,
                  rcases h23 with ⟨ h24, h25, h26⟩, 
                  rw subset_definition at h53,
                  have h33:= h53 t,
                  apply h33,
                  have h34:= range_axiom (Ap (S m) f) h19 t,
                  rw h34,
                  use x,
                  exact h21,
                },
                {
                  exact h50,
                }    
              }
            }
          }
        }
      end,
    intros n hn,
    rw N_members at hn,
    specialize hn (Z_oneoneiteration  M),
    have h3:= hn (and.intro base step),
    rw Z_oneoneiteration_members at h3,
    exact h3.right, 
  end


#axioms_all 
