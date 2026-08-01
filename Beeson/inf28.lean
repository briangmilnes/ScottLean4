import inf27

variables (M:Type) [Model M] (a b x y z u v w X R W κ μ ℓ : M)

open Model 

lemma towerdown: ∀ (n y:M), n ∈ NC M → y ∈ 𝔽 → (∃(u:M), u ∈ 𝕊 y) → (∃(u:M), u ∈ tower M n (𝕊 y)) → ∃ (u:M), u ∈ tower M n y:=
  begin 
    intros n y hn hy hsy h4,
    cases h4 with u h5,
    rw towerE_recursion_equation at h5,
    rw exp2_members at h5,
    cases h5 with a h6,
    cases h6 with h7 h8,
    use USC a,
    exact h7,
    exact hy,
    exact hsy,
  end

lemma exp2Tinhabited: ∀ (m:M), m ∈ NC M → ∃ (u:M), u ∈ exp2 M (𝕋 M m):=
  assume m,
  begin
    intro h,
    have h2:= cardinalsinhabited2 M m h,
    cases h2 with u h3,
    have h4:= Tmembers M u m h3,
    use SC u,
    rw exp2_members M,
    use u,
    exact ⟨ h4, similar_reflexive M (SC u)⟩, 
  end

lemma exp2TinNC: ∀ (m:M), m ∈ NC M → exp2 M (𝕋 M m) ∈ NC M:=
  assume m,
  begin
    intro h,
    have h2:= exp2Tinhabited M m h,
    have h2copy:= h2,
    cases h2 with u h3,
    rw exp2_members at h3,
    cases h3 with a h5,
    cases h5 with h6 h7,
    have h4: exp2 M (𝕋 M m ) = Nc M (SC a):=
      begin
        rw full_extensionality,
        intros t,
        split,
        {
          intros h10,
          rw exp2_members at h10,
          cases h10 with b h11,
          cases h11 with h12 h13,
          rw T_members at h6 h12,
          cases h12 with B h14,
          cases h14 with h15 h16,
          have h39: Nc M (SC a) ∈ NC M:=
            begin
              rw NC_members,
              use (SC a),
            end,
          have h40:= cardinals0 M (Nc M (SC a)) (SC a) t h39 (xinNcx M (SC a)),
          apply h40,
          have h41: similar M a b:= 
            begin
              cases h6 with A h30,
              cases h30 with h31 h32,
              have h33:= uscsimilar M a A,
              have h34:= cardinals2 M m A B h h31 h15,
              have h35:= (uscsimilar M A B).1 h34,
              have h36:= uscsimilar M a b,
              rw h36,
              have h37:= similar_transitive M (USC a)(USC A)(USC B) h32 h35,
              rw similar_symmetric at h16,
              have h38:= similar_transitive M (USC a)(USC B)(USC b) h37 h16,
              exact h38,
            end,
          have h42:= scsimilar M a b h41,
          rw similar_symmetric at h42,
          have h43:= similar_transitive M t (SC b)(SC a) h13 h42,
          rw similar_symmetric,
          exact h43,
        },
        {
          intros h50,
          have h52:= xinNcx M (SC a),
          have h53: Nc M (SC a) ∈ NC M:=
            begin
              rw NC_members,
              use SC a,
            end,
          have h51:= cardinals2 M (Nc M (SC a)) (SC a) t h53 h52 h50,
          rw exp2_members,
          use a,
          rw similar_symmetric,
          exact ⟨ h6, h51⟩,
        }
      end,
    rw NC_members,
    use SC a,
    exact h4,
  end

lemma union_subset2: ∀ (c a:M), c ⊆ a → union c ⊆ union a:=
  begin
    intros c a hc,
    rw subset_definition,
    intros t ht,
    rw union_axiom at ht,
    rw union_axiom,
    cases ht with z h3,
    cases h3 with hz ht,
    use z,
    split,
    {
      exact member_subset M c a z hc hz,
    },
    {
      exact ht,
    }
  end

lemma uscsubsetisusc: ∀ (c a:M), c ⊆ USC a → ∃(b:M),b ⊆a ∧ c = USC b:=
 -- oops, a duplicate of uscsubsets 
  begin
    intros c a hc,
    use union c,
    rw uscunion M a c hc,
    simp,
    have h20:= union_subset2 M c (USC a) hc,
    have h21:= unionusc M a,
    rw h21,
    exact h20,
  end 

lemma twopointsix: ∀ (x:M), similar M (USC (SC x)) (SC (USC x)):=
  begin
    intros x,
    unfold similar,
    use ftwopointsix M x,
    unfold similarity,
    split,
    {
      unfold oneone,
      split,
      {
        unfold maps,
        split,
        {  -- f is a relation
          rw Rel_definition,
          intros z,
          rw ftwopointsix_members,
          intros h2,
          cases h2 with a h3,
          use single a,
          cases h3 with h4 h5,
          use USC a,
          exact h4,
        },
        { 
          split,
          {  -- to prove y in SC(USC x)
            intros t y h5,
            cases h5 with h6 h7,
            rw ftwopointsix_members at h7,
            cases h7 with a h8,
            cases h8 with h9 h10,
            rw ordered_pair_equality at h9,
            cases h9 with h20 h11,
            rw h11 at *,
            rw sc_members,
            have h12:= usc_subset M a x,
            rw← h12,
            rw subset_definition,
            intros z h13,
            exact member_subset M a x z h10 h13,
          },
          {
            split,
            {  --f is single-valued
              intros t y z,
              intros h30,
              rcases h30 with ⟨ h32, h33, h34⟩,
              rw ftwopointsix_members M x at h33,
              rw ftwopointsix_members M x at h34,
              cases h33 with a h35,
              cases h34 with b h36,
              cases h35 with h37 h38,
              cases h36 with h39 h40,
              rw ordered_pair_equality at h37,
              rw ordered_pair_equality at h39,
              rw h37.1 at *,
              rw h37.2 at *,
              rw h39.1 at *,
              rw h39.2 at *,
              cases h39 with h41 h42,
              rw full_extensionality at h41,
              simp_rw singleton1 at h41,
              have h42:= h41 a,
              simp at h42,
              rw h42 at *,
            },
            { -- f is defined on USC(SC x)
              intros t h43,
              rw usc at h43,
              cases h43 with a h44,
              cases h44 with h45 h46,
              use USC a,
              simp_rw ftwopointsix_members M x,
              split,
              { 
                rw sc_members at h45,
                rw sc_members,
                have h46:= (usc_subset M a x).1 h45,
                exact h46,
              },
              {
                use a,
                rw h46 at *,
                simp,
                rw sc_members at h45,
                exact h45,
              }
            }
          }
        }
      },
      { 
        split,
        {  -- to prove f is oneone 
          intros t u y h50,
          rcases h50 with ⟨ h51, h52, h53⟩,
          rw ftwopointsix_members at h51,
          rw ftwopointsix_members at h52,
          cases h51 with a h54,
          cases h52 with b h55,
          cases h54 with h56 h57,
          cases h55 with h58 h59,
          rw ordered_pair_equality at h56 h58,
          cases h58 with h60 h61,
          cases h56 with h62 h63,
          rw h60 at *,
          rw h62 at *,
          rw h63 at h61,
          have h64:= usc_oneone M a b h61,
          rw h64 at *,
        },
        { -- to prove x in USC(SC x) if y ∈ SC(USC x)
          intros t y h70,
          cases h70 with h71 h72,
          rw ftwopointsix_members at h71,
          rw sc_members at h72,
          cases h71 with X h73,
          cases h73 with h74 h75,
          rw ordered_pair_equality at h74,
          cases h74 with h76 h77,
          rw h76 at *,
          rw h77 at *,
          rw usc,
          use X,
          simp,
          rw sc_members,
          exact h75,
        }
      }
    },
    {
      -- to prove onto
      unfold onto,
      intros b h80,
      rw sc_members at h80,
      have h81:= uscsubsetisusc M b x h80,
      cases h81 with t h82,
      use  single t,
      cases h82 with h83 h84,
      rw usc,
      use t,simp,
      rw sc_members,
      exact h83,
      rw ftwopointsix_members M,
      use t,
      rw h84,
      simp,
      exact h83,
    }
  end

--Specker 5.9 
lemma exp2T: ∀ (m:M), m ∈ NC M → (∃ u, u ∈ exp2 M m)→ exp2 M (𝕋 M m) = 𝕋 M (exp2 M m):=
  assume m,
  begin
    intros h h2,
    have h2copy:= h2,
    cases h2 with u h3,
    have h40:= NCexp2 M m h h2copy,
    have h7:= exp2uscsc M m h40,
    cases h7 with a h41,
    cases h41 with h42 h9,
    have h10: USC (SC a) ∈ 𝕋 M (exp2 M m) := Tmembers M (SC a) (exp2 M m) h9,
    have h11: USC (USC a) ∈ 𝕋 M m := Tmembers M (USC a) m h42, 
    have h12: 𝕋 M m ∈ NC M := TNC M m h, 
    have h14:= twopointsix M a,
    have h15:= TNC M (exp2 M m) h40,
    have h16 := cardinals0 M  (𝕋 M (exp2 M m)) (USC (SC a)) (SC (USC a)) h15 h10 h14,
    have h17:= xinNcx M (SC (USC a)),
    have h18: Nc M (SC(USC a)) ∈ NC M:=
      begin
        rw NC_members,
        use SC (USC a),
      end,
    have h18a: Nc M (USC(SC a)) ∈ NC M:=
      begin
        rw NC_members,
        use USC (SC a),
      end,
    have h21:= xinNcx M (USC (SC a)),
    have h20:= cardinals0 M (Nc M (SC (USC a))) (SC (USC a)) (USC (SC a)) h18 h17,
    have h14a:= h14,
    rw similar_symmetric at h14a,
    have h19:= cardinalsdisjoint2 M (Nc M (USC (SC a))) (𝕋 M (exp2 M m)) (USC (SC a)) h18a h15 h21 h10,
    have h22: USC (USC a) ∈ 𝕋 M m:=
      begin
        rw T_members,
        use USC a,
        split,
        {
          exact h42,
        },
        {
          have h43:= similar_reflexive M (USC (USC a)),
          exact h43,
        }
      end,
    have h23: SC(USC a) ∈ exp2 M (𝕋 M m):=
      begin
        rw exp2_members,
        use USC a,
        split,
        {
          exact h11,
        },
        {
          exact similar_reflexive M (SC (USC a)),
        }
      end, 
    have h24:= NCexp2 M (𝕋 M m) h12 ⟨SC(USC a), h23⟩,
    rw sym,
    have h30:= TNC M (exp2 M m) h40,
    have h25:= cardinalsdisjoint2 M (𝕋 M (exp2 M m)) (exp2 M (𝕋 M m)) (SC (USC a)) h30 h24 h16 h23,
    exact h25,
  end
  

lemma TofI: ∀ (n:M), n ∈ NC M →
∀ (y:M), y ∈ 𝔽 → (∃(u:M), u ∈ tower M n y) → 𝕋 M (tower M n y) = tower M (𝕋 M n) (𝕋 M y) :=
  begin
    intros  n hn,
    have base: zero ∈ Z_TofI M n:=
      begin
        rw Z_TofI_members,
        split,
        {
          exact zeroF M,
        },
        {
          intros h3,
          rw towerE_base_equation,
          rw towerE_base_equation at h3,
          rw Tzero,
          rw towerE_base_equation,
        }
      end,
    have step: ∀(y:M), y ∈ Z_TofI M n → (∃(u:M),u ∈ 𝕊 y) →  𝕊 y ∈ Z_TofI M n:=
      begin
        intros y h3 hsy,
        rw Z_TofI_members at h3,
        rw Z_TofI_members,
        cases h3 with hy h4,
        split,
        {
          exact successorF M y hy hsy,
        },
        {
          intro h5,
          have h20:= towerdown M n y hn hy hsy h5,
          rw towerE_recursion_equation,
          have h21:= Tsuccessor M y hy hsy,
          rw h21,
          rw towerE_recursion_equation,
        
          have h23:= towerinNC M n hn y hy h20,
          have h22:= exp2T M (tower M n y) h23,
          cases h5 with u h24,
          rw towerE_recursion_equation at h24,
          have h25:= h22 ⟨ u, h24⟩,
          rw← h25,
          have h26:= h4 h20,
          rw h26,
          exact hy,
          exact hsy,
          exact Tfinite M y hy,
          cases hsy with v h27,
          have h28: USC v ∈ 𝕋 M (𝕊 y):=
            begin
              rw T_members,
              use v,
              exact ⟨ h27, similar_reflexive M (USC v) ⟩,
            end,
          use USC v,
          rw Tsuccessor at h28,
          exact h28,
          exact hy,
          exact ⟨v, h27⟩,
          exact hy,
          exact hsy,
        }
      end,
    intros y hy,
    rw F_members at hy,
    have h200:= hy (Z_TofI M n) ⟨base, step⟩,
    rw Z_TofI_members at h200,
    exact h200.2,
  end

lemma ToneoneNCduplicate: ∀ (n m:M), n ∈ NC M → m ∈ NC M → 𝕋 M n = 𝕋 M m → m = n:=
--oops,  I reproved it. See inf24.lean
-- but the checkmark numbers in the TeX file refer to this proof.
  begin
    intros n m hn hm h3,
    have h4:= cardinalsinhabited2 M m hm,
    have h5:= cardinalsinhabited2 M n hn,
    cases h5 with a ha,
    cases h4 with b hb,
    have h6: USC a ∈ 𝕋 M n:=
      begin
        rw T_members,
        use a,
        exact ⟨ ha, similar_reflexive M (USC a)⟩,
      end, 
     have h7: USC b ∈ 𝕋 M m:=
      begin
        rw T_members,
        use b,
        exact ⟨ hb, similar_reflexive M (USC b)⟩,
      end, 
    have h8:= h7,
    rw← h3 at h8,
    have h9:= TNC M n hn,
    have h10:= TNC M m hm,
    have h11:= cardinals2 M (𝕋 M n) (USC a)(USC b) h9 h6 h8,
    have h12:= (uscsimilar M a b).2 h11,
    have h13:= cardinals0 M n a b hn ha h12,
    have h14:= cardinalsdisjoint2 M m n b hm hn hb h13,
    exact h14,
  end

lemma notxlessdotx: ∀ (x:M), ¬ (x ⋖ x):=
  begin
    intros x h,
    rw lessdot_definition at h,
    cases h with h2 h3,
    cases h3 with h4 h5,
    contradiction,
  end

lemma exp2notzero: ∀ (x:M),  ¬ exp2 M x = zero:=
  begin
    intros x  h4,
    rw full_extensionality at h4,
    specialize h4 Λ,
    rw zero_members at h4,
    simp at h4,
    have h5:=exp2_members M x Λ,
    rw h5 at h4,
    cases h4 with a h6,
    cases h6 with h7 h8,
    rw similar_symmetric at h8,
    have h9:= similar_to_empty2 M (SC a) h8,
    have h20: Λ ⊆ a:= empty_always_subset M a,
    have h10: Λ ∈ SC a:=
      begin
        rw sc_members,
        exact h20,
      end,
    rw h9 at h10,
    have h11:= emptyset_axiom Λ,
    contradiction,
  end 

lemma towerzero: ∀ (y m:M), m ∈ NC M → y ∈ 𝔽 → (tower M m y = zero ↔ m = zero ∧ y = zero):=
  begin
    intros y m hm hy,
    have h3:= FregeNdecidable M,
    rw decidable_members at h3,
    have h4:= h3 y zero ⟨ hy, zeroF M⟩,
    cases h4 with h5 h6,
    { 
      rw h5 at *,
      rw towerE_base_equation M m,
      simp,
    },
    { 
      have h7:= nonzeroissuccessor M y hy h6,
      cases h7 with p h8,
      cases h8 with hp hsp,
      rw hsp,
      rw towerE_recursion_equation M,
      have h9:= exp2notzero M (tower M m p),
      split,
      {
        intros h11,
        contradiction,
      },
      {
        intros h13,
        cases h13 with h14 h15,
        have h16:= Fregesuccessoromits0 M p,
        contradiction,
      },
      exact hp,
      have h20:= cardinalsinhabited M y hy,
      simp_rw hsp at h20,
      exact h20,
    } 
  end

lemma towerorder: ∀(y:M), y ∈ 𝔽 → ∀ (x m:M), x ∈ 𝔽 → m ∈ NC M → 
tower M m y ∈ NC M → x < y →  tower M m x ⋖ tower M m y :=
  begin
    have base: zero ∈ Z_towerorder M:=
      begin
        rw Z_towerorder_members M,
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
    have step: ∀(y:M), y ∈ Z_towerorder M → (∃(u:M), u ∈ 𝕊 y) → 𝕊 y ∈ Z_towerorder M:=
      begin
        intros y h h2, 
        rw Z_towerorder_members M at h,
        rw Z_towerorder_members M,
        cases h with h3 h4,
        split,
        {
          exact successorF M y h3 h2, 
        },
        { 
          intros x m hx hm h5 h6, 
          have h7:= towerE_recursion_equation M m y h3 h2,
          have h9:= cardinalsinhabited2 M (tower M m (𝕊 y)) h5, 
          cases h9 with u h10,
          rw h7 at h10, 
          rw exp2_members at h10, 
          cases h10 with a h11, 
          cases h11 with h12 h13, 
          have h14:= towerENC M m hm y h3 ⟨ USC a, h12⟩,
          have h15:=  h5,
          simp_rw h7 at h15, 
          have h16:= cardinalsinhabited2 M (exp2 M (tower M m y) ) h15,
          have h18:= mlessdotexp2m M (tower M m y) h14 h16,
          have h19:= FregeNdecidable M, 
          rw decidable_members M at h19,
          have h20:= h19 x zero ⟨ hx, (zeroF M)⟩,
          have h2383: tower M m x ⪯ tower M m y:=
            begin
              cases h20 with h21 h22,
              {
                 -- Case 1, x = zero
                rw h21 at *,
                rw towerE_base_equation M,
                have h23:= sixpointfourNC M m hm y h3 h14, 
                exact h23,
              },
              {
                -- Case 2, x ≠ zero
                have h90: x < y ∨ x = y:=
                  begin
                    have h91:= finitetrichotomy M x hx y h3,
                    cases h91 with h100 h101,
                    {
                      left,
                      exact h100,
                    },
                    {
                      cases h101 with h102 h103,
                      {
                        right,
                        exact h102,
                      },
                      {
                        have h104:= noinsertions M y x h3 hx h103,
                        have h106:= successorF M y h3 h2,
                        have h105:= le_transitive3 M (𝕊 y) x (𝕊 y) h106 hx h106 h104 h6,
                        have h107:= xnotlessthanx M (𝕊 y) h106,
                        contradiction,
                      }
                    }
                  end,
                cases h90 with h91 h92,
                {
                  -- case x < y
                  have h93:= h4 x m hx hm h14 h91,
                  rw lessdot_definition at h93,
                  exact h93.1,
                },
                {
                  -- case x = y
                  rw h92 at *,
                  exact ledotreflexive M (tower M m y) h14,
                }
              }
            end,
          have h30:= mlessdotexp2m M (tower M m y) h14 h16,
          have h50:= h2383,
          rw ledot_definition at h50,
          cases h50 with A h51,
          cases h51 with B h52,
          cases h52 with h53 h54,
          have h40:= towerinNC M m  hm x hx ⟨ A, h53⟩,
          have h31:=kmlessdotexp2m M (tower M m x)(tower M m y) h40 h14 h2383 h16,
          rw towerE_recursion_equation,
          exact h31,
          exact h3,
          exact h2,
        },
      end,     
    intros  y h,  
    rw F_members at h, 
    specialize h ( Z_towerorder M ),
    have h3:= h (and.intro base  step), 
    rw ( Z_towerorder_members M ) at h3, 
    cases h3 with h5 h6, 
    exact h6, 
  end 

lemma toweroneone: ∀ (m x y:M), m ∈ NC M → x ∈ 𝔽 → y ∈ 𝔽 → 
tower M m x ∈ NC M → tower M m x = tower M m y → x = y:=
  assume m x y,
  begin
    intros hm hx hy h2 h3,
    have h4:= Theorem2 M x y hx hy,
    cases h4 with h5 h6,
    have h9:= cardinalsinhabited2 M (tower M m x) h2, 
    cases h5 with h7 h8,
    { 
      have h2copy:= h2,
      rw h3 at h2, 
      have h10:= towerorder  M y hy x m hx hm h2 h7,  
      rw h3 at *, 
      have h13:= notxlessdotx M (tower M m y),
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
        have h10:= towerorder  M x hx y m hy hm h2copy h11,  
        rw h3 at *,
        have h13:= notxlessdotx M (tower M m y),
        contradiction,       
      }
    }
  end

lemma towerbreakNC: ∀(n:M), ∀(x:M), n ∈ NC M → (∃(u v:M), u ∈ n ∧ v ∈ u) → x ∈ 𝔽 → (∃(u:M),u ∈  tower M n x) → ∀ (y:M),y ∈ 𝔽 → (∃(u:M),u ∈ tower M (tower M n x) y) →  x+y ∈ 𝔽 ∧   (tower M n (x+y)) = tower M (tower M n x) y :=
  begin
    intros n x hn huv hx h2,
    have base: (zero:M) ∈ Z_towerbreakNC M n x:=
      begin
        rw (Z_towerbreakNC_members M n x),
        split,
        {
          exact zeroF M,
        },
        { 
          intros h3,
          rw right_identityNF,
          split,
          {
            exact hx,
          },
          {
            rw towerE_base_equation,
          }
        }
      end,
    have step: ∀(y:M), y ∈ Z_towerbreakNC M n x → (∃(u:M), u ∈ 𝕊 y) → 𝕊 y ∈ Z_towerbreakNC M n x:= 
      begin
        intros y h3 hsy,
        rw Z_towerbreakNC_members,
        rw Z_towerbreakNC_members at h3,
        cases h3 with hy h39,
        have hsyF:= successorF M y hy hsy,
        split,
        {
          exact hsyF,
        },
        {
          intros h41, 
          have h50:= towerE_recursion_equation M (tower M n x) y hy hsy,
          rw h50 at h41,
          cases h41 with u h42,
          rw exp2_members at h42,
          cases h42 with a h43,
          cases h43 with h44 h45,
          rw and_comm,  -- change the order of the next goals
          have h46:= h39 ⟨ USC a, h44⟩,
          cases h46 with h47 h48,
          have h49:= h44,
          rw←h48 at h49, 
          have h120:= towerinNC M n hn (x+y) h47 ⟨ USC a, h49⟩,
          have h121:= cardinalsinhabited2 M (tower M n (x + y)) h120,
          have h122:= towerup M n hn huv (x+y) h47 h121,
          cases h122 with h123 h124,
          have h126:= FtoNC M (x+y) h47,
          have h125:= noinsertionsNC M (x+y)(tower M n (x+y)) h126 h120 h124,
          have h127:= h125,
          rw←  addition_equation at h127,
          rw ledot_definition at h127,
          cases h127 with A h128,
          cases h128 with B h129,
          cases h129 with h130 h131,
          have h132: x + (𝕊 y) ∈ 𝔽 := 
            begin
              have h133:= inhabited_sum M (𝕊 y) hsyF x hx ⟨A, h130⟩,
              exact h133,
            end,
          have h134:= cardinalsinhabited M (x+ (𝕊 y)) h132,
          split,
          { have h60:= towerE_recursion_equation M (tower M n x) y hy hsy,
            rw h60,
            rw addition_equation,
            have h61:= towerE_recursion_equation M n (x+y) h47,
            rw towerE_recursion_equation,
            rw h48,
            exact h47,
            simp_rw addition_equation at h134,
            exact h134,
          },
          {
            exact h132,
          }
        },
      end,  
    intros y hy,
    rw F_members at hy,
    specialize hy (Z_towerbreakNC M n x),
    have h20:= hy ⟨ base, step⟩,
    rw Z_towerbreakNC_members at h20,
    cases h20 with h21 h22,
    exact h22,
  end 

lemma towerbreakNC3: ∀(n:M), ∀(x:M), n ∈ NC M  → x ∈ 𝔽 → ∀ (y:M),y ∈ 𝔽 → x+y ∈ 𝔽 →  tower M n (x+y) = tower M (tower M n x) y :=
  begin
    intros n x hn,
    have base: (zero:M) ∈ Z_towerbreakNC3 M n x:=
      begin
        rw (Z_towerbreakNC3_members M n x),
        split,
        {
          exact zeroF M,
        },
        { 
          intros hx h3,
          rw right_identityNF,
          rw towerE_base_equation,
        }
      end,
    have step: ∀(y:M), y ∈ Z_towerbreakNC3 M n x → (∃(u:M), u ∈ 𝕊 y) → 𝕊 y ∈ Z_towerbreakNC3 M n x:= 
      begin
        intros y h3 hsy,
        rw Z_towerbreakNC3_members,
        rw Z_towerbreakNC3_members at h3,
        cases h3 with hy h39,
        have hsyF:= successorF M y hy hsy,
        split,
        {
          exact hsyF,
        },
        {
          intros hx, 
          intros h4,
          have h5: x+y ∈ 𝔽:=
            begin
              rw addition_equation at h4,
              have h6:= cardinalsinhabited M (𝕊 (x+y)) h4,
              cases h6 with a h7,
              rw successor_members at h7,
              cases h7 with b h8,
              cases h8 with c h9,
              cases h9 with h10 h11,
              have h12:= inhabited_sum M y hy x hx ⟨ b, h10⟩, 
              exact h12,
            end,
          have h40:= h39 hx h5,
          have h41: exp2 M (tower M n (x + y) ) = exp2 M (tower M (tower M n x) y):=
            begin
              rw h40,
            end,
          have h6:= h4,
          rw addition_equation at h6,
          have h7:= cardinalsinhabited M (𝕊 (x+y)) h6,
          have h50:= towerE_recursion_equation M n (x+y) h5 h7,
          rw← h50 at h41,
          rw addition_equation,
          have h51:= towerE_recursion_equation M (tower M n x) y hy hsy,
          rw← h51 at h41,
          exact h41,
        }
      end,  
    intros hx y hy,
    rw F_members at hy,
    specialize hy (Z_towerbreakNC3 M n x),
    have h20:= hy ⟨ base, step⟩,
    rw Z_towerbreakNC3_members at h20,
    cases h20 with h21 h22,
    exact h22 hx,
  end 

lemma towerarginF: ∀(n y:M), n ∈ NC M → (∃(u:M), u ∈ tower M n y) → y ∈ 𝔽 :=
  begin
    intros n y hn h3,
    cases h3 with u h4,
    rw tower_members at h4,
    cases h4 with z h5,
    cases h5 with h6 h7,
    rw towergraphE_members at h6,
    cases h6 with h7 h8,
    exact h7,
  end


lemma towerbreakNC2: ∀(n:M), ∀(x:M), n ∈ NC M → 
(∃(u v:M), u ∈ n ∧ v ∈ u) → x ∈ 𝔽 → 
(∃(u:M),u ∈  tower M n x) → 
∀ (y:M),y ∈ 𝔽 → (∃(u:M),u ∈ tower M n (x+y)) →  
x+y ∈ 𝔽 ∧   
(tower M n (x+y)) = tower M (tower M n x) y :=
  begin
    intros n x hn huv hx h2,
    have base: (zero:M) ∈ Z_towerbreakNC2 M n x:=
      begin
        rw (Z_towerbreakNC2_members M n x),
        split,
        { 
          exact zeroF M,
        },
        { 
          intros h3,
          rw right_identityNF,
          split,
          {
            exact hx,
          },
          {
            rw towerE_base_equation,
          }
        }
      end,
    have step: ∀(y:M), y ∈ Z_towerbreakNC2 M n x → (∃(u:M), u ∈ 𝕊 y) → 𝕊 y ∈ Z_towerbreakNC2 M n x:= 
      begin
        intros y h3 hsy,
        rw Z_towerbreakNC2_members,
        rw Z_towerbreakNC2_members at h3,
        cases h3 with hy h39,
        have hsyF:= successorF M y hy hsy,
        split,
        {
          exact hsyF,
        },
        {
          intros h41, 
          have h100:= towerarginF M n (x+𝕊 y) hn h41,
          rw addition_equation at h41,
          cases h41 with u h42,
          have h300:= towerE_recursion_equation M n (x+y),
          rw h300 at h42,
          rw exp2_members at h42,
          cases h42 with a h1100,
          cases h1100 with h101 h102,
          have h200: x+y ∈ 𝔽:=
            begin
            rw addition_equation at h100,
            have h110:= inhabited_sum M y hy x hx,
            apply h110,
            have h111:= cardinalsinhabited M (𝕊 (x+y)) h100,
            cases h111 with z h112,
            rw successor_members at h112,
            cases h112 with w h113,
            cases h113 with c h114,
            cases h114 with h116 h117,
            use w,
            exact h116,
            end,
          have h50:= towerE_recursion_equation M (tower M n x) y hy hsy,
          rw h50,
          split,
          { 
            exact h100,
          },
          {
            rw addition_equation,
            rw towerE_recursion_equation,
            have h104:(∃ (u : M), u ∈ tower M n (x + y)) := 
              begin
                use USC a,
                exact h101,
              end,
            have h105:= h39 h104,
            cases h105 with h106 h107,
            rw h107, 
            exact h200,
            rw addition_equation at h100,
            exact cardinalsinhabited M (𝕊 (x+y)) h100,
          },
          {
            have h200: x+y ∈ 𝔽:=
            begin
            rw addition_equation at h100,
            have h110:= inhabited_sum M y hy x hx,
            apply h110,
            have h111:= cardinalsinhabited M (𝕊 (x+y)) h100,
            cases h111 with z h112,
            rw successor_members at h112,
            cases h112 with w h113,
            cases h113 with c h114,
            cases h114 with h116 h117,
            use w,
            exact h116,
            end,
            exact h200,
          },
          {
            rw addition_equation at h100,
            exact cardinalsinhabited M (𝕊 (x+y)) h100,
          } 
        }
      end,
    intros y hy,
    rw F_members at hy,
    specialize hy (Z_towerbreakNC2 M n x),
    have h20:= hy ⟨ base, step⟩,
    rw Z_towerbreakNC2_members at h20,
    cases h20 with h21 h22,
    exact h22,
  end 


lemma towerbreak: ∀ (n z:M), n ∈ NC M → (∃ (u v : M), u ∈ n ∧ v ∈ u) → z ∈ φ M n → φ M z ⊆  φ M n:=
  begin
    intros n z hn h200 hz,
    rw subset_definition,
    intros x hx,
    rw phi_members at hx,
    cases hx with t h3,
    rcases h3 with ⟨ht, h4, h5⟩, 
    rw phi_members at hz,
    cases hz with y h6,
    rcases h6 with ⟨ hy, h7, h8⟩,
    have h9:= h4,
    rw h7 at *,
    have h201:= towerinNC M n hn y hy,
    simp_rw h4 at h5,
    have h10:= towerbreakNC M n y hn h200 hy h8 t ht h5,
    cases h10 with h11 h12,
    have h13: tower M n (y+t) ∈ φ M n:=
      begin
        rw phi_members,
        use y+t,
        split,
        {
          exact h11,
        },
        {
          split,
          {
            simp,
          },
          {
            simp_rw h12,
            exact h5,
          }
        }
      end,
    have h14:= h13,
    rw h12 at h14,
    rw h4,
    exact h14,
  end
 
 lemma minPhim2: ∀ (m:M), m ∈ NC M  →  m ∈ φ M m:=
  begin
    intros m hm,
    have h10:= cardinalsinhabited2 M m hm,
    rw phi_members,
    use zero,
    split,
    { 
      exact zeroF M,
    },
    {
      have h3:= towerE_base_equation M m,
      rw h3,
      simp,
      exact h10,
    }
  end

lemma sixpointfour2:  ∀ (m n:M), m ∈ NC M → n ∈ NC M → n ∈ φ M m → m ⪯  n:=
  begin
    intros m n hm hn h3,
    rw phi_members M at h3,
    cases h3 with y h6,
    cases h6 with h7 h80,
    cases h80 with h8 h81,
    have hncopy:= hn,
    rw h8 at hn,
    have h10:= cardinalsinhabited2 M n hncopy,
    rw h8 at h10,
    have h9:= towerorder M,
    have h12:= FregeNdecidable M,
    rw decidable_members at h12,
    have h13:= h12 y zero ⟨ h7, zeroF M⟩,
    cases h13 with h14 h15,
    {
      rw h14 at *,
      rw towerE_base_equation at *,
      rw h8 at *,
      exact ledotreflexive M m hm,
    },
    {
      have h16:= nonzeroissuccessor M y h7 h15,
      have h17: zero < y:=
        begin
          have h200:= zero_le_x M y h7,
          rw lessthan_definition,
          split,
          {
            exact h200,
          },
          {
            intros h201,
            rw h201 at h15,
            contradiction,
          }
        end,
      have h18:= towerorder M y h7 zero m (zeroF M) hm hn h17,
      rw towerE_base_equation at h18,
      rw← h8 at h18,
      rw lessdot_definition at h18,
      exact h18.1,
    } 
  end

lemma towerone: ∀ (m:M), m ∈ NC M → tower M m one = exp2 M m:=
  begin
    intros m hm,
    rw one_definition,
    rw towerE_recursion_equation,
    rw towerE_base_equation,
    exact zeroF M,
    rw← one_definition,
    use single Λ,
    rw one_members,
    use Λ,        
  end

lemma sixpointsix2: ∀ (m:M), m ∈ NC M → 
(∃ (u v : M), u ∈ m ∧ v ∈ u)→ 
(∃ (u:M), u ∈ exp2 M m) → 
φ M m = ((single m) ∪ φ M (exp2 M m)) :=
  assume m,
  begin
    intros hm huv h3,
    have h3copy:= h3,
    rw full_extensionality,
    intro t,
    rw binary_union_axiom,
    rw singleton1 M,
    cases h3 with u h4,
    rw exp2_members at h4,
    cases h4 with a h5,
    cases h5 with h6 h7, 
    split,
    { --left to right
      intro h,
      rw phi_members M at h,
      cases h with y h2,
      cases h2 with hy h5,
      have h9: y= zero ∨ ¬ y = zero:= 
        begin
          have h10:= FregeNdecidable M,
          rw decidable_members M at h10,
          exact h10 y zero ⟨ hy, (zeroF M)⟩, 
        end,
      cases h9 with h12 h13,
      {  -- y = zero
        left,
        rw h12 at *,
        cases h5 with h6 h7,
        rw towerE_base_equation M m at h6,
        exact h6,
      },
      { --  y ≠ zero
        right,
        rw phi_members,
        have h14:= nonzeroissuccessor M y hy h13,
        cases h14 with p h15,
        cases h15 with h16 h17,
        rw h17 at *,
        have h18:= towerE_recursion_equation M m p h16 (cardinalsinhabited M (𝕊 p) hy),
        cases h5 with h5a h5b,
        rw h5a at *,
        use p,
        split,
        {
          exact h16,
        },
        { 
          split,
          {
            rw h5a at *,
            have h45:= h5a,
            rw successorisplusone M at h45,
            rw commutativityNF at h45,
            have h46: ∃ (w:M),w ∈ tower M m one:= 
              begin 
                have h60:= towerone M m hm,
                simp_rw h60,
                exact h3copy,
              end,
            have h47: (∃ (u : M), u ∈ tower M m (one + p)):= 
              begin
                rw commutativityNF,
                rw← successorisplusone,
                exact h5b,
              end,
            have h50:= towerbreakNC2 M m one hm huv (oneF M) h46 p h16 h47,
            cases h50 with h51 h52,
            rw commutativityNF at h52,
            rw← successorisplusone at h52,
            rw one_definition at h52,
            have h53: tower M m (𝕊 zero) = exp2 M m:=
              begin
                rw towerE_recursion_equation,
                rw towerE_base_equation,
                exact zeroF M,
                rw← one_definition,
                use single Λ,
                rw one_members,
                use Λ,
              end,
            rw h53 at h52,
            exact h52,
          },
          {
            exact h5b,
          }
        }
      }
    },
    {  --right to left 
      intro h,
      have h3:= h3copy,
      cases h3copy with u h403,
      rw exp2_members at h403,
      cases h403 with a h404,
      cases h404 with h405 h406,
      cases h with h4 h5,
      { 
        rw h4,
        exact minPhim2 M m hm,
      },
      { 
        have h5copy:= h5,
        rw phi_members at h5,
        have h280: exp2 M m = tower M m one:=
          begin
            rw one_definition,
            rw towerE_recursion_equation,
            rw towerE_base_equation,
            exact zeroF M,
            rw←one_definition,
            exact cardinalsinhabited M one (oneF M), 
          end,
        have h290: exp2 M m ∈ φ M m:=
          begin
            rw phi_members,
            use one,
            exact ⟨ oneF M, h280, h3⟩, 
          end,
        have h300:= towerbreak M m (exp2 M m) hm huv h290,
        exact member_subset M (φ M (exp2 M m))(φ M m) t h300 h5copy,
      }
    }     
  end
        
lemma sixpointfive2: ∀ (m:M), m ∈ NC M → (∃(u:M), u ∈ exp2 M m) → ¬ m ∈ φ M (exp2 M m):=
  begin
    intros m hm h3 h4,
    have h2:= NCexp2 M m hm h3,
    have h5:= sixpointfour2 M (exp2 M m) m h2 hm h4,
    have h6:= mlessdotexp2m M m hm h3,
    have h7:= kmlessdotexp2m M (exp2 M m) m h2 hm h5 h3,
    have h8:= xnotlessdotx M (exp2 M m) h2,
    contradiction,
  end

lemma sixpointseven2: ∀ (m:M), m ∈ NC M → 
(∃ (u v : M), u ∈ m ∧ v ∈ u)→ 
φ M (exp2 M m) ∈ FINITE M → 
(∃ (u:M), u ∈ exp2 M m) → 
Nc M (φ M m) = Nc M (φ M (exp2 M m)) + one:=
  assume m,
  begin
    intros h huv hfinite h2,
    have h3:= sixpointsix2 M m h huv h2,
    have h4:= sixpointfive2 M m h h2,
    have h80:= Ncadjoint M (φ M (exp2 M m)) m hfinite h4,
    rw union_commutative at h3,
    rw←  h3 at h80,
    rw sym,
    exact h80,
  end

lemma Tinhabitedmember: ∀(m:M), m ∈ NC M → (∃(u v:M), (u ∈ m ∧ v ∈ u)) →
𝕋 M m ∈ NC M ∧ ∃(u v:M), u ∈ 𝕋 M m ∧ v ∈ u:=
  begin
    intros m hm huv,
    split,
    {
      exact TNC M m hm,
    },
    {
      cases huv with u h2,
      cases h2 with v h3,
      cases h3 with hu hv,
      use USC u,
      use single v,
      rw T_members,
      use u,
      exact ⟨hu, similar_reflexive M (USC u)⟩, 
      rw usc,
      use v,
      simp,
      exact hv,
    }
  end  

lemma finitedown: ∀(a b c:M), a = (b ∪ (single c)) → 
a ∈ FINITE M → ¬(c ∈ b)→ b ∈ FINITE M:=
  begin
    intros a b c h3 ha h4,
    have h3copy:= h3,
    rw full_extensionality at h3,
    have h5:b ⊆ a:=
      begin
        rw subset_definition,
        intros z hz,
        have h5:= h3 z,
        rw h5,
        rw binary_union_axiom,
        left,
        exact hz,
      end, 
    have h40:= separablefinite M a ha b h5,
    apply h40,
    unfold separable_subset,
    split,
    {
      exact h5,
    },
    {
      rw full_extensionality,
      intros t,
      rw binary_union_axiom,
      rw minus_members,
      have h6:= h3 t,
      rw h6,
      rw binary_union_axiom,
      rw singleton1,
      split,
      {
        intros h10,
        cases h10 with h11 h12,
        {
          left,
          exact h11,
        },
        {
          rw h12 at *,
          right,
          simp,
          exact h4,
        }
      },
      {
        intros h15,
        cases h15 with h16 h17,
        left,
        {
          exact h16,
        },
        {
          right,
          cases h17 with h18 h19,
          cases h18 with h20 h21,
          contradiction,
          exact h21,
        }
      }
    }
  end

lemma onepointthree: SC 𝕍 = (𝕍:M):=
  begin
    rw full_extensionality,
    intros t,
    split,
    {
      intros h,
      rw sc_members at h,
      exact V_definition t,
    },
    intros h,
    rw sc_members,
    rw subset_definition,
    intros z hz,
    exact V_definition z,
  end

lemma fourpointthree: ∀(κ:M), κ = Nc M 𝕍 → exp2 M (𝕋 M κ) = κ:=
  begin
    intros κ h3,
    have h100: κ ∈ NC M:= 
      begin
        rw NC_members,
        use 𝕍,
        exact h3,
      end, 
    have h4:= xinNcx M 𝕍,
    rw← h3 at *,
    have h5:= exp2Tinhabited M κ h100,
    have h7:= exp2TinNC M κ h100,
    have h8:  USC 𝕍 ∈ 𝕋 M κ :=
      begin
        rw T_members,
        use 𝕍,
        exact ⟨ h4, similar_reflexive M (USC 𝕍)⟩,
      end,
    have h9: SC 𝕍 ∈ exp2 M (𝕋 M κ):=
      begin
        have h10:= exp2_members M (𝕋 M κ) (SC 𝕍),
        rw h10,
        use 𝕍,
        exact ⟨ h8, similar_reflexive M (SC 𝕍)⟩,
      end, 
    rw onepointthree at h9,
    have h10:= cardinalsdisjoint2 M  (exp2 M (𝕋 M κ)) κ 𝕍 h7 h100 h9 h4,
    exact h10,
  end 

lemma kappaNC:  ∀ (κ:M), κ = Nc M 𝕍 → κ ∈ NC M:=
  begin
    intros κ hk,
    rw NC_members,
    use 𝕍,
    exact hk,
  end

lemma Tsqkappa: ∀ (κ:M), κ = Nc M 𝕍 → exp2 M (𝕋 M (𝕋 M κ)) = 𝕋 M κ :=
  begin
    intros κ hk ,
    have h4:= fourpointthree M κ hk,
    have h5: 𝕋 M (exp2 M (𝕋 M κ)) = 𝕋 M κ:=
      begin
        rw h4,
      end,
    have h7:= kappaNC M κ hk,
    have h8:= TNC M κ h7,
    have h9:= exp2Tinhabited M κ h7,
    have h6:= exp2T M (𝕋 M κ) h8 h9,
    rw h4 at h6,
    exact h6,
  end

lemma kappamax: ∀ (κ m:M), κ = Nc M 𝕍 → m ∈ NC M → m ⪯ κ:=
  begin
    intros κ m hk hm,
    have h3:= cardinalsinhabited2 M m hm,
    cases h3 with a h4,
    have h5:= V_definition a,
    have h6:= xinNcx M 𝕍,
    rw← hk at h6,
    have h7: a ⊆ 𝕍:=
      begin
        rw subset_definition,
        intros t ht,
        exact V_definition t,
      end,
    rw ledot_definition,
    use a,
    use 𝕍,
    exact ⟨ h4, h6, h7⟩,
  end

lemma TontoNC: ∀ (p q:M), p ∈ NC M → q ∈ NC M → p ⪯  𝕋 M q → ∃(r:M), (r ∈ NC M ∧ p = 𝕋 M r):=
  begin
    intros m n hm hn h3,
    rw ledot_definition at h3,
    cases h3 with a h4,
    cases h4 with b h5,
    rcases h5 with ⟨ h6, h7, h8⟩,
    rw T_members at h7,
    cases h7 with c h10,
    cases h10 with hc h11,
    unfold similar at h11,
    cases h11 with f h12,
    set e:= image M f a with edef,
    have h13: similarity  M f a e:=
      begin
        unfold similarity,
        unfold similarity at h12,
        rw edef,
        cases h12 with h20 h21,
        unfold oneone at h20,
        cases h20 with h22 h23,
        unfold maps at h22,
        cases h22 with h24 h25,
        split,
        {
          unfold image,
          unfold oneone,
          split,
          {
            unfold maps,
            split,
            {
              exact h24,
            },
            {
              rcases h25 with ⟨ h30,h31,h32⟩,
              repeat{split},
              {
                intros x y h26,
                cases h26 with h27 h28,
                have h29:= member_subset M a b x h8 h27,
                have h130:= h30 x y ⟨ h29, h28⟩,
                have h199: Rel (f ∩ (a × 𝕍)):=
                  begin
                    have h198:= Rel_definition (f ∩ (a × 𝕍)),
                    rw h198,
                    intros z,
                    rw intersection_axiom,
                    intros h197,
                    cases h197 with h185 h196,
                    rw product_axiom at h196,
                    cases h196 with a h194,
                    cases h194 with b h193,
                    use a, use b,
                    exact h193.2.2,
                  end,
                have h200:= range_axiom (f ∩ (a × 𝕍)) h199 y,
                rw h200,
                use x,
                rw intersection_axiom,
                split,
                {
                  exact h28,
                },
                {
                  rw product_axiom,
                  use x, use y,
                  simp,
                  exact ⟨ h27, V_definition y ⟩,
                }
              },
              {
                intros x y z h180,
                rcases h180 with ⟨ h181, h182, h183⟩,
                have h184:= member_subset M a b x h8 h181,
                exact h31 x y z ⟨ h184, h182, h183⟩,
              },
              {
                intros x hx,
                have h179:= member_subset M a b x h8 hx,
                have h178:= h32 x h179,
                cases h178 with y h177,
                cases h177 with h175 h176,
                use y,
                split,
                {
                  rw range_axiom,
                  use x,
                  rw intersection_axiom,
                  split,
                  {
                    exact h176,
                  },
                  {
                    rw product_axiom,
                    use x, use y,
                    simp,
                    exact ⟨ hx, V_definition y⟩,
                  },
                  {
                    rw Rel_definition,
                    intros z h173,
                    rw intersection_axiom at h173,
                    rw product_axiom at h173,
                    cases h173 with h170 h171,
                    cases h171 with a h168,
                    cases h168 with b h169,
                    use a, use b,
                    exact h169.2.2,
                  }
                },
                {
                  exact h176,
                }
              }
            }
          },
          { 
            cases h23 with h26 h27,
            split,
            {
              intros x y u h80,
              rcases h80 with ⟨h81, h82, h83⟩,   
              have h30:= member_subset M a b x h8 h83,
              have h29:= h26 x y u,
              apply h29,
              exact ⟨ h81, h82, h30⟩,
            },
            {
              intros x y h60,
              cases h60 with h61 h62,
              rw range_axiom at h62,
              cases h62 with X h63,
              rw intersection_axiom at h63,
              cases h63 with h64 h65,
              rw product_axiom at h65,
              cases h65 with p h66,
              cases h66 with q h67,
              rw ordered_pair_equality at h67,
              rcases h67 with ⟨ h68, h69, h70, h71⟩,
              rw← h70 at *,
              rw← h71 at *, 
              have h72:= member_subset M a b X h8 h68,
              have h73:= h26 X x y ⟨ h64, h61, h72⟩,
              rw h73 at *,
              exact h68,
              rw Rel_definition,
              intros z h73,
              rw intersection_axiom at h73,
              cases h73 with h74 h75,
              rw product_axiom at h75,
              cases h75 with a h76,
              cases h76 with b h77,
              use a, use b,
              exact h77.2.2,
            },
          }
        },
        {
          unfold onto,
          intros y h100,
          unfold image at h100,
          rw range_axiom at h100,
          cases h100 with x h101,
          rw intersection_axiom at h101,
          cases h101 with h102 h103,
          rw product_axiom at h103,
          cases h103 with p h104,
          cases h104 with q h105,
          rw ordered_pair_equality at h105,
          rcases h105 with ⟨ h106,h107,h108, h109⟩,
          rw← h108 at *,
          rw← h109 at *,
          use x,
          exact ⟨ h106, h102⟩,
          rw Rel_definition,
          intros z h73,
          rw intersection_axiom at h73,
          cases h73 with h74 h75,
          rw product_axiom at h75,
          cases h75 with a h76,
          cases h76 with b h77,
          use a, use b,
          exact h77.2.2,
        }
      end,
    have h14: similar M a e:=
      begin
        unfold similar,
        use f,
        exact h13,
      end,
    have h15:e ⊆ USC c:=
      begin
        rw edef,
        unfold image,
        rw subset_definition,
        intros  t ht,
        rw range_axiom at ht,
        cases ht with x h16,
        rw intersection_axiom at h16,
        cases h16 with h17 h18,
        unfold similarity at h12,
        cases h12 with h13 h14,
        unfold oneone at h13,
        cases h13 with h14 h15,
        cases h15 with h20 h21,
        unfold maps at h14,
        rcases h14 with ⟨ hrel, h16,h217,h218⟩,
        have h19:= h16 x t,
        apply h19,
        have h22:= h21 x t,
        rw product_axiom at h18,
        cases h18 with p h30,
        cases h30 with q h31,
        rw ordered_pair_equality at h31,
        rcases h31 with ⟨ h32,h33,h34,h35⟩,
        rw← h34 at *,
        rw← h35 at *,
        have h36:= member_subset M a b x h8 h32,
        split,
        {
          exact h36,
        },
        {  
          exact h17,
        },
        {
          rw Rel_definition,
          intros t ht,
          rw intersection_axiom at ht,
          cases ht with h50 h51,
          rw product_axiom at h51,
          cases h51 with p h52,
          cases h52 with q h53,
          use p,use q,
          exact h53.2.2,
        }
      end,
    have h20:= USCinverse M e c h15,
    cases h20 with q h21,
    cases h21 with h22 h23,
    have h24:= h14,
    rw h23 at h24,
    have h25: Nc M q ∈ NC M:=
      begin
        rw NC_members,
        use q,
      end,
    have h26:= xinNcx M q,
    use Nc M q,
    split,
    {
      exact h25,
    },
    {
      have h30: a ∈ 𝕋 M(Nc M q):=
        begin
          rw T_members,
          use q,
          exact ⟨ h26, h24⟩,
        end,
      have h31: 𝕋 M (Nc M q) ∈ NC M:=
        begin
          have h32:= TNC M (Nc M q),
          exact h32 h25,
        end,
      have h40:= cardinalsdisjoint2 M m (𝕋 M (Nc M q)) a hm h31 h6 h30,
      exact h40,
    }
  end
  

lemma Tkappaless: ∀ (κ n:M), κ = Nc M 𝕍 → n ∈ NC M → n ⪯ 𝕋 M κ → exp2 M n ∈ NC M:=
  begin
    intros κ n hk hn h3,
    have h5: κ ∈ NC M:=
      begin
        rw NC_members,
        use 𝕍,
        exact hk,
      end,
    have h4:= TontoNC M n κ hn h5 h3,
    cases h4 with r h5,
    cases h5 with h6 h7,
    rw h7 at *,
    have h8:= exp2TinNC M r h6,
    exact h8,
  end

lemma Tkappa: ∀ (κ n:M), κ = Nc M 𝕍 → n ∈ NC M → 𝕋 M κ ⋖ n → exp2 M n = (Λ:M):=
  begin
    intros κ n hk hn h3,
    rw full_extensionality,
    intros t,
    split,
    {
      intros ht,
      have h5:= NCexp2 M n hn ⟨ t, ht⟩,
      have h4:= exp2uscsc M n h5,
      cases h4 with a h6,
      cases h6 with h7 h8,
      set m:= Nc M a with mdef,
      have h9:= xinNcx M a,
      rw← mdef at h9,
      have h10: USC a ∈ 𝕋 M m:=
        begin
          rw T_members,
          use a,
          exact ⟨ h9, similar_reflexive M (USC a)⟩,
        end, 
      have hm: m ∈ NC M:=
        begin
          rw NC_members,
          use a,
        end,
      have h12:= TNC M m hm,
      have h11:= cardinalsdisjoint2 M n (𝕋 M m) (USC a) hn h12 h7 h10,
      have h13: ¬ n ⪯ 𝕋 M κ :=
        begin
          rw lessdot_definition at h3,
          exact h3.2.1,
        end,
      rw h11 at h13,
      have h40: κ ∈ NC M:=
        begin
          rw NC_members,
          use 𝕍,
          exact hk,
        end,
      have h14:= Tledot M m κ hm h40,
      rw←h14 at h13,
      have h15:= kappamax M κ m hk hm,
      contradiction, 
    },
    {
      have h100:= emptyset_axiom t,
      contradiction,
    }
  end

lemma ylessdottower:∀ (y:M), y ∈ 𝔽 → ∀ (n:M), n ∈ NC M → zero ⋖ n →
(∃ (u:M), u ∈ tower M n y) → y ⋖ tower M n y:=
  begin
    have base: (zero:M) ∈ Z_ylessdottower M:=
      begin
        rw Z_ylessdottower_members,
        split,
        {
          exact zeroF M,
        },
        {
          intros n hn hn2 h3,
          rw towerE_base_equation,
          exact hn2,
        }
      end,
    have step: ∀ (y:M), y ∈ Z_ylessdottower M → (∃ (u:M),u ∈ 𝕊 y) → 𝕊 y ∈ Z_ylessdottower M:=
      begin
        intros y h4 hsy,
        rw Z_ylessdottower_members at h4,
        cases h4 with hy h5,
        rw Z_ylessdottower_members,
        split,
        {
          exact successorF M y hy hsy,
        },
        { 
          intros n hn h10 h20,
          have h11:= h5 n hn h10,
          have h6:= towerE_recursion_equation M n y hy hsy,
          simp_rw h6 at h20,
          have h20copy:= h20,
          cases h20 with u h21,
          rw exp2_members at h21,
          cases h21 with a h22,
          cases h22 with h23 h24,
          have h25:= h11 ⟨ USC a, h23⟩,
          have h27:= successorF M y hy hsy,
          have h28:= FtoNC M (𝕊 y) h27,
          have h30: tower M n y ∈ NC M:=
            begin
              have h100:= towerENC M n hn y hy ⟨ USC a, h23⟩,
              exact h100,
            end,
          have h32:= FtoNC M y hy,
          have h31:= noinsertionsNC M y (tower M n y) h32 h30 h25,
          have h26:= kmlessdotexp2m M (𝕊 y)(tower M n y) h28 h30 h31 h20copy,
          rw towerE_recursion_equation,
          exact h26,
          exact hy,
          exact hsy,
        }
      end,
    intros y hy,
    rw F_members at hy,
    specialize hy (Z_ylessdottower M),
    have h40:= hy ⟨ base, step⟩,
    rw Z_ylessdottower_members at h40,
    exact h40.2,
  end



lemma sevenpointtwohelper: ∀(n p:M), n ∈ NC M → p ∈ φ M n → 𝕋 M p ∈ φ M (𝕋 M n):=
  begin
    intros n p hn hp,
    rw phi_members at hp,
    cases hp with y h3,
    rcases h3 with ⟨ hy, h4, h5⟩,
    simp_rw h4 at h5, 
    have h6:= TofI M n hn y hy h5,
    cases h5 with u h7,
    rw phi_members,
    use 𝕋 M y,
    rw h4,
    split,
    {
      exact Tfinite M y hy,
    },
    split,
    {
      exact h6,
    },
    {
      use USC u,
      rw T_members,
      use u,
      exact ⟨h7, similar_reflexive M (USC u)⟩, 
    }
  end

lemma phiexp2: ∀ (n q:M), n ∈ NC M → zero ⋖ n → q ∈ φ M n → exp2 M q ∈ NC M → exp2 M q ∈ φ M n:=
  begin
    intros n q hn hn2 hq h3,
    rw phi_members,
    rw phi_members at hq,
    cases hq with y h4,
    use 𝕊 y,
    rcases h4 with ⟨ hy, h5, h6⟩,
    rw h5 at h6,
    have h10:= towerinNC M n hn y hy h6,
    have h12:= cardinalsinhabited2 M (tower M n y) h10,
    have h11:= ylessdottower M y hy n hn hn2 h12,
    have h14:= FtoNC M y hy,
    have h13:= noinsertionsNC M y (tower M n y) h14 h10 h11,
    have h14:= h13,
    rw ledot_definition at h14,
    cases h14 with a h15,
    cases h15 with b h16,
    cases h16 with h17 h18,
    have h19: ∃ (p:M), p ∈ 𝕊 y:= ⟨ a, h17⟩,
    have h20:= successorF M y hy h19,
    have h7:= towerE_recursion_equation M n y hy h19,
    rw← h5 at h7,
    have h22: exp2 M q ∈ φ M n:=
      begin
        rw phi_members,
        use (𝕊 y),
        split,
        {
          exact h20,
        },
        {
          split,
          {
            rw sym,
            exact h7,
          },
          {
            exact cardinalsinhabited2 M (exp2 M q) h3,
          }
        }
      end,
    split,
    {
      exact h20,
    },
    {
      rw sym at h7,
      split,
      {
        exact h7,
      },
      {
        exact cardinalsinhabited2 M (exp2 M q) h3, 
      }
    }
  end

lemma union_subset3: ∀ (a b c:M), a ⊆ c → b ⊆ c → a ∪ b ⊆c:=
  begin
    intros a b c h2 h3,
    rw subset_definition,
    intros t h4,
    rw binary_union_axiom at h4,
    cases h4 with h5 h6,
    exact member_subset M a c t h2 h5,
    exact member_subset M b c t h3 h6,
  end 

lemma letosum: ∀ (x:M), x ∈ 𝔽→ ∀ (y:M), y ∈ 𝔽 → x ≤ y → ∃ (r:M), r ∈ 𝔽  ∧ x+r = y:=  
  begin
    intros x hx,
    have base: zero ∈ Z_letosum M x:=
      begin
        rw Z_letosum_members,
        split,
        {
          exact zeroF M,
        },
        {
          intros h3,
          have h4:=le_zero M x hx h3,
          rw h4 at *,
          use zero,
          split,
          {
            exact hx,
          },
          {
            rw right_identityNF,
          }
        }
      end,
    have step: ∀ (y:M), y ∈ Z_letosum M x → (∃(u:M), u ∈ 𝕊 y) → 𝕊 y ∈ Z_letosum M x:=
      begin
        intros y h4 hsy,
        rw Z_letosum_members M x at h4,
        rw Z_letosum_members M x,
        cases h4 with hy h5,
        split,
        {
          exact successorF M y hy hsy,
        },
        {
          intros h6,
          have h7:= successorF M y hy hsy,
          have h8:= lessthansuccessor2 M x y hx hy h6,
          cases h8 with case1 case2,
          {
            have h9:= h5 case1,
            cases h9 with t h10,
            cases h10 with ht h11,
            use 𝕊 t,
            rw addition_equation,
            rw h11,
            simp,
            rw← h11 at hsy,
            rw← addition_equation at hsy,
            cases hsy with u h12,
            rw addition_members at h12,
            cases h12 with a h13,
            cases h13 with b h14,
            rcases h14 with ⟨ h15, h16, h17, h18⟩,
            exact successorF M t ht ⟨ b,h17⟩,
          },
          {
            rw case2 at *,
            use zero,
            rw right_identityNF,
            simp,
            exact zeroF M,
          }
        }     
      end,
    intros y hy,
    rw F_members at hy,
    specialize hy (Z_letosum M x),
    have h40:= hy ⟨base, step⟩,
    rw Z_letosum_members at h40,
    exact h40.2,
  end

lemma sevenpointtwoA: ∀(n q:M), n ∈ NC M → zero ⋖ n →  q ∈ φ M n → (∀ (t:M), t ∈ φ M n → t ⪯ q) →
φ M (𝕋 M n) = (imageT M (φ M n) ∪ (φ M (exp2 M (𝕋 M q))))
∧ (imageT M (φ M n) ∩ (φ M (exp2 M (𝕋 M q)))) = (Λ:M):=
  begin
    intros n q hn hn2 hq hmax,
    set κ := Nc M 𝕍 with kappadef,
    have hk: κ ∈ NC M:=
      begin
        rw NC_members,
        use 𝕍,
      end,
    have h1: q ∈ NC M:=
      begin
        rw phi_members at hq,
        cases hq with y h40,
        rcases h40 with ⟨ hy, h42, h43⟩,
        rw h42 at h43,
        have h44:= towerENC M n hn y hy h43,
        rw h42,
        exact h44,
      end,
    have h2: ¬ exp2 M q ∈ NC M:=
      begin
        intros h,
        have h19:= cardinalsinhabited2 M (exp2 M q) h,
        have h20:= mlessdotexp2m M q h1 h19,
        have h21: exp2 M q ∈ φ M n:=
          begin
            have h22:= phiexp2 M n q hn hn2 hq h,
            exact h22,
          end,
        have h23:= mlessdotexp2m M q h1 h19,
        have h24:= hmax (exp2 M q) h21,
        rw lessdot_definition at h23,
        cases h23 with h25 h26,
        cases h26 with h27 h28,
        contradiction,
      end,
    have h3:exp2 M q = (Λ:M):=
      begin
        have h4:= NCexp2 M q h1,
        rw full_extensionality,
        intros t,
        split,
        {
          intros h30,
          have h31:= h4 ⟨ t, h30⟩,
          contradiction,
        },
        {
          intros h34,
          have h35:= emptyset_axiom t,
          contradiction,
        }
      end,
    have h4: imageT M (φ M n) ⊆ φ M (𝕋 M n):=
      begin
        rw subset_definition,
        intros t ht,
        rw imageT_members M (φ M n) at ht,
        cases ht with u h40,
        cases h40 with h42 h43,
        have h44:= sevenpointtwohelper M n u hn h42,
        rw h43,
        exact h44,
      end,
    have h5: 𝕋 M q ∈ imageT M (φ M n):=
      begin
        rw imageT_members M (φ M n),
        use q,
        simp,
        exact hq,
      end,
    have h6: 𝕋 M q ∈ φ M (𝕋 M n):=
      begin
        have h7:= member_subset M (imageT M (φ M n)) (φ M (𝕋 M n)) (𝕋 M q) h4 h5,
        exact h7,
      end,
    have h9: 𝕋 M n ∈ NC M := TNC M n hn,
    have h30: zero ⋖ 𝕋 M n :=
      begin
        have h62:= Tlessdot M zero n (zeroNC M) hn hn2,
        rw Tzero at h62,
        exact h62,
      end,
    have h40:= exp2TinNC M q h1,
    have h10:exp2 M (𝕋 M q) ∈ φ M (𝕋 M n):= 
      begin
        have h11:= phiexp2 M (𝕋 M n)(𝕋 M q) h9 h30 h6 h40,
        exact h11,
      end,
    have h50: (∃ (u v : M), u ∈ 𝕋 M n ∧ v ∈ u) := 
      begin
        rw lessdot_definition at hn2,
        rcases hn2 with ⟨h70, h71, h72⟩,
        cases h72 with a h73, 
        cases h73 with b h74,
        rcases h74 with ⟨ h75, h76, h77, h78⟩,
        cases h78 with u h79,
        use USC b,
        use single u,
        split,
        {
          rw T_members,
          use b,
          exact ⟨ h76, similar_reflexive M (USC b)⟩,
        },
        {
          rw usc,
          use u,
          simp,
          rw minus_members at h79,
          exact h79.1,
        }
      end,
    have h8:= towerbreak M (𝕋 M n)(exp2 M (𝕋 M q)) h9 h50 h10,
    have h80: imageT M (φ M n) ∪ φ M (exp2 M (𝕋 M q)) ⊆ φ M (𝕋 M n):=
      begin
        have h81:= union_subset3 M (imageT M (φ M n))( φ M (exp2 M (𝕋 M q)))(φ  M (𝕋 M n)) h4 h8,
        exact h81,
      end, 
    have hdisjoint1: ∀ (t:M), t ∈ imageT M (φ M n) → t ⪯ 𝕋 M q:=
      begin
        intros t ht,
        rw imageT_members M (φ M n) at ht,
        cases ht with u h90,
        cases h90 with h91 h92,
        rw h92 at *,
        rw← Tledot,
        exact hmax u h91,
        rw phi_members at h91,
        cases h91 with y h92,
        rcases h92 with ⟨ h93, h94, h95⟩,
        rw h94 at h95,
        have h96:= towerinNC M n hn y h93 h95,
        rw h94,
        exact h96,
        exact h1,
      end, 
    have hdisjoint2: ∀ (t:M), t ∈ φ M (exp2 M (𝕋 M q)) → exp2 M (𝕋 M q) ⪯ t:=
      begin
        intros t ht,
        have h97:= exp2TinNC M q h1,
        have h98:= ht,
        have h110: t ∈ NC M := 
          begin
            have h111:=phi_members M (exp2 M (𝕋 M q)) t,
            have h112:= h111.1 h98,
            cases h112 with y h113,
            rcases h113 with ⟨ h114, h115, h116⟩,
            have h117:= towerENC M (exp2 M (𝕋 M q)),
            rw h115,
            apply h117,
            exact h97,
            exact h114,
            simp_rw h115 at h116,
            exact h116,
          end,
        have h100:= sixpointfour2 M (exp2 M (𝕋 M q)) t h97 h110 h98,
        exact h100,
      end,
    have hdisjoint:imageT M (φ M n) ∩ φ M (exp2 M (𝕋 M q)) = Λ:=
      begin
        rw full_extensionality,
        intros t,
        rw intersection_axiom,
        split,
        {
          intros h201,
          cases h201 with h202 h203,
          have h204:= hdisjoint1 t h202,
          have h205:= hdisjoint2 t h203,
          have h110: t ∈ NC M := 
            begin
              have h111:=phi_members M (exp2 M (𝕋 M q)) t,
              have h112:= h111.1 h203,
              cases h112 with y h113,
              rcases h113 with ⟨ h114, h115, h116⟩,
              have h117:= towerENC M (exp2 M (𝕋 M q)),
              rw h115,
              apply h117,
              exact h40,
              exact h114,
              simp_rw h115 at h116,
              exact h116,
            end,
          have h207:= TNC M q h1,
          have h206:= ledottransitive M (exp2 M (𝕋 M q)) t (𝕋 M q) h40 h110 h207 h205 h204,
          have h209:= cardinalsinhabited2 M (exp2 M (𝕋 M q)) h40,
          have h208:= mlessdotexp2m M (𝕋 M q) h207 h209,
          have h210:= kmlessdotexp2m M (exp2 M (𝕋 M q)) (𝕋 M q) h40 h207 h206 h209,
          have h211:= xnotlessdotx M (exp2 M (𝕋 M q)) h40,
          contradiction,
        },
        {
          intros h,
          have h2:= emptyset_axiom t,
          contradiction,
        }
      end,
    have lefttoright: φ M (𝕋 M n) ⊆  imageT M (φ M n) ∪ φ M (exp2 M (𝕋 M q)) :=
      begin
        rw subset_definition,
        intros x h300,
        rw phi_members at h300,
        cases h300 with y h301,
        rcases h301 with ⟨hy, h302, h303⟩,
        have h304:= hq,
        rw phi_members at h304,
        cases h304 with t h305,
        rcases h305 with ⟨ ht, h307, h308⟩,
        have h309: 𝕋 M q = 𝕋 M (tower M n t):=
          begin
            rw h307,
          end,
        simp_rw h307 at h308,
        have h310:= TofI M n hn t ht h308,
        rw h310 at h309,
        have h311:= Tfinite M t ht,
        have h312:= finitetrichotomy M y hy (𝕋 M t) h311,
        cases h312 with case1 case2and3,
        { 
          have h316:= Tonto3 M y t hy ht case1, 
          cases h316 with s h317,
          rcases h317 with ⟨ hs, hys,hst⟩,
          rw hys at h302,
          have h3020:= h302,
          have h401:= h1,
          rw h307 at h401,
          have h400:= towerorder M t ht s n hs hn h401 hst,
          rw← TofI M n at h3020,
          have h601: ∃ (u:M), u ∈ tower M n s:= 
            begin
              have h3030:= h303,
              cases h3030 with u h3031,
              rw h3020 at h3031,
              rw T_members at h3031,
              cases h3031 with z h3032,
              use z,
              exact h3032.1,
            end, 
          have h600:= TofI M n hn s hs h601,
          rw←  h600 at h302,
          have h3030: tower M n s ∈ φ M n:=
            begin
             rw phi_members,
             use s,
             simp,
             simp_rw h302 at h303,
             cases h303 with u h304,
             rw T_members at h304,
             cases h304 with w h305,
             cases h305 with h306 h307,
             exact ⟨hs, w, h306⟩,
            end,
          rw binary_union_axiom,
          left,
          rw imageT_members M (φ M n),
          use tower M n s,
          exact ⟨h3030, h302⟩, 
          exact hn,
          exact hs,
          rw lessdot_definition at h400,
          rcases h400 with ⟨ h401, h402,h403⟩,
          cases h403 with a h404,
          cases h404 with b h405,
          exact ⟨ a, h405.1⟩,
        },
        {
          cases case2and3 with case2 case3,
          { -- case 2, T t = y
            have h430:= TofI M n hn t ht h308,
            rw case2 at *,
            have h431: 𝕋 M q ∈ imageT M (φ M n):=
              begin
                rw imageT_members M (φ M n),
                use q,
                simp,
                exact hq,
              end, 
            rw binary_union_axiom,
            left,
            rw← h302 at h309,
            rw h309 at h431,
            exact h431,
          },
          {  -- case 3
            have h401:= ylessdottower M t ht n hn hn2 h308,
            have h403:= towerinNC M n hn t ht h308,
            have h402:= noinsertionsNC M t (tower M n t) (FtoNC M t ht) h403 h401,
            have h404:  ∃(u:M), u ∈ 𝕊 t :=
              begin
                rw ledot_definition at h402,
                cases h402 with a h403,
                cases h403 with b h404,
                exact ⟨ a, h404.1⟩,
              end,
            have h400:= towerE_recursion_equation M n t ht h404,
            have hTt := Tfinite M t ht,
            have h407:=  successorF M t ht h404,
            have h408:= Tfinite M (𝕊 t) h407,
            have h409:= cardinalsinhabited M (𝕋 M (𝕊 t)) h408,
            rw Tsuccessor M t ht h404 at h409,
            have h405:= towerE_recursion_equation M (𝕋 M n) (𝕋 M t) hTt h409, 
            have h406:= h405,
            rw←  h309 at h406,
            have h407:= noinsertions M (𝕋 M t) y hTt hy case3,
            have h419:= h408,
            rw Tsuccessor M t ht h404 at h419,
            have h420:= letosum M (𝕊 (𝕋 M t)) h419 y hy h407,
            cases h420 with r h421,
            cases h421 with h422 h423,
            have h424: tower M (tower M (𝕋 M n) (𝕊 (𝕋 M t))) r = tower M (exp2 M (𝕋 M q)) r:=
              begin
                rw h406,
              end,
            have h426:= exp2Tinhabited M q h1,
            rw← h406 at h426,
            rw←  Tsuccessor M t ht h404 at h426,
            rw←  Tsuccessor M t ht h404 at h419,
            rw←  Tsuccessor M t ht h404 at h423,
            have h427:= hy,
            rw← h423 at h427,
            have h425:= towerbreakNC3 M (𝕋 M n)(𝕋 M (𝕊 t)) h9 h419 r h422 h427, 
            rw Tsuccessor M t ht h404 at h425,
            rw← h425 at h424,
            rw Tsuccessor M t ht h404 at h423,
            rw h423 at h424,
            rw← h302 at h424,
            rw binary_union_axiom,
            right,
            rw phi_members,
            use r,
            split,
            {
              exact h422,
            },
            {
              exact ⟨ h424,h303⟩, 
            }
          }
        }
      end,
    split,
    {
      rw full_extensionality,
      intros t,
      split,
      { --left to right
        intros ht,
        exact member_subset M ( φ M (𝕋 M n))(imageT M (φ M n) ∪ φ M (exp2 M (𝕋 M q))) t lefttoright ht,
      },
      {
        --right to left
        intros ht,
        exact member_subset M (imageT M (φ M n) ∪ φ M (exp2 M (𝕋 M q)))( φ M (𝕋 M n)) t h80 ht,
      }
    },
    {
      exact hdisjoint,
    }   
  end

#axioms_all