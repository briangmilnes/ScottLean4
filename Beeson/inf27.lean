import inf26

variables (M:Type) [Model M] (a b x y z u v w X R W κ μ ℓ : M)

open Model 

--   iterated exponentiation with exp2 instead of exp

lemma exp2uscsc: ∀ (m:M), exp2 M m ∈ NC M → exists (a:M), USC a ∈ m ∧ SC a ∈ exp2 M m:=
  begin
    intros m h3,
    have h4:= cardinalsinhabited2 M (exp2 M m) h3,
    cases h4 with x h5,
    have h5copy:= h5,
    rw exp2_members at h5,
    cases h5 with a h6,
    cases h6 with h7 h8,
    use a,
    split,
    {
      exact h7,
    },
    {
      have h9:= cardinals0 M  (exp2 M m) x (SC a) h3 h5copy h8,
      exact h9,
    }
  end 

lemma uscinone: ∀(a:M), USC a ∈ one → ∃ (t:M), a = single t:=
  begin
    intros a ha,
    rw one_members at ha,
    cases ha with q h3,
    have h35: ∃ (c:M), c ∈ a:=
      begin
        have h36: q ∈ USC a:=
          begin
            rw full_extensionality at h3,
            have h37:= h3 q,
            rw singleton1 at h37,
            simp at h37,
            exact h37,
          end,
        rw usc at h36,
        cases h36 with t h37,
        use t,
        exact h37.1,
      end,
    cases h35 with c hc,
    have h4: single c ∈ USC a:=
      begin
        rw usc,
        use c,
        simp,
        exact hc,
      end,
    use c,
    rw full_extensionality,
    intros t,
    rw singleton1,
    split,
    {
      intros ht,
      rw full_extensionality at h3,
      have h8: single t ∈ USC a:=
        begin
          rw usc,
          use t,
          simp,
          exact ht,
        end,
      have h5:= h3 (single c),
      have h9:= h3 (single t),
      have h10:= h5.1 h4,
      have h11:= h9.1 h8,
      rw singleton1 at h10,
      rw singleton1 at h11,
      rw h5 at h4,
      rw← h10 at h11,
      rw full_extensionality at h11,
      simp_rw singleton1 at h11,
      have h12:= h11 t,
      simp at h12,
      exact h12,
    },
    {
      intros h13,
      rw h13 at *,
      exact hc,
    }
  end

lemma uscsubsetsc: ∀(a:M), USC a ⊆ SC a:=
  begin
    intros a,
    rw subset_definition,
    intros t,
    intros h4,
    rw usc at h4,
    cases h4 with c h5,
    cases h5 with h6 h7,
    rw h7 at *,
    rw sc_members,
    rw subset_definition,
    intros z,
    rw singleton1,
    intros h8,
    rw h8 at *,
    exact h6,
  end 


lemma oneNC: one ∈ NC M:=
  begin
    rw NC_members,
    use single (Λ:M),
    rw full_extensionality,
    intros t,
    rw one_members,
    split,
    {
      intros h,
      cases h with a h3,
      rw h3 at *,
      have h4:= similar_singletons M a (Λ:M),
      have h5:= xinNcx M (single (Λ:M)),
      have h6:= cardinals0 M (Nc M (single Λ)) (single Λ)(single a),
      apply h6,
      rw NC_members,
      use (single Λ),
      exact xinNcx M (single Λ),
      rw similar_symmetric,
      exact h4,
    },
    {
      intros h,
      rw Nc_members at h,
      have h4:= similar_to_singleton M t Λ h,
      exact h4,
    }
  end

lemma twoNC: (two:M) ∈ NC M:=
  begin
    have h4:= oneNC M,
    have h5:= successorNC M one h4,
    rw two_definition,
    apply h5,
    use {Λ, single Λ},
    rw← two_definition,
    rw two_members,
    use Λ, use single Λ,
    simp,
    intros h,
    rw full_extensionality at h,
    have h6:= h Λ,
    rw singleton1 at h6,
    simp at h6,
    have h7:= emptyset_axiom Λ,
    contradiction,
  end

lemma onelessdottwo : (one:M) ⋖ (two:M):= 
  begin
    rw lessdot_definition,
    have h3: single (Λ:M) ∈ one:=
      begin
        rw one_members,
        use (Λ:M),
      end,
    have h4: { (Λ:M), single (Λ:M)} ∈ two:=
      begin
        rw two_members,
        use (Λ:M),
        use (single (Λ:M)),
        simp,
        intros h4,
        rw full_extensionality at h4,
        have h5:= h4 (Λ:M),
        rw singleton1 at h5,
        simp at h5,
        have h6:= emptyset_axiom (Λ:M),
        contradiction,
      end,
    split,
    {
      rw ledot_definition,
      use (single (Λ:M)),
      use { Λ, single(Λ:M)},
      split,
      {
        rw one_members,
        use (Λ:M),
      },
      {
        split,
        {
          rw two_members,
          use (Λ:M), use (single (Λ:M)),
          simp,
          intros h,
          rw full_extensionality at h,
          have h3:= h (Λ:M),
          rw singleton1 at h3,
          simp at h3,
          have h4:= emptyset_axiom (Λ:M),
          contradiction,
        },
        {
          rw subset_definition,
          intros t,
          rw singleton1,
          intros h,
          rw h at *,
          rw pairing_axiom,
          simp,
        }
      }
    },
    {
      split,
      {
        intros h,
        rw ledot_definition at h,
        cases h with a h5,
        cases h5 with b h6,
        rcases h6 with ⟨ h7, h8, h9⟩,
        rw two_members at h7,
        cases h7 with A h10,
        cases h10 with B h11,
        rw one_members at h8,
        cases h8 with c h12,
        rw h12 at *,
        cases h11 with h13 h14,
        rw h14 at *,
        rw subset_definition at h9,
        have h15:= h9 A,
        have h16:= h9 B,
        rw pairing_axiom at h15,
        simp at h15,
        rw pairing_axiom at h16,
        simp at h16,
        rw singleton1 at h15 h16,
        rw h15 at *,
        rw h16 at *,
        contradiction,
      },
      {
        use single (Λ:M),
        use {Λ,single Λ},
        split,
        {
          exact h3,
        },
        {
          split,
          {
            exact h4,
          },
          {
            split,
            {
              rw subset_definition,
              intros t ht,
              rw singleton1 at ht,
              rw ht at *,
              rw pairing_axiom,
              simp,
            },
            {
              use single (Λ:M),
              rw minus_members,
              rw singleton1,
              split,
              {
                rw pairing_axiom,
                right,
                simp,
              },
              {
                intros h5,
                rw full_extensionality at h5,
                have h6:= h5 (Λ:M),
                rw singleton1 at h6,
                simp at h6,
                have h7:= emptyset_axiom (Λ:M),
                contradiction,
              }
            }
          }
        },
      }
    }
  end

lemma ledotone: ∀ (m:M), m ∈ NC M → m ⪯ one → (∃(u v:M), u ∈ m ∧ v ∈ u) → m = one:=
  begin
    intros m hm h3 h4,
    cases h4 with u h5,
    cases h5 with v h6,
    cases h6 with hu hv,
    rw full_extensionality,
    intros t,
    rw ledot_definition at h3,
    cases h3 with a h16,
    cases h16 with b h17,
    rcases h17 with ⟨ ha, h9, h10⟩,
    rw one_members at h9,
    cases h9 with p h11,
    rw h11 at *,
    have h13:= cardinals2 M m u a hm hu ha,
    unfold similar at h13,
    cases h13 with f h14,
    unfold similarity at h14,
    cases h14 with h15 h16,
    unfold oneone at h15,
    cases h15 with hmaps h17,
    unfold maps at hmaps,
    rcases hmaps with ⟨ h20, h21, h22, h23⟩,
    have h24:= h23 v hv,
    cases h24 with fv h25,
    cases h25 with hfv h26,
    have h27:= member_subset M a (single p) fv h10  hfv,
    rw singleton1 at h27,
    rw h27 at *,
    have h28: a = single p:=
      begin
        rw full_extensionality,
        intros z,
        rw singleton1,
        split,
        {
          intros hz,
          have h30:= member_subset M a (single p) z h10 hz,
          rw singleton1 at h30,
          exact h30,
        },
        {
          intros hz,
          rw hz at *,
          exact hfv,
        }
      end,
    rw h28 at *,
    have h29: single p ∈ one:=
      begin
        rw one_members,
        use p,
      end,
    have h30:= cardinalsdisjoint2 M m one (single p) hm (oneNC M) ha h29,
    rw h30, 
  end

lemma similartoinhabited: ∀(A u:M), similar M A u → (∃ (v:M),v ∈ A) → ∃(w:M),w∈ u:=
  begin
    intros A u h3 h4,
    unfold similar at h3,
    cases h3 with f h5,
    unfold similarity at h5,
    cases h5 with h6 h7,
    unfold oneone at h6,
    rcases h6 with ⟨ h7,h8,h9⟩,
    unfold maps at h7,
    rcases h7 with ⟨ h10, h11, h12, h13⟩,
    cases h4 with v h14,
    have h30:= h13 v h14,
    cases h30 with fv h31,
    cases h31 with hfv h32,
    exact ⟨ fv, hfv⟩,
  end 

lemma twototheone_helper: ¬exp2 M one ⪯ one:=
  begin
    intros h30,
    have h30copy:=h30,
    rw ledot_definition at h30,
    cases h30 with A h31,
    cases h31 with B h32,
    rcases h32 with ⟨ h33, h34, h35⟩,
    have h36:= NCexp2 M one (oneNC M) ⟨ A, h33⟩,
    have h60:= exp2uscsc M one h36,
    cases h60 with a h61,
    cases h61 with h62 h63,
    have h50: ∃ (v:M),v ∈ A:= 
      begin
        have h70:= cardinals2 M (exp2 M one) A (SC a) h36 h33 h63,
        rw similar_symmetric at h70,
        have h71: exists (u:M),u ∈ SC a:=
          begin
            use Λ,
            rw sc_members,
            exact empty_always_subset M a,
          end,
        exact similartoinhabited M (SC a) A h70 h71,
      end,
    cases h50 with v h51,
    have h40:= ledotone M (exp2 M one) h36 h30copy ⟨ A, v, ⟨ h33, h51⟩⟩ ,
    rw h40 at h63,
    have h64:= cardinals2 M one (USC a) (SC a) (oneNC M) h62 h63,
    have h65:= cantor M a,
    contradiction,
  end

lemma onelessdotexp2one: one ⋖ exp2 M one:=
  -- can't say exp2 M one is two
  begin
    rw lessdot_definition,
    have h2: exp2 M one ∈ NC M:=
      begin
        have h200:= NCexp2 M one (oneNC M),
        rw NC_members,
        use SC(single (Λ:M)),
        rw full_extensionality,
        intros t,
        rw exp2_members,
        split,
        { 
          intros h,
          cases h with a h2,
          have h39:= h2.1,
          have h4: ∃(k:M), a = single k:=
            begin
              have h40:= uscinone M a h39,
              exact h40,
            end,
          cases h4 with k h5,
          rw h5 at *,
          have h6:= usc_singleton M k,
          rw h6 at h2,
          have h7:= similar_singletons M k Λ,
          have h8:= cardinals0 M (Nc M (SC (single Λ))) (SC (single k)) t,
          apply h8,
          rw NC_members,
          use SC (single (Λ:M)),
          have h9:= cardinals0 M (Nc M (SC (single Λ))) (SC (single (Λ:M))) (SC (single k)),
          apply h9,
          rw NC_members,
          use SC (single (Λ:M)),
          exact xinNcx M (SC (single (Λ:M))),
          have h10:= scsimilar M (single k)(single (Λ:M)) h7,
          rw similar_symmetric,
          exact h10,
          cases h2 with h11 h12,
          rw similar_symmetric,
          exact h12,
        },
        {
          intros h40,
          use single (Λ:M),
          have h41:= usc_singleton M (Λ:M),
          rw h41,
          split,
          {
            rw one_members,
            use single (Λ:M),
          },
          {
            have h42:= cardinals2 M (Nc M (SC (single Λ))) t (SC (single (Λ:M))),
            apply h42,
            rw NC_members,
            use SC (single (Λ:M)),
            exact h40,
            exact xinNcx M (SC (single (Λ:M))),
          }
        }
      end,
    have h3:= exp2uscsc M one h2,
    cases h3 with a h4,
    split,
    {
      rw ledot_definition,
      use (USC a),
      use (SC a),
      split,
      {
        exact h4.1,
      },
      {
        split,
        {
          exact h4.2,
        },
        {
          exact uscsubsetsc M a,
        }
      }
    },
    {
      split,
      { exact twototheone_helper M,
      },
      {
        use USC a,
        use SC a,
        split,
        {
          exact h4.1,
        },
        {
          split,
          {
            exact h4.2,
          },
          {
            split,
            {
              exact uscsubsetsc M a,
            },
            {
              have h50:= uscinone M a (h4.1),
              cases h50 with t h51,
              rw h51 at *,
              use (Λ:M),
              rw minus_members,
              rw sc_members,
              split,
              {
                rw subset_definition,
                intros z hz,
                have h5:= emptyset_axiom z,
                contradiction,
              },
              {
                intros h6,
                rw usc at h6,
                cases h6 with c h7,
                cases h7 with h8 h9,
                rw full_extensionality at h9,
                have h10:= h9 c,
                rw singleton1 at h10,
                simp at h10,
                have h11:= emptyset_axiom c,
                contradiction,
              }
            }
          }
        }
      }
    },
  end

lemma mlessdotexp2m: ∀(m:M), m ∈ NC M  → (∃ (u:M), u ∈ exp2 M m) → m ⋖ exp2 M m:=
  begin
    intros m hm  h2,
    have hmcopy:= hm,
    have h4:= cardinalsinhabited2 M m hm,
    cases h2 with u h3,
    have h3copy:= h3,
    have h40:= NCexp2 M m hm ⟨ u, h3⟩,
    have h41:= exp2uscsc M m h40,
    cases h41 with a h5,
    cases h5 with ha h6,
    rw lessdot_definition,
    split,
    { 
      rw ledot_definition,
      use (USC a),
      use (SC a),
      split,
      {
        exact ha,
      },
      {
        split,
        {
          rw exp2_members,
          use a,
          exact ⟨ha, similar_reflexive M (SC a)⟩, 
        },
        {
          rw subset_definition,
          intros t ht,
          rw usc at ht,
          cases ht with q h9,
          cases h9 with h10 h11,
          rw h11 at *,
          rw sc_members,
          rw subset_definition,
          intros z hz,
          rw singleton1 at hz,
          rw hz at *,
          exact h10,
        }
      }
    },
    {
      split,
      {
        intros h400,
        have h40copy:= h400,
        have h55:= le2NC M (USC a) (exp2 M m) m h40 hm h400 ha,
        cases h55 with w h56,
        cases h56 with h57 h58,
        have h52:= cardinals2 M (exp2 M m) w (SC a) h40 h57 h6,
        have h60:= subsetusc M a w h58,
        cases h60 with c h61,
        rw h61 at *,
        have h62:= (usc_subset M c a).2 h58,
        have h50:= cantor2 M a c h62,
        contradiction,
      },
      {
        use (USC a), use (SC a),
        split,
        {
          exact ha,
        },
        {
          split,
          {
            rw exp2_members,
            use a,
            exact ⟨ ha, similar_reflexive M (SC a)⟩,
          },
          {
            split,
            {
              exact uscsubsetsc M a,
            },
            { 
              use (Λ:M),
              rw minus_members,
              rw sc_members,
              split,
              {
                exact empty_always_subset M a,
              },
              {
                intros h7,
                rw usc at h7,
                cases h7 with b h8,
                cases h8 with h9 h10,
                have h11: b ∈ single b:= 
                  begin
                    rw singleton1,
                  end,
                rw←h10 at h11,
                have h12:= emptyset_axiom b,
                contradiction, 
              }
            }
          }
        }
      }
    }  
  end

lemma xneqexp2x: ∀ (x:M), x ∈ NC M → ¬ (x = exp2 M x):=
  begin
    intros x hx h,
    have h4:= cardinalsinhabited2 M x hx,
    rw h at h4, 
    have h3:= mlessdotexp2m M x hx h4,
    rw← h at h3,
    have h5:= xnotlessdotx M x hx,
    contradiction,
  end

lemma subset_usc2: ∀ (x c:M), x ⊆ USC c → ∃(a:M), a ⊆ c ∧ x = USC a:=
  begin
    intros x c hx,
    use union x,
    split,
    {
      rw subset_definition,
      intros t ht,
      rw union_axiom at ht,
      cases ht with z h3,
      cases h3 with hz ht,
      have h4:= member_subset M x (USC c) z hx hz,
      rw usc at h4,
      cases h4 with a h5,
      cases h5 with ha h6,
      rw h6 at *,
      rw singleton1 at ht,
      rw ht at *,
      exact ha,
    },
    {
      have h40:= unionusc M x,
      rw full_extensionality,
      intros t,
      split,
      {
        intros ht,
        have h41:= member_subset M x (USC c) t hx ht,
        rw usc at h41,
        cases h41 with a h42,
        cases h42 with ha h43,
        rw h43 at *,
        rw usc,
        use a,
        simp,
        rw union_axiom,
        use t,
        rw h43,
        rw singleton1,
        simp,
        exact ht,
      },
      {
        intros h50,
        rw usc at h50,
        cases h50 with a h51,
        cases h51 with h52 h53,
        rw h53 at *,
        rw union_axiom at h52,
        cases h52 with z h53,
        cases h53 with hz ha,
        have h54:= member_subset M x (USC c) z hx hz,
        rw usc at h54,
        cases h54 with b h55,
        cases h55 with hb h56,
        rw h56 at *,
        rw singleton1 at ha,
        rw ha at *,
        exact hz,
      }
    }
  end

lemma kmcase1: ∀ (n k:M), n ∈ NC M → k ∈ NC M → n ⪯ one → one ⋖ k → n ⋖  k:=
-- case m = one of ledottransitive3, see below
  begin
    intros n k hn hk h3 h4,
    rw lessdot_definition at h4,
    rcases h4 with ⟨ h5, h6, h7⟩,
    cases h7 with a h8,
    cases h8 with b h9,
    rcases h9 with ⟨ h10, h11, h12, h13⟩,
    cases h13 with u h14,
    rw one_members at h10,
    cases h10 with c h15,
    rw minus_members at h14,
    cases h14 with h16 h17,
    rw h15 at *,
    rw singleton1 at h17,
    have h18:= ledottransitive M n one k hn (oneNC M) hk h3 h5,
    have h20: single c ∈ one:=
      begin
        rw one_members,
        use c,
      end,
    have h19:= le2NC M (single c) n one hn (oneNC M) h3 h20,
    cases h19 with e h21,
    cases h21 with h22 h23,
    have h24: e ⊆ b:=
      begin
        rw subset_definition,
        intros t ht,
        have h25:= member_subset M e (single c) t h23 ht,
        rw singleton1 at h25,
        rw h25 at *,
        have h26:= member_subset M (single c) b c h12,
        apply h26,
        rw singleton1,
      end,
    have h27: ¬ u ∈ e:=
      begin
        intros h28,
        have h29:= member_subset M e (single c) u h23 h28,
        rw singleton1 at h29,
        contradiction,
      end, 
    have h30: u ∈ b-e:=
      begin
        rw minus_members,
        exact ⟨ h16, h27⟩,
      end,
    rw lessdot_definition,
    split,
    {
      exact h18,
    },
    {
      split,
      { 
        intros h49,
        have h49copy:= h49,
        have h80:= le2NC M e k n hk hn h49 h22,
        cases h80 with p h81,
        cases h81 with h82 h83,
        have h84:= subset_transitive M p e b h83 h24,
        have h85:= ledottransitive M k n one hk hn (oneNC M) h49 h3,
        have h87: u ∈ b:= 
          begin
            rw minus_members at h30,
            cases h30 with h31 h32,
            exact h31,
          end,
        have h86:= ledotone M k hk h85 ⟨ b,⟨ u, ⟨ h11,h87⟩⟩⟩,
        rw h86 at *,
        rw one_members at h11 h82,
        cases h82 with C h830,
        cases h11 with d h840,
        rw h830 at *,
        rw h840 at *,
        have h85: C=d:=
          begin
            have h90: C ∈ single C:=
              begin
                rw singleton1,
              end,
            
            have h91:= member_subset M (single C) e C h83 h90,
            have h92:= member_subset M e (single d) C h24 h91,
            rw singleton1 at h92,
            exact h92,
          end,
        rw h85 at *,
        rw← h840 at h830,
        have h93: b-p = Λ:=
          begin
            rw full_extensionality,
            intros t,
            rw h830,
            rw minus_members,
            split,
            {
              intros h,
              contradiction,
            },
            {
              intros h,
              have h94:= emptyset_axiom t,
              contradiction,
            }
          end,
        have h95: ¬ u ∈ p:=
          begin
            intros h,
            rw← h840 at h83,
            rw h830 at h,
            have h96:= member_subset M b e u h83 h,
            contradiction,
          end,
        have h97: u ∈ b:=
          begin
            rw← h840 at h30,
            rw minus_members at h30,
            exact h30.1,
          end,
        rw h830 at h95,
        contradiction,
      },
      {
        use e,use b,
        exact ⟨ h22, h11, h24, ⟨ u, h30⟩⟩, 
      }
    }
  end

--lemma ledottransitive3: ∀ (n m k:M), n ∈ NC M → m ∈ NC M → k ∈ NC M →  
-- n ⪯ m → m ⋖ k → n ⋖  k:=
-- this can't be proved constructively!  
-- but the following lemma can, and enables us to get what we need.#check

lemma kmlessdotexp2m: ∀(k m:M), k ∈ NC M → m ∈ NC M → k ⪯ m → (∃ (u:M), u ∈ exp2 M m) → k ⋖ exp2 M m:=
  begin
    intros  k m hk hm hkm h2,  
    have h2copy:= h2,
    have hmcopy:= hm,
    have h4:= cardinalsinhabited2 M m hm,
    cases h2 with u h3,
    have hu:= h3,
    rw exp2_members at h3,
    cases h3 with a h5,
    cases h5 with ha h6,
    rw lessdot_definition,
    have h30:= le2NC M (USC a) k m hk hm hkm ha,
    cases h30 with c h31,
    cases h31 with hc h32,
    have h33:=  subset_usc2 M c a h32,
    cases h33 with q h34,
    cases h34 with hq h35,
    have h36: USC q ⊆ USC a:=
      begin
        have h37:= (usc_subset M q a).1 hq,
        exact h37,
      end,
    have h38:= hc,
    rw h35 at h38,
    have h63:= NCexp2 M m hm h2copy,
    split,
    {
      have h50:= mlessdotexp2m M m hm h2copy,
      rw lessdot_definition at h50,
      cases h50 with h51 h52,
      have h55:= NCexp2 M m hm h2copy,
      exact ledottransitive M k m (exp2 M m) hk hm h55 hkm h51,
    },
    { split,
      {
        intros h60,
        have h61: SC(a) ∈ exp2 M m:=
          begin
            have h62:= cardinals0 M (exp2 M m) u (SC a)h63 hu h6,
            exact h62,
          end,
        have h62:= le2NC M (USC q) (exp2 M m ) k h63 hk h60 h38,
        cases h62 with e h65, 
        cases h65 with h66 h67,
        have h64:= cardinals2 M (exp2 M m) e (SC a) h63 h66 h61,
        have h68:= subset_usc2 M e q h67,
        cases h68 with p h69,
        cases h69 with h70 h71,
        have h72:= h64,
        rw h71 at h72, 
        have h73:= subset_transitive M p q a h70 hq,
        have h74:= cantor2 M a p h73,
        contradiction,
      },
      {
        have h80:= exp2uscsc M m h63,
        cases h80 with A h81,
        cases h81 with h82 h83,
        have h84:=le2NC M (USC A) k m hk hm hkm h82,
        cases h84 with r h85,
        cases h85 with h86 h87,
        have h88:= subset_usc2 M r A h87,
        cases h88 with B h89,
        cases h89 with h90 h91,
        rw h91 at *,
        use USC B,
        use SC A,
        split,
        {
          exact h86,
        },
        {
          split,
          {
            exact h83,
          },
          { 
            have h88:= uscsubsetsc M A,
            have h89:= subset_transitive M (USC B)(USC A)(SC A) h87 h88,
            split,
            {
              exact h89,
            },
            { 
              use Λ,
              rw minus_members,
              rw sc_members,
              split,
              {
                exact empty_always_subset M A,
              },
              {
                intros h,
                rw usc at h,
                cases h with t h40,
                cases h40 with h41 h42,
                have h43: t ∈ single t:=
                  begin
                    rw singleton1,
                  end,
                rw← h42 at h43,
                have h44:=emptyset_axiom t,
                contradiction,
              }
            }
          }
        }
      }
    }
  end

lemma towergraphE1:  --towergraphE satisfies the first equation 
   ∀ (m:M), triple m zero m ∈ towergraphE M := 
  begin
    intro m,
    rw towergraphE_members,
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

lemma towergraphE2:  --towergraphE satisfies the second equation
  ∀ (m y z:M), triple m y z ∈ towergraphE M → (∃ u, u ∈ 𝕊 y) → 
  triple m (𝕊 y) ( exp2 M z) ∈ towergraphE M :=
  begin
    intros m y z h20,
    have hcopy := h20, 
    intro h22, 
    rw towergraphE_members M,  
    rw towergraphE_members at h20,
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

lemma towergraphEimpliesyinF: ∀ (m y z:M), triple m y z ∈ towergraphE M → y ∈ 𝔽 :=
  assume m y z,
  begin
    intro h,
    rw towergraphE_members M at h,
    cases h with h2 h3,
    exact h2,
  end
  
lemma towerEhelper: ∀ (m y z:M),  triple m y z ∈ towergraphE M → (y=zero ∧ z = m) ∨
∃ (u v w:M), y = 𝕊 u ∧ v ∈ y ∧ triple m u w ∈ towergraphE M ∧ z = exp2 M w :=

  begin 
    have base: ∀(m:M), triple m zero m ∈ W81E M:=    
      assume m, 
      begin
        rw W81E_members,
        use m , use zero, use m,
        split, 
        {
          exact refl (triple m zero m),
        },
        {
          split,
          {
            exact towergraphE1 M m,
          },
          {
            left,
            simp, 
          }
        }
      end,
    have step: ∀ (m y z:M), triple m y z ∈ W81E M → (∃ u, u ∈ 𝕊 y) → triple m  (𝕊 y)  (exp2 M z) ∈ W81E M :=
      begin 
        assume m y z,
        intro h2,
        rw W81E_members at h2,
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
          rw W81E_members M,
          use m,
          use 𝕊 zero,
          use exp2 M m,
          split,
          { 
            exact refl (triple m (𝕊 zero) (exp2 M m)),
          },
          {
            split,
            {
              rw towergraphE_members M,
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
          rw W81E_members M,
          use m, use 𝕊 y, use exp2 M z,
          split,
          { 
            simp,
          },
          {
            split,
            {
              exact towergraphE2 M m y z h11 h22, 
            },
            {
              right,
              use y,
              cases h22 with v h23,
              use v,
              use exp2 M w,
              rw← h21, 
              simp,
              exact ⟨ h23, h11⟩,
            }
          }
        }
      end,
    have conclusion: towergraphE M ⊆ W81E M:=
      begin
        rw subset_definition,
        intro t,
        intro h,
        have h2:= towergraphE_members2 M t h,
        cases h2 with m h3,
        cases h3 with y h4,
        cases h4 with z h5,
        rw h5 at *,
        rw towergraphE_members M at h,
        cases h with h6 h7,
        specialize h7 (W81E M),
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
    have h1: y ∈ 𝔽 := towergraphEimpliesyinF M m y z h2, 
    have h3:= member_subset M (towergraphE M) (W81E M) (triple m y z) conclusion h2,
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
        rw W81E_members at h3,
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
      rw W81E_members at h3,
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


lemma towermapsE: ∀ (m y:M), y ∈ 𝔽 → ∃(z:M), triple m y z ∈ towergraphE M:=
  begin
    have base: (zero:M) ∈ Z_towerE_defined M:=
      begin
        rw Z_towerE_defined_members M,
        split,
        {
          exact (zeroF M),
        },
        {
          intro m,
          use m,
          rw towergraphE_members,
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
    have step: ∀(y:M), y ∈ Z_towerE_defined M → (∃(u:M), u ∈ 𝕊 y) → 𝕊 y ∈ Z_towerE_defined M:=
      assume y,
      begin
        intros h1 h2,
        rw Z_towerE_defined_members,
        rw Z_towerE_defined_members at h1,
        cases h1 with h3 h4,
        split,
        {
          exact successorF M y h3 h2, 
        },
        {
          intro m,
          specialize h4 m,
          cases h4 with z h5, 
          use exp2 M z,
          exact towergraphE2 M m y z h5 h2,
        }
      end, 
    intros m y h, 
    rw F_members at h, 
    specialize h ( Z_towerE_defined M),
    have h3:= h (and.intro base  step), 
    rw ( Z_towerE_defined_members M) at h3, 
    cases h3 with h5 h6, 
    exact h6 m, 
  end 

lemma towerE_singlevalued: ∀ (y x z w:M ), triple x y z ∈ towergraphE M → 
triple x y w ∈ towergraphE M → z = w := 
  begin 
    have base: zero ∈ Z82E M:=
      begin
        rw Z82E_members,
        split,
        { 
          exact zeroF M,
        },
        { 
          intros m z w,
          intro h,
          intro h7,
          have h2:= towerEhelper M m zero z h, 
          have h12:= towerEhelper M m zero w h7, 
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
              have h2:= towerEhelper M m zero z h, 
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

    have step: ∀(y:M),  y ∈ Z82E M → (∃ u, u ∈ 𝕊 y) → 𝕊 y ∈ Z82E M:=
      assume y,
      begin 
        intros  h1 h2,
        rw Z82E_members M at h1,
        have h135:= h1,
        cases h135 with h136 h137,
        have h := h136,
        rw Z82E_members M,
        split,
        {
          exact successorF M y h h2,
        },
        {  
          intros m z Z,
          cases h1 with h3 h4,
          --specialize h4 m z Z,
          intro h5,
          have h6:= towerEhelper M m (𝕊 y) z h5, 
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
            have h26:= towerEhelper M m (𝕊 y) Z h16,
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
                  rw towergraphE_members at h35copy,
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
                  rw towergraphE_members at h14copy,
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
    rw towergraphE_members at hcopy, 
    cases hcopy with h h4,
    rw F_members y at h,
    specialize h (Z82E M), 
    have h20:= h ⟨ base, step⟩,
    rw Z82E_members at h20,
    cases h20 with h21 h22,
    have h23:= h22 x z w h2,
    exact h23, 
  end 


lemma towerE_base_equation: ∀( m:M), tower M m zero = m  := 
  assume  m,
  begin
    rw full_extensionality,
    intro t,
    rw tower_members M, 
    split,
    { 
      intro h2,
      cases h2 with z h3,
      cases h3 with h4 h5,
      have h6:=  towerEhelper M m zero z  h4, 
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
      exact ⟨ towergraphE1 M m, h2⟩, 
    }
  end

lemma tower_introduction: ∀ (m z y:M), y∈ 𝔽 → ( triple m y z ∈ towergraphE M ↔ z = tower M m y):=
  begin 
    have base: (zero:M) ∈ Z83E M:=
      begin 
        rw Z83E_members M,
        split,
        {
          exact zeroF M, 
        },
        {
          intros m z,
          rw towerE_base_equation M m,
          split,
          {
            intro h,
            have h2:= towerEhelper M m zero z h,
            cases h2 with h3 h4,
            {
               exact h3.right, 
            },
            {
              cases h4 with p h5,
              cases h5 with q h6,
              cases h6 with r h7,
              rcases h7 with ⟨ h8, h9, h10, h11⟩,
              have h12: p ∈ 𝔽 := towergraphEimpliesyinF M m p r  h10, 
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
            exact towergraphE1 M m,
          }
        }
      end, 
    have step: ∀(y:M), y ∈ Z83E M → (∃ u, u ∈ 𝕊 y) → 𝕊 y ∈ Z83E M:=
      assume y,
      begin
        intros h h2,
        rw Z83E_members M at h,
        rw Z83E_members M,
        cases h with h3 h4,
        split,
        {
          exact successorF M y h3 h2,
        },
        { 
          intros m w,   -- formula (54) in the paper 
          have h5: triple m (𝕊 y) w ∈ towergraphE M ↔ w = exp2 M (tower M m y):=
            begin
              split,
              {
                intro h6,
                have h7:= towerEhelper M m (𝕊 y) w h6,
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
                  have h18:= towergraphEimpliesyinF M m u p h15,
                  have h116:= (successoroneone M y u h3 h18 h2 ⟨ v, h14⟩).mpr h13,
                  rw← h116 at *,
                  rw h4 m p  at h15, 
                  rw← h15,
                  exact h16,
                }
              },
              {
                intro h5,
                have h6:= towergraphE2 M m y (tower M m y),
                specialize h4 m (tower M m y),
                simp at h4,
                have h7:= h6 h4 h2,
                rw h5, 
                exact h7, 
              }
            end,
          have h6: w = tower M m (𝕊 y) ↔ w = exp2 M (tower M m y):=
            begin
              set p:= exp2 M (tower M m y) with h8,
              have h9:  triple m (𝕊 y) p ∈ towergraphE M:=
                begin 
                  specialize h4 m (tower M m y),
                  simp at h4, 
                  have h10:= towergraphE2 M m y (tower M m y) h4 h2,
                  rw h8,
                  exact h10, 
                end, 
              split,
              {
                intro h7,
                rw full_extensionality at h7,
                simp_rw tower_members at h7,
                rw full_extensionality,
                intro t,
                split,
                {
                  specialize h7 t,
                  intro h10,
                  rw h7 at h10,
                  cases h10 with q h11,
                  cases h11 with h12 h13,
                  have h14:= towerE_singlevalued M (𝕊 y) m p q h9 h12,
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
                  rw tower_members M,
                  use p,
                  exact ⟨ h5, h11⟩, 
                },
                {
                  intro h11, 
                  rw tower_members at h11,
                  cases h11 with z h12,
                  cases h12 with h13 h14,
                  have h15:= towerE_singlevalued M (𝕊 y) m p z h5 h13,
                  rw h15 at *,
                  exact h14, 
                } 
              }, 
            end,
          rw h6,
          exact h5, 
        }
      end,
    have h100: ∀(y:M), y ∈ 𝔽 → y ∈ Z83E M:=
      assume y,
      begin
        intro h,
        rw F_members y at h, 
        specialize h  (Z83E M),
        have h2:= h ⟨ base, step⟩, 
        exact h2,
      end,
    intros m z y,
    specialize h100 y,
    rw Z83E_members at h100,
    intro h300,
    have h301:= h100 h300, 
    cases h301 with h302 h303,
    specialize h303 m z,
    exact h303,
  end 

lemma towerE_recursion_equation: ∀(m y:M),  y ∈ 𝔽 → (∃ u, u ∈ (𝕊 y)) → tower M m (𝕊 y) = exp2 M (tower M m y) :=
  assume m y,
  begin
    intros h1 h2, 
    have h3: triple m (𝕊 y) (tower M m (𝕊 y)) ∈ towergraphE M:=  
      begin
        rw tower_introduction M m (tower M m (𝕊 y)) (𝕊 y) (successorF M y h1 h2),        
      end,
    have h4:= towerEhelper M m (𝕊 y) (tower M m (𝕊 y)) h3,
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
      have h14:= towergraphEimpliesyinF M m u w h12,
      have h113:= (successoroneone M y u h1 h14 h2 ⟨ v, h11⟩).mpr h10,
      rw← h113 at *,
      rw tower_introduction M m w y h1 at h12,   
      rw← h12,
      exact h13,
    }
  end

lemma zeroledotx:  ∀(x:M),x ∈ NC M → zero ⪯ x:=
  begin
    intros x hx,
    have h43:= hx,
    rw NC_members at hx,
    cases hx with y h2,
    rw ledot_definition,
    have h4:= cardinalsinhabited2 M x h43,
    cases h4 with b h5,
    use Λ, use b,
    split,
    {
      rw zero_members,
    },
    {
      split,
      { exact h5,
      },
      {
        rw subset_definition,
        intros t ht,
        have h6:= emptyset_axiom t,
        contradiction,
      }
    }
  end

lemma towerENC:  ∀ (m:M), m ∈ NC M → ∀ (y:M), y ∈ 𝔽 →  (∃ (u:M), u ∈ tower M m y) →   tower M m y ∈ NC M := 
  begin
    intros m hm, 
    have base: (zero:M) ∈ Z_towerENC M m:=
      begin
        rw Z_towerENC_members,
        split,
        {
          exact zeroF M,
        },
        { intros h,
          rw towerE_base_equation M m at *,
          exact hm,       
        }
      end,
    have step: ∀ (y:M), y ∈ Z_towerENC M m → (∃ u, u ∈ 𝕊 y) → 𝕊 y ∈ Z_towerENC M m:=
      assume y,
      begin
        intros h2 h, 
        rw Z_towerENC_members at *,
        have hsy:= successorF M y h2.1 h,
        cases h2 with hy h4,
        split,
        {
          exact hsy,
        },
        { 
          intros h8,
          have h9:= towerE_recursion_equation M m y hy h,
          rw h9 at h8,
          have h8copy:= h8,
          cases h8 with u h20,
          rw exp2_members at h20,
          cases h20 with a h10,
          cases h10 with h11 h12,
          have h13:= h4 ⟨ USC a, h11⟩, 
          rw h9,
          have h14:= NCexp2 M (tower M m y) h13 h8copy , 
          exact h14,
        }
      end,
    intros y h,  
    rw F_members at h, 
    specialize h ( Z_towerENC M m),
    have h3:= h (and.intro base  step), 
    rw ( Z_towerENC_members M m) at h3, 
    cases h3 with h5 h6, 
    exact h6, 
  end

lemma two_ledot_exp2one: two ⪯ exp2 M one:=
  begin
    set a:= {(Λ:M), single (Λ:M)} with adef,
    have h3: USC a ∈ two:= 
      begin
        rw two_members,
        use single Λ,
        use single (single Λ),
        split,
        {
          intros h,
          rw full_extensionality at h,
          specialize h (single Λ),
          have h20: single (Λ:M) ∈ single (single Λ):=
            begin
              rw singleton1,
            end, 
          have h21:= h.2 h20,
          rw singleton1 at h21,
          have h22: (Λ:M) ∈ single Λ:= 
            begin
              rw singleton1,
            end, 
          rw h21 at h22,
          have h23:= emptyset_axiom (Λ:M),
          contradiction,   
        },
        {
          rw adef,
          rw full_extensionality,
          intros t,
          rw usc,
          split,
          {
            intros h42,
            cases h42 with c h43,
            cases h43 with h44 h45,
            rw pairing_axiom at h44,
            cases h44 with h46 h47,
            {
              rw h46 at *,
              rw pairing_axiom,
              left,
              exact h45,
            },
            {
              rw h47 at *,
              rw pairing_axiom,
              right,
              exact h45,
            }
          },
          {
            intros h50,
            rw pairing_axiom at h50,
            cases h50 with h50 h51,
            {
              rw h50 at *,
              use (Λ:M),
              simp,
              rw pairing_axiom,
              left,
              simp,
            },
            {
              use single (Λ:M),
              split,
              {
                rw pairing_axiom,
                right,
                simp,
              },
              {
                exact h51,
              }
            }
          }
        }
      end,
    have h4: SC (single (Λ:M)) ∈ exp2 M one:= 
      begin
        rw exp2_members,
        use single (Λ:M),
        split,
        {
          rw one_members,
          have h54:= usc_singleton M (Λ:M),
          use single (Λ:M),
          rw h54,
        },
        {
          exact similar_reflexive M (SC (single (Λ:M))),
        }
      end,
    have h5: USC (single (Λ:M)) ⊆ SC (single (Λ:M)):=
      begin
        rw subset_definition,
        intros z hz,
        rw usc at hz,
        cases hz with t h6,
        cases h6 with h7 h8,
        rw h8,
        rw sc_members,
        rw subset_definition,
        intros w hw,
        rw singleton1 at hw,
        rw hw at *,
        rw singleton1,
        rw singleton1 at h7,
        exact h7,
      end, 
    rw ledot_definition,
    have h11:= usc_singleton M (Λ:M),
    have h12: a ⊆  SC (single (Λ:M)):=
      begin
        rw subset_definition,
        intros z hz,
        rw adef at hz,
        rw pairing_axiom at hz,
        rw sc_members,
        cases hz with h20 h21,
        {
          rw h20,
          exact empty_always_subset M (single (Λ:M)),
        },
        { 
          rw h21 at *,
          exact subset_reflexive M (single (Λ:M)),
        }
      end,
    have h30: a ∈ two:=
      begin
        rw two_members,
        use Λ, use (single Λ),
        rw adef,
        simp,
        intros h31,
        rw full_extensionality at h31,
        have h32:= h31 (Λ:M),
        rw singleton1 at h32,
        simp at h32,
        have h33:= emptyset_axiom (Λ:M),
        contradiction,
      end,
    use a,
    use SC (single (Λ:M)),
    exact ⟨ h30, h4, h12⟩,
  end

lemma  mplusone_ledot_exp2m: ∀ (m:M),  m ∈ 𝔽  → (∃ (u:M), u ∈ exp2 M m) →((𝕊 m) ⪯  exp2 M m)  :=
  begin
    intros m h2 h3,
    cases h3 with u h4,
    rw exp2_members at h4,
    cases h4 with a h5,
    cases h5 with h6 h7,
    have h80: m = one ∨ ¬ m = one:=
      begin
        have h81:= FregeNdecidable M,
        rw decidable_members at h81,
        have h82:= h81 m one ⟨ h2, oneF M⟩,
        exact h82,
      end, 
    cases h80 with h83 h84,
    {
      have h85:= two_ledot_exp2one M,
      rw h83,
      rw two_definition at h85,
      exact h85,   
    },
    -- from now on m ≠ one
    have h8: SC a ∈ exp2 M m:=
      begin
        rw exp2_members,
        use a,
        exact ⟨ h6, similar_reflexive M (SC a)⟩,
      end,
    rw ledot_definition,
    have h12: ∃ (p:M), p ⊆ a ∧ ¬ p ∈ USC a := 
      begin
        use a,
        split,
        {
          exact subset_reflexive M a,
        },
        {
          intros h40,
          rw usc at h40,
          cases h40 with w h41,
          cases h41 with h42 h43,
          rw h43 at *,
          have h44: USC (single w) = single (single w):=
            begin
              rw full_extensionality,
              intros t,
              rw usc,
              rw singleton1,
              split,
              {
                intros h50,
                cases h50 with A h51,
                rw singleton1 at h51,
                cases h51 with h52 h53,
                rw h52 at *,
                rw h53 at *,
              },
              {
                intros h55,
                rw h55 at *,
                use w,
                simp,
                rw singleton1,
              }
            end,
          rw h44 at *,
          have h60: single (single w) ∈ one:=
            begin
              rw one_members,
              use single w,
            end,
          have h61: m= one := 
            begin
              have h62:=  cardinalsdisjoint M m one (single (single w)) h2 (oneF M),
              apply h62,
              rw intersection_axiom,
              exact ⟨ h6, h60⟩,
            end,
          contradiction,  --since m ≠ one
        }
      end,
    cases h12 with p h13,
    use ((USC a) ∪ single p), 
    use SC a,
    split,
    {
      rw successor_members,
      use USC a, use p,
      simp,
      split,
      { 
        exact h6,
      },
      {
        exact h13.2,
      },  
    },
    {
      split,
      {
        exact h8,
      },
      {
        rw subset_definition,
        intros t ht,
        rw binary_union_axiom at ht,
        rw sc_members,
        cases ht with h30 h31,
        {
          rw usc at h30,
          cases h30 with r h32,
          cases h32 with h33 h34,
          rw h34 at *,
          rw subset_definition,
          intros z,
          rw singleton1,
          intros h35,
          rw h35 at *,
          exact h33,
        },
        { 
          rw singleton1 at h31,
          rw h31 at *,
          exact h13.1,
        }
      }
    },
 end

lemma towerEincreasing: ∀ (m:M), m ∈ NC M  → ∀ (y:M), y ∈ 𝔽 → (∃ u, u ∈ tower M m y) → y ⪯ tower M m y:=
  assume m,
  begin
    have base:zero ∈  Z87FE M m:=
      begin
        rw Z87FE_members,
        split,
        {
          exact zeroF M,
        },
        {
          intros h h2,
          rw towerE_base_equation M,
          exact zeroledotx M m h,
        }
      end,
    have step: ∀(y:M),  y ∈ Z87FE M m → (∃ u, u ∈ 𝕊 y) → 𝕊 y ∈ Z87FE M m :=
      begin
        intros y h3 h4,
        rw Z87FE_members M,
        rw Z87FE_members at h3, 
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
          rw towerE_recursion_equation M m y h5 h4 at h10,
          have h10copy:= h10,
          rw exp2_members at h10,
          cases h10 with a h11,
          cases h11 with h12 h13,
          have h14: ∃ u, u ∈ tower M m y:= ⟨ USC a, h12⟩, 
          have h15:= h6 h7 h14,
          have h16:= towerENC M m h7 y h5 h14, 
          have h200:= FtoNC M y h5,
          have h17:= exporderNC M y (tower M m y) h200 h16 h15 ⟨ u, h10copy⟩,
          cases h17 with h18 h19,
          have h38: tower M m y ∈ NC M := towerENC M m h7 y h5 h14,
          have h20:= exporderNC M y (tower  M m y) h200 h38 h15 ⟨ u, h10copy⟩, 
          cases h20 with h21 h22, 
          have h23:= cardinalsinhabited2 M (tower M m y) h38,
          have h224:= cardinalsinhabited2 M (exp2 M y) h21,
          have h24:= mlessdotexp2m M y h200 h224,
          have h225:= FtoNC M y h5,
          have h226:= cardinalsinhabited2 M (exp2 M y) h21,
          have h25: exp2 M y ∈ NC M := NCexp2 M y h225 h226,
          have h27:= successorF M y h5 h4,
          have h227:= FtoNC M (𝕊 y) h27,
          have h29:= towerE_recursion_equation M m y h5 h4,
          have h28:= towerENC M m h7 (𝕊 y) h27 h9copy,
          rw h29 at h28,
          rw h29,
          have h30: 𝕊 y ⪯ exp2 M y:= 
            begin
              have h218:= cardinalsinhabited2 M (exp2 M y) h18,
              have h34:= mplusone_ledot_exp2m M y h5 h218, 
              exact h34,
            end,
          have h32:= ledottransitive M (𝕊 y) (exp2 M y) (exp2 M (tower M m y))  h227 h25 h28 h30 h22,
          exact h32,
        }
      end, 
    intros h2 y h, 
    rw F_members y at h,
    specialize h (Z87FE M m),
    have h200:= h ⟨ base, step⟩,
    rw Z87FE_members at h200,
    cases h200 with h201 h202,
    exact h202 h2,   
  end

lemma exp2_inhabited: ∀(m:M),  ((∃ a, (USC a ∈ m))  ↔ ∃ b, (b ∈ exp2 M m)):=
  assume m,
  begin
    split,
    {
      intro h2,
      cases h2 with a h3,
      use SC a,
      rw exp2_members M,
      use a,
      exact ⟨ h3, similar_reflexive M (SC a)⟩,
    },
    {
      intro h2,
      cases h2 with b h3,
      rw exp2_members at h3,
      cases h3 with a h4,
      cases h4 with h5 h6,
      use a,
      exact h5,
    }
  end

lemma towerinNC: ∀ (m:M), m ∈ NC M → ∀(y:M),y ∈ 𝔽 → (∃(u:M), u ∈ tower M m y) → tower M m y ∈ NC M:=
  begin
    intros m hm,
    have base: zero  ∈ ZIinNC M m:=
      begin
        rw ZIinNC_members,
        split,
        {
          exact zeroF M,
        },
        {
          intros h3 h4,
          rw towerE_base_equation,
          exact hm,
        }
      end,
    have step: ∀( y:M), y ∈ ZIinNC M m → (∃(u:M), u ∈ 𝕊 y) → 𝕊 y ∈ ZIinNC M m:=
      begin
        intros  y h5 h6,
        rw ZIinNC_members M m,
        rw ZIinNC_members M m at h5,
        cases h5 with h7 h8,
        split,
        {
          exact successorF M y h7 h6,
        },
        {
          intros h9 h10,
          have h11:= h8 h9,
          cases h10 with u h12,
          rw towerE_recursion_equation M m y h7 h6 at h12,
          rw towerE_recursion_equation M m y h7 h6,
          have h13:= (exp2_inhabited M (tower M m y)).2 ⟨ u, h12⟩ ,
          cases h13 with a h14,
          have h15:= h11 ⟨ USC a, h14⟩,
          have h16:= NCexp2def M (tower M m y) a h15 h14,
          rw h16,
          rw NC_members,
          use (SC a),
        }
      end, 
    intros y hy,
    rw F_members at hy,
    specialize hy (ZIinNC M m),
    have h12:= hy ⟨base,step⟩,
    rw ZIinNC_members at h12,
    cases h12 with h13 h14,
    have h15:= h14 hm,
    exact h15, 
  end     

lemma zero_ledot_x: ∀ (x:M), x ∈ NC M → zero ⪯ x:=
  begin
    intros x hx,
    have hxcopy:= hx,
    rw NC_members at hxcopy,
    have h4:= cardinalsinhabited2 M x hx,
    cases h4 with b h3,
    rw ledot_definition,
    use (Λ:M), use b,
    rw zero_members,
    simp,
    have h5: (Λ:M) ⊆ b:=
      begin
        rw subset_definition,
        intros t ht,
        have h6:= emptyset_axiom t,
        contradiction,
      end,
    exact ⟨ h3, h5⟩,
  end

lemma scissingle: ∀ (a q:M), SC a = single q → a = (Λ:M):=
  begin
    intros a q h3,
    rw full_extensionality at h3,
    have h4:= h3 a,
    rw sc_members at h4,
    have h5:= subset_reflexive M a,
    rw h4 at h5,
    rw singleton1 at h5,
    rw h5 at *,
    have h6:= h3 (Λ:M),
    have h7: Λ ∈ SC q:=
      begin
        rw sc_members,
        rw subset_definition,
        intros t,
        intros h,
        have h8:= emptyset_axiom t,
        contradiction,
      end,
    rw h6 at h7,
    rw singleton1 at h7,
    rw sym, 
    exact h7,
  end

lemma logone: ∀(m:M), m ∈ NC M → exp2 M m = one → m = zero:=
  begin
    intros m hm h4,
    have h4copy:= h4,
    rw full_extensionality at h4,
    rw full_extensionality,
    intros t,
    rw zero_members,
    have h6:= oneNC M,
    have h7:= h6,
    rw← h4copy at h7,
    have h5:=exp2uscsc M m h7,
    cases h5 with a h8,
    cases h8 with h20 h9,
    have h10:= h4 (SC a),
    rw h10 at h9,
    rw one_members at h9,
    cases h9 with q h11,
    have h12:= scissingle M a q h11,
    rw h12 at *,
    have h13:= usc_empty M,
    rw h13 at *,
    split,
    {
      intros ht,
      have h21:= cardinals2 M m (Λ:M) t hm h20 ht,
      have h22:= similar_to_empty M t,
      rw similar_symmetric at h21,
      rw h22 at h21,
      exact h21,
    },
    {
      intros h23,
      rw h23 at *,
      exact h20,
    }
  end 

lemma towernotzero: ∀ (m y:M), y ∈ 𝔽 →  tower M m y = zero → m = zero ∧ y = zero:=
  begin
    intros m y hy,
    have h3:= FregeNdecidable M,
    rw decidable_members at h3,
    have h4:= h3 y zero ⟨ hy,zeroF M⟩,
    have h5:= h3 y one ⟨ hy, oneF M⟩,
    cases h4 with h6 h7,
    {
      rw h6 at *,
      rw towerE_base_equation,
      intros h,
      rw h at *,
      simp,
    },
    {
      have h10:= nonzeroissuccessor M y hy h7,
      cases h10 with p h11,
      cases h11 with hp hsp,
      rw hsp at *,
      rw towerE_recursion_equation,
      intros h,
      rw full_extensionality at h,
      have h20:= h (Λ:M),
      have h21: (Λ:M) ∈ zero:=
        begin
          rw zero_members,
        end,
      rw← h20 at h21,
      rw exp2_members at h21,
      cases h21 with a h22,
      cases h22 with h23 h24,
      rw similar_symmetric at h24,
      have h25:= (similar_to_empty M (SC a)).1 h24,
      have h26: (Λ:M) ∈ SC a:=
        begin
          rw sc_members,
          exact empty_always_subset M a,
        end,
      rw h25 at h26,
      have h27:= emptyset_axiom (Λ:M),
      contradiction,
      exact hp,
      exact cardinalsinhabited M (𝕊 p) hy,
    }
  end
    
lemma sixpointfourNC: ∀ (m:M), m ∈ NC M → ∀ (y:M), y ∈ 𝔽  → tower M m y ∈ NC M  → m ⪯ tower M m y:=
  assume m hm, 
  begin 
    have base: (zero:M) ∈ ZsixpointfourE M m, 
      begin 
        rw ZsixpointfourE_members M, 
        split,
        { 
          exact (zeroF M),
        },
        {   
          rw towerE_base_equation,
          intros h3,
          exact ledotreflexive M m hm , 
        }
      end, 
    have step: ∀(y:M),  y ∈ ZsixpointfourE M m →(∃ u, u ∈ 𝕊 y) → 𝕊 y ∈ ZsixpointfourE M m:=
      begin
        intros y h2 h,
        rw ZsixpointfourE_members at h2,
        rw ZsixpointfourE_members,
        cases h2 with h3 h4, 
        split,
        {
          exact successorF M y h3 h, 
        },
        { 
          intros h8,
          have h9:= cardinalsinhabited2 M (tower M m (𝕊 y)) h8, 
          rw towerE_recursion_equation M m y h3 h, 
          rw towerE_recursion_equation M m y h3 h at h8,
          rw towerE_recursion_equation M m y h3 h at h9, 
          have h10:= h9,
          cases h10 with x h12,
          rw exp2_members M at h12, 
          cases h12 with a h13,
          cases h13 with h14 h15, 
          have h30:= towerinNC M m hm y h3 ⟨ USC a, h14⟩, 
          have h6 := mlessdotexp2m M (tower M m y) h30 h9, 
          rw  lessdot_definition at h6, 
          cases h6 with h20 h21,
          have h22:= h4 h30, 
          have h23:= ledottransitive M m (tower M m y) (exp2 M (tower M m y))  hm h30 h8 h22 h20, 
          exact h23,
        }
      end, 
    intros y hy,  
    rw F_members at hy, 
    specialize hy ( ZsixpointfourE M m),
    have h3:= hy (and.intro base  step), 
    rw ( ZsixpointfourE_members M m) at h3, 
    cases h3 with h5 h6, 
    exact h6, 
  end

lemma exponentialsinhabited: ∀ (m:M), m ∈ NC M → u ∈ exp2 M m → ∃ (p:M),p ∈ u:=
  begin
    intros m hm hu,
    have h2:= NCexp2 M m hm ⟨ u, hu⟩,
    have h3:= exp2uscsc M m h2,
    cases h3 with a h4,
    cases h4 with h5 h6,
    have h7:= cardinals2 M (exp2 M m) u (SC a) h2 hu h6,
    rw similar_symmetric at h7,
    unfold similar at h7,
    have h8: a ∈ SC a:=
      begin
        rw sc_members,
        exact subset_reflexive M a,
      end,
    cases h7 with f h9,
    unfold similarity at h9,
    cases h9 with honeone honto,
    unfold oneone at honeone,
    rcases honeone with ⟨ h10, h11, h12⟩,
    unfold maps at h10,
    rcases h10 with ⟨ h13, h14, h15, h16⟩,
    have h17:= h16 a h8,
    cases h17 with fa h18,
    cases h18 with h19 h20,
    use fa,
    exact h19,
  end

lemma ledotfinite: ∀ (n m:M), n ∈ 𝔽 → m ∈ 𝔽 → (n ≤ m ↔ n ⪯ m) :=
  begin
    intros n m hn hm,
    split,
    {
      -- left to right,
      intros h3,
      rw ledot_definition,
      rw le_definition at h3,
      cases h3 with a h4,
      cases h4 with b h5,
      use a, use b,
      exact ⟨ h5.1, h5.2.1,h5.2.2.1⟩,
    },
    {
      intros h4,
      rw ledot_definition  at h4,
      rw le_definition,
      cases h4 with a h5,
      cases h5 with b h6,
      use a, use b,
      rcases h6 with ⟨ h7, h8, h9⟩,
      split,
      {
        exact h7,
      },
      {
        split,
        {
          exact h8,
        },
        {
          split,
          {
            exact h9,
          },
          {
            have hb:= finitecardinals1 M m b hm h8,
            have ha:= finitecardinals1 M n a hn h7,
            have h10:= finiteseparable M b a hb ha h9,
            rw union_commutative,
            exact h10,
          }
        }
      }
    }
  end

lemma lessdotfinite: ∀ (n m:M), n ∈ 𝔽 → m ∈ 𝔽 → (n < m ↔ n ⋖ m) :=
  begin
    intros n m hn hm,
    split,
    { --left to right
      intros h,
      rw lessdot_definition,
      have hcopy:= h,
      rw lessthan_definition at h,
      cases h with h2 h3,
      split,
      {
        exact (ledotfinite M n m hn hm).1 h2,
      },
      {
        split,
        {
          intros h4,
          have h5:= (ledotfinite M m n hm hn).2 h4,
          have h6:= finitetrichotomy2 M m n hm hn h5 h2,
          rw h6 at *,
          contradiction,
        },
        {
          rw le_definition at h2,
          cases h2 with a h10,
          cases h10 with b h11,
          use a, use b,
          rcases h11 with ⟨h12, h13, h14, h15⟩,
          split,
          {
            exact h12,
          },
          {
            split,
            {
              exact h13,
            },
            {
              split,
              {
                exact h14,
              },
              {
                have h21:= finitecardinals1 M n a hn h12,
                have h22:= finitecardinals1 M m b hm h13,
                have h20:= finitedif M b a h22 h21 h14,
                have h15:= empty_or_inhabited M (b-a) h20,
                cases h15 with h16 h17,
                {
                  rw h16 at h15,
                  rw x_union_empty at h15,
                  rw h15 at *,
                  have h19: a ∈ m ∩ n:=
                    begin
                      rw intersection_axiom,
                      exact ⟨ h13, h12⟩,
                    end,
                  have h20:= cardinalsdisjoint M m n a hm hn h19,
                  rw h20 at *,
                  contradiction,
                },
                {
                  exact h17,
                }
              }
            }
          }
        }
      }
    },
    { --right to left
      intros h30,
      rw lessdot_definition at h30,
      cases h30 with h31 h32,
      have h33:= (ledotfinite M n m hn hm).2 h31,
      rw lessthan_definition,
      split,
      {
        exact h33,
      },
      {
        intros h34,
        rw h34 at *,
        cases h32 with h35 h36,
        contradiction,
      }
    }
  end

lemma mlessdotsuccessorm: ∀ (m:M), m ∈ 𝔽 → (∃ (u:M), u ∈ 𝕊 m) → m ⋖ 𝕊 m:=
  begin
    intros m hm hsm,
    have hsmcopy:= hsm,
    have hsmf:= successorF M m hm hsm,
    cases hsm with u h3,
    rw successor_members at h3,
    cases h3  with a h4,
    cases h4 with c h5,
    rcases h5 with ⟨ h6,h7, h8⟩,
    rw lessdot_definition,
    split,
    {
      rw ledot_definition,
      use a,
      use (a ∪ single c),
      split,
      {
        exact h6,
      },
      {
        split,
        {
          rw successor_members,
          use a, use c,
          simp,
          exact ⟨ h6, h7⟩,
        },
        {
          have h9:= subset_union M a a (single c) (subset_reflexive M a),
          exact h9,
        }
      }
    },
    {
      split,
      { 
        intros h,
        have h10:= ledotfinite M (𝕊 m) m hsmf hm,
        have h11:= h10.2 h,
        have h12:= xlessthansuccessorx M m hm hsmf,
        have h13:= le_transitive3 M (𝕊 m) m (𝕊 m) hsmf hm hsmf h11 h12,
        have h14:= xnotlessthanx M (𝕊 m) hsmf,
        contradiction,
      },
      {
        use a, use (a ∪ single c),
        split,
        {
          exact h6,
        },
        split,
        {
          rw successor_members,
          use a, use c,
          simp,
          exact ⟨ h6, h7⟩,
        },
        {
          split,
          {
            exact subset_union M a a (single c) (subset_reflexive M a),
          },
          {
            use c,
            rw minus_members,
            split,
            {
              rw binary_union_axiom,
              rw singleton1,
              simp,
            },
            {
              exact h7,
            }
          }
        }
      }
    }
  end

lemma noinsertionsNC: ∀ (n m:M), n ∈ NC M → m ∈ NC M → n ⋖ m → 𝕊 n ⪯ m:=
  begin
    intros n m hn hm h4,
    rw lessdot_definition at h4,
    rcases h4 with ⟨ h5, h6, h7⟩,
    cases h7 with a h8,
    cases h8 with b h9,
    rcases h9 with ⟨ h10, h11, h12, h13⟩,
    cases h13 with c h14,
    rw ledot_definition,
    use a ∪ (single c),
    use b,
    rw minus_members at h14,
    split,
    {
      rw successor_members,
      use a, use c,
      simp,
      exact ⟨ h10, h14.2⟩,
    },
    {
      split,
      {
        exact h11,
      },
      {
        rw subset_definition,
        intros t ht,
        rw binary_union_axiom at ht,
        rw singleton1 at ht,
        cases ht with h15 h16,
        {
          exact member_subset M a b t h12 h15,
        },
        {
          rw h16 at *,
          exact h14.1,
        }
      }
    }
  end

lemma ledotzero: ∀ (p:M), p ∈ NC M → p ⪯ zero → p = zero:=
  begin
    intros p hp h3,
    rw ledot_definition at h3,
    cases h3 with a h4,
    cases h4 with b h5,
    rcases h5 with ⟨h6, h7, h8⟩,
    rw zero_members at h7,
    rw h7 at *,
    have h9:= subset_of_empty M a,
    rw h9 at h8,
    rw h8 at *,
    have h10: (Λ:M) ∈ zero:= 
      begin
        rw zero_members,
      end,
    have h11:= cardinalsdisjoint2 M zero p (Λ:M) (zeroNC M) hp h10 h6,
    rw sym at h11,
    exact h11,
  end

lemma towerup2: ∀ (p:M), p ∈ NC M  → ∀ (y:M), y ∈ 𝔽 → 
(∃ (u:M), u ∈ tower M p y) → tower M p y ∈ NC M ∧ y ⪯  tower M p y:=
  assume p hp,
  begin
    have base: zero ∈ Z_towerup2 M p:=
      begin
        rw Z_towerup2_members M p,
        split,
        {
          exact zeroF M,
        },
        {
          intros h3,
          have h2:= towerE_base_equation M p,
          have h5: (Λ:M) ∈ zero:=
            begin
              rw zero_members,
            end,
          rw towerE_base_equation,
          split,
          { 
            exact hp,
          },
          {   
            rw ledot_definition,
            cases h3 with b h4,
            rw h2 at *,
            use Λ, use b,
            have h6:= empty_always_subset M b,
            exact ⟨ h5, h4, h6⟩,
          }
        }
      end,
    have step: ∀ (y:M), y ∈ Z_towerup2 M p → (exists(u:M), u ∈ 𝕊 y) → 𝕊 y ∈ Z_towerup2 M p:=
      begin
        intros y h21 h22,
        rw Z_towerup2_members at h21,
        cases h21 with hy h23,
        rw Z_towerup2_members,
        have h20:= towerE_recursion_equation M p y hy h22,
        split,
        {
          exact successorF M y hy h22,
        },
        {
          intros h25,
          have h25copy:= h25,
          simp_rw h20 at h25,
          cases h25 with w h26,
          have h26copy:= h26,
          rw exp2_members at h26,
          cases h26 with a h27,
          cases h27 with h28 h29,
          have h30:= towerinNC M p hp y hy ⟨ USC a, h28⟩,
          have h31:= NCexp2 M (tower M p y) h30 ⟨w,h26copy⟩,
          have h32:= h31,
          rw← h20 at h32,
          have h33:= h23 ⟨ USC a, h28 ⟩,
          cases h33 with h34 h35,
          have h36:= mlessdotsuccessorm M y hy h22,
          --have h37:= noinsertionsNC M y (tower M p y) (FtoNC M y hy) h30 h35,
          split,
          {
            exact h32,
          },
          { 
            have h131:= cardinalsinhabited2 M (exp2 M (tower M p y)) h31,
            have h130:= exporderNC M y (tower M p y) (FtoNC M y hy) h34 h35 h131,
            cases h130 with h133 h134,
            have h136:= cardinalsinhabited2 M (exp2 M y) h133,
            have h135:= mlessdotexp2m M y (FtoNC M y hy) h136,
            have h137:= noinsertionsNC M y (exp2 M y) (FtoNC M y hy) h133 h135,
            have h139: 𝕊 y ∈ NC M:=
              begin
                have h200:= successorF M y hy h22,
                have h201:= FtoNC M (𝕊 y) h200,
                exact h201,
              end,
            have h138:= ledottransitive M (𝕊 y) (exp2 M y)(exp2 M (tower M p y)) h139 h133 h31 h137 h134,
            rw towerE_recursion_equation,
            exact h138,
            exact hy,
            exact h22,
          }
        }
      end,
    intros y hy,
    rw F_members at hy,
    have h400:= hy (Z_towerup2 M p) ⟨ base, step⟩,
    rw Z_towerup2_members at h400,
    exact h400.2,
  end

lemma towerup: ∀ (p:M), p ∈ NC M →  (∃ (u v:M),u ∈ p ∧ v ∈ u ) → ∀ (y:M), y ∈ 𝔽 → 
(∃ (u:M), u ∈ tower M p y) → tower M p y ∈ NC M ∧ y ⋖ tower M p y:=
  assume p hncp hp,
  begin
    have base: zero ∈ Z_towerup M p:=
      begin
        rw Z_towerup_members M p,
        split,
        {
          exact zeroF M,
        },
        {
          intros h3,
          cases hp with u h401,
          cases h401 with v h404,
          cases h404 with h4 h405,
          have h2:= towerE_base_equation M p,
          rw← h2 at h4,
          rw towerE_base_equation M p at h4,
          have h5: (Λ:M) ∈ zero:=
            begin
              rw zero_members,
            end,
          have h6: (Λ:M) ⊆ u:=
            begin
              rw subset_definition,
              intros t ht,
              have h7:= emptyset_axiom t,
              contradiction,
            end,
         
          have h8: zero ⪯ p:=
            begin
              rw ledot_definition,
              use Λ, use u,
              exact ⟨ h5, h4, h6 ⟩,
            end,
          rw lessdot_definition,
          split,
          {
            rw towerE_base_equation,
            exact hncp,
          },
          { split,
            { 
              rw h2,
              exact h8,
            },
            { split,
              {
                intros h9,
                rw h2 at h9,
                have h10:= ledotzero M p hncp h9,
                rw h10 at *,
                rw zero_members at h4, 
                rw h4 at *,
                have h10:= emptyset_axiom v,
                contradiction,
              },
              {
                simp_rw towerE_base_equation,
                use (Λ:M),
                use u,
                split,
                {
                  rw zero_members,
                },
                {
                  split,
                  {
                    exact h4,
                  },
                  {
                    split,
                    {
                      have h10:= empty_always_subset M u,
                      exact h10,
                    },
                    { 
                      use v,
                      have h20:= x_minus_empty M u,
                      rw h20,
                      exact h405,
                    }
                  }
                }
              }
            }
          }
        }
      end,
    have step: ∀ (y:M), y ∈ Z_towerup M p → (exists(u:M), u ∈ 𝕊 y) → 𝕊 y ∈ Z_towerup M p:=
      begin
        intros y h21 h22,
        rw Z_towerup_members at h21,
        cases h21 with hy h23,
        rw Z_towerup_members,
        have h20:= towerE_recursion_equation M p y hy h22,
        split,
        {
          exact successorF M y hy h22,
        },
        {
          intros h25,
          have h25copy:= h25,
          simp_rw h20 at h25,
          cases h25 with w h26,
          have h26copy:= h26,
          rw exp2_members at h26,
          cases h26 with a h27,
          cases h27 with h28 h29,
          have h30:= towerinNC M p hncp y hy ⟨ USC a, h28⟩,
          have h31:= NCexp2 M (tower M p y) h30 ⟨w,h26copy⟩,
          have h32:= h31,
          rw← h20 at h32,
          have h33:= h23 ⟨ USC a, h28 ⟩,
          cases h33 with h34 h35,
          have h36:= mlessdotsuccessorm M y hy h22,
          have h37:= noinsertionsNC M y (tower M p y) (FtoNC M y hy) h30 h35,
          split,
          {
            exact h32,
          },
          {
            have h38:= successorF M y hy h22,
            have h39:= FtoNC M (𝕊 y) h38,
            have h40:=kmlessdotexp2m M (𝕊 y)(tower M p y) h39 h30 h37,
            rw towerE_recursion_equation,
            apply h40,
            have h41:= cardinalsinhabited2 M (exp2 M (tower M p y)) h31,
            exact h41,
            exact hy,
            exact h22,
          },
        }
      end,
    intros y hy,
    rw F_members at hy,
    have h400:= hy (Z_towerup M p) ⟨ base, step⟩,
    rw Z_towerup_members at h400,
    exact h400.2,
  end

#axioms_all