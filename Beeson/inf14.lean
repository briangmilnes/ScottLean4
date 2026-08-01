   
import inf13
variables (M:Type) [Model M] (a b x y z u v w X R W κ μ ℓ : M)
-- using ℓ where the source text has λ because you can't use λ for a variable.

open Model 

lemma notlessthan:  ∀ (y r:M), y ∈ 𝔽 → r ∈ 𝔽 → ((¬ (y < r)) ↔ r ≤ y):=
  assume y r,
  begin
    intros hy hr,
    rw lessthan_definition,
    have h4:= finitetrichotomy2 M y r hy hr,
    have h5:= Theorem2 M y r hy hr,
    cases h5 with h6 h7,
    cases h6 with h8 h9,
    {
      split,
      { 
        intro h9, 
        rw lessthan_definition at h8,
        cases h8 with h10 h11,
        have h12:= h4 h10,
        have h13:= h9 ⟨ h10, h11⟩, 
        contradiction, 
      },
      { intro h20,
        have h21:= le_transitive2 M y r y hy hr hy h8 h20, 
        have h22:= xnotlessthanx M y hy, 
        contradiction, 
      }
    },
    { 
      cases h9 with h10 h11,
      {
        rw h10 at *,
        simp at h7, 
        simp,
        exact le_reflexive M r hr, 
      },
      { 
        split,
        {
          intro h12, 
          rw lessthan_definition at h11,
          exact h11.left, 
        },
        {
          intro h12, 
          intro h13,
          cases h13 with h14 h15, 
          have h16:= le_transitive2 M r y r hr hy hr h11 h14, 
          have h17:= xnotlessthanx M r hr, 
          contradiction, 
        }
      }
    } 
  end  
 
lemma empty_minus: ∀ (x:M), Λ -x = Λ :=
  assume x,
  begin
    rw full_extensionality,
    intro t,
    rw minus_members,
    have h:= emptyset_axiom t,
    split,
    {
      intro h2,
      exact h2.left, 
    },
    {
      intro h3,
      contradiction,
    }
  end

lemma JbartoJ: ∀ (m:M),m ∈ 𝔽 → Jbar M m = (𝕁 M m ∪ (single m)):=
  assume m,
  begin
    intro h,
    rw full_extensionality,
    intro t,
    rw Jbar_members,
    rw binary_union_axiom,
    rw singleton1 M,
    rw J_members,
    rw lessthan_definition,
    split,
    {
      intro h2,
      cases h2 with h3 h4,
      have h5:= FregeNdecidable M,
      rw decidable_members M at h5,
      have h6:= h5 t m ⟨ h3, h⟩,
      rw or_comm at h6,
      cases h6 with h30 h31,
      {
        left,
        exact ⟨ h3, h4, h30⟩, 
      },
      {
        right,
        exact h31, 
      }
    },
    {
      intro h2,
      cases h2 with h3 h4,
      {
        rcases h3 with ⟨ h5, h6, h7⟩, 
        exact ⟨ h5, h6⟩, 
      },
      {
        rw h4 at *,
        exact ⟨ h, le_reflexive M m h ⟩, 
      }
    }
  end 

lemma JbartoJ2: ∀ (m:M), m ∈ 𝔽 → 𝕊 m ∈ 𝔽 → Jbar M m = 𝕁 M (𝕊 m):=
  begin
    intros m hm hsm,
    rw full_extensionality,
    intros t,
    rw J_members,
    rw Jbar_members,
    split,
    {
      intros h,
      cases h with ht h3,
      split,
      {
        exact ht,
      },
      {
        rw lessthan_definition,
        split,
        {
          have h4:= xlessthansuccessorx M m hm hsm,
          have h5:= le_transitive3 M t m (𝕊 m) ht hm hsm h3 h4,
          rw lessthan_definition at h5,
          exact h5.1,
        },
        {
          intros h,
          rw h at *,
          have h6:= xlessthansuccessorx M m hm hsm,
          have h7:= le_transitive2 M m (𝕊 m) m hm hsm hm h6 h3,
          have h8:= xnotlessthanx M m hm,
          contradiction,
        }
      }
    },
    {
      intros h,
      cases h with ht h20,
      split,
      {
        exact ht,
      },
      {
        rw lessthan_definition at h20,
        cases h20 with h21 h22,
        have h23:= lessthansuccessor2 M t m ht hm h21,
        cases h23 with h24 h25,
        {
          exact h24,
        },
        {
          contradiction,
        }
      }
    }
  end

lemma lessthan_decidable: ∀ (x y:M), x ∈ 𝔽 → y ∈ 𝔽 → x < y ∨ ¬ (x < y):=
  assume x y,
  begin
    intros h2 h3,
    have h4:= Theorem2 M x y h2 h3,
    cases h4 with h5 h6,
    cases h5 with h7 h8,
    {
      left,
      exact h7,
    },
    {
      cases h8 with h9 h10,
      {
        rw h9 at *,
        simp at h6,
        right,
        exact h6,
      },
      {
        right,
        push_neg at h6, 
        intro h11, 
        have h12:= h6 h11,
        contradiction,
      }
    }
  end


lemma strict_lessthansuccessor: ∀ (x y:M), x ∈ 𝔽  → y ∈ 𝔽  → 𝕊 y ∈ 𝔽 → (x < 𝕊 y ↔ x < y ∨ x = y):=
  assume x y,
  begin
    intros hx hy hsy,
    have h:= lessthansuccessor2 M x y hx hy, 
    split,
    {
      intro h2,
      rw lessthan_definition at h2,
      cases h2 with h3 h4,
      have h5:= h h3, 
      cases h5 with h6 h7,
      { 
        rw letolessthan M x y hx hy at h6, 
        exact h6,
      },
      {
        contradiction, 
      }
    },
    {
      intro h2,
      have h3:= xlessthansuccessorx M y hy hsy, 
      cases h2 with h4 h5,
      {
        have h6:= lessthan_transitive M x y (𝕊 y) hx hy hsy h4 h3, 
        exact h6, 
      },
      {
        rw h5 at *,
        exact h3, 
      }
    }
  end 



lemma lessthansuccessor3: ∀ (m n:M), m ∈ 𝔽 → n ∈ 𝔽 →  (∃(u:M), u ∈ 𝕊 n)→( m < 𝕊 n ↔ m < n ∨ m = n):=
  assume m n,
  begin
    intros hm hn h3,
    have h4:= successorF M n hn h3, 
    have h8:= strict_lessthansuccessor M m n hm hn h4, 
    exact h8, 
  end

lemma usc_empty: USC (Λ:M)= Λ :=
  begin
    rw full_extensionality,
    intro t,
    rw usc M,
    split,
    {
      intro h,
      cases h with a h2,
      cases h2 with h3 h4,
      have h5:= emptyset_axiom a,
      contradiction, 
    },
    {
      intro h,
      have h3:=emptyset_axiom t,
      contradiction,
    }
  end

 
lemma mnotinJm: ∀ (m:M), m ∈ 𝔽 → ¬ m ∈ 𝕁 M m:=
  assume m,
  begin
    intros h h2,
		rw J_members at h2, 
		cases h2 with h3 h4,
		have h5:= xnotlessthanx M m h,
		contradiction, 
	end

lemma minJbarm: ∀ (m:M), m ∈ 𝔽 → m ∈ Jbar M m:=
  assume m,
  begin
    intro h,
    rw Jbar_members, 
    exact ⟨  h, le_reflexive M m h⟩, 
  end

lemma Jsuccessor: ∀(m:M), m ∈ 𝔽 → 𝕊 m ∈ 𝔽 → 𝕁 M (𝕊 m) = ((𝕁 M m) ∪ (single m)):=
  assume m,
	begin
		intros h39 h40,
		rw full_extensionality,
		intro t,
		rw J_members,
		rw binary_union_axiom,
		rw singleton1 M, 
		rw J_members,
		split,
		{
			intro h,
			cases h with h2 h3, 
			have h4:= strict_lessthansuccessor M t m h2 h39 h40,  
		  rw h4 at h3,
			cases h3 with h10 h11,
			{
				left,
				exact ⟨ h2, h10⟩, 
			},
			{
				right,
				exact h11, 
			}
		},
		{
			intro h,
			cases h with h2 h3,
			{
				cases h2 with h4 h5,
				split,
				{
					exact h4,
				},
				{
					have h6:= cardinalsinhabited M (𝕊 m) h40,
					have h7:= lessthansuccessor M m h39 h6, 
					exact lessthan_transitive M t m (𝕊 m) h4 h39 h40 h5 h7,
				}
			},
			{
				rw h3 at *,
			  have h43:= cardinalsinhabited M (𝕊 m) h40, 
				have h44:= lessthansuccessor M m h39 h43, 
				exact ⟨ h39, h44⟩, 	
			}
		}
	end



lemma Jzero: 𝕁 M (zero:M) = (Λ:M) :=
  begin
    rw full_extensionality,
    intro t,
    rw J_members, 
    have h:= emptyset_axiom t,
    have h2:= xnotlessthanzero M t,
    split,
    {
      intro h3,
      cases h3 with h4 h5,
      have h6:= h2 h4,
      contradiction,
    },
    {
      intro h10,
      contradiction,
    }
  end

lemma Jfinite: ∀ (y:M), y ∈ 𝔽 → 𝕁 M y ∈ FINITE M:=
  begin
    have base: zero ∈  Z_Jfinite M:=
      begin
        rw Z_Jfinite_members M,
        split,
        {
          exact zeroF M,
        },
        {
          rw Jzero M,
          exact lambda_finite M,
        }
      end,
    have step: ∀(y:M), y ∈ Z_Jfinite M → (∃ u, u ∈ 𝕊 y) → 𝕊 y ∈ Z_Jfinite M:=
      assume y,
      begin
        intros h h2,
        rw Z_Jfinite_members at h,
        cases h with h3 h4,
        rw Z_Jfinite_members, 
        split,
        {
          exact successorF M y h3 h2, 
        },
        {
          rw Jsuccessor M y h3 (successorF M y h3 h2),
          have h5:= mnotinJm M y h3, 
          have h6:= finite_adjoin M (𝕁 M y) y ⟨  h4, h5⟩ ,
          exact h6,
        }
      end,
    intros y h,
    rw F_members at h, 
    specialize h ( Z_Jfinite M),
    have h3:= h (and.intro base  step), 
    rw ( Z_Jfinite_members M) at h3, 
    cases h3 with h5 h6, 
    exact h6,  
  end

lemma Jbarfinite: ∀ (y:M), y ∈ 𝔽 → Jbar M y ∈ FINITE M:=
  assume y,
  begin
    intro h,
    rw JbartoJ M y h, 
    have h2:= mnotinJm M y h, 
    exact finite_adjoin M (𝕁 M y) y ⟨ (Jfinite M y h) ,h2⟩ , 
  end

lemma reverse_adjoin_ssc: ∀ (a c:M), a ∪ (single c) ∈ SSC(𝔽 ) → ¬ c ∈ a → a ∈ SSC( 𝔽 ):=
  assume a c,
  begin
    intros h h2,
    rw ssc_members at *,
    cases h with h3 h4,
    split,
    {
      rw subset_definition,
      intro t,
      intro h5,
      rw subset_definition at h3,
      specialize h3 t,
      rw binary_union_axiom at h3,
      apply h3,
      left,
      exact h5, 
    },
    {
      intro t,
      intro h5,
      specialize h4 t,
      have h6:= h4 h5,
      rw subset_definition at h3,
      specialize h3 c,
      rw binary_union_axiom at h3,
      rw singleton1 at h3, 
      simp at h3, 
      have h7:= FregeNdecidable M,
      rw decidable_members at h7,
      have h8:= h7 t c ⟨ h5, h3⟩, 
      cases h8 with h9 h10,
      {
        rw h9 at *,
        right,
        exact h2,
      },
      {
        cases h6 with h11 h12,
        {
          rw binary_union_axiom at h11,
          rw singleton1 at h11,
          cases h11 with h20 h21,
          {
            exact or.inl h20,
          },
          {
            contradiction,
          }
        },
        {
          rw binary_union_axiom at h12,
          rw singleton1 at h12,
          right,
          intro h20,
          exact h12 (or.inl h20), 
        }
      }
    }
  end
 

lemma reverse_adjoin2_ssc: ∀ (a c:M), a ∪ (single c) ∈ SSC(𝔽 ) → ¬ c ∈ a → c ∈ 𝔽 :=
 assume a c,
  begin
    intro h3,
    rw ssc_members M 𝔽 (a ∪ (single c)) at h3,
    cases h3 with h4 h5,
    intro h6,
    rw subset_definition at h4,
    specialize h4 c,
    rw binary_union_axiom at h4,
    rw singleton1 at h4,
    simp at h4, 
    exact h4, 
  end

lemma Jbar_monotonic: ∀ (a b:M), a∈ 𝔽 → b ∈ 𝔽 → a ≤ b → Jbar M a ⊆ Jbar M b:=
  assume a b,
  begin
    intros ha hb h3,
    rw subset_definition,
    intro t,
    intro h4,
    rw Jbar_members M at *,
    cases h4 with h5 h6,
    split,
    {
      exact h5,
    },
    {
      have h7:= le_transitive M t b a h5 hb ha h6 h3, 
      exact h7,
    }
  end

lemma empty_similar_empty: similar M (Λ :M) (Λ :M):=
  begin
		unfold similar,
		use Λ,
		unfold similarity,
		split,
		{
			unfold oneone,
			repeat{split},
			{
				rw Rel_definition, 
				intros z h,
				have h3:= emptyset_axiom z,
				contradiction,
			},
			{
				intros x y h,
				cases h with h2 h3,
				have h4:= emptyset_axiom x,
				contradiction,
			},
			{
				intros x y z h,
				cases h with h2 h3,
				have h4:=emptyset_axiom x,
				contradiction,
			},
			{
				intros x h,
				have h4:=emptyset_axiom x,
				contradiction,
			},
			{
        intros x u y h,
				cases h with h2 h3,
				have h4 := emptyset_axiom ‹ x,y ›,
				contradiction, 
			},
			{
				intros x y h,
				cases h with h3 h4,
				have h5:= emptyset_axiom y,
				contradiction,
			}
		},
		{
			unfold onto,
			intros y h,
			have h4:= emptyset_axiom y,
			contradiction, 
		}
	end

lemma J1: ∀(x:M), x ∈ FINITE M → x ∈ SSC 𝔽 → ¬ x = Λ → ∃ (y:M), y ∈ 𝔽 ∧ x ⊆  Jbar  M y ∧ y ∈ x:=
	begin
    have base: Λ ∈ WJ1 M:=
		  begin
				rw WJ1_members,
				split,
				{
					exact lambda_finite M,
				},
				{
					intro h,
					contradiction, 
				}
			end,
		have step: adjoin_closed M (WJ1 M):=
		  begin
				unfold adjoin_closed,
				intros a c h,
				cases h with h2 h3,
				rw WJ1_members at h2,
				cases h2 with h4 h5,
				rw WJ1_members,
				split,
				{
					have h6:= finite_adjoin M a c ⟨ h4, h3⟩, 
					exact h6,
				},
				{
					intro h7,
					have h8:= empty_or_inhabited M a h4, 
					intro h40,
					cases h8 with h9 h10,
					{
						rw h9 at *,
						use c,
						rw empty_union_x M (single c) at h40,
						rw ssc_members at h40,
						cases h40 with h41 h42,
						rw subset_definition at h41,
						specialize h41 c,
						rw singleton1 M at h41,
						simp at h41, 
						repeat{split},
						{
							exact h41, 
						},
						{
							rw empty_union_x M (single c),
							rw subset_definition, 
							intro t,
							rw singleton1 M,
							intro h42,
							rw h42 at *,
							rw Jbar_members M,
              exact ⟨ h41, le_reflexive M c h41⟩, 
						},
						{
							rw empty_union_x M (single c), 
							rw singleton1 M,
						}
					},
					{  -- case 2, a is inhabited
					  have h11: ¬ (a = Λ ):=
					    begin
								intro h12,
								cases h10 with u h13,
								rw h12 at *,
								have h13:= emptyset_axiom u,
								contradiction, 
							end,
            have h41:= reverse_adjoin_ssc M a c h40 h3,
						have h42:= reverse_adjoin2_ssc M a c h40 h3, 
						have h12:= h5 h11 h41,
						cases h12 with y h13,
						rcases h13 with ⟨h14, h15, h16⟩,
					  have h43:= Theorem2 M c y h42 h14, 
						cases h43 with h44 h45, 
						cases h44 with h46 h47,
						{
							use y,
							repeat{split},
							{
								exact h14,
							},
							{
								rw subset_definition,
								intros t h48,
								-- rw Jbar_members,
								rw binary_union_axiom at h48,
                rw singleton1 M at h48,
								cases h48 with h49 h50,
								{
									exact member_subset M a (Jbar M y) t h15 h49,
								},
								{
									rw h50 at *,
									rw Jbar_members,
									split,
									{
										exact h42,
									},
									{
										rw lessthan_definition at h46,
										exact h46.left, 
									}
								}
							},
							{
								rw binary_union_axiom,
								left,
								exact h16, 
							}
						},
						{
							use c,
							repeat{split},
							{
								exact h42,
							},
							{
								rw subset_definition,
								intro t,
								rw binary_union_axiom,
								intro h49,
								cases h49 with h50 h51,
								{
								  have h52: y ≤ c:=
									  begin
											rw lessthan_definition at h47,
											cases h47 with h53 h54,
											{
												rw h53,
												exact le_reflexive M y h14, 
											},
											{
                        exact h54.left, 
											}
										end,
									have h53:= Jbar_monotonic M y c h14 h42 h52, 
									have h54:= subset_transitive M a (Jbar M y) (Jbar M c) h15 h53, 
									have h55:= member_subset M a (Jbar M c) t h54 h50,
									exact h55,
								},
								{
									rw singleton1 M at h51,
									rw h51 at *,
                  exact minJbarm M c h42, 
								}
							},
							{
								rw binary_union_axiom,
								rw singleton1,
								simp,
							}
						}
					}
				}
			end,
		have h90: (FINITE M)⊆ WJ1 M := (finite_conditions M) (WJ1 M)  step base,
    rw subset_definition at h90, 
    intro z,
    specialize h90 z,
    rw WJ1_members M at h90,
		intro h3,
		have h92:= h90 h3,
		cases h92 with h93 h94,
		intros h4 h5,
		exact h94 h5 h4,
	end



lemma ssc_down: ∀ (u x c:M),  ¬ (c ∈ x) →  (x ∪ (single c)) ∈ SSC u → x ∈ SSC( u):=
  assume u x c,
  begin
    intros  h2 h3,
    rw ssc_members,
    rw ssc_members at h3,
    cases h3 with h4 h5,
    split,
    {
      rw subset_definition,
      intro t,
      specialize h5 t,
      intro h6,
      rw subset_definition at h4,
      specialize h4 t,
      rw binary_union_axiom at h4,
      rw singleton1 at h4,
      exact h4 (or.inl h6),
    },
    {
      intro y,
      intro hy,
      specialize h5 y,
      have h6:= h5 hy,
      rw binary_union_axiom at h6,
      rw singleton1 at h6, 
      cases h6 with h20 h21,
      {
        cases h20 with h22 h23,
        {
          exact or.inl h22, 
        },
        {
          rw h23 at *,
          exact or.inr h2,
        }
      },
      {
        right,
        intro h22,
        exact h21 (or.inl h22),
      }
    }
  end 
 

lemma finitemaximal: ∀ (x:M), x ∈ FINITE M → (x ⊆ 𝔽  → ¬ (x = Λ) →  ∃ (m:M), m ∈ x ∧ ∀ (u:M), u ∈ x → u ≤ m) :=
  begin
    have base: (Λ:M)∈ W_finitemaximal M:=
      begin
        rw W_finitemaximal_members, 
        split,
        {
          exact lambda_finite M,
        },
        {
          intros h h2,
          simp at h2,
          contradiction,
        }
      end,
    have step: adjoin_closed M (W_finitemaximal M):=
      begin
        unfold adjoin_closed,
        intros x c h,
        cases h with h2 h3,
        rw W_finitemaximal_members M at *,
        cases h2 with h4 h5,
        split,
        {
          have h6:= finite_adjoin M x c ⟨ h4, h3⟩, 
          exact h6, 
        },
        {
          intros h7 h8,
          have h9:=empty_or_inhabited M x h4, 
          cases h9 with h10 h11,
          {
            use c,
            split,
            {
              rw binary_union_axiom,
              rw singleton1 M,
              simp,
            },
            {
              intro t,
              intro h11,
              rw h10 at *,
              rw empty_union_x M (single c) at h7 h11,
              rw subset_definition at h7,
              specialize h7 c,
              rw singleton1 at h7 h11,
              simp at h7,
              rw h11, 
              exact le_reflexive M c h7,
            }
          },
          {
            have h12: x ⊆ 𝔽 :=
              begin
                rw subset_definition,
                intro t,
                rw subset_definition at h7,
                specialize h7 t,
                rw binary_union_axiom at h7,
                rw singleton1 at h7,
                intro h30,
                exact h7 (or.inl h30),
              end,
            have h13: ¬ (x = Λ ):=
              begin
                intro h14,
                cases h11 with u h15,
                rw h14 at h15,
                have h16:= emptyset_axiom u,
                contradiction,
              end,
            have h14:= h5 h12 h13,
            cases h14 with m h15,
            cases h15 with h16 h17,
            have h8: c ∈ 𝔽 :=
              begin
                rw subset_definition at h7,
                specialize h7 c,
                rw binary_union_axiom at h7,
                rw singleton1 M at h7,
                simp at h7,
                exact h7,
              end,
            have h19: m∈ 𝔽 := member_subset M x 𝔽 m h12 h16,
            have h20:=Theorem2 M c m h8 h19, 
            cases h20 with h21 h22,
            cases h21 with h23 h24,
            {
              use m,
              split,
              {
                rw binary_union_axiom,
                exact or.inl h16,
              },
              { 
                intros t  h25,
                rw binary_union_axiom at h25,
                rw singleton1 at h25,   
                cases h25 with h26 h27,
                {
                  have h24:= member_subset M x 𝔽 t h12 h26,
                  have h28:= h17 t h26, 
                  exact h28,
                },
                {
                  rw h27 at *,
                  rw lessthan_definition at h23,
                  exact h23.left,
                }
              }
            },
            {
              use c,
              split,
              {
                rw binary_union_axiom,
                rw singleton1, 
                simp,
              },
              {
                intro t,
                rw binary_union_axiom,
                rw singleton1 M,
             
             
                intro h31,
                cases h31 with h32 h33,
                { 
                  have h34: m ≤ c:=
                    begin
                      rw letolessthan M m c h19 h8, 
                      rw [or_comm, sym] at h24,
                      exact h24,  
                    end,
                  have h30:= h17 t h32, 
                  have h25:= member_subset M x 𝔽 t h12 h32, 
                  have h35:= le_transitive M t c m h25 h8 h19 h30 h34,
                  exact h35, 
                },
                {
                  rw h33,
                  exact le_reflexive M c h8, 
                }
              }
            }
          }
        }
      end,
    have h90: (FINITE M)⊆ W_finitemaximal M := (finite_conditions M) (W_finitemaximal M)  step base,
    rw subset_definition at h90, 
    intro z,
    specialize h90 z,
    rw W_finitemaximal_members M at h90, 
    intro h91,
    have h92:= h90 h91,
    exact h92.right, 
  end  

#axioms_all  --This file is clean.
