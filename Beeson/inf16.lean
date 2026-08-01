import inf15 
variables (M:Type) [Model M] (a b x y z u v w X R W κ μ ℓ : M)
-- using ℓ where the source text has λ because you can't use λ for a variable.

open Model 

lemma zeroH: (zero:M) ∈ ℍ:=
  begin
    rw H_members, 
    intros w h,
    exact h.left,
  end

lemma successorH: ∀(x:M), x ∈ ℍ → ¬( 𝕊 x = Λ ) →  𝕊 x ∈ ℍ := 
  assume u,
  begin
     repeat{ rw H_members},
    intros h h1,
    intro w,
    specialize h w,
    intro h2,
    have h3:= h h2,
    cases h2 with h4 h5,
    have h6:= h5 u h3 h1,
    exact h6, 
  end

lemma oneH: (one:M) ∈ ℍ:=
  begin
    have h := zeroH M,
    rw one_definition, 
    have h2: ¬ ((one:M) = (Λ:M) ):=
      begin
        intro h3,
        rw full_extensionality M at h3,
        specialize h3 (single Λ ),
        rw one_members at h3,
        cases h3 with h4 h5,
        have h6:= emptyset_axiom (single (Λ :M)), 
        have h7: single Λ ∈ Λ := 
          begin
            apply h4,
            use Λ, 
          end,
        contradiction, 
      end,
    rw one_definition at h2,
    exact successorH M zero h h2, 
  end

lemma FsubsetH: (𝔽:M) ⊆ ℍ :=
  begin
    have base: zero ∈ ℍ := zeroH M, 
    have step: ∀(m:M), m ∈ ℍ → (exists u, u∈ 𝕊 m) → 𝕊 m ∈ ℍ:=
      begin
        intros m h h3,
        have h4: ¬ 𝕊 m = Λ :=
          begin
            intro h4,
            cases h3 with u h5,
            rw h4 at h5,
            have h6:=emptyset_axiom u,
            contradiction, 
          end,
        exact successorH M m h h4, 
      end,
    rw subset_definition, 
    intros y h, 
    rw F_members at h, 
    specialize h  ℍ ,
    have h3:= h (and.intro base  step), 
    exact h3, 
  end

lemma zeroorsuccessorH: ∀(x:M), x ∈ ℍ → x = zero ∨ ∃ (u:M), u ∈ ℍ ∧ 𝕊 u = x:=
  begin
    have base: zero ∈ Z_zeroorsuccessorH M :=
      begin
        rw Z_zeroorsuccessorH_members, 
        simp,
        exact zeroH M,
      end,
    have step: ∀ (x:M),  x ∈ Z_zeroorsuccessorH M → (¬ 𝕊 x = Λ ) → 𝕊 x ∈ Z_zeroorsuccessorH M:=
      begin
        intros x h2 h3,
        rw Z_zeroorsuccessorH_members M at h2,
        rw Z_zeroorsuccessorH_members M,
        cases h2 with h4 h5,
        split,
        {
          exact successorH M x h4 h3,
        },
        {
          right,
          cases h5 with h6 h7,
          {
            use zero,
            rw h6, 
            simp,
            exact zeroH M, 
          },
          {
            cases h7 with u h8,
            use x,
            simp,
            exact h4, 
          }
        }
      end,
    intros y h,
    rw H_members at h,
    specialize h (Z_zeroorsuccessorH M),
    have h3:= h (and.intro base step), 
    rw Z_zeroorsuccessorH_members at h3,
    exact h3.right, 
  end 

lemma nonzeroissuccessorH: ∀ (x:M), x ∈ ℍ → ¬ (x = zero) → ∃ (y:M), y ∈ ℍ ∧ x = 𝕊 y:=
  assume x,
  begin
    intros h h2, 
    have h3:= zeroorsuccessorH M x h,
    cases h3 with h4 h5,
    {
      rw h4 at *,
      contradiction,
    },
    {
      cases h5 with u h6,
      use u,
      split,
      {
        exact h6.left, 
      },
      {
        symmetry, 
        exact h6.right, 
      }
    }
  end

lemma notemptyisnotnotinhabited: ∀ (x:M), ¬ (x = Λ ) → ¬ ¬ ∃ (u:M), u ∈ x:=
  assume x,
  begin
    intros h4 h6,   
    apply h4,
    rw full_extensionality,
    intro t,
    split,
    {
      intro ht,
      have h5: ∃ (u:M), u ∈ x:= ⟨ t, ht⟩, 
      contradiction,
    },
    {
      intro ht,
      have h5:= emptyset_axiom t,
      contradiction,
    }
  end
  
lemma doublecomplementF: ∀(x:M), x ∈ ℍ → ¬¬ x ∈ 𝔽 :=
  begin
    have base: zero ∈ Z_doublecomplementF M:=
      begin
        rw Z_doublecomplementF_members,
        split,
        {
          exact zeroH M,
        },
        {
          have h:= zeroF M,
          intro h2,
          contradiction,
        }
      end,
    have step: ∀ (x:M), x ∈ Z_doublecomplementF M → ¬ (𝕊 x = Λ ) → 𝕊 x ∈ Z_doublecomplementF M:=
      begin
        intros x h,
        rw Z_doublecomplementF_members at h,
        rw Z_doublecomplementF_members,
        cases h with h2 h3,
        intro  h4,
        split,
        {
          exact successorH M x h2 h4, 
        },
        {
          have h5: ¬ ¬ ∃ (u:M), u ∈ 𝕊 x :=
            notemptyisnotnotinhabited M (𝕊 x) h4, 
          have h6:= successorF M x,
          have h7:= double_negate ( x ∈ 𝔽 → (∃ (x_1 : M), x_1 ∈ 𝕊 x) → 𝕊 x ∈ 𝔽) h6,
          have h8:= push_double_negationNF (x ∈ 𝔽 ) ((∃ (x_1 : M), x_1 ∈ 𝕊 x) → 𝕊 x ∈ 𝔽) h7 h3,
          have h9:= push_double_negationNF (∃ (x_1 : M), x_1 ∈ 𝕊 x) (𝕊 x ∈ 𝔽 ) h8 h5,
          exact h9, 
        }
      end,
    intros y h,
    rw H_members at h,
    specialize h (Z_doublecomplementF M),
    have h3:= h (and.intro base step), 
    rw Z_doublecomplementF_members at h3,
    exact h3.right, 
  end

lemma emptynotinH: ∀ (y:M), y ∈ ℍ → ¬ (y = Λ):= 
  begin
    have base: zero ∈ Z_emptynotinH M:=
      begin 
        rw Z_emptynotinH_members M, 
        split,
        {
          exact zeroH M,
        },
        {
          rw zero_definition,
          rw full_extensionality,
          intro h,
          specialize h Λ,
          rw singleton1 M at h,
          have h3:=emptyset_axiom Λ,
          simp at h, 
          contradiction, 
        }
      end,
    have step: ∀ (x:M), x ∈ Z_emptynotinH M → ¬ (𝕊 x = Λ ) → 𝕊 x ∈ Z_emptynotinH M:=
      begin
        intros x h h2,
        rw Z_emptynotinH_members M at h,
        rw Z_emptynotinH_members,
        split,
        {
          exact successorH M x h.left h2, 
        },
        {
          exact h2, 
        }
      end,
    intros y h,
    rw H_members at h,
    specialize h (Z_emptynotinH M),
    have h3:= h (and.intro base step), 
    rw Z_emptynotinH_members at h3,
    exact h3.right, 
  end

lemma successorweaklyoneoneH: ∀(x y:M), x ∈ ℍ → y ∈ ℍ → ¬ (𝕊 x = Λ ) → ¬ (𝕊 y = Λ ) →   ¬ (x = y) → ¬ (𝕊 x = 𝕊 y):=
  assume x y,
  begin
    intros hx hy h3 h4 h5,
    have h6:= successoroneone M x y, 
    have h7:= doublecomplementF M x hx,
    have h8:= doublecomplementF M y hy, 
    have h9:= notemptyisnotnotinhabited M (𝕊 x) h3,
    have h10:= notemptyisnotnotinhabited M (𝕊 y) h4,
    have h11:= double_negate (x ∈ 𝔽 → y ∈ 𝔽 → (∃ (u : M), u ∈ 𝕊 x) → (∃ (u : M), u ∈ 𝕊 y) → (x = y ↔ 𝕊 x = 𝕊 y)) h6,
    have h12:= push_double_negationNF (x ∈ 𝔽 )(y ∈ 𝔽 → (∃ (u : M), u ∈ 𝕊 x) → (∃ (u : M), u ∈ 𝕊 y) → (x = y ↔ 𝕊 x = 𝕊 y)) h11 h7,
    have h13:= push_double_negationNF (y ∈ 𝔽 )((∃ (u : M), u ∈ 𝕊 x) → (∃ (u : M), u ∈ 𝕊 y) → (x = y ↔ 𝕊 x = 𝕊 y)) h12 h8,
    have h14:= push_double_negationNF ( ∃ (u: M), u ∈ 𝕊 x)((∃ (u : M), u ∈ 𝕊 y) → (x = y ↔ 𝕊 x = 𝕊 y)) h13 h9,
    have h15:= push_double_negationNF (∃ (u : M), u ∈ 𝕊 y)( x= y ↔ 𝕊 x = 𝕊 y) h14 h10,
    intro h16,
    rw h16 at *,
    have h17:   𝕊 y =  𝕊 y:=  refl (𝕊 y), 
    have h18:= notnot_iff (x=y) (𝕊 y = 𝕊 y),
    have h20:= h18 h15, 
    have h21:= double_negate (𝕊 y = 𝕊 y) h17,
    have h19:= h20.mpr h21, 
    contradiction, 
  end

lemma Hdecidable: ∀(x:M), x∈ ℍ → ∀ (y:M), y ∈ ℍ → (x = y ∨ ¬ (x = y)) :=
  begin
    have base: zero ∈ Z_Hdecidable M:=
      begin
        rw Z_Hdecidable_members M, 
        split,
        {
          exact zeroH M,
        },
        {
          intros y h,
          have h4:= zeroorsuccessorH M y h,
          cases h4 with h5 h6,
          {
            left,
            symmetry,
            exact h5, 
          },
          {
            cases h6 with u h7,
            cases h7 with h8 h9,
            right,
            rw← h9, 
            have h10:= Fregesuccessoromits0 M u,
            rw sym,
            exact h10,
          }
        }
      end,
    have step: ∀ (x:M), x∈ Z_Hdecidable  M → ¬ (𝕊 x = Λ ) → 𝕊 x ∈ Z_Hdecidable M:=
      begin
        intros x h h3,
        rw Z_Hdecidable_members M,
        rw Z_Hdecidable_members M at h,
        cases h with h4 h5,
        split,
        {
          exact successorH M x h4 h3, 
        },
        {
          intros y h6,
          have h7:= zeroorsuccessorH M y h6, 
          cases h7 with h8 h9,
          {
            rw h8 at *,
            right,
            have h10:= Fregesuccessoromits0 M x,
            exact h10, 
          },
          {
            cases h9 with z h10,
            cases h10 with h11 h12,
            have h13:= h5 z h11, 
            cases h13 with h14 h15,
            {
              rw h14 at *,
              exact or.inl h12,
            },
            { 
              have h17:= emptynotinH M, 
              have h18: ¬ (𝕊 z = Λ ):= 
                begin
                  intro h19,
                  rw h19 at *,
                  rw← h12 at *,
                  have h20:= h17 Λ h6, 
                  contradiction,
                end,    
              have h16:= successorweaklyoneoneH M x z h4 h11 h3 h18 h15,
              rw h12 at h16,
              right, 
              exact h16, 
            }
          }
        } 
      end,
    intros x h,
    rw H_members at h,
    specialize h (Z_Hdecidable M),
    have h3:= h (and.intro base step), 
    rw Z_Hdecidable_members at h3,
    exact h3.right, 
  end 

lemma successoroneoneonH: ∀ (x y:M), x ∈ ℍ → y ∈ ℍ → 𝕊 x ∈ ℍ → 𝕊 x = 𝕊 y → x = y:=
  assume x y,
  begin
    intros hx hy h2 h3,
    have h4: ¬ ¬ (x=y):=
      begin
        intro h5, 
        have h7:= emptynotinH M (𝕊 x) h2, 
        have h8:= h7,
        rw h3 at h8,
        have h6:= successorweaklyoneoneH M x y hx hy h7 h8 h5,
        contradiction, 
      end,
    have h5:= Hdecidable M x hx y hy, 
    cases h5 with h6 h7,
    {
      exact h6,
    },
    {
      contradiction,
    }
  end

lemma inhabitedHisF : ∀ (x:M), x ∈ ℍ → (∃ (u:M), u ∈ x) → x ∈ 𝔽 :=
  begin
    have base: zero ∈ Z_inhabitedHisF M:=
      begin
        rw Z_inhabitedHisF_members M,
        split,
        {
          exact zeroH M,
        },
        {
          intro h,
          exact zeroF M,
        }
      end,
    have step: ∀ (x:M), x ∈ Z_inhabitedHisF M → ¬ 𝕊 x = Λ → 𝕊 x ∈ Z_inhabitedHisF M:=
      assume x,
      begin
        rw Z_inhabitedHisF_members,
        rw Z_inhabitedHisF_members,
        intros h h4,
        cases h with h2 h3,
        split,
        {
          exact successorH M x h2 h4, 
        },
        {
          intro h5, 
          have h5copy:= h5,
          cases h5 with u h6,
          rw successor_members at h6,
          cases h6 with p h7,
          cases h7 with c h8,
          rcases h8 with ⟨ h9, h10, h11⟩,
          have h12:= h3 ⟨ p, h9⟩, 
          have h13:= successorF M x h12 h5copy,
          exact h13, 
        }
      end,
    intros x h,
    rw H_members at h,
    specialize h (Z_inhabitedHisF M),
    have h3:= h (and.intro base step), 
    rw Z_inhabitedHisF_members at h3,
    exact h3.right, 
  end 


lemma boundedDNS: ∀(P y:M), y ∈ 𝔽 → 
((∀ (x:M), x∈ 𝔽 → x < y → ¬¬ x ∈ P) → (¬¬ ∀ (x:M), x ∈ 𝔽 → x < y →  x ∈ P)  ):=
  assume P,
  begin
    have base: (zero:M) ∈ Z_boundedDNS M P:=
      begin
        rw Z_boundedDNS_members,
        split,
        {
          exact zeroF M,
        },
        {
          intro h,
          intro h2,
          have h3: ∀ (x:M), x ∈ 𝔽 → x < zero → x ∈ P:=
            begin
              intros x hx h4,
              have h5:= xnotlessthanzero M x hx,
              contradiction,
            end,
          contradiction,
        }
      end,
    have step: ∀ (y:M), y ∈ Z_boundedDNS M P→ (∃(u:M), u ∈ 𝕊 y) → 𝕊 y ∈ Z_boundedDNS M P:=
      begin
        intros y h2 h3,
        rw Z_boundedDNS_members at h2,
        rw Z_boundedDNS_members,
        cases h2 with hy h4,
        split,
        {
          exact successorF M y hy h3,
        },
        { 
          intros h5, 
          have h6: ∀ (x : M), x ∈ 𝔽 → x < y → ¬¬x ∈ P :=
            begin
              intros x hx h7,
              have h9:= successorF M y hy h3,
              have h8: x < 𝕊 y:=
                begin
                  have h10:= xlessthansuccessorx M y hy h9,
                  have h11:= lessthan_transitive M x y (𝕊 y) hx hy h9 h7 h10,
                  exact h11, 
                end,
              have h12:= h5 x hx h8,
              exact h12,
            end,
          have h13:= h4 h6, 
          have h14:= h5 y hy (lessthansuccessor M y hy h3),
          have h15: y ∈ P → ( ∀ (x : M), x ∈ 𝔽 → x < y → x ∈ P)→  (∀(x:M), x ∈ 𝔽 → x < 𝕊 y → x ∈ P):=
            begin
              intros h20 h21 x hx hsy,
              have h22:= lessthansuccessor3 M x y hx hy h3,
              rw h22 at hsy,
              cases hsy with h23 h24,
              {
                exact h21 x hx h23,
              },
              {
                rw h24 at *,
                exact h20,
              }
            end,
          have h30:= double_negate  (y ∈ P → (∀ (x : M), x ∈ 𝔽 → x < y → x ∈ P) → ∀ (x : M), x ∈ 𝔽 → x < 𝕊 y → x ∈ P) h15,
          have h31:= push_double_negationNF (y ∈ P)((∀ (x : M), x ∈ 𝔽 → x < y → x ∈ P) → ∀ (x : M), x ∈ 𝔽 → x < 𝕊 y → x ∈ P) h30 h14,
          have h32:= push_double_negationNF ((∀ (x : M), x ∈ 𝔽 → x < y → x ∈ P))(∀ (x : M), x ∈ 𝔽 → x < 𝕊 y → x ∈ P) h31,
          apply h32,
          exact h13, 
        }
      end,
    intros y h,
    rw F_members at h,
    specialize h (Z_boundedDNS M P),
    have h3:= h (and.intro base step), 
    rw Z_boundedDNS_members M P at h3,
    exact h3.right, 
  end



lemma nonemptysum: ∀ (y:M), y∈ ℍ  → ∀ (x:M), x ∈ ℍ → ¬ x + y = Λ → x + y ∈ ℍ:=
  begin
    have base: zero ∈ Z_nonemptysum M:=
      begin
        rw Z_nonemptysum_members,
        split,
        {
          exact zeroH M,
        },
        {
          intros x h h2,
          rw right_identityNF,
          exact h, 
        }
      end,
    have step: ∀ (y:M), y ∈ Z_nonemptysum M → ¬ (𝕊 y= Λ) → 𝕊 y ∈ Z_nonemptysum M:=
      assume y,
      begin
        rw Z_nonemptysum_members,
        intro h,
        cases h with hy h2,
        intro h3,
        rw Z_nonemptysum_members,
        split,
        {
          exact successorH M y hy h3, 
        },
        {
          intros x h4 h5,
          have h6:= h2 x h4,
          rw addition_equation,
          rw addition_equation at h5, 
          have h16: 𝕊 Λ = Λ  :=
            begin 
               rw full_extensionality M ,
               intro t,
               rw successor_members,
               split,
               {
                 intro h9,
                 cases h9 with x h10,
                 cases h10 with a h11,
                 rcases h11 with ⟨ h12, h13, h14⟩,
                 have h15:= emptyset_axiom x,
                 contradiction,
               },
               {
                 intro h9,
                 have h10:=emptyset_axiom t,
                 contradiction, 
               }
            end,
          have h7: ¬ (x+y = Λ ):=
            begin
              intro h8,
              rw h8 at h5,
              contradiction,
            end,
          have h9:= h6 h7,
          exact successorH M (x+y) h9 h5, 
        }
      end, 
    intros y h,
    rw H_members at h,
    specialize h (Z_nonemptysum M),
    have h3:= h (and.intro base step), 
    rw Z_nonemptysum_members M at h3,
    exact h3.right, 
  end

lemma Ehelper: ‹ zero,one› ∈ Egraph M ∧ 
∀ (x y:M), ‹ x,y› ∈ Egraph M → (¬ (𝕊 x = Λ ))→ ‹ 𝕊 x, y+y › ∈ Egraph M :=
  begin
    split,
    { 
      rw Egraph_members, 
      split,
      { 
        use zero, use one,
      },
      { 
        intros w h h2,
        exact h, 
      }
    },
    {
      intros x y,
      rw Egraph_members,
      rw Egraph_members,
      intros h h2, 
      use 𝕊 x, use y+y,
      intros w h2,
      cases h with h3 h4,
      intro h5,
      have h6:= h5 x y,
      have h7:= h4 w h2,
      apply h6,
      { 
        apply h7,
        intros p q h8 h9,
        have h10:= h5 p q h8 h9, 
        exact h10, 
      },
      {
        intro h11, 
        contradiction,
      }
    }
  end

lemma Emaps1: ∀ (x:M), x ∈ ℍ → ∃ (y:M), ‹ x,y› ∈ Egraph M:=
  begin
    have base: zero ∈ Z_Emaps1 M:=
      begin
        rw Z_Emaps1_members,
        split,
        {
          exact zeroH M,
        },
        {
          use one,
          rw Egraph_members,
          split,
          {
            use zero, use one, 
          },
          { 
            intros w h h2,
            exact h, 
          }
        }
      end,
    have step: ∀(x:M), x ∈ Z_Emaps1 M → ¬ (𝕊 x = Λ ) → 𝕊 x ∈ Z_Emaps1 M:=
      assume x,
      begin
        intros h h2,
        rw Z_Emaps1_members at h,
        rw Z_Emaps1_members, 
        cases h with h20 h3,
        cases h3 with y h4, 
        rw Egraph_members at h4, 
        cases h4 with h5 h6,
        split,
        {
          exact successorH M x h20 h2, 
        },
        {
          use y+y,
          rw Egraph_members,
          split,
          {
            use 𝕊 x, use y+y,
          },
          { intros w h h8, 
            have h7:= h6 w h h8,
            exact h8 x y h7 h2,
          }
        }
      end, 
    intros y h,
    rw H_members at h,
    specialize h (Z_Emaps1 M),
    have h3:= h (and.intro base step), 
    rw Z_Emaps1_members M at h3,
    exact h3.right, 
  end

lemma successorofempty: 𝕊 (Λ :M) = (Λ :M):=
  begin
    rw full_extensionality,
    intro t,
    rw successor_members,
    split,
    {
      intro h,
      cases h with x h2,
      cases h2 with a h3,
      cases h3 with h4 h5,
      have h6:= emptyset_axiom x,
      contradiction,
    },
    {
      intro h,
      have h2:= emptyset_axiom t,
      contradiction,
    }
  end

lemma emptyplusempty: (Λ :M) + Λ = Λ :=
  begin
    rw full_extensionality,
    intro t,
    rw addition_members M,
    split,
    {
      intro h,
      cases h with u h2,
      cases h2 with v h3,
      rcases h3 with ⟨ h4, h5, h6,h7 ⟩, 
      have h8:= emptyset_axiom u,
      contradiction, 
    },
    {
      intro h,
      have h2:= emptyset_axiom t,
      contradiction, 
    }
  end

lemma Ehelper2: ∀ (x y:M),  ‹ x,y › ∈ Egraph M  → (¬ (x = Λ ) → x ∈ ℍ ) ∧ (¬ (y = Λ )→ y ∈ ℍ ):=
  assume x y,
  begin
    intro h,
    rw Egraph_members at h,
    cases h with h2 h3,
    cases h2 with p h4,
    cases h4 with q h5,
    rw ordered_pair_equality at h5,
    cases h5 with h6 h7,
    rw← h6 at *,
    rw← h7 at *,
    specialize h3 (W_Ehelper2 M), 
    have h8: ‹ zero,one› ∈ W_Ehelper2 M:=
      begin
        rw W_Ehelper2_members,
        use zero, use one,
        simp,
        have h9:= zeroH M, 
        have h10:= oneH M,
        split,
        {
          intro h11,
          exact h9,
        },
        {
          intro h11,
          exact h10, 
        }
      end,
    have h9:= h3 h8,
    have h10: ∀ (x y:M), ‹ x,y › ∈ W_Ehelper2 M→ (¬ (𝕊 x = Λ )) → ‹ 𝕊 x, y+y › ∈ W_Ehelper2 M:=
      begin
        intros x y,
        intros h11 h90,
        rw W_Ehelper2_members at h11,
        rw W_Ehelper2_members,
        cases h11 with p h12,
        cases h12 with q h13,
        cases h13 with h14 h15, 
        rw ordered_pair_equality at h14,
        cases h14 with h16 h17,
        rw← h16 at *,
        rw← h17 at *,
        use 𝕊 x, use y+y,
        simp,
        cases h15 with h18 h19,
        split,
        {
          intro h20,
          have h21: ¬ x = Λ :=
            begin
              intro h22,
              rw h22 at *,
              have h23:= successorofempty M,
              contradiction, 
            end,
          exact successorH M x (h18 h21) h20, 
        },
        { 
          intro h20, 
          have h21: ¬ y = Λ :=
            begin
              intro h22,
              have h23:= emptyplusempty M,
              rw h22 at h20, 
              contradiction, 
            end,
          have h22:= nonemptysum M y (h19 h21) y (h19 h21) h20, 
          exact h22, 
        }
      end,
    have h11:= h9 h10,
    rw W_Ehelper2_members at h11,
    cases h11 with p h12,
    cases h12 with q h13,
    cases h13 with h14 h15,
    rw ordered_pair_equality at h14,
    cases h14 with h15 h16,
    rw← h15 at *,
    rw← h16 at *,
    exact h15, 
  end

lemma Emaps2_base:zero ∈ Z_Emaps2 M:=
  begin
    rw Z_Emaps2_members,
    split,
    {
      exact zeroH M,
    },
    {
      intros y u h2 h3,
      set W:= Egraph M - single (‹ zero, u› ) ∪ single ( ‹ zero,one› ) with h20,
      set V:= Egraph M - single (‹ zero, y› ) ∪ single ( ‹ zero,one› ) with h120,
      have h6: ‹ zero,one› ∈ W:=
        begin
          rw h20, 
          rw binary_union_axiom,
          right,
          rw singleton1,
        end,
      have h106: ‹ zero,one› ∈ V:=
        begin
          rw h120, 
          rw binary_union_axiom,
          right,
          rw singleton1,
        end,
      have h21:= Ehelper M, 
      cases h21 with h22 h23, 
      have h7: ∀ (x y:M), ‹ x,y › ∈ W→ (¬ (𝕊 x = Λ )) → ‹ 𝕊 x, y+y› ∈ W :=
        begin
          intros x p h8 h90 ,
          have h8copy:= h8, 
          rw h20 at h8, 
          rw [binary_union_axiom, minus_members,singleton1] at h8, 
          rw singleton1 at h8, 
          rw or_comm at h8, 
          cases h8 with h9 h10,
          {
            rw ordered_pair_equality at h9,
            cases h9 with h11 h12,
            rw h11 at *,
            rw h12 at *,
            rw h20,
            rw [binary_union_axiom, minus_members], 
            left,
            have h24:= h23 zero one h22, 
            split,
            {
              have h80: ¬ 𝕊 zero = Λ :=
                begin
                  intro h81, 
                  rw←  one_definition at h81, 
                  rw full_extensionality M at h81,
                  specialize h81 (single Λ), 
                  rw one_members at h81,
                  cases h81 with h82 h83,
                  have h84:= h82 ⟨ Λ , refl (single Λ )⟩, 
                  have h85:= emptyset_axiom (single Λ ), 
                  contradiction, 
                end,
              exact h24 h80, 
            },
            {
              rw singleton1,
              rw ordered_pair_equality,
              have h25:= Fregesuccessoromits0 M zero,
              intro h26,
              cases h26 with h27 h28,
              contradiction, 
            }
          },
          {
            cases h10 with h11 h12,
            rw h20,
            rw [binary_union_axiom, minus_members],
            left,
            rw singleton1,
            have h24:= h23 x p h11,
            split,
            {
              exact h24 h90,
            },
            {
              have h25:= Fregesuccessoromits0 M x,
              rw ordered_pair_equality,
              intro h26,
              cases h26 with h27 h28,
              contradiction, 
            }
          }
        end, 
      have h107: ∀ (x y:M), ‹ x,y › ∈ V → (¬ (𝕊 x = Λ ))→ ‹ 𝕊 x, y+y› ∈ V :=
        begin
          intros x p h8 h90,
          have h8copy:= h8, 
          rw h120 at h8, 
          rw [binary_union_axiom, minus_members,singleton1] at h8, 
          rw singleton1 at h8, 
          rw or_comm at h8, 
          cases h8 with h9 h10,
          {
            rw ordered_pair_equality at h9,
            cases h9 with h11 h12,
            rw h11 at *,
            rw h12 at *,
            rw h120,
            rw [binary_union_axiom, minus_members], 
            left,
            have h24:= h23 zero one h22, 
            split,
            {
              exact h24 h90,
            },
            {
              rw singleton1,
              rw ordered_pair_equality,
              have h25:= Fregesuccessoromits0 M zero,
              intro h26,
              cases h26 with h27 h28,
              contradiction, 
            }
          },
          {
            cases h10 with h11 h12,
            rw h120,
            rw [binary_union_axiom, minus_members],
            left,
            rw singleton1,
            have h24:= h23 x p h11,
            split,
            {
              exact h24 h90,
            },
            {
              have h25:= Fregesuccessoromits0 M x,
              rw ordered_pair_equality,
              intro h26,
              cases h26 with h27 h28,
              contradiction, 
            }
          }
        end, 
      have h8: Egraph M ⊆ W:=
        begin
          rw subset_definition, 
          intros z h15,
          rw Egraph_members at h15, 
          cases h15 with h16 h17, 
          cases h16 with x h18,
          cases h18 with p h19,
          rw h19,
          have h30:= h17 W h6 h7,
          rw h19 at h30,
          exact h30, 
        end,
      have h108: Egraph M ⊆ V:=
        begin
          rw subset_definition, 
          intros z h15,
          rw Egraph_members at h15, 
          cases h15 with h16 h17, 
          cases h16 with x h18,
          cases h18 with p h19,
          rw h19,
          have h30:= h17 V h106 h107, 
          rw h19 at h30,
          exact h30, 
        end,
      have h8copy:= h8, 
      rw subset_definition at h8,
      have h9:= h8 ‹ zero, u › h2,
      rw h20 at h9,
      rw [binary_union_axiom, minus_members] at h9,
      cases h9 with h10 h11,
      {
        cases h10 with h12 h13,
        rw singleton1 at h13,
        contradiction,
      },
      {
        rw singleton1 at h11,
        rw ordered_pair_equality at h11,
        cases h11 with h12 h13,
        rw h13 at *,
        have h29:= h8 ‹ zero,y› h3,
        rw h20 at h29,
        rw [binary_union_axiom, minus_members] at h29,
        cases h29 with h40 h41,
        {  
          cases h40 with h42 h43, 
          rw singleton1 at h43, 
          rw ordered_pair_equality at h43,
          simp at h43, 
          have h44:= h8 ‹ zero,y › h3,
          rw h20 at h44, 
          rw [binary_union_axiom, minus_members] at h44,
          rw or_comm at h44,
          cases h44 with h45 h46,
          { 
            rw singleton1 at h45,
            rw ordered_pair_equality at h45,
            exact h45.right, 
          },
          {
            cases h46 with h47 h48,
            have h49:= h8 ‹ zero,y› h47, 
            rw h20 at h49,
            rw [binary_union_axiom, minus_members] at h49,
            rw or_comm at h49,
            cases h49 with h50 h51,
            {
              rw singleton1 at h50,
              rw ordered_pair_equality at h50,
              exact h50.right,
            },
            {
              have h52:= member_subset M (Egraph M) V ‹ zero,y› h108 h42,
              rw h120 at h52,
              rw [binary_union_axiom, minus_members] at h52,
              rw singleton1 at h52,
              rw singleton1 at h52, 
              simp at h52, 
              rw ordered_pair_equality at h52,
              exact h52.right,
            }
          }  
        },
        {
          rw singleton1 at h41,
          rw ordered_pair_equality at h41,
          exact h41.right, 
        }
      }
    }
  end

lemma Emaps2: ∀ (x:M), x ∈ ℍ →   ∀ (y u:M), ‹ x,u› ∈ Egraph M → ‹ x,y › ∈ Egraph M → y = u := 
  begin 
    have base: zero ∈ Z_Emaps2 M:= Emaps2_base M,
    have step: ∀ (x:M), x ∈ Z_Emaps2 M → (¬ (𝕊 x = Λ )) → 𝕊 x ∈ Z_Emaps2 M:=
      assume x,
      begin
        intros h h2, 
        rw Z_Emaps2_members,
        rw Z_Emaps2_members at h, 
        have h3:= Ehelper M, 
        cases h3 with h4 h5,
        cases h with h6 h7,
        have h20:= Emaps1 M x h6,
        cases h20 with y h21, 
        split,
        {
          exact successorH M x h6 h2, 
        },
        { 
          intros w z h8 h9, 
          set W:=  W_maps2 M x y with h22, 
          have h10: ‹ zero,one› ∈ W:=
            begin
              rw h22, 
              rw W_maps2_members,
              use zero, use one, 
              simp,
              have h23:= Ehelper M, 
              split,
              {
                exact h23.left,
              },
              {
                have h24:= Ehelper2 M zero one h23.left, 
                split,
                {
                  exact h24.left,
                },
                {
                  have h25:= Fregesuccessoromits0 M x, 
                  intro h26,
                  rw sym at h26,
                  contradiction,
                }
              }
            end,
          have h11: ∀(s t:M), ‹ s,t › ∈ W → (¬ (𝕊 s = Λ ))→ ‹ 𝕊 s, t+t › ∈ W :=
            assume s t,
            begin 
              rw h22,
              rw W_maps2_members, 
              intros h12 h90,
              cases h12 with p h13,
              cases h13 with q h14,
              rw ordered_pair_equality at h14,
              cases h14 with h15 h16,
              cases h15 with h17 h18,
              rw← h17 at *,
              rw← h18 at *,
              rcases h16 with ⟨ h19, h20, h23⟩, 
              rw W_maps2_members,
              use 𝕊 s, use t+t,
              simp,
              split,
              {
                exact (Ehelper M).right s t h19 h90,
              },
              {
                have h24:= h5 x y h21, 
                split,
                {
                  intro h25,
                  have h26: ¬ (s = Λ ):=
                    begin
                      intro h27,
                      rw h27 at h25,
                      have h28:= successorofempty M, 
                      contradiction, 
                    end,
                  have h27:= Ehelper2 M s t h19, 
                  have h28:= h27.left h26, 
                  have h29:= successorH M s h28 h25, 
                  exact h29,
                },
                {
                  intro h15,
                  have h25:= h90,
                  have h26: ¬ (s = Λ ):=
                    begin
                      intro h27,
                      rw h27 at h25,
                      have h28:= successorofempty M, 
                      contradiction, 
                    end, 
                  have h27:= (Ehelper2 M s t h19).left h26, 
                  have h28: ¬ (x = Λ ):=
                    begin
                      intro h37,
                      rw h37 at h2,
                      have h38:= successorofempty M, 
                      contradiction, 
                    end, 
                  have h29:= (Ehelper2 M x y h21).left h28, 
                  have h30:= successorH M s h27 h25, 
                  have h31:= successorH M x h6 h2, 
                  have h32:= successoroneoneonH M s x h27 h29 h30 h15, 
                  rw h32 at *,
                  have h33:= h5 x t h19, 
                  have h324:= h7 y t h19 h21, 
                  rw h324, 
                }
              },
            end, 
          have h12: Egraph M ⊆ W:= 
            begin
              rw subset_definition, 
              intro t,
              intro h13, 
              rw Egraph_members M at h13, 
              cases h13 with h14 h15, 
              cases h14 with p h16,
              cases h16 with q h17,
              rw h17 at *,
              have h18:= h15 W h10 h11, 
              exact h18, 
            end,
          have h13:= member_subset M (Egraph M) W ‹ x,y › h12 h21, 
          have h14:= h11 x y h13, 
          have h15:= member_subset M (Egraph M) W ‹ 𝕊 x, w ›h12 h9,
          have h16:= member_subset M (Egraph M) W ‹ 𝕊 x, z› h12 h8,
          rw h22 at h15,
          rw W_maps2_members M at h15,
          cases h15 with p h16,
          cases h16 with q h17,
          cases h17 with h18 h19,
          rw ordered_pair_equality at h18,
          cases h18 with h40 h41,
          rw← h40 at *,
          rw← h41 at *,
          rcases h19 with ⟨ h42, h43, h44⟩, 
          simp at h44, 
          rw h22 at h16,
          rw W_maps2_members M at h16,
          cases h16 with p h46,
          cases h46 with q h47,
          cases h47 with h48 h49,
          rw ordered_pair_equality at h48,
          cases h48 with h50 h51,
          rw← h50 at *,
          rw← h51 at *, 
          rcases h49 with ⟨ h62,h63,h64⟩,
          simp at h64, 
          rw [h44, h64], 
        }
      end,
    intros y h,
    rw H_members at h,
    specialize h (Z_Emaps2 M),
    have h3:= h (and.intro base step), 
    rw Z_Emaps2_members M at h3,
    exact h3.right,       
  end

lemma Ebase: 𝔼 M (zero:M) = (one:M) :=
  begin
    rw full_extensionality,
    intro t,
    rw E_members,
    split,
    {
      intro h,
      cases h with y h2,
      cases h2 with h3 h4,
      have h4:= Ehelper M, 
      cases h4 with h5 h6,
      have h7:= Emaps2 M zero (zeroH M) y one h5 h3,
      rw h7 at *,
      exact h4, 
    },
    {
      intro h,
      use one,
      split,
      {
        have h4:= Ehelper M,
        exact h4.left, 
      },
      {
        exact h,
      }
    }
  end

lemma Eworks: ∀ (x:M), x∈ ℍ → ‹ x, 𝔼 M x › ∈ Egraph M :=
  assume x,
  begin
    intros hx,
    have h3:= Emaps1 M x hx, 
    cases h3 with y h4,
    have h5: y = 𝔼 M x:=
      begin
        rw full_extensionality,
        intro t,
        split,
        {
          intro h6, 
          rw E_members,
          use y,
          exact ⟨ h4, h6⟩, 
        },
        {
          intro h5, 
          rw E_members M at h5, 
          cases h5 with p h6,
          cases h6 with h7 h8,
          have h9:= Emaps2 M x hx y p h7 h4, 
          rw h9,
          exact h8, 
        }
      end,
    rw←  h5,
    exact h4, 
  end

lemma E_members2: ∀ (x: M), x ∈ ℍ → ∀ (y:M), ‹ x,y › ∈ Egraph M ↔ y = 𝔼 M x:=
  assume x,
  begin
    intros hx y, 
    split,
    { 
      intro h,
      rw full_extensionality,
      intro t,
      rw E_members,
      split,
      {
        intro h2, 
        use y,
        exact ⟨ h, h2⟩, 
      },
      {
        intro h2,
        cases h2 with w h3,
        cases h3 with h4 h5,
        have h6:= Ehelper2 M x y h, 
        have h7:= Emaps2 M x hx y w h4 h, 
        rw h7,
        exact h5, 
      }
    },
    { 
      have h10:= Eworks M x hx,
      intro h11,
      rw h11 at *,
      exact h10,  
    }
  end

lemma exprecH: ∀ (x:M), x ∈ ℍ → ¬ ( 𝕊 x = Λ ) → 𝔼 M (𝕊 x) = 𝔼 M x + 𝔼 M x:=
  assume x,
  begin
    intros hx h2,
    have h3:= Eworks M x hx,
    have h4:= Ehelper M,
    cases h4 with h5 h6, 
    have h7:= h6 x (𝔼 M x) h3 h2, 
    have h8:= successorH M x hx h2, 
    have h9:= Eworks M (𝕊 x) h8, 
    have h10:= Emaps2 M (𝕊 x) h8 (𝔼 M (𝕊 x)) (𝔼 M x + 𝔼 M x) h7 h9, 
    exact h10, 
  end

lemma expH: ∀ (m:M), m ∈ ℍ  → ¬ (𝔼 M m = Λ) → 𝔼 M m ∈ ℍ :=
  begin
    have base: (zero:M) ∈  Z_expH M:=
      begin
        rw Z_expH_members,
        split,
        {
          exact zeroH M,
        },
        {
          intro h,
          have h2:= Ehelper M, 
          cases h2 with h3 h4,
          have h5:= Eworks M zero (zeroH M), 
          have h6:= Emaps2 M zero (zeroH M) one (𝔼 M zero) h5 h3, 
          have h7:= oneH M, 
          rw h6 at h7,
          exact h7,
        }
      end,
    have step: ∀ (m:M), m ∈ Z_expH M → (¬ 𝕊 m = Λ ) → 𝕊 m ∈ Z_expH M:=
      begin
        intros m h h2, 
        rw Z_expH_members at h, 
        cases h with h3 h4,
        rw Z_expH_members, 
        split,
        {
          exact successorH M m h3 h2, 
        },
        {
          intro h5, 
          have h6:= exprecH M m h3 h2, 
          have h7:= h5,
          have h8:= nonemptysum M (𝔼 M m), 
          have h9: (∃ u, u ∈ 𝔼 M (𝕊 m)) → ¬ (𝔼 M m = Λ ):=
            begin
              intros h10 h11, 
              rw h11 at h6,
              cases h10 with u h12, 
              rw full_extensionality at h6,
              specialize h6 u,
              have h13:= h6.mp h12, 
              rw addition_members at h13,
              cases h13 with p h14,
              cases h14 with q h15, 
              rcases h15 with ⟨ h16, h17, h18, h19⟩, 
              have h20:= emptyset_axiom q,
              contradiction, 
            end,
          have h10:= (nonempty_is_notnot_inhabited M (𝔼 M (𝕊 m))).mp h5, 
          have h11: ¬¬ ∃ (u:M), u ∈ 𝔼 M m + 𝔼 M m:=
            begin 
               simp_rw← h6, 
               exact h10, 
            end, 
          have h12: ¬ 𝔼 M m = Λ :=
            begin
              intro h13,
              simp_rw h13 at h11,
              simp_rw addition_members at h11, 
              have h14:¬ ∃ (u u_1 v : M), u = (u_1 ∪ v) ∧ u_1 ∈ Λ ∧ v ∈ Λ ∧ u_1 ∩ v = Λ:=
                begin
                  intro h15, 
                  cases h15 with p h16,
                  cases h16 with q h17,
                  cases h17 with r h18,
                  rcases h18 with ⟨ h19, h20, h21, h22⟩, 
                  have h23:= emptyset_axiom r,
                  contradiction, 
                end,
              contradiction,  
            end,
          have h13: 𝔼 M m ∈ ℍ := h4 h12,
          have h14 := nonemptysum M (𝔼 M m) h13 (𝔼 M m) h13, 
          rw h6, 
          apply h14, 
          rw← h6, 
          exact h5, 
        }
      end,
    intros y h,
    rw H_members at h,
    specialize h (Z_expH M),
    have h3:= h (and.intro base step), 
    rw Z_expH_members M at h3,
    exact h3.right,   
  end 

lemma Ezero: 𝔼 M zero = one:=
  begin
    have h2:= Eworks M zero (zeroH M), 
    have h3:= Ehelper M, 
    cases h3 with h4 h5, 
    have h6:= Emaps2 M zero (zeroH M) (𝔼 M zero) one h4 h2, 
    exact h6,
  end

lemma Etoexp: ∀ (y:M), y ∈ ℍ → (∃ (u:M), u ∈ exp M y) → 𝔼 M y = exp M y:=
  begin
    have base: zero ∈ Z_Etoexp M:=
      begin
        rw Z_Etoexp_members, 
        split,
        {
          exact zeroH M,
        },
        {
          intro h,
          cases h with u h2,
          have h3:= exp_zero M, 
          have h4:= Ezero M, 
          rw h3,
          exact h4, 
        }
      end,
    have step: ∀ (y:M), y ∈ Z_Etoexp M → (¬ 𝕊 y = Λ ) → 𝕊 y ∈ Z_Etoexp M:=
      begin
        intros y h h2,
        rw Z_Etoexp_members M at h, 
        cases h with h3 h4, 
        rw Z_Etoexp_members M, 
        split,
        {
          exact successorH M y h3 h2, 
        },
        { 
          intro h20,
          have h20copy:= h20,
          cases h20 with u h21,
          rw exp_members at h21,
          cases h21 with a h22,
          cases h22 with h23 h24, 
          have h23copy:= h23,
          rw successor_members M at h23, 
          cases h23 with x h25,
          cases h25 with c h26,
          rcases h26 with ⟨ h27, h28, h29⟩, 
          have h30:= inhabitedHisF M y h3 ⟨ x,h27⟩,
          have h31:= successorF M y h30 ⟨ USC a, h23copy⟩,
          have h32:= finiteexp M (𝕊 y) h31 h20copy, 
          have h6:= exprec M y h30 h32, 
          simp_rw h6 at h20copy, 
          cases h20copy with u h33,
          rw addition_members M at h33, 
          cases h33 with p h34,
          cases h34 with q h35, 
          rcases h35 with ⟨ h36, h37, h38, h39⟩, 
          have h40:= h4 ⟨ p, h37⟩,
          have h41:= exprecH M y h3 h2,
          rw h40 at h41, 
          rw [h6, h41], 
        }
      end,
    intros y h,
    rw H_members at h,
    specialize h (Z_Etoexp M),
    have h3:= h (and.intro base step), 
    rw Z_Etoexp_members M at h3,
    exact h3.right,  
  end
 
/-- 
lemma successorinhabitedimpliesinfinity: (∀ (x:M), x∈ 𝔽 → (∃ (u:M),u ∈ 𝕊 x)) → infinite M 𝔽:=
  begin
    intro  h,
    unfold infinite, 
    set y:= 𝔽 - single zero with h11,
    use y,
    split,
    {
      rw subset_definition,
      intro t,
      rw h11,
      rw minus_members,
      intro h12,
      cases h12 with h13 h14,
      exact h13,
    },
    {
      split,
      {
        rw h11,
        intro h12,
        rw full_extensionality at h12,
        specialize h12 zero,
        rw minus_members at h12,
        rw singleton1 at h12,
        have h13:= zeroF M,
        rw h12 at h13,
        cases h13 with h14 h15,
        contradiction,
      },
      {
        unfold similar,
        sorry, 
      }
    }
  end


lemma notnotmaxint: 𝔽 ∈ FINITE M → ¬¬ ∃(m:M),(m ∈ 𝔽 ∧ ¬ (𝕊 m ∈ 𝔽 )):=
  begin
    intros h2 h3,
    rw not_exists at h3,
    have h4: ∀ (x:M),(x∈ 𝔽 → ¬¬ ∃(t:M), t ∈ 𝕊 x):=
      begin
        intros x hx,
        specialize h3 x,
        have h5: ¬¬ 𝕊 x ∈ 𝔽:=
          begin
            intro h6, 
            apply h3,
            exact ⟨ hx, h6⟩, 
          end,
        have h7: 𝕊 x ∈ 𝔽 → ∃ (t:M), t ∈ 𝕊 x:=
          begin
            intro h8,
            exact cardinalsinhabited M (𝕊 x) h8,
          end,
        have h9:= notnot_imp(𝕊 x ∈ 𝔽)( ∃ (t:M), t ∈ 𝕊 x) h7 h5,
        exact h9,
      end,
    have h10:= successorinhabitedimpliesinfinity M,
    have h11:= infiniteimpliesnotfinite M 𝔽 ,
    have h12:= λ p, h11 (h10 p),
    have h13:= notnot_imp (∀ (x : M), x ∈ 𝔽 → (∃ (u : M), u ∈ 𝕊 x))
      (¬𝔽 ∈ FINITE M) h12, 
    rw triplenegation at h13,
    have h14:= finiteDNS M (Z_notnotmaxint M) 𝔽 h2,
    simp_rw Z_notnotmaxint_members at h14,
    have h15:= h14 h4,
    have h16:= successorinhabitedimpliesinfinity M,
    have h17:  ¬¬ (infinite M 𝔽 ):=
      begin
        have h20:= notnot_imp ((∀ (x : M), x ∈ 𝔽 → (∃ (u : M), u ∈ 𝕊 x))) (infinite M 𝔽 ) h16, 
        apply h20,
        exact h15, 
      end,
    have h18:=infiniteimpliesnotfinite M 𝔽, 
    have h19:= notnot_imp (infinite M 𝔽 )( ¬ 𝔽 ∈ FINITE M) h18 h17,
    rw triplenegation at h19,
    contradiction,
  end
-/ 

lemma maxintegerimpliesFfinite: ∀ (m:M), m ∈ 𝔽 → 𝕊 m = Λ → 𝔽 ∈ FINITE M:=
  assume m,
  begin
    intros hm hsm,
    have h4: 𝔽 = Jbar M m:=
      begin
        rw full_extensionality,
        intro t,
        rw Jbar_members,
        split,
        {
          intro ht,
          split,
          {
            exact ht,
          },
          {
            have h5:= maxinteger M m hm hsm t ht,
            exact h5,
          }
        },
        {
          intro h4,
          exact h4.left,
        }
      end,
    have h5:= Jbarfinite M m hm,
    rw h4,
    exact h5,
  end



#axioms_all  --This file is clean. 

