import inf24

variables (M:Type) [Model M] (a b x y z u v w X R W κ μ ℓ : M)

open Model 

lemma zeroNC: zero ∈ NC M:=
  begin
    rw NC_members,
    have h4:= Nc_Lambda M,
    use (Λ:M),
    rw sym,
    exact h4,
  end

lemma imageunion: ∀(f A B:M), maps M f A B → ∀ (x y:M), x ⊆ A → y ⊆ A → image M f (x ∪ y ) = ((image M f x) ∪ (image M f y)):=
  begin
    intros f A B hmaps x y hx hy,
    rw full_extensionality,
    intros t,
    split,
    {
      intros h3,
      unfold maps at hmaps,
      cases hmaps with hrel h20,
      rw image_members M f (x ∪ y) hrel  at h3,
      rw binary_union_axiom,
      cases h3 with a h4,
      cases h4 with h5 h6,
      rw binary_union_axiom at h5,
     
      cases h5 with h7 h8,
      {
        left,
        rw image_members M f x hrel,
        use a,
        exact ⟨ h7, h6⟩,
      },
      {
        right,
        rw image_members M f y hrel,
        use a,
        exact ⟨h8, h6⟩,
      }
    },
    {
      intros h30,
      unfold maps at hmaps,
      cases hmaps with hrel h20,
      rw image_members M f (x ∪ y) hrel,
      rcases h20 with ⟨ h21, h22,h23⟩,
      rw binary_union_axiom at h30,
      cases h30 with h31 h32,
      {
        rw image_members M f x hrel at h31,
        cases h31 with a h32,
        use a,
        split,
        {
          rw binary_union_axiom,
          left,
          exact h32.1,
        },
        {
          exact h32.2,
        }
      },
      {
        rw image_members M f y hrel at h32,
        cases h32 with b h33,
        use b,
        split,
        {
          rw binary_union_axiom,
          right,
          exact h33.1,
        },
        {
          exact h33.2,
        }
      }
    }
  end  

lemma imageintersection: ∀(f A B:M), maps M f A B → 
∀ (x y:M), x ⊆ A → y ⊆ A → x ∩ y = Λ →
oneone M f A B →
(image M f x) ∩ (image M f y) = Λ:=
  begin
   intros f A B hmaps x y hx hy h3 honeone,
   rw full_extensionality,
   intros t,
   rw intersection_axiom,
   split,
   {
      intros h4,
      cases h4 with h5 h6,
      unfold maps at hmaps,
      cases hmaps with hrel h31,
      rw image_members M f x hrel at h5,
      rw image_members M f y hrel at h6,
      cases h5 with a h7,
      cases h6 with b h8,
      cases h7 with ha h10,
      cases h8 with hb h12,
      unfold oneone at honeone,
      rcases honeone with ⟨ hmaps, h13, h14⟩,
      have h20:= member_subset M x A a hx ha,
      have h15:= h13 a b t ⟨ h10, h12, h20⟩,
      rw h15 at *,
      rw full_extensionality at h3,
      have h22:= h3 b,
      rw intersection_axiom at h22,
      have h23:= h22.1 ⟨ ha, hb⟩,
      have h24:= emptyset_axiom b,
      contradiction,   
   },
   {
     intros h33,
     have h34:= emptyset_axiom t,
     contradiction,
   }
  end

lemma adjointNC: ∀(x c:M), ¬(c ∈ x)  → Nc M (x ∪ (single c)) = Nc M x + one:=
  begin
    intros x c hc,
    rw full_extensionality,
    intros t,
    rw addition_members,
    split,
    {
      intros h,
      rw Nc_members at h,
      rw similar_symmetric at h,
      unfold similar at h,
      cases h with f h3,
      set u:= image M f x with udef,
      have h5:= subset_union M x x (single c) (subset_reflexive M x),
      have h4:= similarity_subset M f x (x ∪ single c) t h3 h5,
      rw← udef at h4,
      have h6: similar M x u:=
        begin
          unfold similar,
          use f,
          exact h4,
        end,
      --rw similar_symmetric at h6,
      have h8: Nc M x ∈ NC M:=
        begin
          rw NC_members,
          use x,
        end,
      have h7:= cardinals0 M (Nc M x) x u h8 (xinNcx M x) h6,
      have h3copy:= h3,
      -- we need to fetch f(c)
      unfold similarity at h3copy,
      cases h3copy with h20 h21,
      unfold oneone at h20,
      rcases h20 with ⟨ h22, h23, h24⟩,
      unfold maps at h22,
      cases h22 with hrel h25,
      rcases h25 with ⟨ h26, h27, h28⟩,
      have h30: c ∈ x ∪ single c:=
        begin
          rw binary_union_axiom,
          rw singleton1,
          simp,
        end,
      have h29:= h28 c h30,
      cases h29 with fc h31,
      cases h31 with hfc h32,
      have h33: ¬ fc ∈ u :=
        begin
          intros h34,
          rw udef at h34,
          rw image_members at h34,
          cases h34 with q h35,
          cases h35 with hq h36,
          have h37:= h23 c q fc ⟨ h32, h36, h30⟩,
          rw← h37 at *,
          contradiction,
          exact hrel,
        end, 
      have h38: single fc ∈ one := 
        begin
          rw one_members,
          use fc,
        end,
      have h3copy:= h3,
      unfold similarity at h3copy,
      cases h3copy with honeone honto,
      unfold oneone at honeone,
      cases honeone with hmaps h50,
      have h40:= imageunion M f (x ∪ single c)t hmaps x (single c),
      have h41: single c ⊆ x ∪ single c:=
        begin
          rw subset_definition,
          intros t,
          rw singleton1,
          intros h50,
          rw h50 at *,
          rw binary_union_axiom,
          rw singleton1,
          simp,
        end,
      have h42:= subset_union2 M x (single c),
      have h43:= h40 h42 h41,
      use image M f x,
      use image M f (single c),
      have h44: t = image M f (x ∪ (single c)):=
        begin
          rw full_extensionality,
          intros w,
          unfold onto at h21,
          split,
          {
            intros hw,
            have h60:= h21 w hw,
            rw image_members M f (x ∪ (single c)) hrel,
            exact h60,
          },
          {
            intros h61,
            rw image_members M f (x ∪ (single c)) hrel at h61,
            cases h61 with a h62,
            cases h62 with h63 h64,
            unfold maps at hmaps,
            cases hmaps with hrel2 h65,
            have h66:= h65.1 a w,
            apply h66,
            exact ⟨ h63, h64⟩,
          }
        end,
      have h45: x ∩ (single c) = Λ:=
        begin
          rw full_extensionality,
          intros p,
          rw intersection_axiom,
          split,
          {
            intros h46,
            rw singleton1 at h46,
            cases h46 with h47 h48,
            rw h48 at *,
            contradiction,
          },
          {
            intros h49,
            have  h500:= emptyset_axiom p,
            contradiction,
          }
        end,
      unfold similarity at h3,
      have h201: image M f (single c) = single fc :=
        begin
          rw full_extensionality,
          intros w,
          rw singleton1,
          rw image_members M f (single c) hrel,
          split,
          {
            intros h202,
            cases h202 with e h204,
            rw singleton1 at h204,
            cases h204 with h205 h206,
            rw h205 at *,
            have h207:= h27 c w fc,
            apply h207,
            exact ⟨h30, h206, h32⟩, 
          },
          {
            intros h210,
            rw h210 at *,
            use c,
            rw singleton1,
            simp,
            exact h32,
          }
        end,
      have h200:= imageintersection M f (x ∪ (single c)) t hmaps x (single c) h42 h41 h45 h3.1,
      have h220: t = (u ∪ (single fc)) :=
        begin
          rw h44,
          rw h43,
          rw h201,
        end,
      repeat{split},
      {
        rw h220,
        rw h201,
      },
      {
        rw← udef,
        have h301: Nc M x ∈ NC M:=
          begin
            rw NC_members,
            use x,
          end, 
        have h300:= cardinals0 M (Nc M x) x u h301 (xinNcx M x) h6,
        exact h300,
      },
      {
        rw one_members,
        use fc,
        exact h201,
      },
      {
        exact h200,
      },
    },
    {  -- right to left 
      intros h400,
      cases h400 with u h401,
      cases h401 with z h402,
      rcases h402 with ⟨ h403, h404, h405, h406⟩,
      have h407:= cardinals0 M (Nc M (x ∪ single c)) (x ∪ single c) t,
      have h430:= h405,
      rw one_members M z at h430,
      cases h430 with a h441,
      have h410:= cardinals2 M (Nc M x) x u,
      have h411: Nc M x ∈ NC M:=
        begin
          rw NC_members,
          use x,
        end,
      have h412:= h410 h411 (xinNcx M x) h404,
      have h423: similar M z (single c):=
        begin
          rw one_members at h405,
          cases h405 with a h406,
          rw h406,
          have h407:= similar_singletons M a c,
          exact h407,
        end,
      have h450:= h423,
      unfold similar at h450,
      cases h450 with f h451,
      unfold similarity at h451,
      cases h451 with h452 h453,
      unfold oneone at h452,
      cases h452 with h455 h456,
      unfold similar at h412,
      cases h412 with f h413,
      have ha: ¬ a ∈ u:=
        begin
          rw h441 at h406,
          intros h,
          rw full_extensionality at h406,
          specialize h406 a,
          rw intersection_axiom at h406,
          rw singleton1 at h406,
          simp at h406,
          rw h406 at h,
          have h407:= emptyset_axiom a,
          contradiction,
        end,
      have h457:= extend_similarity M x u c a f h413 hc ha,
      have h458: similar M (x ∪ single c)(u ∪ single a):=
        begin
          unfold similar,
          exact h457,
        end,
      rw← h441 at *,
      rw← h403 at *,
      have h480:= cardinals0 M (Nc M (x ∪ single c))(x ∪ single c) t,
      apply h480,
      rw NC_members,
      use x ∪ single c,
      exact xinNcx M (x ∪ single c),
      exact h458,
    }
  end

lemma equalNC: ∀(u v:M), similar M u v → Nc M u = Nc M v:=
  begin
    intros u v h,
    set κ := Nc M u with kappadef,
    have h2: κ ∈  NC M:=
      begin
        rw NC_members,
        use u,
      end,
    have h3:= cardinals0 M κ u v h2 (xinNcx M u) h,
    have h4:= xinNcx M v,
    have h10: Nc M v ∈ NC M:=
      begin
        rw NC_members,
        use v,
      end,
    have h5:= cardinalsdisjoint2 M κ (Nc M v) v h2 h10 h3 h4,
    exact h5,
  end

lemma successorNC: ∀(n:M), n ∈ NC M → (∃(u:M), u ∈ 𝕊 n) → 𝕊 n ∈ NC M:=
  begin
    intros m h3 hsm,
    have h3copy:= h3,
    rw NC_members at h3,
    cases h3 with u hm,
    cases hsm with z h23,
    rw successor_members at h23,
    cases h23 with v h4,
    cases h4 with c h5,
    cases h5 with hv h6,
    cases h6 with h7 h8,
    have h10:= Nc_unitclass M c,
    have h11: Nc M (v ∪ single c) ∈ NC M:=
      begin
        rw NC_members,
        use (v ∪ single c),
      end,
    have h12: v ∩ single c = Λ:=
      begin
        rw full_extensionality,
        intros t,
        rw intersection_axiom,
        rw singleton1,
        split,
        {
          intros h,
          cases h with h13 h14,
          rw h14 at *,
          contradiction,
        },
        {
          intros h15,
          have h16:= emptyset_axiom t,
          contradiction,
        }
      end,
    have h13: Nc M (v ∪ single c) = Nc M v + one:=
      adjointNC M v c h7,
    have h20:= xinNcx M u,
    rw← hm at h20, 
    have h14:= cardinals2 M m u v h3copy h20 hv,
    have h21:= equalNC M u v h14,
    rw←h21 at h13,
    rw← hm at h13,
    rw← successorisplusone at h13,
    rw NC_members,
    use v ∪ (single c),
    rw sym,
    exact h13, 
  end  

lemma FtoNC: ∀ (n:M), n ∈ 𝔽→ n ∈ NC M:=
  begin
    have base:= zeroNC M,
    have step:= successorNC M,
    intros n hn,
    rw F_members at hn,
    specialize hn (NC M),
    have h12:= hn ⟨base, step⟩,
    exact h12, 
  end 

lemma FsubsetNC: 𝔽 ⊆ NC M:=
  begin
    have h:= FtoNC M,
    rw subset_definition,
    exact h,
  end

lemma ledotreflexive: ∀ (n:M), n ∈ NC M → n ⪯ n:=
  begin
    intros n hn,
    have hncopy:= hn,
    rw NC_members at hn,
    cases hn with a h2,
    have h3:= ledot_definition n n,
    rw h3,
    have h4:= cardinalsinhabited2 M n hncopy,
    cases h4 with b h5,
    use b, use b,
    simp,
    have h6:= subset_reflexive M b,
    exact ⟨ h5, h6⟩,
  end

lemma ledottransitive: ∀ (n m k:M), n ∈ NC M → m ∈ NC M → k ∈ NC M →  
n ⪯ m → m ⪯ k → n ⪯ k:=
  begin
    intros n m k hn hm hk hnm hmk,
    have hmkcopy := hmk,
    rw ledot_definition m k at hmkcopy,
    cases hmkcopy with a h3,
    cases h3 with b h4,
    rcases h4 with ⟨ ha,hb,h5⟩,
    have h6:= le2NC M a n m hn hm hnm ha,
    cases h6 with c h7,
    rw ledot_definition,
    use c,
    use b,
    have h8:= subset_transitive M c a b h7.2 h5,
    exact ⟨ h7.1, hb, h8⟩,
  end

lemma xnotlessdotx: ∀(n:M), n ∈ NC M → ¬ (n ⋖ n):=
  begin
    intros n hn,
    have h4:= ledotreflexive M n hn,
    intros h5,
    rw lessdot_definition at h5,
    rcases h5 with ⟨ h6, h7, h8⟩,
    contradiction,
  end

lemma scsimilar: ∀ (a b:M), similar M a b →  similar M (SC a)(SC b):= 
  assume a b,
  begin
    intro h,
    unfold similar at h,
    cases h with f h2,
    have h2copy:= h2,
    have h200: Rel f:=
      begin 
        unfold similarity at h2copy,
        unfold oneone at h2copy,
        cases h2copy with h201 h202,
        cases h201 with h203 h204,
        unfold maps at h203,
        cases h203 with h205 h206,
        exact h205, 
      end, 
    have h300: ∀(x:M),  Rel (restrict f x):=
      assume x,
      begin
        rw Rel_definition,
        intro z,
        rw restrict_definition, 
        rw intersection_axiom,
        rw product_axiom,
        intro h43,
        cases h43 with h44 h45,
        cases h45 with p h46,
        cases h46 with q h47,
        use p, use q,
        exact h47.right.right, 
      end,
    set g := Z43 M f a with h3,
    unfold similar,
    use g,
    unfold similarity,
    unfold oneone,
    unfold maps,
    repeat{split}, 
    { 
      rw Rel_definition,
      intro z,
      rw h3,
      rw Z43_members M,
      intro h4,
      cases h4 with u h5,
      cases h5 with v h6,
      use u, use v,
      exact h6.left, 
    },
    {
      intros  x y h4,
      cases h4 with h5 h6,
      rw Z43_members at h6,
      cases h6 with u h7,
      cases h7 with v h8,
      cases h8 with h9 h10,
      rw ordered_pair_equality at h9,
      cases h9 with h11 h12,
      rw h11 at *,
      rw h12 at *,
      cases h10 with h13 h14,
      rw sc_members, 
      rw subset_definition, 
      intro z,
      rw full_extensionality at h14,
      specialize h14 z,
      rw h14,
      intro h15,
      rw range_axiom at h15,
      simp_rw restrict_definition at h15, 
      rw h11 at *,
      rw h12 at *,
      unfold similarity at h2,
      {
        cases h2 with h20 h21,
        unfold oneone at h20,
        cases h20 with h22 h23, 
        cases h15 with p h24,
        rw intersection_axiom at h24,
        cases h24 with h25 h26,
        rw product_axiom at h26, 
        cases h26 with r h27,
        cases h27 with s h28,
        rw ordered_pair_equality at h28,
        rcases h28 with ⟨ h29, h30,h31,h32⟩,
        rw h31 at *,
        rw h32 at *,
        unfold maps at h22,
        cases h22 with h33 h34,
        rcases h34 with ⟨ h35, h36, h37⟩,
        specialize h35 r s,
        rw sc_members at h5,
        have h38:= h5,
        have h40:= member_subset M u a r h38 h29,
        exact h35 ⟨ h40, h25⟩, 
      },
      {
        rw Rel_definition,
        intros z h20,
        rw restrict_definition f u at h20,
        rw intersection_axiom at h20,
        cases h20 with h21 h22,
        rw product_axiom at h22,
        cases h22 with p h23,
        cases h23 with q h24,
        rcases h24 with ⟨ h25, h26,h27⟩,
        use p, use q,
        exact h27,
      } 
    },
    {
      intros x y z h20,
      rcases h20 with ⟨ h21, h22, h23⟩,
      rw h3 at h22 h23,
      rw Z43_members at h22 h23,
      cases h23 with u h24,
      cases h24 with v h25,
      cases h22 with p  h26,
      cases h26 with q h27,
      cases h25 with h28 h29,
      cases h27 with h30 h31,
      rw ordered_pair_equality at h28 h30,
      cases h30 with h32 h33,
      cases h28 with h34 h35,
      rw← h32 at *,
      rw← h34 at *,
      rw← h33 at *,
      rw← h35 at *,
      cases h31 with h40 h41,
      cases h29 with h42 h43,
      rw h41,
      rw h43, 
    },
    { have h100: Rel (f ∩ (a × 𝕍)):=
        begin
          rw Rel_definition,
          intros z h21,
          rw intersection_axiom at h21,
          cases h21 with h22 h23,
          rw product_axiom at h23,
          cases h23 with p h24,
          cases h24 with q h25,
          rcases h25 with ⟨ h26, h27, h28⟩,
          use p, use q,
          exact h28, 
        end, 
      intros x h20,
      rw h3,
      set y:= image M f x with h21,
      use y,
      rw sc_members at h20,
      rw Z43_members,
      rw sc_members,
      unfold similarity at h2copy,
      cases h2copy with h201 h202,
      unfold oneone at h201,
      rcases h201 with ⟨ h203, h204, h205⟩,
      split,
      {
        have h200:= image_subset M f a b x h203 h20,
        rw h21,
        exact h200,
      },
      {
        use x, use y, 
        simp,
        rw sc_members,
        split,
        {
          exact h20,
        },
        {
          rw h21,
          rw full_extensionality,
          intros t,
          split,
          {
            intros h210,
            rw image_members at h210,
            cases h210 with z h211,
            cases h211 with hz hzt,
            rw range_axiom,
            use z,
            rw restrict_definition,
            rw intersection_axiom,
            rw product_axiom,
            split,
            {
              exact hzt,
            },
            {
              use z, use t,
              simp,
              exact ⟨ hz, V_definition t⟩,
            },
            {
              have h220:= restriction M f x,
              exact h300 x,
            },
            {
              exact h200,
            }
          },
          {
            intros h250,
            rw image_members,
            rw range_axiom at h250,
            cases h250 with u h251,
            use u,
            have h252:= (restriction M f x u t).1 h251,
            exact ⟨ h252.2, h252.1⟩,
            exact h300 x,
            exact h200,
          },
        }
      }
    },
    {  -- to prove g is one-to-one 
      intros x z y,
      rw h3,
      intros h400,
      rcases h400 with ⟨ h401, h402, h403⟩,
      rw sc_members at h403,
      rw Z43_members at h401 h402,
      cases h402 with p h403,
      cases h403 with q h404,
      rcases h404 with ⟨ h405, h406, h407⟩,
      rw ordered_pair_equality at h405,
      rw← h405.1 at *,
      rw← h405.2 at *,
      rw sc_members at h406,
      cases h401 with P h403,
      cases h403 with Q h4041,
      rcases h4041 with ⟨ h4051, h4061, h4071⟩,
      rw ordered_pair_equality at h4051,
      rw← h4051.1 at *,
      rw← h4051.2 at *,
      rw sc_members at h4061,
      rw h4071 at h407,
      rw full_extensionality at h407,
      rw full_extensionality,
      intros t,
      unfold similarity at h2copy,
      cases h2copy with h410 h411,
      unfold oneone at h410,
      cases h410 with h412 h413,
      unfold maps at h412,
      rcases h412 with ⟨ hrel, h415, h416, h417 ⟩,
      
      split,
      {
        intros ht,
        have h418:= member_subset M x a t h403 ht,
        have h419:= h417 t h418,
        cases h419 with ft h420,
        cases h420 with hft h421,
        have h422:= h407 ft,
        have h423: ft ∈ range (restrict f x):=
          begin
            rw range_axiom,
            use t,
            rw restriction,
            exact ⟨h421, ht⟩, 
            exact h300 x,
          end,
        rw h422 at h423,
        rw range_axiom at h423,
        cases h423 with q h424,
        rw restriction at h424,
        cases h424 with h425 h426,
        have h427:= h413.1 t q ft ⟨ h421, h425, h418⟩,
        rw h427 at *,
        exact h426,
        exact h300 z,
      },
      {
        intros ht,
        have h418:= member_subset M z a t h406 ht,
        have h419:= h417 t h418,
        cases h419 with ft h420,
        cases h420 with hft h421,
        have h422:= h407 ft,
        have h423: ft ∈ range (restrict f z):=
          begin
            rw range_axiom,
            use t,
            rw restriction,
            exact ⟨h421, ht⟩, 
            exact h300 z,
          end,
        rw←  h422 at h423,
        rw range_axiom at h423,
        cases h423 with q h424,
        rw restriction at h424,
        cases h424 with h425 h426,
        have h427:= h413.1 t q ft ⟨ h421, h425, h418⟩,
        rw h427 at *,
        exact h426,
        exact h300 x,
      }
    },
    {
      intros x y h500,
      rw h3 at h500,
      cases h500 with h501 h502,
      rw Z43_members at h501,
      cases h501 with u h503,
      cases h503 with v h504,
      rw ordered_pair_equality at h504,
      cases h504 with h505 h506,
      rw h505.1 at *,
      rw h505.2 at *,
      cases h506 with h507 h508,
      rw sc_members at h502,
      rw sc_members,
      rw sc_members at h507,
      exact h507,
    },
    {
      unfold onto,
      intros y hy,
      rw sc_members at hy,
      set x:= preimage2 M f a y with xdef,
      use x,
      rw sc_members,
      split,
      {
        rw subset_definition,
        intros t,
        rw preimage2_members,
        intros h510,
        cases h510 with ht h511,
        exact ht,
      },
      {
        rw h3,
        rw Z43_members,
        use x, use y,
        simp,
        split,
        {
          rw xdef,
          rw sc_members,
          rw subset_definition,
          intros t ht,
          rw preimage2_members at ht,
          exact ht.1,
        },
        {
          rw full_extensionality,
          intros t,
          rw range_axiom,
          unfold similarity at h2copy,
          cases h2copy with honeone honto,
          unfold onto at honto,
          have h350:= member_subset M y b t hy,
          split,
          {
            intros ht,
            have h351:= h350 ht,
            have h352:= honto t h351, 
            cases h352 with u h353,
            use u,
            rw restriction,
            split,
            {
              exact h353.2,
            },
            {
              rw xdef,
              rw preimage2_members,
              split,
              {
                exact h353.1,
              },
              {
                use t,
                exact ⟨ht, h353.2⟩, 
              }
            }
          },
          { 
            intros h360,
            cases h360 with u h361,
            rw restriction at h361,
            cases h361 with h362 h363,
            rw xdef at h363,
            rw preimage2_members at h363,
            cases h363 with h364 h365,
            cases h365 with T h366,
            cases h366 with h367 h368,
            have h369:t = T:=
              begin
                unfold oneone at honeone,
                cases honeone with hmaps h370,
                unfold maps at hmaps,
                rcases hmaps with ⟨ hrel, h371, h372, h373⟩,
                have h380:= h372 u t T,
                apply h380,
                exact ⟨ h364, h362, h368⟩,
              end,
            rw h369 at *,
            exact h367,
          },
          exact h300 x,
        },
      } 
    }
  end

lemma NCexp2def: ∀ (m a:M), m ∈ NC M  → USC a ∈ m → exp2 M m = Nc M (SC a):=
  assume m a,
  begin
    intros h1 h2,
    rw full_extensionality,
    intro x,
    rw Nc_members,
    rw exp2_members,
    split,
    { 
      intro h3,
      cases h3 with b h4,
      cases h4 with h5 h6,
      rw h6 at *,
      have h7: similar M (USC a) (USC b):= cardinals2 M m (USC a)(USC b) h1 h2 h5, 
      rw← uscsimilar at h7, 
      have h8:= scsimilar M a b h7, 
      rw similar_symmetric at h8,
      exact similar_transitive M x (SC b) (SC a) h6 h8, 
    },
    {
      intro h3,
      use a,
      exact ⟨ h2, h3⟩, 
    }
  end     

lemma sc_subset: ∀ (a b:M), a ⊆b → SC a ⊆ SC b:=
  begin
    intros a b h3,
    rw subset_definition,
    intros t ht,
    rw sc_members at ht,
    rw sc_members,
    exact subset_transitive M t a b ht h3,
  end   

lemma NCexp2:  ∀ (m:M), m ∈ NC M → (∃(y:M), y ∈ exp2 M m) → exp2 M m ∈ NC M:=
  assume m,
  begin
    intros h1 h2,
    cases h2 with y h3,
    rw exp2_members at h3,
    cases h3 with a h4,
    cases h4 with h5 h6, 
    have h12: SC a ∈ exp2 M m:=
      begin
        rw exp2_members M, 
        use a,
        exact ⟨ h5, similar_reflexive M (SC a)⟩, 
      end,
    have h14: exp2 M m = Nc M (SC a):= NCexp2def M m a h1 h5,
    rw h14 at *,
    rw NC_members,
    use SC a, 
  end

lemma subsetusc: ∀(a z:M), z ⊆ USC a → ∃ (c:M), z = USC c:=
  begin
    intros a z h14,
    have h14copy:= h14,
    set c:= union z with cdef,
    use c, 
    rw cdef,
    rw full_extensionality,
    intros t,
    rw subset_definition at h14,
    specialize h14 t,
    split,
    {
      intros ht,
      have h16:= h14 ht,
      rw usc at h16,
      cases h16 with w h17,
      cases h17 with h18 h19,
      rw h19 at *,
      rw usc_members,
      rw union_axiom,
      use single w,
      rw singleton1,
      simp,
      exact ht,
    },
    {
      intros h20,
      rw usc at h20,
      cases h20 with s h21,
      cases h21 with h22 h23,
      rw h23 at *,
      rw union_axiom at h22,
      cases h22 with w h24,
      cases h24 with h25 h26,
      have h17:= member_subset M z (USC a) w h14copy  h25,
      rw usc at h17,
      cases h17 with r h18,
      cases h18 with h19 h40,
      rw h40 at *,
      rw singleton1 at h26,
      rw h26 at *,
      exact h25,
    }
  end

lemma exporderNC: ∀ (m n:M), m ∈ NC M → n ∈ NC M → m ⪯ n → (∃(u:M), u ∈ exp2 M n) → exp2 M m ∈ NC M ∧ exp2 M m ⪯ exp2 M n:=
  begin
    intros m n hm hn hle h3,
    have h3copy:= h3,
    cases h3 with u h4,
    have h4copy:= h4,
    rw exp2_members at h4,
    cases h4 with a h5,
    cases h5 with h6 h7,
    have h9:= NCexp2 M n hn h3copy,
    have h8:= cardinals0 M (exp2 M n) u (SC a) h9 h4copy h7,
    have h10:= le2NC M (USC a) m n hm hn hle h6,
    cases h10 with z h11,
    cases h11 with h12 h14,
    set c:= union z with cdef,
    have h14copy:= h14,
    have h115:= subsetusc M a z h14copy,
    cases h115 with c h15,
    have h50:= h12,
    rw h15 at h50,
    have h51: SC c ∈ exp2 M m:=
      begin
        have h52:= (exp2_members M m (SC c)).2,
        apply h52,
        use c,
        exact ⟨ h50, similar_reflexive M (SC c)⟩,
      end,
    have h53:= NCexp2 M m hm ⟨ SC c, h51⟩, 
    have h60: USC c ⊆ USC a:=
      begin
        have h59:= cdef,
        rw h15 at h59,
        rw subset_definition,
        intros t ht,
        rw full_extensionality at h59,
        specialize h59 t,
        have h60:= member_subset M z (USC a) t h14,
        apply h60,
        rw h15,
        exact ht,
      end,
    have h70: c ⊆ a:=
      begin
        have h71:= usc_subset M c a,
        rw h71,
        exact h60,
      end,
    
    split,
    {
      exact h53,
    },
    {
      rw ledot_definition,
      use (SC c), use (SC a),
      repeat{split},
      {
        exact h51,
      },
      {
        exact h8,
      },
      {
        exact sc_subset M c a h70,
      }
    },
  end

#axioms_all
