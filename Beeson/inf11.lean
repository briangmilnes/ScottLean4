 -- Results about T
import inf10
variables (M:Type) [Model M] (a b x y z u v w X R W κ μ ℓ : M)
-- using ℓ where the source text has λ because you can't use λ for a variable.

open Model 

lemma Tmembers: ∀ (x κ :M), x ∈ κ → USC x ∈ 𝕋 M κ:=
  assume x κ,
  begin
    intro h,
    rw T_members,
    use x,
    exact ⟨ h, similar_reflexive M (USC x) ⟩, 
  end

lemma Tmembers2:  ∀ (x κ :M), κ ∈ 𝔽 → (x ∈ κ ↔ USC x ∈ 𝕋 M κ ):=
  assume x κ, 
  begin
    intro h20, 
    split,
    {
      exact Tmembers M x κ, 
    },
    {
      rw T_members,
      intro h,
      cases h with z h2,
      cases h2 with h3 h4,
      rw←  uscsimilar at h4,
      rw similar_symmetric at h4, 
      have h5:=finitecardinals0 M κ z x h20  h3 h4, 
      exact h5, 
    }
  end 

lemma T: ∀ (κ x:M), κ ∈ 𝔽 → x ∈ κ → 𝕋 M κ = Nc M (USC x) :=
  assume κ x,
  begin
    intros h h1,
    have h2:x ∈ FINITE M:= finitecardinals1 M κ x h h1,
    have h3: USC x ∈ FINITE M:= (uscfinite M x).mpr h2, 
    have h4: Nc M (USC x) ∈ 𝔽 := finitecardinals3 M (USC x) h3,
    have h5: USC x ∈ 𝕋 M κ:= Tmembers M x κ h1,
    have h6:similar M (USC x) (USC x):=  similar_reflexive M (USC x),
    have h7: USC x ∈ Nc M (USC x) := 
      begin
        rw Nc_members,
        exact h6,
      end,
    have h8: ∃ (z:M), z ∈  (𝕋 M κ ∩ Nc M (USC x)) :=
      begin
        use (USC x),
        rw intersection_axiom,
        exact ⟨ h5, h7⟩,
      end,
    have h9: 𝕋 M κ = Nc M (USC x):=
      -- can't use Lemma 28 because don't know 𝕋 M κ ∈ 𝔽 yet
      begin
        rw full_extensionality,
        intro u,
        split,
        {
          intro h20,
          rw T_members at h20,
          cases h20 with p h21,
          rw Nc_members,
          cases h21 with h22 h23,
          have h10: similar M p x := finitecardinals2 M p x κ h h22 h1,
          rw uscsimilar M at h10,
          exact similar_transitive M u (USC p)(USC x) h23 h10,
        },
        { 
          intro h30,
          rw T_members,
          rw Nc_members at h30,
          use x,
          exact ⟨ h1, h30⟩, 
        }
      end,
    rw h9,
  end

lemma Ncdef: ∀(x κ:M ), κ ∈ 𝔽 → x ∈ κ → κ = Nc M x:=
  assume x κ,
  begin
    intros h h1,
    rw full_extensionality,
    intro u,
    split,
    {
      intro h2,
      rw Nc_members,
      exact finitecardinals2 M u x κ h h2 h1, 
    },
    {
      intro h4,
      rw Nc_members at h4,
      rw similar_symmetric M at h4,
      exact finitecardinals0 M κ x u h h1 h4,
    }
  end 

lemma SpeckerT: ∀(x:M), Nc M x ∈ 𝔽 → 𝕋 M (Nc M x) = Nc M (USC x):=
  assume x,
  begin
    intro h,
    rw full_extensionality, 
    intro u,
    have h2: x ∈ Nc M x:=
      begin
        rw Nc_members M,
        exact similar_reflexive M x,
      end,
    have h3:= T M (Nc M x) x h h2, 
    rw h3,
  end

lemma Tfinite: ∀ (m:M), m ∈ 𝔽 → 𝕋 M m ∈ 𝔽 :=
  assume m,
  begin
    intro h,
    have h2:= cardinalsinhabited M m h,
    cases h2 with a h3,
    have h4: USC a ∈ 𝕋 M m:= Tmembers M a m h3,
    have h5:= finitecardinals1 M m a h h3,
    rw←  (uscfinite M a) at h5,
    have h6:= finitecardinals3 M (USC a) h5,
    have h7:= T M m a h h3,
    rw h7,
    exact h6, 
  end

lemma Ncdefsingleton: ∀(x:M), Nc M (single x) = one:=
  assume x,
  begin
    rw full_extensionality M, 
    intro t,
    rw Nc_members,
    rw one_members,
    split,
    {
      intro h,
      unfold similar at h,
      cases h with f h2,
      unfold similarity at h2,
      cases h2 with h3 h4,
      unfold onto at h4,
      specialize h4 x,
      have h5: x ∈ single x := (singleton1 M x x).mpr (refl x), 
      have h6:= h4 h5,
      cases h6 with u h7,
      use u,
      cases h7 with h8 h9,
      rw full_extensionality,
      intro z,
      split,
      {
        intro h10,
        rw singleton1 M,
        unfold oneone at h3,
        cases h3 with h11 h12,
        rcases h12 with ⟨ h13, h14⟩, 
        unfold maps at h11,
        cases h11 with h15 h16,
        rcases h16 with ⟨ h17,h18, h19⟩, 
        have h20:= h19 z h10,
        cases h20 with y h21,
        rw singleton1 M at h21,
        cases h21 with h22 h23,
        rw h22 at *,
        have h24:= h13 z u x ⟨ h23, h9, h10⟩,
        exact h24, 
      },
      {
        rw singleton1 M,
        intro h25,
        rw h25 at *,
        exact h8, 
      } 
    },
    {
      intro h,
      cases h with a h2,
      rw h2,
      unfold similar,
      use single ‹ a,x ›,
      unfold similarity,
      split,
      {
        unfold oneone,
        split,
        {
          unfold maps,
          repeat{ split},
          {
            unfold Rel_definition, 
            intro z,
            rw singleton1 M,
            intro h3,
            use a, use x,
            exact h3,
          },
          {
            intros z y,
            rw singleton1 M,
            rw singleton1 M,
            rw singleton1 M,
            rw ordered_pair_equality,
            intro h50,
            exact h50.right.right,
          },
          { 
            intros u y z,
            repeat {rw singleton1 M},
            repeat {rw ordered_pair_equality},
            intro h50,
            rcases h50 with ⟨ h51, h52, h53⟩,
            rw h52.right,
            rw h53.right,

          },
          {
            intro u, 
            intro h3,
            use x, 
            repeat {rw singleton1 M}, 
            repeat {rw ordered_pair_equality},
            rw singleton1 M at h3,
            rw h3 at *, 
            simp,
          }
        },
        {
          split,
          {
            intros z u y,
            repeat {rw singleton1 M},
            repeat {rw ordered_pair_equality},
            intro h50,
            rcases h50 with ⟨ h51, h52, h53⟩,
            rw h51.left,
            rw h52.left,
          },
          {
            intros z u,
            repeat {rw singleton1 M},  
            repeat {rw ordered_pair_equality},
            intro h50,
            exact h50.left.left,  
          }
        }
      },
      {
        unfold onto,
        intros y h3,
        use a,
        repeat {rw singleton1 M},  
        repeat {rw ordered_pair_equality},
        rw singleton1 M at h3,
        simp,
        exact h3, 
      }
    } 
  end


lemma Tzero: 𝕋 M (zero:M) = zero:=
  begin
    have h1: USC Λ = Λ := (usc_is_empty M Λ).mpr (refl Λ ),
    have h2:   Nc M Λ  = zero := Nc_Lambda M,
    have h3: zero ∈ 𝔽 := zeroF M, 
    rw←  h2 at h3, 
    have h4:= SpeckerT M Λ h3,
    rw h1 at h4,
    rw h2 at h4,
    exact h4,
  end

lemma Tone:  𝕋 M  (one:M) = one:=
  begin
    have h1: single Λ ∈ one:=
      begin
        rw one_members M, 
        use Λ,
      end,
    have h2:= T M one (single Λ ) (oneF M) h1,
    have h3: USC( single Λ ) = single (single Λ ):=
      begin
        rw full_extensionality M,
        intro t,
        rw usc M,
        split,
        {
          intro h4,
          cases h4 with u h5,
          rw singleton1 M at h5,
          cases h5 with h6 h7,
          rw h6 at *,
          rw h7,
          rw singleton1 M,
        },
        {
          intro h4,
          use Λ, 
          rw singleton1 M,
          rw singleton1 M at h4, 
          rw h4, 
          exact ⟨ refl Λ, refl (single Λ )⟩, 
        }
      end,
    rw h3 at h2,
    have h4: Nc M (single (single Λ )) = one:=
       Ncdefsingleton M (single Λ ),
    rw h4 at h2,
    exact h2,
  end

lemma Tsuccessor: ∀(x:M), x ∈ 𝔽 → (∃ u, u ∈ 𝕊 x) → 𝕋 M (𝕊 x) = 𝕊 (𝕋 M x):=
  begin
    assume m,
    intros h h2,
    have h2copy:= h2,
    cases h2copy with u h6,
    have h7copy := h6, 
    rw successor_members at h6,
    cases h6 with x h7,
    cases h7 with a h8,
    rcases h8 with ⟨ h9, h10, h11⟩,
    rw h11 at h7copy,
    have h12: 𝕊 m ∈ 𝔽 := successorF M m h h2, 
    have h13:𝕋 M (𝕊 m) = Nc M (USC(x ∪ single a)):=
      T M (𝕊 m) (x ∪ (single a)) h12 h7copy,
    have h14: 𝕋 M (𝕊 m) =  Nc M ((USC x) ∪  (single (single a))):=
      begin
        rw usc_successor M x a h10 at h13, 
        exact h13, 
      end,
    have h16: 𝕋 M (𝕊 m) = 𝕊 (Nc M (USC x)):=
      begin
      have h17: ¬ (single a ∈ USC x):=
        begin
          intro h18,
          rw← usc_up_down at h18,
          contradiction, 
        end, 
      rw Ncsuccessor M (USC x) (single a) h17 at h14, 
      exact h14, 
      end,
    rw T M m x h h9,
    exact h16, 
  end

lemma Ttwo: 𝕋 M (two:M) = two:=
  begin
    have h:=cardinalsinhabited M two (twoF M),
    rw two_definition at h,
    have h2:= Tsuccessor M one (oneF M) h, 
    rw Tone M at h2, 
    rw← two_definition at h2, 
    exact h2,   
  end

lemma lemma73c: 𝕋 M two = two:=
  begin
    rw two_definition,
    have h1: two ∈ 𝔽 := twoF M, 
    have h2:= cardinalsinhabited M two h1,
    rw two_definition at h2, 
    have h:= Tsuccessor M one (oneF M) h2,
    rw Tone M at h,
    exact h,
  end

lemma Tsum: ∀ (m:M), m ∈ 𝔽 → ∀(n:M), n ∈ 𝔽 → n+m ∈ 𝔽 → 𝕋 M (n+m) = 𝕋 M n + 𝕋 M m:=
  begin
    have base: zero ∈ Z74 M:=
      begin 
        rw Z74_members,
        split,
        {
          exact zeroF M,
        },
        {
          intros n h,
          rw right_identityNF M,
          rw Tzero M,
          rw right_identityNF M,
          intro h50,
          exact refl (𝕋 M n),
        }
      end,
    have step: ∀m, m  ∈  Z74 M → (exists u, u ∈ 𝕊 m ) →  𝕊 m ∈  Z74 M:=
      begin
        intro m,
        rw Z74_members M,
        intros h2 h3,
        cases h2 with h4 h5,
        rw Z74_members M,
        split,
        {
          exact successorF M m h4 h3,
        },
        {
          intro n,
          intros h6 h7,
          rw addition_equation M, 
          have h10:= cardinalsinhabited M (n + 𝕊 m) h7,
          cases h10 with x h11,
          have h12: ∃ u, u∈ n + m:=
            begin
              rw  addition_equation M n m  at h11, 
              rw successor_members M at h11,
              cases h11 with z h13,
              cases h13 with a h14,
              rcases h14 with ⟨ h15, h16, h17⟩,
              exact ⟨ z, h15⟩, 
            end,
          have h13: n+m ∈ 𝔽 :=  inhabited_sum M  m h4 n h6 h12,
          rw  addition_equation M n m  at h11, 
          rw Tsuccessor M (n+m) h13 ⟨ x, h11⟩, 
          rw Tsuccessor M m h4 h3, 
          rw addition_equation M,
          have h8:= h5 n h6 h13,
          rw h8, 
        }
      end,
    intros m h, 
    rw F_members at h, 
    specialize h ( Z74 M),
    have h3:= h (and.intro base  step), 
    rw ( Z74_members M) at h3, 
    cases h3 with h5 h6, 
    exact h6,  
  end 

lemma lemma75helperA: ∀ (m p:M), m ∈ 𝔽 → m = p + p + p → p ∈ 𝔽 →  p+p ∈ 𝔽 :=
  assume m p,
  begin
    intros h h2 h30,
    have h3: ∃ u, u ∈ m:=
      cardinalsinhabited M m h,
    rw h2 at h3,
    cases h3 with u h4,
    rw addition_members M at h4,
    cases h4 with a h5,
    cases h5 with b h6,
    rcases h6 with ⟨ h7, h8, h9, h10⟩,
    have h11:= inhabited_sum M p h30 p h30 ⟨ a, h8⟩ ,
    exact h11, 
  end 

lemma lemma75helperB: ∀ (m p:M), m ∈ 𝔽 → m = p + p + p + one → p ∈ 𝔽 →  p+p ∈ 𝔽  :=
  assume m p,
  begin
    intros h h2 h30,
    have h3: ∃ u, u ∈ m:=
      cardinalsinhabited M m h,
    rw h2 at h3,
    cases h3 with u h4,
    rw addition_members M at h4,
    cases h4 with a h5,
    cases h5 with b h6,
    rcases h6 with ⟨ h7, h8, h9, h10⟩, 
    rw addition_members M at h8,
    cases h8 with c h12,
    cases h12 with d h13, 
    rcases h13 with ⟨ h14,h15, h16, h17⟩, 
    have h11:= inhabited_sum M p h30 p h30 ⟨ c, h15⟩ ,
    exact h11, 
  end 

lemma lemma75helperC: ∀ (m p:M), m ∈ 𝔽 → m = p + p + p + two → p ∈ 𝔽 →  p+p ∈ 𝔽  :=
  assume m p,
  begin
    intros h h2 h30,
    have h3: ∃ u, u ∈ m:=
      cardinalsinhabited M m h,
    rw h2 at h3,
    cases h3 with u h4,
    rw addition_members M at h4,
    cases h4 with a h5,
    cases h5 with b h6,
    rcases h6 with ⟨ h7, h8, h9, h10⟩, 
    rw addition_members M at h8,
    cases h8 with c h12,
    cases h12 with d h13, 
    rcases h13 with ⟨ h14,h15, h16, h17⟩, 
    have h11:= inhabited_sum M p h30 p h30 ⟨ c, h15⟩ ,
    exact h11, 
  end 

lemma oneplusone: (one:M) + (one:M) = (two:M):=
  begin
    rw two_definition,
    rw successorisplusone, 
  end


lemma fivepointfour:∀(m:M), m ∈ 𝔽 →  ¬ ( m = 𝕋 M m + one) ∧ ¬ (m = 𝕋 M m + two):=
  assume m,
  begin
    intro h,
    have h2:= ppluspplusp M m h, 
    have h20: 𝕋 M m ∈ 𝔽 := Tfinite M m h, 
    cases h2 with h3 h4, 
    {  -- Case 1, m = p + p + p 
      cases h3 with p h5,
      cases h5 with h6 h7,
      have h21: 𝕋 M p ∈ 𝔽 := Tfinite M p h6,
      have h8:= ppluspplusp2 M m h,
      specialize h8 p (𝕋 M p),
      have h9:= h8 h6 h21,
      rcases h9 with ⟨ h10, h11, h12⟩,
      have h13:= h10 h7,
      have h14:= h11 h7,
      have h15: 𝕋 M m = 𝕋 M (p +p+p):= 
        begin  
          rw h7,
        end, 
      have h16:= lemma75helperA M m p h h7 h6,
      have hcopy:= h,
      rw h7 at hcopy,
      have h17:= Tsum M p h6 (p+p) h16 hcopy, 
      rw Tsum M p h6 p h6 h16 at h17,
          -- 𝕋 M (p + p + p) = 𝕋 M p + 𝕋 M p + 𝕋 M p, line 1001
      split,
      {
        intro h18,
        have h19:= h10 h7,
        rw h18 at h19, 
        rw←  h7 at h17,
        rw h17 at h19,
        simp at h19, 
        exact h19, 
      },
      {
        intro h18,
        have h19:= h11 h7,
        rw h18 at h19, 
        rw←  h7 at h17,
        rw h17 at h19,
        simp at h19, 
        exact h19, 
      }
    },
    { 
      cases h4 with h5 h6,
      {  -- Case 2,  m = p + p + p + one
        cases h5 with p h6,
        cases h6 with h7 h8, 
        have h21: 𝕋 M p ∈ 𝔽 := Tfinite M p h7,
        have h9:= ppluspplusp2 M m h,
        specialize h9 p (𝕋 M p),
        have h19:= h9 h7 h21,
        rcases h19 with ⟨ h10, h11, h12⟩, 
        have h13:= h12 h8,
        have h15: 𝕋 M m = 𝕋 M (p +p+p +one):= 
          begin  
            rw h8,
          end, 
        have h16:= lemma75helperB M m p h h8 h7, 
        have hcopy:= h,
        rw h8 at hcopy, 
        have h30:= subterms M (p+p) p one h16 h7 (oneF M) hcopy,
        cases h30 with h31 h32,
        have h33:= Tsum M  one (oneF M) (p+p+p) h31 hcopy,
        have h34:= Tsum M  p h7 (p+p) h16 h31,
        have h35:= Tsum M p h7 p h7 h16, 
        rw h33 at h15,
        rw h34 at h15,
        rw h35 at h15,
        rw Tone at h15,   --formula (57), line 1228
        split,
        { 
          intro h18,   -- Case 2a, m = 𝕋 M m + one 
          rw h8 at h18,
          rw← h8 at h18,
          rw h15 at h18, 
          rw associativityNF at h18,
          rw oneplusone at h18,
          rw h8 at h15,
          have h16:= h12 h8,
          have h20copy:= h20,
          rw h8 at h20copy,
          have h40:= ppluspplusp2 M m h p (𝕋 M p) h7 h21,
          rcases h40 with ⟨ h41, h42,h43⟩,
          have h44:= h43 h8,
          apply h44,
          contradiction,
        },
        { 
          intro h18, -- Case 2b, m = 𝕋 M m + two 
          rw h8 at h18,
          rw← h8 at h18,
          rw h15 at h18, 
          rw associativityNF at h18, 
          rw← oneplusone at h18, 
          have h45:  ∀ (x:M), one + x = x + one:=
            assume x,
            begin
              rw commutativityNF,
            end,
          have h50: m = 𝕊 (𝕋 M p)  +  𝕊 (𝕋 M p) +  𝕊 (𝕋 M p):=
            begin 
              rw successorisplusone, 
              repeat { rw associativityNF}, 
              rw h45  (𝕋 M p + (one + (𝕋 M p + one))), 
              rw h45   (𝕋 M p + one) ,
               repeat { rw associativityNF},
                repeat { rw associativityNF at h18}, 
               exact h18, 
            end,
          have h36:= h32,
          rw← successorisplusone at h36,
          
          have h35:= Tsuccessor M p h7 (cardinalsinhabited M (𝕊 p) h36), 
          have h37:= Tfinite M (𝕊 p) h36, 
          rw h35 at h37, 
          have h40:= ppluspplusp2 M m h (𝕊  (𝕋 M p)) p h37 h7,  
          rcases h40 with ⟨ h41, h42, h43⟩,
          have h44:= h41 h50,
          exact h44 h8,
        }
      },
      {  
        cases h6 with p h76,
        cases h76 with h7 h8,  -- h8 is m= p+p+p+two, case 3 line 1015
        have h21: 𝕋 M p ∈ 𝔽 := Tfinite M p h7, 
        have h121: 𝕋 M m ∈ 𝔽 := Tfinite M m h, 
        have h122: 𝕊 p ∈ 𝔽 :=    -- line 1016
          begin
            rw two_definition at h8,
            rw successor_shift at h8,
            rw← addition_equation M at h8,
            rw successor_shift at h8,
            rw← addition_equation M at h8,
            rw associativityNF M at h8, 
            rw associativityNF M at h8,
            rw← successor_shift M at h8,
            rw addition_equation M at h8,
            rw h8 at h, 
            exact subterms2 M p (p + (p + one)) h7 h, 
          end,
        have h36:= h122,
        have h35:= Tsuccessor M p h7 (cardinalsinhabited M (𝕊 p) h36), 
        have h37:= Tfinite M (𝕊 p) h36, 
        rw h35 at h37, 
        have h40:= ppluspplusp2 M m h (𝕊  (𝕋 M p)) p h37 h7,  
        split,
        {  -- case 3a, m = p+p+p+two and  m = 𝕋 M m + one 
          intro case3a,   -- m = 𝕋 m + one 
          have h15: 𝕋 M m = 𝕋 M (p +p+p +two):= 
            begin 
              rw h8,
            end, 
          have h16:= lemma75helperC M m p h h8 h7, 
          have hcopy:= h,
          rw h8 at hcopy, 
          have h30:= subterms M (p+p) p two h16 h7 (twoF M) hcopy,
          cases h30 with h31 h32,
          have h33:= Tsum M  two (twoF M) (p+p+p) h31 hcopy,
          have h34:= Tsum M  p h7 (p+p) h16 h31,
          have h35:= Tsum M p h7 p h7 h16, 
          rw h33 at h15,
          rw h34 at h15,
          rw h35 at h15,
          rw Ttwo at h15,  
          have h41: m = (𝕊 (𝕋 M p)) + (𝕊 (𝕋 M p)) +(𝕊 (𝕋 M p)):=
            begin 
              rw← Tsuccessor M p h7 (cardinalsinhabited M (𝕊 p) h36), 
              rw h15 at case3a,
              rw two_definition at case3a,
              rw successor_shift at case3a,
              rw←  addition_equation at case3a, 
              rw one_definition at case3a,
              repeat {rw successor_shift at case3a}, 
              rw right_identityNF at case3a,
              rw right_identityNF at case3a,
              rw← addition_equation at case3a, 
              rw←  Tsuccessor  M p h7 (cardinalsinhabited M (𝕊 p) h36) at case3a,
              rw← addition_equation at case3a, 
              rw← addition_equation at case3a, 
              rw←  Tsuccessor  M p h7 (cardinalsinhabited M (𝕊 p) h36) at case3a,
              rw successor_shift at case3a,
              rw← addition_equation at case3a, 
              rw successor_shift at case3a,
              rw←  Tsuccessor  M p h7 (cardinalsinhabited M (𝕊 p) h36) at case3a,
              exact case3a, 
            end, 
          rcases h40 with ⟨ h50, h51, h52⟩,
          exact h51 h41 h8, 
        },
        {  -- case 3b,  m = p+p+p+two and m = 𝕋 m + two
          intro case3b,  -- m - 𝕋 M m + two 
          have h15: 𝕋 M m = 𝕋 M (p +p+p +two):= 
            begin 
              rw h8,
            end, 
          have h16:= lemma75helperC M m p h h8 h7, 
          have hcopy:= h,
          rw h8 at hcopy, 
          have h30:= subterms M (p+p) p two h16 h7 (twoF M) hcopy,
          cases h30 with h31 h32,
          have h33:= Tsum M  two (twoF M) (p+p+p) h31 hcopy,
          have h34:= Tsum M  p h7 (p+p) h16 h31,
          have h35:= Tsum M p h7 p h7 h16, 
          rw h33 at h15,
          rw h34 at h15,
          rw h35 at h15,
          rw Ttwo at h15, 
            have h41: m = (𝕊 (𝕋 M p)) + (𝕊 (𝕋 M p)) +(𝕊 (𝕋 M p)) + one :=
            begin 
              rw← Tsuccessor M p h7 (cardinalsinhabited M (𝕊 p) h36), 
              rw h15 at case3b,
              rw two_definition at case3b,
              rw successor_shift at case3b,
              rw←  addition_equation at case3b, 
              rw one_definition at case3b,
              repeat {rw successor_shift at case3b}, 
              rw right_identityNF at case3b,
              rw right_identityNF at case3b,
              rw← addition_equation at case3b, 
              rw←  Tsuccessor  M p h7 (cardinalsinhabited M (𝕊 p) h36) at case3b,
              rw← addition_equation at case3b, 
              rw successor_shift at case3b, 
              rw← addition_equation at case3b,  
              rw← addition_equation at case3b, 
              rw← addition_equation at case3b, 
              rw←  Tsuccessor  M p h7 (cardinalsinhabited M (𝕊 p) h36) at case3b, 
              rw successor_shift at case3b, 
              rw← addition_equation at case3b, 
              rw successor_shift at case3b,
              rw successor_shift at case3b, 
              rw←  Tsuccessor  M p h7 (cardinalsinhabited M (𝕊 p) h36) at case3b, 
              rw  successorisplusone at case3b, 
              rw commutativityNF at case3b, 
              repeat {rw←  associativityNF at case3b},
              exact case3b, 
            end, 
          exact h40.right.right h41 h8, 
        }
      } 
    }, 
  end

lemma expT_inhabited: ∀ (m:M), m ∈ 𝔽 → ∃ u, u ∈ exp M (𝕋 M m) :=
  assume m,
  begin
    intro h,
    have h2:= cardinalsinhabited M m h,
    cases h2 with x h3,
    have h4:= Tmembers M x m h3,
    use (SSC x), 
    rw exp_members M,
    use x,
    exact ⟨ h4, similar_reflexive M (SSC x)⟩,
  end

lemma expT: ∀ (m:M), m ∈ 𝔽 → (∃ u, u ∈ exp M m)→ exp M (𝕋 M m) = 𝕋 M (exp M m):=
  assume m,
  begin
    intros h h2,
    cases h2 with u h3,
    rw exp_members M at h3,
    cases h3 with a h4, 
    cases h4 with h5 h6, 
    have h7: exp M m = Nc M (SSC a) := expdef M m a h h5, 
    have h9: SSC a ∈ exp M m:= exp_members2 M m a h h5,
    have h10: USC (SSC a) ∈ 𝕋 M (exp M m) := Tmembers M (SSC a) (exp M m) h9,
    have h11: USC (USC a) ∈ 𝕋 M m := Tmembers M (USC a) m h5, 
    have h12: 𝕋 M m ∈ 𝔽 := Tfinite M m h, 
    have h13: SSC (USC a) ∈ exp M (𝕋 M m) := exp_members2 M (𝕋 M m) (USC a) h12 h11, 
    have h14: Nc M (SSC (USC a)) = Nc M (USC (SSC a)) := sscusc M a, 
    have h15: exp M m ∈ 𝔽 := finiteexp M m h ⟨ SSC a, h9⟩, 
    have h16: exp M (𝕋 M m) ∈ 𝔽 := finiteexp M (𝕋 M m) h12 ⟨ SSC (USC a), h13 ⟩, 
    have h17:= Ncdef M (SSC (USC a)) (exp M (𝕋 M m))  h16 h13, 
    have h18:= T M (exp M m) (SSC a) h15 h9,
    rw [h17, h18, h14],
  end
  
lemma expnotzero: ∀ (z:M), ¬ (exp M z = zero):=
  assume z,
  begin
    intro h, 
    have h2:Λ ∈ zero:= 
      begin
        rw zero_definition,
        rw singleton1 M,
      end,
    rw←  h at h2,
    rw exp_members M at h2, 
    cases h2 with a h3,
    cases h3 with h4 h5,
    rw similar_symmetric at h5, 
    unfold similar at h5,
    cases h5 with f h6,
    unfold similarity at h6,
    cases h6 with h7 h8,
    unfold oneone at h7,
    cases h7 with h9 h10,
    have h11:= maps_to_empty M f (SSC a) h9,
    have h12: a ∈ SSC a:=
      begin
        rw ssc_members,
        split,
        {
          exact subset_reflexive M a,
        },
        {
          intros y h,
          left,
          exact h, 
        }
      end,
    have h13: ¬ a ∈ Λ:= emptyset_axiom a,
    rw h11 at h12,
    contradiction,
  end

lemma usc_singleton: ∀(x:M), USC (single x) = single (single x):=
  assume x,
  begin
    rw full_extensionality M,
    intro t,
    rw singleton1 M,
    have h3:= (usc_unitclass M (single x)).mp ⟨ x ,refl (single x)⟩ ,
    cases h3 with u h4,
    rw h4,
    rw singleton1 M,
    rw full_extensionality at h4,
    specialize h4 (single x),
    rw usc_members M at h4,
    rw singleton1 M at h4,
    simp at h4,
    rw singleton1 M at h4, 
    rw h4,
  end

lemma similar_singletons: ∀ (a b:M), similar M (single a) (single b):=
  assume a b,
  begin
    unfold similar,
    use  single (‹ a, b›) ,
    unfold similarity,
    split,
    {
      unfold oneone,
      split,
      {
        unfold maps,
        repeat {split}, 
        {
          rw Rel_definition,
          intro z,
          intro h,
          rw singleton1 M at h,
          use a, use b,
          exact h,
        },
        {
          intros x y,
          intro h,
          rw singleton1 at h,
          cases h with h2 h3,
          rw h2 at *,
          rw singleton1 M,
          rw singleton1 at h3,
          rw ordered_pair_equality M at h3,
          exact h3.right, 
        },
        {
          intros x y z,
          intro h,
          repeat {rw singleton1 at h} , 
          rcases h with ⟨ h2, h3, h4⟩,
          rw ordered_pair_equality at h3,
          rw ordered_pair_equality at h4,
          rw [h3.right, h4.right], 
        },
        {
          intros x h,
          rw singleton1 M at h,
          rw h at *,
          use b,
          rw singleton1 M,
          rw singleton1 M,
          simp,
        }
      },
      {
         split,
         {
           intros x u y,
           intro h,
           repeat {rw singleton1 M at h},
           repeat {rw ordered_pair_equality M at h},
           rcases h with ⟨ h40, h41, h42⟩,
           rw [h40.left, h41.left],
         },
         {
           intros x y h,
           repeat {rw singleton1 M at h},
           rw ordered_pair_equality M at h,
           rw singleton1 M,
           exact h.left.left, 
         }
      }
    },
    {
      rw onto,
      intros y h,
      use a,
      rw singleton1 M at h,
      rw h at *,
      rw singleton1,
      rw singleton1,
      simp,
    }
  end


lemma uscsubsets: ∀ (a p:M), p ⊆ USC a → ∃ (b:M), b ⊆ a ∧ p = USC b:=
  assume a p,
  begin
    intro h,
    use union p,
    split,
    { 
      rw subset_definition, 
      intros u h2,
      rw union_axiom at h2,
      cases h2 with v h3,
      rw subset_definition at h,
      specialize h v,
      cases h3 with h4 h5,
      have h6:= h h4,
      rw usc at h6, 
      cases h6 with w h7,
      cases h7 with h8 h9,
      rw h9 at *,
      rw singleton1 M at *,
      rw h5 at *,
      exact h8,
    },
    {
      rw subset_definition at h,
      rw full_extensionality,
      intro t,
      have hcopy := h,
      specialize h t,
      rw usc,
      split,
      {
        intro h2,
        have h3:= h h2,
        rw usc at h3,
        cases h3 with q h4,
        cases h4 with h5 h6,
        use q,
        rw union_axiom,
        split,
        {
          use t,
          rw h6 at *,
          rw singleton1 M,
          simp,
          exact h2, 
        },
        {
          exact h6, 
        }
      },
      { 
        intro h2,
        rw usc at h,
        cases h2 with u h3,
        cases h3 with h4 h5,
        rw union_axiom at h4,
        cases h4 with v h6,
        cases h6 with h7 h8,
        rw h5 at *,
        have h9:v= single u:=
          begin
            have h10:= hcopy v h7,
            rw usc at h10,
            cases h10 with U h11,
            cases h11 with h12 h13,
            rw h13 at h8,
            rw singleton1 M at h8,
            rw← h8 at *,
            exact h13,
          end,
        rw← h9,
        exact h7,
      }
    }
  end

lemma similar_to_finite: ∀(a b:M), a ∈ FINITE M → similar M a b → b ∈ FINITE M:=
  assume a b,
  begin
    intros h h2,
    set κ := Nc M a with h3,
    have h4: κ ∈ 𝔽:=  finitecardinals3 M a h,
    have h5: similar M a a:= similar_reflexive M a, 
    rw←  Nc_members M a a at h5,
    rw← h3 at h5,
    have h7: b ∈ κ:= finitecardinals0 M κ a b h4 h5 h2,
    exact finitecardinals1 M κ b h4 h7, 
  end

lemma singletons_similar: ∀ (a b:M), similar M (single a) (single b):=
  assume a b,
  begin
    set f:= single ‹ a, b› with h,
    have h2:similarity M f (single a) (single b):=
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
              intro t,
              intro h3,
              rw full_extensionality at h,
              specialize h t,
              rw h at h3,
              rw singleton1 at h3,
              use a, use b,
              exact h3, 
            },
            {
              intros x y h2,
              cases h2 with h3 h4,
              rw singleton1 at h3,
              rw h3 at *,
              rw singleton1,
              rw h at *,
              rw singleton1 at h4,
              rw ordered_pair_equality at h4,
              simp at h4,
              exact h4,
            },
            {
              intros x y z h2,
              rcases h2 with ⟨ h3, h4, h5⟩,
              rw h at *,
              rw singleton1 at *,
              rw ordered_pair_equality at *,
              cases h4 with h6 h7,
              cases h5 with h8 h9,
              rw h7 at *,
              rw h9 at *,
            },
            {
              intros x h3,
              rw singleton1 at h3,
              rw h3 at *,
              use b,
              rw singleton1,
              simp,
              rw h,
              rw singleton1,
            }
          },
          {
            split,
            {
              intros x u y h2,
              rcases h2 with ⟨ h3, h4, h5⟩,
              rw singleton1 at h5,
              rw h5 at *,
              rw h at *,
              rw singleton1 at *,
              rw ordered_pair_equality at *,
              cases h4 with h6 h7,
              cases h5 with h8 h9,
              rw h6,
            },
            {
              intros x y h2,
              rw h at *,
              rw singleton1 at *,
              cases h2 with h3 h4,
              rw singleton1 at h4,
              rw ordered_pair_equality at h3,
              exact h3.left, 
            }
          }
        },
        {
          rw onto,
          intros y h3,
          rw singleton1 at h3,
          rw h3 at *,
          use a,
          rw singleton1,
          simp,
          rw h,
          rw singleton1, 
        }
      end,
    unfold similar,
    use f,
    exact h2, 
  end

lemma Nc_unitclass: ∀ (y:M), Nc M (single y) = one:=
  assume y,
  begin
    rw full_extensionality,
    intro t,
    rw Nc_members,
    split,
    {
      intro h,
      have h3:= similar_to_singleton M t y h,
      cases h3 with a h4,
      rw h4 at *,
      rw one_members,
      use a,
    },
    {
      intro h,
      rw one_definition at h,
      rw zero_definition at h,
      rw successor_members at h,
      cases h with x h2,
      cases h2 with a h3,
      rcases h3 with ⟨ h4,h5,h6⟩, 
      rw singleton1 M at h4,
      rw h4 at *,
      rw empty_union_x M (single a) at h6,
      rw h6 at *,
      exact singletons_similar M a y,
    }
  end

lemma usc_subset3: ∀ (a b:M), a ∈ FINITE M → b ∈ FINITE M → a ∈ SSC (b) → USC a ∈ SSC (SSC b):=
  assume a b,
  begin
    intros ha hb h2,
    rw ssc_members,
    repeat{split},
    {
      rw ssc_members at h2,
      cases h2 with h3 h4,
      rw subset_definition,
      intro t,
      intro h5,
      rw usc at h5,
      cases h5 with p h6,
      cases h6 with h7 h8,
      rw h8 at *,
      rw ssc_members,
      split,
      {
        specialize h4 p,
        have h5:= member_subset M a b p h3 h7,
        have h6:= h4 h5,
        rw subset_definition,
        intro z,
        intro h9,
        rw singleton1 M at h9,
        rw h9 at *,
        exact h5, 
      },
      { 
        intro q,
        intro h10,
        specialize h4 q,
        have h11:= h4 h10,
        rw singleton1 M,
        have h12:= member_subset M a b p h3 h7,
        have h13:b ∈ DECIDABLE M := finitedecidable M b hb,
        rw decidable_members at h13,
        have h14:= h13 q p ⟨ h10 , h12⟩ , 
        exact h14, 
      }
    },
    {
      intro y,
      intro h3,
      rw ssc_members at h3,
      cases h3 with h4 h5,
      rw usc,
      rw ssc_members at h2,
      have h6 := separablefinite M b hb y h4,
      have h7: y ∈ FINITE M:=
        begin
          apply h6,
          unfold separable_subset,
          split,
          { 
            exact h4,
          },
          {
            rw full_extensionality,
            intro t,
            cases h2 with h7 h8,
            specialize h8 t,
            rw binary_union_axiom,
            rw minus_members,
            split,
            { 
              intro h50,
              have h51:= h8 h50,
              have h52:= h5 t h50,
              cases h52 with h53 h54,
              {
                left,
                exact h53,
              },
              {
                right,
                exact ⟨ h50, h54⟩, 
              }
            },
            {
              intro h9,
              cases h9 with h10 h11,
              {
                exact member_subset M y b t h4 h10,
              },
              {
                exact h11.left,
              }
            }
          }
        end,
      have h8: Nc M y ∈ 𝔽 :=  finitecardinals3 M y h7,
      have h9:= FregeNdecidable M,
      rw decidable_members M 𝔽  at h9, 
      specialize h9 (Nc M y) one, 
      have h10:= h9 ⟨ h8, (oneF M)⟩, 
      cases h10 with h11 h12,
      {
        rw full_extensionality at h11,
        rw one_definition at h11,
        specialize h11 (single Λ ),
        have h12: single (Λ:M) ∈ 𝕊 zero:=
          begin
            rw successor_members,
            use Λ , use Λ,
            split,
            {
              rw zero_definition, 
              rw singleton1 M,
            },
            {
              split,
              {
                exact emptyset_axiom Λ ,
              },
              {
                rw empty_union_x M (single Λ ), 
              }
            }
          end,
        rw← h11 at h12,
        rw Nc_members at h12,
        rw similar_symmetric M at h12,
        have h13:= similar_to_singleton M y Λ h12,
        cases h13 with p h14,
        have h14copy:= h14,
        rw subset_definition at h4,
        specialize h4 p,
        rw full_extensionality at h14,
        specialize h14 p,
        rw singleton1 M at h14,
        simp at h14,
        have h15:= h4 h14,
        cases h2 with h16 h17,
        specialize h17 p,
        have h18:= h17 h15,
        cases h18 with h19 h20,
        {
          left,
          use p,
          exact ⟨ h19, h14copy⟩, 
        },
        {
          right,
          intro h21,
          cases h21 with q h22,
          cases h22 with h23 h24,
          rw h24 at *,
          rw singleton1 M at h14,
          rw h14 at *,
          contradiction,
        }
      },
      {
        right,
        intro h13,
        cases h13 with p h14,
        cases h14 with h15 h16, 
        rw h16 at *,
        have h13:= Nc_unitclass M p,
        contradiction,
      }
    }
  end


lemma fivepointfive: ∀ (m n:M), m ∈ 𝔽 → n ∈ 𝔽 → (m ≤ n ↔ 𝕋 M m ≤ 𝕋 M n):=
  assume m n,
  begin
    intros hm hn,
    split,
    {   --left to right
      intro h,
      rw le_definition at h, 
      cases h with a h2,
      cases h2 with b h3,
      rcases h3 with ⟨ h4, h5, h6, h7⟩,
      rw le_definition,
      use (USC a), use (USC b),
      repeat{split}, 
      {
        rw T_members,
        use a,
        exact ⟨ h4, similar_reflexive M (USC a)⟩,
      },
      {
        rw T_members,
        use b,
        exact ⟨ h5, similar_reflexive M (USC b)⟩, 
      },
      {
        rw usc_subset at h6,
        exact h6, 
      },
      {
        rw← usc_dif2,
        rw full_extensionality,
        intro t,
        rw full_extensionality at h7,
        rw usc,
        split,
        {
          intro h8,
          cases h8 with p h9,
          cases h9 with h10 h11,
          rw h11 at *,
          rw binary_union_axiom,
          rw usc,
          specialize h7 p,
          rw h7 at h10,
          rw binary_union_axiom at h10,
          cases h10 with h12 h13,
          {
            left,
            use p,
            simp,
            exact h12,
          },
          {
            right,
            rw usc,
            use p,
            simp,
            exact h13,
          }
        },
        {  -- right to left 
          intro h8,
          rw binary_union_axiom at h8,
          cases h8 with h9 h10,
          {
            rw usc at h9,
            cases h9 with q h11,
            cases h11 with h12 h13,
            rw h13 at *,
            use q,
            specialize h7 q,
            rw binary_union_axiom at h7,
            rw minus_members at h7,
            simp,
            exact member_subset M a b q h6 h12, 
          },
          {
            rw usc at h10,
            cases h10 with p h11,
            cases h11 with h12 h13,
            rw h13 at *,
            use p,
            simp,
            rw minus_members at h12,
            exact h12.left, 
          }
        }
      }
    },
    {
      intro h,
      have h2:=cardinalsinhabited M n hn,
      cases h2 with b h3,
      have h4:=Tmembers M b n h3,
      have h5: 𝕋 M m ∈ 𝔽 :=  Tfinite M m hm,
      have h6: 𝕋 M n ∈ 𝔽 := Tfinite M n hn,
      have h7:= (le2 M (𝕋 M m) (𝕋 M n) h5 h6 (cardinalsinhabited M (𝕋 M n) h6)).mp h (USC b) h4,
      cases h7 with u h8,
      rcases h8 with ⟨ h9, h10, h11⟩, 
      have h12: u ∈ SSC(USC b):=
        begin
          rw ssc_members,
          split,
          {
            exact h10,
          },
          {
            intro y,
            rw full_extensionality at h11,
            specialize h11 y,
            rw binary_union_axiom at h11,
            rw minus_members at h11,
            intro h50,
            rw h11 at h50,
            cases h50 with h51 h52,
            {
              exact or.inl h51,
            },
            {
              exact or.inr h52.right,
            }
          }
        end,
      have h13:= subset_usc M b u h12,
      cases h13 with a h14,
      cases h14 with h15 h16,
      rw h16 at *,
      have h17:= (ssc_subset1 M a b).mpr h12,
      rw T_members M at h9,
      cases h9 with x h17,
      cases h17 with h18 h19,
      rw← uscsimilar at h19,
      rw similar_symmetric at h19,
      have h20:=finitecardinals0 M m x a hm h18 h19,
      rw le_definition, 
      use a,
      use b,
      repeat{split},
      {
        exact h20,
      },
      {
        exact h3,
      },
      {
        rw ssc_members at h15,
        exact h15.left, 
      },
      {
        rw ssc_members at h15,
        cases h15 with h21 h22,
        rw full_extensionality,
        intro t,
        specialize h22 t,
        rw binary_union_axiom,
        rw minus_members,
        split,
        {
          intro h50,
          have h51:= h22 h50,
          cases h51 with h52 h53,
          {
            exact or.inl h52,
          },
          {
            exact or.inr ⟨ h50, h53⟩, 
          }
        },
        {
          intro h23,
          cases h23 with h24 h25,
          {
            exact member_subset M a b t h21 h24,
          },
          {
            exact h25.left,
          }
        }
      }
    }
  end
  
lemma successorincreasing: ∀ (m:M), m ∈ 𝔽 → ¬ (𝕊 m ≤ m):=
  assume m,
  begin
    intros h h2,
    have h12:= h2,
    rw le_definition at h12,
    cases h12 with a h3,
    cases h3 with b h4,
    rcases h4 with ⟨ h5, h6, h7, h8⟩,
    have h9:= lessthansuccessor M m h ⟨ a, h5⟩ ,
    have h10:= successorF M m h ⟨ a, h5⟩, 
    have h13:= finitetrichotomy2 M (𝕊 m) m h10 h h2,
    have h14: m ≤ 𝕊 m :=
      begin
        rw lessthan_definition at h9,
        exact h9.left,
      end,
    have h15:= h13 h14,
    rw h15 at *,
    have h16:= Theorem2 M m m h h,
    cases h16 with h17 h18,
    simp at h18,
    contradiction, 
  end

lemma expTinhabited: ∀ (m:M), m ∈ 𝔽 → ∃ (u:M), u ∈ exp M (𝕋 M m):=
  assume m,
  begin
    intro h,
    have h2:= cardinalsinhabited M m h,
    cases h2 with u h3,
    have h4:= Tmembers M u m h3,
    use SSC u,
    rw exp_members M,
    use u,
    exact ⟨ h4, similar_reflexive M (SSC u)⟩, 
  end

lemma xnotlessthanx: ∀ (x:M), x ∈ 𝔽 →  ¬ x < x:=
  assume x,
  begin
    intros h20  h,
    rw lessthan_definition at h,
    cases h with h2 h3,
    contradiction, 
  end

lemma nothinglessthanzero: ∀(x:M), x ∈ 𝔽 → ¬ x < zero:=
  assume x,
  begin
    intros h10 h,
    have hcopy := h,
    rw zero_definition at h,
    rw lessthan_definition at h,
    cases h with h2 h3,
    rw le_definition at h2,
    cases h2 with a h4,
    cases h4 with b h5, 
    rcases h5 with ⟨h6, h7, h8, h9⟩,  
    rw singleton1 at h7,
    rw h7 at *,
    rw subset_of_empty M a at h8,
    rw h8 at *,
    have h20:Λ ∈ zero:=
      begin
        rw zero_definition,
        rw singleton1 M,
      end, 
    have h11:Λ ∈ zero ∩ x:=
      begin
        rw intersection_axiom,
        exact ⟨ h20, h6⟩, 
      end,
    have h12:= cardinalsdisjoint M zero x  Λ (zeroF M) h10 h11,
    rw← h12 at *,
    have h13:= xnotlessthanx M zero (zeroF M),
    contradiction,
  end 


lemma Torder: ∀ (n:M), n ∈ 𝔽 → ∀ (m:M), m ∈ 𝔽 →  n < m → 𝕋 M n < 𝕋 M m:=
  begin
    have base: zero ∈ ZTorder M:=
      begin
        rw ZTorder_members,
        split,
        {
          exact zeroF M,
        },
				{
					intros m h h2,
					rw Tzero M, 
					have h3:= Tfinite M m h, 
					have h4:=Theorem2 M (𝕋 M m) zero  h3 (zeroF M), 
					cases h4 with h5 h6, 
					cases h5 with h7 h8,
					{
            have h8:= nothinglessthanzero M (𝕋 M m) h3, 
						contradiction,
					},
					{
						rw or_comm at h8,
						cases h8 with h9 h10,
						{
              exact h9, 
						},
					  {
              have h11:= cardinalsinhabited M m h,
							cases h11 with a h12,
							rw lessthan2 M zero (𝕋 M m) (zeroF M) h3, 
							use Λ, use Λ,
							repeat{split},
							{
								rw zero_definition, 
								rw singleton1, 
							},
							{
								rw full_extensionality at h10,
								specialize h10 Λ,
								rw zero_definition at h10,
								rw singleton1 at h10,
								simp at h10, 
								exact h10, 
							},
							{
								have h13:= Tmembers M a m h12, 
								rw h10 at h13,
								rw zero_definition at h13,
								rw singleton1 at h13,
								rw full_extensionality at h13,
								have h14:a = Λ :=
								  begin
										rw full_extensionality,
										intro t,
										specialize h13 (single t),
										rw usc at h13,
										have h15:= emptyset_axiom (single t),
										rw← h13 at h15,
										push_neg at h15, 
										have h16:= emptyset_axiom t,
										split,
										{
											intro h17,
											specialize h15 t, 
											have h18:= h15 h17, 
											contradiction, 
										},
										{
											intro h17,
											contradiction, 
										}
									end,
								rw h14 at *,
								have h15:(Λ:M) ∈ zero:= 
								  begin
										rw zero_definition,
										rw singleton1,
									end, 
								have h16: (Λ :M) ∈ zero ∩ m :=
								  begin 
										rw intersection_axiom,
										exact ⟨ h15, h12⟩, 
									end,
								have h17:= cardinalsdisjoint M zero m Λ (zeroF M) h h16,
                rw← h17 at *,
								have h18:= nothinglessthanzero M zero (zeroF M), 
                contradiction,
							},
							{
								rw full_extensionality at h10,
								specialize h10 Λ ,
								rw zero_definition at h10,
								rw singleton1 at h10,
								simp at h10,
								rw T_members at h10,
								cases h10 with x h11,
								cases h11 with h12 h13,
								rw  similar_symmetric at h13,
								rw similar_to_empty at h13, 
							  rw usc_is_empty at h13,
								rw h13 at *,
								have h15:(Λ:M) ∈ zero:= 
								  begin
										rw zero_definition,
										rw singleton1,
									end, 
								have h16: (Λ :M) ∈ zero ∩ m :=
								  begin 
										rw intersection_axiom,
										exact ⟨ h15, h12⟩, 
									end,
								have h17:= cardinalsdisjoint M zero m Λ (zeroF M) h h16,
                rw← h17 at *,
								have h18:= nothinglessthanzero M zero (zeroF M), 
                contradiction,
							}
						}
					}
				}
      end,
		have step: ∀ (n:M), n ∈ ZTorder M → (∃ u, u ∈ 𝕊 n) → (𝕊 n ∈ ZTorder M):=
		  assume n,
			begin
			  intros h h2,
        rw ZTorder_members M at h, 
				cases h with h3 h4,
				rw ZTorder_members M,
				split,
				{
					exact (successorF M n h3 h2), 
				},
				{
					intros m h5 h6,
          have h7: ¬ m = zero:=
					  begin
							intro h8,
							rw h8 at *,
							have h9:=nothinglessthanzero M (𝕊 n) (successorF M n h3 h2),
							contradiction,
						end,
					have h8:= nonzeroissuccessor M m h5 h7,
          cases h8 with r h9,
					cases h9 with h10 h11,
					rw h11 at h6,
					have h12:= cardinalsinhabited M m h5,
					cases h12 with b h13,
					rw h11 at h13, 
					have h5copy:= h5,
					rw h11 at h5copy, 
					have h16: 𝕊 n ≤ 𝕊 r:=
					  begin
							rw lessthan_definition at h6,
							exact h6.left, 
						end,
			    have h15:= ordersuccessor M n r h3 h10  (cardinalsinhabited M (𝕊 r) h5copy),
          rw← h15 at h16, 
					have h17: n < r:=
					  begin
							rw lessthan_definition,
							split,
							{
								exact h16,
							},
							{
								intro h18,
								rw h18 at *,
								have h19:= xnotlessthanx M (𝕊 r) h5copy, 
								contradiction, 
							}
						end,
					specialize h4  r,
          have h18:= h4 h10 h17,
					have h19:= Tfinite M n h3,
					have h20:= Tfinite M r h10, 
					have h21:= cardinalsinhabited M m h5,
					have h22: exists u, u ∈ 𝕊 r:=
					  begin
							 rw h11 at h21,
							 exact h21, 
						end,
					have h23:= Tsuccessor M r h10 h22, 
					have h25:= cardinalsinhabited M n h3,
					have h24:= Tsuccessor M n h3, 
					have h26:= successorF  M n h3 h2, 
					have h27:= cardinalsinhabited M (𝕊 n) h26,
					have h28:= Tsuccessor M n h3 h27, 
					have h29:= Tfinite M (𝕊 r) h5copy, 
					have h30:= Tfinite M (𝕊 n) h26,
	        have h31:= cardinalsinhabited M (𝕋 M (𝕊 n)) h30, 
					have h32:= cardinalsinhabited M (𝕋 M (𝕊 r)) h29, 
					simp_rw h23 at h32, 
					simp_rw h28 at h31, 
					have h40:=  strictordersuccessor M (𝕋 M n) (𝕋 M r) h19 h20 h31 h32,
          rw h40 at h18,
					have h41: 𝕋 M (𝕊 n) < 𝕋 M (𝕊 r):= 
            begin 
              rw [h23, h28],
              exact h18,
            end, 
					rw h11, 
          exact h41,
				}
			end,
		intros n h,
    rw F_members at h, 
    specialize h ( ZTorder M),
    have h3:= h (and.intro base  step), 
    rw ( ZTorder_members M) at h3, 
    cases h3 with h5 h6, 
    exact h6,  
  end



lemma Toneone: ∀ (n m: M), n ∈ 𝔽 → m ∈ 𝔽 → 𝕋 M n = 𝕋 M m → n = m:=
  assume n m,
  begin
    intros hn hm h,
    rw full_extensionality,
    have h2:= cardinalsinhabited M n hn,
    cases h2 with a h3,
    have h4:= cardinalsinhabited M m hm,
    cases h4 with b h5,
    have h6: USC a ∈ 𝕋 M n:=
      begin
        rw T_members,
        use a,
        split,
        {
          exact h3,
        },
        {
          exact similar_reflexive M (USC a), 
        }
      end,
    have h8: USC b ∈ 𝕋 M m:=
      begin
        rw T_members,
        use b,
        split,
        {
          exact h5,
        },
        {
          exact similar_reflexive M (USC b),
        },
      end,
    rw h at h6, 
    have h10:= Tfinite M m hm,
    have h11:= Tfinite M n hn, 
    have h9:= finitecardinals2 M (USC a) (USC b) (𝕋 M m) h10 h6 h8, 
    rw← uscsimilar at h9,
    have h12:= finitecardinals0 M n a b hn h3 h9, 
    have h14: b ∈ n ∩ m:=
      begin
        rw intersection_axiom,
        exact ⟨ h12, h5⟩, 
      end,
    have h13:= cardinalsdisjoint M n m b hn hm h14, 
    intro x,
    rw h13,
  end

lemma Tlessthan: ∀ (n m:M), n ∈ 𝔽 → m ∈ 𝔽 → (n < m ↔  𝕋 M n < 𝕋 M m):=
  assume n m,
  begin
    intros hn hm,
    split,
    {  --left to right
      have h3:= Torder M n hn m hm, 
      exact h3,
    },
    { --right to left 
      intro h,
      have h4:=Theorem2 M m n hm hn, 
      cases h4 with h5 h6,
      rw or_comm at h5, 
      have h20:= Tfinite M n hn, 
      have h30:= Tfinite M m hm, 
      cases h5 with h7 h8,
      {
        cases h7 with h9 h10,
        {
          rw h9 at *, 
          have h11:= xnotlessthanx M (𝕋 M n) h20,
          contradiction,
        },
        {
          exact h10,
        }
      },
      {
        have h21:= Torder M m hm n hn h8, 
        have h22:= Theorem2 M (𝕋 M n) (𝕋 M m) h20 h30,
        cases h22 with h23 h24,
        have h25:= and.intro h h21, 
        contradiction, 
      }
    }
  end

lemma Tlessthanorequal: ∀ (n m:M), n ∈ 𝔽 → m ∈ 𝔽 → (n ≤  m ↔  𝕋 M n ≤  𝕋 M m):=
  assume n m hn hm,
  begin
    have h3:= letolessthan M n m hn hm,
    have h4:= Tfinite M m hm,
    have h5:= Tfinite M n hn,
    have h6:= letolessthan M (𝕋 M n) (𝕋 M m) h5 h4,
    split,
    {
      intro h10,
      rw h3 at h10,
      cases h10 with h11 h12,
      {
        rw h6,
        left,
        have h13:= Tlessthan M n m hn hm,
        exact h13.1 h11,
      },
      {
        rw h12 at *,
        have h20:= le_reflexive M (𝕋 M m) h5,
        exact h20,
      },
    },
    {
      intros h21,
      rw h6 at h21,
      have h24:= Tlessthan M n m hn hm,
      cases h21 with h22 h23,
      {
        rw h3,
        left,   
        rw h24,
        exact h22,
      },
      {
        rw h3,
        right,
        have h24:= Toneone M n m hn hm h23,
        exact h24,
      }
    }
  end

lemma USCinverse: ∀ (e c:M), e ⊆ USC c → ∃ (q:M),q ⊆ c ∧ e = USC q:=
  begin
    intros e c h3,
    set q:= USC_inverse M e with qdef,
    use q,
    split,
    {
      rw subset_definition,
      intros x hx,
      rw qdef at hx,
      rw USC_inverse_members M at hx,
      have h4:= member_subset M e (USC c) (single x) h3 hx,
      rw usc_members at h4,
      exact h4,
    },
    {
      rw full_extensionality,
      intros t,
      split,
      {
        intros ht,
        have h5:= member_subset M e (USC c) t h3 ht,
        rw usc at h5,
        cases h5 with x h6,
        cases h6 with hx h7,
        rw qdef,
        rw usc,
        use x,
        split,
        {
          rw USC_inverse_members,
          rw h7 at *,
          exact ht,
        },
        {
          exact h7,
        }
      },
      {
        intros h8,
        rw usc at h8,
        cases h8 with x h9,
        cases h9 with h10 h11,
        rw h11 at *,
        rw qdef at h10,
        rw USC_inverse_members at h10,
        exact h10,
      }
    }
  end

lemma TNC: ∀(m:M), m ∈ NC M → 𝕋 M m ∈ NC M:=
  begin
    intros m h3,
    have h3copy:= h3,
    rw NC_members at h3,
    cases h3 with a h4,
    have h5:= xinNcx M a,
    rw← h4 at h5,
    have h6: USC a ∈ 𝕋 M m:=
      begin
        rw T_members,
        use a,
        exact ⟨ h5, similar_reflexive M (USC a) ⟩,
      end,
    have h7:= xinNcx M (USC a),
    have h8: 𝕋 M m = Nc M (USC a):=
      begin
        rw full_extensionality,
        intros t,
        rw T_members,
        rw Nc_members,
        split,
        {
          intros h,
          cases h with x h2,
          cases h2 with h10 h11,
          have h12:= cardinals2 M m a x h3copy h5 h10,
          have h13:= (uscsimilar M a x).1 h12,
          have h14:= (similar_symmetric M (USC a) (USC x)).1 h13,
          have h15:= similar_transitive M t (USC x) (USC a) h11 h14,
          exact h15,
        },
        {
          intros h20,
          use a,
          exact ⟨ h5, h20⟩,
        }
      end,
    rw NC_members,
    use USC a,
    exact h8,
  end

lemma Tonto: ∀ (p q:M), p ∈ 𝔽 → q ∈ 𝔽 → p < 𝕋 M q → ∃(r:M), (r ∈ 𝔽 ∧ p = 𝕋 M r):=
  assume p q,
  begin
    have base: zero ∈ Z_Tonto M:=
      begin
        rw Z_Tonto_members,
        split,
        {
          exact zeroF M,
        },
        {
          intros q hq  h,
          use zero,
          split,
          {
            exact zeroF M,
          },
          {
            have h3:= Tzero M,
            symmetry,
            exact h3,
          }
        }
      end,
    have step: ∀ (p:M), p ∈ Z_Tonto M → (∃ u, u ∈ 𝕊 p) → 𝕊 p ∈ Z_Tonto M:=
      assume p,
      begin
        intros h h3,
        rw Z_Tonto_members at h,
        rw Z_Tonto_members, 
        cases h with h4 h5,

        split,
        {
          exact successorF M p h4 h3, 
        },
        {
          intros q hq h6,
          have h7:= lessthansuccessor M p h4 h3, 
          have h9:=  successorF M p h4 h3,
          have h10:= Tfinite M p h4, 
          have h11:= Tfinite M q hq, 
          have h8:= lessthan_transitive M p (𝕊 p) (𝕋 M q) h4 h9 h11 h7 h6,
          have h9:= h5 q hq h8,
          cases h9 with r h12,
          cases h12 with h13 h14,
          use (𝕊 r),
          have h17: 𝕋 M r < 𝕋  M q:=
            begin
              rw← h14,
              have h15:= lessthan_transitive M p (𝕊 p) (𝕋 M q) h4 h9 h11 h7 h6,
              exact h15,
            end,
          have h18:= Tlessthan M r q h13 hq, 
          rw← h18 at h17, 
          have h19:= noinsertions M r q h13 hq h17,
          have h20: ∃(u:M), u ∈ 𝕊 r:=
            begin
              rw le_definition at h19,
              cases h19 with a h21,
              cases h21 with b h22,
              cases h22 with h23 h24,
              use a,
              exact h23, 
            end,
          have h21:= Tsuccessor M r h13 h20,
          split,
          { 
            have h22:= successorF M r h13 h20,
            exact h22, 
          },
          {
            rw h14, 
            symmetry,
            exact h21, 
          }
        }
      end,
    intro h,
    have hcopy := h, 
    rw F_members at h,
    specialize h (Z_Tonto M),
    have h3:= h ⟨ base, step  ⟩ , 
    rw (Z_Tonto_members M) at h3,
    cases h3 with h4 h5, 
    exact h5 q, 
  end

lemma Tonto2: ∀ (p q:M), p ∈ 𝔽 → q ∈ 𝔽 → p ≤ 𝕋 M q → ∃(r:M), (r ∈ 𝔽 ∧ p = 𝕋 M r):=
  assume p q,
  begin
    intros hp hq h,
    have h4:= letolessthan M p (𝕋 M q) hp (Tfinite M q hq),
    rw h4 at h,
    cases h with h5 h6,
    {
      have h3:= Tonto M p q hp hq h5, 
      exact h3,
    },
    {
      rw h6 at *,
      use q,
      exact ⟨ hq, refl (𝕋 M q)⟩, 
    }
  end

lemma Tonto3: ∀ (p q:M), p ∈ 𝔽 → q ∈ 𝔽 → p < 𝕋 M q → ∃(r:M), (r ∈ 𝔽 ∧ p = 𝕋 M r ∧ r < q):=
  assume p q,
  begin
    have base: zero ∈ Z_Tonto3 M:=
      begin
        rw Z_Tonto3_members,
        split,
        {
          exact zeroF M,
        },
        {
          intros q hq  h,
          use zero,
          split,
          {
            exact zeroF M,
          },
          {
            have h3:= Tzero M,
            split,
            {
              symmetry,
              exact h3,
            },
            {
              rw← h3 at h,
              rw← Tlessthan at h,
              exact h,
              exact zeroF M,
              exact hq,
            }
          }
        }
      end,
    have step: ∀ (p:M), p ∈ Z_Tonto3 M → (∃ u, u ∈ 𝕊 p) → 𝕊 p ∈ Z_Tonto3 M:=
      assume p,
      begin
        intros h h3,
        rw Z_Tonto3_members at h,
        rw Z_Tonto3_members, 
        cases h with h4 h5,

        split,
        {
          exact successorF M p h4 h3, 
        },
        {
          intros q hq h6,
          have h7:= lessthansuccessor M p h4 h3, 
          have h9:=  successorF M p h4 h3,
          have h10:= Tfinite M p h4, 
          have h11:= Tfinite M q hq, 
          have h8:= lessthan_transitive M p (𝕊 p) (𝕋 M q) h4 h9 h11 h7 h6,
          have h9:= h5 q hq h8,
          cases h9 with r h12,
          cases h12 with h13 h140,
          cases h140 with h14 h141,
          use (𝕊 r),
          have h17: 𝕋 M r < 𝕋  M q:=
            begin
              rw← h14,
              have h15:= lessthan_transitive M p (𝕊 p) (𝕋 M q) h4 h9 h11 h7 h6,
              exact h15,
            end,
          have h18:= Tlessthan M r q h13 hq, 
          rw← h18 at h17, 
          have h19:= noinsertions M r q h13 hq h17,
          have h20: ∃(u:M), u ∈ 𝕊 r:=
            begin
              rw le_definition at h19,
              cases h19 with a h21,
              cases h21 with b h22,
              cases h22 with h23 h24,
              use a,
              exact h23, 
            end,
          have h21:= Tsuccessor M r h13 h20,
          split,
          { 
            have h22:= successorF M r h13 h20,
            exact h22, 
          },
          {
            rw h14, 
            split,
            { 
              symmetry,
              exact h21, 
            },
            {
              rw lessthan_definition,
              split,
              {
                exact h19,
              },
              {
                intros h200,
                rw← h200 at *,
                rw h14 at h6,
                rw Tsuccessor at h6,
                have h8:= xnotlessthanx M (𝕊 (𝕋 M r)),
                have h201: 𝕊 (𝕋 M r ) ∈ 𝔽 :=
                  begin
                    rw← h14,
                    exact h9,
                  end, 
                have h202:= h8 h201,
                contradiction,
                exact h13,
                exact h20,
              }
            }
          }
        }
      end,
    intro h,
    have hcopy := h, 
    rw F_members at h,
    specialize h (Z_Tonto3 M),
    have h3:= h ⟨ base, step  ⟩ , 
    rw (Z_Tonto3_members M) at h3,
    cases h3 with h4 h5, 
    exact h5 q, 
  end

lemma fivepointthree_converse: ∀ (b:M), b ∈ 𝔽 → (∀ (a c:M), a ∈ 𝔽 → c ∈ 𝔽 →  𝕋 M a + 𝕋 M b  ∈ 𝔽 → 𝕋 M a + 𝕋 M b = 𝕋 M c → a + b = c):=
begin
  have base: zero ∈  Z_fivepointthree_converse M:=
    begin
      rw Z_fivepointthree_converse_members,
      split,
      {
        exact zeroF M,
      },
      {
        intros a c ha hc h20,
        rw Tzero,
        rw right_identityNF,
        rw right_identityNF,
        intro h,
        exact Toneone M a c ha hc h, 
      }
    end,
  have step: ∀ (b:M), b ∈ Z_fivepointthree_converse M→ (∃ (u:M), u ∈ 𝕊 b) → 𝕊 b ∈ Z_fivepointthree_converse M:=
    begin
      intros b hIH hsb,
      rw Z_fivepointthree_converse_members,
      rw Z_fivepointthree_converse_members at hIH,
      cases hIH with hb h3,
      split,
      {
        exact successorF M b hb hsb,
      },
      {
        intros a c ha hc h40,
        have hccopy:= hc, 
        have h4:= Tsuccessor M b hb hsb,
        rw h4,
        have h5:= h3 a c ha hc, 
        rw addition_equation,
        intro h10, 
        have h6: ¬ c = zero:=
          begin
            intro h7,
            rw h7 at *,
            rw Tzero at h10,
            have h11:= Fregesuccessoromits0 M (𝕋 M a + 𝕋 M b),
            contradiction,
          end,
        have h7:= nonzeroissuccessor M c hc h6, 
        cases h7 with r h8,
        cases h8 with h9 h11,
        rw h11 at hc h10,
        have h12:= Tsuccessor M r h9 (cardinalsinhabited M (𝕊 r) hc),
        rw h12 at h10, 
        rw h4 at h40,
        rw addition_equation at h40,
        have h20:= cardinalsinhabited M (𝕊 (𝕋 M a + 𝕋 M b)) h40, 
        have h21:= cardinalsinhabited M (𝕊 r) hc,
        have h22: ∃ (u:M), u ∈ 𝕋 M a + 𝕋 M b:=
          begin
            cases h20 with x h21,
            rw successor_members at h21, 
            cases h21 with p h22,
            cases h22 with q h23, 
            have h24:= h23.left,
            exact ⟨ p, h24⟩, 
          end,
        have h23:= Tfinite M a ha,
        have h24:= Tfinite M b hb, 
        have h25:= inhabited_sum M (𝕋 M b) h24 (𝕋 M a) h23 h22,
        have h26:= Tfinite M r h9, 
        have h27: ∃(u:M), (u ∈ 𝕊 (𝕋 M r)):=
          begin
            rw h10 at h40,
            exact cardinalsinhabited M (𝕊 (𝕋 M r)) h40,
          end, 
        have h121:= successoroneone M (𝕋 M a + 𝕋 M b) (𝕋 M r) h25 h26 h20 h27, 
        rw← h121 at h10,
        have h28:= h3 a r ha h9 h25 h10,
        rw h11, 
        rw addition_equation,
        rw h28, 
      }
    end,
  intros b h,
  rw F_members at h,
  specialize h (Z_fivepointthree_converse M),
  have h3:= h ⟨ base, step⟩,
  rw Z_fivepointthree_converse_members at h3,
  exact h3.right, 
end 

lemma Tzero2: ∀ (m:M), m ∈ 𝔽 → 𝕋 M m = zero → m = zero:=
  assume m hm h2,
  begin
    have h3:= Tzero M,
    rw← h3 at h2,
    have h4:= Toneone M m zero hm (zeroF M) h2,
    exact h4,
  end

lemma Tsum2_helper: ∀ (y:M), y ∈ 𝔽 → ∀ (x:M),x ∈ 𝔽 → 𝕊 (x + y) ∈ 𝔽 → x+y ∈ 𝔽:=
  begin
    intros y hy x hx h3,
    have h4:= cardinalsinhabited M (𝕊 (x+y)) h3,
    cases h4 with u hu,
    have h5:= successor_members M (x+y) u,
    rw h5 at hu,
    cases hu with v h6,
    cases h6 with c h7,
    rcases h7 with ⟨ h9, h10, h11⟩,
    have h12:= inhabited_sum M y hy x hx ⟨ v, h9⟩, 
    exact h12, 
  end

lemma Tsum2: ∀(r:M), r ∈ 𝔽 →  ∀ (n m:M), n ∈ 𝔽 → m ∈ 𝔽 → 𝕋 M n + 𝕋 M m = 𝕋 M r →  n+m = r:=
  begin
    have base: zero ∈ Z_Tsum2 M:=
      begin
        rw Z_Tsum2_members,
        split,
        {
          exact zeroF M,
        },
        {
          intros n m hn hm h1,
          rw Tzero at h1,
          rw sym at h1,
          have h2:= adds_to_zero M (𝕋 M n) (𝕋 M m) h1,
          have h3:= Tzero2 M n hn h2,
          rw h3,
          rw left_identityNF,
          rw h2 at h1,
          rw left_identityNF at h1,
          rw sym at h1,
          have h4:= Tzero2 M m hm h1,
          exact h4, 
        }
      end,
    have step: ∀ (r:M), r ∈ Z_Tsum2 M → (∃(u:M), u ∈ 𝕊 r) → 𝕊 r ∈ Z_Tsum2 M:=
      begin
        intros r h3 hsr,
        rw Z_Tsum2_members at h3,
        cases h3 with hr hIH,
        rw Z_Tsum2_members,
        split,
        {
          exact successorF M r hr hsr,
        },
        {
          intros n m hn hm h4,
          have h5:= FregeNdecidable M,
          rw decidable_members at h5,
          have h6:= h5 m zero ⟨ hm, zeroF M⟩,
          cases h6 with h7 h8,
          {
            rw h7 at *,
            rw Tzero at h4,
            rw right_identityNF at h4,
            have h9:= Toneone M n (𝕊 r) hn (successorF M r hr hsr) h4,
            rw right_identityNF,
            exact h9,
          },
          {
            have h10:= nonzeroissuccessor M m hm h8,
            cases h10 with p h11,
            cases h11 with hp h12,
            have h13:=Tsuccessor M r hr hsr,
            rw h13 at h4,
            rw h12 at h4,
            have hmcopy := hm,
            rw h12 at hm,
            have h15:= cardinalsinhabited M (𝕊 p) hm,
            have h14:=Tsuccessor M p hp h15,
            have h4copy:= h4,
            rw h14 at h4,
            rw addition_equation at h4,
            have h16:= successorF M r hr hsr,
            have h17:= Tfinite M (𝕊 r) h16,
            rw h13 at h17,
            have h18:= cardinalsinhabited M (𝕊 r) h16, 
            have h19:= Tfinite M r hr,
            rw← h12 at h4copy,
            have h17copy:= h17,
            rw← h4copy at h17copy,
            have h20:= cardinalsinhabited M (𝕊 (𝕋 M r)) h17,
            have h21:= h20,
            rw← h4 at h21,
            rw← h4 at h17,
            have h22:= Tsum2_helper M (𝕋 M p) (Tfinite M p hp) (𝕋 M n)(Tfinite M n hn) h17,
            have h15:= successoroneone M (𝕋 M n + 𝕋 M p) (𝕋 M r) h22 h19 h21 h20,
            rw h4 at h15,
            simp at h15,
            have h30:= hIH n p hn hp h15,
            rw← h30,
            rw h12,
            rw addition_equation,
          }
        }
      end,
    intros r hr,
    rw F_members at hr,
    have h5:= hr (Z_Tsum2 M) ⟨base, step⟩,
    rw Z_Tsum2_members at h5,
    exact h5.right,
  end
  
#axioms_all  -- This file is clean.