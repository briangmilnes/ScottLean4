import ChurchNumbers8
-- proof of equivalence of ChurchCountingAxiom and RosserCountingAxiom

variables (M:Type) [Model M] (a b x y z u v w X R W κ μ ℓ : M)

open Model 
 
def RosserCountingAxiom:= ∀ (x:M), x ∈ 𝔽 → 𝕁 M x ∈ x
def ChurchCountingAxiom:= ∀ (x:M), x ∈ ℕℕ → Ap (Ap x (SG M)) ChurchZero = x

lemma T2: (∀ (x:M), x ∈ 𝔽 → 𝕋 M (𝕋 M x) = x) → ∀ (x:M), x ∈ 𝔽 → 𝕋 M x = x:=
  begin
    intros h x hx,
    have hTx:= Tfinite M x hx,
    have h3:= finitetrichotomy M x hx (𝕋 M x) hTx,
    have hT2x:= Tfinite M (𝕋 M x) hTx,
    have h21:= h x hx,
    cases h3 with h4 h5,
    {
      have h6:= Tlessthan M x (𝕋 M x) hx hTx,
      rw h6 at h4,
      have h7:= h x hx,
      rw h7 at h4,
      rw h7 at h6,
      rw← h6 at h4,
      have h8:= h6.mp h4,
      have h9:= lessthan_transitive M (𝕋 M x) x (𝕋 M x) hTx hx hTx h8 h4,
      have h10:= xnotlessthanx M (𝕋 M x) hTx,
      contradiction,
    },
    {
      cases h5 with h30 h31,
      {
        symmetry,
        exact h30,
      },
      {
        have h32:= Tlessthan M (𝕋 M x) x hTx hx,
        rw h21 at h32,
        have h33:= h32.mp h31,
        have h34:= lessthan_transitive M x (𝕋 M x) x hx hTx hx h33 h31,
        have h35:= xnotlessthanx M x hx,
        contradiction,
      }
    }
  end

lemma T6: (∀ (x:M), x ∈ 𝔽 → (𝕋 M (𝕋 M (𝕋 M (𝕋 M  (𝕋 M (𝕋 M x)))))) = x) → ∀ (x:M), x ∈ 𝔽 → 𝕋 M x = x:=
  begin
    intros h x hx,
    have hTx:= Tfinite M x hx,
    have h3:= finitetrichotomy M x hx (𝕋 M x) hTx,
    have hT2x:= Tfinite M (𝕋 M x) hTx,
    have hT3x:= Tfinite M (𝕋 M (𝕋 M x)) hT2x,
    have hT4x:= Tfinite M (𝕋 M (𝕋 M (𝕋 M x))) hT3x,
    have hT5x:= Tfinite M (𝕋 M (𝕋 M (𝕋 M (𝕋 M x)))) hT4x,
    have hT6x:= Tfinite M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M x))))) hT5x,
    have h21:= h x hx,
    cases h3 with h4 h5,
    {
      have h6:= (Tlessthan M x (𝕋 M x) hx hTx).mp h4,
      have h17:= (Tlessthan M (𝕋 M x) (𝕋 M (𝕋 M x)) hTx hT2x).mp h6,
      have h18:= lessthan_transitive M x (𝕋 M x) (𝕋 M (𝕋 M x)) hx hTx hT2x h4 h6,
      have h19:= lessthan_transitive M x (𝕋 M (𝕋 M x))  (𝕋 M (𝕋 M (𝕋 M x))) hx hT2x hT3x h18 h17,
      have h22:= ((Tlessthan M ) x (𝕋 M (𝕋 M (𝕋 M x))) hx hT3x).mp h19,
      have h23:= lessthan_transitive M x (𝕋 M x) (𝕋 M (𝕋 M (𝕋 M (𝕋 M x)))) hx hTx hT4x h4 h22,
      have h24:= (Tlessthan M x (𝕋 M (𝕋 M (𝕋 M (𝕋 M x)))) hx hT4x).mp h23,
      have h25:= lessthan_transitive M x (𝕋 M x) (𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M x))))) hx hTx hT5x h4 h24,
      have h26:= (Tlessthan M x (𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M x))))) hx hT5x).mp h25,
      have h27:= lessthan_transitive M x (𝕋 M x) (𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M x)))))) hx hTx hT6x h4 h26, 
      have h28:= h x hx,
      rw h28 at h27,
      have h29:= xnotlessthanx M x hx,
      contradiction,
    },
    {
      cases h5 with h30 h31,
      {
        symmetry,
        exact h30,
      },
      { 
        have h6:= (Tlessthan M  (𝕋 M x) x hTx hx).mp h31,
        have h17:= (Tlessthan M  (𝕋 M (𝕋 M x))(𝕋 M x) hT2x hTx).mp h6,
        have h18:= lessthan_transitive M (𝕋 M (𝕋 M x))   (𝕋 M x)  x  hT2x  hTx  hx h6 h31,
        have h19:= lessthan_transitive M  (𝕋 M (𝕋 M (𝕋 M x))) (𝕋 M (𝕋 M x)) x hT3x hT2x hx h17 h18,
        have h22:= ((Tlessthan M )(𝕋 M (𝕋 M (𝕋 M x)))  x  hT3x hx).mp h19,
        have h23:= lessthan_transitive M (𝕋 M (𝕋 M (𝕋 M (𝕋 M x))))  (𝕋 M x) x hT4x  hTx hx h22 h31,
        have h24:= (Tlessthan M   (𝕋 M (𝕋 M (𝕋 M (𝕋 M x)))) x   hT4x hx).mp h23,
        have h25:= lessthan_transitive M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M x)))))  (𝕋 M x) x  hT5x hTx hx h24 h31,
        have h26:= (Tlessthan M  (𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M x))))) x  hT5x hx).mp h25,
        have h27:= lessthan_transitive M   (𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M x))))))  (𝕋 M x) x hT6x hTx hx h26 h31, 
        rw (h x hx) at h27,
        have h35:= xnotlessthanx M x hx,
        contradiction,
      }
    }
  end

lemma RosserT: 
  RosserCountingAxiom M ↔ ∀ (x:M),x ∈ 𝔽 → 𝕋 M x = x:=
    begin
      
      split,
      {  intro h,
         have h20: ∀ (x:M), x ∈ 𝔽  → (𝕋 M (𝕋 M x)) = x:=
          begin
            intros x hx,
            unfold RosserCountingAxiom at h,
            have h3:= Jcardinality M x hx,
            have h4:= Ncdef M (𝕁 M x) x hx (h x hx),
            have hTx:= Tfinite M x hx,
            have hT2x:= Tfinite M (𝕋 M x) hTx,
            have h5:= Ncdef M (𝕁 M x) (𝕋 M (𝕋 M x)) hT2x h3,
            rw← h4 at h5,
            exact h5,
          end,
        intros x hx,
        have h30:= T2 M h20 x hx,
        exact h30,
      },
      {
        intros h,
        unfold RosserCountingAxiom,
        intros x hx,
        have h3:= Jcardinality M x hx,
        have h4:= h x hx,
        rw h4 at h3,
        rw h4 at h3,
        exact h3,
      }
    end

lemma ChurchFregeRel: Rel (ChurchFrege M):=
  begin
    rw Rel_definition,
    intros z h,
    rw ChurchFrege_members at h,
    cases h with h3 h4,
    cases h3 with p h5,
    cases h5 with q h6,
    rcases h6 with ⟨ h7, h8, h9⟩, 
    use p, use q,
    exact h7, 
  end

lemma ChurchFrege0: ‹ ChurchZero, zero › ∈ ChurchFrege M:=
  begin
    rw ChurchFrege_members,
    split,
    {
      use ChurchZero, use zero,
      simp,
      exact ⟨ zeroN M, zeroF M⟩,
    },
    {
      intros w hw h3,
      exact hw,
    } 
  end

lemma ChurchFrege1: ∀ (p q:M), ‹ p, q› ∈ ChurchFrege M → 𝕊 q ∈ 𝔽 → ‹ S p, 𝕊 q › ∈ ChurchFrege M:=
  begin
    intros p q h3 h4,
    rw ChurchFrege_members at h3,
    rw ChurchFrege_members,
    cases h3 with h4 h5,
    cases h4 with a h6,
    cases h6 with b h7,
    cases h7 with h8 h9,
    rw ordered_pair_equality at h8,
    cases h8 with h10 h11,
    rw← h10 at *,
    rw← h11 at *,
    cases h9 with h12 h13,
    split,
    {
      use S p, use 𝕊 q, simp,
      exact ⟨ successorN M p h12, h4⟩, 
    },
    { 
      intros w h14 h15,
      have h16:= h5 w h14 h15,
      have h17:= h15 p q h16 h4,
      exact h17,
    }
  end

lemma ChurchFrege_domainrange: ∀ (p q:M), ‹ p,q › ∈ ChurchFrege M → p ∈ ℕℕ ∧ q ∈ 𝔽 :=
  assume p q h,
  begin
    rw ChurchFrege_members at h,
    cases h with h1 h2,
    cases h1 with a h3,
    cases h3 with b h4,
    cases h4 with h5 h6,
    rw ordered_pair_equality at h5,
    cases h5 with h7 h8,
    rw← h7 at *,
    rw← h8 at *,
    exact h6,
  end

lemma ChurchFrege2: ∀ (p q:M), ‹ p,q › ∈ ChurchFrege M → 
((p = ChurchZero ∧ q = zero) ∨ ∃ (t r:M), ‹ t,r› ∈ ChurchFrege M ∧ p = S t ∧ q = 𝕊 r):=
  begin
    have base: ‹ ChurchZero, zero›  ∈ W_ChurchFrege M:=
      begin
        rw W_ChurchFrege_members,
        use ChurchZero, use zero,
        simp,
      end,
    have step: ∀ (p q:M), ‹ p,q › ∈ W_ChurchFrege M → 𝕊 q ∈ 𝔽 → ‹ S p, 𝕊 q › ∈ W_ChurchFrege M:=
      begin
        intros p q h h40,
        rw W_ChurchFrege_members at h,
        rw W_ChurchFrege_members,
        cases h with a h2,
        cases h2 with b h3,
        cases h3 with h4 h5,
        rw ordered_pair_equality at h4,
        cases h4 with h6 h7,
        rw← h6 at *,
        rw← h7 at *,
        cases h5 with h8 h9,
        {
          cases h8 with h10 h11,
          use S p, use 𝕊 q,
          simp,
          right,
          use p, use q,
          simp,
          rw h10,
          rw h11,
          exact ChurchFrege0 M,
        },
        { 
          cases h9 with t h10,
          cases h10 with r h11,
          rcases h11 with ⟨ h12, h13, h14⟩, 
          use S p, use 𝕊 q,
          simp,
          right,
          use p, use q,
          simp,
          rw h13,
          rw h14,
          have h16:= ChurchFrege_domainrange M t r h12,
          have h17:= successorF M r h16.right,
          have h15:= ChurchFrege1 M t r h12,
          cases h16 with h18 h19,
          have h41:= cardinalsinhabited M (𝕊 q) h40,
          cases h41 with x h42,
          rw successor_members at h42,
          cases h42 with y h43,
          cases h43 with c h44,
          rw h14 at *,
          cases h44 with h45 h46,
          have h47:= successorF M r h19 ⟨ y, h45⟩, 
          exact h15 h47,
        }
      end,
    intros p q h,
    have h20:= ChurchFrege_domainrange M p q h,
    have h21: ChurchFrege M ⊆ W_ChurchFrege M:=
      begin
        rw subset_definition,
        intros z h22,
        rw ChurchFrege_members at h22,
        cases h22 with h23 h24,
        have h25:= h24 (W_ChurchFrege M) base step,
        exact h25,
      end,
    cases h20 with h30 h31,
    have h32:= member_subset M (ChurchFrege M) (W_ChurchFrege M) ‹ p,q › h21 h,
    rw W_ChurchFrege_members at h32,
    cases h32 with a h33,
    cases h33 with b h34,
    cases h34 with h35 h36,
    rw ordered_pair_equality at h35,
    cases h35 with h36 h37,
    rw← h36 at *,
    rw← h37 at *,
    cases h36 with h38 h39,
    {
      left,
      exact h38,
    },
    {
      right,
      exact h39,
    }
  end

lemma ChurchFrege3: ∀ (p y:M), y ∈ 𝔽 → ‹ p,𝕊 y › ∈ ChurchFrege M → 
  ∃ (t:M), ‹ t,y› ∈ ChurchFrege M ∧ p = S t:=
  begin
    intros p y hy h3,
    have h4:= ChurchFrege2 M p (𝕊 y) h3,
    cases h4 with h5 h6,
    {
      cases h5 with h7 h8,
      have h9:= Fregesuccessoromits0 M y,
      contradiction,
    },
    {
      cases h6 with t h10,
      cases h10 with r h11,
      use t,
      rcases h11 with ⟨ h12, h13, h14⟩,
      have h20:= ChurchFrege_domainrange M t r h12,
      cases h20 with ht hr,
      have h21:= ChurchFrege_domainrange M p (𝕊 y) h3,
      cases h21 with hp hsy,
      have h22:= cardinalsinhabited M (𝕊 y) hsy,
      have hsr:= hsy,
      rw h14 at hsr,
      have h23:= cardinalsinhabited M (𝕊 r) hsr,
      have h25:= successoroneone M y r hy hr h22 h23,
      rw← h25 at h14,
      rw← h14 at *,
      exact ⟨ h12, h13⟩,
    }
  end
 
lemma ChurchRosserhelper:
(∀ (x y:M), x∈ ℕℕ  → y ∈ ℕℕ → S x = S y → x = y)→ 
∀ (x:M), x ∈ ℕℕ → ∀(y z:M), ‹ x,y › ∈ ChurchFrege M → ‹ Ap (Ap x (SG M)) ChurchZero, z› ∈ ChurchFrege M → 𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M z))))) = y:=
  begin
    intros honeone,
    have base: ChurchZero ∈ Z_ChurchRosserhelper M:=
      begin
        rw Z_ChurchRosserhelper_members,
        split,
        {
          exact zeroN M,
        },
        {
          intros y z h h3,
          have h4:= ChurchFrege2 M ChurchZero y h,
          simp at h4,
          cases h4 with h5 h6,
          {
            rw h5 at *,
            have h7:= ChurchFrege2 M ( Ap (Ap ChurchZero (SG M)) ChurchZero)  z h3,
            cases h7 with h8 h9,
            {
              cases h8 with h10 h11,
              rw h11 at *,
              have h12:= Tzero M,
              repeat {rw h12},
            },
            { 
              cases h9 with t h10,
              cases h10 with r h11,
              rcases h11 with ⟨ h12, h13, h14⟩, 
              rw h14,
              have h15:= Tsuccessor M,
              have h16:= ChurchFrege_domainrange M  (Ap (Ap ChurchZero (SG M)) ChurchZero) z h3,
              cases h16 with h17 hz,
              have h18:= ChurchFrege_domainrange M t r h12,
              cases h18 with ht hr,
              have h19:= h15 r hr,
              have h20:= ApZero M (SG M),
              rw h20 at h13,
              have h21:= ApId M ChurchZero,
              rw h21 at h13,
              have h22:= successoromitszero M t ht,
              rw← h13 at h22,
              contradiction,
            }
          },
          {
            cases h6 with t h7,
            cases h7 with r h8,
            cases h8 with h9 h10,
            cases h10 with h11 h12,
            have h13:= ChurchFrege_domainrange M t r h9,
            cases h13 with ht hr,
            have h14:= successoromitszero M t ht,
            rw sym at h14,
            contradiction,
          }
        }
      end,
    have step: ∀ (x:M), x ∈ Z_ChurchRosserhelper M → S x ∈ Z_ChurchRosserhelper M:=
      begin
        intros x h3,
        rw Z_ChurchRosserhelper_members at h3,
        rw Z_ChurchRosserhelper_members,
        cases h3 with hx h4,
        split,
        {
          exact successorN M x hx,
        },
        {
          intros y z h5 h6,
          have h7:= xsmapsN M x hx ChurchZero (zeroN M),
          have h9:= successorequation M ℕℕ (SG M) (SGFUNC M) (SGRel M) (SGMaps M) x ChurchZero hx (zeroN M),
          rw h9 at h6,
          have h10:= ChurchFrege2 M (Ap (SG M) (Ap (Ap x (SG M)) ChurchZero)) z h6,
          cases h10 with h11 h12,
          {
            have h13:= ApSG M (  (Ap (Ap x (SG M)) ChurchZero)) h7,
            rw h13 at h11,
            cases h11 with h14 h15,
            have h16:= successoromitszero M (Ap (Ap x (SG M)) ChurchZero) h7, 
            contradiction, 
          },
          {
            cases h12 with p h13,
            cases h13 with r h14,
            cases h14 with h15 h16,
            cases h16 with h17 h18,
            have h19:= ApSG M (Ap (Ap x (SG M)) ChurchZero) h7,
            rw h19 at h17,
            have h20:= ChurchFrege_domainrange M p r h15,
            cases h20 with hp hr,
            have h21:= honeone (Ap (Ap x (SG M)) ChurchZero) p h7 hp h17,
            rw← h21 at *,
            have h22:= ChurchFrege2 M (S x) y h5,
            cases h22 with h23 h24,
            {
              cases h23 with h25 h26,
              have h27:= successoromitszero M x hx,
              contradiction,
            },
            {
              cases h24 with q h25,
              cases h25 with t h26,
              cases h26 with h27 h28,
              cases h28 with h29 h30,
              have h31:= ChurchFrege_domainrange M q t h27,
              cases h31 with hq ht,
              have h32:= honeone x q hx hq h29,
              rw← h32 at *,
              have h33:= h4 t r h27 h15,
              have h34: 𝕊 (𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M r)))))) = 𝕊 t:=
                begin
                  rw h33,
                end,
              rw h30,
              rw h18,
              have h49:= ChurchFrege_domainrange M (Ap (SG M) (Ap (Ap x (SG M)) ChurchZero)) z h6,
              cases h49 with h48 hz,
              have h50:= cardinalsinhabited M z hz,
              rw h18 at h50,
              have h40:= Tsuccessor M r hr h50,
              rw h40, 
              have h35:= Tfinite M r hr,
              have h36:= successorT M r hr,
              have h37:= cardinalsinhabited M (𝕊 (𝕋 M r)) h36,
              have h38:= successorT M (𝕋 M r) h35,
              have h68:= cardinalsinhabited M (𝕊 (𝕋 M (𝕋 M r))) h38,
              have h39:= Tfinite M (𝕋 M r) h35,
              have h40:= successorT M (𝕋 M (𝕋 M r)) h39,
              have h69:= cardinalsinhabited M (𝕊 (𝕋 M (𝕋 M (𝕋 M r)))) h40,
              have h41:= Tfinite M (𝕋 M (𝕋 M r)) h39,
              have h42:= successorT M (𝕋 M (𝕋 M (𝕋 M r))) h41,
              have h70:= cardinalsinhabited M (𝕊 (𝕋 M (𝕋 M (𝕋 M (𝕋 M r))))) h42,
              have h43:= Tfinite M (𝕋 M (𝕋 M (𝕋 M r))) h41,
              have h44:= successorT M (𝕋 M (𝕋 M (𝕋 M (𝕋 M r)))) h43,
              have h71:= cardinalsinhabited M (𝕊 (𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M r)))))) h44,
              have h45:= Tfinite M (𝕋 M (𝕋 M (𝕋 M (𝕋 M r)))) h43,
              have h46:= successorT M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M r))))) h45,
              have h72:= cardinalsinhabited M (𝕊 (𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M r))))))) h46, 
              have h47:= Tfinite M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M r))))) h45,
              have h51:= Tsuccessor M (𝕋 M r) h35 h37,
              have h52:= Tsuccessor M (𝕋 M (𝕋 M r)) h39 h68,
              have h53:= Tsuccessor M (𝕋 M (𝕋 M (𝕋 M r))) h41 h69,
              have h54:= Tsuccessor M (𝕋 M (𝕋 M (𝕋 M (𝕋 M r)))) h43 h70,
              have h55:= Tsuccessor M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M r))))) h45 h71,
              rw h51,
              rw h52,
              rw h53,
              rw h54,
              rw h55,
              rw h33, 
            }
          } 
        }
      end,
    intros x hx,
    rw N_members at hx,
    have h4:= hx (Z_ChurchRosserhelper M) ⟨ base, step⟩,
    rw Z_ChurchRosserhelper_members at h4,
    exact h4.right,
  end

lemma ChurchFregeonto: ∀ (y:M), y ∈ 𝔽 → ∃ (x:M), x ∈ ℕℕ ∧ ‹ x,y› ∈ ChurchFrege M:=
  begin
    have base: zero ∈ Z_ChurchFregeonto M:=
      begin
        rw Z_ChurchFregeonto_members, 
        split,
        {
          exact zeroF M,
        },
        {
          use ChurchZero,
          split,
          {
            exact zeroN M,
          },
          {
            exact ChurchFrege0 M,
          }
        }
      end,
    have step: ∀ (y:M), y ∈ Z_ChurchFregeonto M → (∃ (u:M), u ∈ 𝕊 y) → 𝕊 y ∈ Z_ChurchFregeonto M:=
      begin
        intros y h hsy,
        rw Z_ChurchFregeonto_members at h,
        cases h with hy h3,
        have h4:= successorF M y hy hsy,
        rw Z_ChurchFregeonto_members,
        split,
        {
          exact h4,
        },
        {
          cases h3 with x h5,
          cases h5 with hx h6,
          use S x,
          split,
          {
            exact successorN M x hx,
          },
          {
            have h6:= ChurchFrege1 M x y h6 h4,
            exact h6,
          }
        }
      end,
    intros y hy,
    rw F_members at hy,
    have h5:= hy (Z_ChurchFregeonto M) ⟨ base, step⟩,
    rw Z_ChurchFregeonto_members at h5,
    exact h5.right,
  end
 
theorem ChurchimpliesRosser: ChurchCountingAxiom M → RosserCountingAxiom M :=
  begin
    intro hChurch,
    have hnotfinite:= main M hChurch, 
    have honeone:= Churchsuccessoroneone M hnotfinite,
    have honto:= ChurchFregeonto M,
    have h5: ∀ (z:M), z ∈ 𝔽 → (𝕋 M (𝕋 M (𝕋 M (𝕋 M  (𝕋 M (𝕋 M z)))))) = z:=
      begin
        intros z hz,
        have h6:= honto z hz,
        cases h6 with x h7,
        cases h7 with hx h8,
        have h9:= hChurch x hx,
        have h8copy:= h8,
        rw← h9 at h8copy,
        have h10:= ChurchRosserhelper M honeone x hx z z h8 h8copy,
        exact h10,
      end,
    have h20:= T6 M h5,
    rw RosserT,
    exact h20,
  end

lemma ChurchFregeoneone: ∀ (y:M), y ∈ 𝔽 →  ∀ (x z:M), ‹ x,y › ∈ ChurchFrege M → ‹ z,y › ∈ ChurchFrege M → x = z:=
  begin
    have base: zero ∈ Z_ChurchFregeoneone M:=
      begin
        rw Z_ChurchFregeoneone_members,
        split,
        {
          exact zeroF M,
        },
        {
          intros x z h3 h4,
          have h5:= ChurchFrege2 M x zero h3,
          simp at h5,
          cases h5 with h6 h7,
          {
            rw h6 at *,
            have h8:= ChurchFrege2 M z zero h4,
            simp at h8,
            cases h8 with h9 h10,
            {
              rw h9 at *,
            },
            {
              cases h10 with t h11,
              cases h11 with r h12,
              cases h12 with h13 h14,
              cases h14 with h15 h16,
              have h17:= ChurchFrege_domainrange M t r h13,
              cases h17 with ht hr,
              have h20:= Fregesuccessoromits0 M r,
              rw h16 at h20,
              contradiction,
            }
          },
          {
            cases h7 with t h8,
            cases h8 with r h9,
            rcases h9 with ⟨ h10, h11, h12⟩,
            have h13:= Fregesuccessoromits0 M r,
            rw h12 at h13,
            contradiction,
          }
        }
      end,
    have step: ∀ (y:M), y ∈ Z_ChurchFregeoneone M → (∃ (u:M), u ∈ 𝕊 y) → 𝕊 y ∈ Z_ChurchFregeoneone M:=
      begin
        intros y h4 hsy,
        rw Z_ChurchFregeoneone_members at h4,
        cases h4 with hy h5,
        rw Z_ChurchFregeoneone_members,
        split,
        {
          exact successorF M y hy hsy,
        },
        {
          intros x z h10 h11,
          have h12:= ChurchFrege2 M x (𝕊 y) h10,
          cases h12 with h13 h14,
          {
            cases h13 with h15 h16,
            have h17:= Fregesuccessoromits0 M y,
            contradiction,
          },
          {
            cases h14 with p h20,
            cases h20 with r h21,
            rcases h21 with ⟨ h22, h23, h24⟩, 
            have h25:= ChurchFrege2 M z (𝕊 y) h11,
            cases h25 with h26 h27,
            {
              cases h26 with h28 h29,
              have h30:= Fregesuccessoromits0 M y,
              contradiction,
            },
            {
              cases h27 with q h31,
              cases h31 with t h32,
              rcases h32 with ⟨ h33, h34, h35⟩,
              have h36:= ChurchFrege_domainrange M q t h33,
              have h37:= ChurchFrege_domainrange M p r h22,
              cases h36 with hq ht,
              cases h37 with hp hr,
              have hst := hsy,
              have hsr := hsy,
              rw h24 at hsr,
              rw h35 at hst,
              have h38:= successoroneone M y t hy ht hsy hst,
              rw← h38 at h35,
              have h39:= successoroneone M y r hy hr hsy hsr,
              rw← h39 at h24,
              have h40: ‹ q,y › ∈ ChurchFrege M:=
                begin
                  rw h35,
                  exact h33,
                end,
              have h41: ‹ p,y › ∈ ChurchFrege M:=
                begin
                  rw←  h24 at h22,
                  exact h22,
                end,
              have h42:= h5 p q h41 h40,
              rw [h23, h34, h42],
            }
          }
        }
      end,
    intros y hy,
    rw F_members at hy,
    have h5:= hy (Z_ChurchFregeoneone M) ⟨ base,step⟩,
    rw Z_ChurchFregeoneone_members at h5,
    exact h5.right,
  end

lemma RosserimpliesFinfinite: RosserCountingAxiom M → ∀ (x:M),x ∈ 𝔽 → ∃ (u:M), u ∈ 𝕊 x:=
  assume Rosser,
  begin
    have base: zero ∈ Z_successorinhabited M:=
      begin
        rw Z_successorinhabited_members,
        split,
        {
          exact zeroF M,
        },
        {
          use zero,
          have h5:= zeroinone M,
          rw one_definition at h5,
          exact h5,
        }
      end,
    have step: ∀ (x:M), x ∈ Z_successorinhabited M → (∃(u:M), u ∈ 𝕊 x) → 𝕊 x ∈ Z_successorinhabited M:=
      begin
        intros x h5 hsx,
        rw Z_successorinhabited_members,
        rw Z_successorinhabited_members at h5,
        cases h5 with hx h6,
        split,
        {
          exact successorF M x hx hsx,
        },
        {
          have h8:= successorF M x hx hsx,
          have h9:= Rosser (𝕊 x) h8,
          have h10:= xnotlessthanx M (𝕊 x) h8,
          have h11: ¬ (𝕊 x ∈ 𝕁 M (𝕊 x)):=
            begin
              intro h,
              rw J_members at h,
              cases h with h12 h13,
              contradiction,
            end,
          use 𝕁 M (𝕊 x) ∪ (single (𝕊 x)),
          rw successor_members,
          use 𝕁 M (𝕊 x), use (𝕊 x),
          simp,
          exact ⟨ h9, h11⟩, 
        }
      end,
    intros y hy,
    rw F_members at hy,
    have h5:= hy (Z_successorinhabited M)⟨ base, step⟩,
    rw Z_successorinhabited_members at h5,
    exact h5.right,
  end

lemma Rosserimpliesitotal: RosserCountingAxiom M → ∀ (x:M), x ∈ ℕℕ → ∃ (y:M), y ∈ 𝔽 ∧ ‹ x,y› ∈ ChurchFrege M:=
  assume Rosser,
  begin
    have base: ChurchZero ∈ dom (ChurchFrege M):=
      begin
        rw domain_axiom (ChurchFrege M) (ChurchFregeRel M),
        use zero,
        exact ChurchFrege0 M,
      end,
    have step: ∀(x:M), x ∈ dom (ChurchFrege M) → S x ∈ dom (ChurchFrege M):=
      begin
        intros x h,
        rw domain_axiom (ChurchFrege M) (ChurchFregeRel M) at h,
        cases h with y h3,
        rw domain_axiom (ChurchFrege M) (ChurchFregeRel M),
        use 𝕊 y,
        have h5:= ChurchFrege1 M x y h3,
        apply h5,
        have h3:= ChurchFrege_domainrange M x y h3,
        cases h3 with hx hy,
        have h6:= RosserimpliesFinfinite M Rosser y hy,
        have h7:= successorF M y hy h6,
        exact h7,
      end,
    intros x hx,
    rw N_members at hx,
    have h5:= hx (dom (ChurchFrege M)) ⟨ base, step⟩, 
    rw domain_axiom (ChurchFrege M) (ChurchFregeRel M) at h5,
    cases h5 with y h6,
    have h7:= ChurchFrege_domainrange M x y h6,
    cases h7 with hx hy,
    use y,
    exact ⟨ hy, h6⟩, 
  end

lemma jFUNC: RosserCountingAxiom M → ∀ (x:M), x ∈ 𝔽 → ∀ (y z:M), ‹ y,x › ∈ ChurchFrege M → ‹ z,x› ∈ ChurchFrege M → y = z:=
  assume Rosser,
  begin
    have base: zero ∈ Z_jFUNC M:=
      begin
        rw Z_jFUNC_members,
        split,
        {
          exact zeroF M,
        },
        {
          intros y z h2 h3,
          have h4:= ChurchFrege2 M y zero h2,
          have h5:= ChurchFrege2 M z zero h3,
          simp at h4,
          simp at h5,
          cases h4 with h6 h7,
          {
            rw h6 at *,
            cases h5 with h8 h9,
            {
              rw h8 at *,
            },
            {
              cases h9 with t h10,
              cases h10 with r h11,
              rcases h11 with ⟨ h12, h13, h14⟩,
              have h16:= ChurchFrege_domainrange M t r h12,
              cases h16 with ht hr,
              rw sym at h14,
              have h15:= Fregesuccessoromits0 M r,
              contradiction,
            }
          },
          {
            cases h7 with t h20,
            cases h20 with r h21,
            rcases h21 with ⟨ h22, h23,h24⟩,
            have h25:= Fregesuccessoromits0 M r,
            rw sym at h24,
            contradiction,
          }
        }
      end,
    have step: ∀ (x:M), x ∈ Z_jFUNC M → (∃ (u:M), u ∈ 𝕊 x) → 𝕊 x ∈ Z_jFUNC M:=
      begin
        intros x h3 hsx,
        rw Z_jFUNC_members at h3,
        rw Z_jFUNC_members,
        cases h3 with hx h4,
        split,
        {
          exact successorF M x hx hsx,
        },
        {
          intros y z h5 h6,
          have h7:= ChurchFrege_domainrange M y (𝕊 x) h5,
          cases h7 with h8 h9,
          have h10:= ChurchFrege_domainrange M z (𝕊 x) h6,
          cases h10 with h11 h12,
          have h13:= ChurchFrege3 M y x hx h5,
          have h14:= ChurchFrege3 M z x hx h6,
          cases h13 with r h16,
          cases h16 with h17 h18,
          cases h14 with t h19,
          cases h19 with h20 h21,
          have h22:= h4 r t h17 h20,
          rw [h18, h21, h22],
        }
      end,
    intros x hx,
    rw F_members at hx,
    have h5:= hx (Z_jFUNC M) ⟨ base, step⟩, 
    rw Z_jFUNC_members at h5,
    exact h5.right,
  end 

lemma jhelper: RosserCountingAxiom M →  ∀ (x:M), x ∈ 𝔽 → ∀ (y z:M), ‹ y,x› ∈ ChurchFrege M → ‹ z, 𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M (𝕋 M x))))) › ∈ ChurchFrege M →   Ap( Ap y (SG M)) ChurchZero = z :=
  assume Rosser,
  begin
    have base: zero ∈ Z_jhelper M:=
      begin
        rw Z_jhelper_members,
        split,
        {
          exact zeroF M,
        },
        {
          intros y z h3 h4,
          have h5:= ChurchFrege0 M,
          have h6:= jFUNC M Rosser zero (zeroF M) y ChurchZero h3 h5,
          rw h6 at *,
          rw ApZero,
          rw ApId,
          repeat {rw Tzero at h4},
          have h7:= jFUNC M Rosser zero (zeroF M) z ChurchZero h4 h3,
          symmetry,
          exact h7,
        }
      end,
    have step: ∀ (x:M), x ∈ Z_jhelper M → (∃ (u:M), u ∈ 𝕊 x) → 𝕊 x ∈ Z_jhelper M:= 
      begin
        intros x  h5 hsx,
        rw Z_jhelper_members at h5,
        cases h5 with hx h6,
        rw Z_jhelper_members,
        split,
        {
          exact successorF M x hx hsx,
        },
        {
          intros y z h7 h8,
          have h9:= ChurchFrege3 M y x hx h7,
          cases h9 with t h10,
          cases h10 with h11 h12,
          rw h12 at *,
          have h13:= ChurchFrege_domainrange M t x h11,
          cases h13 with ht hx2,
          have h15:= successorequation M ℕℕ (SG M) (SGFUNC M) (SGRel M) (SGMaps M) t ChurchZero ht (zeroN M),
          rw h15,
          have h16:= (RosserT M).mp Rosser (𝕊 x) (successorF M x hx hsx),
          repeat {rw h16 at h8},
          have h17:= (RosserT M).mp Rosser x hx,
          repeat {rw h17 at h6},
          have h18:= h6 t t h11 h11,
          rw h18,
          rw ApSG M t ht,
          have h19:= jFUNC M Rosser (𝕊 x) (successorF M x hx hsx) (S t) z h7 h8,
          exact h19, 
        }
      end,
    intros x hx,
    rw F_members at hx,
    have h5:= hx (Z_jhelper M) ⟨ base, step⟩,
    rw Z_jhelper_members at h5,
    exact h5.right,
  end

theorem RosserimpliesChurch: RosserCountingAxiom M → ChurchCountingAxiom M:=
  begin
    intro Rosser,
    unfold ChurchCountingAxiom,
    intros z hz,
    have h3:= xsmapsN M z hz ChurchZero (zeroN M),
    have h4:= Rosserimpliesitotal M Rosser z hz,
    cases h4 with x h5,
    cases h5 with hx h6,
    have h7:= jhelper M Rosser x hx z z h6,
    apply h7,
    have h8:= (RosserT M).mp Rosser x hx,
    repeat {rw h8},
    exact h6,
  end


#axioms_all  --This file is clean. 

