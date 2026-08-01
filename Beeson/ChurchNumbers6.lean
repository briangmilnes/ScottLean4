import ChurchNumbers5

variables (M:Type) [Model M] (a b x y z u v w X R W κ μ ℓ : M)
-- using ℓ where the source text has λ because you can't use λ for a variable.

open Model 

lemma successorrestricted: ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n → 
∀ (f:M), f = restrict (SG M)(LOOP n) → 
f ∈ FUNC ∧ Rel f ∧ maps M f (LOOP n)(LOOP n) ∧ injection M f (LOOP n):=
  assume hfinite k n hk hn hkn hskn f hf,
  begin
    have h11: f ∈ FUNC:=
      begin
        rw hf,
        have h12:= restriction M (SG M)(LOOP n),
        rw FUNC_members,
        intros x y z h,
        have h20:= h12 x y,
        have h21:= h12 x z,
        rw h21,
        rw h12 at h,
        cases h with h13 h14,
        have h22:= SGFUNC M,
        rw FUNC_members at h22,
        have h23:= h22 x y z,
        intro h24,
        cases h24 with h25 h26,
        exact h23 h13 h25,
      end,
    have h12: Rel f:=
      begin
        rw Rel_definition,
        intro z,
        rw hf,
        rw restrict_definition,
        intro h,
        rw intersection_axiom at h,
        cases h with h13 h14,
        rw product_axiom at h14,
        cases h14 with a h15,
        cases h15 with b h16,
        rcases h16 with ⟨ h17, h18, h19⟩,
        use a,
        use b,
        exact h19,
      end,
    have h13: maps M f (LOOP n)(LOOP n):=
      begin
        unfold maps,
        split,
        {
          exact h12,
        },
        {
          split,
          {
            intros x y h,
            cases h with h4 h5,
            rw hf at h5,
            rw restriction at h5,
            cases h5 with h6 h7,
            have h8:=SGMapsLoop M hfinite k n hk hn hkn hskn,
            unfold maps at h8,
            rcases h8 with ⟨ h9, h52,h53,h54⟩,
            have h55:= h54 x h7,
            cases h55 with p h56,
            cases h56 with h57 h58,
            have h59:= SGFUNC M,
            rw FUNC_members at h59,
            specialize h59 x y p,
            have h60:= h59 h6 h58,
            rw h60 at *,
            exact h57,
          },
          {
            split,
            {
              intros x y z h,
              rcases h with ⟨ h54, h55, h56⟩,
              rw hf at h55 h56,
              rw restriction at h55 h56,
              cases h56 with h57 h58,
              cases h55 with h59 h60,
              have h61:= SGFUNC M,
              rw FUNC_members at h61,
              specialize h61 x y z,
              exact h61 h59 h57,
            },
            {
              intros x hxloop,
              use S x,
              split,
              {
                have h55:= L1 M k n hk hn hkn hskn,
                exact h55.right x hxloop,
              },
              {
                rw hf,
                rw restriction,
                split,
                {
                  rw SG_members,
                  use x,
                  simp,
                  have h44:= member_subset M (LOOP n) ℕℕ x (LN M k n hk hn hkn hskn ) hxloop,
                  exact h44,
                },
                {
                  exact hxloop,
                }
              }
            }
          }
        }
      end,
    have h14: injection M f (LOOP n):=
      begin
        unfold injection,
        split,
        {
          unfold oneone,
          split,
          {
            exact h13,
          },
          {
            split,
            {
              intros x u y h,
              rcases h with ⟨ h2, h3, hxloop⟩,
              have h4:= looponeone M hfinite k n hk hn hkn hskn x u hxloop,
              rw hf at h2 h3,
              rw restriction at h2 h3,
              cases h3 with h5 huloop,
              cases h2 with h7 hyloop,
              have h8:= h4 huloop,
              rw SG_members at h5 h7,
              cases h7 with p h9,
              cases h5 with q h10,
              rw ordered_pair_equality at h9 h10,
              cases h9 with h11 h12,
              cases h10 with h13 h14,
              cases h11 with h15 h16,
              cases h13 with h17 h18,
              rw← h15 at *,
              rw← h17 at *,
              rw h16 at h18,
              exact h8 h18,
            },
            {
              intros x y h,
              cases h with h2 hyloop,
              rw hf at h2,
              rw restriction at h2,
              cases h2 with h3 hxloop,
              exact hxloop,
            }
          }
        },
        {
          split,
          {
            exact h12,
          },
          {
            split,
            {
              exact h11,
            },
            {
              split,
              {
                rw subset_definition,
                intros t h,
                rw domain_axiom at h,
                cases h with y h2,
                rw hf at h2,
                rw restriction at h2,
                cases h2 with h3 h4,
                exact h4,
                exact h12,
              },
              { 
                rw subset_definition,
                intros z h,
                rw hf at h,
                rw range_axiom at h,
                {
                  cases h with x h4,
                  rw restriction at h4,
                  cases h4 with h5 h6,
                  rw SG_members at h5,
                  cases h5 with p h6,
                  cases h6 with h7 hp,
                  rw ordered_pair_equality at h7,
                  cases h7 with h8 h9,
                  rw← h8 at *,
                  rw h9 at *,
                  have h10:= L1 M k n hk hn hkn hskn,
                  exact h10.right x h6,
                },
                {
                  rw Rel_definition, 
                  intros z h,
                  rw restrict_definition at h,
                  rw intersection_axiom at h,
                  cases h with h2 h3,
                  rw product_axiom at h3,
                  cases h3 with a h4,
                  cases h4 with b h5,
                  use a,
                  use b,
                  exact h5.right.right,
                }
              }
            }
          }
        }
      end,
    exact ⟨ h11, h12, h13, h14⟩, 
  end 

lemma successoronloop:  ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n → 
∀ (f:M), f = restrict (SG M)(LOOP n) → 
∀ (x:M), x ∈ LOOP n → ∀ (q:M), q ∈ ℕℕ → 
Ap (Ap q f) x = Ap (Ap q (SG M)) x:=
  assume hfinite k n hk hn hkn hskn f hf x hxloop,
  begin
    have base: ChurchZero ∈ Z_successoronloop M f x:=
      begin
        rw Z_successoronloop_members,
        split,
        {
          exact zeroN M,
        },
        {
          rw zeroAp,
          rw zeroAp,
        }
      end,
    have step: ∀ (q:M), q ∈ Z_successoronloop M f x → S q ∈ Z_successoronloop M f x:=
      begin
        intros q h2,
        rw Z_successoronloop_members at h2,
        cases h2 with hq h3,
        rw Z_successoronloop_members,
        split,
        {
          exact successorN M q hq,
        },
        {
          have h20:= successorequation M (LOOP n) (SG M) (SGFUNC M) (SGRel M) (SGMapsLoop M hfinite k n hk hn hkn hskn) q x hq hxloop,
          rw h20, 
          have h10:= successorequation M (LOOP n) f,
          have h100:= successorrestricted M hfinite k n hk hn hkn hskn f hf,
          rcases h100 with ⟨ h11, h12, h13,h14⟩,
          have h30:= h10 h11 h12 h13 q x hq hxloop,
          rw h30,
          rw h3,
          have h31:= xsmapsloop M hfinite k n hk hn hkn hskn q hq x hxloop,
          rw hf,
          rw full_extensionality,
          intro t,
          rw Ap_members,
          rw Ap_members,
          split,
          {
            intro h,
            cases h with y h32,
            use y,
            rw restriction at h32,
            cases h32 with h33 h34,
            exact ⟨ h33.left, h34⟩, 
          },
          {
            intro h,
            cases h with y h32,
            use y,
            rw restriction,
            split,
            {
              exact ⟨ h32.left, h31⟩,
            },
            {
              exact h32.right,
            }
          }
        }
      end,
    intros q hq,
    rw N_members at hq,
    have h6:= hq (Z_successoronloop M f x)⟨ base,step⟩,
    rw Z_successoronloop_members at h6,
    exact h6.right,
  end

lemma orderq: ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n → 
∃ (q:M), (∀(x:M), x ∈ LOOP n → Ap (Ap q (SG M)) x = x) ∧ 
∀ (r:M), r ∈ ℕℕ → r ≺ q → ¬ r = ChurchZero →  ¬ (∀(x:M), x ∈ LOOP n → Ap (Ap r (SG M)) x = x):=
  assume hfinite k n hk hn hkn hskn,
  begin
    set X:= Z_orderq M n with h50,
    have h80:= finitedecidable M ℕℕ hfinite,
    rw decidable_members at h80,
    have h82: X ⊆ ℕℕ:=
      begin
        rw subset_definition,
        intros t h,
        rw h50 at h,
        rw Z_orderq_members at h,
        rcases h with ⟨ h83, h84, h85⟩,
        exact h83,
      end,
    have h81:= separablefinite M ℕℕ hfinite X h82,
    have h83: X ∈ FINITE M:= 
      begin
        apply h81,
        unfold separable_subset,
        split,
        {
          exact h82,
        },
        {
          rw full_extensionality,
          intro t,
          rw binary_union_axiom,
          rw minus_members,
          split,
          {
            intro h,
            rw h50,
            rw Z_orderq_members,
            have h85: (Ap (Ap t (SG M)) n) ∈ ℕℕ:=
              begin
                have hnloop := (L1 M k n hk hn hkn hskn).left,
                have h100:= xsmapsloop M hfinite k n hk hn hkn hskn t h n hnloop,
                have h102:= member_subset M (LOOP n) ℕℕ (Ap (Ap t (SG M)) n)  (LN M k n hk hn hkn hskn) h100,
                exact h102,
              end,
            have h84:= h80 (Ap (Ap t (SG M)) n) n ⟨ h85, hn⟩,
            have h200:= h80 t ChurchZero ⟨ h, zeroN M⟩,
            cases h84 with h86 h87,
            { 
              cases h200 with h201 h202,
              {
                right,
                split,
                {
                  exact h,
                },
                {
                  intro h2,
                  rcases h2 with ⟨ h3, h4, h5⟩, 
                  contradiction,
                }
              },
              {
                left, 
                exact ⟨ h, h202, h86⟩, 
              }
            },
            { 
              right,
              split,
              {
                exact h,
              },
              { 
                intro h34,
                rcases h34 with ⟨ h35, h36, h37⟩,
                contradiction,
              }
            },
          },
          {
            intro h,
            cases h with h90 h91,
            {
              exact member_subset M X ℕℕ t h82 h90,
            },
            {
              exact h91.left,
            }
          }
        }
      end,
    have h84:= mexists M hfinite k n hk hn hkn hskn,
    cases h84 with m h85,
    rcases h85 with ⟨ hm, h86, h87⟩,
    have h40:= knm M hfinite k n hk hn hkn hskn m hm h86,
    have h88:= annihilation M n m hn hm h40,
    set f:= restrict (SG M)(LOOP n) with h70,
    have h71: ∀ (u:M), u ∈ LOOP n → Ap f u = Ap (SG M) u:=
      begin
        intros u hloopu,
        rw full_extensionality,
        intro t,
        rw Ap_members, 
        rw Ap_members,
        split,
        { 
          intro h,
          cases h with y h91,
          use y,
          rw h70 at h91,
          rw restriction at h91,
          cases h91 with h92 h93,
          exact ⟨ h92.left, h93⟩,
        },
        {
          intro h,
          cases h with y h91,
          use y,
          rw h70,
          rw restriction,
          cases h91 with h92 h93,
          exact ⟨ ⟨ h92, hloopu⟩, h93⟩,
        }
      end,
    have h89: m ∈ X:=
      begin
        have h300: ¬ m = ChurchZero:=
          begin 
            intro h301,
            rw h301 at *,
            have h302: k ∈ ℕℕ :=
              begin 
                have h303:= SN M,
                exact member_subset M STEM ℕℕ k h303 hk,
              end,
            rw ChurchZero_equation k h302 at h86,
            contradiction,
          end,
        rw h50,
        rw Z_orderq_members,
        have h51:= h88 (LOOP n) f,
        have h52:= successorrestricted M hfinite k n hk hn hkn hskn f h70,
        rcases h52 with ⟨ h53, h54, h55, h56⟩,
        have hnloop := (L1 M k n hk hn hkn hskn).left,
        have h57:= h51 h56 n hnloop,
        have h58:= successoronloop M hfinite k n hk hn hkn hskn f h70 n hnloop m hm,
        rw h57 at h58,
        split,
        {
          exact hm,
        },
        { 
          rw sym at h58,
          exact ⟨ h300, h58⟩,
        }
      end,
    have h72: ¬ X = Λ:=
      begin
        intro h,
        rw h at h89,
        have h72:= emptyset_axiom m,
        contradiction,
      end,
    have h90:= leastelement M hfinite k n hk hn hkn hskn X h83 h82 h72,
    cases h90 with q h91,
    cases h91 with h92 h93,
    use q,
    split,
    {
      rw h50 at h92,
      rw Z_orderq_members at h92,
      rcases h92 with ⟨ hq, hq0, h95⟩,
      have h100:= orderq_helper M hfinite k n hk hn hkn hskn q hq hq0 h95,
      exact h100,
    },
    {
      intros r hr hrq hq0 h,
      have h100:= h93 r,
      have h101: q ∈ ℕℕ:= member_subset M X ℕℕ q h82 h92,
      have h110: r ∈ X:=
        begin
          rw h50,
          rw Z_orderq_members,
          split,
          {
            exact hr,
          },
          {
            split,
            {
              exact hq0,
            },
            {
              have hnloop := L1 M k n hk hn hkn hskn, 
              exact h n hnloop.left,
            }
          }
        end,
      have h111 := h100 h110,
      rw prec_definition at hrq,
      cases hrq with h112 h113,
      rw sym at h113,
      have h114:= prectrichotomy2 M hfinite k n hk hn hkn hskn r hr q h101 h113,
      exact h114 ⟨ h111,h112⟩, 
    }
  end

lemma kplusm: ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n → 
∀ (x:M), x ∈ ℕℕ → ¬ x = ChurchZero → n = n ⊕  x → n = k ⊕  x:=
  assume hfinite k n hk hn hkn hskn x hx h6 h3,
  begin
    have h1:= L1 M k n hk hn hkn hskn,
    cases h1 with hloopn h2,
    have h5:= h2 n hloopn,
    have h4: S n = S (n ⊕ x):= 
      begin 
        rw←  h3,
      end,
    have h7:= predecessor M x hx h6,
    cases h7 with r h8,
    cases h8 with h9 h10,
    have h20:= looponeone M hfinite k n hk hn hkn hskn n (k ⊕ x) hloopn,
    rw←  ChurchAddition_equation n x hn hx at h4,
    rw ChurchSuccessorShift M x hx n hn at h4,
    have h21: S n = S k ⊕ x:=
      begin
        rw hskn,
        exact h4,
      end,
    have h30: k ∈ ℕℕ:= member_subset M STEM ℕℕ k (SN M) hk,
    rw← ChurchSuccessorShift M x hx k h30 at h21,
    rw ChurchAddition_equation k x h30 hx  at h21,
    have hloopk := h5,
    rw← hskn at hloopk,
    have h22: k ⊕ x = k ⊕ S r:=
      begin
        rw h10,
      end,
    rw ChurchSuccessorShift M r h9 k h30 at h22,
    have h23:= additionmapsloop M hfinite k n hk hn hkn hskn (S k) hloopk r h9,
    rw← h22 at h23,
    exact h20 h23 h21,
  end

theorem orderm:  ℕℕ ∈ FINITE M →  ∀ (k n:M),
k ∈ STEM → n ∈ ℕℕ → ¬ k = n → S k = S n → 
( ∀ (x:M), x ∈ ℕℕ →  Ap ( Ap x (SG M)) ChurchZero = x) →
∀ (m:M), m ∈ ℕℕ  → n = k ⊕ m → 
(∀ (r:M), r ∈ ℕℕ  → n = k ⊕ r → m ≼ r) → 
∀ (q:M), q ∈ ℕℕ → ¬ q = ChurchZero → Ap   (Ap q (SG M)) n  = n → m ≼ q:=
  assume hfinite k n hk hn hkn hskn ChurchCountingAxiom,
  begin
    intros m hm hnkm hmin q hq hqnzero h3,
    have h4:=loopcounting M hfinite k n hk hn hkn hskn ChurchCountingAxiom,
    have h5:= h4 q hq,   --  qSn = n ⊕ q
    have h6: n = n ⊕ q:=
      begin
        rw h3 at h5,
        exact h5,
      end,
    have h7:= kplusm M hfinite k n hk hn hkn hskn q hq hqnzero h6, 
    exact hmin q hq h7,
  end



lemma stemseparable_helper: ℕℕ ∈ FINITE M → 
∀ (x:M), x ∈ STEM → (∃ (y:M), y ∈ ℕℕ ∧ S y = S x ∧ ¬ x = y) ∨ ¬ (∃ (y:M), y ∈ ℕℕ ∧ S y = S x ∧ ¬ x = y):=
  assume hfinite x h2,
  begin
    have h1:= SN M,
    have hx:= member_subset M STEM ℕℕ x h1 h2,
    set R:= Z_stemseparable_helper M with h50,
    have h3:= boundedquantification M R ℕℕ ℕℕ,
    have h4: ∀ (u z:M), ‹ u, z › ∈ R ↔ S u = S z ∧ u ∈ ℕℕ  ∧ z ∈ ℕℕ ∧ ¬ z = u:=
      begin
        intros u z,
        rw h50,
        rw Z_stemseparable_helper_members,
        split,
        {
          intros h,
          cases h with x h4,
          cases h4 with y h5,
          rcases h5 with ⟨ h6, h7, h8,h9, h12⟩, 
          rw ordered_pair_equality at h6,
          cases h6 with h10 h11,
          rw← h10 at *,
          rw← h11 at *,
          exact ⟨ h7, h8, h9, h12⟩, 
        },
        {
          intros h,
          rcases h with ⟨ h4, h5, h6, h7⟩,
          use u, use z,
          simp,
          exact ⟨ h4, h5, h6, h7⟩, 
        }
      end,
    have h5: (∃(y : M), y ∈ ℕℕ ∧ S y = S x ∧ ¬ x = y) ↔ (∃ (y : M), y ∈ ℕℕ ∧  ‹ y,x ›  ∈ R) :=
      begin
        split,
        {
          intros h,
          cases h with y h6,
          use y,
          rw h4 y x,
          rcases h6 with ⟨ h7, h8, h9⟩,
          exact ⟨ h7, h8, h7, hx, h9⟩, 
        },
        {
          intros h,
          cases h with y h6,
          use y,
          cases h6 with h7 h8,
          rw h4 y x at h8,
          rcases h8 with ⟨ h9, h10, h11, h12⟩,
          exact ⟨ h10, h9, h12⟩, 
        }
      end,
    rw h5,
    have h80:= finitedecidable M ℕℕ hfinite,
    apply h3,
    {
      repeat{split},
      {
        exact hfinite,
      },
      {
        exact my_subset_reflexive M ℕℕ,
      },
      {
        exact h80,
      },
      {
        intros u z hu hz,
        rw h50,
        rw Z_stemseparable_helper_members,
        have h20:= successorN M u hu,
        have h21:= successorN M z hz,
        rw decidable_members at h80,
        have h81:= h80 (S u)(S z) ⟨ h20, h21⟩,
        have h82:= h80 u z ⟨ hu, hz⟩, 
        cases h81 with h22 h23,
        {
          cases h82 with h30 h31,
          { 
            right,
            intro h32,
            cases h32 with x h33,
            cases h33 with y h34,
            rw ordered_pair_equality at h34,
            rcases h34 with ⟨ h35, h36, h37, h38, h39⟩,
            cases h35 with h40 h41,
            rw← h40 at *,
            rw← h41 at *,
            rw sym at h30,
            contradiction,
          },
          {
            left,
            use u, use z,
            simp,
            rw sym at h31,
            exact ⟨ h22, hu, hz, h31⟩,
          }
        },
        {   
          right,
          intro h,
          cases h with x h10,
          cases h10 with y h11,
          rcases h11 with ⟨ h12, h13, h14, h15⟩,
          rw ordered_pair_equality at h12,
          cases h12 with h16 h17,
          rw h16 at *,
          rw h17 at *,
          contradiction,
        }
      }
    },
    { 
      exact hx,
    }
  end 

lemma stemseparable: ℕℕ ∈ FINITE M → ∀ (x:M), x ∈ ℕℕ → x ∈ STEM ∨ ¬ x ∈ STEM:=
  assume hfinite,
  begin
    have h3:= S1 M,
    cases h3 with h20 h21,
    have base: ChurchZero ∈ Z_stemseparable M:=
      begin
        rw Z_stemseparable_members, 
        split,
        {
          exact zeroN M,
        },
        { 
          left,
          exact h20,
        }
      end,
    have step: ∀ (x:M), x ∈ Z_stemseparable M → S x ∈ Z_stemseparable M:=
      assume x,
      begin
        intros h,
        rw Z_stemseparable_members at h,
        rw Z_stemseparable_members,
        cases h with hx h4,
        split,
        {
          exact successorN M x hx,
        },
        {
          cases h4 with h5 h6,
          {
            have h7:= stemseparable_helper M hfinite x h5,
            cases h7 with h1a h1b,
            {
              cases h1a with y h8,
              rcases h8 with ⟨ h9, h10, h11⟩,
              have h12:= Soneone M x y h5,
              right,
              intro h13,
              rw sym at h10,
              have h14:= h12 h13 h9 h10,
              contradiction,
            },
            { 
              left,
              have h30:= (S1 M).right x hx h5,
              apply h30,
              have h80:= finitedecidable M ℕℕ hfinite,
              rw decidable_members at h80,
              intros v hv hxv,
              have h81:= h80 x v ⟨ hx,hv⟩,
              cases h81 with h82 h83,
              {
                exact h82,
              },
              {
                have false:=
                  begin
                    apply h1b,
                    use v,
                    rw sym at hxv,
                    exact ⟨ hv, hxv, h83⟩,
                  end,
                contradiction,
              }
            }
          },
          {
            right,
            intro h,
            have h30:= Spred M x hx h,
            contradiction,
          }
        }
      end,
    intros x hx,
    rw N_members at hx,
    have h10:= hx (Z_stemseparable M) ⟨ base, step⟩, 
    rw Z_stemseparable_members at h10,
    exact h10.right,
  end
 

lemma kinstem: ℕℕ ∈ FINITE M → 
∃ (k n:M), k ∈ ℕℕ ∧ n ∈ ℕℕ ∧ ¬ k = n ∧ S k = S n ∧ k ∈ STEM:=
  assume hfinite, 
  begin 
    have h5:= stemseparable M hfinite,
    have h6:= separablefinite M ℕℕ hfinite STEM (SN M),
    have h7: STEM ∈ FINITE M:=
      begin
        apply h6,
        unfold separable_subset,
        split,
        {
          exact (SN M),
        },
        { 
          rw full_extensionality,
          intro t,
          split,
          { 
            rw binary_union_axiom,
            rw minus_members,
            intro ht,
            have h7:= h5 t ht,
            cases h7 with h8 h9,
            {
              left, 
              exact h8,
            },
            {
              right,
              exact ⟨ ht, h9⟩,
            }
          },
          {
            rw binary_union_axiom,
            rw minus_members,
            intro h,
            cases h with h20 h21,
            {
              have h22:= SN M,
              exact member_subset M STEM ℕℕ t h22 h20,
            },
            {
              exact h21.left,
            }
          }
        }
      end,
    set R:= R_kinstem_helper M with h50,
    have h8:= boundedquantification M R ℕℕ ℕℕ ,
    set Z:= Z_kinstem_helper M with h51,
    have h11: Z ⊆ ℕℕ:=
      begin
        rw subset_definition,
        intros t ht,
        rw Z_kinstem_helper_members at ht,
        exact ht.left,
      end,
    have h80:= finitedecidable M ℕℕ hfinite,
    rw decidable_members at h80,
    have h12:(ℕℕ ∈ FINITE M ∧ ℕℕ ⊆ ℕℕ ∧ ℕℕ ∈ DECIDABLE M ∧ ∀ (u z : M), u ∈ ℕℕ → z ∈ ℕℕ →  ‹ u,z›  ∈ R ∨ ¬ ‹u,z ›  ∈ R):=
      begin
        repeat{split},
        {
          exact hfinite,
        },
        {
          exact my_subset_reflexive M ℕℕ,
        },
        {
          exact finitedecidable M ℕℕ hfinite,
        },
        {
          intros u z hu hz,
          rw h50,
          rw R_kinstem_helper_members,
          have h13:= h80 u z ⟨ hu, hz⟩,
          have h14:= h80 (S u) (S z) ⟨ successorN M u hu, successorN M z hz⟩, 
          cases h13 with h15 h16,
          {
            right,
            intro h,
            cases h with x h17,
            cases h17 with y h18,
            rcases h18 with ⟨ h19, h20, h21, h22, h23, h24⟩,
            rw ordered_pair_equality at h19,
            cases h19 with h25 h26,
            rw← h25 at *,
            rw← h26 at *,
            -- rw sym at h15,
            contradiction,
          },
          {
            cases h14 with h17 h18,
            { 
              have h19:= stemseparable M hfinite z hz,
              cases h19 with h20 h21,
              {
                left,
                use z, use u,
                simp,
                rw sym at h17,
                exact ⟨ h17, hz, hu, h16, h20⟩,
              },
              {
                right,
                intro h,
                cases h with x h21,
                cases h21 with y h22,
                rcases h22 with ⟨ h23, h24, h25, h26, h27, h28⟩,
                rw ordered_pair_equality at h23,
                cases h23 with h29 h30,
                rw← h29 at *,
                rw← h30 at *,
                contradiction,
              }
            },
            {
              right,
              intro h,
              cases h with x h19,
              cases h19 with y h20,
              rcases h20 with ⟨ h21, h22, h23, h24, h25, h26⟩,
              rw ordered_pair_equality at h21,
              cases h21 with h34 h33,
              rw← h34 at *,
              rw← h33 at *, 
              rw sym at h22,
              contradiction,
            }
          }
        }
      end,
    have h20:= h8 h12,
    have h19: Z ∈ FINITE M:=
      begin
        have h10:= separablefinite M ℕℕ hfinite Z h11,
        apply h10,
        unfold separable_subset,
        split,
        {
          exact h11,
        },
        {
          rw full_extensionality,
          intro t,
          rw binary_union_axiom,
          rw minus_members,
          split,
          {
            intro ht,
            rw h51,
            rw Z_kinstem_helper_members,
            rw← h50,
            have h22:= h20 t ht,
            cases h22 with h23 h24,
            {
              left,
              exact ⟨ ht, h23⟩,
            },
            {
              right,
              split,
              {
                exact ht,
              },
              {
                intro h,
                cases h with h25 h26,
                contradiction,
              }
            }
          },
          {
            intro h,
            cases h with h30 h31,
            {
              exact member_subset M Z ℕℕ t h11 h30,
            },
            {
              exact h31.left,
            }
          }
        }
      end,
    have h30:= empty_or_inhabited M Z h19,
    cases h30 with h31 h32,
    {
      have h33: (ℕℕ:M) ⊆ STEM:=
        begin
          have base: ChurchZero ∈ STEM:= (S1 M).left,
          have step: ∀ (x:M), x ∈ STEM → S x ∈ STEM:=
            begin
              intros x hxstem,
              have hx:= member_subset M STEM ℕℕ x (SN M) hxstem,
              have h34:= (S1 M).right x hx hxstem,
              apply h34,
              intros v hv hxv,
              have h35:= h80 x v ⟨ hx, hv⟩, 
              cases h35 with h36 h37,
              {
                exact h36,
              },
              {
                have h38: x ∈ Z:=
                  begin
                    rw h51,
                    rw Z_kinstem_helper_members,
                    split,
                    {
                      exact hx,
                    },
                    {
                      use v,
                      split,
                      {
                        exact hv,
                      },
                      {
                        rw R_kinstem_helper_members,
                        use x, use v,
                        simp,
                        rw sym at h37,
                        exact ⟨ hxv, hx, hv, h37, hxstem⟩,
                      }
                    }
                  end,
                rw h31 at h38,
                have h39:= emptyset_axiom x,
                contradiction,
              }
            end,
          rw subset_definition,
          intros t ht,
          rw N_members at ht,
          have h34:= ht STEM ⟨ base, step⟩,
          exact h34,
        end,
      have h34:= (SN M),
      have h35: (ℕℕ:M) = STEM:=
        begin
          rw full_extensionality,
          intros t,
          split,
          {
            intro ht,
            exact member_subset M ℕℕ STEM t h33 ht,
          },
          {
            intro ht,
            exact member_subset M STEM ℕℕ t h34 ht,
          }
        end,
      have h36:= Soneone M,
      simp_rw← h35 at h36,
      have h37: infinite M ℕℕ:=
        begin
          unfold infinite,
          use ℕℕ - single ChurchZero,
          split,
          {
            rw subset_definition,
            intros t h,
            rw minus_members at h,
            exact h.left,
          },
          {
            split,
            {
              intro h,
              rw full_extensionality at h,
              specialize h ChurchZero,
              rw minus_members at h,
              rw singleton1 at h,
              cases h with h60 h61,
              have h62:= h60 (zeroN M),
              cases h62 with h63 h64,
              contradiction,
            },
            {
              unfold similar,
              use (SG M),
              unfold similarity,
              split,
              {
                unfold oneone,
                repeat{split},
                {
                  exact SGRel M,
                },
                {
                  intros x y h,
                  cases h with h37 h38,
                  rw SG_members at h38,
                  cases h38 with p h39,
                  cases h39 with h60 hp,
                  rw ordered_pair_equality at h60,
                  cases h60 with h61 h62,
                  rw h61 at *,
                  rw h62 at *,
                  rw minus_members,
                  rw singleton1,
                  split,
                  {
                    exact successorN M p h37,
                  },
                  {
                    exact successoromitszero M p h37,
                  }
                },
                {
                  intros x y z h,
                  rcases h with ⟨ hx, hxy, hxz⟩,
                  rw SG_members at hxy hxz,
                  cases hxz with p h37,
                  cases hxy with q h38,
                  cases h38 with h60 hq,
                  cases h37 with h62 hp,
                  rw ordered_pair_equality at h60 h62,
                  cases h62 with h63 h64,
                  cases h60 with h65 h66,
                  rw← h63 at *,
                  rw← h65 at *,
                  rw h64,
                  rw h66,
                },
                {
                  intros t ht,
                  use  (S t),
                  rw SG_members,
                  split,
                  {
                    rw minus_members,
                    rw singleton1,
                    split,
                    {
                      exact successorN M t ht,
                    },
                    {
                      exact successoromitszero M t ht,
                    }
                  },
                  {
                    use t,
                    simp,
                    exact ht,
                  }
                },
                {
                  intros x u y h,
                  rcases h with ⟨ h60, h61, hx⟩,
                  rw SG_members at h60 h61,
                  cases h61 with p h62,
                  cases h60 with q h63,
                  rw ordered_pair_equality at h62 h63,
                  cases h63 with h64 h65,
                  cases h62 with h66 h67,
                  cases h64 with h68 h69,
                  cases h66 with h70 h71,
                  rw h71 at *,
                  rw h68 at *,
                  rw h70 at *,
                  symmetry,
                  have h72:= h36 p q h67 (successorN M p h67) hx h69,
                  exact h72,
                },
                {
                  intros x y h,
                  cases h with h60 h61,
                  rw SG_members at h60,
                  cases h60 with p h62,
                  cases h62 with h63 hp,
                  rw ordered_pair_equality at h63,
                  cases h63 with h64 h65,
                  rw h64 at *,
                  rw h64 at *,
                  exact hp,
                }
              },
              {
                unfold onto,
                intros y h,
                rw minus_members at h,
                rw singleton1 at h,
                cases h with hy h61,
                have h62:= predecessor M y hy h61,
                cases h62 with p h63,
                use p,
                rw SG_members,
                cases h63 with hp h64,
                split,
                {
                  exact hp,
                },
                {
                  use p,
                  rw h64,
                  simp,
                  exact hp,
                }
              }
            }
          }
        end,
      have h47:= infiniteimpliesnotfinite M ℕℕ h37,
      contradiction,
    },
    {
      cases h32 with x h33,
      rw h51 at h33,
      rw Z_kinstem_helper_members at h33,
      cases h33 with hx h34,
      cases h34 with y h35,
      cases h35 with hy h36,
      rw R_kinstem_helper_members at h36,
      cases h36 with k h37,
      cases h37 with n h38,
      cases h38 with h39 h60,
      rw ordered_pair_equality at h39,
      cases h39 with h61 h62,
      rw h61 at *,
      rw h62 at *,
      use k, use n,
      rcases h60 with ⟨ h63, h64, h65, h66, h67⟩,
      rw sym at h66,
      exact ⟨ h64, h65, h66, h63, h67⟩,
    }
  end

#axioms_all 
