import inf18
variables (M:Type) [Model M] (a b x y z u v w X R W κ μ ℓ : M)

open Model 

lemma TmlessthanM:
  ∀ (m:M), MAXIMAL M(m) →   𝕋 M m < m:=
  begin
    intros m h,
    unfold MAXIMAL at h,
    cases h with hm h2,
    have h4:= Tfinite M m hm,
    have h3:= h2 (𝕋 M m) h4,
    have h5: exp M (𝕋 M m) ∈ 𝔽:=
      expTinF M m hm, 
    have h5copy:= h5,
    have h6: ∃ (u:M), u ∈ exp M ( 𝕋 M m):=
      expT_inhabited M m hm,
    have h7: 𝕋 M m < exp M ( 𝕋 M m):=
      mlessthanexpm M (𝕋 M m) h4 h6,
    have h7copy:= h7,
    have h8:= (letolessthan M (𝕋 M m) m h4 hm).1 h3,
    cases h8 with h9 h10,
      exact h9,
      rw h10,
      rw h10 at h7,
      rw h10 at h5,
      have h11:=xnotlessthanx M (exp M m) h5,
      have h12:= h2 (exp M m) h5,
      have h13:=
        le_transitive3 M m (𝕋 M m) (exp M (𝕋 M m)) hm h4 h5copy,
      rw h10 at h13,
      have h14:= le_reflexive M m hm,
      have h15:= h13 h14 h7,
      have h16:= h2 (exp M m) h5,
      have h17:= le_transitive2 M m (exp M m) m hm h5 hm h15 h16,
      exact h17,
  end

lemma notnotfinitesubsetU: ∀ (m x U:M), (MAXIMAL M m → x ∈ FINITE M → U ∈ m → ¬¬ x ⊆ U):=
  assume m x U,
  begin
    intros hmax hx hu,
    have hmaxcopy:= hmax,
    unfold MAXIMAL at hmax,
    cases hmax with hm h4,
    have h6:= maximalimpliesnosuccessor M m hmaxcopy,
    have h5:= unenlargeable M m U hm h6 hu,
    have h7:= finiteDNS M U x hx,
    have h8:= λx,λq,h5 x,
    have h9:= h7 h8,
    rw subset_definition,
    exact h9,
  end

lemma NcSingleton: ∀(a:M), Nc M (single a) = one:=
  assume a,
  begin
    apply extensionality_axiom (Nc M (single a)) one,
    intros x,
    split,
    {
      intro h,
      rw one_members,
      have h3:= xinNcx M (single a),
      rw Nc_members M at h,
      have h4:= similar_to_singleton M x a h,
      exact h4,
    },
    {
      intros h,
      rw Nc_members,
      rw one_members at h,
      cases h with b h6,
      rw h6,
      have h7:= similar_singletons M,
      exact h7 b a,
    }
  end

-- following lemma is not actually used
lemma ucsinssc2: ∀ (x:M), x ∈ FINITE M → USC x ∈ SSC (SSC x):=
  assume x hfinite,
  begin
    have h50:= finitedecidable M x hfinite,
    rw ssc_definition,
    split,
    { 
      rw subset_definition,
      intros z h,
      rw ssc_members,
      rw usc at h,
      cases h with a h4,
      cases h4 with h5 h6,
      rw h6,
      split,
      {
        rw subset_definition,
        intros q hq,
        rw singleton1 at hq,
        rw hq,
        exact h5,
      },
      {
        intros y h9,
        rw singleton1,
        have h51:= h50,
        rw decidable_members at h51,
        exact  h51 y a ⟨ h9, h5 ⟩,
      }
    },
    -- That shows USC x ⊆ SSC x.
    -- We must still show it is a separable subset.
    { 
      apply extensionality_axiom,
      intro p,
      rw binary_union_axiom,
      split,
      {
        intros h,
        --next show p is finite
        have hp:= h,
        rw ssc_members at h,
        cases h with h31 h32,
        have h30:= separablefinite M x hfinite p h31,
        unfold separable_subset at h30,
        have h33: p ∈ FINITE M:=
          begin
            apply h30,
            have h34:= extensionality_axiom x (p ∪ x-p),
            split,
            { 
              exact h31,
            },
            {
              apply h34,
              intros t,
              have h35:= h32 t,
              split,
              {
                intros ht,
                have h36:= h35 ht,
                rw binary_union_axiom,
                rw minus_members,
                cases h36 with h37 h38,
                {
                  left,
                  exact h37,
                },
                {
                  right,
                  exact ⟨ ht, h38 ⟩,
                }
              },
              {
                intros h40,
                rw binary_union_axiom at h40,
                rw minus_members at h40,
                cases h40 with h41 h42,
                {
                  have h43:= member_subset M p x t h31 h41,
                  exact h43,
                },
                {
                  exact h42.1,
                }
              }
            }
          end,
        have h60:= finitecardinals3 M p h33,
        have h61:= oneF M,
        have h62:= FregeNdecidable M,
        rw decidable_members at h62,
        have h63:= h62 (Nc M p) one ⟨ h60, h61 ⟩,
        cases h63 with h64 h65,
        {
          left,
          rw usc,
          have h65:= one_members M,
          have h66:= xinNcx M p,
          rw h64 at h66,
          rw h65 at h66,
          cases h66 with a h67,
          use a,
          rw← h67,
          simp,
          have h68:= member_subset M p x a h31,
          apply h68,
          rw h67,
          rw singleton1,
        },
        {
          right,
          rw minus_members, 
          split,
          {
            exact hp,
          },
          {
            intros h70,
            apply h65,
            rw usc at h70,
            cases h70 with a h71,
            cases h71 with h72 h73,
            rw h73,
            exact NcSingleton M a,
          }
        }
      },
      {
        intros h80,
        cases h80 with h81 h82,
        {
          have h83:= usc_subset_ssc M x h50,
          have h84:= member_subset M (USC x) (SSC x) p h83 h81,
          exact h84,
        },
        {
          rw minus_members at h82,
          exact h82.1,
        }
      }
    }
  end

lemma notnotssc1:  ∀(m U:M), MAXIMAL M m → U ∈ m → ∀ (x:M), x ∈ FINITE M → ¬¬ x ⊆ U:=
  assume m U hmaximal hU,
  begin
    have hmax:= hmaximal;
    unfold MAXIMAL at hmax,
    cases hmax with hm h1,
    have h2:= unenlargeable2 M m hm h1 U hU,
    intros x hx,
    rw subset_definition,
    apply finiteDNS,
    {
      exact hx,
    },
    {
      intros t ht,
      exact h2 t,
    }
  end


lemma notnotssc2:  ∀(m U:M), MAXIMAL M m → U ∈ m → ∀ (x:M), x ∈ FINITE M → ¬¬ x ∈ SSC U:=
  assume m U hmaximal hU x hx,
  begin
    have hmax:=hmaximal;
    unfold MAXIMAL at hmax,
    cases hmax with hm h7,
    have hUfinite:= finitecardinals1 M m U hm hU,
    have h20:= notnotssc1 M m U hmaximal hU x hx,
    have h30: x ⊆ U → ∀ (q:M),q ∈ U → ¬¬(q∈ x ∨ ¬ q ∈ x):=
      begin
        intros hx q hq,
        have h31:= notnotLEM,
        exact h31 (q ∈ x),
      end,
    have h32: x ⊆ U → ¬¬∀ (q:M),q ∈ U → (q∈ x ∨ ¬ q ∈ x):=
      begin
        intros h33,
        have h34:= h30 h33,
        have h35:= finiteDNS M,
        have h36:= h35 (Z_notnotssc2 M x),
        simp_rw Z_notnotssc2_members at h36,
        have h37:= h36 U hUfinite,
        apply h37,
        exact h34,
      end,
    have h100:= notnot_imp (x ⊆ U) (∀ (q : M), q ∈ U → ¬¬(q ∈ x ∨ ¬q ∈ x)) h30,
    have h38:= h100 h20,
    have h40: x ⊆ U → ¬¬ (x ⊆ U ∧ ∀ (q:M), q ∈ U →(q ∈ x ∨ ¬ q ∈ x)):=
      begin
        intros h41,
        rw notnot_and,
        split,
        {
          exact h20,
        },
        {
          have h43:= h32 h41,
          exact h43,
        }
      end,
    have h41:= notnot_imp (x ⊆ U)(¬¬∀ (q : M),q∈ U → (q ∈ x ∨ ¬q ∈ x)) h32 h20,
    rw triplenegation at h41,
    have h42: ∀ (q:M),q ∈ U → ¬¬(q ∈ x ∨ q ∈ U-x):=
      begin
        intros q hq h43,
        have h44:= not_orNF (q ∈ x) (q ∈ U-x),
        rw h44 at h43,
        cases h43 with h45 h46,
        rw minus_members at h46,
        apply h46,
        exact ⟨ hq, h45⟩,
      end,
    
    have h103: ¬¬ x ⊆ U ∧   ¬¬∀(q:M),q ∈ U → q ∈ x ∨ ¬ q ∈ x:=
      begin
        exact ⟨h20,h41⟩,
      end,
    have h104:= notnot_and (x ⊆ U)(∀(q:M),q ∈ U → (q ∈ x ∨ ¬ q ∈ x)), 
    have h105:= h104.2 h103, 
    have h110:(∀(q:M),(q ∈ U → q∈ x ∨ ¬ q ∈ x)) ↔
              (∀(q:M),(q ∈ U → q ∈x ∨ q ∈ U-x)):=
      begin
        split,
        {
          intro h111,
          intros q hq,
          have h112:= h111 q hq,
          cases h112 with h113 h114,
          {
            left,
            exact h113,
          },
          {
            right,
            rw minus_members,
            exact ⟨ hq, h114⟩,
          }
        },
        {
          intros h115 q hq,
          have h116:= h115 q hq,
          cases h116 with h117 h118,
          {
            left, 
            exact h117,
          },
          {
            rw minus_members at h118,
            right,
            exact h118.2,
          }
        }
      end,
    have h200:= double_negate ((∀(q:M),(q ∈ U → q∈ x ∨ ¬ q ∈ x))↔
              (∀(q:M),(q ∈ U → q ∈x ∨ q ∈ U-x))) h110,
    have h210:= notnot_iff_2way (∀ (q : M), q ∈ U → q ∈ x ∨ ¬q ∈ x)
              (∀ (q : M), q ∈ U → q ∈ x ∨ q ∈ U - x),
    have h211:= h210.1 h200,
    have h212:= h211.1 h41,
    have h213:= h42,
    have h214:= binary_union_axiom x (U-x),
    have h215: ∀ (q : M), q ∈ U → ¬¬(q ∈ x ∪ U - x):=
      begin
        intros q hq,
        have h216:= h213 q hq,
        have h217:= h214 q,
        have h218:= double_negate (q ∈ x ∪ U - x ↔ q ∈ x ∨ q ∈ U - x) h217,
        have h219:= notnot_iff_2way (q ∈ x ∪ U - x) ( q ∈ x ∨ q ∈ U - x),
        rw h219 at h218,
        exact h218.2 h216,
      end,
    have h220: x ⊆ U → x ∪ (U-x) ∈ FINITE M:=
      begin
        assume h222,
        have h221:= finitedif M U x hUfinite hx h222,
        have h223: x ∩ U-x = Λ:=
          begin
            rw full_extensionality,
            intro t,
            split,
            {
              intros h224,
              have h225:=intersection_axiom x (U-x) t,
              have h226:= h225.1 h224,
              rw minus_members at h226,
              cases h226 with h227 h228,
              have h229:= h228.2 h227,
              contradiction,
            },
            {
              intros h230,
              have h231:= emptyset_axiom t,
              contradiction,
            }
          end,
        have h232:= union M x (U-x) hx h221 h223,
        exact h232,
      end,
    have h225:= finiteDNS M (x ∪ (U-x)) U hUfinite h215,
    have h226: ¬¬(U ⊆ x ∪ (U-x)):=
      begin
        rw subset_definition,
        exact h225,
      end,
    have h230: x ⊆ U → x ∪ (U-x) ⊆ U:=
      begin
        intros hxU,
        have hxUcopy:= hxU,
        rw subset_definition at hxU,
        rw subset_definition,
        intros q h231,
        rw binary_union_axiom at h231,
        cases h231 with h232 h233,
        {
          have h234:= member_subset M x U q hxUcopy h232,
          exact h234,
        },
        {
          rw minus_members at h233,
          exact h233.1,
        }
      end,
    have h236:= notnot_imp (x ⊆ U) (x ∪ U - x ⊆ U) h230,
    have h237:= h236 h20,
    have h238: (¬¬U ⊆ x ∪ U - x)∧ (¬¬x ∪ U - x ⊆ U):= ⟨ h226, h237⟩,
    have h239:= notnot_and (U ⊆ x ∪ (U - x))(x ∪ (U - x) ⊆ U),
    rw← h239 at h238,
    have h240:= subsets_to_equal2 M U (x ∪ (U-x)),
    have h241:= notnot_imp 
    (U ⊆ x ∪ U - x ∧ x ∪ U - x ⊆ U )
     (U = (x ∪ U - x)) h240.1 h238,
    rw ssc_definition,
    have h242:= notnot_and (x ⊆ U)(U = (x ∪ U - x)),
    rw h242,
    split,
    {
      exact h20,
    },
    {
      exact h241,
    }
  end

lemma notnotssc3:  ∀(m U:M), MAXIMAL M m → U ∈ m → ∀ (p:M), (p ∈ FINITE M ∧ ∀ (x:M), x ∈ p → x ∈ FINITE M)→ ¬¬ p ⊆ SSC U:=
  begin
    intros m U hmax hU p hp,
    have hmaximal:= hmax,
    unfold MAXIMAL at hmaximal,
    cases hmaximal with hm h3,
    have hUfinite:= finitecardinals1 M m U hm hU,
    have h4: ∀(t:M),(t∈ p → ¬¬ t ∈ SSC(U)):=
      begin
        intros t ht,
        have h5:= notnotssc2 M m U hmax hU t,
        apply h5,
        cases hp with h6 h7,
        exact h7 t ht,
      end,
    cases hp with h10 h11,
    have h12:= finiteDNS M (SSC U) p h10 h4,
    rw subset_definition,
    exact h12,
  end   

lemma notnotssc4_helper:  ∀(m U:M), MAXIMAL M m → U ∈ m → 
∀ (p:M), p ∈ FINITE M  → p ⊆ (SSC U) →  ¬¬ p ∈ SSC (SSC U):=
  begin
    intros m U hmax hU p hp h4,
    have hmaximal:= hmax,
    unfold MAXIMAL at hmaximal,
    cases hmaximal with hm h3,
    have hUfinite:= finitecardinals1 M m U hm hU,
    have h4copy:= h4,
    rw subset_definition at h4,
    have h223: p ∩ (SSC U)-p = Λ:=
      begin
        rw full_extensionality,
        intro t,
        split,
        {
          intros h224,
          have h225:=intersection_axiom p ((SSC U)-p) t,
          have h226:= h225.1 h224,
          rw minus_members at h226,
          cases h226 with h227 h228,
          have h229:= h228.2 h227,
          contradiction,
        },
        {
          intros h230,
          have h231:= emptyset_axiom t,
          contradiction,
        }
      end,
    have h5: ∀ (t:M), t ∈ p → t ∈ FINITE M:=
      begin
        intros t ht,
        have h6:= h4 t ht,
        have h7:= ssc_definition U t,
        rw h7 at h6,
        cases h6 with h8 h9,
        have h10:= separablefinite M U hUfinite t h8,
        apply h10,
        unfold separable_subset,
        exact ⟨ h8,h9⟩,
      end,
    have h11:= finitepowerset M U hUfinite,
    have h20: ∀ (t:M),t ∈ (SSC U) → ¬¬(t ∈ p ∪ ((SSC U)-p)):=
      begin
        intros t ht,
        have h21:=binary_union_axiom p ((SSC U)-p) t,
        rw h21,
        rw minus_members,
        intro h22,
        have h23:= not_orNF (t ∈ p) (t ∈ SSC U ∧ ¬ t ∈ p),
        rw h23 at h22,
        cases h22 with h24 h25,
        apply h25,
        exact ⟨ ht, h24⟩,
      end,
    have h30:= finiteDNS M (p ∪ ((SSC U)-p)) (SSC U) h11 h20,
    rw ssc_definition,
    rw notnot_and,
    split,
    {
      intro h31,
      contradiction,
    },
    {
      have h31: (∀ (x : M), x ∈ SSC U → x ∈ p ∪ SSC U - p) → 
      (SSC U = (p ∪ SSC U - p)):=
       begin
         intros h32,
         rw full_extensionality,
         intros t,
         have h33:= h32 t,
         split,
         {
          exact h33,
         },
         {
          intros h34,
          rw binary_union_axiom at h34,
          cases h34 with h35 h36,
          {
            have h37:= member_subset M p (SSC U) t h4copy h35,
            exact h37,
          },
          {
            rw minus_members at h36,
            exact h36.1,
          }
         }
       end,
      have h40:= notnot_imp 
      (∀ (x : M), x ∈ SSC U → x ∈ p ∪ SSC U - p)
      (SSC U = (p ∪ SSC U - p)) h31,
      apply h40,
      exact h30,
    }
  end

lemma notnotdivide: ∀(a b:M), b ⊆ a → ∀(x:M), ¬¬ (x ∈ a ↔ x ∈  (b ∪ (a-b))):=
  begin
    intros a b hba x,
    rw binary_union_axiom,
    rw minus_members,
    rw notnot_iff_2way,
    have h3:= notnotLEM (x ∈ b),
    have h4: (x ∈ b ∨ ¬ x ∈ b) → (x∈ a ↔ (x ∈ b ∨ (x ∈ a ∧ ¬ x ∈b))):=
      begin
        intros lem,
        cases lem with h5 h6,
        {
          split,
          {
            intros ha,
            left,
            exact h5,
          },
          {
            intros h7,
            cases h7 with h8 h9,
            { 
              have h10:= member_subset M b a x hba h5,
              exact h10,
            },
            {
              exact h9.1,
            }
          }
        },
        {
          split,
          {
            intros ha,
            right,
            exact ⟨ ha, h6⟩,
          },
          {
            intros h9,
            cases h9 with h10 h11,
            {
              contradiction,
            },
            {
              exact h11.1,
            }
          }
        }
      end,  
    have h20:= double_negate (x ∈ b ∨ ¬x ∈ b → (x ∈ a ↔ x ∈ b ∨ x ∈ a ∧ ¬x ∈ b)),
    have h21:= notnot_imp (x ∈ b ∨ ¬x ∈ b)  (x ∈ a ↔ x ∈ b ∨ x ∈ a ∧ ¬x ∈ b) h4 h3,
    have h22:= notnot_iff_2way (x ∈ a)(x ∈ b ∨ x ∈ a ∧ ¬x ∈ b),
    rw h22 at h21,
    exact h21,
  end

lemma notnotdivide2: ∀(a b:M), b ⊆ a → a ∈ FINITE M → ¬¬ a = (b ∪ (a-b)):=
  begin
    intros a b h3 hfinite,
    --simp_rw full_extensionality,
    have h4:= notnotdivide M a b h3,
    simp_rw iff_def at h4,
    have h5:= λ (x:M),notnot_and (x ∈ a → x ∈ b ∪ a - b)
     (x ∈ b ∪ a - b → x ∈ a),
    simp_rw h5 at h4,
    have h6: ∀ (x : M), ¬¬(x ∈ a → x ∈ b ∪ a - b):=
      begin
        intros x,
        exact (h4 x).1,
      end,
    have h7: ∀(x:M), (x ∈ a → ¬¬ (x ∈ (b ∪ a - b))):=
      begin
        intros x h8,
        have h9:= h6 x,
        have h10: x ∈ a → ¬¬ (x ∈ (b ∪ (a-b))):=
          begin
            intros hx,
            have h12:= notnot_imp2way (x ∈ a) (x ∈ (b ∪ (a-b))),
            rw h12 at h9,
            apply h9,
            have h11:= double_negate (x ∈ a) hx,
            exact h11,
          end,
        exact h10 h8,
      end,
    have h20:= finiteDNS M (b ∪ (a-b)) a hfinite h7,
    have h25: ¬¬(a ⊆ (b ∪ (a-b))):=
      begin
        rw subset_definition,
        exact h20,
      end,
    have h26: (b ∪ (a-b)) ⊆ a:=
      begin
        rw subset_definition,
        intros z h27,
        rw binary_union_axiom at h27,
        cases h27 with h28 h29,
        {
          have h30:= member_subset M b a z h3 h28,
          exact h30,
        },
        {
          rw minus_members at h29,
          exact h29.1,
        }
      end, 
    have h31:= double_negate ((b ∪ (a-b)) ⊆ a) h26,
    have h32: (¬¬(a ⊆ (b ∪ (a - b))))∧ (¬¬ ((b ∪ (a - b)) ⊆ a)):=
      begin
        exact ⟨ h25, h31 ⟩,
      end,
    have h33: ¬¬((a ⊆ (b ∪ (a - b)))∧  ((b ∪ (a - b)) ⊆ a)):=
      begin
        have h34:= notnot_and (a ⊆ (b ∪ (a - b))) ((b ∪ (a - b)) ⊆ a),
        rw h34,
        exact h32,
      end,
    have h40:= subsets_to_equal2 M a (b ∪ (a-b)),
    rw h40 at h33,
    exact h33,
  end
 
lemma notnotssc4:  ∀(m U:M), MAXIMAL M m → U ∈ m → 
∀ (p:M), p ∈ FINITE M → 
(∀(t:M),(t ∈ p → t ∈ FINITE M )) →   
¬¬ p ∈ SSC (SSC U):=
  begin
    intros m U hmax hU p h4 h400,
    have hmaximal:= hmax,
    unfold MAXIMAL at hmaximal,
    cases hmaximal with hm h3,
    have hUfinite:= finitecardinals1 M m U hm hU,
    have h4copy:= h4,
    have h5:= notnotssc4_helper M m U hmax hU p h4copy,
    have h6:= notnot_imp 
     (p ⊆ SSC U)( ¬¬p ∈ SSC (SSC U)) h5,
    rw triplenegation at h6,
    apply h6,
    have h7:= notnotssc3 M m U hmax hU p ⟨ h4copy, h400⟩, 
    exact h7,
  end

lemma functionfinite: ∀(A B f:M), A ∈ FINITE M → B ∈ FINITE M →
  maps M f A B → ( ∀(x y:M), ‹x,y›   ∈ f → x ∈ A) → f ∈ FINITE M:=
    begin   
      have base: Λ ∈ W_functionfinite M:=
        begin
          rw W_functionfinite_members M,
          split,
          exact lambda_finite M,
          intros B f hB hmaps hdom,
          unfold maps at hmaps,
          cases hmaps with hrel h3,
          cases h3 with h4 h5,
          cases h5 with h6 h7,
          rw Rel_definition at hrel,
          have h10: f = Λ:=
            begin
              rw full_extensionality,
              intros z,
              split,
              {
                intros hz,
                have h90:= hrel z hz,
                cases h90 with a h91,
                cases h91 with b h92,
                rw h92 at *,
                have h93:= hdom a b hz,
                have h94:= emptyset_axiom a,
                contradiction,
              },
              {
                intros h20,
                have h21:= emptyset_axiom z,
                contradiction,
              }
            end,
          rw h10 at *,
          have h11:= lambda_finite M,
          exact h11,
        end,
      have step: ∀ (A c:M), A ∈ W_functionfinite M → ¬ c ∈ A → A ∪ single c ∈ W_functionfinite M:=  
        begin
          intros A c h32 h4,
          rw W_functionfinite_members,
          rw W_functionfinite_members at h32,
          cases h32 with hA h3,
          split,
          exact finite_adjoin M A c ⟨ hA, h4⟩ ,
          intros B f hB hmaps2 hdom,
          unfold maps at hmaps2,
          cases hmaps2 with h30 h31,
          cases h31 with h32 h33,
          cases h33 with h34 h35,
          have h34copy:= h34,
          have h36:= h35 c,
          have h200:= finite_adjoin M A c ⟨ hA, h4⟩,
          have h37: c ∈ A ∪ (single c):=
            begin
              rw binary_union_axiom,
              rw singleton1,
              right,
              refl,
            end,
          have h38:= h35 c h37,
          cases h38 with y h39,
          cases h39 with hy h40,
          have h41: ∀(x z:M), ‹ x,z› ∈ (f-single ‹ c,y› ) → x ∈ A:=
            begin
              intros x z h42,
              rw minus_members at h42,
              rw singleton1 at h42,
              cases h42 with h43 h44,
              have h45:= hdom x z h43,
              rw binary_union_axiom at h45,
              rw singleton1 at h45,
              cases h45 with h46 h47,
              {
                exact h46,
              },
              {
                rw h47 at *,
                have h48:= h34 c y z,
                have h49:= h48 ⟨ h37,⟨h40,h43⟩⟩,
                rw h49 at *,
                contradiction,   
              }
            end, 
          have h50:= h3 B (f-single ‹ c,y› ) hB,
          have h51: maps M (f - single  ‹ c,y › ) A B :=
            begin
              unfold maps,
              split,
              {
                rw Rel_definition,
                intros z h52,
                rw minus_members at h52,
                cases h52 with h53 h54,
                rw Rel_definition at h30,
                have h55:= h30 z h53,
                exact h55,
              },
              {
                split,
                {
                  intros x z h51,
                  cases h51 with h52 h53,
                  rw minus_members at h53,
                  cases h53 with h54 h55,
                  have h56:= h32 x z,
                  apply h56,
                  split,
                  {
                    rw binary_union_axiom,
                    left,
                    exact h52,
                  },
                  {
                    exact h54,
                  }
                },
                {
                  have h70:= finitedecidable M (A ∪ single c) h200,
                  rw decidable_members at h70,
                  split,
                  { 
                    intros x t z h51,
                    have h71:= h70 x c,
                    cases h51 with h52 h53,
                    cases h53 with h54 h55,
                    have h56:= h34 c t z,
                    have h62:x = c ∨ ¬ x = c:=
                      begin
                        apply h71,
                        split,
                        {
                          rw binary_union_axiom,
                          left,
                          exact h52,
                        },
                        {
                          exact h37,
                        }
                      end,
                    cases h62 with h63 h64,
                    {
                      rw h63 at *,
                      rw minus_members at h54 h55,
                      rw singleton1 at h54 h55,
                      rw ordered_pair_equality at h54 h55,
                      cases h54 with h56 h57,
                      cases h55 with h60 h61,
                      simp at h57 h61,
                      have h62:= h34copy c t y,
                      have h63: c ∈ A ∪ single c:=
                        begin
                          rw binary_union_axiom,
                          rw singleton1,
                          simp,
                        end, 
                      have h70:= h62 ⟨h63,⟨ h56, h40⟩⟩ , 
                      contradiction,
                    },         
                    {
                      have h71:= h34 x t z,
                      apply h71,
                      split,
                      {
                        rw binary_union_axiom,
                        left,
                        exact h52,
                      },
                      {
                        split,
                        {
                          rw minus_members at h54,
                          rw singleton1 at h54,
                          exact h54.1,
                        },
                        {
                          rw minus_members at h55,
                          rw singleton1 at h55,
                          exact h55.1,
                        }
                      }
                    }     
                  },
                  {
                    intros x hx,
                    have h80: x = c ∨ ¬ x = c:=
                      begin
                        have h81:= h70 x c,
                        apply h81,
                        split,
                        {
                          rw binary_union_axiom,
                          left,
                          exact hx,
                        },
                        {
                          exact h37,
                        }
                      end,
                    cases h80 with h81 h82,
                    {
                      rw h81 at *,
                      contradiction,
                    },
                    {
                      have h83: x ∈A ∪ single c:=
                        begin
                          rw binary_union_axiom,
                          left,
                          exact hx,
                        end, 
                      have h84:= h35 x h83,
                      cases h84 with y2 h85,
                      use y2,
                      cases h85 with h86 h87,
                      split,
                      {
                        exact h86,
                      },
                      {
                        rw minus_members,
                        split,
                        {
                          exact h87,
                        },
                        {
                          intros h88,
                          rw singleton1 at h88,
                          rw ordered_pair_equality at h88,
                          cases h88 with h89 h90,
                          contradiction, 
                        }
                      }
                    } 
                  }
                }
              }
            end,
          have h100:= h50 h51 h41,
          have h102: f = ((f - single  ‹ c,y ›) ∪ single  ‹ c,y ›):=
            begin
              rw full_extensionality,
              intros t,
              split,
              {
                intros ht,
                rw Rel_definition at h30,
                have h103:= h30 t ht,
                cases h103 with a h104,
                cases h104 with b h105,
                rw h105 at *,
                rw binary_union_axiom,
                have h210:= finite_decidable2 M (A ∪ single c) a c h200,
                have h106:a = c ∨ ¬ a = c:=
                  begin
                    apply h210,
                    have h211:= hdom a b ht,
                    exact h211,
                    rw binary_union_axiom,
                    right,
                    rw singleton1,
                  end,
                cases h106 with h107 h108,
                {
                  rw h107 at *,
                  right,
                  rw singleton1,
                  rw ordered_pair_equality,
                  simp,
                  have h109:= h34copy c b y,
                  apply h109,
                  exact ⟨ h37, ⟨ ht,h40⟩⟩, 
                },
                {
                  left,
                  rw minus_members,
                  rw singleton1,
                  split,
                  { exact ht,
                  },
                  {
                    rw ordered_pair_equality,
                    intros h109,
                    cases h109 with h110 h111,
                    contradiction,
                  }
                }
              },
              {
                intros h120,
                rw binary_union_axiom at h120,
                cases h120 with h121 h122,
                {
                  rw minus_members at h121,
                  exact h121.1,
                },
                {
                  rw singleton1 at h122,
                  rw h122,
                  exact h40,
                }
              }
            end,
          rw h102, 
          have h130:= finite_adjoin M ( f- single  ‹ c,y › ) ‹ c,y ›,
          apply h130,
          split,
          {
            exact h100,
          },
          {
            intros h131,
            rw minus_members at h131,
            rw singleton1 at h131,
            simp at h131,
            exact h131,
          }
        end,   
      have step2: adjoin_closed M  (W_functionfinite M):=
        begin
          rw adjoin_closed,
          intros A2 c2 h20,
          exact step A2 c2 h20.1 h20.2,
        end,
      have h: (FINITE M) ⊆ W_functionfinite M:= finite_conditions M (W_functionfinite M) step2 base, 
      intros A,
      have h22:= member_subset M (FINITE M)(W_functionfinite M) A h,
      rw W_functionfinite_members at h22,
      intros B f hA,
      have h23:= h22 hA,
      cases h23 with h24 h25,
      exact h25 B f,
    end 

lemma decidable_image: ∀ (X Y f:M),   X ∈ FINITE M → Y ∈ FINITE M → maps M f X Y → dom f = X → Rel f → ∀ (y:M), y ∈ Y →
(∃ (x:M), x ∈ X ∧ ‹ x,y› ∈ f) ∨ (¬ ∃ (x:M), x ∈ X ∧ ‹ x,y › ∈ f):=
  assume X Y f,
  begin
    intros hX hY hmaps hdom hrel hy,
    have hproduct := productfinite2 M X hX Y hY,
    have hrelcopy:= hrel,
    set Z:= preimage M f X with h50,
    have h3: f ⊆ X × Y:=
      begin
        rw subset_definition,
        intros t ht,
        rw Rel_definition at hrel,
        have h3:= hrel t ht,
        cases h3 with x h4,
        cases h4 with y h5,
        rw h5 at *,
        rw product_axiom,
        use x, use y,
        simp,
        rw full_extensionality at hdom,
        have h6:= hdom x,
        rw domain_axiom f hrelcopy at h6,
        have h7:= h6.mp ⟨ y, ht⟩, 
        unfold maps at hmaps,
        rcases hmaps with ⟨ h17, h8, h9, h10⟩, 
        have h11:= h8 x y ⟨ h7, ht⟩, 
        exact ⟨ h7, h11⟩, 
      end,
    have h19:= domain_axiom f hrel,
    simp_rw hdom at h19,
    have h20:= functionfinite  M X Y f hX hY hmaps, 
    have h100: f ∈ FINITE M:=
      begin
        apply h20,
        intros x y h101,
        have h102:= (h19 x).2,
        exact h102 ⟨y, h101 ⟩, 
      end, 
    have h21:= finitedecidable M X hX,
    have h22:= subset_reflexive M X,
    have h24:= finiteseparable M   (X × Y) f hproduct h100 h3,
    have h25:= boundedquantification2 M f X Y,
    apply h25,
    {
      repeat{split},
      {
        exact hX,
      },
      {
        exact h22,
      },
      {
        exact h21,
      },
      {
        intros u z hu hz,
        rw full_extensionality at h24,
        specialize h24 ‹ u,z›,
        rw product_axiom at h24,
        have h25: (∃ (a b : M), a ∈ X ∧ b ∈ Y ∧  ‹ u,z ›  =  ‹ a,b › ):=
          begin
            use u, use z,
            simp,
            exact ⟨ hu, hz⟩,
          end,
        rw h24 at h25,
        rw binary_union_axiom at h25,
        cases h25 with h26 h27,
        {
          rw minus_members at h26,
          right,
          exact h26.right,
        },
        {
          left,
          exact h27,
        }
      }
    },
  end

lemma subsetoffinite: (¬ 𝕍 ∈ FINITE M)→ ∀ (m:M), MAXIMAL M m → 
∀ (k:M), k ∈ 𝔽 → k ≤ exp M (𝕋 M m) → ¬¬ ∃(u:M), u ∈ k ∧ u ⊆ FINITE M:=

begin
  intros hV m hmax,
  have base: zero ∈ Z_subsetoffinite M m:=
    begin
      rw Z_subsetoffinite_members M m,
      split,
      {
        exact zeroF M,
      },
      {
        intros h3 h30,
        apply h30,
        use Λ,
        rw zero_members,
        simp,
        rw subset_definition,
        intros z h4,
        have h5:= emptyset_axiom z,
        contradiction,
      }
    end,
  have step: ∀ (k:M), k ∈ Z_subsetoffinite M m → (∃ (u:M), u ∈ 𝕊 k) → 𝕊 k ∈ Z_subsetoffinite M m:=
    begin
      intros k h6 hsk,
      rw Z_subsetoffinite_members at h6,
      rw Z_subsetoffinite_members,
      cases h6 with hk h7,
      split,
      {
        exact successorF M k hk hsk,
      },
      {
        intros hsk2,
        have h338: ∀(u c:M), u ∈ k → u ⊆ FINITE M →  c ∈ FINITE M → ¬ c ∈ u → ( u ∪ single c ∈ FINITE M ∧  u ∪ single c ⊆ FINITE M  ∧ u ∪ single c ∈ 𝕊 k):=
          begin
            intros u c hu husub hcfinite h8,
            have h10:= finitecardinals1 M k u hk hu,
            repeat{split},
            {
              have h9:= finite_adjoin M u c ⟨ h10, h8⟩,
              exact h9,
            },
            {
              rw subset_definition,
              intros z hz,
              rw binary_union_axiom at hz,
              rw singleton1 at hz,
              cases hz with hz h12,
              {
                exact member_subset M u (FINITE M) z husub  hz,
              },
              {
                rw h12 at *,
                exact hcfinite,
              }
            },
            {
              rw successor_members,
              use u, use c,
              simp,
              exact ⟨ hu, h8⟩,
            }
          end,
        have hmaximal:= hmax,
        unfold MAXIMAL at hmaximal,
        cases hmaximal with hm h199,
        have h200:= cardinalsinhabited M m hm,
        cases h200 with U hU,
        have hUfinite:= finitecardinals1 M m U hm hU,  
        have h354:(∃ (u: M), u ∈ k ∧ u ⊆ FINITE M) → 
           ¬¬(∃(u: M),  u ⊆ FINITE M ∧ u ∈ 𝕊 k ):=
          begin
            intros h355,
            cases h355 with u h356,
            cases h356 with hu husub,
            have hfinite:= finitecardinals1 M k u hk hu,
            have h20:= finitenotfinite1 M,
            have h376: ¬¬ ∃(c:M), ¬c ∈ u ∧ u ⊆ FINITE M ∧ c ∈ FINITE M:=
              begin
                intros h21,
                have h19: SSC U ∈ FINITE M:=
                  begin
                     exact finitepowerset M U hUfinite,
                  end,
                have h22: SSC U ⊆ FINITE M:=
                  begin
                    rw subset_definition,
                    intros z h23,
                    rw ssc_members at h23,
                    have h24:= separablefinite M U hUfinite z,
                    apply h24,
                    {
                      exact h23.1,
                    },
                    {
                      unfold separable_subset,
                      cases h23 with h25 h26,
                      split,
                      {
                        exact h25,
                      },
                      {
                        rw full_extensionality,
                        intros y,
                        split,
                        {
                          rw binary_union_axiom,
                          intros hy,
                          rw minus_members,
                          have h27:= h26 y hy,
                          cases h27 with h28 h29,
                          {
                            left,
                            exact h28,
                          },
                          {
                            right,
                            exact ⟨ hy, h29⟩,
                          }
                        },
                        {
                          specialize h26 y,
                          intros h30,
                          rw binary_union_axiom at h30,
                          cases h30 with h31 h32,
                          {
                            exact member_subset M z U y h25 h31,
                          },
                          {
                            rw minus_members at h32,
                            exact h32.1,
                          }
                        }
                      }
                    }
                  end,
                have h40: SSC U - u = Λ:=
                  begin
                    rw full_extensionality,
                    intros x,
                    split,
                    {
                      intros h41,
                      rw minus_members at h41,
                      cases h41 with h42 h43,
                      have h44:= member_subset M (SSC U) (FINITE M) x h22 h42,
                      have h45:= h21 ⟨ x, ⟨ h43, husub,h44⟩⟩,
                      contradiction,
                    },
                    {
                      intros h46,
                      have h47:= emptyset_axiom x,
                      contradiction,
                    }
                  end,
                have h50: ∀ (x:M), ((x∈ SSC U)) → ¬¬ (x ∈ u):=
                  begin
                    intros x,
                    rw full_extensionality at h40,
                    specialize h40 x,
                    rw minus_members at h40,
                    have h52:= emptyset_axiom x,
                    rw←h40 at h52,
                    have h53:= not_and.1 h52,
                    intros h51,                
                    exact h53 h51,                 
                  end,
                have h60: ∀(x:M), x ∈ u → ¬¬x ∈ SSC U :=
                  begin
                    intros x h61,
                    have h62:= member_subset M u (FINITE M) x husub,
                    have h63:=  h62 h61,
                    have h64:= notnotssc2 M m U hmax hU x h63,
                    exact h64,
                  end,
                have h70:= finiteDNS M u (SSC U) h19 h50,
                have h71:= finiteDNS M (SSC U) u hfinite h60,
                have h72: (∀ (x : M), x ∈ SSC U → x ∈ u)→ (∀ (x : M), x ∈ u → x ∈ SSC U) → ∀ (x:M), x ∈u ↔ x ∈ SSC U:=  
                  begin
                    intros h73 h74 x,
                    split,
                    {
                      intros h75,
                      exact h74 x h75,
                    },
                    {
                      intros h76,
                      exact h73 x h76,
                    }
                  end,
                have h80: ¬¬ ∀ (x:M), x∈ u ↔ x ∈ SSC U :=
                  begin
                    have h81:= notnot_imp 
                        (∀ (x : M), x ∈ SSC U → x ∈ u)
                        ((∀ (x : M), x ∈ u → x ∈ SSC U) → 
                          ∀ (x : M), x ∈ u ↔ x ∈ SSC U) h72 h70,
                    have h82:= (notnot_imp2way 
                           ((∀ (x : M), x ∈ u → x ∈ SSC U))
                          (∀ (x : M), x ∈ u ↔ x ∈ SSC U)).1 h81 h71,
                    exact h82, 
                  end, 
                have h90: ¬¬(u = SSC U):=
                  begin
                    rw full_extensionality,
                    exact h80,
                  end,
                have h92: SSC U ∈ exp M (𝕋 M m):=
                  begin
                    rw exp_members,
                    use U,
                    split,
                    {
                       rw T_members,
                       use U,
                       exact ⟨ hU, similar_reflexive M (USC U) ⟩,
                    },
                    {
                      exact similar_reflexive M (SSC U),
                    }
                  end,
                have h100:= expTinF M m hm,
                have h93: u = SSC U → k = exp M (𝕋 M m):=
                  begin
                    intros h94,
                    have h95:= hu,
                    rw←  h94 at h92,
                    have h96:= cardinalsdisjoint M k (exp M (𝕋 M m)) u hk h100,
                    rw intersection_axiom at h96,
                    exact h96 ⟨ h95, h92⟩,
                  end,
                have h95:= notnot_imp (u = SSC U )( k = exp M (𝕋 M m)) h93 h90,
                have h96:= FregeNdecidable M,
                rw decidable_members at h96,
                have h97:= h96 k (exp M (𝕋 M m)) ⟨ hk, h100⟩,
                have h98: k = exp M (𝕋 M m) :=
                  begin
                    cases h97 with h98 h99,
                    {
                      exact h98,
                    },
                    {
                      contradiction,
                    }
                  end,
                rw←  h98 at *,
                have hskf:= (successorF M k hk hsk),
                have h101:= xlessthansuccessorx M k hk hskf,
                have h102:= le_transitive2 M k (𝕊 k) k hk hskf hk h101 hsk2,
                have h103:= xnotlessthanx M k hk,
                contradiction,
              end, 
            have h750:  (∃ (c : M), ¬c ∈ u ∧ u ⊆ FINITE M ∧ c ∈ FINITE M) →  ∃ (c:M), u ∪ single c ∈ FINITE M ∧ u ∪ single c ⊆ FINITE M ∧ u ∪ single c ∈ 𝕊 k :=
               begin
                 intros h751,
                 cases h751 with c h752,
                 use c,
                 repeat{split},
                 {
                  have h753:= finite_adjoin M u c ⟨ hfinite, h752.1⟩,
                  exact h753,
                 },
                 {
                   cases h752 with h754 h755,
                   rw subset_definition,
                   intros z hz,
                   rw binary_union_axiom at hz,
                   rw singleton1 at hz,
                   cases hz with h756 h757,
                   {
                     exact member_subset M u (FINITE M) z husub h756,
                   },
                   {
                     rw h757 at *,
                     exact h755.2,
                   }
                 },
                 {
                   rw successor_members,
                   use u, use c,
                   simp,
                   exact ⟨hu, h752.1⟩, 
                 }
               end,
            have h779: ¬¬ ∃ (c:M), u ∪ single c ∈ FINITE M ∧ u ∪ single c ⊆ FINITE M ∧ u ∪ single c ∈ 𝕊 k:=
              begin
                have h780:= notnot_imp  (∃ (c : M), ¬c ∈ u ∧ u ⊆ FINITE M ∧ c ∈ FINITE M )(
                  (∃ (c : M), u ∪ single c ∈ FINITE M ∧ u ∪ single c ⊆ FINITE M ∧ u ∪ single c ∈ 𝕊 k)) h750 h376,

              exact h780,
              end,  
            have h3380:= h338 u,          
            have h790:  (∃ (c : M), ¬ c ∈ u ∧  u ⊆ FINITE M ∧  c ∈ FINITE M) → ∃ (p:M),  p ⊆ FINITE M ∧ p ∈ 𝕊 k  :=
              begin
                intros h791,
                cases h791 with c h792,
                use u ∪ single c,
                have h793:= h3380 c hu husub h792.2.2 h792.1,
                exact h793.2,
              end,
            have h800:= notnot_imp (∃ (c : M), ¬c ∈ u ∧ u ⊆ FINITE M ∧ c ∈ FINITE M)(∃ (p : M),  p ⊆ FINITE M  ∧ p ∈ 𝕊 k) h790,
            apply h800,
            exact h376,
          end,
        simp_rw and_comm,
        have h355:= notnot_imp 
        (∃ (u : M), u ∈ k ∧ u ⊆ FINITE M) (¬¬∃ (u : M), u ⊆ FINITE M ∧ u ∈ 𝕊 k) h354,
        rw triplenegation at h355,
        apply h355,
        apply h7,
        have hskf:= successorF M k hk hsk,
        have h356:= xlessthansuccessorx M k hk hskf,
        have h358:= expTinF M m hm,
        have h360:= le_transitive2 M k (𝕊 k) (exp M (𝕋 M m)) hk hskf h358 h356 hsk2,
        rw lessthan_definition at h360,
        exact h360.1,
      }
    end,
  intros k hk,
  rw F_members at hk,
  have h200:= hk (Z_subsetoffinite M m) ⟨ base,step⟩,
  rw Z_subsetoffinite_members at h200,
  exact h200.2,
end

lemma subsetoffinite2: (¬ 𝕍 ∈ FINITE M)→ ∀ (m:M), MAXIMAL M m → 
∀(u:M), u ∈ FINITE M → Nc M u ≤ exp M (𝕋 M m) → ¬¬ ∃ (v:M), similar M u v ∧  v ∈ FINITE M ∧ v ⊆ FINITE M  :=
  begin
    intros hV m hmaximal u hu h4,
    have hmax2 := hmaximal,
    unfold MAXIMAL at hmax2,
    cases hmax2 with hm hmax,
    set kappa:= Nc M u with kappadef,
    have hk3:= xinNcx M u,
    have hk2:= hk3,
    have hk:= finitecardinals3 M u hu,
    rw← kappadef at hk,
    rw← kappadef at hk2,
    have h5:= cardinalsinhabited M m hm,
    cases h5 with U hU,
    have h6:= expTinF M m hm,
    have h7:= subsetoffinite M hV m hmaximal kappa hk h4,    
    have h8: ∀ (v:M), v ∈ kappa → similar M u v:=
      begin
        intros v,
        have h9:=finitecardinals2 M u v kappa hk hk2,
        exact h9,
      end,
    have h10: ∀ (v:M), v ∈ kappa → v ∈ FINITE M :=
      begin
        intros v hv,
        have h11:=finitecardinals1 M kappa v hk hv,
        exact h11,
      end,
    have h12: (∃(v:M),v ∈ kappa ∧ v ⊆ FINITE M ) →
              (∃(v:M), similar M u v ∧ v ∈ FINITE M ∧ v ⊆ FINITE M):=
                begin
                  intros h20,
                  cases h20 with v h21,
                  use v,
                  cases h21 with h22 h23,
                  exact ⟨ h8 v h22, h10 v h22,h23⟩,
                end,
    have h13:= notnot_imp (∃ (v : M), v ∈ kappa ∧ v ⊆ FINITE M)(∃ (v : M), similar M u v ∧ v ∈ FINITE M ∧ v ⊆ FINITE M) h12 h7,
    exact h13,
  end


 #axioms_all  -- This file is clean. 