import inf23

variables (M:Type) [Model M] (a b x y z u v w X R W κ μ ℓ : M)

open Model 

lemma notsscusc1:∀(m c U:M), c ∈ FINITE M → MAXIMAL M m → U ∈ m →
  c ⊆ U → SSC (SSC U) ⊆ U → c ⊆ (SSC U) →  
  ¬ similar M (USC c) (SSC (SSC U)):=
  begin
    intros m c U hc hmax hU extra extra2 extra3 hsimilar,
    have hmax2:= hmax,
    unfold MAXIMAL at hmax2,
    cases hmax2 with hm h2,
    have h22: USC U ∈ 𝕋 M m:=  
      begin
        rw T_members,
        use U,
        have h2:= similar_reflexive M (USC U),
        exact ⟨hU, h2⟩, 
      end,
    have h23: SSC U ∈ exp M (𝕋 M m):=
      begin
        rw exp_members,
        use U,
        have h3:= similar_reflexive M (SSC U),
        exact ⟨h22, h3⟩,  
      end,
    have h24: USC (SSC U) ∈ 𝕋 M (exp M (𝕋 M m)):=
      begin
        rw T_members,
        use SSC U,
        have h4:= similar_reflexive M (USC (SSC U)),
        exact ⟨ h23, h4⟩,
      end,
    have h21: 𝕋 M m ∈ 𝔽:= Tfinite M m hm, 
    have h25: USC (SSC U) ∈ exp M (𝕋 M (𝕋 M m)):=
      begin
        have h26:= expT M (𝕋 M m) h21 ⟨ SSC U, h23⟩,
        rw h26,
        exact h24,
      end,
    have h27: SSC (SSC U) ∈ exp M (exp M (𝕋 M (𝕋 M m))):=
      begin
        rw exp_members,
        use SSC U,
        have h28:= similar_reflexive M (SSC (SSC U)),
        exact ⟨ h25, h28⟩,
      end,
    have h31:= finitecardinals1 M m U hm hU,
    have h32:= finitepowerset M U h31,
    have h40: Nc M (SSC U) ∈ 𝔽 := finitecardinals3 M (SSC U) h32,
    have h44:= finitepowerset M (SSC U) h32,
    have h45: Nc M (SSC (SSC U)) ∈ 𝔽:= finitecardinals3 M (SSC (SSC U)) h44,
    have h41:= expTinF M m hm, 
    unfold similar at hsimilar,
    cases hsimilar with f h40,
    unfold similarity at h40,
    cases h40 with honeone honto,
    set D:= Diagonal M f c with Ddef,
    have h41: c ∈  SSC U :=
      begin
        have h42:= finiteseparable M U c h31 hc extra,
        rw ssc_members,
        split,
        {
          exact extra,
        },
        {
          intros y hy,
          rw full_extensionality at h42,
          specialize h42 y,
          rw h42 at hy,
          rw binary_union_axiom at hy,
          cases hy with h43 h44,
          {
            right,
            rw minus_members at h43,
            exact h43.2,
          },
          {
            left,
            exact h44,
          }
        }
      end,
    have h50: D ⊆ c:=
      begin
        rw subset_definition,
        intros t,
        rw Ddef,
        rw Diagonal_members M f c,
        intros h51,
        cases h51 with ht h52,
        exact ht,
      end,
    have h53: D ⊆ U :=
      begin
        rw subset_definition,
        intros t ht,
        have h54:= member_subset M D c t h50 ht,
        have h55:= member_subset M c U  t extra h54,
        exact h55,
      end,
    unfold oneone at honeone,
    cases honeone with hmaps h56,
    cases h56 with hfunc hdom,
    unfold maps at hmaps,
    cases hmaps with hrel h57,
    cases h57 with h58 h59,
    cases h59 with h60 h61,
    have h62: ∀ (t y:M), t ∈ c → ‹ single t,y › ∈ f → y ∈ SSC(SSC(U)):=
      begin
        intros t y ht hy,
        specialize h61 (single t),
        have h62: single t ∈ USC c:=
          begin
            rw usc,
            use t,
            simp,
            exact ht,
          end,
        have h63:= h61 h62,
        cases h63 with y2 h64,
        cases h64 with h65 h66,
        have h67:= h60 (single t) y y2 ⟨ h62, hy, h66⟩,
        rw h67 at *,
        exact h65,
      end,
    have h70: ∀ (t y : M), t ∈ c →  ‹ single t,y ›  ∈ f → y ⊆ SSC U :=
      begin
        intros t y ht h71,
        have h72:= h62 t y ht h71,
        rw ssc_members at h72,
        exact h72.1,
      end,
    have h80: ∀ (t y : M), t ∈ c →  ‹ single t,y ›  ∈ f → y ∈ FINITE M :=
      begin
        intros t y ht h81,
        have h82:= h70 t y ht h81,
        have h83:= separablefinite M (SSC U) h32 y h82,
        have h84:= h62 t y ht h81,
        apply h83,
        split,
        {
          exact h82,
        },
        {
          rw ssc_members at h84,
          cases h84 with h85 h86,
          rw full_extensionality,
          intros z,
          specialize h86 z,
          rw binary_union_axiom,
          rw minus_members,
          split,
          {
            intros hz,
            have h87:= h86 hz,
            cases h87 with h88 h89,
            {
              left,
              exact h88,
            },
            {
              right,
              exact ⟨hz, h89⟩, 
            }
          },
          {
            intros h90,
            cases h90 with h91 h92,
            {
                exact member_subset M y (SSC U) z h85 h91,
            },
            {
              exact h92.1,
            }
          }
        }
      end,
    have h200:∀ (t:M),  t∈ c → t ∈ SSC U:=
      begin
        intros t ht,
        exact member_subset M c (SSC U) t extra3 ht,
      end,
    have h201: ∀(t y:M), t∈ c → ‹ single t, y › ∈ f → t ∈ y ∨ ¬ t ∈ y:=
      begin
        intros t y ht h202,
        have h203:= h62 t y ht h202,
        rw ssc_members at h203,
        cases h203 with h204 h205,
        have h206:= h205 t,
        apply h206,
        have h207:= member_subset M c (SSC U) t extra3 ht,
        exact h207,
      end, 
    have h210: ∀ (t:M), t ∈ c → t ∈ D ∨ ¬ t ∈ D:=
      begin
        intros t ht,
        rw Ddef,
        rw Diagonal_members M f c,
        have h211: single t ∈ USC c:=
          begin
            rw usc_members,
            exact ht,
          end,
        have h212:= h61 (single t) h211,
        cases h212 with y h213,
        cases h213 with h214 h215,
        have h216:= h201 t y ht h215,
        cases h216 with h217 h218,
        {
          right,
          intros h219,
          cases h219 with h220 h221,
          cases h221 with y2 h222,
          cases h222 with h223 h224,
          have h225:= h60 (single t) y y2 ⟨ h211, h215, h223⟩,
          rw← h225 at *,
          contradiction,
        },
        {
          left,
          split,
          {
            exact ht,
          },
          {
            use y,
            exact ⟨ h215, h218⟩,
          }
        }
      end, 
    have h220: D ⊆ SSC U:= subset_transitive M D c (SSC U) h50 extra3,
    have h241:= finitepowerset M U h31,
    have h240: c ∈ SSC(SSC U):=
      begin
        rw ssc_members,
        split,
        {
          exact extra3,
        },
        {
          have h242:= finiteseparable M (SSC U) c h241 hc extra3,
          rw full_extensionality at h242,
          intros y,
          specialize h242 y,
          rw binary_union_axiom at h242,
          rw minus_members at h242,
          rw h242,
          intros h243, 
          cases h243 with h244 h245,
          {
            right,
            exact h244.2,
          },
          {
            left,
            exact h245,
          }
        }
      end,
    have h230: D ∈ SSC (SSC U):=
      begin
        rw ssc_members,
        split,
        {
          exact h220,
        },
        {
          intros t h231,
          rw ssc_members at h240,
          cases h240 with h242 h243,
          have h244:= h243 t h231,
          cases h244 with h245 h246,
          {
            exact h210 t h245,
          },
          {
            right,
            rw Diagonal_members M f c,
            intro h247,
            cases h247 with h248 h249,
            contradiction,
          }
        }
      end,
    unfold onto at honto,
    have h250:= honto D h230,
    cases h250 with q h251,
    cases h251 with hq h252,
    rw usc at hq,
    cases hq with p h253,
    cases h253 with hp h254,
    rw h254 at *,
    have h255:= h210 p hp,
    cases h255 with h256 h257,
    {
      have h256copy:= h256,
      rw Diagonal_members M f c  at h256,
      cases h256 with h257 h258,
      cases h258 with D2 h259,
      cases h259 with h260 h261,
      have h262:= h60 (single p) D D2,
      rw usc_members at h262,
      have h263:= h262 ⟨ h257, h252, h260⟩,
      rw← h263 at *,
      contradiction,  -- we had to keep h256copy! 
    },
    {
      rw Diagonal_members M f c  at h257,
      apply h257,
      split,
      {
        exact hp,
      },
      {
        use D,
        split,
        {
          exact h252,
        },
        {
          rw Diagonal_members M f c,
          exact h257,
        }
      }
    }
  end  


lemma notsscusc4:  ∀(m c U e:M),  MAXIMAL M m → U ∈ m →
  SSC(SSC U) ⊆ U →
  c ∈ FINITE M →
  c ⊆ U →
  e ∈ FINITE M →
  similar M e c →
  e ⊆ SSC U →
  e ⊆ U →
  ¬ similar M (USC c) (SSC (SSC U)):=
  begin
   intros m c U e hmax hU h4 hcfinite hcU hefinite hesim hessc heu hsim,
   have h409:= (uscsimilar M e c).1 hesim,
   have h410:= similar_transitive M (USC e) (USC c) (SSC (SSC U)) h409 hsim,
   have h411:= notsscusc1 M m e U hefinite hmax hU heu h4 hessc,
   contradiction,
  end

lemma notsscusc5: ∀(m c U e:M),  MAXIMAL M m → U ∈ m →
  ¬¬ SSC(SSC U) ⊆ U →
  ¬¬ c ∈ FINITE M →
  ¬¬ c ⊆ U →
  ¬¬ e ∈ FINITE M →
  ¬¬ similar M e c →
  ¬¬ e ⊆ SSC U →
  ¬¬ e ⊆ U →
  ¬ similar M (USC c) (SSC (SSC U)):=
  begin
    intros m c U e hmax hU,
    have h3:= double_negate 
    (  
      SSC(SSC U) ⊆ U →
      c ∈ FINITE M →
      c ⊆ U →
      e ∈ FINITE M →
      similar M e c →
      e ⊆ SSC U →
      e ⊆ U →
      ¬ similar M (USC c) (SSC (SSC U))
    ) (notsscusc4 M m c U e hmax hU),
    repeat{rw notnot_imp2way at h3},
    rw triplenegation at h3,
    exact h3,
  end

lemma reorder_conj_for_h302 {c : M} :
  (∃ v : M, similar M c v ∧ v ∈ FINITE M ∧ v ⊆ FINITE M) ↔
  (∃ v : M, v ∈ FINITE M ∧ v ⊆ FINITE M ∧ similar M c v) :=
begin
  apply exists_congr,
  intro v,
  exact ⟨λ ⟨h1, h2, h3⟩, ⟨h2, h3, h1⟩, λ ⟨h2, h3, h1⟩, ⟨h1, h2, h3⟩⟩,
end

lemma  notsscusc2: 
  ¬ 𝕍 ∈ FINITE M →  ∀(m c U:M),  MAXIMAL M m → U ∈ m →
  c ∈ FINITE M → 
  Nc M c ≤ exp M (𝕋 M m) → 
  c ⊆ U → 
  SSC (SSC U) ⊆ U → 
  ¬ similar M (USC c) (SSC (SSC U)):=
      begin
        intros hV m c U hmax hU hc hineq hcsubu hssc hsim,
        have h302:= subsetoffinite2 M hV m hmax c hc hineq,
        have h303: ∀ (e:M), e ∈ FINITE M → e ⊆ (FINITE M) → similar M e c → ¬ similar M (USC c) (SSC (SSC U)):=
          begin
            intros e he hesub hec hsim,
            have h304: ∀ (u:M), u ∈ e → ¬¬ u ∈ (SSC U):=
              begin
                intros u hu,
                have hufinite:=member_subset M e (FINITE M) u hesub hu,
                have h305:= notnotssc2 M m U hmax hU u hufinite,
                exact h305,
              end,
            have h305:= finiteDNS M (SSC U) e he h304,
            have h306:= h305,
            rw← subset_definition at h306,
            have h307:= double_negate (SSC (SSC U) ⊆ U) hssc,
            have h308:= double_negate (c ∈ FINITE M) hc,
            have h309:= double_negate (c ⊆ U) hcsubu,
            have h310:= double_negate (e ∈ FINITE M) he,
            have h311:= double_negate (similar M e c) hec,
            have h312:= notnotssc1 M m U hmax hU e he,
            have h320:= notsscusc5 M m c U e hmax hU h307 h308 h309 h310 h311 h306 h312,
            contradiction,
          end,
        have h325: (∃ (e:M), e ∈ FINITE M ∧  e ⊆ (FINITE M) ∧  similar M e c) → ¬ similar M (USC c) (SSC (SSC U)):=
          begin
            intros h326,
            cases h326 with e h327,
            rcases h327 with ⟨ h328, h329, h330⟩,
            have h331:= h303 e h328 h329 h330,
            exact h331,
          end,
        have h332:= double_negate ((∃ (e:M), e ∈ FINITE M ∧  e ⊆ (FINITE M) ∧  similar M e c) → ¬ similar M (USC c) (SSC (SSC U))) h325,
        have h340:= push_double_negationNF (∃ (e : M), e ∈ FINITE M ∧ e ⊆ FINITE M ∧ similar M e c) 
                    (¬similar M (USC c) (SSC (SSC U))) h332,
        rw triplenegation at h340,
        simp_rw reorder_conj_for_h302 at h302,
        have h302fixed: ¬¬∃ (v : M), v ∈ FINITE M ∧ v ⊆ FINITE M ∧ similar M v c:=
          begin
            intros h90,
            apply h302,
            intros h91,
            apply h90,
            cases h91 with v h92,
            use v,
            rw similar_symmetric at h92,
            exact h92,
          end,
        have h:= h340 h302fixed,
        contradiction,
      end

lemma smalltower: ∀(m:M), MAXIMAL M m → exp M (exp M (𝕋 M m)) = Λ:=
  begin
    intros m hmaximal,
    rw full_extensionality,
    intros x,
    have hmax:= hmaximal,
    unfold MAXIMAL at hmax,
    cases hmax with hm h1,
    have hTm:= Tfinite M m hm,
    split,
    {
      intros h,
      have hcopy:= h,
      rw exp_members at h,
      cases h with w h3,
      cases h3 with h4 h5,
      have h6:= xinNcx M w,
      have h7:= expTinF M m hm,
      have h8:= finitecardinals1 M (exp M (𝕋 M m)) (USC w)  h7 h4,
      have h9:= (uscfinite M w).1 h8,
      have h10:= finitecardinals3 M w h9,
      have h11:= h1 (Nc M w) h10,
      have h12:= letolessthan M (Nc M w) m h10 hm,
      rw h12 at h11,
      cases h11 with h13 h14,
      {
        have h15:= Torder M (Nc M w) h10 m hm h13,
        have h16:= mlessthanexpm M (𝕋 M m) hTm ⟨ USC w, h4⟩,
        have h17:= Tmax M m (exp M (𝕋 M m)) hmaximal h7 h16,
        rw h17 at hcopy,
        exact hcopy,
      },
      {
        rw h14 at *,
        have h21:= similar_reflexive M (USC w),
        have h20: USC w ∈ 𝕋 M m:=
          begin
            have h22:= (T_members M m (USC w)).2,
            apply h22,
            use w,
            exact ⟨h6, h21⟩, 
          end,  
        have h23:= cardinalsdisjoint M (exp M (𝕋 M m)) (𝕋 M m) (USC w) h7 hTm,
        rw intersection_axiom at h23,
        have h24:= h23 ⟨ h4, h20⟩,
        have h25:= mlessthanexpm M (𝕋 M m) hTm ⟨ USC w, h4⟩,
        rw h24 at h25,
        have h26:= xnotlessthanx M (𝕋 M m) hTm,
        contradiction,
      }
    },
    {
      intros h,
      have h2:= emptyset_axiom x,
      contradiction,
    }
  end

lemma nonemptytoF: ∀ (max n:M), MAXIMAL M max → n ∈ 𝔽 → ¬ exp M n = Λ → exp M n ∈ 𝔽:=
  begin
    intros max n hmax hn h3,
    have h4:= Tmax5  M max n hmax hn,
    have hmaximal:= hmax,
    unfold MAXIMAL at hmaximal,
    cases hmaximal with hm h200,
    have h5:= Tfinite M max hm,
    have h6:= finitetrichotomy M n hn (𝕋 M max) h5,
    have h7: n ≤ 𝕋 M max ∨ 𝕋 M max < n:=
      begin
        rw letolessthan M n (𝕋 M max) hn h5,
        cases h6 with h7 h8,
        {
          left, left,
          exact h7,
        },
        {
          cases h8 with h9 h10,
          {
            left, right,
            exact h9,
          },
          {
            right,
            exact h10,
          }
        }
      end,
    cases h7 with h20 h21,
    {
      exact h4.1 h20,
    },
    {
      have h30: ¬ exp M n ∈ 𝔽:=
        begin
          intros h31,
          have h32:=cardinalsinhabited M (exp M n) h31,
          have h33:= h4.2 h31,
          have h34:= le_transitive3 M n (𝕋 M max) n hn h5 hn h33 h21,
          have h35:= xnotlessthanx M n hn,
          contradiction,
        end,
      have h31: ¬ ∃ (u:M), u ∈ exp M n:=
        begin
          intros h32,
          have h33:= finiteexp M n hn h32,
          contradiction,
        end,
      have h34: exp M n = Λ:=
        begin
          rw full_extensionality,
          intros x,
          split,
          {
            intros h35,
            have h36:false:=
              begin
                apply h31,
                use x,
                exact h35,
              end,
            contradiction,
          },
          {
            intros h40,
            have h41:= emptyset_axiom x,
            contradiction,
          }
        end,
      contradiction,
    }
  end

lemma nonemptytoF2:  ∀ (max n:M), MAXIMAL M max → n ∈ 𝔽 →  exp M n = Λ  ∨  exp M n ∈ 𝔽:=
  begin
    intros m n hmax hn,
    have hmaximal:= hmax,
    cases hmaximal with hm h2,
    have h3:= finitetrichotomy M n hn (𝕋 M m) (Tfinite M m hm),
    cases h3 with h4 h5,
    {
      have h10:= Tonto M n m hn hm h4,
      cases h10 with k h11,
      cases h11 with hk h12,
      rw h12 at *,
      right,
      exact expTinF M  k hk,
    },
    {
      cases h5 with h15 h16,
      {
        rw h15 at *,
        right,
        exact expTinF M m hm,
      },
      {
        left,
        have h20:= Tmax M m n hmax hn h16,
        exact h20,
      }
    }
  end

lemma explambda: exp M (Λ:M) = Λ:=
  begin
    rw full_extensionality,
    intros x,
    split,
    {
      intros h,
      rw exp_members at h,
      cases h with a h2,
      cases h2 with h3 h4,
      have h5:= emptyset_axiom (USC a),
      contradiction,
    },
    {
      intros h6,
      have h7:= emptyset_axiom x,
      contradiction, 
    }
  end 


lemma Irange:  ∀ (max m:M), MAXIMAL M max → m ∈ 𝔽 →   ∀(n:M), n ∈ 𝔽  → 𝕀 M m n = Λ ∨ 𝕀 M m n ∈ 𝔽  :=
  assume max m hmax hm,
  begin
    have hmaximal:= hmax,
    unfold MAXIMAL at hmaximal,
    cases hmaximal with hmx h300,
    have base: zero ∈ Z_Irange M max m:=
      begin
        rw Z_Irange_members M max m,
        split,
        {
          exact zeroF M,
        },
        {
          right,
          rw tower_base_equation,
          exact hm,
        }
      end,
    have step: ∀(n:M), n ∈ Z_Irange M max m → (∃ (u:M), u ∈ 𝕊 n) → 𝕊 n ∈ Z_Irange M max m:=
      begin
        intros n h4 hsn,
        rw Z_Irange_members M max m at h4,
        cases h4 with hn h6,
        have h7:= successorF M n hn hsn,
        rw Z_Irange_members M max m,
        split,
        {
          exact h7,
        },
        {
          cases h6 with h20 h21,
          {
            left,
            rw tower_recursion_equation M m n hn hsn,
            rw h20,
            rw explambda,
          },
          {
            have h11:= Tmax5 M max (𝕀 M m n) hmax h21,
            have h10: 𝕀 M m n ≤ 𝕋 M max  ∨ 𝕋 M max < 𝕀 M m n:=
              begin
                have htm:= Tfinite M max hmx,
                have h301:=finitetrichotomy M ( 𝕀 M m n) h21 (𝕋 M max) htm,
                rw letolessthan M (𝕀 M m n)( 𝕋 M max ) h21 htm,
                cases h301 with h302 h303,
                {
                  left,left,
                  exact h302,
                },
                {
                  cases h303 with h304 h305,
                  {
                    left,right,
                    exact h304,
                  },
                  {
                    right,
                    exact h305,
                  }
                }
              end,
            rw h11 at h10,
            cases h10 with h20 h221,
            {
              right,
              rw tower_recursion_equation M m n hn hsn,
              exact h20,
            },
            {
              left,
              have h22:= Tmax3 M max (𝕀 M m n) hmax h21 h221,
              rw tower_recursion_equation M m n hn hsn,
              exact h22,
            }
          }
        } 
      end,
    intros n hn,
    rw F_members at hn,
    have h120:= hn (Z_Irange M max m) ⟨ base, step⟩,
    rw Z_Irange_members M max m at h120,
    exact h120.2,
  end  


lemma mplusonelessthanexpm: ∀(p:M),p ∈ 𝔽 → (¬ p = zero → ¬ p = one → exp M p ∈ 𝔽 → 𝕊 p < exp M p):=
  begin
    have base: zero ∈ Z_mplusonelessthanexpm M:=
      begin
        rw Z_mplusonelessthanexpm_members,
        split,
        {
          exact zeroF M,
        },
        {
          intros h,
          have h3: false:=
            begin
              apply h,
              simp,
            end,
          contradiction,
        }
      end,

    have step: ∀(p:M), p ∈ Z_mplusonelessthanexpm M → (∃(u:M), u ∈  𝕊 p) → 𝕊 p ∈ Z_mplusonelessthanexpm M:=
      begin
        intros p h2 hsp,
        rw Z_mplusonelessthanexpm_members,
        rw Z_mplusonelessthanexpm_members at h2,
        cases h2 with hp h3,
        split,
        {
          have h3:= successorF M p hp hsp,
          exact h3,
        },
        {
          have h4:p = one ∨ ¬ p = one:=
            begin
              have h5:=FregeNdecidable M,
              rw decidable_members at h5,
              have h6:= h5 p one ⟨ hp,oneF M⟩,
              exact h6,
            end,
          intros h9 h10 h11,
          cases h4 with h7 h8,
          {
            rw h7 at *,
            have h12:= two_definition,
            rw← h12,
            have h14:= three_lessthan_four M,
            have h15:= three_definition,
            rw← h15,
            have h16:= exp_two M,
            rw h16,
            exact h14,
          },
          {  
            have h19: ¬ p = zero:=
              begin
                intros h21,
                rw h21 at *,
                rw one_definition at h10,
                contradiction,
              end,
            have h20:= exprec M p hp h11,
            have hspf:= successorF M p hp hsp,
            have h22:= xlessthansuccessorx M p hp hspf,
            have h23:= cardinalsinhabited M (exp M (𝕊 p)) h11,
            have h25:= exporderstrict M p (𝕊 p) hp hspf h22 h23,
            
            cases h25 with h26 h27,
            have h28:= finiteexp M p hp h26,
            have h29:= h3 h19 h8 h28,
            rw h20 at h11, 
            have h40: 𝕊 p ≤  exp M p:=
              begin
                rw letolessthan M (𝕊 p)(exp M p) hspf h28,
                left,
                exact h29,
              end,
            have h30:= addorder2 M (𝕊 p)(exp M p)(𝕊 p)(exp M p) hspf h28 hspf h28 h11 h29 h40,
            have h42:= h30,
            rw←h20 at h42,
            have h43:= h42,
            rw successor_shift at h43,
            have h44:= xlessthan_xplusy M (𝕊 (𝕊 p)) p,
            have h45:= h11,
            rw←h20 at h45,
            have h50: 𝕊(𝕊 p) ∈ 𝔽 := 
              begin
                have h100:= successorF M (𝕊 p) hspf,
                apply h100,
                have h101:= (lessthan_definition (𝕊 (𝕊 p) + p)(exp M (𝕊 p))).1 h43,
                cases h101 with h102 h103,
                have h104:= le_definition ( 𝕊 (𝕊 p) + p)(exp M (𝕊 p)),
                have h105:= h104.1 h102,
                cases h105 with a h106,
                cases h106 with b h107,
                cases h107 with h108 h109,
                rw addition_members at h108,
                cases h108 with A h109,
                cases h109 with B h110,
                exact ⟨ A, h110.2.1⟩,
              end,
            have h51: 𝕊 (𝕊 p) + p ∈ 𝔽 := 
             begin
                have h101:= (lessthan_definition (𝕊 (𝕊 p) + p)(exp M (𝕊 p))).1 h43,
                cases h101 with h102 h103,
                have h104:= le_definition ( 𝕊 (𝕊 p) + p)(exp M (𝕊 p)),
                have h105:= h104.1 h102,
                cases h105 with a h106,
                cases h106 with b h107,
                cases h107 with h108 h109,
                have h110:= inhabited_sum M p hp (𝕊 (𝕊 p)) h50 ⟨ a, h108⟩,
                exact h110, 
              end,         
            have h52:= h44 h50 hp h51,
            have h60:= le_transitive3 M (𝕊(𝕊 p))(𝕊 (𝕊 p) + p)(exp M (𝕊 p)) h50 h51 h45 h52 h43,
            exact h60,                
          }
        }
      end,
    intros p hp,
    rw F_members at hp,  
    have h200:= hp (Z_mplusonelessthanexpm M) ⟨ base, step⟩,
    rw Z_mplusonelessthanexpm_members at h200,
    exact h200.2,
  end

lemma Tmsuccessor:  ∀ (m:M), MAXIMAL M m → ∃(u:M), u ∈ 𝕊 (𝕋 M m):=
  begin
    intros m hmax,
    have hmaximal:= hmax,
    unfold MAXIMAL at hmaximal,
    cases hmaximal with hm h4,
    have h214:= TmlessthanM M m hmax,
    have htm:= Tfinite M m hm,
    have h215:= noinsertions M (𝕋 M m) m htm hm h214,
    have h216:= (le_definition (𝕊 (𝕋 M m)) m).1 h215,
    cases h216 with a h217,
    cases h217 with b h218,
    cases h218 with ha h219,
    have h212: ∃(u:M), u ∈ 𝕊 (𝕋 M m):= ⟨ a, ha⟩,
    exact h212,
  end

lemma Tmplusoneneqm: ∀ (m:M), MAXIMAL M m → ¬ 𝕊  (𝕋 M m) = m:=
  begin
    intros m hmax h,
    have hmaximal:= hmax,
    unfold MAXIMAL at hmaximal,
    cases hmaximal with hm h2,
    have hTm:= Tfinite M m hm,
    have h4:= expTinF M m hm,
    have h303:= TmlessthanM M m hmax,
    have h5: ¬ 𝕋 M m = zero:= 
      begin
        intros h300,
        have h301:= Tzero M,
        rw← h301 at h300,
        have h302:= Toneone M m zero hm (zeroF M) h300, 
        rw h302 at h303,
        have h304:= xnotlessthanzero M (𝕋 M zero) (Tfinite M zero (zeroF M)),
        contradiction,
      end,
    have h6: ¬ 𝕋 M m = one := 
      begin
        intros h400,
        have h401:= Tone M,
        rw←  h401 at h400,
        have h402:= Toneone M m one hm (oneF M) h400,
        rw h402 at h2,
        have h403:= h2 two (twoF M),
        have h405:= one_lessthan_two M,
        have h406:= le_transitive2 M one two one (oneF M)(twoF M)(oneF M) h405 h403,
        have h407:= xnotlessthanx M one (oneF M),
        contradiction,
      end,
    have h7:= mplusonelessthanexpm M (𝕋 M m) hTm h5 h6 h4,
    rw h at h7,
    have h8:= h2 (exp M (𝕋 M m)) h4,
    have h9:= le_transitive2 M m (exp M (𝕋 M m)) m hm h4 hm h7 h8,
    have h10:= xnotlessthanx M m hm,
    contradiction,
  end



lemma offtheend:  ∀ (m:M), MAXIMAL M m →
∀ (p:M), p ∈ 𝔽 → 𝕀 M p m = Λ:= 
  begin
    intros m hmax p hp,
    have hmax2:= hmax,
    unfold MAXIMAL at hmax2,
    cases hmax2 with hm h3,
    have h4:= towerincreasing M p hp m hm,
    have htm:= Tfinite M m hm,
    have h5: ¬ m = zero:=
      begin
        intros h300,
        rw h300 at h3,
        have h301:= h3 two (twoF M),
        have h302:= zero_lessthan_two M,
        have h303:= le_transitive2 M zero two zero (zeroF M)(twoF M)(zeroF M) h302 h301,
        have h304:= xnotlessthanx M zero (zeroF M),
        contradiction,
      end,
    have h6: ¬ 𝕋 M m = zero:=
      begin
        intros h7,
        have h8:= Tzero M,
        rw← h7 at h8,
        have h9:= Toneone M (𝕋 M m) m htm hm h8,
        have h10:= TmlessthanM M m hmax,
        rw h9 at h10,
        have h11:= xnotlessthanx M m hm,
        contradiction,
      end,
    have h12:= nonzeroissuccessor M m hm h5,
    cases h12 with q h13,
    cases h13 with hq h14,
    have h15:= Irange M m p hmax hp m hm,
    cases h15 with h16 h17,
    {
      exact h16,
    },
    {
      have h18:= Irange M m p hmax hp q hq,
      have h210:= cardinalsinhabited M m hm,
      cases h18 with h19 h20,
      {
        have h21:= explambda M,
        rw h14 at h210,
        have h22:= tower_recursion_equation M p q hq h210,
        have h23: 𝕀 M p m = Λ:=
          begin
            rw← h14 at h22,
            rw  h19 at h22,
            rw h21 at h22,
            exact h22,
          end,
        rw h23 at *,
      },
      { 
        have h29:= h210,
        rw h14 at h29,
        have h30:= tower_recursion_equation M p q hq h29,
        have h31:= cardinalsinhabited M (𝕀 M p q) h20,
        have h32:= towerincreasing M p hp q hq h31,
        have h33:= mlessthanexpm M (𝕀 M p q) h20,
        have h34:= h17,
        rw h14 at h34,
        have h35:= cardinalsinhabited M (𝕀 M p (𝕊 q)) h34,
        rw h30 at h35,
        have h36:= h33 h35,
        have h39:= h34,
        rw  h30 at h39,
        have h38:= le_transitive3 M q (𝕀 M p q)(exp M (𝕀 M p q)) hq h20 h39 h32 h36,
        have h40:= noinsertions M q (exp M (𝕀 M p q)) hq h39 h38,
        have h41:= h40,
        rw← h30 at h41,
        have h42:= h41,
        rw← h14 at h42,
        have h43:= h3 (𝕀 M p m) h17,
        have h44:= finitetrichotomy2 M m (𝕀 M p m) hm h17 h42 h43,
        have h45:= h44,
        have h46:= h30,
        rw←h14 at h46,
        rw h46 at h45,
        have h47:= (Tmax5 M m (𝕀 M p q) hmax h20).2 h39,
        have h211:= h210,
        have h48:= le_transitive M q  (𝕋 M m) (𝕀 M p q) hq htm h20 h32 h47,
        rw h14 at h211,  
        have h212:= Tmsuccessor M m hmax, 
        have h213: 𝕊 (𝕋 M m) ∈ 𝔽 := successorF M (𝕋 M m) htm h212,
        have h50:= (ordersuccessor M q (𝕋 M m) hq htm h212).1 h48,
        have h51:= h50,
        rw←  h14 at h51,
        have h52:= h3 (𝕊 (𝕋 M m)) h213,
        have h53:= finitetrichotomy2 M m  (𝕊 (𝕋 M m)) hm h213 h51 h52,
        have h54:= Tmplusoneneqm M m hmax,
        rw← h53 at h54,
        contradiction,
      }
    }   
  end

lemma Phifinite:  ∀ (max:M), MAXIMAL M max→ ∀ (p:M), p ∈ 𝔽 → Φ M p ∈ FINITE M:=
  begin
    intros max hmax p hp,
    have hF:= maximalfiniteF M max hmax,
    have h180:= Irange M max p hmax hp,
    have h3: maps M (gphi M p) 𝔽 (𝔽 ∪ single Λ) :=
      begin
        unfold maps,
        repeat{split},
        {
          rw Rel_definition,
          intros z hz,
          rw gphi_members at hz,
          cases hz with a h4,
          cases h4 with b h5,
          cases h5 with h6 h7,
          use a, use b,
          exact h6,
        },
        {
          intros x y h8,
          cases h8 with hx h9,
          rw gphi_members at h9,
          cases h9 with a h10,
          cases h10 with b h11,
          cases h11 with h12 h13,
          rw ordered_pair_equality at h12,
          rw h12.1 at *,
          rw h12.2 at *,
          rw binary_union_axiom,
          rw singleton1,
          rw←h13.2,
          have h181:= h180 a hx,
          rw or_comm,
          exact h181, 
        },
        {
          intros x y z h200,
          cases h200 with hx h201,
          cases h201 with h202 h203,
          rw gphi_members at h202 h203,
          cases h202 with a h204,
          cases h204 with b h205,
          cases h203 with A h206,
          cases h206 with B h207,
          rw ordered_pair_equality at h205 h207,
          cases h207 with h208 h209,
          cases h205 with h210 h211,
          rw h210.1 at *,
          rw h210.2 at *,
          rw h208.1 at *,
          rw h208.2 at *,
          rw←h209.2,
          rw←h211.2, 
        },
        {
          intros x hx,
          simp_rw gphi_members,
          use 𝕀 M p x,
          split,
          {
            have h181:= h180 x hx,
            cases h181 with h182 h183,
            {
              rw h182,
              rw binary_union_axiom,
              right,
              rw singleton1,
            },
            {
              rw binary_union_axiom,
              left,
              exact h183,
            }
          },
          {
            use x,
            use 𝕀 M p x,
            simp,
            exact hx,
          }
        }
      end,
    have h99:= lambdanotinF M,
    have h100: 𝔽 ∪ (single Λ) ∈ FINITE M:=
      begin
        have h101:= finite_adjoin M 𝔽 Λ ⟨ hF, h99⟩,
        exact h101,
      end,
    have h110:= h3,
    unfold maps at h110,
    cases h110 with hrel h111,
    have h102: dom (gphi M p) = 𝔽:=
      begin
        have h103:= domain_axiom (gphi M p) hrel,
        rw full_extensionality,
        intros x,
        specialize h103 x,
        rw h103,
        split,
        {
          intros h112,
          cases h112 with y h113,
          rw gphi_members at h113,
          cases h113 with a h114,
          cases h114 with b h115,
          cases h115 with h116 h117,
          rw ordered_pair_equality at h116,
          rw h116.1 at *,
          rw h116.2 at *,
          exact h117.1,
        },
        {
          intros hx,
          use (𝕀 M p x),
          rw gphi_members,
          use x, use (𝕀 M p x),
          simp,
          exact hx,
        }
      end, 
    have h4:= decidable_image M 𝔽 (𝔽 ∪ single Λ) (gphi M p) hF h100 h3 h102 hrel,
    set theImage:= range (gphi M p) with Imagedef,
    cases h111 with h112 h113,
    cases h113 with h114 h115,
    have h400: theImage ∈ FINITE M:=
      begin
        have h401:= separablefinite M (𝔽 ∪ single Λ ) h100 theImage,
        apply h401,
        {
          rw subset_definition,
          intros x,
          intros hx,
          rw Imagedef at hx,
          rw range_axiom (gphi M p) hrel at hx,
          cases hx with a h402,
          have h403:= h112 a x,
          apply h403,
          have h404:= h402,
          rw gphi_members at h404,
          cases h404 with A h405,
          cases h405 with B h406,
          cases h406 with h407 h408,
          rw ordered_pair_equality at h407,
          rw h407.1 at *,
          rw h407.2 at *,
          exact ⟨ h408.1, h402⟩,  
        },
        {
          unfold separable_subset,
          split,
          {
            rw subset_definition,
            intros z hz,
            rw Imagedef at hz,
            rw range_axiom (gphi M p) hrel  at hz,
            cases hz with x h420,
            have h421:= h420,
            rw gphi_members at h421,
            cases h421 with A h422,
            cases h422 with B h423,
            cases h423 with h424 h425,
            rw ordered_pair_equality at h424,
            rw h424.1 at *,
            rw h424.2 at *,
            have h426:= h112 A B ⟨ h425.1, h420⟩,
            exact h426,
          },
          {
            rw full_extensionality,
            intros x,
            split,
            {
              intros h500,
              rw binary_union_axiom,
              rw Imagedef,
              rw range_axiom (gphi M p),
              have h501:= h4 x h500,
              cases h501 with h502 h503,
              {
                left,
                cases h502 with u h504,
                use u,
                exact h504.2,
              },
              {
                right,
                rw minus_members,
                split,
                {
                  exact h500,
                },
                {
                  intros h505,
                  apply h503,
                  rw range_axiom at h505,
                  cases h505 with a h506,
                  use a,
                  have h507:= h506,
                  rw gphi_members at h507,
                  cases h507 with A h508,
                  cases h508 with B h509,
                  rw ordered_pair_equality at h509,
                  cases h509 with h510 h511,
                  rw h510.1 at *,
                  rw h510.2 at *,
                  exact ⟨h511.1, h506⟩,
                  exact hrel, 
                }
              },
              {
                exact hrel,
              }
            },
            {
              intros h600,
              rw binary_union_axiom at h600,
              cases h600 with h601 h602,
              {
                rw Imagedef at h601,
                rw range_axiom at h601,
                cases h601 with a h604,
                have h605:= h112 a x,
                apply h605,
                have h606:= h604,
                rw gphi_members at h606,
                cases h606 with A h607,
                cases h607 with B h608,
                cases h608 with h609 h610,
                rw ordered_pair_equality at h609,
                rw h609.1 at *,
                rw h609.2 at *,
                exact ⟨ h610.1, h604⟩,
                exact hrel,
              },
              {
                rw minus_members at h602,
                exact h602.1,
              }
            }
          }
        }
      end,
    have h700: Φ M p = theImage - single (Λ:M) :=
      begin
        rw full_extensionality,
        intros x,
        split,
        {
          intros h701,
          rw minus_members,
          rw Phi_members at h701,
          --cases h701 with hx h703,
          --cases h703 with y h704,
          --cases h704 with hy h705,
          cases h701 with y h702,
          cases h702 with hy h703,
          cases h703 with h704 h705,
          have h705copy:= h705,
          cases h705copy with b hb,

          rw h704 at *,
          split,
          {
            rw Imagedef,
            rw range_axiom (gphi M p) hrel,
            use y,
            rw gphi_members,
            use y, use 𝕀 M p y,
            simp,
            exact hy,
          },
          {
            rw singleton1,
            intros h707,
            rw h707 at *,
            have h708:= emptyset_axiom b,
            contradiction,
          }
        },
        {
          intros h800,
          rw Phi_members,
          rw minus_members at h800,
          cases h800 with h801 h802,
          rw singleton1 at h802,
          rw Imagedef at h801,
          rw range_axiom (gphi M p) hrel at h801,
          cases h801 with A h804,
          rw gphi_members at h804,
          cases h804 with a h805,
          cases h805 with b h806,
          cases h806 with h807 h808,
          rw ordered_pair_equality at h807,
          rw h807.1 at *,
          rw h807.2 at *,
          cases h808 with h809 h810,
          use a,
          split,
          { 
            exact h809,
          },
          {
            split,
            {
              rw sym,
              exact h810,
            },
            {
              rw← h810,
              have h820:= h180 a h809,
              cases h820 with h821 h822,
              {
                rw h810 at h821,
                contradiction,
              },
              {
                exact cardinalsinhabited M (𝕀 M p a) h822,
              }
            }
          }
        }
      end,
  
    have h900:= finitedif M theImage (single Λ) h400,
    rw h700,
    apply h900,
    exact singletons_finite M Λ,
    rw subset_definition,
    intros x hx,
    rw singleton1 at hx,
    rw hx at *,
    rw Imagedef,
    rw range_axiom (gphi M p) hrel,
    use max,
    rw gphi_members,
    use max, use Λ,
    simp,
    unfold MAXIMAL at hmax,
    split,
    {
      exact hmax.1,
    },
    {  
      exact offtheend M max hmax p hp,
    } 
  end    

lemma mneqexpm: ∀ (m:M), m ∈ 𝔽 → ¬ m = exp M m:=
  begin
    intros m hm,
    intros h17,
    have h19:= cardinalsinhabited M m hm,
    rw h17 at h19,
    have h16:= mlessthanexpm M m hm h19,
    rw← h17 at h16, 
    have h22:= xnotlessthanx M m hm,
    contradiction,
  end 


lemma sixpointtwo_helper:  ∀ (m:M), m ∈ 𝔽 → exp M m= Λ → ∀(p:M), p ∈ 𝔽 → (𝕊 p ∈ 𝔽  →  𝕀 M m (𝕊 p) = Λ):= 
  assume m hm hexpm,  
  begin
    have base: zero ∈  Z_sixpointtwo M m:=
      begin
        rw Z_sixpointtwo_members M m, 
        have h3:= tower_base_equation M m,
        have h4:= tower_recursion_equation M m zero (zeroF M),
        rw h3 at *,
        rw hexpm at *,
        split,
        {
          exact zeroF M,
        },
        { intros h10,
          apply h4,
          rw← one_definition ,
          exact cardinalsinhabited M one (oneF M),
        }
      end,
    have step: ∀(p:M), p ∈ Z_sixpointtwo M m → (∃(v : M), v ∈ 𝕊 p)→  𝕊 p ∈ Z_sixpointtwo M m:=
      begin
        intros p h10 h20,
        rw Z_sixpointtwo_members M m  at h10,
        rw Z_sixpointtwo_members M m,
        cases h10 with hp h12,
        have h21:= successorF M p hp h20,
        have h22:= h12 h21,
        have h13:= tower_recursion_equation M m (𝕊 p )  h21,
        simp_rw h22 at *,
        have h14: exp M Λ = Λ:= explambda M,
        rw h14 at *,
        split,
        {
          exact h21,
        },
        {
          intros h22,
          have h23:= cardinalsinhabited M (𝕊 (𝕊 p)) h22,
          exact h13 h23,
        }
      end,
    intros p hp,
    rw F_members at hp,
    specialize hp (Z_sixpointtwo M m),
    have h200:= hp ⟨ base, step⟩, 
    rw Z_sixpointtwo_members M m at h200,
    exact h200.2,
  end  

lemma sixpointtwo: ∀ (m:M), m ∈ 𝔽 → exp M m= Λ → Φ M m = single m:=
  begin
    intros m hm h3,
    rw full_extensionality,
    intros n,
    split,
    {
      intros h4,
      have h4copy := h4,
      rw Phi_members at h4,
      cases h4 with k h5,
      cases h5 with hk h21,
      cases h21 with h22 h23,
      have h23copy:= h23,
      cases h23copy with b h24,
      rw h22 at h23,
      rw singleton1,
      
      have h40:= towerF M m hm k hk h23,
      have hn:= h40,
      rw← h22 at hn,
      have h6:= sixpointfour M m n hm hn h4copy,
      -- cases h5 with k h8,
      -- cases h8 with hk h7,
    
      have h8: k = zero ∨ ¬ k = zero:=
        begin
          have h9:= FregeNdecidable M,
          rw decidable_members M at h9,
          have h10:= h9 k zero ⟨ hk, zeroF M⟩,
          exact h10,
        end,
      cases h8 with h11 h12,
      {
        rw h11 at *,
        have h12:=tower_base_equation M m,
        rw h12 at *,
        exact h22,
      },
      {
        have h13:= nonzeroissuccessor M k hk h12,
        cases h13 with p h14,
        cases h14 with hp h15,
        rw h15 at *,
        have h16:= cardinalsinhabited M (𝕊 p) hk,
        have h17:= tower_recursion_equation M m p hp h16,
        have h18:= sixpointtwo_helper M m hm h3 p hp hk,
        rw h18 at *,
        rw h22 at *,
        have h30:= cardinalsinhabited M Λ hn,
        cases h30 with q h31,
        have h32:= emptyset_axiom q,
        contradiction,
      }
    },
    {
      rw singleton1,
      intros h40,
      rw h40 at *,
      have h41:= cardinalsinhabited M m hm,
      exact minPhim M m h41,
    }  
  end

lemma oneequalsxplusone: ∀ (x:M), x ∈ 𝔽 → (∃(u:M), u ∈ 𝕊 x) →one = x + one → x = zero:=
  begin
    intros x hx hsx h3,
    rw one_definition at h3,
    rw successor_shift at h3,
    rw right_identityNF at h3,
    have h5: exists(u:M),u ∈ 𝕊 zero:=
      begin
        rw← one_definition,
        exact cardinalsinhabited M one (oneF M),
      end,
    have h4:= successoroneone M zero x (zeroF M) hx h5 hsx,
    rw← h4 at h3,
    rw sym M,
    exact h3,    
  end

lemma ncsingleton: ∀ (x:M), Nc M (single x) = one:=
 begin
   intros x,
   rw full_extensionality,
   intros t,
   rw one_members,
   have h3:= finitecardinals0 M,
   have h4:= finitecardinals2 M,
   have h5:= Nc_members M,
   rw h5 (single x) t,
   have h6:= similar_to_singleton M,
   split,
   {
     intros h10,
     exact h6 t x h10,
   },
   {
     intros h11,
     cases h11 with a h12,
     rw h12,
     have h13:=similar_singletons M a x,
     exact h13,
   }
 end

lemma monotonicity: ∀ (m:M), MAXIMAL M m → ∀(p:M), 
  p ∈ 𝔽 → ∀ (a b:M), a ∈ 𝔽 → b ∈ 𝔽 →   Nc M (Φ M a) = p→ a ≤ b → Nc M (Φ M b) ≤  p :=
  begin
    intros m hmax,
    have hmaximal:= hmax,
    unfold MAXIMAL at hmaximal,
    cases hmaximal with hm h4,
    have base: (zero:M) ∈ Z_monotonicity M m:=
      begin
        rw  Z_monotonicity_members M,
        split,
        {
          exact zeroF M,
        },
        {
          intros a b ha hb h5 hab,
          have h6:= minPhim M a (cardinalsinhabited M a ha),
          have h7:= xinNcx M (Φ M a),
          rw h5 at h7,
          rw zero_members at h7,
          have h8:= emptyset_axiom a,
          rw h7 at *,
          contradiction,
        }
      end, 
    have step: ∀ (p:M), p ∈ Z_monotonicity M m → (∃ (u:M), u ∈ 𝕊 p)  → 𝕊 p ∈ Z_monotonicity M m:=
      begin
        intros p h5 hsp,
        rw Z_monotonicity_members at h5,
        rw Z_monotonicity_members,
        cases h5 with hp h6,
        split,
        {
          exact successorF M p hp hsp,
        },
        {
          intros A B hA hB h7 hAB,
          have h8:= Phifinite M m hmax A hA,
          have h9:= Phifinite M m hmax B hB,
          have h10:= finitecardinals3 M (Φ M A) h8,
          have h11:= finitecardinals3 M (Φ M B) h9,
          have h12:= finitetrichotomy M p hp one (oneF M),
          have h13: p < one ∨ one ≤ p:=
            begin
              have h14:= letolessthan M one p (oneF M) hp,
              rw h14,
              cases h12 with h15 h16,
              {
                left, exact h15,
              },
              {
                cases h16 with h17 h18,
                { rw h17 at *,
                  right,
                  right,
                  refl,
                },
                {
                  right,left,
                  exact h18,
                }
              }
            end,
          cases h13 with h14 h15,
          {
            -- case p < one
            have h16:= lessthanone M p hp h14,
            have h17: Nc M (Φ M A) = (one:M):=
              begin
                rw h7,
                have h18:= one_definition,
                rw h18,
                rw h16,  
              end,
            have h20:= xinNcx M (Φ M A),
            have h21:= h20,
            rw h17 at h20,
            have h21:= h20,
            rw one_members at h21,
            cases h21 with c h22,
            have h23:= minPhim M A (cardinalsinhabited M A hA),
            have h24:= h23,
            rw h22 at h24,
            rw singleton1 at h24,
            rw←  h24 at *,
            have h25:=  mneqexpm M A hA,
            have h26:= nonemptytoF2 M m B hmax hB,
            cases h26 with h27 h28,
            {
              have h29:= sixpointtwo M B hB h27,
              have h30:= xinNcx M (Φ M B),
              have h31:= (one_members M (single B)).2 ⟨ B, refl (single B)⟩ ,
              have h32:= h31,
              rw←  h29 at h32,
              have h33:= finitecardinals3 M (Φ M B) h9,
              have h34:= cardinalsdisjoint M (Nc M (Φ M B)) one (Φ M B) h33 (oneF M),
              have h35: Nc M (Φ M B) = one:=
                begin
                  apply h34,
                  rw intersection_axiom,
                  exact ⟨h30, h32⟩,
                end,
              rw h35,
              rw h16,
              rw← one_definition,
              exact le_reflexive M one (oneF M),
            },
            {
              have h38:= cardinalsinhabited M (exp M B) h28,
              have h40:= exporder M A B hA hB hAB h38,
              have h42:= sixpointseven M B hB h9 h38,
              cases h40 with h43 h44,
              have h45:= finiteexp M A hA h43,
              rw h16 at *,
              have h46:= sixpointseven M A hA h8 h43,
              have h46copy:= h46,
              have h51:= lessthanone M,
              rw← one_definition at *,
              rw h7 at h46,
              have h146:= Phifinite M m hmax (exp M A) h45,
              have h147:= finitecardinals3 M (Φ M (exp M A)) h146,
              have h48:= minPhim M (exp M A) (cardinalsinhabited M (exp M A) h45),
              have h49: ¬ Nc M (Φ M (exp M A)) = zero:=
                begin
                  intros h50,
                  have h51:= xinNcx M (Φ M (exp M A)),
                  rw h50 at h51,
                  rw zero_members at h51,
                  rw h51 at h48,
                  have h52:= emptyset_axiom (exp M A),
                  contradiction,
                end,
              have h55:= finitecardinals3 M  (Φ M (exp M A)),
              have h53: false:=
                begin
                  apply h49,
                  have h54:= oneequalsxplusone M (Nc M (Φ M (exp M A))) h147,
                  apply h54,
                  simp_rw successorisplusone,
                  simp_rw← h46copy,
                  exact cardinalsinhabited M (Nc M (Φ M A)) h10,
                  exact h46,
                end,
              contradiction,
            },
          },
          {
            -- case 2, one ≤ p 
            have hsp:= h10,
            rw h7 at hsp, 
            have h60:= cardinalsinhabited M (𝕊 p) hsp,
            have h61:= (ordersuccessor M one p (oneF M) hp h60).1  h15,
            have h62:= h61,
            rw← two_definition at h62,
            have h63:= minPhim M A (cardinalsinhabited M A hA),
            have h64:= nonemptytoF2 M m A hmax hA,
            cases h64 with h2a h2b,
            { --case 2a
              have h65:= sixpointtwo M A hA h2a,
              have h66: Nc M (Φ M A) = one:=
                begin
                  rw h65,
                  have h66:= ncsingleton M A,
                  exact h66,
                end,
              have h67: two ≤ Nc M(Φ M A):=
                begin
                  rw← h7 at h62,
                  exact h62,
                end,
              have h68:= h67,
              rw h66 at h68,
              have h69:= one_lessthan_two M,
              have h70:= le_transitive2 M one two one (oneF M)(twoF M)(oneF M) h69 h68,
              have h71:= xnotlessthanx M one (oneF M),
              contradiction,
            },
            { --case 2b
              have h79:= Phifinite M m hmax (exp M A) h2b,
              have h78:= finitecardinals3 M  (Φ M (exp M A)) h79,
              have h80:= cardinalsinhabited M (exp M A) h2b,
              have h81:= sixpointsix M A hA h80,
              have h82:= sixpointseven M A hA h8 h80,
              have h83:= h82,
              rw←  successorisplusone at h83,
              have h84:= successoroneone M (Nc M (Φ M (exp M A))) p h78 hp,
              have h85:= h10,
              rw h83 at h85,
              have h86:= cardinalsinhabited M ( 𝕊 (Nc M (Φ M (exp M A)))) h85,
              have h87:= h84 h86 h60,
              have h88: 𝕊 (Nc M (Φ M (exp M A))) = 𝕊 p :=
                begin
                  rw← h83,
                  rw← h7,
                end,
              rw← h87 at h88,
              have h91:= nonemptytoF2 M m B hmax hB,
              cases h91 with h92 h93,
              {  --case exp M B = Λ 
                have h100:= sixpointtwo M B hB h92,
                rw h100,
                have h101:= ncsingleton M B,
                rw h101,
                rw one_definition,
                have h102:= ordersuccessor M zero p (zeroF M) hp h60,
                rw← h102,
                have h103:= zero_le_x M p hp,
                exact h103,
              },
              { -- case exp M B ∈ 𝔽  
                have h108:= cardinalsinhabited M (exp M B) h93,
                have h109:= exporder M A B hA hB hAB h108,
                cases h109 with h110 h111,
                have h90:= h6 (exp M A) (exp M B) h2b h93 h88 h111,
                have h112:= Phifinite M m hmax (exp M B) h93,
                have h113:= finitecardinals3 M (Φ M (exp M B)) h112,
                have h120:= ordersuccessor M (Nc M (Φ M (exp M B))) p h113 hp h60,
                rw h120 at h90,
                have h121:= sixpointseven M B hB h9 h108,
                rw← successorisplusone at h121,
                have h122:= h90,
                rw← h121 at h122,
                exact h122,
              }
            },
          }
        }
      end,
    intros p hp,
    rw F_members at hp,
    have h300:= hp (Z_monotonicity M m) ⟨ base, step⟩,
    rw Z_monotonicity_members at h300,
    exact h300.2,
  end

lemma Phione: ∀(m:M), m ∈ 𝔽 → exp M m = Λ → Nc M (Φ M m) = one:=
  begin
    intros m hm h2,
    have h3:= sixpointtwo M m hm h2,
    have h4:= xinNcx M (single m),
    have h5: single m ∈ one :=
      begin
        have h6:= one_members M (single m),
        rw h6,
        use m,
      end,
    have h20:= singletons_finite M m,
    have h21:= finitecardinals3 M (single m) h20,
    have h7:= cardinalsdisjoint M  (Nc M (single m)) one (single m)  h21 (oneF M),
    rw h3,
    apply h7,
    rw intersection_axiom,
    exact ⟨ h4, h5⟩, 
  end   

lemma Phitwo: ∀ (max m:M), MAXIMAL M max → m ∈ 𝔽 →    exp M (exp M (𝕋 M m)) = Λ  → Nc M (Φ M (𝕋 M m)) = two:=
  begin
    intros max m hmax hm h3,
    have h4:= expTinF M m hm,
    have h5:= sixpointtwo M (exp M (𝕋 M m)) h4 h3,
    have hTm:= Tfinite M m hm,
    have h6:= expTinhabited M m hm,
    have h7:= sixpointsix M (𝕋 M m) hTm h6,
    rw h5 at h7,
    have h8: Φ M (𝕋 M m) = { 𝕋 M m, exp M (𝕋 M m)}:=
      begin
        rw full_extensionality,
        intros x,
        rw h7,
        rw binary_union_axiom,
        repeat{ rw singleton1},
        rw pairing_axiom,  
      end,
    have h9: Φ M (𝕋 M m) ∈ two:=
      begin
        rw two_members,
        use (exp M (𝕋 M m)),
        use (𝕋 M m),
        split,
        {
          have h9:= mneqexpm  M (𝕋 M m) hTm,
          intros h10,
          rw h10 at h9,
          apply h9,
          simp,
        },
        { 
          rw h8,
          rw full_extensionality,
          intros x,
          repeat{rw pairing_axiom},
          rw or_comm,
        }
      end, 
    have h10:= xinNcx M ( Φ M (𝕋 M m)),
    have h12:= finitecardinals1 M two (Φ M (𝕋 M m)) (twoF M) h9,
    have h13:= finitecardinals3 M (Φ M (𝕋 M m)) h12,
    have h11:=cardinalsdisjoint M (Nc M (Φ M (𝕋 M m))) two (Φ M (𝕋 M m)) h13 (twoF M),
    apply h11,
    rw intersection_axiom,
    exact ⟨ h10, h9⟩, 
  end       


lemma Phithree: ∀ (m n:M), MAXIMAL M m → n ∈ 𝔽 →    exp M (exp M (exp M (𝕋 M n))) = Λ  → ¬ Nc M (Φ M (𝕋 M n)) = two → Nc M (Φ M (𝕋 M n)) = three:=
  begin
    intros m n hm hn h3 hnottwo,
    have h4:= expTinF M n hn,
    have h100: ¬ exp M (exp M (𝕋 M n)) = Λ:=
      begin 
        have h101:= Phitwo M m n hm hn,
        intros h102,
        have h103:= h101 h102,
        contradiction,
      end,
    have hTn:= Tfinite M n hn,
    have h6:= expTinhabited M n hn,
    have h103: exp M (exp M (𝕋 M n)) ∈ 𝔽 := 
      nonemptytoF M m (exp M (𝕋 M n)) hm h4 h100,
    have h104:= cardinalsinhabited M (exp M (exp M (𝕋 M n))) h103,
    have h7:= sixpointsix M (𝕋 M n) hTn h6,
    have h5:= sixpointsix M (exp M (𝕋 M n)) h4 h104,
    rw h5 at h7,
    have h105:= sixpointtwo M (exp M (exp M (𝕋 M n))) h103 h3,
    rw h105 at *,
    have h8: (single  (𝕋 M n)) ∪ (single  (exp M (𝕋 M n))) = { 𝕋 M n, exp M (𝕋 M n)}:=
      begin
        rw full_extensionality,
        intros x,
        rw binary_union_axiom,
        repeat{ rw singleton1},
        rw pairing_axiom,
      end,
    have h9: { 𝕋 M n, exp M (𝕋 M n)} ∈ two:=
      begin
        rw two_members,
        use (𝕋 M n),
        use (exp M (𝕋 M n)),
        split,
        {
          exact mneqexpm  M (𝕋 M n) hTn,
        },
        { 
          simp,
        }
      end, 
    have h10:= xinNcx M ( Φ M (𝕋 M m)),
    have h11: Φ M (𝕋 M n) =  ({ 𝕋 M n, exp M (𝕋 M n)} ∪ (single  (exp M (exp M (𝕋 M n))))):=
      begin  
        rw full_extensionality,
        intros x,
        rw h7,
        repeat{rw binary_union_axiom},
        repeat{rw singleton1},
        rw pairing_axiom,
        rw or_assoc,
      end,
    have h12: ¬ (exp M (exp M (𝕋 M n)) ∈ { 𝕋 M n, exp M (𝕋 M n)}):=
      begin
        intros h13,
        rw pairing_axiom at h13,
        cases h13 with h14 h15,
        { 
          have h15:= mlessthanexpm M (𝕋 M n) hTn h6,
          have h16:= mlessthanexpm M (exp M (𝕋 M n)) h4 h104,
          have h17:= lessthan_transitive M (𝕋 M n)(exp M (𝕋 M n))(exp M (exp M (𝕋 M n))) hTn h4 h103 h15 h16,
          rw h14 at h17,
          have h18:= xnotlessthanx M (𝕋 M n) hTn,
          contradiction,
        },
        {
          have h19:= mneqexpm M (exp M (𝕋 M n)) h4,
          rw h15 at h19,
          apply h19,
          simp,
        }
      end,
    have h20: Φ M (𝕋 M n) ∈ 𝕊 two:=
      begin
        rw successor_members,
        use {𝕋 M n,exp M (𝕋 M n)},
        use exp M (exp M (𝕋 M n)),
        repeat{split},
        {
          exact h9,
        },
        {
          exact h12,
        },
        {
          exact h11,
        }
      end,
    rw← three_definition at h20,
    have h21:= xinNcx M (Φ M (𝕋 M n)), 
    have h22: Φ M (𝕋 M n) ∈ FINITE M:=
      begin
        rw h7,
        have h100:= union M,
        apply h100,
        {
          exact singletons_finite M (𝕋 M n),
        },
        {
          apply h100,
          {
            exact singletons_finite M (exp M (𝕋 M n)),
          },
          {
            exact singletons_finite M (exp M (exp M (𝕋 M n))),
          },
          {
            rw full_extensionality,
            intros x,
            rw intersection_axiom,
            repeat{ rw singleton1},
            split,
            {
              intros h101,
              cases h101 with h103 h104,
              rw h103 at *,
              have h104:= mneqexpm M (exp M (𝕋 M n)) h4,
              contradiction,
            },
            {
              intros h105,
              have h106:= emptyset_axiom x,
              contradiction,
            }
          }
        },
        {
          rw full_extensionality,
          intros x,
          rw intersection_axiom,
          rw binary_union_axiom,
          repeat{rw singleton1},
          split,
          {
            intros h110,
            cases h110 with h111 h112,
            rw h111 at *,
            cases h112 with h113 h114,
            {
              have h115:= mneqexpm M(𝕋 M n) hTn,
              contradiction,
            },
            {
              rw← h114 at h12,
              rw pairing_axiom at h12,
              have h120: false:=
                begin
                  apply h12,
                  left,
                  simp,
                end,
              contradiction,
            }
          },
          {
            intros h130,
            have h131:= emptyset_axiom x,
            contradiction,
          }
        }
      end,
    have h23:= finitecardinals3 M (Φ M (𝕋 M n)) h22,
    have h24:=cardinalsdisjoint M (Nc M (Φ M (𝕋 M n))) three (Φ M (𝕋 M n)) h23 (threeF M),
    apply h24,
    rw intersection_axiom,
    exact ⟨ h21, h20⟩, 
  end  

lemma finitenotfinite3:  (¬ 𝕍 ∈ FINITE M) →  ∀ (X:M), USC 𝕍 ⊆ FINITE M - X →
 ¬( FINITE M - X ∈ FINITE M):=
  begin
    intros hv X h4 h5,
    have h107: ∀ (x:M), x ∈ FINITE M → Nc M x ∈ 𝔽 :=
      begin
        intros x h,
        have h8:= finitecardinals3 M x h,
        exact h8,
      end, 
    have h109:= FregeNdecidable M,
    rw decidable_members at h109,
    have h110: ∀ (x:M), x ∈ FINITE M → Nc M x = one ∨ ¬ Nc M x = one:=
      begin
        intros x h,
        have h111:=  h107 x h,
        have h112:= h109 (Nc M x) one ⟨ h111, oneF M⟩,
        exact h112,
      end,
    have h200:= singletons_finite M,
    have h201: USC 𝕍 ⊆ FINITE M:=
      begin
        rw subset_definition,
        intros z hz,
        rw usc at hz,
        cases hz with a h202,
        cases h202 with h203 h204,
        rw h204,
        exact singletons_finite M a,
      end,
      
    have h113:= Ncone M,
    simp_rw← h113 at h110,
    have h120: USC 𝕍 ∈ SSC(FINITE M - X):=
      begin
        rw ssc_members,
        split,
        { 
          exact h4,
        },
        {
          intros t ht,
          rw minus_members at ht,
          cases ht with h112 h113,
          have h111:= h110 t h112,
          exact h111,
        }
      end,
    have h135:= separablefinite M (FINITE M -X) h5 (USC 𝕍) h4,
    unfold separable_subset at h135,
    have h140: USC 𝕍 ∈ FINITE M:=
      begin
        apply h135,
        split,
        {
          exact h4,
        },
        {
          rw full_extensionality,
          intros t,
          split,
          {
            intros h150,
            rw minus_members at h150,
            cases h150 with h151 h152,
            have h153:= h110 t h151,
            rw binary_union_axiom,
            cases h153 with h154 h155,
            {
              left,
              exact h154,
            },
            {
              right,
              rw minus_members,
              split,
              {
                rw minus_members,
                exact ⟨ h151,h152⟩,
              },
              {
                exact h155,
              }
            }
          },
          {
            intros h160,
            rw binary_union_axiom at h160,
            cases h160 with h161 h162,
            rw minus_members,
            rw usc at h161,
            cases h161 with a h162,
            rw h162.2,
            split,
            {
              exact singletons_finite M a,
            },
            {
              intros h164,
              have h165: single a ∈ USC 𝕍:=
                begin
                  rw usc,
                  use a,
                  simp,
                  exact h162.1,
                end,
              have h166:= member_subset M (USC 𝕍)(FINITE M -X) (single a) h4 h165,
              rw minus_members at h166,
              cases h166 with h167 h168,
              contradiction,
            },
            {
              rw minus_members at h162,
              exact h162.1,
            }
          }
        }
      end,
    rw uscfinite at h140,
    contradiction,
  end

lemma Timageunion: ∀(X Y:M), imageT M (X ∪ Y) = (imageT M X ∪ imageT M Y):=
  begin
    intros X Y,
    rw full_extensionality,
    intros t,
    split,
    {
      intros h3,
      rw imageT_members M (X ∪ Y) at h3,
      cases h3 with u h4,
      cases h4 with h5 h6,
      rw binary_union_axiom at h5,
      rw binary_union_axiom,
      cases h5 with h8 h7,
      {
        left,
        rw imageT_members M X,
        use u,
        exact ⟨ h8, h6⟩,
      },
      {
        right,
        rw imageT_members M Y,
        use u,
        exact ⟨ h7,h6⟩,
      }
    },
    {
      intros h30,
      rw binary_union_axiom at h30,
      rw imageT_members M (X ∪ Y),
      cases h30 with h31 h41,
      {
        rw imageT_members M X at h31,
        cases h31 with u h32,
        use u,
        cases h32 with h33 h34,
        rw binary_union_axiom,
        split,
        {
          left,
          exact h33,
        },
        {
          exact h34,
        }
      },
      {
        rw imageT_members M Y at h41,
        cases h41 with u h42,
        use u,
        cases h42 with h43 h44,
        rw binary_union_axiom,
        split,
        {
          right,
          exact h43,
        },
        {
          exact h44,
        }
      }
    }
  end

lemma ToneoneNC: ∀ (n m: M), n ∈ NC M → m ∈ NC M → 𝕋 M n = 𝕋 M m → n = m:=
  assume n m,
  begin
    intros hn hm h,
    rw full_extensionality,
    have h2:= cardinalsinhabited2 M n hn,
    cases h2 with a h3,
    have h4:= cardinalsinhabited2 M m hm,
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
    have h10:= TNC M m hm,
    have h11:= TNC M n hn, 
    have h9:= cardinals2 M (𝕋 M m) (USC a) (USC b)  h10 h6 h8, 
    rw← uscsimilar at h9,
    have h12:= cardinals0 M n a b hn h3 h9, 
    have h13:= cardinalsdisjoint2 M n m b hn hm h12 h5,
    intro x,
    rw h13,
  end

lemma NCsum: ∀ (a b:M), a ∈ FINITE M → b ∈ FINITE M →  a ∩ b = Λ → Nc M (a ∪ b) = (Nc M a) + (Nc M b):=
  begin
    intros a b ha hb h3,
    have h4:= xinNcx M (a ∪ b),
    have h5:= xinNcx M a,
    have h6:= xinNcx M b,
    have h7: a ∪ b ∈ (Nc M a) + (Nc M b) :=
      begin
        rw addition_members,
        use a, use b,
        simp,
        exact ⟨ h5, h6, h3⟩, 
      end,
    have h9:= finitecardinals3 M a ha,
    have h10:= finitecardinals3 M b hb,
    have h12:= union M a b ha hb h3,
    have h11:= finitecardinals3 M (a ∪ b) h12,
    have h19:= inhabited_sum M (Nc M b) h10 (Nc M a) h9 ⟨ a ∪ b, h7⟩,
    have h8:= cardinalsdisjoint M (Nc M (a ∪ b)) ((Nc M a) + (Nc M b)) (a ∪ b) h11 h19,
    apply h8,
    rw intersection_axiom,
    split,
    {
      exact h4,
    },
    {
      exact h7,
    }
  end

lemma Ncadjoint: ∀ (X c:M), X ∈ FINITE M → ¬ (c ∈ X) → (Nc M X) + one = Nc M (X ∪ (single c)):=
  begin
    intros X  c hX hc,
    have h3:= xinNcx M X,
    have h4: (single Λ:M) ∈  (one:M):=
      begin
        rw one_members,
        use Λ,
      end,
    have h5: X ∪ (single c) ∈ (Nc M X) + one:=
      begin
        rw addition_members,
        use X, use (single c),
        simp,
        split,
        {
          exact h3,
        },
        {
          split,
          {
            rw one_members,
            use c,
          },
          {
            rw full_extensionality,
            intros t,
            split,
            {
              intros h5,
              rw intersection_axiom at h5,
              rw singleton1 at h5,
              rw h5.2 at *,
              cases h5 with h6 h7,
              rw h7 at *,
              contradiction,
            },
            {
              intros h8,
              have h9:= emptyset_axiom t,
              contradiction,
            }
          }
        }
      end,
    have h30:= xinNcx M (X ∪ (single c)),
    have h31:= cardinalsdisjoint M (Nc M (X ∪ single c)) (Nc M X + one) (X ∪ single c),
    rw sym,
    apply h31,
    have h36:= finite_adjoin M X c ⟨ hX, hc⟩ ,
    have h35:= finitecardinals3 M (X ∪ single c) h36,
    exact h35,
    have h40:= finitecardinals3 M X hX,
    have h37:= inhabited_sum M one (oneF M) (Nc M X) h40 ⟨ X ∪ (single c), h5⟩,
    exact h37,
    rw intersection_axiom,
    exact ⟨ h30, h5⟩,
  end

lemma Timage: ∀(X:M), X ∈ FINITE M → X ⊆ NC M  → Nc M (imageT M X)  = 𝕋 M (Nc M X):=
  begin
    have base: Λ ∈ W_Timage M:=
      begin
        rw W_Timage_members,
        split,
        {
          exact lambda_finite M,
        },
        {
          have h4:= Nc_empty M,
          rw h4,
          rw Tzero,
          have h5: imageT M Λ = Λ:=
            begin
              rw full_extensionality,
              intros t,
              split,
              {
                intros h6,
                rw imageT_members M (Λ:M) at h6,
                cases h6 with u h7,
                cases h7 with h8 h9,
                have h10:= emptyset_axiom u,
                contradiction,
              },
              {
                intros h11,
                have h12:= emptyset_axiom t,
                contradiction,
              }
            end,
          rw h5,
          have h13:= Nc_empty M,
          rw h13,
          simp,
        }
      end,
    have step: ∀(X c:M), ((¬ c ∈ X) ∧ X ∈ W_Timage M)  → X ∪ single c ∈ W_Timage M:=
      begin
        intros X c h400,
        cases h400 with hc hX,
        rw W_Timage_members,
        rw W_Timage_members at hX,
        cases hX with hXfinite h20,
        split,
        {
          exact finite_adjoin M X c ⟨ hXfinite, hc⟩,
        },
        { intros h40,
          have h41:X ⊆ NC M:=
            begin
              rw subset_definition,
              intros t ht,
              rw subset_definition at h40,
              specialize h40 t,
              rw binary_union_axiom at h40,
              apply h40,
              left,
              exact ht,
            end, 
          have h30:= Timageunion M X (single c),
          have hc2:= member_subset M X (NC M) c h41,
          have h31: ¬ 𝕋 M c ∈ imageT M X:=
            begin
              intros h32,
              have h35:= finite_adjoin M X c ⟨ hXfinite, hc⟩,
              rw imageT_members M X at h32,
              cases h32 with u h33,
              cases h33 with h34 h35,
              have h36:= ToneoneNC M u c,
              have h37:= member_subset M X (NC M) u h41 h34,
              have h39: c ∈ X ∪ (single c):=
                begin
                  rw binary_union_axiom,
                  right,
                  rw singleton1,
                end,
              have h38:= member_subset M (X ∪ (single c)) (NC M) c h40  h39,
              rw sym at h35,
              have h40:= h36 h37 h38 h35,
              rw h40 at *,
              contradiction,
            end,
          have h32: Nc M (imageT M (X ∪ single c)) = Nc M (imageT M X ∪ imageT M (single c)) :=
            begin
               rw h30,
            end,
          have h21:= h20 h41,  -- the induction hypothesis
          have h40:= finitecardinals3 M X hXfinite,
          have h22: 𝕋 M (Nc M X) ∈ 𝔽 := 
            begin
              have h23:= Tfinite M (Nc M X) h40,
              exact h23,
            end, 
          have h24: imageT M X ∈ FINITE M:= 
            begin
              have h25:= finitecardinals1 M (𝕋 M (Nc M X)) (imageT M X) h22,
              apply h25,
              rw← h21,
              exact xinNcx M (imageT M X),
            end,
          have h26:= singletons_finite M (𝕋 M c),
          have h27: imageT M X ∩ single (𝕋 M c) = Λ:=
            begin
              rw full_extensionality,
              intros t,
              rw intersection_axiom,
              rw singleton1,
              split,
              {
                intros h28,
                cases h28 with h29 h30,
                rw h30 at *,
                contradiction,
              },
              {
                intros h31,
                have h32:= emptyset_axiom t,
                contradiction,
              }
            end,
          have h33:= NCsum M (imageT M X)(single (𝕋 M c)) h24 h26 h27,
          have h35:= Nc_unitclass M (𝕋 M c),
          rw h35 at *,
          rw h21 at *,
          rw←  (Tone M) at h33,
          have h70: (Nc M X) + one ∈ 𝔽 := 
            begin
              have h71:= inhabited_sum M one (oneF M) (Nc M X) h40 ,
              apply h71,
              use X ∪ (single c),
              rw addition_members,
              use X, use (single c),
              simp,
              split,
              {
                exact xinNcx M X,
              },
              {
                rw one_members,
                split,
                {
                  use c,
                },
                {
                  rw full_extensionality,
                  intros t,
                  rw intersection_axiom,
                  split,
                  {
                    intros h200,
                    cases h200 with h201 h202,
                    rw singleton1 at h202,
                    rw h202 at *,
                    contradiction,
                  },
                  {
                    intros h203,
                    have h204:= emptyset_axiom t,
                    contradiction,
                  }
                }
              }
            end,
          rw← Tsum M one (oneF M) (Nc M X) h40 h70 at h33,
          have h50:= Ncadjoint M X c hXfinite hc,
          have h51: Nc M ( (imageT M X) ∪ (single (𝕋 M c))) = 𝕋 M (Nc M (X ∪ (single c))):=
            begin
               rw h33,
               rw h50,
            end,
          rw h30,
          have h54: single (𝕋 M c) = imageT M (single c):=
            begin
              rw full_extensionality,
              intros t,
              rw singleton1,
              rw imageT_members M (single c),
              split,
              {
                intros h60,
                rw h60 at *,
                use c,
                simp,
                rw singleton1,
              },
              {
                intros h61,
                cases h61 with u h62,
                rw singleton1 at h62,
                cases h62 with h63 h64,
                rw h63 at *,
                exact h64,
              }
            end,
          rw← h54,
          exact h51,
        }
      end,
    intros X hfinite hX,
    rw finite_members at hfinite,
    specialize hfinite (W_Timage M),
    have h100:= hfinite ⟨ base,step⟩,
    rw W_Timage_members at h100,
    cases h100 with h101 h102,
    exact h102 hX, 
  end

lemma Tledot:  ∀ (n m:M), n ∈ NC M → m ∈ NC M → (n ⪯ m ↔ 𝕋 M n ⪯ 𝕋 M m) :=
  begin
    intros n m hn hm,
    split,
    { -- left to right
      intros h3,
      rw ledot_definition at h3,
      cases h3 with a h4,
      cases h4 with b h5,
      rcases h5 with ⟨ ha, hb, h6⟩ ,
      have h14: USC a ∈ 𝕋 M n:= 
        begin
          rw T_members,
          use a,
          exact ⟨ha, similar_reflexive M (USC a)⟩, 
        end,
      have h15: USC b ∈ 𝕋 M m:= 
        begin
          rw T_members,
          use b,
          exact ⟨hb, similar_reflexive M (USC b)⟩, 
        end,
      rw ledot_definition,
      use USC a,
      use USC b,
      have h16:= usc_subset M a b,
      rw h16 at h6,
      exact ⟨ h14, h15, h6⟩,
    },
    {
      intros h20,
      rw ledot_definition,
      have h200:= h20,
      rw ledot_definition at h20,
      cases h20 with A h21,
      cases h21 with B h22,
      rcases h22 with ⟨ h23,h24,h25⟩,
      have h23copy:= h23,
      have h24copy:= h24, 
      rw T_members at h23 h24,
      cases h24 with q h26,
      cases h26 with hq h28,
      have h29:= TNC M m hm,
      have h30:= TNC M n hn,
      have h31:= cardinals0 M (𝕋 M m) B (USC q) h29 h24copy h28,
      have h32:= le2NC M (USC q) (𝕋 M n)(𝕋 M m) h30 h29 h200 h31,
      cases h32 with P h33,
      cases h33 with h34 h35,
      have h36:= uscsubsets M q P h35,
      cases h36 with p h37,
      cases h37 with h38 h39,
      rw h39 at *,
      use p, use q,
      rw T_members at h34,
      cases h34 with x h35,
      cases h35 with h36 h37,
      have h380:= uscsimilar M p x,
      have h39 := (h380.2) h37,
      rw similar_symmetric at h39,
      have h40:= cardinals0 M n x p hn h36 h39,
      exact ⟨ h40,hq, h38⟩,
    }

   end

lemma Tlessdot: ∀ (n m:M), n ∈ NC M → m ∈ NC M → n ⋖ m → 𝕋 M n ⋖ 𝕋 M m :=
  begin
    intros n m hn hm h3,
    rw lessdot_definition at h3,
    cases h3 with h4 h5,
    cases h5 with h6 h7,
    cases h7 with a h8,
    cases h8 with b h9,
    rcases h9 with ⟨ h10, h11, h12, h13⟩,
    have h14: USC a ∈ 𝕋 M n :=
      begin
        rw T_members,
        use a,
        exact ⟨ h10, similar_reflexive M (USC a)⟩,
      end, 
      have h15: USC b ∈ 𝕋 M m :=
      begin
        rw T_members,
        use b,
        exact ⟨ h11, similar_reflexive M (USC b)⟩,
      end,
    cases h13 with u h16,
    rw lessdot_definition,
    have h20:= (usc_subset M a b).1 h12,
    split,
    {
      rw ledot_definition,
      use USC a,
      use USC b,
      exact ⟨ h14, h15, h20⟩,
    },
    {
      split,
      {
        intros h,
        have h30:= (Tledot M m n hm hn).2 h,
        contradiction,
      },
      {
        use USC a,
        use USC b,
        split,
        {
          exact h14,
        },
        {
          split,
          {
            exact h15,
          },
          {
            split,
            {
              exact h20,
            },
            {
              use single u,
              rw minus_members,
              rw usc,
              use u,
              simp,
              rw minus_members at h16,
              exact h16.1,
              rw usc,
              intros h40,
              cases h40 with p h41,
              cases h41 with hp h42,
              have h43:= single_oneone M u p h42,
              rw← h43 at *,
              rw minus_members at h16,
              cases h16 with h17 h18,
              contradiction,
            }
          }
        }
      }
    }
  end

lemma Hclosed: ¬ 𝔽 ∈  FINITE M → ∀ (m:M), m ∈ 𝔽 → ¬¬ (𝕊 m ∈ 𝔽):=
  begin
    intros h101 m hm h3,
    have h4:= cardinalsinhabited M m hm,
    cases h4 with U hU,
    have h5: MAXIMAL M m:=
      begin
        unfold MAXIMAL,
        split,
        {
          exact hm,
        },
        {
          intros k hk,
          have h6:= finitetrichotomy M k hk m hm,
          cases h6 with h7 h8,
          { rw letolessthan M k m hk hm,
            left,
            exact h7,
          },
          {
            cases h8 with h9 h10,
            {
              rw letolessthan M k m hk hm,
              right, 
              exact h9,
            },
            {
              have h12:= noinsertions M m k hm hk h10,
              have h13:= h12,
              rw le_definition  at h13,
              cases h13 with a h14,
              cases h14 with b h15,
              cases h15 with ha h16,
              have hsm:= successorF M m hm ⟨ a, ha⟩,
              contradiction,
            }
          }
        }
      end,
    unfold MAXIMAL at h5,
    cases h5 with hm hmax,
    have h20: 𝔽 = Jbar M m:=
      begin
        rw full_extensionality,
        intros x,
        rw Jbar_members M m,
        split,
        {
          intros hx,
          have h21:= hmax x hx,
          exact ⟨hx, h21⟩, 
        },
        {
          intros h22,
          exact h22.1,
        }
      end,
    have h30:= Jbarfinite M m hm,
    rw←h20 at h30,
    contradiction, 
  end

lemma Hclosed2: zero ∈ HH M ∧ ∀ (x:M), x ∈ HH M→ 𝕊 x ∈ HH M:=
  begin
    split,
    {
    rw HH_members,
    intros w hw,
    exact hw.1,
    },
    {
    intros x h3,
    rw HH_members,
    intros w hw,
    cases hw with h4 h5,
    rw HH_members at h3,
    specialize h3 w,
    have h6:= h3 ⟨ h4, h5⟩,
    exact h5 x h6, 
    }
  end

lemma HHtonotnotF: (¬ 𝔽 ∈ FINITE M) → ∀ (x:M), x ∈ HH M → ¬¬ x ∈ 𝔽:=
  begin
    intros hnotfinite,
    have base: zero ∈ Z_HtonotnotF M:=
      begin
        rw Z_HtonotnotF_members,
        have h4:= zeroF M,
        have h5:= double_negate(zero ∈ 𝔽) h4,
        have h3:= (Hclosed2 M).1,
        exact ⟨ h3, h5⟩,
      end,
    have step: ∀(x:M), x ∈ Z_HtonotnotF M → 𝕊 x ∈ Z_HtonotnotF M:=
      begin
        intros x h5,
        rw Z_HtonotnotF_members at h5,
        rw Z_HtonotnotF_members,
        cases h5 with h6 h7,
        have h8:= Hclosed M hnotfinite x,
        have h9:= double_negate (x ∈ 𝔽 → ¬¬𝕊 x ∈ 𝔽) h8,
        have h10:= push_double_negationNF (x ∈ 𝔽)( ¬¬𝕊 x ∈ 𝔽) h9,
        rw triplenegation at h10,
        have h11:= h10 h7,
        have h12:= (Hclosed2 M).2 x h6,
        exact ⟨ h12, h11⟩,
      end,
    intros x h30,
    rw HH_members at h30,
    have h31:= h30 (Z_HtonotnotF M) ⟨ base, step⟩,
    rw Z_HtonotnotF_members at h31,
    exact h31.2,
  end

lemma nonzeroissuccessorHH: ∀(x:M),x ∈ HH M → ¬ x = zero → 
∃ (p:M), p ∈ HH M ∧  𝕊 p = x :=
  begin
    have base: zero ∈ Z_nonzeroissuccessorH M:=
      begin
        rw Z_nonzeroissuccessorH_members,
        have h3:= Hclosed2 M,
        split,
        {
          exact h3.1,
        },
        {
          intros h4,
          contradiction,
        }
      end,
    have step: ∀(x:M), x ∈ Z_nonzeroissuccessorH M → 𝕊 x ∈ Z_nonzeroissuccessorH M:=
      begin
        intros x h3,
        rw Z_nonzeroissuccessorH_members at h3,
        rw Z_nonzeroissuccessorH_members,
        cases h3 with hx h4,
        split,
        {
          have h5:= Hclosed2 M,
          cases h5 with hzero h6,
          exact h6 x hx,
        },
        {
          intros h7,
          use x,
          simp,
          exact hx,
        }
      end,
    intros x hx,
    rw HH_members at hx,
    have h200:= hx (Z_nonzeroissuccessorH M)⟨ base, step⟩,
    rw Z_nonzeroissuccessorH_members at h200,
    exact h200.2,
  end

lemma decidableHzero: ∀ (x:M),x ∈ HH M → x = zero ∨ ¬ x = zero:=
  begin
    have base: zero ∈ Z_decidableHzero M:=
      begin
        rw Z_decidableHzero_members,
        simp,
        exact (Hclosed2 M).1,
      end,
    have step: ∀ (x:M), x ∈ Z_decidableHzero M → 𝕊 x ∈ Z_decidableHzero M:=
      begin
        intros x h3,
        rw Z_decidableHzero_members at h3,
        rw Z_decidableHzero_members,
        cases h3 with hx h4,
        split,
        {
          have h5:= (Hclosed2 M).2 x hx,
          exact h5,
        },
        {
          right,
          exact Fregesuccessoromits0 M x,
        }
      end,
    intros x hx,
    rw HH_members at hx,
    have h200:= hx (Z_decidableHzero M) ⟨base, step⟩,
    rw Z_decidableHzero_members at h200, 
    exact h200.2,
  end  

lemma decidableequalityonHH: (¬ 𝔽 ∈ FINITE M) → ∀ (y:M),y ∈ HH M →  ∀ (x:M),x ∈ HH M → x = y ∨ ¬ x = y:=
  begin
    intros hnotfinite,
    have base: zero ∈ Z_decidableequalityonH M:=
      begin
        rw Z_decidableequalityonH_members,
        have h2:= decidableHzero M,
        have h3:= (Hclosed2 M).1,
        exact ⟨ h3, h2⟩,
      end,
    have step: ∀ (y:M), y ∈ Z_decidableequalityonH M → 𝕊 y ∈ Z_decidableequalityonH M:=
      begin
        intros y h4,
        rw Z_decidableequalityonH_members at h4,
        rw Z_decidableequalityonH_members,
        cases h4 with hy h5,
        split,
        {
          exact (Hclosed2 M).2 y hy,
        },
        {
          intros x hx,
          have h6:= decidableHzero M x hx,
          cases h6 with h7 h8,
          {
            rw h7 at *,
            right,
            have h9:= Fregesuccessoromits0 M y,
            intros h10,
            apply h9,
            rw h10,
          },
          {
            have h20:= nonzeroissuccessorHH M x hx h8,
            cases h20 with p h21,
            cases h21 with hp h23,
            rw←  h23,
            have h24:= h5 p hp,
            cases h24 with h25 h26,
            {
              rw h25 at *,
              simp,
            },
            {
              right,
              have h29:= successoroneone M p y,
              have h30:= successoroneone M p x,
              have h31:= double_negate (p ∈ 𝔽 → y ∈ 𝔽 → (∃ (u : M), u ∈ 𝕊 p) → (∃ (u : M), u ∈ 𝕊 y) → (p = y ↔ 𝕊 p = 𝕊 y)) h29,
              have h32:= HHtonotnotF M hnotfinite y hy,
              have h33:= HHtonotnotF M hnotfinite p hp,
              have h36:= HHtonotnotF M hnotfinite x hx,
              have h34:= push_double_negationNF (p ∈ 𝔽)( y ∈ 𝔽 → (∃ (u : M), u ∈ 𝕊 p) → (∃ (u : M), u ∈ 𝕊 y) → (p = y ↔ 𝕊 p = 𝕊 y)) h31 h33,
              have h35:= push_double_negationNF (y ∈ 𝔽)((∃ (u : M), u ∈ 𝕊 p) → (∃ (u : M), u ∈ 𝕊 y) → (p = y ↔ 𝕊 p = 𝕊 y)) h34 h32,
              have h37:= (Hclosed2 M).2 p hp,
              have h38:= HHtonotnotF M hnotfinite (𝕊 p) h37,
              have h39:=cardinalsinhabited M (𝕊 p),
              have h40:= double_negate ( 𝕊 p ∈ 𝔽 → (∃ (x : M), x ∈ 𝕊 p)) h39,
              have h41:= push_double_negationNF (𝕊 p ∈ 𝔽)((∃ (x : M), x ∈ 𝕊 p)) h40  h38,
              have h42:= (Hclosed2 M).2 y hy,
              have h43:= HHtonotnotF M hnotfinite (𝕊 y) h42, 
              have h44:=cardinalsinhabited M (𝕊 y), 
              have h45:= double_negate ( 𝕊 y ∈ 𝔽 → (∃ (x : M), x ∈ 𝕊 y)) h44,
              have h46:= push_double_negationNF (𝕊 y ∈ 𝔽)((∃ (x : M), x ∈ 𝕊 y)) h45  h43,
              have h47:= push_double_negationNF (p ∈ 𝔽)( y ∈ 𝔽 → (∃ (u : M), u ∈ 𝕊 p) → (∃ (u : M), u ∈ 𝕊 y) → (p = y ↔ 𝕊 p = 𝕊 y)) h31 h33,
              have h48:= push_double_negationNF (y ∈ 𝔽)( (∃ (u : M), u ∈ 𝕊 p) → (∃ (u : M), u ∈ 𝕊 y) → (p = y ↔ 𝕊 p = 𝕊 y)) h47 h32,
              have h49:= push_double_negationNF  (∃ (u : M), u ∈ 𝕊 p) ( (∃ (u : M), u ∈ 𝕊 y) → (p = y ↔ 𝕊 p = 𝕊 y)) h48 h41,
              have h50:= push_double_negationNF  ( (∃ (u : M), u ∈ 𝕊 y))( (p = y ↔ 𝕊 p = 𝕊 y)) h49 h46,
              have h51:= push_double_negationNF  (p = y) ( 𝕊 p = 𝕊 y),
              have h52:((¬¬ (p = y ↔ (𝕊 p = 𝕊 y)))) → ¬¬ (𝕊 p = 𝕊 y → p = y ):=
                begin
                  intros h60 h62,
                  apply h60,
                  intros h63,
                  apply h62,
                  rw h63,
                  simp,
                end,
              have h64:= h52 h50,
              have h65:= push_double_negationNF ( 𝕊 p = 𝕊 y)(p = y) h64,
              rw← h23 at *,
              intro h70,
              have h71:= double_negate (𝕊 p = 𝕊 y) h70,
              have h72:= h65 h71,
              contradiction,
            }
          }
        }
      end,
    intros y hy,
    rw HH_members at hy,
    have h80:= hy (Z_decidableequalityonH M) ⟨ base, step⟩ ,
    rw Z_decidableequalityonH_members at h80,
    exact h80.2,
  end

lemma Honeone:(¬ 𝔽 ∈ FINITE M) → ∀ (x y:M), x ∈ HH M → y ∈ HH M → 𝕊 x = 𝕊 y → x = y:=
  begin 
    intros hnotfinite x y hx hy h4,
    have h5:= (Hclosed2 M).2 x hx,
    have h6:= (Hclosed2 M).2 y hy,
    have h7:= HHtonotnotF M hnotfinite (𝕊 x) h5,
    have h8:= HHtonotnotF M hnotfinite (𝕊 y) h6,
    have h9:= successoroneone M x y,
    have h10:= double_negate (𝕊 x = 𝕊 y) h4,
    have h11:= double_negate (x ∈ 𝔽 → y ∈ 𝔽 → (∃ (u : M), u ∈ 𝕊 x) → (∃ (u : M), u ∈ 𝕊 y) → (x = y ↔ 𝕊 x = 𝕊 y)) h9,
    have h12:= HHtonotnotF M hnotfinite x hx,
    have h13:= HHtonotnotF M hnotfinite y hy,
    have h30:= cardinalsinhabited M (𝕊 x),
    have h31:= double_negate ( 𝕊 x ∈ 𝔽 → (∃ (x_1 : M), x_1 ∈ 𝕊 x)) h30,
    have h32:= push_double_negationNF (𝕊 x ∈ 𝔽 )( (∃ (x_1 : M), x_1 ∈ 𝕊 x)) h31 h7,
    have h40:= cardinalsinhabited M (𝕊 y),
    have h41:= double_negate ( 𝕊 y ∈ 𝔽 → (∃ (x_1 : M), x_1 ∈ 𝕊 y)) h40,
    have h42:= push_double_negationNF (𝕊 y ∈ 𝔽 )( (∃ (x_1 : M), x_1 ∈ 𝕊 y)) h41 h8,
    have h14:= push_double_negationNF (x ∈ 𝔽)( y ∈ 𝔽 → (∃ (u : M), u ∈ 𝕊 x) → (∃ (u : M), u ∈ 𝕊 y) → (x = y ↔ 𝕊 x = 𝕊 y)) h11 h12,
    have h15:= push_double_negationNF ( y ∈ 𝔽)((∃ (u : M), u ∈ 𝕊 x) → (∃ (u : M), u ∈ 𝕊 y) → (x = y ↔ 𝕊 x = 𝕊 y)) h14 h13,
    have h20:= push_double_negationNF ((∃ (u : M), u ∈ 𝕊 x) )((∃ (u : M), u ∈ 𝕊 y) → (x = y ↔ 𝕊 x = 𝕊 y)) h15 h32,
    have h22:= push_double_negationNF ((∃ (u : M), u ∈ 𝕊 y) )( (x = y ↔ 𝕊 x = 𝕊 y)) h20 h42,
    have h23:= notnot_iff_2way (x = y)( 𝕊 x = 𝕊 y),
    rw h23  at h22,
    rw← h22 at h10,
    have h50:= decidableequalityonHH M hnotfinite x hx y hy,
    have h53:= sym M y x,
    cases h50 with h51 h52,
    { 
      rw h53 at h51,
      exact h51,
    },
    {
      rw h53 at h52,
      contradiction,
    }
  end

theorem HHinfinite: (¬ 𝔽 ∈ FINITE M) → infinite M (HH M):=
  begin
    intros hnotfinite,
    unfold infinite,
    set Hplus:= image M (successorHH M) (HH M) with Hplusdef,
    use Hplus,
    have hrel: Rel (successorHH M):=
      begin
        rw Rel_definition,
        intros z h30,
        rw successorHH_members at h30,
        cases h30 with x h31,
        cases h31 with h32 h33,
        use x, use (𝕊 x),
        exact h33,
      end,
    split,
    {
      rw subset_definition,
      intros z h4,
      rw Hplusdef at h4,
      rw image_members M (successorHH M) (HH M) hrel  at h4,
      cases h4 with x h5,
      cases h5 with h6 h7,
      rw successorHH_members at h7,
      cases h7 with a h9,
      cases h9 with ha h11,
      rw ordered_pair_equality at h11,
      rw h11.2 at *,
      rw h11.1 at *,
      have h13:= (Hclosed2 M).2 a h6,
      exact h13,
    },
    {
      split,
      {
        intros h40,
        rw Hplusdef at h40,
        rw full_extensionality at h40,
        have h41:= h40 zero,
        have h42:= Hclosed2 M,
        cases h42 with h43 h44,
        rw h41 at h43,
        rw image_members at h43,
        cases h43 with a h44,
        cases h44 with h45 h46,
        rw successorHH_members at h46,
        cases h46 with b h47,
        cases h47 with h48 h49,
        rw ordered_pair_equality at h49,
        rw h49.1 at *,
        rw h49.2 at *,
        cases h49 with h50 h51,
        have h52:= Fregesuccessoromits0 M b,
        rw sym at h51,
        contradiction,
        exact hrel,
      },
      {
        unfold similar,
        use successorHH M,
        unfold similarity,
        split,
        {
          unfold oneone,
          repeat{split},
          {
            exact hrel,
          },
          {
            intros x y h60,
            cases h60 with hx h61,
            rw Hplusdef,
            rw image_members,
            use x,
            exact ⟨ hx, h61⟩,
            exact hrel,
          },
          {
            intros x y z h64,
            cases h64 with h65 h66,
            cases h66 with h67 h68,
            rw successorHH_members at h67,
            rw successorHH_members at h68,
            cases h67 with a h70,
            cases h70 with ha h71,
            cases h68 with b h72,
            cases h72 with hb h73,
            rw ordered_pair_equality at h73,
            rw ordered_pair_equality at h71,
            rw h71.1 at *,
            rw h71.2 at *,
            rw h73.1 at *,
            rw h73.2 at *,
          },
          {
            intros x hx,
            use 𝕊 x,
            have h82:= (Hclosed2 M).2 x hx,
            split,
            {
              rw Hplusdef,
              rw image_members,
              use x,
              rw successorHH_members,
              split,
              {
                exact hx,
              },
              {
                use x,
                simp,
                exact hx,
              },
              {
                exact hrel,
              } 
            },
            {
              rw successorHH_members,
              use x,
              simp,
              exact hx,
            }
          },
          {
            intros x u y h90,
            cases h90 with h91 h92,
            cases h92 with h93 ha,
            rw successorHH_members at h91,
            rw successorHH_members at h93,
            cases h91 with a h95,
            cases h93 with b h96,
            cases h95 with ha h97,
            cases h96 with hb h98,
            rw ordered_pair_equality at h97,
            rw ordered_pair_equality at h98,
            rw h97.1 at *,
            rw h97.2 at *,
            rw h98.1 at *,
            rw h98.2 at *,
            cases h98 with h99 h100,
            have h101:= Honeone M hnotfinite a b ha hb h100,
            exact h101,
          },
          {
            intros x y h110,
            cases h110 with h111 h112,
            rw successorHH_members at h111,
            cases h111 with a h112,
            cases h112 with h113 h114,
            rw ordered_pair_equality at h114,
            rw h114.1 at *,
            exact h113,
          }
        },
        {
          rw Hplusdef,
          unfold onto,
          intros y h120,
          rw image_members at h120,
          exact h120,
          exact hrel,
        }
      }
    }
  end


 #axioms_all