import ScottDomains.PowerdomainMap
-- `PRep.domain_orderIso`, the transport of `Domain` along an order isomorphism.
-- It is the only thing taken from §7.3; the dependency runs this way and never
-- back, so `PowerdomainMap.lean` itself stays importable by `PRep`.
import ScottDomains.PRep

/-!
# `p(K(D)) ⊆ K(D)` is false, already for a finitary projection

Round r0038 recorded, and `Lemma28AtU.lean`'s docstring repeats, an obligation
that no round had settled:

> The natural construction acts on finite sets of compacts and so wants
> `p(K(D)) ⊆ K(D)` for a finitary projection `p`; whether that holds is the step
> to settle first, and no round has settled it.

This module settles it: **it fails.** The witness is one domain, one finitary
projection on it, and one compact element whose image is not compact.

## Why it fails, in one sentence

A projection satisfies `p(x) ⊑ x`, and **compactness is not downward closed**.
So the only way `p(K) ⊆ K` could hold in general is if every element below a
compact element were compact, and that is false in any domain with a non-compact
element sitting strictly under a compact one.

## The witness

Take `A = ⟨ℕ ∪ {⊤}, ≤⟩`, the naturals with a top adjoined — countable, with a
least element, so Theorem 11 (`IdealCompletion.instDomain`) makes `D = Idl(A)` a
domain with no further work. Three of its elements matter:

| # | element of `D` | as a set of `A` | compact? |
| - | -------------- | --------------- | -------- |
| 1 | `↓⊤` | all of `A` | **yes** — principal, `isCompactElement_principal` |
| 2 | `natIdeal` | `{a \| a ≠ ⊤}`, the naturals | **no** — `not_isCompactElement_natIdeal` |
| 3 | `↓n` | `{a \| a ≤ n}` | yes |

`natIdeal` is an ideal (directed by `max` in a linear order, downward closed
because nothing below a natural is `⊤`) and it is not principal: a generator
would be some `↑n`, and `↑(n+1)` lies in it. It sits **strictly below** the
compact `↓⊤`, which is the whole configuration the argument above needs.

The projection is `p(I) = I ∩ natIdeal` — "delete `⊤`". It is Scott continuous
because a directed supremum of ideals is the union of them
(`IdealCompletion.mem_sSup_iff`) and intersection with a fixed set commutes with
union; it is idempotent and below the identity because intersection is. And
`p(↓⊤) = natIdeal`, so it carries a compact element to a non-compact one.

## It is *finitary*, which is the whole point

The obligation was stated for a **finitary** projection, so the counterexample
must produce a `Domain` structure on `im(p)`, and that is the only real work in
this file. `im(p)` is the set of ideals of `A` containing no `⊤`, which is
order-isomorphic to `Idl(ℕ)` by the mutually inverse maps

    up : Idl(ℕ) → im(p),   up(K) = {↑n | n ∈ K}
    down : im(p) → Idl(ℕ), down(J) = {n | ↑n ∈ J}

and `Idl(ℕ)` is a domain by Theorem 11 again. `PRep.domain_orderIso` transports
it. So `p` is a finitary projection (`isFinitaryProjection_pHom`) and the
counterexample is at full strength, not at the weaker "projection" reading.

## What this does and does not close

It closes the question and **removes the obstruction rather than discharging
it**. The construction that wanted `p(K(D)) ⊆ K(D)` — transporting finite sets
of compacts along `p` and then acting on ideals — cannot be carried out for any
`f` at all, since even a finitary projection breaks it.

`ScottDomains.PowerdomainMap` builds the action a different way, the paper's own:
`f♮ = ext({|·|} ∘ f)` factors through the ideal completion's universal property,
which quantifies over ideals and never over a transported basis, so it is defined
for **every** continuous `f` with no hypothesis on compacts. What Lemma 28 needs
— that the action of a projection is a projection — is
`PowerdomainMap.isProjection_map`, proved from the two functor laws.
-/

namespace ScottDomains.PowerdomainMap.Compacts

open ScottDomains ScottDomains.IdealCompletion ScottDomains.ScottHom

/-! ## 1. The carrier `⟨ℕ ∪ {⊤}, ≤⟩` and its ideal completion -/

/-- The index pre-order: the naturals with a top adjoined. Countable, with a
least element — Theorem 11's two hypotheses. -/
abbrev Chain : Type := WithTop ℕ

/-- The domain `D = Idl(A)`. A domain by Theorem 11 and nothing else. -/
abbrev Dom : Type := IdealCompletion Chain

example : Domain Dom := inferInstance

/-! ## 2. `natIdeal`: a non-compact element strictly below a compact one -/

/-- `{a ∈ A | a ≠ ⊤}` — the naturals inside `A`. -/
def natSet : Set Chain := {a | a ≠ ⊤}

/-- `natSet` is an ideal: downward closed because nothing below a natural is `⊤`,
directed by `max`, which stays out of `⊤` because `A` is linearly ordered. -/
theorem isIdeal_natSet : Order.IsIdeal natSet := by
  refine ⟨fun a b hba ha hb => ha (top_le_iff.mp (hb ▸ hba)),
    ⟨((0 : ℕ) : Chain), WithTop.coe_ne_top⟩, fun a ha b hb => ⟨max a b, ?_, le_max_left a b,
      le_max_right a b⟩⟩
  rcases le_total a b with h | h
  · rw [max_eq_right h]; exact hb
  · rw [max_eq_left h]; exact ha

/-- The ideal of all naturals, as a point of `D`. -/
def natIdeal : Dom := ofIdeal isIdeal_natSet.toIdeal

@[simp] theorem mem_natIdeal {a : Chain} : a ∈ natIdeal ↔ a ≠ ⊤ := Iff.rfl

/-- `↓⊤`, the top of `D`, which is compact because it is principal. -/
def topIdeal : Dom := principal (⊤ : Chain)

@[simp] theorem mem_topIdeal {a : Chain} : a ∈ topIdeal ↔ a ≤ (⊤ : Chain) := Iff.rfl

theorem isCompactElement_topIdeal : IsCompactElement topIdeal :=
  isCompactElement_principal (⊤ : Chain)

/-- **`natIdeal` is not compact.** A compact ideal is principal
(`exists_eq_principal_of_isCompactElement`), its generator would be some `↑n`
since `⊤ ∉ natIdeal`, and `↑(n+1)` is then a member above the generator. -/
theorem not_isCompactElement_natIdeal : ¬ IsCompactElement natIdeal := by
  intro h
  obtain ⟨a, ha, heq⟩ := exists_eq_principal_of_isCompactElement h
  obtain ⟨n, rfl⟩ := WithTop.ne_top_iff_exists.mp (mem_natIdeal.mp ha)
  have hmem : (((n + 1 : ℕ) : ℕ) : Chain) ∈ natIdeal := WithTop.coe_ne_top
  rw [heq, mem_principal] at hmem
  exact Nat.not_succ_le_self n (WithTop.coe_le_coe.mp hmem)

/-- `natIdeal` sits strictly below the compact `↓⊤` — the configuration that
makes `p(K) ⊆ K` refutable at all. -/
theorem natIdeal_lt_topIdeal : natIdeal < topIdeal := by
  refine lt_of_le_of_ne (fun a _ => mem_topIdeal.mpr le_top) fun h => ?_
  have htop : (⊤ : Chain) ∈ topIdeal := mem_topIdeal.mpr le_top
  rw [← h] at htop
  exact (mem_natIdeal.mp htop) rfl

/-! ## 3. The projection `p(I) = I ∩ natIdeal` -/

/-- The underlying set of `p(I)`. -/
def pSet (I : Dom) : Set Chain := {a | a ∈ I ∧ a ≠ ⊤}

theorem isIdeal_pSet (I : Dom) : Order.IsIdeal (pSet I) := by
  refine ⟨fun a b hba ha => ⟨I.lower hba ha.1, fun hb => ha.2 (top_le_iff.mp (hb ▸ hba))⟩,
    ⟨((0 : ℕ) : Chain), ?_, WithTop.coe_ne_top⟩, fun a ha b hb => ?_⟩
  · exact I.lower (le_of_eq rfl) (bot_mem I)
  · refine ⟨max a b, ⟨?_, ?_⟩, le_max_left a b, le_max_right a b⟩
    · rcases le_total a b with h | h
      · rw [max_eq_right h]; exact hb.1
      · rw [max_eq_left h]; exact ha.1
    · rcases le_total a b with h | h
      · rw [max_eq_right h]; exact hb.2
      · rw [max_eq_left h]; exact ha.2

/-- **The projection**: delete `⊤` from an ideal. -/
def p (I : Dom) : Dom := ofIdeal (isIdeal_pSet I).toIdeal

@[simp] theorem mem_p {I : Dom} {a : Chain} : a ∈ p I ↔ a ∈ I ∧ a ≠ ⊤ := Iff.rfl

theorem p_le (I : Dom) : p I ≤ I := fun _ ha => ha.1

theorem p_mono : Monotone p := fun _ _ h _ ha => ⟨h ha.1, ha.2⟩

theorem p_idem (I : Dom) : p (p I) = p I :=
  le_antisymm (fun _ ha => ha.1) (fun _ ha => ⟨ha, ha.2⟩)

/-- `p` is Scott continuous: a directed supremum of ideals has the union as its
underlying set (`mem_sSup_iff`), and intersecting with a fixed set commutes with
that union. -/
theorem scottContinuous_p : ScottContinuous p := by
  intro S hne hd I hI
  refine ⟨?_, fun J hJ a ha => ?_⟩
  · rintro _ ⟨K, hK, rfl⟩
    exact p_mono (hI.1 hK)
  · have hIS : I = sSup S := hI.unique hd.isLUB_sSup
    have haI : a ∈ sSup S := hIS ▸ ha.1
    obtain ⟨K, hK, haK⟩ := (mem_sSup_iff hne hd).mp haI
    exact hJ ⟨K, hK, rfl⟩ ⟨haK, ha.2⟩

/-- `p` bundled as a `ScottHom`, the form `IsProjection` takes. -/
def pHom : ScottHom Dom Dom := ⟨p, scottContinuous_p⟩

@[simp] theorem pHom_apply (I : Dom) : pHom I = p I := rfl

theorem isProjection_pHom : IsProjection pHom := ⟨p_idem, p_le⟩

/-- **`p` carries the compact `↓⊤` to the non-compact `natIdeal`.** -/
theorem p_topIdeal : p topIdeal = natIdeal :=
  le_antisymm (fun _ ha => ha.2) fun _ ha => ⟨mem_topIdeal.mpr le_top, ha⟩

/-! ## 4. `im(p)` is a domain, so `p` is *finitary*

`im(p)` is the ideals of `A` avoiding `⊤`, order-isomorphic to `Idl(ℕ)`. -/

/-- `up K = {↑n | n ∈ K}`. -/
def upSet (K : IdealCompletion ℕ) : Set Chain := {a | ∃ n : ℕ, a = (n : Chain) ∧ n ∈ K}

theorem isIdeal_upSet (K : IdealCompletion ℕ) : Order.IsIdeal (upSet K) := by
  refine ⟨?_, ⟨((0 : ℕ) : Chain), 0, rfl, bot_mem K⟩, ?_⟩
  · rintro a b hba ⟨n, rfl, hn⟩
    obtain ⟨m, rfl, hmn⟩ := WithTop.le_coe_iff.mp hba
    exact ⟨m, rfl, K.lower hmn hn⟩
  · rintro a ⟨n, rfl, hn⟩ b ⟨m, rfl, hm⟩
    obtain ⟨k, hk, hnk, hmk⟩ := K.directed n hn m hm
    exact ⟨(k : Chain), ⟨k, rfl, hk⟩, WithTop.coe_le_coe.mpr hnk, WithTop.coe_le_coe.mpr hmk⟩

/-- `up K`, as a point of `D`. -/
def upIdeal (K : IdealCompletion ℕ) : Dom := ofIdeal (isIdeal_upSet K).toIdeal

@[simp] theorem mem_upIdeal {K : IdealCompletion ℕ} {a : Chain} :
    a ∈ upIdeal K ↔ ∃ n : ℕ, a = (n : Chain) ∧ n ∈ K := Iff.rfl

/-- `down J = {n | ↑n ∈ J}`. -/
def downSet (J : Dom) : Set ℕ := {n | ((n : ℕ) : Chain) ∈ J}

theorem isIdeal_downSet (J : Dom) : Order.IsIdeal (downSet J) := by
  refine ⟨fun a b hba ha => J.lower (WithTop.coe_le_coe.mpr hba) ha,
    ⟨0, J.lower (le_of_eq rfl) (bot_mem J)⟩, fun a ha b hb => ?_⟩
  obtain ⟨c, hc, hac, hbc⟩ := J.directed _ ha _ hb
  rcases le_total ((a : ℕ) : Chain) ((b : ℕ) : Chain) with h | h
  · exact ⟨b, hb, WithTop.coe_le_coe.mp h, le_refl b⟩
  · exact ⟨a, ha, le_refl a, WithTop.coe_le_coe.mp h⟩

/-- `down J`, as a point of `Idl(ℕ)`. -/
def downIdeal (J : Dom) : IdealCompletion ℕ := ofIdeal (isIdeal_downSet J).toIdeal

@[simp] theorem mem_downIdeal {J : Dom} {n : ℕ} :
    n ∈ downIdeal J ↔ ((n : ℕ) : Chain) ∈ J := Iff.rfl

theorem downIdeal_upIdeal (K : IdealCompletion ℕ) : downIdeal (upIdeal K) = K := by
  refine le_antisymm (fun n hn => ?_) fun n hn => ⟨n, rfl, hn⟩
  obtain ⟨m, hm, hmK⟩ := mem_upIdeal.mp (mem_downIdeal.mp hn)
  have hnm : n = m := WithTop.coe_eq_coe.mp hm
  subst hnm
  exact hmK

theorem upIdeal_mem_range (K : IdealCompletion ℕ) : upIdeal K ∈ Set.range ⇑pHom := by
  refine ⟨upIdeal K, le_antisymm (fun _ ha => ha.1) fun a ha => ⟨ha, ?_⟩⟩
  obtain ⟨n, rfl, -⟩ := mem_upIdeal.mp ha
  exact WithTop.coe_ne_top

theorem upIdeal_downIdeal {J : Dom} (hJ : ∀ a ∈ J, a ≠ (⊤ : Chain)) :
    upIdeal (downIdeal J) = J := by
  refine le_antisymm (fun a ha => ?_) fun a ha => ?_
  · obtain ⟨n, rfl, hn⟩ := mem_upIdeal.mp ha
    exact hn
  · obtain ⟨n, rfl⟩ := WithTop.ne_top_iff_exists.mp (hJ a ha)
    exact ⟨n, rfl, ha⟩

/-- **`im(p) ≅ Idl(ℕ)`.** -/
def rangeOrderIso : IdealCompletion ℕ ≃o ↥(Set.range ⇑pHom) where
  toFun K := ⟨upIdeal K, upIdeal_mem_range K⟩
  invFun J := downIdeal J.val
  left_inv := downIdeal_upIdeal
  right_inv J := by
    obtain ⟨I, hI⟩ := J.2
    refine Subtype.ext (upIdeal_downIdeal fun a ha => ?_)
    rw [← hI] at ha
    exact (mem_p.mp ha).2
  map_rel_iff' {K L} := by
    constructor
    · intro h n hn
      obtain ⟨m, hm, hmL⟩ := mem_upIdeal.mp (h (show ((n : ℕ) : Chain) ∈ upIdeal K from ⟨n, rfl, hn⟩))
      have hnm : n = m := WithTop.coe_eq_coe.mp hm
      subst hnm
      exact hmL
    · rintro h a ⟨n, rfl, hn⟩
      exact ⟨n, rfl, h hn⟩

/-- **`im(p)` is a domain**, by transport of `Domain (Idl(ℕ))` along
`rangeOrderIso`. This is the clause that makes `p` *finitary*. -/
theorem domain_range :
    @Domain _ (IsProjection.rangeCompletePartialOrder isProjection_pHom) := by
  letI : CompletePartialOrder ↥(Set.range ⇑pHom) :=
    IsProjection.rangeCompletePartialOrder isProjection_pHom
  exact PRep.domain_orderIso rangeOrderIso

theorem isFinitaryProjection_pHom : IsFinitaryProjection pHom :=
  ⟨isProjection_pHom, domain_range⟩

/-! ## 5. The verdict -/

/-- **`p(K(D)) ⊆ K(D)` fails for a finitary projection.** The three conjuncts are
the three things the claim would need: `p` is finitary, `↓⊤` is compact, and its
image under `p` is not. -/
theorem finitaryProjection_not_maps_compacts :
    IsFinitaryProjection pHom ∧ IsCompactElement topIdeal ∧
      ¬ IsCompactElement (pHom topIdeal) :=
  ⟨isFinitaryProjection_pHom, isCompactElement_topIdeal, by
    rw [pHom_apply, p_topIdeal]
    exact not_isCompactElement_natIdeal⟩

/-- The same result as the refutation of the universal statement r0038 asked
about. `Dom` is a domain, so this is a counterexample to the claim as stated and
not to a weakened form of it. -/
theorem not_forall_isCompactElement_apply :
    ¬ ∀ q : ScottHom Dom Dom, IsFinitaryProjection q →
        ∀ k : Dom, IsCompactElement k → IsCompactElement (q k) := by
  intro h
  have := h pHom isFinitaryProjection_pHom topIdeal isCompactElement_topIdeal
  rw [pHom_apply, p_topIdeal] at this
  exact not_isCompactElement_natIdeal this

end ScottDomains.PowerdomainMap.Compacts

/- Axiom audit, by `scripts/axioms.sh` (run, then recorded here so the build emits
no `info` lines). None depends on `sorryAx`.

  …Compacts.isFinitaryProjection_pHom              [propext, Classical.choice, Quot.sound]
  …Compacts.finitaryProjection_not_maps_compacts   [propext, Classical.choice, Quot.sound]
  …Compacts.not_forall_isCompactElement_apply      [propext, Classical.choice, Quot.sound]

The counterexample is therefore a genuine refutation in the same logic the rest
of the development is proved in, not one relying on an extra principle. -/
