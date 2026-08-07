import ScottDomains.Skeleton.Section6b
import Mathlib.Tactic.DeriveFintype

/-!
# Theorem 16's second conjunct is false

Gunter & Scott, *Semantic Domains*, §6.2, quoted from the source PDF:

> **Theorem 16** If `D` is bifinite, then the poset `Fp(D)` of finitary
> projections on `D` is an algebraic lattice and the inclusion map
> `i : Fp(D) ↪ (D → D)` is an embedding.

> Proof: (Sketch) One uses Theorem 6 to show that `Fp(D)` is an algebraic
> lattice. Suppose `f : D → D` is continuous. Let `S_f = {x ∈ K(D) | x ⊑ f(x)}`.
> One can show that there is a least set `N_f` such that `S_f ⊆ N_f ◁ K(D)`. This
> set determines a finitary projection `p_{N_f}` as in the discussion before
> Theorem 6. On the other hand, if `f : D → D` is a finitary projection then
> `N_f = im(f) ∩ K(D)` and `f = p_{N_f}`. The remaining steps required to verify
> that `f ↦ N_f` is a projection are straight-forward.

The first conjunct is `ScottDomains.thm16` (r0028). **This file refutes the
second conjunct**: there is a bifinite domain `D` — a five-element poset — and a
continuous `f : D → D` for which no finitary projection below `f` is greatest, so
no map `s : (D → D) → Fp(D)` whatever, not even a merely monotone one, can
satisfy the two equations that make `(i, s)` an embedding–projection pair. This
is outcome 3 of the round's plan, and it subsumes outcomes 1 and 2: no repair of
the sketch can exist, because the statement the sketch aims at is false.

## What "embedding" means here

The paper fixes the term in §3.1, and `ScottHom.IsEmbeddingProjectionPair`
(`Projection.lean`) is its transcription:

> A pair of continuous functions `g : D → E` and `f : E → D` is said to be an
> **embedding–projection pair** (`g` is the embedding and `f` is the projection)
> if they satisfy `f ∘ g = id_D` and `g ∘ f ⊑ id_E`.

So "the inclusion `i : Fp(D) ↪ (D → D)` is an embedding" asserts the existence of
a continuous `s : (D → D) → Fp(D)` with `s ∘ i = id` and `i ∘ s ⊑ id`. The
sketch's last sentence — "the remaining steps required to verify that `f ↦ N_f`
is a projection" — names `s` explicitly as `f ↦ p_{N_f}`, which confirms the
reading. The alternative reading, *order*-embedding, is not a candidate: the
order on `Fp(D)` **is** the restriction of the pointwise order (`Fp.le_def`, by
`Iff.rfl`), so under that reading the conjunct is true by definition and the
paper's proof sketch would have nothing to prove.

`not_exists_monotone_projection` below is stated for an arbitrary function `s`
assumed only **monotone**, which is weaker than continuous; `TwoMub.not_isEmbeddingProjectionPair`
is the corollary phrased in `ScottHom.IsEmbeddingProjectionPair` itself. Refuting
the monotone form refutes every strengthening of it.

## Why the conjunct fails: the order of the inclusion is backwards

`Fp.le_iff_fpBasis_subset_stableCompacts` below is the exact criterion, and it is
the diagnosis of the sketch:

> For `p ∈ Fp(D)` with basis `N = im(p) ∩ K(D)`, and `f : D → D` continuous,
> `p ⊑ f` **if and only if** `N ⊆ S_f`.

Forward, because `p` fixes its basis: `k = p(k) ⊑ f(k)`. Backward, because
`p(x) = ⨆{k ∈ N | k ⊑ x}` and each such `k` has `k ⊑ f(k) ⊑ f(x)`.

The paper takes `N_f` to be the **least normal set containing** `S_f`. The
criterion asks for a normal set **contained in** `S_f`. The two agree exactly
when `S_f` is itself normal. When `f` is a finitary projection `S_f` *is* normal
— indeed `S_f = im(f) ∩ K(D)` (`stableCompacts_val` below), so the sketch's
round-trip half `s(i(p)) = p` is correct. For general `f` it is not, and then
`p_{N_f} ⊑ f` fails, which is the obstacle r0028 recorded. What r0028 could not
yet say is that no other choice of `N_f` rescues the claim: the largest normal
subposet of `K(D)` inside `S_f` need not exist.

## The witness

`TwoMub` is `{⊥, a, b, m₁, m₂}` with `a, b` incomparable and both strictly below
the two incomparable elements `m₁, m₂`, which are the two *minimal upper bounds*
of `{a, b}`. It is finite, so it is a cpo, a domain (every element is compact),
and bifinite (`K(D)` is finite and normal in itself, so it is a Plotkin order).
It is the smallest poset that is bifinite without being bounded complete — it is
Figure 3's failure of bounded completeness, not of the Plotkin condition.

Take `f = λ x. m₁`, constant, hence continuous. Then `S_f = ↓m₁ = {⊥, a, b, m₁}`,
which omits `m₂`. A normal `N ⊆ K(D)` containing both `a` and `b` must contain
every minimal upper bound of `a` and `b` — both `m₁` **and** `m₂` — so it is not
contained in `S_f`. Hence `{⊥, a, m₁}` and `{⊥, b, m₁}` are two *maximal* normal
subposets inside `S_f`, and the finitary projections they determine are two
incomparable maximal elements of `{p ∈ Fp(D) | p ⊑ f}`. That set therefore has no
greatest element, and `s(f)` would have to be one: for every finitary projection
`p ⊑ f`, monotonicity and `s ∘ i = id` give `p = s(p) ⊑ s(f)`, while `i ∘ s ⊑ id`
gives `s(f) ⊑ f`.

The formal argument does not need the two projections to be *maximal*, only to
exist: `isGreatest_of_section` produces a projection `q ⊑ f` above both, and then
`q(a) = a` and `q(b) = b` force `q(m₂) ⊒ a, b` with `q(m₂) ⊑ m₂`, so `q(m₂) = m₂`,
contradicting `q(m₂) ⊑ f(m₂) = m₁`.

## Scope of the refutation

`thm16_first_conjunct` below instantiates `thm16` at `TwoMub`, so the same `D`
satisfies Theorem 16's hypothesis and its first conjunct. The refutation is
therefore of the second conjunct alone, at a `D` where the rest of the theorem
holds — it is not a complaint about the hypothesis.
-/

namespace ScottDomains.FpEmbedding

variable {α : Type*}

/-! ## Finite posets

Four facts that make a finite poset a bifinite domain and a monotone map between
finite posets Scott continuous. Nothing here is specific to the witness; it is
the machinery any finite counterexample in this development would need. -/

section Finite

/-- A finite subset of a nonempty directed set has an upper bound **inside the
directed set**. Induction on the finite subset: the directed set supplies a
witness above the new point and above the bound already found. Stated for a
subset `t` of `s` rather than for `s` itself because directedness of `s` says
nothing about directedness of a piece of `s`, so the induction cannot be run on
`s` directly. -/
theorem exists_upperBound_mem_of_finite [Preorder α] {s : Set α}
    (hd : DirectedOn (· ≤ ·) s) (hne : s.Nonempty) {t : Set α} (ht : t.Finite) :
    t ⊆ s → ∃ u ∈ s, ∀ y ∈ t, y ≤ u := by
  induction t, ht using Set.Finite.induction_on with
  | empty =>
    intro _
    obtain ⟨u, hu⟩ := hne
    exact ⟨u, hu, fun y hy => absurd hy (Set.notMem_empty y)⟩
  | @insert a r _ _ ih =>
    intro hsub
    obtain ⟨u, hu, hru⟩ := ih fun y hy => hsub (Set.mem_insert_of_mem a hy)
    obtain ⟨c, hc, hac, huc⟩ := hd a (hsub (Set.mem_insert a r)) u hu
    refine ⟨c, hc, ?_⟩
    rintro y (rfl | hy)
    · exact hac
    · exact (hru y hy).trans huc

/-- A finite nonempty directed set has a greatest element, which is then its
least upper bound. -/
theorem isLUB_of_finite_directed [Preorder α] {s : Set α} (hfin : s.Finite)
    (hne : s.Nonempty) (hd : DirectedOn (· ≤ ·) s) : ∃ u ∈ s, IsLUB s u := by
  obtain ⟨u, hu, hub⟩ := exists_upperBound_mem_of_finite hd hne hfin subset_rfl
  exact ⟨u, hu, hub, fun v hv => hv hu⟩

/-- **In a finite poset every element is compact.** A nonempty directed set
attains its least upper bound, so the element required by compactness is the
attained value itself. -/
theorem isCompactElement_of_finite [PartialOrder α] [Finite α] (k : α) :
    IsCompactElement k := by
  intro s u _ hd hlub hku
  obtain ⟨g, hg, hglub⟩ := isLUB_of_finite_directed s.toFinite ‹s.Nonempty› hd
  exact ⟨g, hg, (hlub.unique hglub) ▸ hku⟩

/-- **A finite cpo is a domain.** Algebraic because every element is compact
(`isCompactElement_of_finite`), and `K(D)` is countable because the whole type
is. -/
theorem domain_of_finite [CompletePartialOrder α] [Finite α] : Domain α :=
  { __ := isAlgebraic_of_forall_isCompactElement (isCompactElement_of_finite (α := α))
    countable_compacts := (compacts α).to_countable }

/-- **On a finite poset, monotone implies Scott continuous.** A nonempty directed
set has a greatest element `m`; the least upper bound hypothesis pins `a = m`, and
`g m` is then the greatest element of `g '' d`. -/
theorem scottContinuous_of_monotone_of_finite {β : Type*} [PartialOrder α] [Finite α]
    [Preorder β] {g : α → β} (hg : Monotone g) : ScottContinuous g := by
  intro d hne hd a ha
  obtain ⟨m, hm, hmlub⟩ := isLUB_of_finite_directed d.toFinite hne hd
  rw [ha.unique hmlub]
  refine ⟨?_, fun v hv => hv ⟨m, hm, rfl⟩⟩
  rintro _ ⟨y, hy, rfl⟩
  exact hg (hmlub.1 hy)

/-- **On a finite cpo every projection is finitary.** The image of a projection is
a subtype of a finite type, hence finite, hence a domain by
`domain_of_finite`. -/
theorem isFinitaryProjection_of_finite [CompletePartialOrder α] [Finite α]
    {p : ScottHom α α} (hp : ScottHom.IsProjection p) : ScottHom.IsFinitaryProjection p :=
  ⟨hp, by
    letI : CompletePartialOrder ↥(Set.range ⇑p) := ScottHom.IsProjection.rangeCompletePartialOrder hp
    exact domain_of_finite⟩

end Finite

/-! ## `S_f` and the criterion for `p ⊑ f`

The paper's `S_f = {x ∈ K(D) | x ⊑ f(x)}`, and the exact characterization of
which finitary projections lie below `f`. -/

section StableCompacts

variable [CompletePartialOrder α]

/-- The paper's `S_f = {x ∈ K(D) | x ⊑ f(x)}`: the compact elements `f` moves
upward, equivalently the compact pre-fixed points of `f`. -/
def stableCompacts (f : ScottHom α α) : Set α := {x ∈ compacts α | x ≤ f x}

/-- **The obstruction, stated once and for all.** If the inclusion
`i : Fp(D) ↪ (D → D)` has a monotone left inverse `s` that is also below the
identity, then for every continuous `f` the finitary projections below `f` have a
**greatest** element, namely `s f`.

Only monotonicity of `s` is used, so this rules out continuous `s` a fortiori.
The order on `↥(Fp α)` is the pointwise order (`Fp.le_def`), which is the order
`thm16`'s middle conjunct pins the lattice to, so the statement does not depend
on which cpo structure `Fp(D)` is given. -/
theorem isGreatest_of_section (s : ScottHom α α → ↥(Fp α)) (hmono : Monotone s)
    (hsec : ∀ p : ↥(Fp α), s p.val = p) (hproj : ∀ g : ScottHom α α, (s g).val ≤ g)
    (f : ScottHom α α) : IsGreatest {p : ↥(Fp α) | p.val ≤ f} (s f) := by
  refine ⟨hproj f, fun p hp => ?_⟩
  have h := hmono hp
  rwa [hsec p] at h

variable [Domain α]

omit [Domain α] in
/-- **`p ⊑ f` implies `im(p) ∩ K(D) ⊆ S_f`.** A projection fixes its own image, so
a basis element `k` satisfies `k = p(k) ⊑ f(k)`. -/
theorem fpBasis_subset_stableCompacts {p : ↥(Fp α)} {f : ScottHom α α} (h : p.val ≤ f) :
    fpBasis p ⊆ stableCompacts f := by
  rintro k ⟨hkr, hkc⟩
  refine ⟨hkc, ?_⟩
  calc k = p.val k := (p.2.isProjection.apply_of_mem_range hkr).symm
    _ ≤ f k := h k

/-- **`im(p) ∩ K(D) ⊆ S_f` implies `p ⊑ f`.** Rewriting `p` as `p_N` for
`N = im(p) ∩ K(D)` (Theorem 6, `normalHom_fpBasis`), `p(x)` is the supremum of
`N ∩ ↓x`, and each `k` in that set has `k ⊑ f(k) ⊑ f(x)` by monotonicity. -/
theorem le_of_fpBasis_subset_stableCompacts {p : ↥(Fp α)} {f : ScottHom α α}
    (h : fpBasis p ⊆ stableCompacts f) : p.val ≤ f := by
  rw [← normalHom_fpBasis p]
  intro x
  refine ((fpBasis_isNormalIn p).directedOn_inter_Iic x).sSup_le ?_
  rintro y ⟨hy, hyx⟩
  exact (h hy).2.trans (f.monotone hyx)

/-- **The criterion.** A finitary projection is below `f` exactly when its basis
is contained in `S_f`. The paper's sketch builds the least normal set
*containing* `S_f`; this says the requirement is a normal set *contained in*
`S_f`. -/
theorem Fp.le_iff_fpBasis_subset_stableCompacts {p : ↥(Fp α)} {f : ScottHom α α} :
    p.val ≤ f ↔ fpBasis p ⊆ stableCompacts f :=
  ⟨fpBasis_subset_stableCompacts, le_of_fpBasis_subset_stableCompacts⟩

omit [Domain α] in
/-- **The sketch's round-trip half is correct.** When `f` is itself a finitary
projection, `S_f = im(f) ∩ K(D)`, which is normal, so the least normal set
containing `S_f` is `S_f` and `p_{N_f} = f`. `⊆` is `p(x) ⊑ x` together with
`x ⊑ p(x)`, giving `p(x) = x`; `⊇` is that `p` fixes its image. -/
theorem stableCompacts_val (p : ↥(Fp α)) : stableCompacts p.val = fpBasis p := by
  ext x
  constructor
  · rintro ⟨hxc, hxp⟩
    exact ⟨⟨x, le_antisymm (p.2.isProjection.le x) hxp⟩, hxc⟩
  · rintro ⟨hxr, hxc⟩
    exact ⟨hxc, le_of_eq (p.2.isProjection.apply_of_mem_range hxr).symm⟩

end StableCompacts

/-! ## The witness `TwoMub` -/

/-- The five-element poset `{⊥, a, b, m₁, m₂}`: `a` and `b` are incomparable, and
`m₁` and `m₂` are the two incomparable **minimal upper bounds** of `{a, b}`. It is
bifinite and not bounded complete, and it is the smallest such poset. -/
inductive TwoMub where
  /-- The least element. -/
  | bot
  /-- One of the two incomparable elements whose upper bounds split. -/
  | a
  /-- The other one. -/
  | b
  /-- One minimal upper bound of `{a, b}`. -/
  | m₁
  /-- The other minimal upper bound of `{a, b}`. -/
  | m₂
  deriving DecidableEq, Fintype

namespace TwoMub

/-- The order relation, as a Boolean-valued function so that every statement
about `TwoMub` is settled by `decide`. -/
def leB : TwoMub → TwoMub → Bool
  | .bot, _ => true
  | .a, .a => true
  | .a, .m₁ => true
  | .a, .m₂ => true
  | .b, .b => true
  | .b, .m₁ => true
  | .b, .m₂ => true
  | .m₁, .m₁ => true
  | .m₂, .m₂ => true
  | _, _ => false

/-- `x ⊑ y` on `TwoMub`. -/
protected def le (x y : TwoMub) : Prop := leB x y = true

instance instDecidableLe (x y : TwoMub) : Decidable (TwoMub.le x y) :=
  inferInstanceAs (Decidable (leB x y = true))

instance instPartialOrder : PartialOrder TwoMub where
  le := TwoMub.le
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide

instance instDecidableLe' (x y : TwoMub) : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (TwoMub.le x y))

theorem bot_le' : ∀ x : TwoMub, TwoMub.bot ≤ x := by decide

/-- Every directed subset of a finite poset has a least upper bound: the empty
set has `⊥`, and a nonempty one has a greatest element. -/
theorem exists_isLUB {s : Set TwoMub} (hs : DirectedOn (· ≤ ·) s) : ∃ u, IsLUB s u := by
  rcases Set.eq_empty_or_nonempty s with rfl | hne
  · exact ⟨TwoMub.bot, fun x hx => absurd hx (Set.notMem_empty x), fun v _ => bot_le' v⟩
  · obtain ⟨u, _, hu⟩ := isLUB_of_finite_directed s.toFinite hne hs
    exact ⟨u, hu⟩

open Classical in
/-- `sSup`, branching on **existence of a least upper bound** — the proposition
the `CompletePartialOrder` field needs. Directedness is merely sufficient for it
(`exists_isLUB`), and is not what the definition splits on; that is the rule the
`ScottHom` and `Smash` defects established. -/
noncomputable def sSupAux (s : Set TwoMub) : TwoMub :=
  if h : ∃ u, IsLUB s u then h.choose else TwoMub.bot

theorem isLUB_sSupAux {s : Set TwoMub} (hs : DirectedOn (· ≤ ·) s) :
    IsLUB s (sSupAux s) := by
  have h : ∃ u, IsLUB s u := exists_isLUB hs
  unfold sSupAux
  rw [dif_pos h]
  exact h.choose_spec

noncomputable instance instCompletePartialOrder : CompletePartialOrder TwoMub :=
  { instPartialOrder with
    sSup := sSupAux
    bot := TwoMub.bot
    bot_le := bot_le'
    lubOfDirected := fun _ hd => isLUB_sSupAux hd }

instance instDomain : Domain TwoMub := domain_of_finite

/-- **`TwoMub` is bifinite.** `K(D)` is the whole (finite) type and is normal in
itself, so it is the finite normal subposet the Plotkin condition asks for. -/
theorem isBifinite : IsBifinite TwoMub := fun _ _ hu =>
  ⟨compacts TwoMub, Set.toFinite _, IsNormalIn.refl _, hu⟩

/-- **The shape of `TwoMub`, machine-checked.** `a` and `b` are incomparable;
their upper bounds are exactly `m₁` and `m₂`; and those two are incomparable. So
`{a, b}` is bounded and has no least upper bound: `TwoMub` is bifinite and not
bounded complete, which is what Proposition 15 says is possible and what the
whole construction needs. -/
theorem shape :
    (¬ TwoMub.a ≤ TwoMub.b ∧ ¬ TwoMub.b ≤ TwoMub.a) ∧
      (∀ z : TwoMub, (TwoMub.a ≤ z ∧ TwoMub.b ≤ z) ↔ (z = TwoMub.m₁ ∨ z = TwoMub.m₂)) ∧
      (¬ TwoMub.m₁ ≤ TwoMub.m₂ ∧ ¬ TwoMub.m₂ ≤ TwoMub.m₁) := by decide

/-- Theorem 16's **first** conjunct at `TwoMub`, so that the refutation below is
of the second conjunct alone and not of the hypothesis. -/
theorem thm16_first_conjunct :
    ∃ L : CompleteLattice ↥(Fp TwoMub),
      (∀ p q : ↥(Fp TwoMub), (letI := L; p ≤ q) ↔ ∀ x, p.val x ≤ q.val x) ∧
      @IsCompactlyGenerated _ L :=
  thm16 isBifinite

/-! ### The continuous function and the two projections below it -/

/-- `f = λ x. m₁`, continuous because constant. `S_f = ↓m₁ = {⊥, a, b, m₁}`, which
omits the second minimal upper bound `m₂`. -/
def fConst : ScottHom TwoMub TwoMub := ScottHom.const TwoMub.m₁

/-- `p_{⊥,a,m₁}`: the finitary projection whose basis is `{⊥, a, m₁}`. -/
def p₁Fun : TwoMub → TwoMub
  | .bot => .bot
  | .a => .a
  | .b => .bot
  | .m₁ => .m₁
  | .m₂ => .a

/-- `p_{⊥,b,m₁}`: the finitary projection whose basis is `{⊥, b, m₁}`. -/
def p₂Fun : TwoMub → TwoMub
  | .bot => .bot
  | .a => .bot
  | .b => .b
  | .m₁ => .m₁
  | .m₂ => .b

theorem monotone_p₁Fun : Monotone p₁Fun := by
  have h : ∀ x y : TwoMub, x ≤ y → p₁Fun x ≤ p₁Fun y := by decide
  exact fun x y hxy => h x y hxy

theorem monotone_p₂Fun : Monotone p₂Fun := by
  have h : ∀ x y : TwoMub, x ≤ y → p₂Fun x ≤ p₂Fun y := by decide
  exact fun x y hxy => h x y hxy

/-- `p₁` as an element of the function space. -/
def p₁ : ScottHom TwoMub TwoMub :=
  ⟨p₁Fun, scottContinuous_of_monotone_of_finite monotone_p₁Fun⟩

/-- `p₂` as an element of the function space. -/
def p₂ : ScottHom TwoMub TwoMub :=
  ⟨p₂Fun, scottContinuous_of_monotone_of_finite monotone_p₂Fun⟩

theorem isProjection_p₁ : ScottHom.IsProjection p₁ := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · show p₁Fun (p₁Fun x) = p₁Fun x
    revert x; decide
  · show p₁Fun x ≤ x
    revert x; decide

theorem isProjection_p₂ : ScottHom.IsProjection p₂ := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · show p₂Fun (p₂Fun x) = p₂Fun x
    revert x; decide
  · show p₂Fun x ≤ x
    revert x; decide

/-- `p₁` as a member of `Fp(D)`. -/
def P₁ : ↥(Fp TwoMub) := ⟨p₁, isFinitaryProjection_of_finite isProjection_p₁⟩

/-- `p₂` as a member of `Fp(D)`. -/
def P₂ : ↥(Fp TwoMub) := ⟨p₂, isFinitaryProjection_of_finite isProjection_p₂⟩

theorem p₁_le_fConst : p₁ ≤ fConst := by
  intro x
  show p₁Fun x ≤ TwoMub.m₁
  revert x; decide

theorem p₂_le_fConst : p₂ ≤ fConst := by
  intro x
  show p₂Fun x ≤ TwoMub.m₁
  revert x; decide

/-- **`S_f = {⊥, a, b, m₁}`.** Every element of `TwoMub` is compact, so `S_f` is
just `↓m₁`, and it omits the second minimal upper bound `m₂` of `{a, b}`. That
omission is the whole obstruction: a normal subposet containing `a` and `b`
contains every minimal upper bound of the pair, hence contains `m₂`, hence is not
contained in `S_f`. -/
theorem stableCompacts_fConst :
    stableCompacts fConst = {TwoMub.bot, TwoMub.a, TwoMub.b, TwoMub.m₁} := by
  have hdown : ∀ x : TwoMub, x ≤ TwoMub.m₁ ↔
      (x = TwoMub.bot ∨ x = TwoMub.a ∨ x = TwoMub.b ∨ x = TwoMub.m₁) := by decide
  ext x
  constructor
  · rintro ⟨-, hx⟩
    exact (hdown x).mp hx
  · intro hx
    exact ⟨isCompactElement_of_finite x, (hdown x).mpr hx⟩

/-- `p₁` and `p₂` are **incomparable** finitary projections below `f`: `p₁` fixes
`a` and kills `b`, `p₂` does the reverse. This is the concrete reason
`{p ∈ Fp(D) | p ⊑ f}` has no greatest element. -/
theorem p₁_incomparable_p₂ : ¬ p₁ ≤ p₂ ∧ ¬ p₂ ≤ p₁ := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hab := h TwoMub.a
    revert hab
    show ¬ (TwoMub.a ≤ TwoMub.bot)
    decide
  · have hba := h TwoMub.b
    revert hba
    show ¬ (TwoMub.b ≤ TwoMub.bot)
    decide

/-! ### The refutation -/

/-- **No finitary projection below `f = λ x. m₁` is greatest.** A greatest one `q`
dominates both `p₁` and `p₂`, so `q(a) = a` and `q(b) = b`; monotonicity then puts
both `a` and `b` below `q(m₂)`, and `q ⊑ id` puts `q(m₂)` below `m₂`. The only
element of `TwoMub` above `a` and `b` and below `m₂` is `m₂` itself, so
`q(m₂) = m₂ ⋢ m₁ = f(m₂)`, contradicting `q ⊑ f`. -/
theorem not_isGreatest_below_fConst (q : ↥(Fp TwoMub)) :
    ¬ IsGreatest {p : ↥(Fp TwoMub) | p.val ≤ fConst} q := by
  rintro ⟨hqf, hub⟩
  have hq : ScottHom.IsProjection q.val := q.2.isProjection
  have h₁ : P₁ ≤ q := hub p₁_le_fConst
  have h₂ : P₂ ≤ q := hub p₂_le_fConst
  have hqa : q.val TwoMub.a = TwoMub.a := le_antisymm (hq.le _) (h₁ TwoMub.a)
  have hqb : q.val TwoMub.b = TwoMub.b := le_antisymm (hq.le _) (h₂ TwoMub.b)
  have ham : TwoMub.a ≤ q.val TwoMub.m₂ := by
    rw [← hqa]; exact q.val.monotone (by decide)
  have hbm : TwoMub.b ≤ q.val TwoMub.m₂ := by
    rw [← hqb]; exact q.val.monotone (by decide)
  have key : ∀ z : TwoMub, TwoMub.a ≤ z → TwoMub.b ≤ z → z ≤ TwoMub.m₂ →
      z ≤ TwoMub.m₁ → False := by decide
  exact key _ ham hbm (hq.le _) (hqf TwoMub.m₂)

end TwoMub

/-- **Theorem 16's second conjunct is false.** There is no map
`s : (D → D) → Fp(D)` — not even a merely monotone one, let alone a continuous
one — satisfying `s ∘ i = id` and `i ∘ s ⊑ id`, where `i : Fp(D) ↪ (D → D)` is
the inclusion and `D = TwoMub` is bifinite.

`isGreatest_of_section` turns such an `s` into a greatest finitary projection
below `f = λ x. m₁`, and `TwoMub.not_isGreatest_below_fConst` says there is
none. -/
theorem TwoMub.not_exists_monotone_projection :
    ¬ ∃ s : ScottHom TwoMub TwoMub → ↥(Fp TwoMub),
        Monotone s ∧ (∀ p : ↥(Fp TwoMub), s p.val = p) ∧
          ∀ g : ScottHom TwoMub TwoMub, (s g).val ≤ g := by
  rintro ⟨s, hmono, hsec, hproj⟩
  exact TwoMub.not_isGreatest_below_fConst _
    (isGreatest_of_section s hmono hsec hproj TwoMub.fConst)

/-- The same refutation phrased in the paper's own vocabulary: for the bifinite
domain `TwoMub`, no continuous `i` with underlying function the inclusion
`Subtype.val : Fp(D) → (D → D)` and no continuous `s` form an
embedding–projection pair. Since `Fp(D)`'s order is the pointwise order and `i`
is the inclusion, this is exactly "the inclusion `i : Fp(D) ↪ (D → D)` is an
embedding", which Theorem 16 asserts. -/
theorem TwoMub.not_isEmbeddingProjectionPair
    (i : ScottHom ↥(Fp TwoMub) (ScottHom TwoMub TwoMub)) (hi : ∀ p, i p = p.val)
    (s : ScottHom (ScottHom TwoMub TwoMub) ↥(Fp TwoMub)) :
    ¬ ScottHom.IsEmbeddingProjectionPair i s := by
  rintro ⟨h₁, h₂⟩
  refine TwoMub.not_exists_monotone_projection ⟨⇑s, s.monotone, fun p => ?_, fun g => ?_⟩
  · rw [← hi p]; exact h₁ p
  · rw [← hi (s g)]; exact h₂ g

end ScottDomains.FpEmbedding
