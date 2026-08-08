import ScottDomains.Flat
import ScottDomains.Powerdomain.Hoare
import ScottDomains.Powerdomain.Smyth
import ScottDomains.Powerdomain.Plotkin
import ScottDomains.Powerset

/-!
# §5.2–§5.3's worked computations of the three powerdomains of `N⊥`

Gunter & Scott, *Semantic Domains*, §5.2 (printed p. 26) and §5.3 (printed
p. 27). The paper computes all three powerdomains of the flat naturals and then
uses them to separate three readings of non-determinism. Every sentence
formalized below was read off a 170 dpi rendering of the physical page, because
`pdftotext` renders `♮`/`♯`/`♭` as `\`/`]`/`[`.

The single reason none of this was statable before r0041 is that `N⊥` did not
exist in the development; `ScottDomains.Flat` builds it, and `Flat.compacts_eq_univ`
supplies the paper's opening move — *"Since `K(N⊥) = N⊥` …"*.

## Orientation, once

`IdealCompletion.lean` fixes the convention: the paper's `a ⊢ b` is Mathlib's
`b ≤ a`. So the paper's `u ⊢♮ v` is `v ≤ u` here, and every statement below is
given in Mathlib's orientation with the paper's own form quoted in the docstring.

## What is proved

| paper sentence (§ / printed p.) | declaration |
| ------------------------------- | ----------- |
| `(N⊥)♭` is isomorphic to `P N` under subset inclusion (5.2 / 26) | `hoare_natBot_orderIso_powerset` |
| `(N⊥)♯` is isomorphic to `{N} ∪ P*f(N)` under superset inclusion (5.2 / 26) | `smyth_natBot_orderIso` |
| `u ⊢♮ v` iff (1) `⊥ ∈ v` and `u ⊇ v`, or (2) `u = v` (5.2 / 26) | `plotkin_le_iff`, and `plotkin_printed_clause_one_fails` |
| `(N⊥)♮` is the finite non-empty subsets of `N` together with the arbitrary subsets of `N⊥` containing `⊥` (5.2 / 26) | `plotkin_natBot_orderIso` |
| `{\|1, ⊥\|} = ⊥ = {\|⊥\|}` in `(N⊥)♯` (5.3 / 27) | `smyth_oneBot_eq_bot`, `smyth_bot_eq_bot` |
| `{\|1, ⊥\|} = {\|1\|}` and `{\|1, ⊥\|} ≠ ⊥` in `(N⊥)♭` (5.3 / 27) | `hoare_oneBot_eq_one`, `hoare_oneBot_ne_bot` |
| `{\|1, ⊥\|}`, `{\|1\|}`, `{\|⊥\|}` are all distinct in `(N⊥)♮` (5.3 / 27) | `plotkin_three_distinct` |

## One place where the paper's printed statement is false

The printed characterization of `⊢♮` over `P*f(N⊥)` (§5.2, p. 26) reads

> `u ⊢♮ v` iff 1. `⊥ ∈ v` and `u ⊇ v` or 2. `u = v`.

Clause 1 is **strictly stronger than the truth**. Take `u = {1}` and
`v = {1, ⊥}`. Then `u ⊢♯ v` holds because `⊥ ∈ v`, and `u ⊢♭ v` holds because
`1 ∈ u` covers `1 ∈ v` and `1 ⊒ ⊥` covers `⊥ ∈ v`; so `u ⊢♮ v`. But `u ⊉ v`
(`⊥ ∉ u`) and `u ≠ v`. The correct condition, proved as `plotkin_le_iff`, is

> `u ⊢♮ v` iff 1. `⊥ ∈ v` and `v ∖ {⊥} ⊆ u`, or 2. `u = v`,

which agrees with the paper's whenever `⊥ ∈ u`, and the paper's two following
sentences (the principal ideals at `⊥`-free sets, and `⋃x ⊆ ⋃y` for the rest) are
both correct as printed under the corrected clause.
`plotkin_printed_clause_one_fails` is the kernel-checked refutation.
-/

namespace ScottDomains.Flat

open ScottDomains

universe u

-- `Flat.instCompletePartialOrder` is `noncomputable` (its `sSup` chooses the
-- unique non-`⊥` member), so every definition below that mentions a powerdomain
-- of `N⊥` inherits that. The section marker states it once.
noncomputable section

/-! ## Generic tools

Two facts about the ideal completion that the computations below need and that
neither `IdealCompletion.lean` nor Mathlib's `Order.Ideal` states. They are
declared here, in this agent's namespace, rather than added to `IdealCompletion`:
their only consumers are in this file. -/

/-- **A finite subset of an ideal is bounded inside the ideal.** `Order.Ideal`
carries only *binary* directedness; the paper's own definition of *ideal* quantifies
over arbitrary finite subsets, and this is the induction that reconciles the two.
Proved for the ideal completion of any pre-order. -/
theorem exists_mem_upperBound {A : Type u} [Preorder A] (I : IdealCompletion A)
    (t : Finset A) (ht : ∀ a ∈ t, a ∈ I) : ∃ w ∈ I, ∀ a ∈ t, a ≤ w := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    obtain ⟨w, hw⟩ := I.nonempty
    exact ⟨w, hw, by simp⟩
  | @insert a t _ ih =>
    obtain ⟨w, hw, hle⟩ := ih fun b hb => ht b (Finset.mem_insert_of_mem hb)
    obtain ⟨z, hz, haz, hwz⟩ := I.directed a (ht a (Finset.mem_insert_self a t)) w hw
    refine ⟨z, hz, fun b hb => ?_⟩
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact haz
    · exact (hle b hb).trans hwz

/-! ## `K(X⊥)` as a copy of `X⊥`

`Flat.compacts_eq_univ` says the basis is everything, so `↥(compacts (Flat X))`
is a copy of `Flat X`. `cpt` is that copy's constructor; the three lemmas after it
are what every computation below uses to move between the two. -/

variable {X : Type u}

/-- A point of `X⊥` read as a point of `K(X⊥)`. Total, because every element of a
flat cpo is compact. -/
def cpt (a : Flat X) : ↥(compacts (Flat X)) := ⟨a, isCompactElement a⟩

@[simp] theorem cpt_val (a : Flat X) : (cpt a : Flat X) = a := rfl

@[simp] theorem coe_cpt (k : ↥(compacts (Flat X))) : cpt (k : Flat X) = k := rfl

@[simp] theorem cpt_le_cpt {a b : Flat X} : cpt a ≤ cpt b ↔ a ≤ b := Iff.rfl

@[simp] theorem cpt_bot : cpt (⊥ : Flat X) = ⊥ := rfl

@[simp] theorem cpt_inj {a b : Flat X} : cpt a = cpt b ↔ a = b :=
  ⟨fun h => congrArg Subtype.val h, fun h => congrArg cpt h⟩

/-- The two shapes of an element of `X⊥`. -/
theorem flat_cases (a : Flat X) : a = ⊥ ∨ ∃ x : X, a = up x := by
  cases a with
  | bot => exact Or.inl rfl
  | up x => exact Or.inr ⟨x, rfl⟩

/-- The two shapes of a compact element of `X⊥` — which, by `compacts_eq_univ`,
is any element at all. -/
theorem compact_cases (k : ↥(compacts (Flat X))) : k = ⊥ ∨ ∃ x : X, k = cpt (up x) := by
  rcases flat_cases (k : Flat X) with h | ⟨x, hx⟩
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr ⟨x, Subtype.ext hx⟩

/-- In `K(X⊥)`, an element above `up x` **is** `up x`: the flat order has nothing
strictly above a non-`⊥` point. -/
theorem eq_cpt_up_of_le {x : X} {k : ↥(compacts (Flat X))} (h : cpt (up x) ≤ k) :
    k = cpt (up x) :=
  Subtype.ext (eq_of_up_le h)

theorem cpt_up_ne_bot {x : X} : cpt (up x) ≠ (⊥ : ↥(compacts (Flat X))) :=
  fun h => up_ne_bot (congrArg Subtype.val h)

/-! ## The carrier `K(N⊥)`, and the paper's `1` -/

/-- `K(N⊥)`, which by `compacts_eq_univ` is `N⊥` itself. -/
abbrev KNat : Type := ↥(compacts NatBot)

/-- `1 : N⊥`, the output of the paper's program `P₂`. -/
def kOne : KNat := cpt (up 1)

theorem kOne_ne_bot : kOne ≠ (⊥ : KNat) := cpt_up_ne_bot

theorem not_kOne_le_bot : ¬ kOne ≤ (⊥ : KNat) := fun h => up_ne_bot (eq_of_up_le h).symm

/-! ## `(N⊥)♭ ≅ P N`

> As an example, we compute the lower powerdomain of `N⊥`. Since `K(N⊥) = N⊥`,
> the lower powerdomain of `N⊥` is the set of ideals over the pre-order
> `⟨P*f(N⊥), ⊢♭⟩`. … Now, if `u` and `v` both contain `⊥`, then `u ⊢♭ v` iff
> `u ⊇ v`. Hence we may identify an ideal `x ∈ (N⊥)♭` with the union `⋃x` of all
> the elements in `x`. Thus `(N⊥)♭` is isomorphic to the domain `P N` of all
> subsets of `N` under subset inclusion. (§5.2, printed p. 26)

The isomorphism is `x ↦ ⋃x ∩ N`, written `hoareToSet`; the `∩ N` is the paper's
"identify", since `⊥` lies in every element of every ideal's downward closure and
so carries no information. Its inverse sends `S ⊆ N` to the set of finite
non-empty `u ⊆ N⊥` whose non-`⊥` part lies in `S`. -/

/-- The `N`-part of a finite non-empty subset of `N⊥`. -/
def hoareSet (u : Hoare.Pf KNat) : Set ℕ := {n | cpt (up n) ∈ u}

theorem hoareSet_mono {u v : Hoare.Pf KNat} (h : u ≤ v) : hoareSet u ⊆ hoareSet v := by
  intro n hn
  obtain ⟨y, hy, hle⟩ := Hoare.Pf.le_def.mp h _ hn
  rw [eq_cpt_up_of_le hle] at hy
  exact hy

@[simp] theorem hoareSet_bot : hoareSet (⊥ : Hoare.Pf KNat) = ∅ := by
  ext n
  simp only [hoareSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro h
  exact cpt_up_ne_bot (Hoare.Pf.mem_bot.mp h)

/-- The candidate ideal attached to `S ⊆ N`: every finite non-empty `u ⊆ N⊥`
whose non-`⊥` part lies in `S`. -/
def hoareIdealSet (S : Set ℕ) : Set (Hoare.Pf KNat) := {u | hoareSet u ⊆ S}

theorem isIdeal_hoareIdealSet (S : Set ℕ) : Order.IsIdeal (hoareIdealSet S) := by
  classical
  refine ⟨fun u v hvu hu => (hoareSet_mono hvu).trans hu, ⟨⊥, ?_⟩, ?_⟩
  · simp [hoareIdealSet]
  · intro u hu v hv
    refine ⟨Hoare.Pf.ofFinset (u.toFinset ∪ v.toFinset)
        (Finset.Nonempty.inl u.toFinset_nonempty), ?_, ?_, ?_⟩
    · intro n hn
      rcases Finset.mem_union.mp hn with h | h
      · exact hu h
      · exact hv h
    · exact fun a ha => ⟨a, Finset.mem_union_left _ ha, le_rfl⟩
    · exact fun a ha => ⟨a, Finset.mem_union_right _ ha, le_rfl⟩

/-- `⋃x ∩ N`, the paper's identification of an ideal of `(N⊥)♭` with a set of
naturals. -/
def hoareToSet (x : Hoare.Powerdomain NatBot) : Set ℕ := {n | ∃ u ∈ x, cpt (up n) ∈ u}

/-- The inverse map, `S ↦ {u | u ∩ N ⊆ S}`. -/
def hoareOfSet (S : Set ℕ) : Hoare.Powerdomain NatBot :=
  IdealCompletion.ofIdeal (isIdeal_hoareIdealSet S).toIdeal

@[simp] theorem mem_hoareOfSet {S : Set ℕ} {u : Hoare.Pf KNat} :
    u ∈ hoareOfSet S ↔ hoareSet u ⊆ S := Iff.rfl

theorem hoareToSet_hoareOfSet (S : Set ℕ) : hoareToSet (hoareOfSet S) = S := by
  ext n
  constructor
  · rintro ⟨u, hu, hnu⟩
    exact (mem_hoareOfSet.mp hu) hnu
  · intro hn
    refine ⟨Hoare.Pf.ofFinset {cpt (up n)} (Finset.singleton_nonempty _), ?_,
      Finset.mem_singleton_self _⟩
    intro m hm
    have hsing : cpt (up m) = cpt (up n) := Finset.mem_singleton.mp hm
    have hmn : m = n := by simpa using hsing
    exact hmn ▸ hn

/-- The `⊇` half of the round trip, and the only place finite directedness is
spent: a finite non-empty `u` whose non-`⊥` part lies in `⋃x` is dominated by a
single member of `x`, hence lies in `x` by downward closure. -/
theorem mem_of_hoareSet_subset {x : Hoare.Powerdomain NatBot} {u : Hoare.Pf KNat}
    (h : hoareSet u ⊆ hoareToSet x) : u ∈ x := by
  classical
  have key : ∀ k ∈ u.toFinset, ∃ w ∈ x, ∃ y ∈ w, k ≤ y := by
    intro k hk
    rcases compact_cases k with rfl | ⟨n, rfl⟩
    · exact ⟨⊥, IdealCompletion.bot_mem x, ⊥, Hoare.Pf.mem_bot.mpr rfl, le_rfl⟩
    · obtain ⟨w, hw, hnw⟩ := h hk
      exact ⟨w, hw, cpt (up n), hnw, le_rfl⟩
  -- collect a single dominating member of `x`
  have dom : ∀ t : Finset KNat, (∀ k ∈ t, ∃ w ∈ x, ∃ y ∈ w, k ≤ y) →
      ∃ w ∈ x, ∀ k ∈ t, ∃ y ∈ w, k ≤ y := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact fun _ => ⟨⊥, IdealCompletion.bot_mem x, by simp⟩
    | @insert a t _ ih =>
      intro hall
      obtain ⟨w, hw, hdom⟩ := ih fun k hk => hall k (Finset.mem_insert_of_mem hk)
      obtain ⟨w', hw', y, hy, hay⟩ := hall a (Finset.mem_insert_self a t)
      obtain ⟨z, hz, hwz, hw'z⟩ := x.directed w hw w' hw'
      refine ⟨z, hz, fun k hk => ?_⟩
      rcases Finset.mem_insert.mp hk with rfl | hk
      · obtain ⟨y', hy', hyy'⟩ := Hoare.Pf.le_def.mp hw'z y hy
        exact ⟨y', hy', hay.trans hyy'⟩
      · obtain ⟨y₀, hy₀, hky₀⟩ := hdom k hk
        obtain ⟨y₁, hy₁, hy₀y₁⟩ := Hoare.Pf.le_def.mp hwz y₀ hy₀
        exact ⟨y₁, hy₁, hky₀.trans hy₀y₁⟩
  obtain ⟨w, hw, hdom⟩ := dom u.toFinset key
  exact x.lower (Hoare.Pf.le_def.mpr fun k hk => hdom k hk) hw

theorem hoareOfSet_hoareToSet (x : Hoare.Powerdomain NatBot) :
    hoareOfSet (hoareToSet x) = x := by
  ext u
  constructor
  · intro hu
    exact mem_of_hoareSet_subset (mem_hoareOfSet.mp hu)
  · intro hu
    exact mem_hoareOfSet.mpr fun n hn => ⟨u, hu, hn⟩

theorem hoareToSet_subset_iff {x y : Hoare.Powerdomain NatBot} :
    hoareToSet x ⊆ hoareToSet y ↔ x ≤ y := by
  constructor
  · intro h u hu
    have h1 : hoareSet u ⊆ hoareToSet x := fun n hn => ⟨u, hu, hn⟩
    exact mem_of_hoareSet_subset (h1.trans h)
  · rintro h n ⟨u, hu, hnu⟩
    exact ⟨u, h hu, hnu⟩

/-- **`(N⊥)♭ ≅ P N`, under subset inclusion.** The paper's own sentence, §5.2,
printed p. 26. -/
def hoareOrderIso : Hoare.Powerdomain NatBot ≃o Set ℕ where
  toFun := hoareToSet
  invFun := hoareOfSet
  left_inv := hoareOfSet_hoareToSet
  right_inv := hoareToSet_hoareOfSet
  map_rel_iff' := hoareToSet_subset_iff

/-- **`(N⊥)♭` is isomorphic to the domain `P N`.** "Isomorphic" is spelled out as
in `IdealCompletion.thm11_converse`: an order isomorphism that also preserves
every directed supremum, so it is an isomorphism of cpos, with `P N` a domain on
the other side. -/
theorem hoare_natBot_orderIso_powerset :
    ∃ e : Hoare.Powerdomain NatBot ≃o Set ℕ,
      (∀ s : Set (Hoare.Powerdomain NatBot), DirectedOn (· ≤ ·) s →
        e (sSup s) = sSup (e '' s)) ∧ Domain (Set ℕ) :=
  ⟨hoareOrderIso, fun _ hs => hoareOrderIso.map_sSup_of_directedOn hs, inferInstance⟩

/-! ## `(N⊥)♯ ≅ {N} ∪ P*f(N)` under superset inclusion

> Note that if `u` and `v` are finite non-empty subsets of `N⊥` and `⊥ ∈ v`, then
> `u ⊢♯ v`. … let us say that a set `u ∈ P*f(N⊥)` is *non-trivial* if it does not
> contain `⊥` … Now, if `u` and `v` are non-trivial, then `u ⊢♯ v` iff `u ⊆ v`.
> Therefore, if an ideal `x` is non-trivial, then it is the principal ideal
> generated by the intersection of its non-trivial elements! … `(N⊥)♯` is
> isomorphic to the domain of sets `{N} ∪ P*f(N)` ordered by superset inclusion.
> (§5.2, printed p. 26)

The concrete poset is `SmythCarrier`: the subsets of `N` that are either all of
`N` or finite and non-empty, ordered by **⊇**. `N` is its least element, matching
the trivial ideal `⊥` of `(N⊥)♯`. -/

/-- A point of `Pf(K(N⊥))` is *trivial* when it contains `⊥` — the paper's word.
Trivial points are exactly the ones equivalent to the least element. -/
def SmythTrivial (u : Smyth.Basis NatBot) : Prop := (⊥ : KNat) ∈ u.toFinset

theorem smyth_le_bot_iff {u : Smyth.Basis NatBot} : u ≤ ⊥ ↔ SmythTrivial u := by
  constructor
  · intro h
    obtain ⟨a, ha, hab⟩ := h ⊥ (Finset.mem_singleton_self _)
    rcases compact_cases a with rfl | ⟨n, rfl⟩
    · exact ha
    · exact absurd hab (fun hle => up_ne_bot (eq_of_up_le hle).symm)
  · intro h b hb
    exact ⟨⊥, h, bot_le⟩

/-- Above a non-trivial point everything is non-trivial: `u ≤ v` with `⊥ ∉ u`
forces `⊥ ∉ v`, because the Smyth condition would need an element of `u` below
`⊥`. -/
theorem smyth_not_trivial_of_le {u v : Smyth.Basis NatBot} (h : u ≤ v)
    (hu : ¬ SmythTrivial u) : ¬ SmythTrivial v := by
  intro hv
  obtain ⟨a, ha, hab⟩ := h ⊥ hv
  rcases compact_cases a with rfl | ⟨n, rfl⟩
  · exact hu ha
  · exact up_ne_bot (eq_of_up_le hab).symm

/-- On non-trivial points the Smyth order **is** reverse inclusion, which is the
paper's `u ⊢♯ v` iff `u ⊆ v`. -/
theorem smyth_le_iff_of_not_trivial {u v : Smyth.Basis NatBot} (hu : ¬ SmythTrivial u) :
    u ≤ v ↔ v.toFinset ⊆ u.toFinset := by
  constructor
  · intro h b hb
    obtain ⟨a, ha, hab⟩ := h b hb
    rcases compact_cases a with rfl | ⟨n, rfl⟩
    · exact absurd ha hu
    · rw [eq_cpt_up_of_le hab]
      exact ha
  · intro h b hb
    exact ⟨b, h hb, le_rfl⟩

/-- The `N`-part of a point of the Smyth pre-order. -/
def smythSet (u : Smyth.Basis NatBot) : Set ℕ := {n | cpt (up n) ∈ u.toFinset}

theorem up_cpt_injective : Function.Injective (fun n : ℕ => cpt (up n)) := by
  intro m n h
  simpa using h

theorem smythSet_finite (u : Smyth.Basis NatBot) : (smythSet u).Finite := by
  have : smythSet u = (fun n : ℕ => cpt (up n)) ⁻¹' (↑u.toFinset : Set KNat) := rfl
  rw [this]
  exact Set.Finite.preimage (up_cpt_injective.injOn) u.toFinset.finite_toSet

/-- `N` itself is never the `N`-part of a finite set — this is what makes the
trivial ideal a *separate* point of the carrier `{N} ∪ P*f(N)`. -/
theorem not_univ_subset_smythSet (u : Smyth.Basis NatBot) : ¬ (Set.univ ⊆ smythSet u) :=
  fun h => Set.infinite_univ (Set.Finite.subset (smythSet_finite u) h)

/-- The point of `Pf(K(N⊥))` generated by a finite non-empty `S ⊆ N`: the image
of `S` under `n ↦ up n`, which is `⊥`-free. -/
def smythGen {S : Set ℕ} (hf : S.Finite) (hne : S.Nonempty) : Smyth.Basis NatBot :=
  ⟨hf.toFinset.image (fun n : ℕ => cpt (up n)),
    Finset.Nonempty.image (by simpa using hne) _⟩

@[simp] theorem smythSet_smythGen {S : Set ℕ} (hf : S.Finite) (hne : S.Nonempty) :
    smythSet (smythGen hf hne) = S := by
  ext n
  simp [smythSet, smythGen, hf.mem_toFinset]

theorem bot_notMem_smythGen {S : Set ℕ} (hf : S.Finite) (hne : S.Nonempty) :
    (⊥ : KNat) ∉ (smythGen hf hne).toFinset := by
  intro h
  obtain ⟨n, -, hn⟩ := Finset.mem_image.mp h
  exact cpt_up_ne_bot hn

/-- `{N} ∪ P*f(N)`, the paper's carrier: the subsets of `N` that are either all
of `N` or finite and non-empty.

A `structure` and not the subtype `{S : Set ℕ // …}`, for the reason
`Smyth.Basis` is one: the subtype inherits `Subtype.partialOrder` over `⊆`, and
the paper's order here is **⊇**. Two non-defeq `PartialOrder`s on one type is the
incoherence the development keeps out by hand. -/
structure SmythCarrier where
  /-- The underlying set of naturals. -/
  carrier : Set ℕ
  /-- `N` itself, or a finite non-empty set. -/
  mem' : carrier = Set.univ ∨ (carrier.Finite ∧ carrier.Nonempty)

@[ext] theorem SmythCarrier.ext {S T : SmythCarrier} (h : S.carrier = T.carrier) : S = T := by
  cases S; cases T; cases h; rfl

theorem smythCarrier_nonempty (S : SmythCarrier) : S.carrier.Nonempty := by
  rcases S.mem' with h | h
  · rw [h]; exact Set.univ_nonempty
  · exact h.2

/-- **Superset inclusion**, the paper's ordering on `{N} ∪ P*f(N)`. `N` is the
least element, matching the trivial ideal `⊥` of `(N⊥)♯`. -/
instance : PartialOrder SmythCarrier where
  le S T := T.carrier ⊆ S.carrier
  le_refl _ := subset_rfl
  le_trans _ _ _ h₁ h₂ := Set.Subset.trans h₂ h₁
  le_antisymm _ _ h₁ h₂ := SmythCarrier.ext (Set.Subset.antisymm h₂ h₁)

theorem smythCarrier_le_def {S T : SmythCarrier} : S ≤ T ↔ T.carrier ⊆ S.carrier := Iff.rfl

/-- The candidate ideal attached to `S`: every point that is trivial (contains
`⊥`) together with every `⊥`-free point whose `N`-part contains `S`. -/
def smythIdealSet (S : Set ℕ) : Set (Smyth.Basis NatBot) :=
  {v | (⊥ : KNat) ∈ v.toFinset ∨ S ⊆ smythSet v}

theorem isIdeal_smythIdealSet {S : Set ℕ} (hS : S.Nonempty) :
    Order.IsIdeal (smythIdealSet S) := by
  classical
  refine ⟨?_, ⟨⊥, Or.inl ?_⟩, ?_⟩
  · intro v w hwv hv
    by_cases hb : (⊥ : KNat) ∈ w.toFinset
    · exact Or.inl hb
    refine Or.inr fun n hn => ?_
    rcases hv with hv | hv
    · exfalso
      obtain ⟨a, ha, hab⟩ := hwv ⊥ hv
      rcases compact_cases a with rfl | ⟨m, rfl⟩
      · exact hb ha
      · exact up_ne_bot (eq_of_up_le hab).symm
    · obtain ⟨a, ha, hab⟩ := hwv (cpt (up n)) (hv hn)
      rcases compact_cases a with rfl | ⟨m, rfl⟩
      · exact absurd ha hb
      · have hmn : m = n := hab
        rw [← hmn]
        exact ha
  · rw [Smyth.Basis.bot_toFinset]
    exact Finset.mem_singleton_self _
  · intro v hv w hw
    by_cases hbv : (⊥ : KNat) ∈ v.toFinset
    · by_cases hbw : (⊥ : KNat) ∈ w.toFinset
      · exact ⟨v, hv, le_rfl, fun b _ => ⟨⊥, hbw, bot_le⟩⟩
      · exact ⟨w, hw, fun b _ => ⟨⊥, hbv, bot_le⟩, le_rfl⟩
    · by_cases hbw : (⊥ : KNat) ∈ w.toFinset
      · exact ⟨v, hv, le_rfl, fun b _ => ⟨⊥, hbw, bot_le⟩⟩
      · have hSv : S ⊆ smythSet v := hv.resolve_left hbv
        have hSw : S ⊆ smythSet w := hw.resolve_left hbw
        obtain ⟨n₀, hn₀⟩ := hS
        refine ⟨⟨v.toFinset ∩ w.toFinset,
            ⟨cpt (up n₀), Finset.mem_inter.mpr ⟨hSv hn₀, hSw hn₀⟩⟩⟩,
          Or.inr fun n hn => Finset.mem_inter.mpr ⟨hSv hn, hSw hn⟩, ?_, ?_⟩
        · exact fun b hb => ⟨b, (Finset.mem_inter.mp hb).1, le_rfl⟩
        · exact fun b hb => ⟨b, (Finset.mem_inter.mp hb).2, le_rfl⟩

/-- The map `{N} ∪ P*f(N) → (N⊥)♯`. -/
def smythOf (S : SmythCarrier) : Smyth.Powerdomain NatBot :=
  IdealCompletion.ofIdeal (isIdeal_smythIdealSet (smythCarrier_nonempty S)).toIdeal

@[simp] theorem mem_smythOf {S : SmythCarrier} {v : Smyth.Basis NatBot} :
    v ∈ smythOf S ↔ (⊥ : KNat) ∈ v.toFinset ∨ S.carrier ⊆ smythSet v := Iff.rfl

theorem smythOf_le_iff {S T : SmythCarrier} : smythOf S ≤ smythOf T ↔ S ≤ T := by
  constructor
  · intro h
    rcases S.mem' with hS | ⟨hfin, hne⟩
    · rw [smythCarrier_le_def, hS]
      exact Set.subset_univ _
    · have hgen : smythGen hfin hne ∈ smythOf S := by
        rw [mem_smythOf, smythSet_smythGen]
        exact Or.inr subset_rfl
      have := h hgen
      rw [mem_smythOf, smythSet_smythGen] at this
      exact this.resolve_left (bot_notMem_smythGen hfin hne)
  · intro h v hv
    rw [mem_smythOf] at hv ⊢
    exact hv.imp id fun hsub => (smythCarrier_le_def.mp h).trans hsub

theorem smythOf_injective : Function.Injective smythOf := fun _ _ h =>
  le_antisymm (smythOf_le_iff.mp h.le) (smythOf_le_iff.mp h.ge)

/-- **Every ideal of `(N⊥)♯` is one of the `smythOf S`.** With no `⊥`-free
member the ideal is the trivial one and `S = N`; otherwise the paper's sentence
applies — the ideal is principal at its `⊥`-free member of least cardinality, and
`S` is that member's `N`-part. Minimality is what replaces the paper's
"intersection of its non-trivial elements": the Smyth order on `⊥`-free points is
reverse inclusion, so a directed family of them has its intersection as a
member. -/
theorem smythOf_surjective : Function.Surjective smythOf := by
  classical
  intro x
  by_cases h : ∃ u : Smyth.Basis NatBot, u ∈ x ∧ (⊥ : KNat) ∉ u.toFinset
  · obtain ⟨u₀, hu₀x, hu₀b⟩ := h
    have hP : ∃ c, ∃ u : Smyth.Basis NatBot,
        u ∈ x ∧ (⊥ : KNat) ∉ u.toFinset ∧ u.toFinset.card = c :=
      ⟨u₀.toFinset.card, u₀, hu₀x, hu₀b, rfl⟩
    obtain ⟨u, hux, hub, huc⟩ := Nat.find_spec hP
    have hmin : ∀ w : Smyth.Basis NatBot, w ∈ x → (⊥ : KNat) ∉ w.toFinset →
        u.toFinset.card ≤ w.toFinset.card := by
      intro w hw hwb
      rw [huc]
      exact Nat.find_min' hP ⟨w, hw, hwb, rfl⟩
    have hne : (smythSet u).Nonempty := by
      obtain ⟨k, hk⟩ := u.nonempty'
      rcases compact_cases k with rfl | ⟨n, rfl⟩
      · exact absurd hk hub
      · exact ⟨n, hk⟩
    refine ⟨⟨smythSet u, Or.inr ⟨smythSet_finite u, hne⟩⟩, ?_⟩
    ext v
    rw [mem_smythOf]
    constructor
    · rintro (hbv | hsub)
      · exact x.lower (smyth_le_bot_iff.mpr hbv) (IdealCompletion.bot_mem x)
      · refine x.lower (?_ : v ≤ u) hux
        intro b hb
        rcases compact_cases b with rfl | ⟨n, rfl⟩
        · exact absurd hb hub
        · exact ⟨cpt (up n), hsub hb, le_rfl⟩
    · intro hv
      by_cases hbv : (⊥ : KNat) ∈ v.toFinset
      · exact Or.inl hbv
      refine Or.inr ?_
      obtain ⟨z, hz, huz, hvz⟩ := x.directed u hux v hv
      have hzb : ¬ SmythTrivial z := smyth_not_trivial_of_le huz hub
      have hzu : z.toFinset ⊆ u.toFinset := (smyth_le_iff_of_not_trivial hub).mp huz
      have hcard : u.toFinset.card ≤ z.toFinset.card := hmin z hz hzb
      have hzeq : z.toFinset = u.toFinset := Finset.eq_of_subset_of_card_le hzu hcard
      have hvu : u.toFinset ⊆ v.toFinset := by
        have := (smyth_le_iff_of_not_trivial hbv).mp hvz
        rwa [hzeq] at this
      exact fun n hn => hvu hn
  · have h' : ∀ v : Smyth.Basis NatBot, v ∈ x → (⊥ : KNat) ∈ v.toFinset := by
      intro v hv
      by_contra hc
      exact h ⟨v, hv, hc⟩
    refine ⟨⟨Set.univ, Or.inl rfl⟩, ?_⟩
    ext v
    rw [mem_smythOf]
    constructor
    · rintro (hbv | hsub)
      · exact x.lower (smyth_le_bot_iff.mpr hbv) (IdealCompletion.bot_mem x)
      · exact absurd hsub (not_univ_subset_smythSet v)
    · intro hv
      exact Or.inl (h' v hv)

/-- **`(N⊥)♯ ≅ {N} ∪ P*f(N)` under superset inclusion.** The paper's own
sentence, §5.2, printed p. 26. -/
def smythOrderIso : SmythCarrier ≃o Smyth.Powerdomain NatBot :=
  { Equiv.ofBijective smythOf ⟨smythOf_injective, smythOf_surjective⟩ with
    map_rel_iff' := smythOf_le_iff }

/-- **`(N⊥)♯` is isomorphic to the domain of sets `{N} ∪ P*f(N)` ordered by
superset inclusion.** Stated as an order isomorphism that carries every directed
supremum, as in `hoare_natBot_orderIso_powerset`. -/
theorem smyth_natBot_orderIso :
    ∃ e : SmythCarrier ≃o Smyth.Powerdomain NatBot,
      ∀ S : SmythCarrier, e S = smythOf S :=
  ⟨smythOrderIso, fun _ => rfl⟩

/-! ## `⊢♮` over `P*f(N⊥)`, and the printed statement of it

> Finally, let us look at the convex powerdomain of `N⊥`. If `u, v ∈ P*f(N⊥)`,
> then `u ⊢♮ v` iff
> 1. `⊥ ∈ v` and `u ⊇ v` or
> 2. `u = v`.  (§5.2, printed p. 26)

Clause 1 is **false as printed**; see the module docstring. `plotkin_le_iff` is
the corrected characterization and `plotkin_printed_clause_one_fails` is the
refutation of the printed one. Both are in Mathlib's orientation, where the
paper's `u ⊢♮ v` is `v ≤ u`. -/

/-- **The convex ordering over `N⊥`, corrected.** In the paper's notation:
`u ⊢♮ v` iff (1) `⊥ ∈ v` and `v ∖ {⊥} ⊆ u`, or (2) `u = v`.

The argument is that the flat order has nothing strictly above a non-`⊥` point.
Reading the Egli–Milner conjunction with that in hand: when `⊥ ∈ v` the Smyth
conjunct is free (every element of `u` sits above `⊥ ∈ v`) and the Hoare conjunct
says exactly that each non-`⊥` member of `v` is already a member of `u`; when
`⊥ ∉ v` both conjuncts become inclusions and the two sets coincide. -/
theorem plotkin_le_iff {u v : Plotkin.FinCompacts NatBot} :
    v ≤ u ↔ ((⊥ : KNat) ∈ v ∧ ∀ a ∈ v, a ≠ ⊥ → a ∈ u) ∨ u = v := by
  constructor
  · rintro ⟨hlow, hupp⟩
    by_cases hb : (⊥ : KNat) ∈ v
    · refine Or.inl ⟨hb, fun a ha hne => ?_⟩
      obtain ⟨b, hbu, hab⟩ := hlow a ha
      rcases compact_cases a with rfl | ⟨n, rfl⟩
      · exact absurd rfl hne
      · rw [eq_cpt_up_of_le hab] at hbu
        exact hbu
    · refine Or.inr (Plotkin.FinCompacts.ext fun a => ⟨fun hau => ?_, fun hav => ?_⟩)
      · obtain ⟨c, hcv, hca⟩ := hupp a hau
        rcases compact_cases c with rfl | ⟨n, rfl⟩
        · exact absurd hcv hb
        · rw [eq_cpt_up_of_le hca]
          exact hcv
      · obtain ⟨b, hbu, hab⟩ := hlow a hav
        rcases compact_cases a with rfl | ⟨n, rfl⟩
        · exact absurd hav hb
        · rw [eq_cpt_up_of_le hab] at hbu
          exact hbu
  · rintro (⟨hb, hsub⟩ | rfl)
    · refine ⟨fun a ha => ?_, fun b _ => ⟨⊥, hb, bot_le⟩⟩
      by_cases hab : a = ⊥
      · obtain ⟨c, hc⟩ := u.nonempty
        exact ⟨c, hc, by rw [hab]; exact bot_le⟩
      · exact ⟨a, hsub a ha hab, le_rfl⟩
    · exact le_rfl

/-! ### The paper's three finite sets, and the `{|·|}` of §5.3

`{|1|}`, `{|⊥|}` and `{|1, ⊥|}` are the principal ideals of the finite sets
`{1}`, `{⊥}` and `{1, ⊥}` of `K(N⊥)`. The paper writes `{|1, ⊥|}` for
`{|1|} ⊔ {|⊥|}`; since `1` and `⊥` are compact and `{1, ⊥}` is the greatest set
each of `{1}` and `{⊥}` generates under `⊔`, that element is the principal ideal
of `{1, ⊥}`, and it is under that name that the three identities are stated. -/

/-- `{1} ⊆ K(N⊥)`, as a point of the Hoare pre-order. -/
def pfOne : Hoare.Pf KNat := Hoare.Pf.ofFinset {kOne} (Finset.singleton_nonempty _)

/-- `{1, ⊥} ⊆ K(N⊥)`, as a point of the Hoare pre-order. -/
def pfOneBot : Hoare.Pf KNat := Hoare.Pf.ofFinset {kOne, ⊥} (Finset.insert_nonempty _ _)

/-- `{1}`, as a point of the Smyth pre-order. -/
def bOne : Smyth.Basis NatBot := ⟨{kOne}, Finset.singleton_nonempty _⟩

/-- `{1, ⊥}`, as a point of the Smyth pre-order. -/
def bOneBot : Smyth.Basis NatBot := ⟨{kOne, ⊥}, Finset.insert_nonempty _ _⟩

/-- `{1}`, as a point of the Plotkin pre-order. -/
def fcOne : Plotkin.FinCompacts NatBot := Plotkin.FinCompacts.single kOne

/-- `{⊥}`, as a point of the Plotkin pre-order — the least element. -/
def fcBot : Plotkin.FinCompacts NatBot := Plotkin.FinCompacts.single ⊥

/-- `{1, ⊥}`, as a point of the Plotkin pre-order. -/
def fcOneBot : Plotkin.FinCompacts NatBot := Plotkin.FinCompacts.pair kOne ⊥

/-- Principal ideals are ordered exactly as their generators. Stated for any
pre-order; `Plotkin.principal_le_principal` is the same fact at one carrier. -/
theorem principal_le_principal_iff {A : Type u} [Preorder A] {a b : A} :
    (IdealCompletion.principal a : IdealCompletion A) ≤ IdealCompletion.principal b ↔ a ≤ b :=
  IdealCompletion.principal_le_iff.trans IdealCompletion.mem_principal

theorem principal_eq_principal_iff {A : Type u} [Preorder A] {a b : A} :
    (IdealCompletion.principal a : IdealCompletion A) = IdealCompletion.principal b ↔
      a ≤ b ∧ b ≤ a :=
  ⟨fun h => ⟨principal_le_principal_iff.mp h.le, principal_le_principal_iff.mp h.ge⟩,
   fun h => le_antisymm (principal_le_principal_iff.mpr h.1)
     (principal_le_principal_iff.mpr h.2)⟩

/-! ### The three non-determinism identities (§5.3, printed p. 27)

> if program `P₁` can give output 1 or diverge on any of its inputs, then it will
> be identified with the program `Q` which diverges everywhere, since
> `{|1, ⊥|} = ⊥ = {|⊥|}` in `(N⊥)♯`. … if the lower powerdomain is used …
> `{|1, ⊥|} = {|1|}` in `(N⊥)♭`. However, `P₁` and `P₂` will not have the same
> meaning as the always divergent program `Q` since `{|1, ⊥|} ≠ ⊥` in the lower
> powerdomain. Finally, in the convex powerdomain, *none* of the programs
> `P₁, P₂, Q` have the same meaning since `{|1, ⊥|}`, `{|1|}` and `{|⊥|}` are all
> distinct in `(N⊥)♮`. -/

/-- **`{|1, ⊥|} = ⊥ = {|⊥|}` in `(N⊥)♯`.** The upper powerdomain identifies the
program that may diverge with the one that always does: `{1, ⊥}` sits below `{⊥}`
in the Smyth order because `⊥` covers `⊥`, and `{⊥}` is the least element. -/
theorem smyth_oneBot_eq_bot_eq_unit_bot :
    (IdealCompletion.principal bOneBot : Smyth.Powerdomain NatBot) = ⊥ ∧
      (IdealCompletion.principal (⊥ : Smyth.Basis NatBot) : Smyth.Powerdomain NatBot) = ⊥ := by
  refine ⟨?_, IdealCompletion.bot_eq_principal.symm⟩
  rw [IdealCompletion.bot_eq_principal]
  refine principal_eq_principal_iff.mpr ⟨?_, bot_le⟩
  intro b _
  exact ⟨⊥, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), bot_le⟩

/-- **`{|1, ⊥|} = {|1|}` in `(N⊥)♭`.** The lower powerdomain discards the
divergence: every element of `{1, ⊥}` is below `1`. -/
theorem hoare_oneBot_eq_one :
    (IdealCompletion.principal pfOneBot : Hoare.Powerdomain NatBot) =
      IdealCompletion.principal pfOne := by
  refine principal_eq_principal_iff.mpr ⟨?_, ?_⟩
  · intro x hx
    refine ⟨kOne, Finset.mem_singleton_self _, ?_⟩
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact le_rfl
    · rw [Finset.mem_singleton.mp hx]
      exact bot_le
  · intro x hx
    rw [Finset.mem_singleton.mp hx]
    exact ⟨kOne, Finset.mem_insert_self _ _, le_rfl⟩

/-- **`{|1, ⊥|} ≠ ⊥` in `(N⊥)♭`.** The lower powerdomain still separates the
program that may return `1` from the one that always diverges: `1` has nothing
above it in `{⊥}`. -/
theorem hoare_oneBot_ne_bot :
    (IdealCompletion.principal pfOneBot : Hoare.Powerdomain NatBot) ≠ ⊥ := by
  intro h
  rw [IdealCompletion.bot_eq_principal] at h
  obtain ⟨hle, -⟩ := principal_eq_principal_iff.mp h
  obtain ⟨y, hy, hxy⟩ := hle kOne (Finset.mem_insert_self _ _)
  exact not_kOne_le_bot ((Hoare.Pf.mem_bot.mp hy) ▸ hxy)

/-- **`{|1, ⊥|}`, `{|1|}` and `{|⊥|}` are pairwise distinct in `(N⊥)♮`.** Each
inequality fails for the same reason — the Smyth conjunct of Egli–Milner needs an
element of the left set below `⊥`, and `{1}` has none. -/
theorem plotkin_three_distinct :
    (Plotkin.principal fcOneBot : Plotkin.Powerdomain NatBot) ≠ Plotkin.principal fcOne ∧
      (Plotkin.principal fcOneBot : Plotkin.Powerdomain NatBot) ≠ Plotkin.principal fcBot ∧
        (Plotkin.principal fcOne : Plotkin.Powerdomain NatBot) ≠ Plotkin.principal fcBot := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    obtain ⟨-, h2⟩ := Plotkin.principal_eq_principal_iff.mp h
    obtain ⟨c, hc, hcb⟩ := h2.2 (⊥ : KNat) (Plotkin.FinCompacts.mem_pair.mpr (Or.inr rfl))
    rw [Plotkin.FinCompacts.mem_single.mp hc] at hcb
    exact not_kOne_le_bot hcb
  · intro h
    obtain ⟨h1, -⟩ := Plotkin.principal_eq_principal_iff.mp h
    obtain ⟨c, hc, hcb⟩ := h1.1 kOne (Plotkin.FinCompacts.mem_pair.mpr (Or.inl rfl))
    rw [Plotkin.FinCompacts.mem_single.mp hc] at hcb
    exact not_kOne_le_bot hcb
  · intro h
    obtain ⟨h1, -⟩ := Plotkin.principal_eq_principal_iff.mp h
    obtain ⟨c, hc, hcb⟩ := h1.1 kOne (Plotkin.FinCompacts.mem_single.mpr rfl)
    rw [Plotkin.FinCompacts.mem_single.mp hc] at hcb
    exact not_kOne_le_bot hcb

/-- **The printed clause 1 of the `⊢♮` characterization is refuted.** Take
`u = {1}` and `v = {1, ⊥}`. Then `u ⊢♮ v` holds, `⊥ ∈ v`, and yet `u ⊉ v` and
`u ≠ v` — so the printed disjunction fails on a pair the relation holds of. The
corrected clause, `v ∖ {⊥} ⊆ u`, holds here. -/
theorem plotkin_printed_clause_one_fails :
    ∃ u v : Plotkin.FinCompacts NatBot,
      v ≤ u ∧ ¬ (((⊥ : KNat) ∈ v ∧ ∀ a ∈ v, a ∈ u) ∨ u = v) := by
  refine ⟨fcOne, fcOneBot, plotkin_le_iff.mpr (Or.inl ⟨?_, ?_⟩), ?_⟩
  · exact Plotkin.FinCompacts.mem_pair.mpr (Or.inr rfl)
  · intro a ha hne
    rcases Plotkin.FinCompacts.mem_pair.mp ha with rfl | rfl
    · exact Plotkin.FinCompacts.mem_single.mpr rfl
    · exact absurd rfl hne
  · rintro (⟨-, hsub⟩ | heq)
    · have := hsub (⊥ : KNat) (Plotkin.FinCompacts.mem_pair.mpr (Or.inr rfl))
      exact kOne_ne_bot (Plotkin.FinCompacts.mem_single.mp this).symm
    · have : (⊥ : KNat) ∈ fcOne := by
        rw [heq]
        exact Plotkin.FinCompacts.mem_pair.mpr (Or.inr rfl)
      exact kOne_ne_bot (Plotkin.FinCompacts.mem_single.mp this).symm

/-! ## `(N⊥)♮`, described

> Hence, if `x` is an ideal and there is a set `u ∈ x` with `⊥ ∉ u`, then `x` is
> the principal ideal generated by `u`. No two distinct principal ideals like this
> will be comparable. On the other hand, if `x` is an ideal with `⊥ ∈ u` for each
> `u ∈ x`, then `x ⊆ y` for an arbitrary ideal `y` iff `⋃x ⊆ ⋃y`. Thus the convex
> powerdomain of `N⊥` corresponds to the set of finite, non-empty subsets of `N`
> unioned with the set of arbitrary subsets of `N⊥` that contain `⊥`. The ordering
> on these sets is like the pre-ordering `⊢♮` but extended to include infinite
> sets. (§5.2, printed p. 26)

`PlotkinCarrier` is that set of sets and `Ple` is that extended ordering — the
corrected `⊢♮` of `plotkin_le_iff`, read on arbitrary subsets of `N⊥` instead of
finite ones. `plotkinOrderIso` is the correspondence. -/

/-- The extended `⊢♮`, in Mathlib's orientation: `S ⊑ T` iff `⊥ ∈ S` and every
non-`⊥` member of `S` lies in `T`, or `S = T`. On finite sets this is exactly the
pre-order of `plotkin_le_iff`; the definition places no finiteness condition, so
it is the paper's "extended to include infinite sets". -/
def Ple (S T : Set (Flat ℕ)) : Prop :=
  ((⊥ : Flat ℕ) ∈ S ∧ ∀ a ∈ S, a ≠ ⊥ → a ∈ T) ∨ S = T

theorem Ple.refl (S : Set (Flat ℕ)) : Ple S S := Or.inr rfl

theorem Ple.trans {S T U : Set (Flat ℕ)} (h₁ : Ple S T) (h₂ : Ple T U) : Ple S U := by
  rcases h₁ with ⟨hb, hsub⟩ | rfl
  · rcases h₂ with ⟨-, hsub'⟩ | rfl
    · exact Or.inl ⟨hb, fun a ha hne => hsub' a (hsub a ha hne) hne⟩
    · exact Or.inl ⟨hb, hsub⟩
  · exact h₂

theorem Ple.antisymm {S T : Set (Flat ℕ)} (h₁ : Ple S T) (h₂ : Ple T S) : S = T := by
  rcases h₁ with ⟨hbS, hsub⟩ | h
  · rcases h₂ with ⟨hbT, hsub'⟩ | h
    · refine Set.Subset.antisymm (fun a ha => ?_) (fun a ha => ?_)
      · by_cases hne : a = ⊥
        · rw [hne]; exact hbT
        · exact hsub a ha hne
      · by_cases hne : a = ⊥
        · rw [hne]; exact hbS
        · exact hsub' a ha hne
    · exact h.symm
  · exact h

/-- With `⊥` present on the right, the equality branch collapses into the first:
`Ple` always holds by its left disjunct. -/
theorem Ple.left_of_bot_mem {S T : Set (Flat ℕ)} (h : Ple S T) (hb : (⊥ : Flat ℕ) ∈ T) :
    (⊥ : Flat ℕ) ∈ S ∧ ∀ a ∈ S, a ≠ ⊥ → a ∈ T := by
  rcases h with h | rfl
  · exact h
  · exact ⟨hb, fun a ha _ => ha⟩

/-- The same collapse with `⊥` present on the left instead. -/
theorem Ple.left_of_bot_mem_src {S T : Set (Flat ℕ)} (h : Ple S T) (hb : (⊥ : Flat ℕ) ∈ S) :
    (⊥ : Flat ℕ) ∈ S ∧ ∀ a ∈ S, a ≠ ⊥ → a ∈ T := by
  rcases h with h | rfl
  · exact h
  · exact ⟨hb, fun a ha _ => ha⟩

/-- A point of `P*f(K(N⊥))` read back as a subset of `N⊥`. -/
def pset (u : Plotkin.FinCompacts NatBot) : Set (Flat ℕ) := {a | cpt a ∈ u}

@[simp] theorem mem_pset {a : Flat ℕ} {u : Plotkin.FinCompacts NatBot} :
    a ∈ pset u ↔ cpt a ∈ u := Iff.rfl

theorem pset_injective :
    Function.Injective (pset : Plotkin.FinCompacts NatBot → Set (Flat ℕ)) := by
  intro u v h
  refine Plotkin.FinCompacts.ext fun k => ?_
  constructor
  · intro hk
    exact (h ▸ (hk : (k : Flat ℕ) ∈ pset u) : (k : Flat ℕ) ∈ pset v)
  · intro hk
    exact (h ▸ (hk : (k : Flat ℕ) ∈ pset v) : (k : Flat ℕ) ∈ pset u)

theorem pset_finite (u : Plotkin.FinCompacts NatBot) : (pset u).Finite := by
  have : pset u = (cpt : Flat ℕ → KNat) ⁻¹' u.carrier := rfl
  rw [this]
  exact Set.Finite.preimage (fun a _ b _ h => cpt_inj.mp h) u.finite

theorem pset_nonempty (u : Plotkin.FinCompacts NatBot) : (pset u).Nonempty := by
  obtain ⟨k, hk⟩ := u.nonempty
  exact ⟨(k : Flat ℕ), hk⟩

/-- `Ple` on the `pset`s **is** the convex pre-order — this is `plotkin_le_iff`
transported along the bijection `cpt`. -/
theorem Ple_pset_iff {u v : Plotkin.FinCompacts NatBot} : Ple (pset u) (pset v) ↔ u ≤ v := by
  rw [plotkin_le_iff]
  constructor
  · rintro (⟨hb, hsub⟩ | heq)
    · refine Or.inl ⟨hb, fun k hk hne => ?_⟩
      exact hsub (k : Flat ℕ) hk fun h => hne (Subtype.ext h)
    · exact Or.inr (pset_injective heq).symm
  · rintro (⟨hb, hsub⟩ | rfl)
    · refine Or.inl ⟨hb, fun a ha hne => ?_⟩
      exact hsub (cpt a) ha fun h => hne (congrArg Subtype.val h)
    · exact Or.inr rfl

/-- A finite non-empty subset of `N⊥` as a point of `P*f(K(N⊥))`. -/
def fcOfSet {S : Set (Flat ℕ)} (hf : S.Finite) (hne : S.Nonempty) :
    Plotkin.FinCompacts NatBot := ⟨cpt '' S, hf.image _, hne.image _⟩

@[simp] theorem pset_fcOfSet {S : Set (Flat ℕ)} (hf : S.Finite) (hne : S.Nonempty) :
    pset (fcOfSet hf hne) = S := by
  ext a
  simp only [mem_pset, fcOfSet]
  constructor
  · rintro ⟨b, hb, hab⟩
    exact (cpt_inj.mp hab) ▸ hb
  · intro ha
    exact ⟨a, ha, rfl⟩

/-- `{⊥, a}` as a point of `P*f(K(N⊥))` — the probe that recovers one member of
an infinite set. -/
def fcBotPair (a : Flat ℕ) : Plotkin.FinCompacts NatBot :=
  Plotkin.FinCompacts.pair ⊥ (cpt a)

@[simp] theorem pset_fcBotPair (a : Flat ℕ) : pset (fcBotPair a) = {⊥, a} := by
  ext b
  simp only [mem_pset, fcBotPair, Plotkin.FinCompacts.mem_pair, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (cpt_inj.mp h)
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- **The paper's carrier for `(N⊥)♮`:** the finite non-empty subsets of `N`
together with the arbitrary subsets of `N⊥` containing `⊥`. A `structure`, not a
subtype, for the reason `SmythCarrier` is one. -/
structure PlotkinCarrier where
  /-- The underlying subset of `N⊥`. -/
  carrier : Set (Flat ℕ)
  /-- Either `⊥` is present, or the set is a finite non-empty subset of `N`. -/
  mem' : (⊥ : Flat ℕ) ∈ carrier ∨ ((⊥ : Flat ℕ) ∉ carrier ∧ carrier.Finite ∧ carrier.Nonempty)

@[ext] theorem PlotkinCarrier.ext {S T : PlotkinCarrier} (h : S.carrier = T.carrier) : S = T := by
  cases S; cases T; cases h; rfl

instance : PartialOrder PlotkinCarrier where
  le S T := Ple S.carrier T.carrier
  le_refl S := Ple.refl _
  le_trans _ _ _ := Ple.trans
  le_antisymm _ _ h₁ h₂ := PlotkinCarrier.ext (Ple.antisymm h₁ h₂)

theorem plotkinCarrier_le_def {S T : PlotkinCarrier} : S ≤ T ↔ Ple S.carrier T.carrier := Iff.rfl

/-- The ideal attached to `S`: every finite non-empty `u ⊆ N⊥` with `u ⊑ S` in
the extended ordering. -/
def plotkinIdealSet (S : Set (Flat ℕ)) : Set (Plotkin.FinCompacts NatBot) :=
  {u | Ple (pset u) S}

theorem isIdeal_plotkinIdealSet (S : PlotkinCarrier) :
    Order.IsIdeal (plotkinIdealSet S.carrier) := by
  refine ⟨fun u v hvu hu => Ple.trans (Ple_pset_iff.mpr hvu) hu, ⟨⊥, ?_⟩, ?_⟩
  · refine Or.inl ⟨Plotkin.FinCompacts.mem_single.mpr rfl, fun a ha hne => ?_⟩
    exact absurd (congrArg Subtype.val (Plotkin.FinCompacts.mem_single.mp ha)) hne
  · intro u hu v hv
    by_cases hu' : (⊥ : Flat ℕ) ∈ pset u
    · by_cases hv' : (⊥ : Flat ℕ) ∈ pset v
      · obtain ⟨-, hsu⟩ := hu.left_of_bot_mem_src hu'
        obtain ⟨-, hsv⟩ := hv.left_of_bot_mem_src hv'
        refine ⟨⟨u.carrier ∪ v.carrier, u.finite.union v.finite, u.nonempty.inl⟩,
          Or.inl ⟨Or.inl hu', ?_⟩, ?_, ?_⟩
        · rintro a (ha | ha) hne
          · exact hsu a ha hne
          · exact hsv a ha hne
        · exact Ple_pset_iff.mp (Or.inl ⟨hu', fun a ha _ => Or.inl ha⟩)
        · exact Ple_pset_iff.mp (Or.inl ⟨hv', fun a ha _ => Or.inr ha⟩)
      · have heq : pset v = S.carrier := hv.resolve_left fun hh => hv' hh.1
        refine ⟨v, hv, Ple_pset_iff.mp ?_, le_rfl⟩
        rw [heq]
        exact hu
    · have heq : pset u = S.carrier := hu.resolve_left fun hh => hu' hh.1
      refine ⟨u, hu, le_rfl, Ple_pset_iff.mp ?_⟩
      rw [heq]
      exact hv

/-- The map `PlotkinCarrier → (N⊥)♮`. -/
def plotkinOf (S : PlotkinCarrier) : Plotkin.Powerdomain NatBot :=
  IdealCompletion.ofIdeal (isIdeal_plotkinIdealSet S).toIdeal

@[simp] theorem mem_plotkinOf {S : PlotkinCarrier} {u : Plotkin.FinCompacts NatBot} :
    u ∈ plotkinOf S ↔ Ple (pset u) S.carrier := Iff.rfl

theorem plotkinOf_le_iff {S T : PlotkinCarrier} : plotkinOf S ≤ plotkinOf T ↔ S ≤ T := by
  constructor
  · intro h
    rcases S.mem' with hb | ⟨hnb, hfin, hne⟩
    · refine Or.inl ⟨hb, fun a ha hne => ?_⟩
      have hmem : fcBotPair a ∈ plotkinOf S := by
        rw [mem_plotkinOf, pset_fcBotPair]
        refine Or.inl ⟨Set.mem_insert _ _, ?_⟩
        rintro b (rfl | rfl) hbne
        · exact absurd rfl hbne
        · exact ha
      have := h hmem
      rw [mem_plotkinOf, pset_fcBotPair] at this
      rcases this with ⟨-, hsub⟩ | heq
      · exact hsub a (Set.mem_insert_of_mem _ rfl) hne
      · rw [← heq]
        exact Set.mem_insert_of_mem _ rfl
    · have hmem : fcOfSet hfin hne ∈ plotkinOf S := by
        rw [mem_plotkinOf, pset_fcOfSet]
        exact Ple.refl _
      have := h hmem
      rwa [mem_plotkinOf, pset_fcOfSet] at this
  · intro h u hu
    exact Ple.trans hu h

theorem plotkinOf_injective : Function.Injective plotkinOf := fun _ _ h =>
  le_antisymm (plotkinOf_le_iff.mp h.le) (plotkinOf_le_iff.mp h.ge)

/-- **Every ideal of `(N⊥)♮` is one of the `plotkinOf S`.** With a `⊥`-free
member `u₀` the ideal is `↓u₀` — the paper's own sentence, and the proof is that
nothing is strictly above a `⊥`-free set in `⊢♮`. Without one, the ideal is
determined by `⋃x`, which is the paper's second sentence. -/
theorem plotkinOf_surjective : Function.Surjective plotkinOf := by
  classical
  intro x
  by_cases h : ∃ u : Plotkin.FinCompacts NatBot, u ∈ x ∧ (⊥ : KNat) ∉ u
  · obtain ⟨u₀, hu₀x, hu₀b⟩ := h
    refine ⟨⟨pset u₀, Or.inr ⟨hu₀b, pset_finite u₀, pset_nonempty u₀⟩⟩, ?_⟩
    ext t
    rw [mem_plotkinOf]
    constructor
    · intro ht
      exact x.lower (Ple_pset_iff.mp ht) hu₀x
    · intro ht
      obtain ⟨z, hz, hu₀z, htz⟩ := x.directed u₀ hu₀x t ht
      have hzu : z = u₀ := by
        rcases plotkin_le_iff.mp hu₀z with ⟨hb, -⟩ | heq
        · exact absurd hb hu₀b
        · exact heq
      rw [hzu] at htz
      exact Ple_pset_iff.mpr htz
  · have h' : ∀ u : Plotkin.FinCompacts NatBot, u ∈ x → (⊥ : KNat) ∈ u := by
      intro u hu
      by_contra hc
      exact h ⟨u, hu, hc⟩
    have hbot : (⊥ : Plotkin.FinCompacts NatBot) ∈ x := IdealCompletion.bot_mem x
    refine ⟨⟨{a : Flat ℕ | ∃ u ∈ x, cpt a ∈ u}, Or.inl ⟨⊥, hbot, h' ⊥ hbot⟩⟩, ?_⟩
    ext t
    rw [mem_plotkinOf]
    constructor
    · rintro ht
      obtain ⟨hbt, hsub⟩ := ht.left_of_bot_mem ⟨⊥, hbot, h' ⊥ hbot⟩
      -- collect a single member of `x` holding every non-`⊥` member of `t`
      have dom : ∀ s : Finset KNat, (∀ k ∈ s, k ≠ ⊥ → ∃ w ∈ x, k ∈ w) →
          ∃ w ∈ x, ∀ k ∈ s, k ≠ ⊥ → k ∈ w := by
        intro s
        induction s using Finset.induction_on with
        | empty => exact fun _ => ⟨⊥, hbot, by simp⟩
        | @insert a s _ ih =>
          intro hall
          obtain ⟨w, hw, hdom⟩ := ih fun k hk => hall k (Finset.mem_insert_of_mem hk)
          by_cases hane : a = ⊥
          · exact ⟨w, hw, fun k hk hkne => by
              rcases Finset.mem_insert.mp hk with rfl | hk
              · exact absurd hane hkne
              · exact hdom k hk hkne⟩
          obtain ⟨w', hw', haw'⟩ := hall a (Finset.mem_insert_self a s) hane
          obtain ⟨z, hz, hwz, hw'z⟩ := x.directed w hw w' hw'
          have keep : ∀ {p q : Plotkin.FinCompacts NatBot}, p ≤ q → ∀ k ∈ p, k ≠ ⊥ → k ∈ q := by
            intro p q hpq k hk hkne
            rcases plotkin_le_iff.mp hpq with ⟨-, hs⟩ | rfl
            · exact hs k hk hkne
            · exact hk
          refine ⟨z, hz, fun k hk hkne => ?_⟩
          rcases Finset.mem_insert.mp hk with rfl | hk
          · exact keep hw'z k haw' hkne
          · exact keep hwz k (hdom k hk hkne) hkne
      obtain ⟨w, hw, hdom⟩ := dom t.finite.toFinset (by
        intro k hk hkne
        exact hsub (k : Flat ℕ) (t.finite.mem_toFinset.mp hk)
          fun hh => hkne (Subtype.ext hh))
      refine x.lower (plotkin_le_iff.mpr (Or.inl ⟨hbt, fun k hk hkne => ?_⟩)) hw
      exact hdom k (t.finite.mem_toFinset.mpr hk) hkne
    · intro ht
      refine Or.inl ⟨h' t ht, fun a ha _ => ⟨t, ht, ha⟩⟩

/-- **`(N⊥)♮` corresponds to the finite non-empty subsets of `N` unioned with
the arbitrary subsets of `N⊥` containing `⊥`, under the extended `⊢♮`.** The
paper's own sentence, §5.2, printed p. 26. -/
def plotkinOrderIso : PlotkinCarrier ≃o Plotkin.Powerdomain NatBot :=
  { Equiv.ofBijective plotkinOf ⟨plotkinOf_injective, plotkinOf_surjective⟩ with
    map_rel_iff' := plotkinOf_le_iff }

theorem plotkin_natBot_orderIso :
    ∃ e : PlotkinCarrier ≃o Plotkin.Powerdomain NatBot, ∀ S, e S = plotkinOf S :=
  ⟨plotkinOrderIso, fun _ => rfl⟩

end

end ScottDomains.Flat
