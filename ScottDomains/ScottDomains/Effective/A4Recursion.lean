import ScottDomains.Effective.A2Compactness
import Mathlib.Data.List.GetD

/-!
# r0049, agent4: the recursion theory Theorem 7's two recursive claims need

r0047 measured what remains for `Effective.Theorem7ArrowRecursive` and
`Effective.Theorem7StrictRecursive` once the enumeration is guarded by
consistency (`R47.Agent2.scottHomC`, `R47.Agent2.strictHomC`), and it is
recursion theory: `Primrec` facts for the `Denumerable (Finset _)` coding, and a
search over finite normal subposets whose termination is a theorem rather than a
hope.

This file supplies both, and spends them on the fact §3.2 leaves implicit:

    ScottDomains.R49.Agent4.computablePred_bddAbove :
      IsRecursive d → ComputablePred fun n : ℕ =>
        BddAbove (d.enum '' ↑(Denumerable.ofNat (Finset ℕ) n))

**§3.2's two conditions decide boundedness.** `R47.Agent2.bddAbove_iff_exists_normal`
states the order-theoretic equivalence and its docstring asserts the
recursion-theoretic consequence — "'is this finite set of compacts bounded?' is
not an extra hypothesis on an effective presentation — it is a consequence of the
two the paper states" — without proving it. The proof is an unbounded search for
a finite normal subposet containing the given finite set, which terminates by
`R47.Agent2.isNormalIn_joinClosure`, followed by a finite test inside the
subposet found.
-/

namespace ScottDomains.R49.Agent4

open ScottDomains.Effective
open ScottDomains.Computable (RecursiveLE)

/-! ## 1. The `Denumerable (Finset α)` coding, primitively recursively

`Denumerable.finset` decodes `n` by `raise' (ofNat (List ℕ) n) 0` and then maps
along `ofNat α`. r0045 (`R45.Agent1.zero_mem_ofNat_finset_iff`) proved the single
membership test `0 ∈ ofNat (Finset ℕ) n` primitive recursive by reading the
decoded list's head. That argument does not generalize — every other element of
the decoded list is behind the accumulator of `raise'` — so this section decodes
the whole list instead, which is what quantification over the finite set needs
and what the `Finset (ℕ × ℕ)` coding needs. -/

/-- One step of the left fold that computes `Denumerable.raise'`: the state is
the prefix emitted so far together with the running offset. -/
def raiseStep (s : List ℕ × ℕ) (m : ℕ) : List ℕ × ℕ := (s.1 ++ [m + s.2], m + s.2 + 1)

/-- `Denumerable.raise'` is a left fold. Stated with an accumulator because the
fold's state carries one; the offset is threaded, which is exactly why `raise'`
is not a `List.map`. -/
theorem foldl_raiseStep :
    ∀ (l acc : List ℕ) (n : ℕ),
      (l.foldl raiseStep (acc, n)).1 = acc ++ Denumerable.raise' l n
  | [], acc, n => by simp [Denumerable.raise']
  | m :: l, acc, n => by
      have h := foldl_raiseStep l (acc ++ [m + n]) (m + n + 1)
      simpa [Denumerable.raise', raiseStep] using h

theorem raise'_eq_foldl (l : List ℕ) (n : ℕ) :
    Denumerable.raise' l n = (l.foldl raiseStep ([], n)).1 := by
  rw [foldl_raiseStep]
  simp

/-- **`Denumerable.raise'` is primitive recursive**, in both arguments. -/
theorem primrec₂_raise' : Primrec₂ Denumerable.raise' := by
  have hoff : Primrec fun x : (List ℕ × ℕ) × ((List ℕ × ℕ) × ℕ) => x.2.2 + x.2.1.2 :=
    Primrec₂.comp Primrec.nat_add (Primrec.snd.comp Primrec.snd)
      (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
  have hstep : Primrec₂ fun (_ : List ℕ × ℕ) (q : (List ℕ × ℕ) × ℕ) => raiseStep q.1 q.2 :=
    Primrec.to₂ (Primrec.pair
      (Primrec₂.comp Primrec.list_concat
        (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)) hoff)
      (Primrec.succ.comp hoff))
  have hfold : Primrec fun p : List ℕ × ℕ =>
      (p.1.foldl (fun s b => raiseStep s b) (([] : List ℕ), p.2)).1 :=
    Primrec.fst.comp
      (Primrec.list_foldl Primrec.fst
        (Primrec.pair (Primrec.const ([] : List ℕ)) Primrec.snd) hstep)
  exact hfold.of_eq fun p => (raise'_eq_foldl p.1 p.2).symm

/-- The decoded list of indices: the underlying list of `ofNat (Finset ℕ) n`. -/
def idxList (n : ℕ) : List ℕ := Denumerable.raise' (Denumerable.ofNat (List ℕ) n) 0

theorem primrec_idxList : Primrec idxList :=
  Primrec₂.comp primrec₂_raise' (Primrec.ofNat (List ℕ)) (Primrec.const 0)

/-- The `n`-th finite subset of `α`, as a list. -/
def decodeList (α : Type*) [Denumerable α] (n : ℕ) : List α :=
  (idxList n).map (Denumerable.ofNat α)

/-- **The decoding, as a membership test on the index list.** The
`Denumerable (Finset α)` instance maps `raise'Finset (ofNat (List ℕ) n) 0` along
`(eqv α).symm = ofNat α`, so an element belongs exactly when its code does. -/
theorem mem_idxList_iff {α : Type*} [Denumerable α] {x : α} {n : ℕ} :
    Encodable.encode x ∈ idxList n ↔ x ∈ Denumerable.ofNat (Finset α) n := by
  rw [show Denumerable.ofNat (Finset α) n =
      Finset.map (Denumerable.eqv α).symm.toEmbedding
        (Denumerable.raise'Finset (Denumerable.ofNat (List ℕ) n) 0) from
      Denumerable.ofNat_of_decode rfl, Finset.mem_map_equiv]
  simp [idxList, Denumerable.raise'Finset, Denumerable.eqv]

theorem mem_decodeList {α : Type*} [Denumerable α] {x : α} {n : ℕ} :
    x ∈ decodeList α n ↔ x ∈ Denumerable.ofNat (Finset α) n := by
  rw [decodeList, List.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact mem_idxList_iff.mp (by simpa using hy)
  · intro hx
    exact ⟨Encodable.encode x, mem_idxList_iff.mpr hx, by simp⟩

/-- **The `Finset α` coding is primitive recursive**, for every denumerable
`Primcodable α` — in particular for `α = ℕ` and for `α = ℕ × ℕ`, which is the
coding `Effective.scottHomEnum` and `R47.Agent2.consistentEnum` run over. -/
theorem primrec_decodeList_nat : Primrec (decodeList ℕ) :=
  Primrec.list_map primrec_idxList (Primrec.to₂ ((Primrec.ofNat ℕ).comp Primrec.snd))

/-- The same for the coding the step-function enumeration runs over. Stated at
`ℕ × ℕ` rather than for a general denumerable `α` because `[Denumerable α]` and
`[Primcodable α]` as separate binders build **two** `Encodable α` instances, and
the `Primrec.ofNat` application is then ill-typed; at each concrete carrier the
two agree. -/
theorem primrec_decodeList_pair : Primrec (decodeList (ℕ × ℕ)) :=
  Primrec.list_map primrec_idxList (Primrec.to₂ ((Primrec.ofNat (ℕ × ℕ)).comp Primrec.snd))

/-- At `α = ℕ` the decoding is the index list itself: `ofNat ℕ` is the identity. -/
theorem mem_ofNat_finset_nat_iff {x n : ℕ} :
    x ∈ Denumerable.ofNat (Finset ℕ) n ↔ x ∈ idxList n :=
  (mem_idxList_iff (α := ℕ) (x := x) (n := n)).symm.trans (by simp)

/-- Surjectivity of the decoding at `Finset ℕ`, the counterpart of
`Effective.surjective_ofNat_finset`. Stated rather than used inline for the same
reason that one is: `Finset ℕ` carries two `Encodable` instances and only the
`Denumerable` one satisfies `Denumerable.ofNat_encode`. -/
theorem surjective_ofNat_finset_nat : Function.Surjective (Denumerable.ofNat (Finset ℕ)) :=
  fun s => ⟨_, Denumerable.ofNat_encode s⟩

/-- **Membership in the decoded finite set is primitive recursive in both
arguments.** This is the general form of `R45.Agent1.primrecPred_zero_mem_ofNat_finset`,
which decided only `0 ∈ ·` and by an argument specific to `0`. -/
theorem primrecRel_mem_ofNat_finset :
    PrimrecRel fun (x n : ℕ) => x ∈ Denumerable.ofNat (Finset ℕ) n :=
  (PrimrecRel.comp₂ (PrimrecRel.exists_mem_list Primrec.eq)
      (Primrec.to₂ (primrec_idxList.comp Primrec.snd)) Primrec₂.left).of_eq
    fun x n => by
      rw [mem_ofNat_finset_nat_iff]
      exact ⟨fun ⟨a, ha, hax⟩ => hax ▸ ha, fun h => ⟨x, h, rfl⟩⟩

/-! ### The decoding runs, but not under the kernel

`R45.Agent1` closed the corresponding checks for `Flat ℕ` with `decide`, which is
what shows a decision procedure is a program rather than a `Classical.dec`. That
check is **unavailable for any `Denumerable` decoding in this Mathlib**, and the
obstruction is one declaration deep:

    example : Nat.sqrt 5 = 2 := by decide   -- fails: reduction stuck at `Nat.sqrt 5`

`Nat.unpair` calls `Nat.sqrt`, which is compiled by well-founded recursion and
does not reduce in the kernel, and every `Denumerable` decoding of a pair, a list
or a `Finset` goes through `Nat.unpair`. The compiled evaluator runs them —
`scripts/a4-decode-probe.lean` prints `idxList 5 = [0, 1, 2]` and
`decodeList (ℕ × ℕ) 5 = [(0, 0), (0, 1), (1, 0)]` — so this is a statement about
kernel reduction, not about computability. The `Primrec` facts above are the
kernel-checked content; the `#eval`s are evidence of a different kind and are
kept out of the module so the build stays free of `info` output. -/

/-! ## 2. Bounded quantification, at the `Computable` level

`Primrec.forall_mem_list` and `Primrec.exists_mem_list` are Mathlib's bounded
quantifiers, and they are the wrong strength here: the ordering test comes from
`Computable.RecursiveLE d`, a `ComputablePred` hypothesis, and Mathlib states no
`Computable` analogue of either. `Computable.nat_rec` supplies them — bounded
quantification is primitive recursion on the bound — and the two lemmas below are
the only place that recursion is written. -/

/-- Bounded universal quantification as a program: `allLt q b` tests `q` at every
`k < b`. -/
def allLt (q : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | (b + 1) => allLt q b && q b

theorem allLt_eq_true (q : ℕ → Bool) :
    ∀ b : ℕ, allLt q b = true ↔ ∀ k < b, q k = true
  | 0 => by simp [allLt]
  | (b + 1) => by
      rw [allLt, Bool.and_eq_true, allLt_eq_true q b]
      constructor
      · rintro ⟨h₁, h₂⟩ k hk
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
        · exact h₁ k hk
        · exact h₂
      · exact fun h => ⟨fun k hk => h k (by omega), h b (by omega)⟩

/-- The `Nat.rec` form `Computable.nat_rec` produces. -/
theorem allLt_eq_rec (q : ℕ → Bool) :
    ∀ b : ℕ, Nat.rec (motive := fun _ => Bool) true (fun y IH => IH && q y) b = allLt q b
  | 0 => rfl
  | (b + 1) => congrArg (fun x : Bool => x && q b) (allLt_eq_rec q b)

/-- **Bounded universal quantification preserves computability.** -/
theorem computable_allLt {α : Type*} [Primcodable α] {q : α → ℕ → Bool}
    (hq : Computable₂ q) : Computable fun p : α × ℕ => allLt (q p.1) p.2 :=
  (Computable.nat_rec Computable.snd (Computable.const true)
    (Computable.to₂ (Computable₂.comp (Primrec.and.to_comp)
      (Computable.snd.comp Computable.snd)
      (Computable₂.comp hq (Computable.fst.comp Computable.fst)
        (Computable.fst.comp Computable.snd))))).of_eq
    fun p => allLt_eq_rec (q p.1) p.2

/-! ### Two closure facts about `ComputablePred` that Mathlib does not state -/

/-- Precomposition with a computable function. -/
theorem computablePred_comp {α β : Type*} [Primcodable α] [Primcodable β] {p : β → Prop}
    {f : α → β} (hp : ComputablePred p) (hf : Computable f) :
    ComputablePred fun a => p (f a) := by
  obtain ⟨g, hg, rfl⟩ := ComputablePred.computable_iff.mp hp
  exact ComputablePred.computable_iff.mpr ⟨fun a => g (f a), hg.comp hf, rfl⟩

/-- Conjunction. -/
theorem computablePred_and {α : Type*} [Primcodable α] {p q : α → Prop}
    (hp : ComputablePred p) (hq : ComputablePred q) :
    ComputablePred fun a => p a ∧ q a := by
  obtain ⟨f, hf, rfl⟩ := ComputablePred.computable_iff.mp hp
  obtain ⟨g, hg, rfl⟩ := ComputablePred.computable_iff.mp hq
  refine ComputablePred.computable_iff.mpr
    ⟨fun a => f a && g a, Computable₂.comp Primrec.and.to_comp hf hg, ?_⟩
  funext a
  simp

/-! ### Quantification over the decoded finite set

The bound is the length of the decoded list and the element at each index is
read with `List.getI`, both primitive recursive; the quantified predicate is the
`ComputablePred` hypothesis. -/

theorem forall_mem_ofNat_finset_iff (n : ℕ) (R : ℕ → Prop) :
    (∀ x ∈ Denumerable.ofNat (Finset ℕ) n, R x) ↔
      ∀ k < (idxList n).length, R ((idxList n).getI k) := by
  constructor
  · intro h k hk
    refine h _ (mem_ofNat_finset_nat_iff.mpr ?_)
    rw [List.getI_eq_getElem _ hk]
    exact List.getElem_mem hk
  · intro h x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp (mem_ofNat_finset_nat_iff.mp hx)
    rw [← List.getI_eq_getElem _ hk]
    exact h k hk

theorem exists_mem_ofNat_finset_iff (n : ℕ) (R : ℕ → Prop) :
    (∃ x ∈ Denumerable.ofNat (Finset ℕ) n, R x) ↔
      ∃ k < (idxList n).length, R ((idxList n).getI k) := by
  constructor
  · rintro ⟨x, hx, hR⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp (mem_ofNat_finset_nat_iff.mp hx)
    exact ⟨k, hk, by rwa [← List.getI_eq_getElem _ hk] at hR⟩
  · rintro ⟨k, hk, hR⟩
    refine ⟨_, mem_ofNat_finset_nat_iff.mpr ?_, hR⟩
    rw [List.getI_eq_getElem _ hk]
    exact List.getElem_mem hk

/-- **`∀ x ∈ (the `code a`-th finite set), R a x` is computable when `R` is.** -/
theorem computablePred_forall_mem {α : Type*} [Primcodable α] {code : α → ℕ}
    (hcode : Computable code) {R : α → ℕ → Prop} [DecidableRel R]
    (hR : ComputablePred fun p : α × ℕ => R p.1 p.2) :
    ComputablePred fun a : α => ∀ x ∈ Denumerable.ofNat (Finset ℕ) (code a), R a x := by
  classical
  have hget : Computable fun p : α × ℕ => (idxList (code p.1)).getI p.2 :=
    Computable₂.comp (Primrec.list_getI.to_comp)
      ((primrec_idxList.to_comp).comp (hcode.comp Computable.fst)) Computable.snd
  have hq : Computable₂ fun (a : α) (k : ℕ) => decide (R a ((idxList (code a)).getI k)) :=
    Computable.to₂ (hR.decide.comp (Computable.pair Computable.fst hget))
  have hlen : Computable fun a : α => (idxList (code a)).length :=
    (Primrec.list_length.to_comp).comp ((primrec_idxList.to_comp).comp hcode)
  refine Computable.computablePred (p := fun a : α =>
    ∀ x ∈ Denumerable.ofNat (Finset ℕ) (code a), R a x) ?_
  refine ((computable_allLt hq).comp (Computable.pair Computable.id hlen)).of_eq fun a => ?_
  rw [Bool.eq_iff_iff, decide_eq_true_iff, allLt_eq_true]
  simpa using (forall_mem_ofNat_finset_iff (code a) (R a)).symm

/-- …and the existential form. -/
theorem computablePred_exists_mem {α : Type*} [Primcodable α] {code : α → ℕ}
    (hcode : Computable code) {R : α → ℕ → Prop} [DecidableRel R]
    (hR : ComputablePred fun p : α × ℕ => R p.1 p.2) :
    ComputablePred fun a : α => ∃ x ∈ Denumerable.ofNat (Finset ℕ) (code a), R a x := by
  classical
  have hnot : ComputablePred fun a : α =>
      ∀ x ∈ Denumerable.ofNat (Finset ℕ) (code a), ¬ R a x :=
    computablePred_forall_mem hcode
      (R := fun a x => ¬ R a x) (ComputablePred.not hR)
  refine (ComputablePred.not hnot).of_eq fun a => ?_
  simp

/-! ## 3. The search over finite normal subposets, and what it decides -/

section Search

variable {γ : Type*} [CompletePartialOrder γ] [Domain γ] [BoundedComplete γ]

/-- The finite set of basis elements named by the `n`-th finite set of indices.
`Effective.RecursiveNormal d` is exactly `ComputablePred fun n => basisSet d n ◁
compacts γ`, which `recursiveNormal_iff_basisSet` records. -/
def basisSet (d : EffectivePresentation γ) (n : ℕ) : Set γ :=
  d.enum '' (↑(Denumerable.ofNat (Finset ℕ) n) : Set ℕ)

omit [BoundedComplete γ] in
theorem recursiveNormal_iff_basisSet (d : EffectivePresentation γ) :
    RecursiveNormal d ↔ ComputablePred fun n : ℕ => basisSet d n ◁ compacts γ := Iff.rfl

omit [BoundedComplete γ] in
theorem finite_basisSet (d : EffectivePresentation γ) (n : ℕ) : (basisSet d n).Finite :=
  (Finset.finite_toSet _).image _

omit [BoundedComplete γ] in
theorem basisSet_subset_compacts (d : EffectivePresentation γ) (n : ℕ) :
    basisSet d n ⊆ compacts γ := by
  rintro _ ⟨i, _, rfl⟩
  exact d.enum_mem_compacts i

omit [BoundedComplete γ] in
theorem mem_basisSet {d : EffectivePresentation γ} {n i : ℕ}
    (hi : i ∈ Denumerable.ofNat (Finset ℕ) n) : d.enum i ∈ basisSet d n :=
  ⟨i, Finset.mem_coe.mpr hi, rfl⟩

omit [BoundedComplete γ] in
theorem basisSet_mono {d : EffectivePresentation γ} {n m : ℕ}
    (h : Denumerable.ofNat (Finset ℕ) n ⊆ Denumerable.ofNat (Finset ℕ) m) :
    basisSet d n ⊆ basisSet d m := by
  rintro _ ⟨i, hi, rfl⟩
  exact mem_basisSet (h (Finset.mem_coe.mp hi))

/-- The relation the search runs on: the `m`-th finite set of basis elements is
normal and its index set contains the `n`-th. -/
def NormAt (d : EffectivePresentation γ) (n m : ℕ) : Prop :=
  Denumerable.ofNat (Finset ℕ) n ⊆ Denumerable.ofNat (Finset ℕ) m ∧
    basisSet d m ◁ compacts γ

instance decidableNormAt (d : EffectivePresentation γ) (n m : ℕ) :
    Decidable (NormAt d n m) := by
  unfold NormAt basisSet
  exact @instDecidableAnd _ _ inferInstance (d.decidableNormal _)

/-- **The search terminates.** The witness is `R47.Agent2.joinClosure` of the
`n`-th finite set of basis elements: `R47.Agent2.isNormalIn_joinClosure` makes it
normal and `R47.Agent2.finite_joinClosure` finite, every member is compact so `d`
names it, and the index set is taken to contain the `n`-th so the superset
condition holds.

This is the totality proof the unbounded search below needs, and it is the
recursion-theoretic content of `R47.Agent2.bddAbove_iff_exists_normal`'s
docstring. -/
theorem exists_normal_superset (d : EffectivePresentation γ) (n : ℕ) :
    ∃ m : ℕ, NormAt d n m := by
  classical
  have hSfin : (basisSet d n).Finite := finite_basisSet d n
  have hScpt : basisSet d n ⊆ compacts γ := basisSet_subset_compacts d n
  have hJfin : (R47.Agent2.joinClosure (basisSet d n)).Finite :=
    R47.Agent2.finite_joinClosure hSfin
  have hJnorm : R47.Agent2.joinClosure (basisSet d n) ◁ compacts γ :=
    R47.Agent2.isNormalIn_joinClosure hSfin hScpt
  have hchoice : ∀ c ∈ R47.Agent2.joinClosure (basisSet d n), ∃ i : ℕ, d.enum i = c :=
    fun c hc => d.enum_surjective c (hJnorm.subset hc)
  choose! φ hφ using hchoice
  obtain ⟨m, hm⟩ := surjective_ofNat_finset_nat
    (Denumerable.ofNat (Finset ℕ) n ∪ hJfin.toFinset.image φ)
  have hbasis : basisSet d m = R47.Agent2.joinClosure (basisSet d n) := by
    rw [basisSet, hm]
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      rcases Finset.mem_union.mp (Finset.mem_coe.mp hi) with hi | hi
      · exact R47.Agent2.subset_joinClosure _ (mem_basisSet hi)
      · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hi
        have hc' : c ∈ R47.Agent2.joinClosure (basisSet d n) := by
          simpa using hc
        rw [hφ c hc']
        exact hc'
    · intro hx
      exact ⟨φ x, Finset.mem_coe.mpr (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨x, by simpa using hx, rfl⟩)), hφ x hx⟩
  exact ⟨m, by rw [hm]; exact Finset.subset_union_left, by rw [hbasis]; exact hJnorm⟩

/-- **Inside a normal superset, boundedness is a finite test on the two index
sets.** `R47.Agent2.bddAbove_iff_exists_mem_upperBounds` is where the compactness
of the join is spent; here it is read off the indices, which is the form §3.2's
condition 1 decides. -/
theorem bddAbove_basisSet_iff {d : EffectivePresentation γ} {n m : ℕ}
    (h : NormAt d n m) :
    BddAbove (basisSet d n) ↔
      ∃ i ∈ Denumerable.ofNat (Finset ℕ) m,
        ∀ j ∈ Denumerable.ofNat (Finset ℕ) n, d.enum j ≤ d.enum i := by
  rw [R47.Agent2.bddAbove_iff_exists_mem_upperBounds h.2 (basisSet_mono h.1)
    (finite_basisSet d n)]
  constructor
  · rintro ⟨b, ⟨i, hi, rfl⟩, hb⟩
    exact ⟨i, Finset.mem_coe.mp hi, fun j hj => hb (mem_basisSet hj)⟩
  · rintro ⟨i, hi, hle⟩
    refine ⟨d.enum i, mem_basisSet hi, ?_⟩
    rintro _ ⟨j, hj, rfl⟩
    exact hle j (Finset.mem_coe.mp hj)

/-- The least code of a finite normal subposet containing the `n`-th finite set
of basis elements. `noncomputable` because `d`'s own decision procedures are
data this development does not extract; `computable_normCode` is the statement
that matters. -/
noncomputable def normCode (d : EffectivePresentation γ) (n : ℕ) : ℕ :=
  Nat.find (exists_normal_superset d n)

omit [BoundedComplete γ] in
/-- `NormAt` is decided by the two conditions of §3.2: the subset test is
primitive recursive in the codes, and normality is `RecursiveNormal d`. -/
theorem computablePred_normAt {d : EffectivePresentation γ} (hd : IsRecursive d) :
    ComputablePred fun p : ℕ × ℕ => NormAt d p.1 p.2 := by
  classical
  have hsub : ComputablePred fun p : ℕ × ℕ =>
      Denumerable.ofNat (Finset ℕ) p.1 ⊆ Denumerable.ofNat (Finset ℕ) p.2 := by
    have hmem : ComputablePred fun q : (ℕ × ℕ) × ℕ =>
        q.2 ∈ Denumerable.ofNat (Finset ℕ) q.1.2 :=
      (PrimrecRel.comp primrecRel_mem_ofNat_finset Primrec.snd
        (Primrec.snd.comp Primrec.fst)).computablePred
    exact (computablePred_forall_mem (code := fun p : ℕ × ℕ => p.1) Computable.fst
      hmem).of_eq fun p => Finset.subset_iff.symm
  have hnorm : ComputablePred fun p : ℕ × ℕ => basisSet d p.2 ◁ compacts γ :=
    computablePred_comp hd.2 Computable.snd
  exact computablePred_and hsub hnorm

/-- **The search is computable**, by `Computable.find` — Mathlib's bridge from
`Partrec.rfind` to total unbounded search — with `exists_normal_superset` as the
totality proof. -/
theorem computable_normCode {d : EffectivePresentation γ} (hd : IsRecursive d) :
    Computable (normCode d) :=
  Computable.find (computablePred_normAt hd) (exists_normal_superset d)

/-- **§3.2's two conditions decide boundedness of a finite set of basis
elements.**

`R47.Agent2.bddAbove_iff_exists_normal` proves the order-theoretic equivalence
and its docstring asserts this consequence — "so 'is this finite set of compacts
bounded?' is not an extra hypothesis on an effective presentation — it is a
consequence of the two the paper states" — without proving it. The proof is the
unbounded search `normCode`, total by `exists_normal_superset`, followed by the
finite test `bddAbove_basisSet_iff` inside the subposet it finds. -/
theorem computablePred_bddAbove {d : EffectivePresentation γ} (hd : IsRecursive d) :
    ComputablePred fun n : ℕ => BddAbove (basisSet d n) := by
  classical
  have hle : ComputablePred fun r : ((ℕ × ℕ) × ℕ) × ℕ => d.enum r.2 ≤ d.enum r.1.2 :=
    computablePred_comp hd.1
      (Computable.pair Computable.snd (Computable.snd.comp Computable.fst))
  have hinner : ComputablePred fun q : (ℕ × ℕ) × ℕ =>
      ∀ j ∈ Denumerable.ofNat (Finset ℕ) q.1.1, d.enum j ≤ d.enum q.2 :=
    computablePred_forall_mem (code := fun q : (ℕ × ℕ) × ℕ => q.1.1)
      (Computable.fst.comp Computable.fst) hle
  have htest : ComputablePred fun p : ℕ × ℕ =>
      ∃ i ∈ Denumerable.ofNat (Finset ℕ) p.2,
        ∀ j ∈ Denumerable.ofNat (Finset ℕ) p.1, d.enum j ≤ d.enum i :=
    computablePred_exists_mem (code := fun p : ℕ × ℕ => p.2) Computable.snd hinner
  refine (computablePred_comp htest
    (Computable.pair Computable.id (computable_normCode hd))).of_eq fun n => ?_
  exact (bddAbove_basisSet_iff (Nat.find_spec (exists_normal_superset d n))).symm

/-! ## 4. The join of a bounded finite set of basis elements, as a computable index

`R47.Agent2.ofPairs_le_ofPairs_iff` reduces the ordering on the step-function
enumeration to `p.2 ≤ sSup (Prod.snd '' belowSet Q p.1)` — a join in `E` of a
finite set of basis elements. Testing that with `Computable.RecursiveLE e`
requires an *index* for the join, not the element, which is what this section
computes. -/

omit [Domain γ] [BoundedComplete γ] in
/-- **The least upper bound of a bounded finite subset of a normal set lies in
the set.** The join is compact (`R47.Agent2.isCompactElement_of_isLUB_finite`),
so normality applies at it and `R47.Agent2.exists_mem_ub_of_finite` produces a
member of the set above the whole subset and below the join — which is therefore
the join.

Stated nowhere in the development: `R47.Agent2.bddAbove_iff_exists_mem_upperBounds`
produces *some* bound in the normal set, this produces *the least* one. -/
theorem mem_of_isLUB_of_isNormalIn {u v : Set γ} (hu : u ◁ compacts γ) (hv : v ⊆ u)
    (hvfin : v.Finite) {c : γ} (hc : IsLUB v c) : c ∈ u := by
  have hcpt : IsCompactElement c :=
    R47.Agent2.isCompactElement_of_isLUB_finite hvfin (fun x hx => hu.subset (hv hx)) hc
  obtain ⟨z, hzmem, hz⟩ :=
    R47.Agent2.exists_mem_ub_of_finite (hu.nonempty hcpt) (hu.directedOn hcpt) hvfin
      (fun x hx => ⟨hv hx, Set.mem_Iic.mpr (hc.1 hx)⟩)
  have hcz : c ≤ z := hc.2 fun y hy => hz y hy
  exact le_antisymm (Set.mem_Iic.mp hzmem.2) hcz ▸ hzmem.1

/-- The predicate the join search runs on. The left disjunct makes the search
total on unbounded index sets, where there is no join to find; `joinIdx` is then
`0` and no theorem below claims anything about it. -/
def JoinIdxAt (d : EffectivePresentation γ) (n i : ℕ) : Prop :=
  ¬ BddAbove (basisSet d n) ∨
    (i ∈ Denumerable.ofNat (Finset ℕ) (normCode d n) ∧
      (∀ j ∈ Denumerable.ofNat (Finset ℕ) n, d.enum j ≤ d.enum i) ∧
      ∀ k ∈ Denumerable.ofNat (Finset ℕ) (normCode d n),
        (∀ j ∈ Denumerable.ofNat (Finset ℕ) n, d.enum j ≤ d.enum k) → d.enum i ≤ d.enum k)

theorem exists_joinIdxAt (d : EffectivePresentation γ) (n : ℕ) : ∃ i, JoinIdxAt d n i := by
  classical
  by_cases hb : BddAbove (basisSet d n)
  · have hnorm := Nat.find_spec (exists_normal_superset d n)
    have hc : IsLUB (basisSet d n) (sSup (basisSet d n)) := isLUB_sSup_of_bddAbove hb
    obtain ⟨i, hi, hie⟩ := mem_of_isLUB_of_isNormalIn hnorm.2
      (basisSet_mono (d := d) hnorm.1) (finite_basisSet d n) hc
    refine ⟨i, Or.inr ⟨Finset.mem_coe.mp hi, ?_, ?_⟩⟩
    · exact fun j hj => hie ▸ hc.1 (mem_basisSet hj)
    · intro k _ hk
      rw [hie]
      exact hc.2 (by rintro _ ⟨j, hj, rfl⟩; exact hk j (Finset.mem_coe.mp hj))
  · exact ⟨0, Or.inl hb⟩

/-- `JoinIdxAt` is `Decidable` classically; the content is
`computable_joinIdx`, which does not depend on the instance. -/
noncomputable instance decidableJoinIdxAt (d : EffectivePresentation γ) (n i : ℕ) :
    Decidable (JoinIdxAt d n i) := Classical.dec _

/-- The index of the join of the `n`-th finite set of basis elements. -/
noncomputable def joinIdx (d : EffectivePresentation γ) (n : ℕ) : ℕ :=
  Nat.find (exists_joinIdxAt d n)

/-- **The computed index names the join.** -/
theorem isLUB_enum_joinIdx {d : EffectivePresentation γ} {n : ℕ}
    (hb : BddAbove (basisSet d n)) : IsLUB (basisSet d n) (d.enum (joinIdx d n)) := by
  classical
  unfold joinIdx
  rcases Nat.find_spec (exists_joinIdxAt d n) with h | ⟨_, hub, hmin⟩
  · exact absurd hb h
  have hnorm := Nat.find_spec (exists_normal_superset d n)
  have hc : IsLUB (basisSet d n) (sSup (basisSet d n)) := isLUB_sSup_of_bddAbove hb
  obtain ⟨k, hk, hke⟩ := mem_of_isLUB_of_isNormalIn hnorm.2
    (basisSet_mono (d := d) hnorm.1) (finite_basisSet d n) hc
  have hkub : ∀ j ∈ Denumerable.ofNat (Finset ℕ) n, d.enum j ≤ d.enum k :=
    fun j hj => hke ▸ hc.1 (mem_basisSet hj)
  have h₁ : d.enum (Nat.find (exists_joinIdxAt d n)) ≤ sSup (basisSet d n) := by
    rw [← hke]
    exact hmin k (Finset.mem_coe.mp hk) hkub
  have h₂ : sSup (basisSet d n) ≤ d.enum (Nat.find (exists_joinIdxAt d n)) :=
    hc.2 (by rintro _ ⟨j, hj, rfl⟩; exact hub j (Finset.mem_coe.mp hj))
  have heq : d.enum (Nat.find (exists_joinIdxAt d n)) = sSup (basisSet d n) :=
    le_antisymm h₁ h₂
  rw [heq]
  exact hc

/-- Disjunction of computable predicates. -/
theorem computablePred_or {α : Type*} [Primcodable α] {p q : α → Prop}
    (hp : ComputablePred p) (hq : ComputablePred q) :
    ComputablePred fun a => p a ∨ q a := by
  obtain ⟨f, hf, rfl⟩ := ComputablePred.computable_iff.mp hp
  obtain ⟨g, hg, rfl⟩ := ComputablePred.computable_iff.mp hq
  refine ComputablePred.computable_iff.mpr
    ⟨fun a => f a || g a, Computable₂.comp Primrec.or.to_comp hf hg, ?_⟩
  funext a
  simp

/-- **The join index is computable**: another total unbounded search, whose
termination is `exists_joinIdxAt` and whose test is built from `IsRecursive d`
exactly as `computablePred_bddAbove`'s is. -/
theorem computable_joinIdx {d : EffectivePresentation γ} (hd : IsRecursive d) :
    Computable (joinIdx d) := by
  classical
  have hcode : Computable (normCode d) := computable_normCode hd
  -- `i` is above every member of the `n`-th set
  have hub : ComputablePred fun p : ℕ × ℕ =>
      ∀ j ∈ Denumerable.ofNat (Finset ℕ) p.1, d.enum j ≤ d.enum p.2 :=
    computablePred_forall_mem (code := fun p : ℕ × ℕ => p.1) Computable.fst
      (computablePred_comp hd.1
        (Computable.pair Computable.snd (Computable.snd.comp Computable.fst)))
  -- and below every member of the normal superset that is
  have hcond : ComputablePred fun r : (ℕ × ℕ) × ℕ =>
      (∀ j ∈ Denumerable.ofNat (Finset ℕ) r.1.1, d.enum j ≤ d.enum r.2) →
        d.enum r.1.2 ≤ d.enum r.2 := by
    have h₁ : ComputablePred fun r : (ℕ × ℕ) × ℕ =>
        ∀ j ∈ Denumerable.ofNat (Finset ℕ) r.1.1, d.enum j ≤ d.enum r.2 :=
      computablePred_forall_mem (code := fun r : (ℕ × ℕ) × ℕ => r.1.1)
        (Computable.fst.comp Computable.fst)
        (computablePred_comp hd.1
          (Computable.pair Computable.snd (Computable.snd.comp Computable.fst)))
    have h₂ : ComputablePred fun r : (ℕ × ℕ) × ℕ => d.enum r.1.2 ≤ d.enum r.2 :=
      computablePred_comp hd.1
        (Computable.pair (Computable.snd.comp Computable.fst) Computable.snd)
    exact (computablePred_or (ComputablePred.not h₁) h₂).of_eq fun r => by
      constructor
      · rintro (h | h)
        · exact fun hj => absurd hj h
        · exact fun _ => h
      · intro h
        by_cases hj : ∀ j ∈ Denumerable.ofNat (Finset ℕ) r.1.1, d.enum j ≤ d.enum r.2
        · exact Or.inr (h hj)
        · exact Or.inl hj
  have hmin : ComputablePred fun p : ℕ × ℕ =>
      ∀ k ∈ Denumerable.ofNat (Finset ℕ) (normCode d p.1),
        (∀ j ∈ Denumerable.ofNat (Finset ℕ) p.1, d.enum j ≤ d.enum k) →
          d.enum p.2 ≤ d.enum k :=
    computablePred_forall_mem (code := fun p : ℕ × ℕ => normCode d p.1)
      (hcode.comp Computable.fst) hcond
  have hmem : ComputablePred fun p : ℕ × ℕ =>
      p.2 ∈ Denumerable.ofNat (Finset ℕ) (normCode d p.1) :=
    computablePred_comp
      (PrimrecRel.comp primrecRel_mem_ofNat_finset Primrec.fst Primrec.snd).computablePred
      (Computable.pair Computable.snd (hcode.comp Computable.fst))
  have hunb : ComputablePred fun p : ℕ × ℕ => ¬ BddAbove (basisSet d p.1) :=
    ComputablePred.not (computablePred_comp (p := fun n : ℕ => BddAbove (basisSet d n))
      (computablePred_bddAbove hd) Computable.fst)
  have hall : ComputablePred fun p : ℕ × ℕ => JoinIdxAt d p.1 p.2 :=
    computablePred_or hunb
      (computablePred_and hmem (computablePred_and hub hmin))
  exact Computable.find hall (exists_joinIdxAt d)

end Search

/-! ## 5. The paper's own index needs no search

r0049's agent3 read Theorem 7's printed proof at folio 12 and found that Gunter &
Scott index the basis of `K(D → E)` by a pair `(N, s)` — `N` a finite normal
subposet of `K(D)`, `s : N → K(E)` monotone — and not by an arbitrary finite set
of index pairs. On that index the join `⨆{s y | y ∈ N ∩ ↓x}` always exists, so
there is nothing to guard.

This section measures what that costs the search above, and the answer is: on the
*order* test, everything. `N ∩ ↓x` is directed, its image under a monotone `s` is
directed, and a compact element is below a directed join exactly when it is below
a member. So `e_b ⊑ ⨆{…}` is a **finite** test over `N`, decided by
`RecursiveLE d` and `RecursiveLE e` with no unbounded search at all — this is
agent3's residue item 2, discharged.

What it does **not** touch is `RecursiveNormal` for the enumeration
(agent3's item 4): `R47.Agent2.isNormalIn_compacts_iff` asks whether two basis
elements of `D → E` are bounded and, if so, whether their join is in the set, and
those are the two questions §3 answers. So both routes are needed, and they are
needed at different places. -/

section StepOrder

variable {γ δ : Type*} [CompletePartialOrder γ] [Domain γ] [BoundedComplete γ]
  [CompletePartialOrder δ] [Domain δ]

omit [Domain γ] in
/-- **`N ∩ ↓x` is directed at every `x`, not only at compact `x`.** `IsNormalIn`
gives directedness only at members of `K(D)`; a pair below an arbitrary `x` is
bounded, so its join exists, is compact, and normality applies there.

An independent re-derivation of `R49.Agent3.directedOn_inter_Iic_of_isNormalIn`,
which is on agent3's branch and not in this worktree. agent3 reports it
axiom-free; this proof spends `[BoundedComplete γ]` to get the join of the pair,
which is the hypothesis `R47.Agent2.isNormalIn_compacts_iff` also spends. -/
theorem directedOn_inter_Iic {N : Set γ} (hN : N ◁ compacts γ) (x : γ) :
    DirectedOn (· ≤ ·) (N ∩ Set.Iic x) := by
  rintro a ⟨haN, hax⟩ b ⟨hbN, hbx⟩
  have hux : x ∈ upperBounds ({a, b} : Set γ) := by
    rintro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | rfl
    · exact Set.mem_Iic.mp hax
    · exact Set.mem_Iic.mp hbx
  have hlub := isLUB_sSup_of_bddAbove (⟨x, hux⟩ : BddAbove ({a, b} : Set γ))
  have hcpt : IsCompactElement (sSup ({a, b} : Set γ)) :=
    isCompactElement_of_isLUB_pair (hN.subset haN) (hN.subset hbN) hlub
  obtain ⟨w, ⟨hwN, hw⟩, haw, hbw⟩ :=
    hN.directedOn hcpt a ⟨haN, Set.mem_Iic.mpr (hlub.1 (Set.mem_insert _ _))⟩
      b ⟨hbN, Set.mem_Iic.mpr (hlub.1 (Set.mem_insert_of_mem _ rfl))⟩
  exact ⟨w, ⟨hwN, Set.mem_Iic.mpr ((Set.mem_Iic.mp hw).trans (hlub.2 hux))⟩, haw, hbw⟩

omit [Domain γ] [BoundedComplete γ] [Domain δ] in
/-- **Compactness, as a finite test against a directed join.** -/
theorem le_sSup_iff_exists_of_directedOn {b : δ} (hb : IsCompactElement b) {S : Set δ}
    (hne : S.Nonempty) (hd : DirectedOn (· ≤ ·) S) :
    b ≤ sSup S ↔ ∃ z ∈ S, b ≤ z := by
  refine ⟨fun h => hb S (sSup S) hne hd (DirectedOn.isLUB_sSup hd) h, ?_⟩
  rintro ⟨z, hz, hbz⟩
  exact hbz.trans ((DirectedOn.isLUB_sSup hd).1 hz)

/-- The values the paper's step function takes below `x`: `{s y | y ∈ N ∩ ↓x}`,
read off the indices. -/
def stepValues (d : EffectivePresentation γ) (e : EffectivePresentation δ) (n : ℕ)
    (t : ℕ → ℕ) (x : γ) : Set δ :=
  (fun j => e.enum (t j)) '' {j : ℕ | j ∈ Denumerable.ofNat (Finset ℕ) n ∧ d.enum j ≤ x}

/-- **The order test on the paper's index is finite.** With the index set normal
and `t` monotone on it, `e_b ⊑ ⨆{e_{t j} | j ∈ u, d_j ⊑ x}` holds exactly when
some single `j` witnesses it.

Every quantifier on the right ranges over the decoded finite set, and every atom
is a `≤` between basis elements — so `RecursiveLE d` and `RecursiveLE e` decide
it. No `Nat.rfind`, and no boundedness test. -/
theorem le_sSup_stepValues_iff {d : EffectivePresentation γ} {e : EffectivePresentation δ}
    {n : ℕ} {t : ℕ → ℕ} (hu : basisSet d n ◁ compacts γ)
    (hmono : ∀ i ∈ Denumerable.ofNat (Finset ℕ) n, ∀ j ∈ Denumerable.ofNat (Finset ℕ) n,
      d.enum i ≤ d.enum j → e.enum (t i) ≤ e.enum (t j))
    (x : γ) (b : ℕ) :
    e.enum b ≤ sSup (stepValues d e n t x) ↔
      ∃ j ∈ Denumerable.ofNat (Finset ℕ) n, d.enum j ≤ x ∧ e.enum b ≤ e.enum (t j) := by
  have hne : (stepValues d e n t x).Nonempty := by
    obtain ⟨j, hj, hjb⟩ := hu.bot_mem isCompactElement_bot
    exact ⟨e.enum (t j), ⟨j, ⟨Finset.mem_coe.mp hj, hjb ▸ bot_le⟩, rfl⟩⟩
  have hdir : DirectedOn (· ≤ ·) (stepValues d e n t x) := by
    rintro _ ⟨i, ⟨hiu, hix⟩, rfl⟩ _ ⟨j, ⟨hju, hjx⟩, rfl⟩
    obtain ⟨w, ⟨hwu, hwx⟩, hiw, hjw⟩ :=
      directedOn_inter_Iic hu x (d.enum i) ⟨mem_basisSet hiu, Set.mem_Iic.mpr hix⟩
        (d.enum j) ⟨mem_basisSet hju, Set.mem_Iic.mpr hjx⟩
    obtain ⟨k, hk, rfl⟩ := hwu
    refine ⟨e.enum (t k), ⟨k, ⟨Finset.mem_coe.mp hk, Set.mem_Iic.mp hwx⟩, rfl⟩, ?_, ?_⟩
    · exact hmono i hiu k (Finset.mem_coe.mp hk) hiw
    · exact hmono j hju k (Finset.mem_coe.mp hk) hjw
  rw [le_sSup_iff_exists_of_directedOn (e.enum_mem_compacts b) hne hdir]
  constructor
  · rintro ⟨_, ⟨j, ⟨hju, hjx⟩, rfl⟩, hb⟩
    exact ⟨j, hju, hjx, hb⟩
  · rintro ⟨j, hju, hjx, hb⟩
    exact ⟨e.enum (t j), ⟨j, ⟨hju, hjx⟩, rfl⟩, hb⟩

omit [BoundedComplete γ] in
/-- …and that finite test is computable from the two conditions of §3.2 alone.
The index triple is `((u-code, a), b)`: the index set, the argument's index, and
the value's index. -/
theorem computablePred_le_stepValues {d : EffectivePresentation γ}
    {e : EffectivePresentation δ} (hd : RecursiveLE d) (he : RecursiveLE e)
    {t : ℕ → ℕ} (ht : Computable t) :
    ComputablePred fun p : (ℕ × ℕ) × ℕ =>
      ∃ j ∈ Denumerable.ofNat (Finset ℕ) p.1.1,
        d.enum j ≤ d.enum p.1.2 ∧ e.enum p.2 ≤ e.enum (t j) := by
  classical
  refine computablePred_exists_mem (code := fun p : (ℕ × ℕ) × ℕ => p.1.1)
    (Computable.fst.comp (Computable.fst.comp Computable.id)) ?_
  refine computablePred_and ?_ ?_
  · exact computablePred_comp hd
      (Computable.pair Computable.snd (Computable.snd.comp (Computable.fst.comp Computable.fst)))
  · exact computablePred_comp he
      (Computable.pair (Computable.snd.comp Computable.fst) (ht.comp Computable.snd))

end StepOrder

end ScottDomains.R49.Agent4
