import ScottDomains.Effective.A3StepDecidable
-- r0049's `Denumerable (Finset _)` decoding facts (`R49.Agent4.idxList`,
-- `primrec_idxList`, `mem_idxList_iff`), reused rather than restated.
import ScottDomains.Effective.A4Recursion

/-!
# `StrictHomCRecursive` from `ScottHomCRecursive` (r0053, agent2)

r0052 recorded `R49.Agent3.StrictHomCRecursive` as a root hole **separate** from
`R49.Agent3.ScottHomCRecursive`, on this reason:

> the development's only route to countability of `K(D ⊸ E)`,
> `PRepFun.strictHomDomain`, is an injection into `K(D → E)` that names no
> enumeration, so no proved reduction carries recursiveness across it.

This file names the enumeration and carries the recursiveness across it, so the
two roots collapse to one. Nothing here is unconditional: the conclusion is
`IsRecursive (strictHomC d e)` **from** `IsRecursive (scottHomC d e)`, so the
`sorry` count does not fall — what falls is the number of independent open
statements, from three to two.
-/

namespace ScottDomains.R53.Agent2

open ScottDomains ScottDomains.Effective ScottDomains.R47.Agent2
open ScottDomains.Computable (RecursiveLE)

/-! ## 1. `List.flatMap` by a computable function is computable

Mathlib states `Primrec.list_map`, `Primrec.list_flatMap` and friends, but the
`Computable` namespace carries no list recursor at all: its list API is
`list_cons`, `list_reverse`, `list_getElem?`, `list_append`, `list_concat`,
`list_length`. Everything this file needs from a *computable* (not primitive
recursive) element map is derived here from `Computable.nat_rec`, by folding over
the indices `0, …, length - 1` with the pair (remaining list, output so far) as
the state. -/

section ListComputability

variable {ι : Type*} [Primcodable ι]

/-- `Option.casesOn` at `List ℕ`, named so that the computability proof can match
the shape `Computable.option_casesOn` asks for. -/
def optElim (g : ℕ → List ℕ) (o : Option ℕ) : List ℕ := Option.casesOn o [] g

theorem computable₂_optElim {g : ι → ℕ → List ℕ} (hg : Computable₂ g) :
    Computable₂ fun (a : ι) (o : Option ℕ) => optElim (g a) o :=
  Computable.option_casesOn Computable.snd (Computable.const [])
    (Computable₂.comp hg (Computable.fst.comp Computable.fst) Computable.snd)

/-- One step of the fold: drop the head of the remaining list and append `g` of
it to the output. -/
def flatStep (g : ℕ → List ℕ) (s : List ℕ × List ℕ) : List ℕ × List ℕ :=
  (s.1.tail, s.2 ++ optElim g s.1.head?)

/-- After `k` steps the remaining list is `l.drop k` and the output is the
`flatMap` of the first `k` entries. -/
theorem flatStep_iterate (g : ℕ → List ℕ) (l : List ℕ) : ∀ k : ℕ,
    (Nat.rec (motive := fun _ => List ℕ × List ℕ) (l, [])
      (fun _ IH => flatStep g IH) k) = (l.drop k, (l.take k).flatMap g)
  | 0 => by simp
  | (k + 1) => by
    rw [show (Nat.rec (motive := fun _ => List ℕ × List ℕ) (l, [])
        (fun _ IH => flatStep g IH) (k + 1))
      = flatStep g (Nat.rec (motive := fun _ => List ℕ × List ℕ) (l, [])
        (fun _ IH => flatStep g IH) k) from rfl, flatStep_iterate g l k]
    have hhead : (l.drop k).head? = l[k]? := List.head?_drop
    have htake : (l.take (k + 1)).flatMap g = (l.take k).flatMap g ++ optElim g l[k]? := by
      rw [List.take_add_one, List.flatMap_append]
      congr 1
      cases l[k]? with
      | none => simp [optElim]
      | some b => simp [optElim]
    refine Prod.ext ?_ ?_
    · exact List.tail_drop
    · simpa [flatStep, hhead] using htake.symm

/-- **`fun l => l.flatMap (g a)` is computable in `(a, l)` when `g` is.** The
engine every element-wise list operation below runs on. -/
theorem computable_flatMap {g : ι → ℕ → List ℕ} (hg : Computable₂ g) :
    Computable fun p : ι × List ℕ => p.2.flatMap (g p.1) := by
  have hg' : Computable₂ fun (p : ι × List ℕ) (b : ℕ) => g p.1 b :=
    Computable₂.comp hg (Computable.fst.comp Computable.fst) Computable.snd
  have hstep : Computable₂ fun (p : ι × List ℕ) (z : ℕ × (List ℕ × List ℕ)) =>
      flatStep (g p.1) z.2 := by
    refine Computable.pair ?_ ?_
    · exact (Primrec.list_tail.to_comp).comp (Computable.fst.comp (Computable.snd.comp
        Computable.snd))
    · refine Computable.list_append.comp
        (Computable.snd.comp (Computable.snd.comp Computable.snd)) ?_
      exact Computable₂.comp
        (f := fun (p : ι × List ℕ) (o : Option ℕ) => optElim (g p.1) o)
        (computable₂_optElim hg') Computable.fst
        ((Primrec.list_head?.to_comp).comp
          (Computable.fst.comp (Computable.snd.comp Computable.snd)))
  have hrec := Computable.nat_rec (σ := List ℕ × List ℕ)
    (f := fun p : ι × List ℕ => p.2.length)
    (g := fun p : ι × List ℕ => (p.2, ([] : List ℕ)))
    (h := fun (p : ι × List ℕ) (z : ℕ × (List ℕ × List ℕ)) => flatStep (g p.1) z.2)
    (Computable.list_length.comp Computable.snd)
    (Computable.pair Computable.snd (Computable.const []))
    hstep
  refine (Computable.snd.comp hrec).of_eq fun p => ?_
  rw [flatStep_iterate]
  simp

theorem list_filter_eq_flatMap (q : ℕ → Bool) (l : List ℕ) :
    l.filter q = l.flatMap fun b => bif q b then [b] else [] := by
  induction l with
  | nil => rfl
  | cons a t ih => by_cases h : q a <;> simp [h, ih]

theorem list_map_eq_flatMap (f : ℕ → ℕ) (l : List ℕ) :
    l.map f = l.flatMap fun b => [f b] := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

/-- **Filtering a list of naturals by a computable test is computable.** -/
theorem computable_list_filter {q : ι → ℕ → Bool} (hq : Computable₂ q) :
    Computable fun p : ι × List ℕ => p.2.filter (q p.1) := by
  have hg : Computable₂ fun (a : ι) (b : ℕ) => bif q a b then [b] else ([] : List ℕ) :=
    Computable.cond hq
      (Computable.list_cons.comp Computable.snd (Computable.const ([] : List ℕ)))
      (Computable.const ([] : List ℕ))
  exact (computable_flatMap hg).of_eq fun p => (list_filter_eq_flatMap _ _).symm

/-- **Mapping a list of naturals by a computable function is computable.** -/
theorem computable_list_map {f : ι → ℕ → ℕ} (hf : Computable₂ f) :
    Computable fun p : ι × List ℕ => p.2.map (f p.1) := by
  have hg : Computable₂ fun (a : ι) (b : ℕ) => [f a b] :=
    Computable.list_cons.comp hf (Computable.const ([] : List ℕ))
  exact (computable_flatMap hg).of_eq fun p => (list_map_eq_flatMap _ _).symm

end ListComputability

/-! ## 2. `Denumerable.lower'`, the encoding half of the `Finset` coding

`Denumerable.finset` decodes `n` by reading it as a `List ℕ` of gaps and turning
those gaps into a strictly increasing list of element codes with
`Denumerable.raise'`; it encodes by the inverse, `Denumerable.lower'`.

r0049's `Effective/A4Recursion.lean` proved the **decoding** half primitive
recursive — `R49.Agent4.primrec₂_raise'`, `R49.Agent4.idxList`,
`R49.Agent4.mem_idxList_iff` — and this file reuses those rather than restating
them. The **encoding** half is what is missing there, and it is what a code
*map* needs: to name a finite set one has to produce its code, not only read it.
`lower'` is a left fold with a two-component state, the mirror image of
`R49.Agent4.raiseStep`. -/

section Coding

/-- The state transition computing `Denumerable.lower'` as a left fold. -/
def lowerStep (s : ℕ × List ℕ) (m : ℕ) : ℕ × List ℕ := (m + 1, s.2 ++ [m - s.1])

theorem foldl_lowerStep : ∀ (l : List ℕ) (n : ℕ) (acc : List ℕ),
    (l.foldl lowerStep (n, acc)).2 = acc ++ Denumerable.lower' l n
  | [], n, acc => by simp [Denumerable.lower']
  | (m :: l), n, acc => by
    rw [List.foldl_cons]
    show (l.foldl lowerStep (m + 1, acc ++ [m - n])).2 = _
    rw [foldl_lowerStep l (m + 1) (acc ++ [m - n]), Denumerable.lower']
    simp

theorem primrec_lower' : Primrec fun l : List ℕ => Denumerable.lower' l 0 := by
  have hstep : Primrec₂ fun (_ : List ℕ) (z : (ℕ × List ℕ) × ℕ) => lowerStep z.1 z.2 := by
    refine Primrec.pair (Primrec.succ.comp (Primrec.snd.comp Primrec.snd)) ?_
    exact Primrec.list_concat.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.nat_sub.comp (Primrec.snd.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
  refine (Primrec.snd.comp (Primrec.list_foldl Primrec.id
    (Primrec.const ((0 : ℕ), ([] : List ℕ))) hstep)).of_eq fun l => ?_
  simpa using foldl_lowerStep l 0 []

/-- The one code-level fact every code map below is built from: the raised list of
the code `Encodable.encode (lower' l 0)` is `l` itself, whenever `l` is strictly
increasing. -/
theorem raise'_ofNat_encode_lower' {l : List ℕ} (hl : l.SortedLT) :
    Denumerable.raise' (Denumerable.ofNat (List ℕ)
      (Encodable.encode (Denumerable.lower' l 0))) 0 = l := by
  rw [Denumerable.ofNat_encode]
  exact Denumerable.raise_lower' (fun m _ => Nat.zero_le m) hl

end Coding

/-! ## 3. Two code maps: filtering, and taking an image -/

section CodeMaps

theorem sortedLT_idxList (n : ℕ) : (R49.Agent4.idxList n).SortedLT :=
  Denumerable.raise'_sorted _ _

/-- **The code of the subset cut out by a decidable test on element codes.** -/
def filterCode (q : ℕ → Bool) (n : ℕ) : ℕ :=
  Encodable.encode (Denumerable.lower' ((R49.Agent4.idxList n).filter q) 0)

theorem idxList_filterCode (q : ℕ → Bool) (n : ℕ) :
    R49.Agent4.idxList (filterCode q n) = (R49.Agent4.idxList n).filter q :=
  raise'_ofNat_encode_lower'
    (List.Pairwise.sortedLT (((sortedLT_idxList n).pairwise).filter q))

/-- **`filterCode` computes `Finset.filter` in the codes.** -/
theorem ofNat_finset_filterCode {α : Type*} [Denumerable α] (q : ℕ → Bool) (n : ℕ) :
    Denumerable.ofNat (Finset α) (filterCode q n) =
      (Denumerable.ofNat (Finset α) n).filter fun a => q (Encodable.encode a) = true := by
  ext a
  rw [Finset.mem_filter, ← R49.Agent4.mem_idxList_iff, ← R49.Agent4.mem_idxList_iff,
    idxList_filterCode, List.mem_filter]

theorem computable_filterCode {ι : Type*} [Primcodable ι] {q : ι → ℕ → Bool}
    (hq : Computable₂ q) : Computable fun p : ι × ℕ => filterCode (q p.1) p.2 := by
  have hfil : Computable fun p : ι × ℕ => (R49.Agent4.idxList p.2).filter (q p.1) :=
    (computable_list_filter hq).comp
      (Computable.pair Computable.fst (R49.Agent4.primrec_idxList.to_comp.comp Computable.snd))
  exact Computable.encode.comp (primrec_lower'.to_comp.comp hfil)

/-! ### The image code

`Finset.image` does not preserve the sorted order the coding stores, so it cannot
be computed by rewriting the decoded list in place. It is computed instead by
*re-scanning*: the image is a finite set of naturals bounded by the sum of the
mapped list, so filtering `List.range (bound + 1)` by membership in the mapped
list produces the sorted, duplicate-free list the coding wants. -/

/-- A crude bound: every entry of a list of naturals is at most the list's sum. -/
def natSum (l : List ℕ) : ℕ := l.foldr (· + ·) 0

theorem le_natSum : ∀ (l : List ℕ) {x : ℕ}, x ∈ l → x ≤ natSum l
  | (a :: t), x, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_add_right _ _
    · exact (le_natSum t h).trans (Nat.le_add_left _ _)

theorem primrec_natSum : Primrec natSum :=
  Primrec.list_foldr Primrec.id (Primrec.const 0)
    (Primrec.to₂ (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)))

/-- Membership in a list of naturals as an arithmetic test on the index of first
occurrence — the form `Primrec.list_idxOf` decides. -/
def memTest (l : List ℕ) (k : ℕ) : Bool := decide (l.idxOf k < l.length)

theorem memTest_iff (l : List ℕ) (k : ℕ) : memTest l k = true ↔ k ∈ l := by
  rw [memTest, decide_eq_true_iff]
  exact List.idxOf_lt_length_iff

/-- The sorted, duplicate-free list of the image of `l` under `f`. -/
def imageList (f : ℕ → ℕ) (l : List ℕ) : List ℕ :=
  (List.range (natSum (l.map f) + 1)).filter fun k => memTest (l.map f) k

theorem mem_imageList (f : ℕ → ℕ) (l : List ℕ) (k : ℕ) :
    k ∈ imageList f l ↔ k ∈ l.map f := by
  rw [imageList, List.mem_filter]
  constructor
  · rintro ⟨_, h⟩
    exact (memTest_iff _ _).mp h
  · intro h
    exact ⟨List.mem_range.mpr (Nat.lt_succ_of_le (le_natSum _ h)), (memTest_iff _ _).mpr h⟩

theorem sortedLT_imageList (f : ℕ → ℕ) (l : List ℕ) : (imageList f l).SortedLT :=
  List.Pairwise.sortedLT (((List.sortedLT_range _).pairwise).filter _)

/-- **The code of the image of a finite set of naturals under a map on codes.** -/
def imageCode (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  Encodable.encode (Denumerable.lower' (imageList f (R49.Agent4.idxList n)) 0)

theorem idxList_imageCode (f : ℕ → ℕ) (n : ℕ) :
    R49.Agent4.idxList (imageCode f n) = imageList f (R49.Agent4.idxList n) :=
  raise'_ofNat_encode_lower' (sortedLT_imageList f (R49.Agent4.idxList n))

/-- **`imageCode` computes `Finset.image` in the codes.** -/
theorem ofNat_finset_imageCode (f : ℕ → ℕ) (n : ℕ) :
    Denumerable.ofNat (Finset ℕ) (imageCode f n) =
      (Denumerable.ofNat (Finset ℕ) n).image f := by
  ext a
  rw [Finset.mem_image, R49.Agent4.mem_ofNat_finset_nat_iff, idxList_imageCode,
    mem_imageList, List.mem_map]
  constructor
  · rintro ⟨b, hb, hba⟩
    exact ⟨b, R49.Agent4.mem_ofNat_finset_nat_iff.mpr hb, hba⟩
  · rintro ⟨b, hb, hba⟩
    exact ⟨b, R49.Agent4.mem_ofNat_finset_nat_iff.mp hb, hba⟩

set_option maxHeartbeats 1000000 in
theorem computable_imageCode {f : ℕ → ℕ} (hf : Computable f) :
    Computable fun n : ℕ => imageCode f n := by
  have hmap : Computable fun n : ℕ => (R49.Agent4.idxList n).map f :=
    (computable_list_map (ι := ℕ) (f := fun _ => f)
      (hf.comp Computable.snd)).comp
      (Computable.pair Computable.id R49.Agent4.primrec_idxList.to_comp)
  have hbound : Computable fun n : ℕ =>
      List.range (natSum ((R49.Agent4.idxList n).map f) + 1) :=
    Primrec.list_range.to_comp.comp
      (Computable.succ.comp (primrec_natSum.to_comp.comp hmap))
  have hidx : Computable fun z : ℕ × ℕ => ((R49.Agent4.idxList z.1).map f).idxOf z.2 :=
    Computable₂.comp (f := fun (k : ℕ) (l : List ℕ) => l.idxOf k)
      (Primrec₂.to_comp Primrec.list_idxOf) Computable.snd (hmap.comp Computable.fst)
  have hlen : Computable fun z : ℕ × ℕ => ((R49.Agent4.idxList z.1).map f).length :=
    Computable.list_length.comp (hmap.comp Computable.fst)
  have hltPrim : Primrec₂ fun a b : ℕ => decide (a < b) := Primrec.nat_lt.decide
  have hcontains : Computable₂ fun (n : ℕ) (k : ℕ) =>
      memTest ((R49.Agent4.idxList n).map f) k :=
    Computable₂.comp (f := fun (a b : ℕ) => decide (a < b))
      (Primrec₂.to_comp hltPrim) hidx hlen
  have hfil : Computable fun n : ℕ =>
      (List.range (natSum ((R49.Agent4.idxList n).map f) + 1)).filter
        (fun k => memTest ((R49.Agent4.idxList n).map f) k) :=
    (computable_list_filter hcontains).comp (Computable.pair Computable.id hbound)
  exact Computable.encode.comp (primrec_lower'.to_comp.comp hfil)

/-- The unparametrized filter code map, for a single computable test. -/
theorem computable_filterCode' {q : ℕ → Bool} (hq : Computable q) :
    Computable (filterCode q) :=
  (computable_filterCode (ι := ℕ) (q := fun _ => q) (hq.comp Computable.snd)).comp
    (Computable.pair Computable.id Computable.id)

end CodeMaps

/-! ## 4. `⊥` is recognizable from condition 1 alone

`RecursiveLE d` decides `dₘ ⊑ dₙ`. Since `⊥` is compact it has *some* index `i₀`,
and `dᵢ = ⊥` is `dᵢ ⊑ d_{i₀}`, so bottom-ness is decided by the same procedure at
a fixed second argument. No search and no extra hypothesis. -/

theorem computablePred_enum_eq_bot {γ : Type*} [CompletePartialOrder γ] [Domain γ]
    (d : EffectivePresentation γ) (hd : RecursiveLE d) :
    ComputablePred fun i : ℕ => d.enum i = ⊥ := by
  obtain ⟨i₀, hi₀⟩ := d.enum_surjective (⊥ : γ) isCompactElement_bot
  obtain ⟨f, hf, hfE⟩ := ComputablePred.computable_iff.mp hd
  refine ComputablePred.computable_iff.mpr
    ⟨fun i => f (i, i₀), hf.comp (Computable.pair Computable.id (Computable.const i₀)), ?_⟩
  funext i
  rw [← congrFun hfE (i, i₀)]
  show (d.enum i = ⊥) = (d.enum i ≤ d.enum i₀)
  rw [hi₀]
  exact propext le_bot_iff.symm

/-! ## 5. The injection `K(D ⊸ E) ↪ K(D → E)`, in the codes

`R46.Agent3.strictPairsOf d e Q` is `Effective.pairsOf d e Q` cut down by a
condition on the *pair of indices* — `isStrict_iff_of_isStepPair` is what makes it
one — so it is `pairsOf d e` of a **sub-finset** of `Q`, and `filterCode` computes
that sub-finset in the codes. `strictCode d e` is therefore the index map
carrying an index of `strictConsistentEnum d e` to an index of
`consistentEnum d e` naming the same function of `D → E`. -/

section Injection

variable {α β : Type*} [CompletePartialOrder α] [Domain α]
  [CompletePartialOrder β] [Domain β] [BoundedComplete β]

open Classical in
/-- The strictness condition on an index pair, as a `Bool`-valued test on the
`ℕ`-code of the pair. Defined classically; `computable_strictTest` is the theorem
that it is decided by a total recursive function, and it is proved from
`RecursiveLE d` and `RecursiveLE e` rather than assumed. -/
noncomputable def strictTest (d : EffectivePresentation α) (e : EffectivePresentation β)
    (k : ℕ) : Bool :=
  decide (d.enum (Denumerable.ofNat (ℕ × ℕ) k).1 = ⊥ →
    e.enum (Denumerable.ofNat (ℕ × ℕ) k).2 = ⊥)

omit [BoundedComplete β] in
theorem strictTest_encode (d : EffectivePresentation α) (e : EffectivePresentation β)
    (a : ℕ × ℕ) :
    strictTest d e (Encodable.encode a) = true ↔ (d.enum a.1 = ⊥ → e.enum a.2 = ⊥) := by
  classical
  rw [strictTest, decide_eq_true_iff, Denumerable.ofNat_encode]

omit [BoundedComplete β] in
/-- **The test is decided by a total recursive function.** -/
theorem computable_strictTest (d : EffectivePresentation α) (e : EffectivePresentation β)
    (hd : RecursiveLE d) (he : RecursiveLE e) : Computable (strictTest d e) := by
  classical
  obtain ⟨bd, hbd, hbdE⟩ := ComputablePred.computable_iff.mp (computablePred_enum_eq_bot d hd)
  obtain ⟨be, hbe, hbeE⟩ := ComputablePred.computable_iff.mp (computablePred_enum_eq_bot e he)
  have hofNat : Computable (Denumerable.ofNat (ℕ × ℕ)) := Computable.ofNat _
  have hcomp : Computable fun k : ℕ =>
      bif bd (Denumerable.ofNat (ℕ × ℕ) k).1 then be (Denumerable.ofNat (ℕ × ℕ) k).2
      else true :=
    Computable.cond (hbd.comp (Computable.fst.comp hofNat))
      (hbe.comp (Computable.snd.comp hofNat)) (Computable.const true)
  refine hcomp.of_eq fun k => ?_
  have h1 : (d.enum (Denumerable.ofNat (ℕ × ℕ) k).1 = ⊥) ↔
      (bd (Denumerable.ofNat (ℕ × ℕ) k).1 = true) :=
    iff_of_eq (congrFun hbdE _)
  have h2 : (e.enum (Denumerable.ofNat (ℕ × ℕ) k).2 = ⊥) ↔
      (be (Denumerable.ofNat (ℕ × ℕ) k).2 = true) :=
    iff_of_eq (congrFun hbeE _)
  rw [strictTest]
  by_cases hb : bd (Denumerable.ofNat (ℕ × ℕ) k).1 = true
  · rw [hb, cond_true, Bool.eq_iff_iff, decide_eq_true_iff]
    exact ⟨fun h _ => h2.mpr h, fun h => h2.mp (h (h1.mpr hb))⟩
  · have hb' : bd (Denumerable.ofNat (ℕ × ℕ) k).1 = false := by simpa using hb
    rw [hb', cond_false]
    symm
    rw [decide_eq_true_iff]
    intro h
    exact absurd (h1.mp h) hb

/-- **The index map `K(D ⊸ E) → K(D → E)`.** -/
noncomputable def strictCode (d : EffectivePresentation α) (e : EffectivePresentation β)
    (n : ℕ) : ℕ := filterCode (strictTest d e) n

omit [BoundedComplete β] in
theorem computable_strictCode (d : EffectivePresentation α) (e : EffectivePresentation β)
    (hd : RecursiveLE d) (he : RecursiveLE e) : Computable (strictCode d e) :=
  computable_filterCode' (computable_strictTest d e hd he)

omit [BoundedComplete β] in
/-- **The index map names the same set of compact pairs.** -/
theorem pairsOf_ofNat_strictCode (d : EffectivePresentation α) (e : EffectivePresentation β)
    (n : ℕ) :
    Effective.pairsOf d e (Denumerable.ofNat (Finset (ℕ × ℕ)) (strictCode d e n))
      = R46.Agent3.strictPairsOf d e (Denumerable.ofNat (Finset (ℕ × ℕ)) n) := by
  rw [strictCode, ofNat_finset_filterCode]
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [Finset.mem_coe, Finset.mem_filter] at hq
    exact ⟨⟨q, hq.1, rfl⟩, (strictTest_encode d e q).mp hq.2⟩
  · rintro ⟨⟨q, hq, rfl⟩, hstrict⟩
    refine ⟨q, ?_, rfl⟩
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨hq, (strictTest_encode d e q).mpr hstrict⟩

omit [BoundedComplete β] in
/-- **The enumeration identity.** The `n`-th value of the strict enumeration is,
as a function of `D → E`, the `strictCode d e n`-th value of the arrow
enumeration. This is the fact r0052 recorded as missing. -/
theorem consistentEnum_strictCode [Domain (StrictHom α β)]
    (d : EffectivePresentation α) (e : EffectivePresentation β) (n : ℕ) :
    consistentEnum d e (strictCode d e n) = (strictConsistentEnum d e n).val := by
  classical
  rw [show consistentEnum d e (strictCode d e n)
      = if Consistent (Effective.pairsOf d e
            (Denumerable.ofNat (Finset (ℕ × ℕ)) (strictCode d e n)))
        then ScottHom.ofPairs (Effective.pairsOf d e
            (Denumerable.ofNat (Finset (ℕ × ℕ)) (strictCode d e n)))
        else ⊥ from rfl,
    pairsOf_ofNat_strictCode]
  rw [show strictConsistentEnum d e n
      = if Consistent (R46.Agent3.strictPairsOf d e (Denumerable.ofNat (Finset (ℕ × ℕ)) n))
        then R46.Agent3.strictStepJoin d e (Denumerable.ofNat (Finset (ℕ × ℕ)) n)
        else ⊥ from rfl]
  split_ifs with h
  · rfl
  · rfl

end Injection

/-! ## 6. The transport: order and normality across `Subtype.val`

`ClosureProperties.strictHom` is the retraction `D → E ↠ D ⊸ E`, right adjoint to
the inclusion (`le_strictHom_iff`). It is what makes the least upper bounds of the
subtype agree with those of the ambient space, which is what normality is stated
in terms of once `isNormalIn_compacts_iff` is applied. -/

section Transport

variable {α β : Type*} [CompletePartialOrder α] [CompletePartialOrder β] [BoundedComplete β]

/-- **`D ⊸ E` is bounded complete when `D → E` is**, with no bounded-completeness
hypothesis on `D`. `Skeleton.lemma_10_strict` proves the same thing but asks for
`[Domain α] [BoundedComplete α] [Domain β]`, none of which
`R49.Agent3.StrictHomCRecursive` grants. The proof is the subtype's `sSup`, which
is the ambient one. -/
theorem boundedComplete_strictHom : BoundedComplete (StrictHom α β) where
  isLUB_sSup_of_bddAbove s hs := by
    obtain ⟨u, hu⟩ := hs
    have hb : BddAbove (Subtype.val '' s) := ⟨u.val, by rintro _ ⟨g, hg, rfl⟩; exact hu hg⟩
    have h := isLUB_sSup_of_bddAbove hb
    constructor
    · intro g hg
      show (g.val : ScottHom α β) ≤ sSup (Subtype.val '' s)
      exact h.1 ⟨g, hg, rfl⟩
    · intro v hv
      show sSup (Subtype.val '' s) ≤ (v.val : ScottHom α β)
      exact h.2 (by rintro _ ⟨g, hg, rfl⟩; exact hv hg)

omit [BoundedComplete β] in
/-- **The inclusion `D ⊸ E ↪ D → E` is left adjoint to strictification.** -/
theorem le_strictHom_iff (g : StrictHom α β) (x : ScottHom α β) :
    g ≤ ClosureProperties.strictHom x ↔ (g.val : ScottHom α β) ≤ x := by
  constructor
  · intro h
    exact (Subtype.coe_le_coe.mpr h).trans (ClosureProperties.strictHom_val_le x)
  · intro h
    have := ClosureProperties.monotone_strictHom h
    rwa [show ClosureProperties.strictHom (g.val : ScottHom α β) = g from
      Subtype.ext (ClosureProperties.strictHom_val_of_isStrict g.2)] at this

omit [BoundedComplete β] in
/-- **A least upper bound of two strict functions is strict.** -/
theorem isStrict_of_isLUB_pair {a b : StrictHom α β} {C : ScottHom α β}
    (h : IsLUB ({(a.val : ScottHom α β), (b.val : ScottHom α β)} : Set (ScottHom α β)) C) :
    IsStrict C := by
  have ha : (a.val : ScottHom α β) ≤ (ClosureProperties.strictHom C).val :=
    (le_strictHom_iff a C).mpr (h.1 (Set.mem_insert _ _))
  have hb : (b.val : ScottHom α β) ≤ (ClosureProperties.strictHom C).val :=
    (le_strictHom_iff b C).mpr (h.1 (Set.mem_insert_of_mem _ rfl))
  have hub : (ClosureProperties.strictHom C).val ∈
      upperBounds ({(a.val : ScottHom α β), (b.val : ScottHom α β)} : Set (ScottHom α β)) := by
    rintro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | rfl
    · exact ha
    · exact hb
  have hCeq : C = (ClosureProperties.strictHom C).val :=
    le_antisymm (h.2 hub) (ClosureProperties.strictHom_val_le C)
  rw [hCeq]
  exact (ClosureProperties.strictHom C).2

omit [BoundedComplete β] in
/-- **Binary least upper bounds of the subtype are those of the ambient space.** -/
theorem isLUB_pair_val_iff {a b c : StrictHom α β} :
    IsLUB ({a, b} : Set (StrictHom α β)) c ↔
      IsLUB ({(a.val : ScottHom α β), (b.val : ScottHom α β)} : Set (ScottHom α β))
        (c.val : ScottHom α β) := by
  constructor
  · intro h
    constructor
    · rintro z hz
      rcases Set.mem_insert_iff.mp hz with rfl | rfl
      · exact h.1 (Set.mem_insert _ _)
      · exact h.1 (Set.mem_insert_of_mem _ rfl)
    · intro V hV
      have hstrict : c ≤ ClosureProperties.strictHom V := by
        refine h.2 ?_
        rintro z hz
        rcases Set.mem_insert_iff.mp hz with rfl | rfl
        · exact (le_strictHom_iff _ _).mpr (hV (Set.mem_insert _ _))
        · exact (le_strictHom_iff _ _).mpr (hV (Set.mem_insert_of_mem _ rfl))
      exact ((le_strictHom_iff c V).mp hstrict)
  · intro h
    constructor
    · rintro z hz
      rcases Set.mem_insert_iff.mp hz with rfl | rfl
      · exact h.1 (Set.mem_insert _ _)
      · exact h.1 (Set.mem_insert_of_mem _ rfl)
    · intro v hv
      refine h.2 ?_
      rintro z hz
      rcases Set.mem_insert_iff.mp hz with rfl | rfl
      · exact hv (Set.mem_insert _ _)
      · exact hv (Set.mem_insert_of_mem _ rfl)

/-- **Normality transports across the injection `K(D ⊸ E) ↪ K(D → E)`.**

Both sides are read through `R47.Agent2.isNormalIn_compacts_iff` — over a bounded
complete cpo, `N ◁ K(D)` is "`N` consists of compacts, contains `⊥`, and is closed
under the binary joins that exist". Each of the three conditions matches its
image under `Subtype.val`: compactness by
`ClosureProperties.isCompactElement_val_of_isCompactElement` and its converse,
`⊥` because `(⊥ : D ⊸ E).val = ⊥`, and the joins by `isLUB_pair_val_iff`.

This is the transport lemma the r0053 plan asks for, in the shape the argument
actually has: the embedding is an order-embedding whose image is closed under the
existing joins, and normality is exactly a statement about those. -/
theorem isNormalIn_val_image_iff {N : Set (StrictHom α β)} :
    N ◁ compacts (StrictHom α β) ↔ (Subtype.val '' N) ◁ compacts (ScottHom α β) := by
  haveI : BoundedComplete (StrictHom α β) := boundedComplete_strictHom
  rw [isNormalIn_compacts_iff, isNormalIn_compacts_iff]
  constructor
  · rintro ⟨hsub, hbot, hcl⟩
    refine ⟨?_, ⟨⊥, hbot, rfl⟩, ?_⟩
    · rintro _ ⟨g, hg, rfl⟩
      exact ClosureProperties.isCompactElement_val_of_isCompactElement (hsub hg)
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ C hC
      exact ⟨⟨C, isStrict_of_isLUB_pair hC⟩,
        hcl a ha b hb ⟨C, isStrict_of_isLUB_pair hC⟩ (isLUB_pair_val_iff.mpr hC), rfl⟩
  · rintro ⟨hsub, hbot, hcl⟩
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      exact ClosureProperties.isCompactElement_of_isCompactElement_val (hsub ⟨g, hg, rfl⟩)
    · obtain ⟨g, hg, hgv⟩ := hbot
      have : g = ⊥ := Subtype.ext hgv
      rwa [this] at hg
    · intro a ha b hb c hc
      obtain ⟨g, hg, hgv⟩ :=
        hcl _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ (c.val : ScottHom α β) (isLUB_pair_val_iff.mp hc)
      have : g = c := Subtype.ext hgv
      rwa [this] at hg

end Transport

/-! ## 7. `StrictHomCRecursive` from `ScottHomCRecursive` -/

section Main

variable {α β : Type*} [CompletePartialOrder α] [Domain α]
  [CompletePartialOrder β] [Domain β] [BoundedComplete β] [Domain (StrictHom α β)]

/-- **Condition 1 transports.** The order test on the strict enumeration is the
order test on the arrow enumeration, precomposed with the computable index map. -/
theorem recursiveLE_strictHomC (d : EffectivePresentation α) (e : EffectivePresentation β)
    (hd : RecursiveLE d) (he : RecursiveLE e) (h : RecursiveLE (scottHomC d e)) :
    RecursiveLE (strictHomC d e) := by
  obtain ⟨f, hf, hfE⟩ := ComputablePred.computable_iff.mp h
  have hσ : Computable (strictCode d e) := computable_strictCode d e hd he
  refine ComputablePred.computable_iff.mpr
    ⟨fun p : ℕ × ℕ => f (strictCode d e p.1, strictCode d e p.2),
      hf.comp (Computable.pair (hσ.comp Computable.fst) (hσ.comp Computable.snd)), ?_⟩
  funext p
  rw [← congrFun hfE (strictCode d e p.1, strictCode d e p.2)]
  show ((strictHomC d e).enum p.1 ≤ (strictHomC d e).enum p.2)
    = ((scottHomC d e).enum (strictCode d e p.1) ≤ (scottHomC d e).enum (strictCode d e p.2))
  show (strictConsistentEnum d e p.1 ≤ strictConsistentEnum d e p.2)
    = (consistentEnum d e (strictCode d e p.1) ≤ consistentEnum d e (strictCode d e p.2))
  rw [consistentEnum_strictCode, consistentEnum_strictCode]
  exact propext Subtype.coe_le_coe.symm

/-- **Condition 2 transports.** A finite index set names a normal subposet of
`K(D ⊸ E)` exactly when its image under the index map names one of `K(D → E)`
(`isNormalIn_val_image_iff`), and `imageCode` computes that image in the codes. -/
theorem recursiveNormal_strictHomC (d : EffectivePresentation α) (e : EffectivePresentation β)
    (hd : RecursiveLE d) (he : RecursiveLE e) (h : RecursiveNormal (scottHomC d e)) :
    RecursiveNormal (strictHomC d e) := by
  obtain ⟨f, hf, hfE⟩ := ComputablePred.computable_iff.mp h
  have hσ : Computable (strictCode d e) := computable_strictCode d e hd he
  refine ComputablePred.computable_iff.mpr
    ⟨fun n => f (imageCode (strictCode d e) n),
      hf.comp (computable_imageCode hσ), ?_⟩
  funext n
  rw [← congrFun hfE (imageCode (strictCode d e) n)]
  show ((strictConsistentEnum d e) '' (↑(Denumerable.ofNat (Finset ℕ) n) : Set ℕ)
        ◁ compacts (StrictHom α β))
    = ((consistentEnum d e) ''
        (↑(Denumerable.ofNat (Finset ℕ) (imageCode (strictCode d e) n)) : Set ℕ)
        ◁ compacts (ScottHom α β))
  refine propext (Iff.trans isNormalIn_val_image_iff ?_)
  have hval : (Subtype.val '' (strictConsistentEnum d e ''
        (↑(Denumerable.ofNat (Finset ℕ) n) : Set ℕ)))
      = consistentEnum d e ''
        (↑(Denumerable.ofNat (Finset ℕ) (imageCode (strictCode d e) n)) : Set ℕ) := by
    rw [ofNat_finset_imageCode, Finset.coe_image, Set.image_image, Set.image_image]
    exact Set.image_congr' fun m => (consistentEnum_strictCode d e m).symm
  rw [hval]

/-- **The collapse.** `R49.Agent3.StrictHomCRecursive d e` follows from
`R49.Agent3.ScottHomCRecursive d e`.

This is a **conditional** result: it closes no `sorry`. What it does is remove one
of the development's three independent open statements — after it,
`R49.Agent3.strictHomCRecursive_unproven` is a corollary of
`R49.Agent3.scottHomCRecursive_unproven` and not a second root. -/
theorem strictHomCRecursive_of_scottHomC (d : EffectivePresentation α)
    (e : EffectivePresentation β) (h : R49.Agent3.ScottHomCRecursive d e) :
    R49.Agent3.StrictHomCRecursive d e := fun hd he =>
  ⟨recursiveLE_strictHomC d e hd.1 he.1 (h hd he).1,
    recursiveNormal_strictHomC d e hd.1 he.1 (h hd he).2⟩

end Main

/-- **Theorem 7's third sentence from the arrow residue alone.** The `⊸`
counterpart of `R49.Agent3.three_claims_of_residue`: the fourth claim,
`Effective.Theorem7StrictRecursive`, no longer needs a residue of its own. -/
theorem theorem_7_strictRecursive_of_scottHomC.{u}
    (h : ∀ {α : Type u} {β : Type u} [CompletePartialOrder α] [Domain α]
      [CompletePartialOrder β] [Domain β] [BoundedComplete β]
      (d : EffectivePresentation α) (e : EffectivePresentation β),
      R49.Agent3.ScottHomCRecursive d e) :
    Effective.Theorem7StrictRecursive.{u, u} :=
  R49.Agent3.theorem_7_strictRecursive_of_residue
    fun d e => strictHomCRecursive_of_scottHomC d e (h d e)

end ScottDomains.R53.Agent2
