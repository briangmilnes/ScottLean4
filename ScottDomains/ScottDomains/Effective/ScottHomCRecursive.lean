import ScottDomains.Effective.A3StepDecidable
import ScottDomains.Effective.A4Recursion

/-!
# r0053, agent1: the recursion theory of `R47.Agent2.scottHomC`

`R49.Agent3.ScottHomCRecursive d e` is `IsRecursive d → IsRecursive e →
IsRecursive (scottHomC d e)`, and `Effective.IsRecursive` is the conjunction
`Computable.RecursiveLE ∧ Effective.RecursiveNormal`. This module discharges
**both conjuncts**, under one instance the statement in
`Effective/A3StepDecidable.lean` does not carry: `[BoundedComplete α]`.

## What is proved

| # | Declaration | Statement |
| -- | ---------- | --------- |
| 1 | `recursiveLE_scottHomC` | `IsRecursive d → IsRecursive e → RecursiveLE (scottHomC d e)` |
| 2 | `recursiveNormal_scottHomC` | `IsRecursive d → IsRecursive e → RecursiveNormal (scottHomC d e)` |
| 3 | `scottHomCRecursive_of_boundedComplete` | `R49.Agent3.ScottHomCRecursive d e`, from 1 and 2 |
| 4 | `stepFunctionsDecidable_of_boundedComplete` | `Effective.StepFunctionsDecidable d e`, from 3 |

`#print axioms` on each shows `propext`, `Classical.choice`, `Quot.sound` and no
`sorryAx`. Every `ComputablePred` below is discharged through
`ComputablePred.computable_iff` — "`p` is the extension of a `Computable`
`Bool`-valued function" — so no decision is supplied by `Classical.propDecidable`
standing in for a program. `Classical.choice` enters only where the surrounding
development already spends it: the total `sSup` on `ScottHom`, the classical `if`
inside `R47.Agent2.consistentEnum`, and the `Decidable` instances the `Nat.find`
searches are written with, whose value `Computable.find` fixes independently of
the instance.

## The one added instance, and why it is the paper's own hypothesis

`[BoundedComplete α]` is needed at exactly one place and it is not removable by
rearranging the proof. `Consistent (pairsOf d e Q)` quantifies over the subsets
of the index set and asks, of each, whether its **sources** are bounded above in
`D`; `R49.Agent4.computablePred_bddAbove` decides boundedness of a finite set of
basis elements and carries `[BoundedComplete γ]`, because its route —
`R47.Agent2.bddAbove_iff_exists_normal` through `isNormalIn_joinClosure` — needs
the join of a bounded pair of compacts to exist.

Without bounded completeness of `D` the test does not disappear, it drops a
quantifier class: in an algebraic cpo a finite set of compacts is bounded exactly
when some *compact* bounds it (the compacts below a bound are directed), so
"bounded" is `Σ₁` in the indices and "consistent" is `Π₁`. A `Σ₁` test is not a
decision procedure, and this development has no theorem making it one.

`Domain` here is `IsAlgebraic` plus a countable basis; Gunter & Scott's "domain"
in Theorem 7 is bounded complete, which is also why `[BoundedComplete β]` already
appears on every statement about `D → E` in this development. The instance added
here is the same hypothesis, on `D` instead of on `E`. The root
`R49.Agent3.scottHomCRecursive_unproven` is therefore **left alone**: its binder
list does not include `[BoundedComplete α]`, so nothing here discharges it as
stated.

Nothing here edits `Effective/A3StepDecidable.lean`.
-/

namespace ScottDomains.R53.Agent1

open ScottDomains ScottDomains.Effective ScottDomains.R47.Agent2 ScottDomains.R49.Agent4
open ScottDomains.Computable (RecursiveLE)

/-! ## 1. Bounded quantification over a computable list

`R49.Agent4.computablePred_forall_mem` quantifies over `Denumerable.ofNat
(Finset ℕ) (code a)`. Two of the searches below quantify over a decoded
`Finset (ℕ × ℕ)` and one over a list of sublists, so the same argument is
restated once for an arbitrary computable list-valued function. -/

theorem forall_mem_list_iff {σ : Type*} [Inhabited σ] (L : List σ) (R : σ → Prop) :
    (∀ s ∈ L, R s) ↔ ∀ k < L.length, R (L.getI k) := by
  constructor
  · intro h k hk
    refine h _ ?_
    rw [List.getI_eq_getElem _ hk]
    exact List.getElem_mem hk
  · intro h s hs
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hs
    rw [← List.getI_eq_getElem _ hk]
    exact h k hk

/-- **`∀ s ∈ l a, R a s` is computable when `l` and `R` are.** -/
theorem computablePred_forall_mem_list {A σ : Type*} [Primcodable A] [Primcodable σ]
    [Inhabited σ] {l : A → List σ} (hl : Computable l) {R : A → σ → Prop} [DecidableRel R]
    (hR : ComputablePred fun p : A × σ => R p.1 p.2) :
    ComputablePred fun a : A => ∀ s ∈ l a, R a s := by
  classical
  have hget : Computable fun p : A × ℕ => (l p.1).getI p.2 :=
    Computable₂.comp (Primrec.list_getI.to_comp) (hl.comp Computable.fst) Computable.snd
  have hq : Computable₂ fun (a : A) (k : ℕ) => decide (R a ((l a).getI k)) :=
    Computable.to₂ (hR.decide.comp (Computable.pair Computable.fst hget))
  have hlen : Computable fun a : A => (l a).length :=
    (Primrec.list_length.to_comp).comp hl
  refine Computable.computablePred (p := fun a : A => ∀ s ∈ l a, R a s) ?_
  refine ((computable_allLt hq).comp (Computable.pair Computable.id hlen)).of_eq fun a => ?_
  rw [Bool.eq_iff_iff, decide_eq_true_iff, allLt_eq_true]
  simpa using (forall_mem_list_iff (l a) (R a)).symm

/-- …and the existential form. -/
theorem computablePred_exists_mem_list {A σ : Type*} [Primcodable A] [Primcodable σ]
    [Inhabited σ] {l : A → List σ} (hl : Computable l) {R : A → σ → Prop} [DecidableRel R]
    (hR : ComputablePred fun p : A × σ => R p.1 p.2) :
    ComputablePred fun a : A => ∃ s ∈ l a, R a s := by
  classical
  have hnot : ComputablePred fun a : A => ∀ s ∈ l a, ¬ R a s :=
    computablePred_forall_mem_list hl (R := fun a s => ¬ R a s) (ComputablePred.not hR)
  refine (ComputablePred.not hnot).of_eq fun a => ?_
  simp

/-- Implication, the third `ComputablePred` closure fact this development needs
after `R49.Agent4.computablePred_and` and `computablePred_or`. -/
theorem computablePred_imp {A : Type*} [Primcodable A] {p q : A → Prop}
    (hp : ComputablePred p) (hq : ComputablePred q) :
    ComputablePred fun a => p a → q a := by
  classical
  refine (computablePred_or (ComputablePred.not hp) hq).of_eq fun a => ?_
  constructor
  · rintro (h | h)
    · exact fun hh => absurd hh h
    · exact fun _ => h
  · intro h
    by_cases hh : p a
    · exact Or.inr (h hh)
    · exact Or.inl hh

/-- Membership in a list is primitive recursive: `∃ a ∈ L, a = x`. -/
theorem primrecRel_mem_list {σ : Type*} [Primcodable σ] [DecidableEq σ] :
    PrimrecRel fun (L : List σ) (x : σ) => x ∈ L :=
  (PrimrecRel.exists_mem_list Primrec.eq).of_eq fun _ x =>
    ⟨fun ⟨_, ha, hax⟩ => hax ▸ ha, fun h => ⟨x, h, rfl⟩⟩

/-- Surjectivity of the `Finset (ℕ × ℕ)` decoding. Stated rather than used inline
for the reason `Effective.surjective_ofNat_finset` gives: `Finset (ℕ × ℕ)` carries
two `Encodable` instances and only the `Denumerable` one satisfies
`Denumerable.ofNat_encode`, so the lemma supplies its own `encode`. -/
theorem surjective_ofNat_finset_pair :
    Function.Surjective (Denumerable.ofNat (Finset (ℕ × ℕ))) :=
  fun Q => ⟨_, Denumerable.ofNat_encode Q⟩

theorem exists_ofNat_pair_empty : ∃ m, Denumerable.ofNat (Finset (ℕ × ℕ)) m = ∅ :=
  surjective_ofNat_finset_pair ∅

/-- A code for the empty index set. `R47.Agent2.consistentEnum` takes the value
`⊥` there, which is the value it takes on every inconsistent index set.

Specified by `Classical.choose` rather than by `Nat.find`: with `Nat.find` and the
real `DecidableEq (Finset (ℕ × ℕ))` instance, an `isDefEq` query meeting this
constant can try to *evaluate* the search, which runs into `Nat.unpair`'s
`Nat.sqrt` — a reduction `R49.Agent4` records as stuck. Nothing is given up: a
constant is computable however it is specified (`Computable.const`). -/
noncomputable def emptyPairCode : ℕ := Classical.choose exists_ofNat_pair_empty

theorem ofNat_emptyPairCode : Denumerable.ofNat (Finset (ℕ × ℕ)) emptyPairCode = ∅ :=
  Classical.choose_spec exists_ofNat_pair_empty

/-! ## 2. The subsets of a finite set, as a primitive recursive list of lists

`R47.Agent2.Consistent P` quantifies over the subsets of `P`. `P` is finite, so
the quantifier is bounded — but by the power set, which has to be produced as a
list before it can be quantified over. -/

/-- Every sublist of `L`, in `List.sublists'` order. Defined here rather than
reused from `List.sublists'` because the `Primrec` fact below is proved from
this equation and Mathlib states no primitive recursiveness for `sublists'`. -/
def sublistsAux {σ : Type*} : List σ → List (List σ)
  | [] => [[]]
  | (a :: l) => sublistsAux l ++ (sublistsAux l).map (fun t => a :: t)

theorem mem_of_mem_sublistsAux {σ : Type*} {L T : List σ} (hT : T ∈ sublistsAux L) :
    ∀ x ∈ T, x ∈ L := by
  induction L generalizing T with
  | nil =>
      rw [sublistsAux, List.mem_singleton] at hT
      subst hT
      simp
  | cons a l ih =>
      rw [sublistsAux, List.mem_append] at hT
      rcases hT with hT | hT
      · exact fun x hx => List.mem_cons_of_mem _ (ih hT x hx)
      · obtain ⟨T', hT', rfl⟩ := List.mem_map.mp hT
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (ih hT' x hx)

/-- **Every decidable subset of `L` is realized as a member of `sublistsAux L`.**
The witness is `L.filter p`, which is why the list of *sublists* rather than of
subsets is the right object: a subset of the underlying set is cut out by a
predicate, and filtering respects the list structure. -/
theorem filter_mem_sublistsAux {σ : Type*} (p : σ → Bool) :
    ∀ L : List σ, L.filter p ∈ sublistsAux L
  | [] => by simp [sublistsAux]
  | (a :: l) => by
      rw [sublistsAux, List.filter_cons]
      by_cases h : p a = true
      · rw [if_pos h]
        exact List.mem_append_right _
          (List.mem_map.mpr ⟨l.filter p, filter_mem_sublistsAux p l, rfl⟩)
      · rw [if_neg h]
        exact List.mem_append_left _ (filter_mem_sublistsAux p l)

theorem primrec_sublistsAux {σ : Type*} [Primcodable σ] :
    Primrec (sublistsAux : List σ → List (List σ)) := by
  have hih : Primrec fun p : List σ × (σ × List σ × List (List σ)) => p.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hmap : Primrec fun p : List σ × (σ × List σ × List (List σ)) =>
      p.2.2.2.map (fun t => p.2.1 :: t) :=
    Primrec.list_map hih
      (Primrec.to₂ (Primrec₂.comp Primrec.list_cons
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd))
  have hstep : Primrec₂ fun (_ : List σ) (x : σ × List σ × List (List σ)) =>
      x.2.2 ++ x.2.2.map (fun t => x.1 :: t) :=
    Primrec.to₂ (Primrec₂.comp Primrec.list_append hih hmap)
  refine (Primrec.list_rec Primrec.id (Primrec.const ([[]] : List (List σ))) hstep).of_eq ?_
  intro L
  induction L with
  | nil => rfl
  | cons a l ih => simpa [sublistsAux] using congrArg (fun r => r ++ r.map (fun t => a :: t)) ih

/-! ## 3. A computable code for a computably-cut-out finite set

Both searches of section 5 need a `Finset` **code** for a set that is described
by a computable membership test inside a computable finite list of candidates.
`Denumerable.ofNat` is onto, so the code exists; the search for it terminates
and its test is bounded by the candidate list. -/

section CodeSearch

variable {A σ : Type*} [Primcodable A] [Primcodable σ] [Inhabited σ] [DecidableEq σ]

/-- `m` codes exactly the members of `cand a` satisfying `memb a`. -/
def SetCodeAt (ofn : ℕ → Finset σ) (memb : A → σ → Prop) (cand : A → List σ)
    (a : A) (m : ℕ) : Prop :=
  (∀ x ∈ ofn m, memb a x) ∧ (∀ x ∈ cand a, memb a x → x ∈ ofn m)

noncomputable instance decidableSetCodeAt (ofn : ℕ → Finset σ) (memb : A → σ → Prop)
    (cand : A → List σ) : DecidableRel (SetCodeAt ofn memb cand) := fun _ _ => Classical.dec _

omit [Primcodable A] [Primcodable σ] [Inhabited σ] in
theorem exists_setCodeAt {ofn : ℕ → Finset σ} (hsurj : Function.Surjective ofn)
    (memb : A → σ → Prop) (cand : A → List σ) (a : A) :
    ∃ m, SetCodeAt ofn memb cand a m := by
  classical
  obtain ⟨m, hm⟩ := hsurj ((cand a).toFinset.filter (memb a))
  refine ⟨m, fun x hx => ?_, fun x hx hmx => ?_⟩
  · rw [hm, Finset.mem_filter] at hx
    exact hx.2
  · rw [hm, Finset.mem_filter]
    exact ⟨List.mem_toFinset.mpr hx, hmx⟩

/-- The code, as an unbounded search that `exists_setCodeAt` proves total. -/
noncomputable def setCode (ofn : ℕ → Finset σ) (memb : A → σ → Prop) (cand : A → List σ)
    (h : ∀ a, ∃ m, SetCodeAt ofn memb cand a m) (a : A) : ℕ :=
  Nat.find (h a)

omit [Primcodable A] [Primcodable σ] [Inhabited σ] [DecidableEq σ] in
/-- **The code names exactly the set the membership test cuts out**, provided
every element passing the test is among the candidates. -/
theorem mem_ofn_setCode {ofn : ℕ → Finset σ} {memb : A → σ → Prop} {cand : A → List σ}
    (h : ∀ a, ∃ m, SetCodeAt ofn memb cand a m) (hsub : ∀ a x, memb a x → x ∈ cand a)
    (a : A) (x : σ) : x ∈ ofn (setCode ofn memb cand h a) ↔ memb a x := by
  have hs := Nat.find_spec (h a)
  exact ⟨fun hx => hs.1 x hx, fun hx => hs.2 x (hsub a x hx) hx⟩

theorem computable_setCode {ofn : ℕ → Finset σ} {dec : ℕ → List σ} (hdecp : Primrec dec)
    (hdec : ∀ (x : σ) (m : ℕ), x ∈ dec m ↔ x ∈ ofn m)
    {memb : A → σ → Prop} [DecidableRel memb]
    (hmemb : ComputablePred fun p : A × σ => memb p.1 p.2)
    {cand : A → List σ} (hcand : Computable cand)
    (h : ∀ a, ∃ m, SetCodeAt ofn memb cand a m) :
    Computable (setCode ofn memb cand h) := by
  classical
  have hmembp : ComputablePred fun q : (A × ℕ) × σ => memb q.1.1 q.2 :=
    computablePred_comp hmemb
      (Computable.pair (Computable.fst.comp (Computable.fst.comp Computable.id)) Computable.snd)
  have h1 : ComputablePred fun p : A × ℕ => ∀ x ∈ dec p.2, memb p.1 x :=
    computablePred_forall_mem_list (l := fun p : A × ℕ => dec p.2)
      (hdecp.to_comp.comp Computable.snd) (R := fun (p : A × ℕ) (x : σ) => memb p.1 x) hmembp
  have hmemdec : ComputablePred fun q : (A × ℕ) × σ => q.2 ∈ dec q.1.2 :=
    computablePred_comp
      (PrimrecRel.comp primrecRel_mem_list Primrec.fst Primrec.snd).computablePred
      (Computable.pair (hdecp.to_comp.comp (Computable.snd.comp Computable.fst)) Computable.snd)
  have h2 : ComputablePred fun p : A × ℕ => ∀ x ∈ cand p.1, memb p.1 x → x ∈ dec p.2 :=
    computablePred_forall_mem_list (l := fun p : A × ℕ => cand p.1)
      (hcand.comp Computable.fst)
      (R := fun (p : A × ℕ) (x : σ) => memb p.1 x → x ∈ dec p.2)
      (computablePred_imp hmembp hmemdec)
  have hall : ComputablePred fun p : A × ℕ => SetCodeAt ofn memb cand p.1 p.2 :=
    (computablePred_and h1 h2).of_eq fun p => by
      unfold SetCodeAt
      constructor
      · rintro ⟨ha, hb⟩
        exact ⟨fun x hx => ha x ((hdec x p.2).mpr hx),
          fun x hx hmx => (hdec x p.2).mp (hb x hx hmx)⟩
      · rintro ⟨ha, hb⟩
        exact ⟨fun x hx => ha x ((hdec x p.2).mp hx),
          fun x hx hmx => (hdec x p.2).mpr (hb x hx hmx)⟩
  exact Computable.find hall h

end CodeSearch

/-! ## 4. Boundedness and joins for a list-indexed finite set of basis elements

`R49.Agent4` states both facts for an index set given by a `Finset ℕ` **code**.
The sets that arise below are given by lists, so this section transports the two
statements along `finsetCode`. -/

section ListJoin

variable {γ : Type*} [CompletePartialOrder γ] [Domain γ] [BoundedComplete γ]

theorem exists_finsetCodeAt (l : List ℕ) :
    ∃ m, SetCodeAt (Denumerable.ofNat (Finset ℕ)) (fun (l : List ℕ) (x : ℕ) => x ∈ l) id l m :=
  exists_setCodeAt surjective_ofNat_finset_nat _ _ l

/-- A `Finset ℕ` code for the set of entries of a list. -/
noncomputable def finsetCode : List ℕ → ℕ :=
  setCode (Denumerable.ofNat (Finset ℕ)) (fun (l : List ℕ) (x : ℕ) => x ∈ l) id
    exists_finsetCodeAt

theorem mem_ofNat_finsetCode (l : List ℕ) (x : ℕ) :
    x ∈ Denumerable.ofNat (Finset ℕ) (finsetCode l) ↔ x ∈ l :=
  mem_ofn_setCode exists_finsetCodeAt (fun _ _ h => h) l x

theorem computable_finsetCode : Computable finsetCode := by
  classical
  exact computable_setCode primrec_idxList (fun x m => mem_ofNat_finset_nat_iff.symm)
    (PrimrecRel.comp primrecRel_mem_list Primrec.fst Primrec.snd).computablePred
    Computable.id exists_finsetCodeAt

omit [BoundedComplete γ] in
theorem basisSet_finsetCode (f : EffectivePresentation γ) (l : List ℕ) :
    basisSet f (finsetCode l) = f.enum '' {j : ℕ | j ∈ l} := by
  unfold basisSet
  congr 1
  ext j
  exact mem_ofNat_finsetCode l j

/-- **Boundedness of the basis elements named by a computable list is
decidable.** `R49.Agent4.computablePred_bddAbove` with the index set supplied as
a list rather than as a `Finset ℕ` code. -/
theorem computablePred_bddAbove_list {A : Type*} [Primcodable A]
    {f : EffectivePresentation γ} (hf : IsRecursive f) {l : A → List ℕ} (hl : Computable l) :
    ComputablePred fun a : A => BddAbove (f.enum '' {j : ℕ | j ∈ l a}) :=
  (computablePred_comp (computablePred_bddAbove hf)
    (computable_finsetCode.comp hl)).of_eq fun a => by rw [basisSet_finsetCode]

end ListJoin

/-! ## 5. Deciding `R47.Agent2.Consistent` on an index set

`Consistent P` quantifies over the subsets of `P`, and `P = pairsOf d e Q` is
the image of a decoded `Finset (ℕ × ℕ)`. Section 2 turns that quantifier into a
bounded one; section 4 decides each of its two atoms. -/

section Consistency

variable {α β : Type*} [CompletePartialOrder α] [Domain α] [BoundedComplete α]
  [CompletePartialOrder β] [Domain β] [BoundedComplete β]
variable (d : EffectivePresentation α) (e : EffectivePresentation β)

omit [BoundedComplete α] [BoundedComplete β] in
theorem image_fst_pairsImage (T : List (ℕ × ℕ)) :
    Prod.fst '' ((fun q : ℕ × ℕ => (d.enum q.1, e.enum q.2)) '' {q : ℕ × ℕ | q ∈ T})
      = d.enum '' {i : ℕ | i ∈ T.map Prod.fst} := by
  ext x
  constructor
  · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨q.1, List.mem_map.mpr ⟨q, hq, rfl⟩, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hi
    exact ⟨(d.enum q.1, e.enum q.2), ⟨q, hq, rfl⟩, rfl⟩

omit [BoundedComplete α] [BoundedComplete β] in
theorem image_snd_pairsImage (T : List (ℕ × ℕ)) :
    Prod.snd '' ((fun q : ℕ × ℕ => (d.enum q.1, e.enum q.2)) '' {q : ℕ × ℕ | q ∈ T})
      = e.enum '' {j : ℕ | j ∈ T.map Prod.snd} := by
  ext x
  constructor
  · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨q.2, List.mem_map.mpr ⟨q, hq, rfl⟩, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hj
    exact ⟨(d.enum q.1, e.enum q.2), ⟨q, hq, rfl⟩, rfl⟩

omit [BoundedComplete α] [BoundedComplete β] in
/-- **Consistency of an index set is a bounded condition on its sublists.**
Every subset of `pairsOf d e Q` is the image of a sublist of the decoded index
list, and the two boundedness tests read off the two projections of that
sublist. -/
theorem consistent_pairsOf_iff (n : ℕ) :
    Consistent (Effective.pairsOf d e (Denumerable.ofNat (Finset (ℕ × ℕ)) n)) ↔
      ∀ T ∈ sublistsAux (decodeList (ℕ × ℕ) n),
        BddAbove (d.enum '' {i : ℕ | i ∈ T.map Prod.fst}) →
          BddAbove (e.enum '' {j : ℕ | j ∈ T.map Prod.snd}) := by
  classical
  constructor
  · intro hc T hT hb
    have hsub : (fun q : ℕ × ℕ => (d.enum q.1, e.enum q.2)) '' {q : ℕ × ℕ | q ∈ T}
        ⊆ Effective.pairsOf d e (Denumerable.ofNat (Finset (ℕ × ℕ)) n) := by
      rintro _ ⟨q, hq, rfl⟩
      exact ⟨q, Finset.mem_coe.mpr (mem_decodeList.mp (mem_of_mem_sublistsAux hT q hq)), rfl⟩
    have := hc _ hsub (by rw [image_fst_pairsImage]; exact hb)
    rwa [image_snd_pairsImage] at this
  · intro h S hS hb
    set p : ℕ × ℕ → Bool := fun q => decide ((d.enum q.1, e.enum q.2) ∈ S) with hp
    set T : List (ℕ × ℕ) := (decodeList (ℕ × ℕ) n).filter p with hTdef
    have hTmem : T ∈ sublistsAux (decodeList (ℕ × ℕ) n) :=
      hTdef ▸ filter_mem_sublistsAux p _
    have himg : (fun q : ℕ × ℕ => (d.enum q.1, e.enum q.2)) '' {q : ℕ × ℕ | q ∈ T} = S := by
      ext s
      constructor
      · rintro ⟨q, hq, rfl⟩
        have := (List.mem_filter.mp hq).2
        simpa [hp] using this
      · intro hs
        obtain ⟨q, hq, rfl⟩ := hS hs
        refine ⟨q, ?_, rfl⟩
        refine List.mem_filter.mpr ⟨mem_decodeList.mpr (Finset.mem_coe.mp hq), ?_⟩
        simpa [hp] using hs
    have hb' : BddAbove (d.enum '' {i : ℕ | i ∈ T.map Prod.fst}) := by
      rw [← image_fst_pairsImage d e, himg]; exact hb
    have := h T hTmem hb'
    rwa [← image_snd_pairsImage d e, himg] at this

/-- **`Consistent (pairsOf d e Q)` is decided by the two conditions of §3.2 on
`d` and on `e`.** The quantifier over subsets is the sublist enumeration of
section 2; the source test is `R49.Agent4.computablePred_bddAbove` at `d` and
the value test the same at `e`. -/
theorem computablePred_consistent (hd : IsRecursive d) (he : IsRecursive e) :
    ComputablePred fun n : ℕ =>
      Consistent (Effective.pairsOf d e (Denumerable.ofNat (Finset (ℕ × ℕ)) n)) := by
  classical
  have hsrc : ComputablePred fun p : ℕ × List (ℕ × ℕ) =>
      BddAbove (d.enum '' {i : ℕ | i ∈ p.2.map Prod.fst}) :=
    computablePred_bddAbove_list hd
      (Primrec.list_map Primrec.snd (Primrec.to₂ (Primrec.fst.comp Primrec.snd))).to_comp
  have hval : ComputablePred fun p : ℕ × List (ℕ × ℕ) =>
      BddAbove (e.enum '' {j : ℕ | j ∈ p.2.map Prod.snd}) :=
    computablePred_bddAbove_list he
      (Primrec.list_map Primrec.snd (Primrec.to₂ (Primrec.snd.comp Primrec.snd))).to_comp
  refine (computablePred_forall_mem_list
    (l := fun n : ℕ => sublistsAux (decodeList (ℕ × ℕ) n))
    (primrec_sublistsAux.comp primrec_decodeList_pair).to_comp
    (R := fun (_ : ℕ) (T : List (ℕ × ℕ)) =>
      BddAbove (d.enum '' {i : ℕ | i ∈ T.map Prod.fst}) →
        BddAbove (e.enum '' {j : ℕ | j ∈ T.map Prod.snd}))
    (computablePred_imp hsrc hval)).of_eq fun n => (consistent_pairsOf_iff d e n).symm

end Consistency

/-! ## 6. Obligation 1: `Computable.RecursiveLE (scottHomC d e)`

`R49.Agent3.consistentEnum_le_iff` reduces the order test to a condition
quantifying over the two decoded index sets, with one atom left: `b ⊑ ⨆{values
below a}` in `E`. This section supplies a *code* for that join, so the atom
becomes a `≤` between two basis elements of `E` and `Computable.RecursiveLE e`
decides it. -/

section Order

variable {α β : Type*} [CompletePartialOrder α] [Domain α] [BoundedComplete α]
  [CompletePartialOrder β] [Domain β] [BoundedComplete β]
variable (d : EffectivePresentation α) (e : EffectivePresentation β)

omit [Domain α] [BoundedComplete α] [Domain β] [BoundedComplete β] in
theorem consistent_empty : Consistent (∅ : Set (α × β)) := by
  intro S hS _
  refine ⟨⊥, ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  exact (hS hq).elim

open Classical in
/-- **The index set `consistentEnum` actually joins at `n`**: `n`'s own when that
one is consistent, the empty one otherwise. Every value of the enumeration is
`ofPairs` of a *consistent* index set, which is what lets `R47.Agent2.ofPairs_le_iff`
and `ofPairs_apply` be applied uniformly, with no case split left in the
statements below. -/
noncomputable def normPairCode (n : ℕ) : ℕ :=
  if Consistent (Effective.pairsOf d e (Denumerable.ofNat (Finset (ℕ × ℕ)) n)) then n
  else emptyPairCode

omit [BoundedComplete α] [BoundedComplete β] in
theorem consistent_normPairCode (n : ℕ) :
    Consistent (Effective.pairsOf d e
      (Denumerable.ofNat (Finset (ℕ × ℕ)) (normPairCode d e n))) := by
  classical
  unfold normPairCode
  split_ifs with h
  · exact h
  · rw [ofNat_emptyPairCode, R49.Agent3.pairsOf_empty d e]
    exact consistent_empty

omit [BoundedComplete α] [BoundedComplete β] in
theorem consistentEnum_eq_ofPairs (n : ℕ) :
    consistentEnum d e n = ScottHom.ofPairs (Effective.pairsOf d e
      (Denumerable.ofNat (Finset (ℕ × ℕ)) (normPairCode d e n))) := by
  classical
  by_cases h : Consistent (Effective.pairsOf d e (Denumerable.ofNat (Finset (ℕ × ℕ)) n))
  · rw [consistentEnum, if_pos h, normPairCode, if_pos h]
  · rw [consistentEnum, if_neg h, normPairCode, if_neg h, ofNat_emptyPairCode,
      R49.Agent3.pairsOf_empty d e, R49.Agent3.ofPairs_empty]

theorem computable_normPairCode (hd : IsRecursive d) (he : IsRecursive e) :
    Computable (normPairCode d e) := by
  classical
  obtain ⟨g, hg, hgeq⟩ := ComputablePred.computable_iff.mp (computablePred_consistent d e hd he)
  refine (Computable.cond hg Computable.id (Computable.const emptyPairCode)).of_eq fun n => ?_
  have hiff : Consistent (Effective.pairsOf d e (Denumerable.ofNat (Finset (ℕ × ℕ)) n))
      ↔ g n = true := Iff.of_eq (congrFun hgeq n)
  by_cases hc : Consistent (Effective.pairsOf d e (Denumerable.ofNat (Finset (ℕ × ℕ)) n))
  · rw [hiff.mp hc]
    show n = normPairCode d e n
    rw [normPairCode, if_pos hc]
  · have hgn : g n = false := by
      rcases Bool.eq_false_or_eq_true (g n) with h | h
      · exact absurd (hiff.mpr h) hc
      · exact h
    rw [hgn]
    show emptyPairCode = normPairCode d e n
    rw [normPairCode, if_neg hc]

/-- `j` is the value of a pair of the `n`-th normalized index set whose source
lies below `dᵢ`. The join of these is the value `consistentEnum d e n` takes at
`dᵢ` — see `enum_joinBelow`. -/
def BelowVal (p : ℕ × ℕ) (j : ℕ) : Prop :=
  ∃ q ∈ Denumerable.ofNat (Finset (ℕ × ℕ)) (normPairCode d e p.1),
    d.enum q.1 ≤ d.enum p.2 ∧ q.2 = j

/-- The candidate list the search for `BelowVal`'s code is bounded by. -/
noncomputable def belowValCand (p : ℕ × ℕ) : List ℕ :=
  (decodeList (ℕ × ℕ) (normPairCode d e p.1)).map Prod.snd

omit [BoundedComplete α] [BoundedComplete β] in
theorem belowVal_mem_cand (p : ℕ × ℕ) (j : ℕ) :
    BelowVal d e p j → j ∈ belowValCand d e p := by
  rintro ⟨q, hq, _, rfl⟩
  exact List.mem_map.mpr ⟨q, mem_decodeList.mpr hq, rfl⟩

omit [BoundedComplete α] [BoundedComplete β] in
theorem exists_belowValCodeAt (p : ℕ × ℕ) :
    ∃ m, SetCodeAt (Denumerable.ofNat (Finset ℕ)) (BelowVal d e) (belowValCand d e) p m :=
  exists_setCodeAt surjective_ofNat_finset_nat _ _ p

/-- A `Finset ℕ` code for the values below `dᵢ`. -/
noncomputable def belowValCode : ℕ × ℕ → ℕ :=
  setCode (Denumerable.ofNat (Finset ℕ)) (BelowVal d e) (belowValCand d e)
    (exists_belowValCodeAt d e)

omit [BoundedComplete α] [BoundedComplete β] in
theorem mem_ofNat_belowValCode (p : ℕ × ℕ) (j : ℕ) :
    j ∈ Denumerable.ofNat (Finset ℕ) (belowValCode d e p) ↔ BelowVal d e p j :=
  mem_ofn_setCode (exists_belowValCodeAt d e) (belowVal_mem_cand d e) p j

omit [BoundedComplete α] [BoundedComplete β] in
theorem basisSet_belowValCode (n i : ℕ) :
    basisSet e (belowValCode d e (n, i))
      = Prod.snd '' belowSet (Effective.pairsOf d e
          (Denumerable.ofNat (Finset (ℕ × ℕ)) (normPairCode d e n))) (d.enum i) := by
  unfold basisSet
  ext y
  constructor
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨q, hq, hle, rfl⟩ := (mem_ofNat_belowValCode d e (n, i) j).mp (Finset.mem_coe.mp hj)
    exact ⟨(d.enum q.1, e.enum q.2), ⟨⟨q, Finset.mem_coe.mpr hq, rfl⟩, hle⟩, rfl⟩
  · rintro ⟨_, ⟨⟨q, hq, rfl⟩, hle⟩, rfl⟩
    exact ⟨q.2, Finset.mem_coe.mpr ((mem_ofNat_belowValCode d e (n, i) q.2).mpr
      ⟨q, Finset.mem_coe.mp hq, hle, rfl⟩), rfl⟩

omit [BoundedComplete α] [BoundedComplete β] in
theorem bddAbove_basisSet_belowValCode (n i : ℕ) :
    BddAbove (basisSet e (belowValCode d e (n, i))) := by
  rw [basisSet_belowValCode]
  exact bddAbove_snd_belowSet (consistent_normPairCode d e n) (d.enum i)

/-- **The index of the join the enumerated function takes at `dᵢ`.** -/
noncomputable def joinBelow (n i : ℕ) : ℕ := joinIdx e (belowValCode d e (n, i))

omit [BoundedComplete α] in
theorem enum_joinBelow (n i : ℕ) :
    e.enum (joinBelow d e n i)
      = sSup (Prod.snd '' belowSet (Effective.pairsOf d e
          (Denumerable.ofNat (Finset (ℕ × ℕ)) (normPairCode d e n))) (d.enum i)) := by
  have hb := bddAbove_basisSet_belowValCode d e n i
  have h1 := isLUB_enum_joinIdx (d := e) (n := belowValCode d e (n, i)) hb
  rw [basisSet_belowValCode] at h1 hb
  exact h1.unique (isLUB_sSup_of_bddAbove hb)

omit [BoundedComplete α] in
/-- **The order test on the enumeration, entirely between basis indices.** -/
theorem consistentEnum_le_iff_index (m n : ℕ) :
    consistentEnum d e m ≤ consistentEnum d e n ↔
      ∀ q ∈ Denumerable.ofNat (Finset (ℕ × ℕ)) (normPairCode d e m),
        e.enum q.2 ≤ e.enum (joinBelow d e n q.1) := by
  rw [consistentEnum_eq_ofPairs d e m, consistentEnum_eq_ofPairs d e n,
    ofPairs_le_iff (finite_pairsOf d e _) (pairsOf_subset_compacts d e _)
      (consistent_normPairCode d e m)]
  constructor
  · intro h q hq
    have hq' := h (d.enum q.1, e.enum q.2) ⟨q, Finset.mem_coe.mpr hq, rfl⟩
    rw [ofPairs_apply (finite_pairsOf d e _) (pairsOf_subset_compacts d e _)
      (consistent_normPairCode d e n)] at hq'
    rw [enum_joinBelow]
    exact hq'
  · rintro h _ ⟨q, hq, rfl⟩
    rw [ofPairs_apply (finite_pairsOf d e _) (pairsOf_subset_compacts d e _)
      (consistent_normPairCode d e n), ← enum_joinBelow]
    exact h q (Finset.mem_coe.mp hq)

theorem computable_belowValCode (hd : IsRecursive d) (he : IsRecursive e) :
    Computable (belowValCode d e) := by
  classical
  have hnorm : Computable (normPairCode d e) := computable_normPairCode d e hd he
  have hinner : ComputablePred fun r : ((ℕ × ℕ) × ℕ) × (ℕ × ℕ) =>
      d.enum r.2.1 ≤ d.enum r.1.1.2 ∧ r.2.2 = r.1.2 := by
    refine computablePred_and ?_ ?_
    · exact computablePred_comp hd.1
        (Computable.pair (Computable.fst.comp Computable.snd)
          (Computable.snd.comp (Computable.fst.comp Computable.fst)))
    · exact (PrimrecRel.comp Primrec.eq (Primrec.snd.comp Primrec.snd)
        (Primrec.snd.comp Primrec.fst)).computablePred
  have hdecl : Computable fun r : (ℕ × ℕ) × ℕ =>
      decodeList (ℕ × ℕ) (normPairCode d e r.1.1) :=
    (primrec_decodeList_pair.to_comp).comp (hnorm.comp (Computable.fst.comp Computable.fst))
  have hmemb : ComputablePred fun r : (ℕ × ℕ) × ℕ => BelowVal d e r.1 r.2 := by
    refine (computablePred_exists_mem_list hdecl
      (R := fun (r : (ℕ × ℕ) × ℕ) (q : ℕ × ℕ) => d.enum q.1 ≤ d.enum r.1.2 ∧ q.2 = r.2)
      hinner).of_eq fun r => ?_
    constructor
    · rintro ⟨q, hq, h⟩
      exact ⟨q, mem_decodeList.mp hq, h⟩
    · rintro ⟨q, hq, h⟩
      exact ⟨q, mem_decodeList.mpr hq, h⟩
  have hmapsnd : Primrec fun l : List (ℕ × ℕ) => l.map Prod.snd :=
    Primrec.list_map Primrec.id (Primrec.to₂ (Primrec.snd.comp Primrec.snd))
  have hcand : Computable (belowValCand d e) :=
    hmapsnd.to_comp.comp ((primrec_decodeList_pair.to_comp).comp (hnorm.comp Computable.fst))
  exact computable_setCode primrec_idxList (fun _ _ => mem_ofNat_finset_nat_iff.symm)
    hmemb hcand (exists_belowValCodeAt d e)

/-- **Obligation 1, discharged.** The ordering on `R47.Agent2.scottHomC d e` is
decided by a total recursive function whenever the orderings and finite normal
subposets of `d` and of `e` are. -/
theorem recursiveLE_scottHomC (hd : IsRecursive d) (he : IsRecursive e) :
    RecursiveLE (scottHomC d e) := by
  classical
  have hnorm : Computable (normPairCode d e) := computable_normPairCode d e hd he
  have hjb : Computable fun r : (ℕ × ℕ) × (ℕ × ℕ) => joinBelow d e r.1.2 r.2.1 :=
    (computable_joinIdx he).comp
      ((computable_belowValCode d e hd he).comp
        (Computable.pair (Computable.snd.comp Computable.fst)
          (Computable.fst.comp Computable.snd)))
  have hR : ComputablePred fun r : (ℕ × ℕ) × (ℕ × ℕ) =>
      e.enum r.2.2 ≤ e.enum (joinBelow d e r.1.2 r.2.1) :=
    computablePred_comp he.1 (Computable.pair (Computable.snd.comp Computable.snd) hjb)
  have hmain : ComputablePred fun p : ℕ × ℕ =>
      ∀ q ∈ decodeList (ℕ × ℕ) (normPairCode d e p.1),
        e.enum q.2 ≤ e.enum (joinBelow d e p.2 q.1) :=
    computablePred_forall_mem_list
      ((primrec_decodeList_pair.to_comp).comp (hnorm.comp Computable.fst)) hR
  unfold RecursiveLE
  refine hmain.of_eq fun p => ?_
  show (∀ q ∈ decodeList (ℕ × ℕ) (normPairCode d e p.1),
      e.enum q.2 ≤ e.enum (joinBelow d e p.2 q.1)) ↔
    consistentEnum d e p.1 ≤ consistentEnum d e p.2
  rw [consistentEnum_le_iff_index]
  constructor
  · exact fun h q hq => h q (mem_decodeList.mpr hq)
  · exact fun h q hq => h q (mem_decodeList.mp hq)

end Order

/-! ## 7. Obligation 2: `Effective.RecursiveNormal (scottHomC d e)`

`Effective/FunctionSpace.lean`'s item 4 records what is needed: a
characterization of `IsNormalIn` for a finite set of compact functions in terms
of `d` and `e`, "needing mub-closure in `K(D → E)`", and notes that "a mub of
step functions is a bounded join". That is exactly the shape below: two values of
the enumeration are bounded above precisely when the union of their index sets
is consistent, and their join is then the enumeration's value at a code for that
union. Nothing here needs `BoundedComplete (ScottHom α β)` — the mub is
exhibited, not obtained from an instance. -/

section Normal

variable {α β : Type*} [CompletePartialOrder α] [Domain α] [BoundedComplete α]
  [CompletePartialOrder β] [Domain β] [BoundedComplete β]
variable (d : EffectivePresentation α) (e : EffectivePresentation β)

omit [Domain α] [BoundedComplete α] [Domain β] [BoundedComplete β] in
/-- **A function dominating every value of `P` at the matching source dominates
every step function `P` names.** The `mpr` half of `R47.Agent2.ofPairs_le_iff`
without its consistency hypothesis — which is what lets consistency be *derived*
rather than assumed. -/
theorem forall_le_of_forall_le_apply {P : Set (α × β)} {g : ScottHom α β}
    (h : ∀ p ∈ P, p.2 ≤ g p.1) : ∀ f ∈ ScottHom.stepsOf P, f ≤ g := by
  rintro f ⟨p, hp, hstep⟩ x
  show f x ≤ g x
  rw [show f x = ScottHom.stepFun p.1 p.2 x from congrFun hstep.2.2 x]
  by_cases hle : p.1 ≤ x
  · rw [ScottHom.stepFun_of_le hle]
    exact (h p hp).trans (g.monotone hle)
  · rw [ScottHom.stepFun_of_not_le hle]
    exact bot_le

omit [Domain α] [BoundedComplete α] [Domain β] in
/-- Each value of a consistent index set sits below the join at its own source. -/
theorem le_ofPairs_apply {P : Set (α × β)} (hP : P.Finite)
    (hcptP : P ⊆ compacts α ×ˢ compacts β) (hc : Consistent P) {p : α × β} (hp : p ∈ P) :
    p.2 ≤ ScottHom.ofPairs P p.1 :=
  (ScottHom.step_le_iff (hcptP hp).1).mp
    ((isLUB_stepsOf_ofPairs hP hcptP hc).1
      ⟨p, hp, ⟨(hcptP hp).1, (hcptP hp).2, rfl⟩⟩)

/-! ### The union of two index sets -/

/-- Membership in the union of the two normalized index sets. -/
def UnionPair (p : ℕ × ℕ) (q : ℕ × ℕ) : Prop :=
  q ∈ Denumerable.ofNat (Finset (ℕ × ℕ)) (normPairCode d e p.1) ∨
    q ∈ Denumerable.ofNat (Finset (ℕ × ℕ)) (normPairCode d e p.2)

noncomputable def unionPairCand (p : ℕ × ℕ) : List (ℕ × ℕ) :=
  decodeList (ℕ × ℕ) (normPairCode d e p.1) ++ decodeList (ℕ × ℕ) (normPairCode d e p.2)

omit [BoundedComplete α] [BoundedComplete β] in
theorem unionPair_mem_cand (p q : ℕ × ℕ) : UnionPair d e p q → q ∈ unionPairCand d e p := by
  rintro (h | h)
  · exact List.mem_append_left _ (mem_decodeList.mpr h)
  · exact List.mem_append_right _ (mem_decodeList.mpr h)

omit [BoundedComplete α] [BoundedComplete β] in
theorem exists_unionPairCodeAt (p : ℕ × ℕ) :
    ∃ m, SetCodeAt (Denumerable.ofNat (Finset (ℕ × ℕ))) (UnionPair d e)
      (unionPairCand d e) p m :=
  exists_setCodeAt surjective_ofNat_finset_pair _ _ p

/-- A code for the union of the two normalized index sets. -/
noncomputable def unionPairCode : ℕ × ℕ → ℕ :=
  setCode (Denumerable.ofNat (Finset (ℕ × ℕ))) (UnionPair d e) (unionPairCand d e)
    (exists_unionPairCodeAt d e)

omit [BoundedComplete α] [BoundedComplete β] in
theorem mem_ofNat_unionPairCode (p q : ℕ × ℕ) :
    q ∈ Denumerable.ofNat (Finset (ℕ × ℕ)) (unionPairCode d e p) ↔ UnionPair d e p q :=
  mem_ofn_setCode (exists_unionPairCodeAt d e) (unionPair_mem_cand d e) p q

omit [BoundedComplete α] [BoundedComplete β] in
theorem pairsOf_unionPairCode (a b : ℕ) :
    Effective.pairsOf d e (Denumerable.ofNat (Finset (ℕ × ℕ)) (unionPairCode d e (a, b)))
      = Effective.pairsOf d e (Denumerable.ofNat (Finset (ℕ × ℕ)) (normPairCode d e a))
        ∪ Effective.pairsOf d e (Denumerable.ofNat (Finset (ℕ × ℕ)) (normPairCode d e b)) := by
  ext s
  constructor
  · rintro ⟨q, hq, rfl⟩
    rcases (mem_ofNat_unionPairCode d e (a, b) q).mp (Finset.mem_coe.mp hq) with h | h
    · exact Or.inl ⟨q, Finset.mem_coe.mpr h, rfl⟩
    · exact Or.inr ⟨q, Finset.mem_coe.mpr h, rfl⟩
  · rintro (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩)
    · exact ⟨q, Finset.mem_coe.mpr ((mem_ofNat_unionPairCode d e (a, b) q).mpr
        (Or.inl (Finset.mem_coe.mp hq))), rfl⟩
    · exact ⟨q, Finset.mem_coe.mpr ((mem_ofNat_unionPairCode d e (a, b) q).mpr
        (Or.inr (Finset.mem_coe.mp hq))), rfl⟩

omit [BoundedComplete α] in
/-- **Two values of the enumeration are bounded above only if the union of their
index sets is consistent.** This is the half that makes the normality test
decidable: the boundedness question in `K(D → E)` becomes `Consistent`, which
section 5 decides. -/
theorem consistent_unionPairCode_of_le {a b : ℕ} {x : ScottHom α β}
    (ha : consistentEnum d e a ≤ x) (hb : consistentEnum d e b ≤ x) :
    Consistent (Effective.pairsOf d e
      (Denumerable.ofNat (Finset (ℕ × ℕ)) (unionPairCode d e (a, b)))) := by
  have hall : ∀ p ∈ Effective.pairsOf d e
      (Denumerable.ofNat (Finset (ℕ × ℕ)) (unionPairCode d e (a, b))), p.2 ≤ x p.1 := by
    rw [pairsOf_unionPairCode]
    rintro p (hp | hp)
    · exact (ofPairs_le_iff (finite_pairsOf d e _) (pairsOf_subset_compacts d e _)
        (consistent_normPairCode d e a)).mp
        ((consistentEnum_eq_ofPairs d e a) ▸ ha) p hp
    · exact (ofPairs_le_iff (finite_pairsOf d e _) (pairsOf_subset_compacts d e _)
        (consistent_normPairCode d e b)).mp
        ((consistentEnum_eq_ofPairs d e b) ▸ hb) p hp
  exact (bddAbove_stepsOf_iff (finite_pairsOf d e _) (pairsOf_subset_compacts d e _)).mp
    ⟨x, fun f hf => forall_le_of_forall_le_apply hall f hf⟩

omit [BoundedComplete α] in
/-- **…and when it is, the enumeration's value at the union code is their least
upper bound.** The mub `Effective/FunctionSpace.lean` asks for, exhibited. -/
theorem isLUB_pair_consistentEnum {a b : ℕ}
    (hc : Consistent (Effective.pairsOf d e
      (Denumerable.ofNat (Finset (ℕ × ℕ)) (unionPairCode d e (a, b))))) :
    IsLUB ({consistentEnum d e a, consistentEnum d e b} : Set (ScottHom α β))
      (consistentEnum d e (unionPairCode d e (a, b))) := by
  classical
  have hu : consistentEnum d e (unionPairCode d e (a, b))
      = ScottHom.ofPairs (Effective.pairsOf d e
        (Denumerable.ofNat (Finset (ℕ × ℕ)) (unionPairCode d e (a, b)))) := by
    rw [consistentEnum, if_pos hc]
  have hsubA : Effective.pairsOf d e (Denumerable.ofNat (Finset (ℕ × ℕ)) (normPairCode d e a))
      ⊆ Effective.pairsOf d e
        (Denumerable.ofNat (Finset (ℕ × ℕ)) (unionPairCode d e (a, b))) := by
    rw [pairsOf_unionPairCode]; exact Set.subset_union_left
  have hsubB : Effective.pairsOf d e (Denumerable.ofNat (Finset (ℕ × ℕ)) (normPairCode d e b))
      ⊆ Effective.pairsOf d e
        (Denumerable.ofNat (Finset (ℕ × ℕ)) (unionPairCode d e (a, b))) := by
    rw [pairsOf_unionPairCode]; exact Set.subset_union_right
  constructor
  · rintro f (rfl | rfl)
    · rw [consistentEnum_eq_ofPairs d e a, hu]
      exact (ofPairs_le_iff (finite_pairsOf d e _) (pairsOf_subset_compacts d e _)
        (consistent_normPairCode d e a)).mpr fun p hp =>
          le_ofPairs_apply (finite_pairsOf d e _) (pairsOf_subset_compacts d e _) hc (hsubA hp)
    · rw [consistentEnum_eq_ofPairs d e b, hu]
      exact (ofPairs_le_iff (finite_pairsOf d e _) (pairsOf_subset_compacts d e _)
        (consistent_normPairCode d e b)).mpr fun p hp =>
          le_ofPairs_apply (finite_pairsOf d e _) (pairsOf_subset_compacts d e _) hc (hsubB hp)
  · intro g hg
    have hga : consistentEnum d e a ≤ g := hg (Set.mem_insert _ _)
    have hgb : consistentEnum d e b ≤ g := hg (Set.mem_insert_of_mem _ rfl)
    rw [hu]
    refine (ofPairs_le_iff (finite_pairsOf d e _) (pairsOf_subset_compacts d e _) hc).mpr ?_
    rw [pairsOf_unionPairCode]
    rintro p (hp | hp)
    · exact (ofPairs_le_iff (finite_pairsOf d e _) (pairsOf_subset_compacts d e _)
        (consistent_normPairCode d e a)).mp
        ((consistentEnum_eq_ofPairs d e a) ▸ hga) p hp
    · exact (ofPairs_le_iff (finite_pairsOf d e _) (pairsOf_subset_compacts d e _)
        (consistent_normPairCode d e b)).mp
        ((consistentEnum_eq_ofPairs d e b) ▸ hgb) p hp

omit [BoundedComplete α] [BoundedComplete β] in
theorem consistentEnum_emptyPairCode :
    consistentEnum d e emptyPairCode = (⊥ : ScottHom α β) := by
  classical
  have hc : Consistent (Effective.pairsOf d e
      (Denumerable.ofNat (Finset (ℕ × ℕ)) emptyPairCode)) := by
    rw [ofNat_emptyPairCode, R49.Agent3.pairsOf_empty d e]
    exact consistent_empty
  rw [consistentEnum, if_pos hc, ofNat_emptyPairCode, R49.Agent3.pairsOf_empty d e,
    R49.Agent3.ofPairs_empty]

omit [BoundedComplete α] in
/-- **Normality of a finite set of enumerated functions, as a finite condition on
the index sets.** `R47.Agent2.isNormalIn_compacts_iff` is the general statement
and carries `[BoundedComplete γ]` at `γ = D → E`; this one does not, because the
join of two values is *named* — `consistentEnum` at the union code — rather than
obtained from `sSup`. -/
theorem isNormalIn_basisSet_iff (n : ℕ) :
    basisSet (scottHomC d e) n ◁ compacts (ScottHom α β) ↔
      (∃ a ∈ Denumerable.ofNat (Finset ℕ) n,
          consistentEnum d e a ≤ consistentEnum d e emptyPairCode) ∧
        ∀ a ∈ Denumerable.ofNat (Finset ℕ) n, ∀ b ∈ Denumerable.ofNat (Finset ℕ) n,
          Consistent (Effective.pairsOf d e
              (Denumerable.ofNat (Finset (ℕ × ℕ)) (unionPairCode d e (a, b)))) →
            ∃ c ∈ Denumerable.ofNat (Finset ℕ) n,
              consistentEnum d e (unionPairCode d e (a, b)) ≤ consistentEnum d e c ∧
                consistentEnum d e c ≤ consistentEnum d e (unionPairCode d e (a, b)) := by
  classical
  constructor
  · intro hN
    refine ⟨?_, ?_⟩
    · obtain ⟨a, ha, hEq⟩ := hN.bot_mem (isCompactElement_bot (α := ScottHom α β))
      refine ⟨a, Finset.mem_coe.mp ha, ?_⟩
      rw [consistentEnum_emptyPairCode]
      exact le_of_eq hEq
    · intro a ha b hb hc
      have hlub := isLUB_pair_consistentEnum d e hc
      have hwc : IsCompactElement (consistentEnum d e (unionPairCode d e (a, b))) :=
        consistentEnum_isCompactElement d e _
      obtain ⟨v, ⟨hvN, hvw⟩, h1, h2⟩ :=
        hN.directedOn hwc (consistentEnum d e a)
          ⟨mem_basisSet (d := scottHomC d e) ha,
            Set.mem_Iic.mpr (hlub.1 (Set.mem_insert _ _))⟩
          (consistentEnum d e b)
          ⟨mem_basisSet (d := scottHomC d e) hb,
            Set.mem_Iic.mpr (hlub.1 (Set.mem_insert_of_mem _ rfl))⟩
      obtain ⟨c, hcmem, rfl⟩ := hvN
      refine ⟨c, Finset.mem_coe.mp hcmem, ?_, Set.mem_Iic.mp hvw⟩
      refine hlub.2 ?_
      rintro f (rfl | rfl)
      · exact h1
      · exact h2
  · rintro ⟨⟨a₀, ha₀, hbot⟩, hjoin⟩
    have hbot' : consistentEnum d e a₀ = (⊥ : ScottHom α β) :=
      le_bot_iff.mp (by rwa [consistentEnum_emptyPairCode] at hbot)
    refine ⟨?_, fun x _ => ⟨?_, ?_⟩⟩
    · rintro _ ⟨i, _, rfl⟩
      exact consistentEnum_isCompactElement d e i
    · exact ⟨consistentEnum d e a₀, mem_basisSet (d := scottHomC d e) ha₀,
        Set.mem_Iic.mpr (by rw [hbot']; exact bot_le)⟩
    · rintro _ ⟨⟨a, ha, rfl⟩, hax⟩ _ ⟨⟨b, hb, rfl⟩, hbx⟩
      have hax' : consistentEnum d e a ≤ x := Set.mem_Iic.mp hax
      have hbx' : consistentEnum d e b ≤ x := Set.mem_Iic.mp hbx
      have hc := consistent_unionPairCode_of_le d e hax' hbx'
      obtain ⟨c, hcmem, hwc, hcw⟩ :=
        hjoin a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb) hc
      have hlub := isLUB_pair_consistentEnum d e hc
      have hwx : consistentEnum d e (unionPairCode d e (a, b)) ≤ x :=
        hlub.2 (by rintro f (rfl | rfl); exacts [hax', hbx'])
      refine ⟨consistentEnum d e c, ⟨mem_basisSet (d := scottHomC d e) hcmem,
        Set.mem_Iic.mpr (hcw.trans hwx)⟩, ?_, ?_⟩
      · exact (hlub.1 (Set.mem_insert _ _)).trans hwc
      · exact (hlub.1 (Set.mem_insert_of_mem _ rfl)).trans hwc

theorem computable_unionPairCode (hd : IsRecursive d) (he : IsRecursive e) :
    Computable (unionPairCode d e) := by
  classical
  have hnorm : Computable (normPairCode d e) := computable_normPairCode d e hd he
  have hmem1 : ComputablePred fun r : (ℕ × ℕ) × (ℕ × ℕ) =>
      r.2 ∈ Denumerable.ofNat (Finset (ℕ × ℕ)) (normPairCode d e r.1.1) := by
    refine (computablePred_comp
      (PrimrecRel.comp primrecRel_mem_list Primrec.fst Primrec.snd).computablePred
      (Computable.pair
        ((primrec_decodeList_pair.to_comp).comp
          (hnorm.comp (Computable.fst.comp Computable.fst))) Computable.snd)).of_eq fun r => ?_
    exact mem_decodeList
  have hmem2 : ComputablePred fun r : (ℕ × ℕ) × (ℕ × ℕ) =>
      r.2 ∈ Denumerable.ofNat (Finset (ℕ × ℕ)) (normPairCode d e r.1.2) := by
    refine (computablePred_comp
      (PrimrecRel.comp primrecRel_mem_list Primrec.fst Primrec.snd).computablePred
      (Computable.pair
        ((primrec_decodeList_pair.to_comp).comp
          (hnorm.comp (Computable.snd.comp Computable.fst))) Computable.snd)).of_eq fun r => ?_
    exact mem_decodeList
  have happ : Primrec fun q : List (ℕ × ℕ) × List (ℕ × ℕ) => q.1 ++ q.2 :=
    Primrec₂.comp Primrec.list_append Primrec.fst Primrec.snd
  have hcand : Computable (unionPairCand d e) :=
    happ.to_comp.comp (Computable.pair
      ((primrec_decodeList_pair.to_comp).comp (hnorm.comp Computable.fst))
      ((primrec_decodeList_pair.to_comp).comp (hnorm.comp Computable.snd)))
  exact computable_setCode primrec_decodeList_pair (fun _ _ => mem_decodeList)
    (computablePred_or hmem1 hmem2) hcand (exists_unionPairCodeAt d e)

/-- Obligation 1, restated with the enumeration written out. -/
theorem computablePred_consistentEnum_le (hd : IsRecursive d) (he : IsRecursive e) :
    ComputablePred fun p : ℕ × ℕ => consistentEnum d e p.1 ≤ consistentEnum d e p.2 :=
  recursiveLE_scottHomC d e hd he

/-- The `⊥ ∈ N` conjunct of the normality test. -/
theorem computablePred_bot_mem (hd : IsRecursive d) (he : IsRecursive e) :
    ComputablePred fun n : ℕ => ∃ a ∈ Denumerable.ofNat (Finset ℕ) n,
      consistentEnum d e a ≤ consistentEnum d e emptyPairCode := by
  classical
  have hf : Computable fun q : ℕ × ℕ => (q.2, emptyPairCode) :=
    Computable.pair Computable.snd (Computable.const emptyPairCode)
  have hstep := computablePred_comp (computablePred_consistentEnum_le d e hd he) hf
  exact computablePred_exists_mem (code := fun n : ℕ => n) Computable.id
    (R := fun (_ : ℕ) (a : ℕ) => consistentEnum d e a ≤ consistentEnum d e emptyPairCode)
    hstep

/-- The innermost atom of the mub conjunct: the union code names the same
compact function as the index `c`.

`g1` and `g2` are bound before use, not written inline into `computablePred_and`:
inline, the two `ComputablePred` metavariables are solved against each other and
the elaborator unfolds `consistentEnum` looking for a match, which does not
terminate. This is an elaboration-order fact, not a mathematical one. -/
theorem computablePred_union_eq (hd : IsRecursive d) (he : IsRecursive e) :
    ComputablePred fun s : ((ℕ × ℕ) × ℕ) × ℕ =>
      consistentEnum d e (unionPairCode d e (s.1.1.2, s.1.2)) ≤ consistentEnum d e s.2 ∧
        consistentEnum d e s.2 ≤ consistentEnum d e (unionPairCode d e (s.1.1.2, s.1.2)) := by
  classical
  have hle := computablePred_consistentEnum_le d e hd he
  have hcode : Computable fun s : ((ℕ × ℕ) × ℕ) × ℕ =>
      unionPairCode d e (s.1.1.2, s.1.2) :=
    (computable_unionPairCode d e hd he).comp (Computable.pair
      (Computable.snd.comp (Computable.fst.comp Computable.fst))
      (Computable.snd.comp Computable.fst))
  have hf1 : Computable fun s : ((ℕ × ℕ) × ℕ) × ℕ =>
      (unionPairCode d e (s.1.1.2, s.1.2), s.2) := Computable.pair hcode Computable.snd
  have hf2 : Computable fun s : ((ℕ × ℕ) × ℕ) × ℕ =>
      (s.2, unionPairCode d e (s.1.1.2, s.1.2)) := Computable.pair Computable.snd hcode
  have g1 := computablePred_comp hle hf1
  have g2 := computablePred_comp hle hf2
  exact computablePred_and g1 g2

/-- The mub conjunct of the normality test. -/
theorem computablePred_mub_closed (hd : IsRecursive d) (he : IsRecursive e) :
    ComputablePred fun n : ℕ =>
      ∀ a ∈ Denumerable.ofNat (Finset ℕ) n, ∀ b ∈ Denumerable.ofNat (Finset ℕ) n,
        Consistent (Effective.pairsOf d e
            (Denumerable.ofNat (Finset (ℕ × ℕ)) (unionPairCode d e (a, b)))) →
          ∃ c ∈ Denumerable.ofNat (Finset ℕ) n,
            consistentEnum d e (unionPairCode d e (a, b)) ≤ consistentEnum d e c ∧
              consistentEnum d e c ≤ consistentEnum d e (unionPairCode d e (a, b)) := by
  classical
  have hex : ComputablePred fun r : (ℕ × ℕ) × ℕ =>
      ∃ c ∈ Denumerable.ofNat (Finset ℕ) r.1.1,
        consistentEnum d e (unionPairCode d e (r.1.2, r.2)) ≤ consistentEnum d e c ∧
          consistentEnum d e c ≤ consistentEnum d e (unionPairCode d e (r.1.2, r.2)) :=
    computablePred_exists_mem (code := fun r : (ℕ × ℕ) × ℕ => r.1.1)
      (Computable.fst.comp Computable.fst)
      (R := fun (r : (ℕ × ℕ) × ℕ) (c : ℕ) =>
        consistentEnum d e (unionPairCode d e (r.1.2, r.2)) ≤ consistentEnum d e c ∧
          consistentEnum d e c ≤ consistentEnum d e (unionPairCode d e (r.1.2, r.2)))
      (computablePred_union_eq d e hd he)
  have hcons : ComputablePred fun r : (ℕ × ℕ) × ℕ =>
      Consistent (Effective.pairsOf d e
        (Denumerable.ofNat (Finset (ℕ × ℕ)) (unionPairCode d e (r.1.2, r.2)))) :=
    have hf : Computable fun r : (ℕ × ℕ) × ℕ => unionPairCode d e (r.1.2, r.2) :=
      (computable_unionPairCode d e hd he).comp
        (Computable.pair (Computable.snd.comp Computable.fst) Computable.snd)
    computablePred_comp
      (p := fun m : ℕ =>
        Consistent (Effective.pairsOf d e (Denumerable.ofNat (Finset (ℕ × ℕ)) m)))
      (computablePred_consistent d e hd he) hf
  have hmid : ComputablePred fun p : ℕ × ℕ =>
      ∀ b ∈ Denumerable.ofNat (Finset ℕ) p.1,
        Consistent (Effective.pairsOf d e
            (Denumerable.ofNat (Finset (ℕ × ℕ)) (unionPairCode d e (p.2, b)))) →
          ∃ c ∈ Denumerable.ofNat (Finset ℕ) p.1,
            consistentEnum d e (unionPairCode d e (p.2, b)) ≤ consistentEnum d e c ∧
              consistentEnum d e c ≤ consistentEnum d e (unionPairCode d e (p.2, b)) :=
    computablePred_forall_mem (code := fun p : ℕ × ℕ => p.1) Computable.fst
      (R := fun (p : ℕ × ℕ) (b : ℕ) =>
        Consistent (Effective.pairsOf d e
            (Denumerable.ofNat (Finset (ℕ × ℕ)) (unionPairCode d e (p.2, b)))) →
          ∃ c ∈ Denumerable.ofNat (Finset ℕ) p.1,
            consistentEnum d e (unionPairCode d e (p.2, b)) ≤ consistentEnum d e c ∧
              consistentEnum d e c ≤ consistentEnum d e (unionPairCode d e (p.2, b)))
      (computablePred_imp hcons hex)
  exact computablePred_forall_mem (code := fun n : ℕ => n) Computable.id
    (R := fun (n : ℕ) (a : ℕ) =>
      ∀ b ∈ Denumerable.ofNat (Finset ℕ) n,
        Consistent (Effective.pairsOf d e
            (Denumerable.ofNat (Finset (ℕ × ℕ)) (unionPairCode d e (a, b)))) →
          ∃ c ∈ Denumerable.ofNat (Finset ℕ) n,
            consistentEnum d e (unionPairCode d e (a, b)) ≤ consistentEnum d e c ∧
              consistentEnum d e c ≤ consistentEnum d e (unionPairCode d e (a, b)))
    hmid

/-- **Obligation 2, discharged.** -/
theorem recursiveNormal_scottHomC (hd : IsRecursive d) (he : IsRecursive e) :
    RecursiveNormal (scottHomC d e) :=
  (computablePred_and (computablePred_bot_mem d e hd he)
    (computablePred_mub_closed d e hd he)).of_eq fun n =>
      (isNormalIn_basisSet_iff d e n).symm

/-- **`R49.Agent3.ScottHomCRecursive`, under the paper's own bounded completeness
of `D`.** Both conjuncts of `Effective.IsRecursive` are discharged; the extra
instance `[BoundedComplete α]` is discussed in the module docstring. -/
theorem scottHomCRecursive_of_boundedComplete : R49.Agent3.ScottHomCRecursive d e :=
  fun hd he => ⟨recursiveLE_scottHomC d e hd he, recursiveNormal_scottHomC d e hd he⟩

/-- **Theorem 7's proof sentence, at the same strengthening.**
`Effective.StepFunctionsDecidable d e` — "some step-function enumeration of
`K(D → E)` built from `d` and `e` is recursive" — follows from the residue by
`R49.Agent3.stepFunctionsDecidable_of_scottHomC`.

`Effective.Theorem7ArrowRecursive` does **not** follow: its reduction
`R47.Agent2.theorem_7_arrowRecursive_of_scottHomC` takes a hypothesis quantified
over all `α` and `β` carrying `[CompletePartialOrder] [Domain]` and
`[BoundedComplete β]`, and a hypothesis cannot acquire the extra
`[BoundedComplete α]` binder. -/
theorem stepFunctionsDecidable_of_boundedComplete : StepFunctionsDecidable d e :=
  R49.Agent3.stepFunctionsDecidable_of_scottHomC (scottHomCRecursive_of_boundedComplete d e)

end Normal

end ScottDomains.R53.Agent1
