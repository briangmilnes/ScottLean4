import ScottDomains.Powerdomain.BoundedComplete
import ScottDomains.ContinuousAlgebra

/-!
# r0038 audit evidence: the five duplicate pairs in `Audit.Powerdomains`

Round r0038 classified all 201 `theorem`/`lemma` declarations of `IdealCompletion`,
`Powerdomain/{Hoare,Smyth,Plotkin,BoundedComplete,Universal}` and
`ContinuousAlgebra`. Five of them state something another declaration already
states. "Looks the same" is not evidence, so each pair is discharged here by
`rfl` — the two proof terms are *definitionally equal*, which forces their types
equal, which is the strongest form the claim can take.

Nothing in the development imports this module and nothing should: it adds no
mathematics. It exists so the duplication claim in
`reports/r0038-report-from-agent4-to-orchestrator-audit-powerdomains.md` is
kernel-checked rather than asserted, in the way r0028's shipped duplicate pair
was invisible to `lake build` until an axiom audit imported both halves.

The five pairs, and why each is a duplicate rather than a specialization worth
keeping:

| # | declaration | already stated by | citers of the duplicate |
| - | ----------- | ----------------- | ----------------------- |
| 1 | `Hoare.isCompactElement_iff` | `IdealCompletion.isCompactElement_iff_exists_eq_principal` at `A := Hoare.Pf K(D)` | none |
| 2 | `Plotkin.isCompactElement_iff` | the same, at `A := Plotkin.FinCompacts D` | none |
| 3 | `Plotkin.compacts_eq_range_principal` | `IdealCompletion.compacts_eq_range_principal` at `A := Plotkin.FinCompacts D` | none |
| 4 | `Smyth.compacts_eq_range_principal` | the same, at `A := Smyth.Basis D` | one — `Smyth.powerdomain_isDomain` |
| 5 | `ContinuousAlgebra.ext_principal` | `ContinuousAlgebra.idealExtend_principal` at `g := foldGen f` | none |

Rows 1–3 and 5 have no citer at all, so the general lemma serves every call site
that exists. Row 4 has exactly one citer, and it is the only one of the three
powerdomains that routes Theorem 11's second conjunct through a named
intermediate: `Hoare.thm11_hoare` and `Plotkin.isDomain` are each
`IdealCompletion.thm11` applied directly, while `Smyth.powerdomain_isDomain` is
`⟨inferInstance, compacts_eq_range_principal⟩`. Making the Smyth case match the
other two removes the intermediate.

Row 5 is the sharper one. `ext_principal`'s only consumer relationship runs the
other way: it is the sole named citer of `idealExtend_principal`, which is
`@[simp]`. Removing `ext_principal` leaves `idealExtend_principal` cited by
nothing but `simp`.
-/

namespace ScottDomains.Audit.Powerdomains

open ScottDomains ScottDomains.ContinuousAlgebra

universe u

/-- **Pair 1.** `Hoare.isCompactElement_iff` is
`IdealCompletion.isCompactElement_iff_exists_eq_principal` at
`A := Hoare.Pf ↥(compacts D)`, on the nose. -/
theorem hoare_isCompactElement_iff_eq (D : Type u) [CompletePartialOrder D]
    {I : Hoare.Powerdomain D} :
    Hoare.isCompactElement_iff D (I := I)
      = IdealCompletion.isCompactElement_iff_exists_eq_principal
          (A := Hoare.Pf ↥(compacts D)) (I := I) := rfl

/-- **Pair 2.** The same, at the Egli–Milner pre-order. -/
theorem plotkin_isCompactElement_iff_eq {D : Type u} [CompletePartialOrder D]
    {P : Plotkin.Powerdomain D} :
    Plotkin.isCompactElement_iff (P := P)
      = IdealCompletion.isCompactElement_iff_exists_eq_principal
          (A := Plotkin.FinCompacts D) (I := P) := rfl

/-- **Pair 3.** `Plotkin.compacts_eq_range_principal` is
`IdealCompletion.compacts_eq_range_principal` at `A := Plotkin.FinCompacts D`. -/
theorem plotkin_compacts_eq_range_principal_eq (D : Type u) [CompletePartialOrder D] :
    Plotkin.compacts_eq_range_principal D
      = IdealCompletion.compacts_eq_range_principal
          (A := Plotkin.FinCompacts D) := rfl

/-- **Pair 4.** The same, at `A := Smyth.Basis D`. Unlike pairs 1–3 this one has a
citer, `Smyth.powerdomain_isDomain`. -/
theorem smyth_compacts_eq_range_principal_eq {D : Type u} [CompletePartialOrder D] :
    Smyth.compacts_eq_range_principal (D := D)
      = IdealCompletion.compacts_eq_range_principal
          (A := Smyth.Basis D) := rfl

/-- **Pair 5.** `ext_principal` is `idealExtend_principal` at `g := foldGen f`.
The two are definitionally equal because `ext f` is by definition
`idealExtend (foldGen f)`; `ext_principal` adds no step. -/
theorem ext_principal_eq {D : Type u} [CompletePartialOrder D] [IsAlgebraic D]
    {A : Type u} [Preorder A] [OrderBot A] [FinSets (↥(compacts D)) A]
    {E : Type u} [CompletePartialOrder E] [Binop E] [IsSemilattice E] {f : D → E}
    (hmono : Monotone (foldGen (A := A) f)) (u : A) :
    ext_principal (A := A) (f := f) hmono u
      = idealExtend_principal (g := foldGen (A := A) f) hmono u := rfl

/-! ## The three over-strength hypotheses, also kernel-checked

`W` in the r0038 label set is a hypothesis no call site supplies. Three were
measured in this area, and the evidence is that the same conclusion elaborates
without them. Each `example` below is the declaration's own proof term at the
weakened signature.

The elaborated signature of `Hoare.Powerdomain` is
`(D : Type u) → [CompletePartialOrder D] → Type u` — it does **not** take
`[Domain D]`, contrary to the docstring of `instBoundedCompleteHoare`, which
gives that as the reason the hypothesis is there. -/

/-- `instBoundedCompleteHoare` needs no `[Domain α]`. -/
example (α : Type u) [CompletePartialOrder α] : BoundedComplete (Hoare.Powerdomain α) :=
  IdealCompletion.boundedComplete fun u v _ => PowerdomainBC.hoare_exists_isLUB_pair u v

/-- `lem13_hoare` needs neither `[Domain α]` nor `[BoundedComplete α]`. The second
is recorded in its own docstring; the first is not. -/
example (α : Type u) [CompletePartialOrder α] (S : Set (Hoare.Powerdomain α))
    (hS : BddAbove S) : ∃ I, IsLUB S I :=
  PowerdomainBC.exists_isLUB_of_bddAbove_idealCompletion
    (fun u v _ => PowerdomainBC.hoare_exists_isLUB_pair u v) hS

/-- `lem13_smyth` needs no `[Domain α]`. `[BoundedComplete α]` it genuinely
consumes, through `smyth_exists_isLUB_pair`. -/
example (α : Type u) [CompletePartialOrder α] [BoundedComplete α]
    (S : Set (Smyth.Powerdomain α)) (hS : BddAbove S) : ∃ I, IsLUB S I :=
  PowerdomainBC.exists_isLUB_of_bddAbove_idealCompletion
    (fun _ _ h => PowerdomainBC.smyth_exists_isLUB_pair h) hS

end ScottDomains.Audit.Powerdomains
