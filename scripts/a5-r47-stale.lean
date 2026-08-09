/-
a5-r47-stale.lean — r0047 / agent5.

Confirms **by the kernel, not by reading a source file**, that three of the
sixteen `S+H` rows `PaperInventory.md` still carries are stale: their properties
now have theorems with **no `Prop` hypothesis and no added instance binder**, so
they are `S+P`.

Run with: scripts/a5-r46-probe.sh scripts/a5-r47-stale.lean
A `#check` that resolves at the stated type is the measurement; an arity above
zero would print a `→` in the type and fail the `example`s below.
-/

import ScottDomains.A5Unfinished

open ScottDomains ScottDomains.BifiniteUniversal ScottDomains.PRep

/-! ### Row 1 — §6, Theorem 18. r0040 recorded `S+H` with open steps
`JungNets.Thm137` and `JungFinite.FixedPointOfCompactDeflationIsCompact`.
Both are gone from the signature: the hypotheses are the paper's own two. -/

#check @ScottDomains.thm18

example {α : Type} [CompletePartialOrder α] [Domain α] [Domain (ScottHom α α)] :
    IsBifinite α :=
  ScottDomains.thm18

/-! ### Rows 2 and 3 — §7.3, Lemma 28's conjuncts 8 and 9, `(·)♯` and `(·)♭`.
r0040 recorded them `S+H`, open as `h_smyth` / `h_hoare` of
`Lemma28AtU.lemma28AtU_of'`. r0045's agent4 discharged both; these are arity 0. -/

example : IsPRepresentable Dyadic.U smythOp := ScottDomains.R45.Agent4.repSmythAtU
example : IsPRepresentable Dyadic.U hoareOp := ScottDomains.R45.Agent4.repHoareAtU

/-- And the whole nine-fold conjunction of Lemma 28 over `U`, with no hypothesis
at all — which is what makes conjuncts 8 and 9 `S+P` rather than reduced. -/
example : PRep.Lemma28AtU := ScottDomains.R45.Agent4.lemma28AtU

/-! ### The 12 that remain: `Thm29Normal` carries ten of them, with the
hypothesis used **exactly as stated** — no added instance binder. -/

example (h : LemThirty.Thm29Normal) :
    LemThirty.Thm29SecondAtDomains ∧
    IsPRepresentable₂ Colimit.V PRep.prodOp ∧
    IsPRepresentable₂ Colimit.V PRep.smashOp ∧
    IsPRepresentable₂ Colimit.V PRep.sepSumOp ∧
    IsPRepresentable₂ Colimit.V PRep.coalSumOp ∧
    IsPRepresentable Colimit.V PRep.liftOp ∧
    IsPRepresentable Colimit.V PRep.smythOp ∧
    IsPRepresentable Colimit.V PRep.hoareOp ∧
    IsPRepresentable Colimit.V LemThirty.plotkinOp :=
  ScottDomains.R47.Agent5.nine_props_ten_rows h

/-! ### And the two that `Thm29Normal` does not reach are blocked by a
contradictory hypothesis set, not by missing work. -/

example : ¬ (LemThirty.Thm29SecondAtDomains ∧ BoundedComplete Colimit.V) :=
  ScottDomains.R47.Agent5.not_thm29SecondAtDomains_and_boundedComplete_V
