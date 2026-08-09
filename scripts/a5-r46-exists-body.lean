/-!
r0046 / agent5, Goal B — **the existence and signature probe** (body; the
105-module import block is prepended by `scripts/a5-r46-gen.sh`).

NOT part of the package: generated into `scripts/`, outside
`ScottDomains/ScottDomains/`, so `lake build` never sees it.

## What it decides

Two of the sweep's shapes are settled by name resolution and binder inspection
against the **built environment**, not against a source line:

**Shape 3 — "`X` does not exist" / "the development has no `X`", where `X` is a
declaration of this package.** `#check @X` resolves or it does not. r0044
measured that four of four falsified prose claims were contradicted by a
declaration in or near the same file, so this is the highest-yield shape.

**Shape 4 — "no `H` is needed" / "`H` is absent by design" / "`H` is
load-bearing", where `H` is an instance binder.** `#check @T` prints `T`'s
binders, and the claim is true exactly when `H` is (or is not) among them.
Checking the *source line* instead would be a category error: `variable`
declarations, `include`, and instance synthesis all change what a declaration
actually takes.

Every `#check` below is annotated with the sentence it decides and the expected
answer, so a future round can re-run the file and diff.
-/

open ScottDomains

/-! ## Shape 3 — intra-development absence claims

### E1 — `A3Thm29.lean:318-319`

> "The three that remain open are the powerdomain conjuncts `(·)♯`, `(·)♭`,
> `(·)♮`, **whose `PRep` schemes do not exist**"

`PRep.lean:214` and `PRep.lean:225` define `smythOp` and `hoareOp`, and
`PRep.lean:260-261` state Lemma 28's conjuncts 8 and 9 in terms of them. If both
resolve, the sentence is false for two of the three operators named. Expected:
`smythOp` and `hoareOp` resolve; `plotkinOp` does not. -/

#check @ScottDomains.PRep.smythOp
#check @ScottDomains.PRep.hoareOp
-- #check @ScottDomains.PRep.plotkinOp  -- asserted absent; uncomment to see the error

-- The Lemma 28 conjunct stated over those schemes — further evidence that the
-- schemes exist, since a `Prop` cannot be stated over a missing name.
#check @ScottDomains.PRep.Lemma28AtU

/-! ### E2 — `PRepFun.lean:655,658`

> "1. **`r ⊗ s` does not exist.** … 2. **`Domain (D ⊗ E)` does not exist.**"

Sentence 1 is followed in the same paragraph by "This section builds it", so it
states a gap the file then closes rather than a standing claim — recorded here
so the next round does not re-convict it.

Sentence 2 ends "`SmashObstruction` below names this as a `Prop`, so the gap is a
statement the kernel elaborates rather than a sentence of prose." **There is no
`SmashObstruction`**, anywhere in the package — the check below fails to resolve
it. r0044's agent7 (row 10 of its false-names table) and agent8 both recorded
this; it is still unrepaired, and `PRepFun.lean` is agent4's file this round, so
r0046/agent5 reports it rather than editing it. -/

-- #check @ScottDomains.PRepFun.SmashObstruction  -- asserted present; does not resolve
-- #check @ScottDomains.SmashObstruction          -- nor under the parent namespace

/-! ## Shape 4 — binder claims

### E3 — `ClosureProperties/SeparatedSum.lean:159`

> "**Lemma 17, `D + E`.** … No bounded completeness is needed anywhere — this is
> the operator's whole point in §6, where `E` is not assumed bounded complete."

Expected: `[Domain α] [Domain β]` and **no** `[BoundedComplete _]`. Contrast with
`lem10_separated` on the line above, which takes two. -/

#check @ScottDomains.ClosureProperties.lem17_separated
#check @ScottDomains.ClosureProperties.lem10_separated

/-! ### E4 — `MinimalUpperBounds.lean:177-179`

> "nonempty — apply completeness to `v = ∅` … **No least element is needed, and
> none is assumed.**"

Expected: no `[OrderBot _]`, no `[Bot _]`. -/

#check @ScottDomains.isNormalIn_of_isMubClosed

/-! ### E5 — `Kleene/Uniform.lean:39-41`, the confirmed necessity claim

> "strictness is used exactly once, at `n = 0`, and it is indispensable"

Expected: `hbot : h ⊥ = ⊥` present on both `map_iterate_bot` and
`map_kleeneFix_of_commutes`. The claim is confirmed at grade A in
`scripts/a5-r46-delete.lean`; this records the binder it is about. -/

#check @ScottDomains.Kleene.map_iterate_bot
#check @ScottDomains.Kleene.map_kleeneFix_of_commutes

/-! ### E6 — `Kleene/Graph.lean:38-41`, the refuted necessity claim

> "**bounded completeness of `E`** — which the paper does not mention here but
> which the argument cannot do without."

Expected: `[BoundedComplete β]` present on `sSup_recoverAt`, and
`scripts/a1-probe45.lean` (r0044/agent1, re-run in r0046) proving the same
statement without it. -/

#check @ScottDomains.Kleene.sSup_recoverAt

/-! ### E7 — `Effective/FunctionSpace.lean:299-303`, the refuted absence claim

> "The index is needed because the condition quantifies over `u : Finset ℕ` and
> Mathlib v4.32.2 has no `Primcodable (Finset ℕ)` instance, so `ComputablePred`
> cannot be asked of a predicate on `Finset ℕ` at all."

`scripts/a5-r46-mathlib.lean` synthesizes the instance and inhabits
`ComputablePred` on `Finset ℕ`. Here the `ℕ`-indexed workaround is recorded, and
the `Finset ℕ`-direct form is elaborated to show it is well-formed — which is
what "cannot be asked … at all" denies. -/

#check @ScottDomains.Effective.RecursiveNormal

/-- The predicate `RecursiveNormal` decodes, stated **directly on `Finset ℕ`**
with no `ℕ` index. If this elaborates, "cannot be asked of a predicate on
`Finset ℕ` at all" is false. -/
example {γ : Type} [CompletePartialOrder γ] [Domain γ]
    (d : EffectivePresentation γ) : Prop :=
  ComputablePred fun u : Finset ℕ => (d.enum '' (↑u : Set ℕ)) ◁ compacts γ
