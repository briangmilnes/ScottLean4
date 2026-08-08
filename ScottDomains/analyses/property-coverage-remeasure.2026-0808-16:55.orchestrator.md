# r0043 — row 2e re-measured

`PaperInventory.md` row 2e read **"≈22, and zero of them numbered."** The 22 was
subtraction: r0040 measured 62 unstated properties, r0041 was believed to have
closed about 40, and 62 − 40 was written down.

**The measured figure is 26.** The estimate was low by 4, and the composition of
the residue is not what subtraction suggested.

## Result

Five agents re-checked each of their own r0040 `N` rows against the current tree,
assigning the r0040 label set afresh. No `.lean` file was edited by any agent.

| # | Agent | Area | `N` rows | now stated | still `N` |
| -- | ----- | ---- | -------: | ---------: | --------: |
| 1 | agent1 | §2, §3 | 24 | 14 | 10 |
| 2 | agent2 | §4 → Lemma 10 | 12 | 12 | 0 |
| 3 | agent3 | Thm 11 → §5 | 9 | 8 | 1 |
| 4 | agent4 | §6 | 4 | 2 | 2 |
| 5 | agent5 | §7 | 13 | 0 | 13 |
| | **total** | | **62** | **36** | **26** |

The 36 are not 36 `S+P`:

| # | Label | Count | Meaning |
| -- | ---- | ----: | ------- |
| 1 | `S+P` | 33 | stated as the paper states it, and proved |
| 2 | `S≠` | 2 | stated, but not the paper's statement |
| 3 | `S+H` | 1 | stated, proof open |

## The residue is concentrated, not spread

Of the 26 remaining, **13 are §7 alone** — half the residue in one section.
agent5's re-check moved nothing.

Its finding is the round's most useful negative result: for row 23,
`X ≅ N⊥ + (X → X)`, r0040's three greps returned 1/0/0 and now return 48/1/66,
because `Flat.NatBot` exists with `Domain` and `BoundedComplete` instances. So
**r0041 changed expressibility, not statedness** — the sentence became writable in
Lean for the first time and nothing writes it. Three confirming probes are zero
and the package still contains exactly two solvability theorems,
`recursiveDomain_funSpace` and `recursiveDomain_prod`.

That distinction is worth carrying: adding a carrier does not add a claim, and a
round that adds 22 modules can move a coverage number by zero.

The other 13: agent1's 10 are three missing carriers (ℝ, ℚ), two meta-claims those
block, `N⊥`'s two function spaces, and three independent order facts; agent4's 2
are a Figure 3c poset nobody has built and a step the development declares
unnecessary in its own prose; agent3's 1 is a "subset" claim without `⊆`.

## What closed

All 15 conjuncts of **Theorems 1–3, Lemmas 4–5 and Theorem 7** are now stated and
proved (agent1, with the caveat below). agent2 closed §4 outright, 12 of 12,
each declaration put through `#check @d` and `#print axioms d` against the built
`.olean` files rather than read out of a source file. agent3 closed 8 of 9 in §5,
including all three powerdomains of `N⊥` and the action of a map on each.

## Four qualifications that the count alone hides

1. **Two of agent1's `S+P` rows are vacuous.** They are proved via
   `Effective.nonempty_effectivePresentation`, which establishes that *every*
   domain has an `EffectivePresentation` — `Classical.dec` fills both
   decidability fields at no cost — so their hypotheses go unused. Row 13,
   Theorem 7's second sentence proper, is **not** one of them: it goes through
   the paper's step-function enumeration. The non-vacuous `RecursivePresentation`
   remains deliberately uninstantiated. See `docs/AxiomFootprint.md`.

2. **agent3 declined to inflate its own number.** Row 18's `⊢♮` characterization
   it ruled `S≠`, not `S+P`: `plotkin_le_iff` states the *repaired* proposition
   and `plotkin_printed_clause_one_fails` refutes the printed one at a witness.
   Entailment is not statement. This applies agent2's Lemma 9 test and r0040's
   own Theorem 16.2 precedent.

3. **The label set has no slot for an undischarged `def`.** agent1 found
   `StepFunctionsDecidable` stated and unproved but *not* a `sorry`, which is why
   the count stays 0. It was recorded `S+H` as the nearest fit. A genuinely open
   `Prop` and a `sorry` are different objects and the taxonomy conflates them.

4. **agent3 flags a modelling gap in three of its own `S+P` rows.** Rows 25–27
   state their identities at `principal`, not the paper's `{|·|}`;
   `FlatPowerdomain.lean` never mentions `unit` or `⋓`. The bridge is two lines
   from declarations already in the tree, never chained. Ruled `S+P` on r0040's
   row-15 precedent; a stricter reading gives `S≠`.

## Cross-agent corrections

**agent4 corrected agent1, and agent4 is right.** agent1 had reported that the
paper's `(T × T)♮` argument "does not transfer from the pre-order to the ideal
completion." agent4 checked the carriers rather than assuming them — `Truth =
Flat Bool`, `Plotkin.Powerdomain D` the ideal completion of Egli–Milner on finite
sets of compacts — and found the paper's inference *is* valid in the pre-order.
The one step left implicit is that a join of two compacts is compact, hence the
ideal is principal, and `not_exists_isLUB` supplies exactly that. The row is
`S+P`.

Both agents independently confirmed the `{u, u′}` typo on physical p. 30, and the
development refutes the printed reading rather than asserting it: `setU_le_setU'`
gives `u ⊑ u′`, so `{u, u′}` trivially has a least upper bound.

## Defects found in the round's own instruments

1. **r0040's row-3 grep was directionally weak** (`Set ℕ ≃o`, never `≃o Set ℕ`).
   The symmetric form finds `FlatPowerdomain.hoareOrderIso` — but that is §5.2's
   `(N⊥)♭ ≅ P N`, a different left-hand side from §7.1's `(I⊤)^N ≅ P N`. Label
   unchanged; the transcript would otherwise have read as covering both.
2. **The launch brief transposed rows 35 and 36** (agent2).
3. **`PaperInventory.md` row 554 and `PRepFun.lean:98` are now false** — both
   assert the development has no action of a map on a powerdomain. Row 29
   refutes them.
4. **`FlatPowerdomain.lean:34` names two declarations that do not exist**,
   `smyth_oneBot_eq_bot` and `smyth_bot_eq_bot`; the real one is
   `smyth_oneBot_eq_bot_eq_unit_bot`. `smyth_natBot_orderIso`'s docstring claims
   a directed-supremum clause its statement lacks.

## Orchestrator spot-check

The plan admits only "you name the declaration and confirm it exists" as `S+P`
evidence, and the failure mode is a cited name that does not elaborate — r0038
found two files asserting false things about themselves, and item 4 above is the
same defect found again.

`scripts/r0043-verify-citations.sh` extracted all 347 backticked tokens from the
five reports and tested each against the 1,720 distinct declaration names
`lean-decls.py` finds in the package. **No name cited as `S+P` evidence fails to
exist.** The 15 snake_case tokens that did not resolve are accounted for:
`op_comm`, `op_idem` and `app_lam` are class *fields* (`IsSemilattice`,
`Combinator.LambdaModel`), which the lister does not enumerate; `lam_app`,
`eta_law`, `pair_fst_snd`, `isRepresentable_comp` and `isRepresentable_const` are
cited by agents 3 and 5 as **zero-hit greps**, i.e. as evidence of absence, where
unresolved is the correct outcome; and `smyth_bot_eq_bot` /
`smyth_oneBot_eq_bot` are item 4's genuinely false names, which live in a source
docstring rather than in any report.

That check independently reproduces agent3's finding without having seen it.

## Out-of-scope improvements reported, not re-labelled

* p1's negative half is now kernel-checked
  (`convex_does_not_preserve_boundedComplete`), making that `P` row a candidate
  for `S+P` (agent4).
* Row 14 is arguably `S+P` — `Flat.exists_mem_upperBound` proves exactly the
  finite-subset directedness r0040 said nothing proved (agent3).
* **Theorem 18 moved `S+H → S+P`**, closing r0040's §5 composition gap (agent4).
* No regression: 43 of 43 r0040 declaration names still defined (agent1).

## Cheapest remaining item

`Colimit.Thm29Second`'s refutation, prose since r0037. It needs an uncountable
flat cpo and `Flat ℝ` now supplies one; r0040 could not have written it (agent5).

## Duplicate construction, found twice independently

`N⊥` is defined twice — `ScottDomains.Flat.NatBot` and a separate `inductive
ScottDomains.Kleene.NatBot` (`Kleene/Factorial.lean:55`) with its own cpo
instances and a duplicate `scottContinuous_of_monotone`. That file's docstring
says it should be replaced once the general construction lands, which happened in
the same round. agents 1 and 5 found it without seeing each other.

## Measurement discipline

Counts identical at start and end, as the plan required: **100 modules, 37,300
lines, 1,773 theorems, `sorry` 0 in 0 files**, build 1,339 jobs, 0 errors, 0
warnings. The 38 `sorry` string matches are all docstring prose.
