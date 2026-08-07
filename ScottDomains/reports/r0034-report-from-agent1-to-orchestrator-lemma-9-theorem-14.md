---
round: r0034
from: agent1
to: orchestrator
subject: lemma-9-theorem-14
date: 2026-0807-07:35
started: 2026-0806-22:47
finished: 2026-0807-07:35
related:
  - plans/r0034-plan-from-orchestrator-to-agent1-lemma-9-theorem-14.md
  - docs/StatementRecovery.md
---

# r0034 agent1 — Lemma 9 closed, Theorem 14 still open

## Measured outcome

| # | Metric | Before | After | Acceptance |
| -- | ------ | -----: | ----: | ---------- |
| 1 | Development-wide `sorry` | 8 | **2** | plan asked for 1 |
| 2 | `Skeleton/Recovered.lean` `sorry` | 7 | **1** | plan asked for 0 |
| 3 | Lean diagnostics (errors) | 0 | **0** | 0 |
| 4 | Warnings beyond `sorry` | 0 | **0** | 0 |
| 5 | Modules | 45 | **51** | — |
| 6 | Lines | 14048 | **15504** | — |
| 7 | Theorems | 659 | **695** | — |

Counts from `scripts/counts.sh`; build from `scripts/compile.sh -r r0034` over
the whole library, 1078 jobs, wall 7.66 s, peak 3204 MiB process-group PSS
(`ScottDomains/logs/compile-20260807-072911.agent1.log`).

The two remaining `sorry`s are `Skeleton/Recovered.lean:257` (`thm14`) and
`Skeleton/Section6.lean:197` (`thm18`, not in this stream's scope).

**Six of the plan's seven `sorry`s are retired.** The seventh, `thm14`, is not,
and section 4 below reports why — the plan's premise about it is wrong, and the
correction matters for planning the next round.

## 1. Lemma 9 — all six conjuncts proved

Each conjunct is discharged by a named order isomorphism under
`ScottDomains.Isomorphism`; `Skeleton/Recovered.lean` now reads as the statement
of the results, with each `theorem` a one-line `⟨…⟩` citing its map.

| # | Conjunct | Lean statement | Map | Module |
| -- | -------- | -------------- | --- | ------ |
| 1 | `D ⊗ E ≅ E ⊗ D` | `lem9_1` | `smashComm` | `Isomorphism/Smash.lean` |
| 2 | `(D ⊗ E) ⊗ F ≅ D ⊗ (E ⊗ F)` | `lem9_2` | `smashAssoc` | `Isomorphism/Smash.lean` |
| 3 | `(E ⊕ F) ◦→ D ≅ (E ◦→ D) × (F ◦→ D)` | `lem9_3` | `coalescedSumCopair` | `Isomorphism/Copair.lean` |
| 4 | `D ◦→ (E ◦→ F) ≅ (D ⊗ E) ◦→ F` | `lem9_4` | `smashCurry` | `Isomorphism/StrictCurry.lean` |
| 5 | `D ⊗ (E ⊕ F) ≅ (D ⊗ E) ⊕ (D ⊗ F)` | `lem9_5` | `smashDistribCoalescedSum` | `Isomorphism/Distribute.lean` |
| 6 | `D⊥ ◦→ E ≅ D → E` | `lem9_6` | `liftStrictHomIso` | `Isomorphism/Lift.lean` |

Six new modules, 65 new declarations, 1506 inserted lines against `main`:

| # | Module | Lines | Declarations | What it contains |
| -- | ------ | ----: | -----------: | ---------------- |
| 1 | `Isomorphism/Smash.lean` | 112 | 6 | commutativity and associativity of `⊗` |
| 2 | `Isomorphism/Lift.lean` | 151 | 6 | the lift adjunction, `up` and `(·)†` |
| 3 | `Isomorphism/Copair.lean` | 490 | 21 | the two injections of `⊕` and copairing |
| 4 | `Isomorphism/StrictCurry.lean` | 322 | 16 | `smashVal`, `smashPair`, strict curry/apply |
| 5 | `Isomorphism/Distribute.lean` | 211 | 7 | `⊗` distributes over `⊕` |
| 6 | `Isomorphism/Counterexample.lean` | 162 | 9 | the two refutations (section 3) |

### Where the proofs actually spend effort

Items 1, 2 and 5 need no continuity argument at all: `Smash` and `CoalescedSum`
are both `WithBot` of a base, so each law is an isomorphism of bases transported
by `OrderIso.withBotCongr`, and `≃o` between cpos preserves every least upper
bound already (the reading `Product.lean` fixes for the paper's `≅`). The base
isomorphisms are `WithBot.unbot` computations: `unbot ↑a h = a` by `rfl`
discharges `right_inv`, `WithBot.coe_unbot` discharges `left_inv`, and
`WithBot.unbot_le_unbot_iff` discharges the order.

Items 3, 4 and 6 are function-space laws and carry real continuity obligations.
Three arguments do the work.

1. `scottContinuous_sumInlFun` (item 3): an upper bound of a set of injected
   non-bottom elements is not the adjoined bottom, so it is a coercion `↑r`, and
   `r` lies on the injected side because `Sum`'s order relates only same-side
   elements. Its component is then an upper bound downstairs.
2. `scottContinuous_smashPair` (item 4): on a directed set whose least upper
   bound has both coordinates non-`⊥`, **some member already has both
   coordinates non-`⊥`**. This is not immediate — one member may be `(x, ⊥)` and
   another `(⊥, y)` — and it is the one place directedness is spent: take a
   member with non-`⊥` first coordinate (one exists, else `(⊥, c.2)` would bound
   the set), one with non-`⊥` second coordinate, and the member above both.
3. `scottContinuous_liftExtendFun` (item 6): a directed set whose least upper
   bound is a coercion has nonempty `liftBase`, because an empty base would make
   `⊥` an upper bound and contradict `WithBot.not_coe_le_bot`. That nonemptiness
   is what lets `g`'s own continuity be applied.

Item 4 re-proves nothing about joint versus separate continuity: it factors
through `ScottHom.curry` / `ScottHom.uncurry` over `D × E` (r0021,
`Currying.lean`) using `smashVal : D ⊗ E → D × E` and
`smashPair : D × E → D ⊗ E` as transport maps. The only subtype bookkeeping is
two lemmas — `isLUB_strictHom_of_isLUB_val` and `scottContinuous_subtypeVal`.

### Axiom audit

`scripts/axioms.sh` over the six conjuncts and the two refutations:

```
'ScottDomains.Recovered.lem9_1' depends on axioms: [propext, Quot.sound]
'ScottDomains.Recovered.lem9_2' … [propext, Classical.choice, Quot.sound]
'ScottDomains.Recovered.lem9_3' … [propext, Classical.choice, Quot.sound]
'ScottDomains.Recovered.lem9_4' … [propext, Classical.choice, Quot.sound]
'ScottDomains.Recovered.lem9_5' … [propext, Classical.choice, Quot.sound]
'ScottDomains.Recovered.lem9_6' … [propext, Classical.choice, Quot.sound]
'ScottDomains.Isomorphism.lem9_3_printed_false' … [propext, Classical.choice, Quot.sound]
'ScottDomains.Isomorphism.lem9_5_printed_false' … [propext, Classical.choice, Quot.sound]
```

**No `sorryAx` anywhere.** All eight are kernel-checked. `Classical.choice`
enters through `Smash`'s and `ScottHom`'s `sSup`, which are `dite`-defined, as
those modules' docstrings already record; `lem9_1` needs no `sSup` at all and so
depends on only two axioms.

## 2. Naming and collision avoidance

Every new declaration is under `ScottDomains.Isomorphism`, per the plan's rule 1.
No declaration outside `Skeleton/Recovered.lean` was edited, and inside it only
the seven `sorry` bodies, the import list, and two docstrings changed. All file
edits used `Write`/`Edit`; no heredoc, no `python3 -`, no `sed -i`.

## 3. Items 3 and 5 refuted under the kernel

`Isomorphism/Counterexample.lean` states both printed forms as negations and
proves them, per the `lem10_smash` precedent and open decision 2 of the r0033
restart plan.

| # | Theorem | Statement refuted | Witness |
| -- | ------- | ----------------- | ------- |
| 1 | `lem9_3_printed_false` | `(E ⊕ F) ◦→ D ≅ (E ◦→ D) × (E ◦→ F)` | `D = PUnit`, `E = F = Prop` |
| 2 | `lem9_5_printed_false` | `D ⊗ (E ⊕ F) ≅ (D ⊗ E) ⊕ (D ⊗ E)` | `D = Prop`, `E = PUnit`, `F = Prop` |

**These are not the witnesses `docs/StatementRecovery.md` names, and the change
is deliberate.** The prose separates the two sides by cardinality on
`D = E = Prop`, `F = Prop × Prop` (item 3: `10` versus `8`; item 5: `5` versus
`3`). Counting the elements of a strict function space under the kernel requires
`Fintype` instances for `WithBot` of a subtype of `Prop × Prop` and an
enumeration of the strict monotone maps — a large obligation that proves more
than is needed. The witnesses above separate the two sides by the coarsest
invariant an order isomorphism must preserve, **one element versus more than
one**, which `Equiv.subsingleton` discharges in a step. `PUnit` is the sharp
witness because it is the cpo with `⊥ = ⊤`: it collapses the smash product
(`Prop ⊗ PUnit` has one element) and empties a summand of the coalesced sum
(`PUnit ∖ {⊥}` is empty), which is exactly what a right-hand side naming `E`
where the corrected form names `F` fails to track.

Each witness is chosen so the **corrected** law is not refuted by it — for item 3
the corrected right side `StrictHom Prop PUnit × StrictHom Prop PUnit` has one
element, matching its left side; for item 5 the corrected right side
`(Prop ⊗ PUnit) ⊕ (Prop ⊗ Prop)` has two, matching its left side. The separation
is therefore specific to the misprint, not an artifact of degenerate domains.
Both facts are automatic, since `lem9_3` and `lem9_5` are proved for all cpos.

The docstrings name the witness, give the element counts, and cross-reference
`docs/StatementRecovery.md`. I did not edit `docs/StatementRecovery.md` — its
cardinality argument remains correct, and changing another agent's evidence file
is outside this stream.

## 4. Theorem 14 — not closed, and the plan's premise is wrong

The plan states: "The obstacle is definitional, not mathematical.
`Bifinite.lean` *defines* `IsBifinite` as the paper's condition 2, which would
make the theorem `P ↔ P`. `IsBifiniteViaProjections` supplies condition 1 …
`thm14` is the equivalence between the two."

The first sentence is the part that does not hold. Supplying condition 1 removes
the `P ↔ P` degeneracy, but what remains is **Plotkin's characterization of the
SFP objects**, and neither direction is a rearrangement of the other's data. I
recorded the four measured gaps in `thm14`'s own docstring so the next round has
them in the file; in brief:

1. **The `Fp(D)` machinery cannot serve the forward direction.** Every result in
   `FinitaryProjectionPoset.lean`'s `FpLattice` section — `toFp`,
   `Fp.le_iff_fpBasis_subset`, `isCompactElement_toFp_of_finite`,
   `isLUB_compactsBelow_fp`, `Fp.isCompactlyGenerated` — is stated under
   `variable [Domain α]` (line 556). `Domain α` is exactly what the forward
   direction must conclude, so none of it is in scope there.
2. **Finite basis and finite image are different conditions.** `Fp(D)`'s
   compactness results speak of `(fpBasis q).Finite`, i.e. `range q ∩ K(D)`
   finite; `finiteImageProjections` asks for `(Set.range ⇑q).Finite`. Bridging
   them needs `Set.range ⇑(toFp hN) = N` for finite normal `N` — that a finite
   normal subposet is closed under the directed suprema its own projection can
   form. No lemma in the development states this.
3. **`IsLUB` does not transfer from `↥(Fp α)` to `ScottHom α α` for free.** The
   two orders agree, but an upper bound of `M` in `ScottHom α α` need not be a
   finitary projection, so leastness in the subtype is strictly weaker than the
   `IsLUB … ScottHom.id` the definition asks for. Discharging the stronger form
   is a second appeal to approximation, not a coercion.
4. **Two finite-combinatorial lemmas are missing**: a nonempty finite directed
   set contains its own greatest element (this is what makes each element of a
   finite image compact), and a finite subset of a directed set has an upper
   bound inside the set (this produces the single projection whose image
   contains a given finite set of compacts, hence the Plotkin witness).

Given item 4, the forward direction is otherwise routine and I estimate it at
150–250 lines: each `p ∈ M` has compact image; `{p x | p ∈ M}` is a directed set
of compacts with least upper bound `x`, which gives `IsAlgebraic`;
`K(D) ⊆ ⋃_{p ∈ M} range p` gives `countable_compacts` as a countable union of
finite sets; and a single `p` fixing a finite set of compacts gives the Plotkin
order through `IsFinitaryProjection.isNormalIn_compacts`. The converse is where
gaps 1–3 bite, and I do not have a line estimate for it that I would defend.

I stopped rather than land a half-proof: a proved forward direction still leaves
the `sorry` in place, so it would not move metric 1 while adding review burden.
**Recommendation: Theorem 14 is its own round**, with gap 2 (`range (toFp hN) = N`
for finite `N`) scheduled first, since gaps 1 and 3 both route through it.

## 5. Deviations from the plan

| # | Plan said | What I did | Why |
| -- | --------- | ---------- | --- |
| 1 | Refute items 3 and 5 with `D = E = Prop`, `F = Prop × Prop`, by cardinality | Refuted with `PUnit`-based witnesses, by a one-element-versus-more invariant | The cardinality route needs `Fintype` instances and an enumeration of strict monotone maps; the invariant route is one `Equiv.subsingleton` step. Section 3 gives the full argument, including that the corrected laws survive both witnesses. |
| 2 | Development-wide `sorry` 8 → 1 | 8 → 2 | `thm14` not closed; section 4. |
| 3 | Put the negations in `Skeleton/Recovered.lean` (implied by "appear as") | Put them in `Isomorphism/Counterexample.lean`, cited from `Recovered.lean`'s docstrings | Rule 1 requires every new declaration under `ScottDomains.Isomorphism`; `Recovered.lean`'s namespace is `ScottDomains.Recovered`. Keeping the negations in the plan's namespace is the collision-safe reading. |

## 6. Commits on branch `agent1`

| # | SHA | Contents |
| -- | --- | -------- |
| 1 | `ef49056` | five isomorphism modules (9.1, 9.2, 9.3, 9.5, 9.6); 9.4 written, not yet built |
| 2 | `a0f068d` | Lemma 9 closed — all six conjuncts wired into `Recovered.lean`, items 3 and 5 refuted |
| 3 | `3db1d21` | `thm14`'s four measured gaps recorded in its docstring |

Not pushed, per the agent workflow; the push step's "no tracking information" is
the expected outcome. `main` is unmodified.
