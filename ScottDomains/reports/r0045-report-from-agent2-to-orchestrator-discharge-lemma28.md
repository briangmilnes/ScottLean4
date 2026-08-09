---
round: r0045
from: agent2
to: orchestrator
subject: discharge-lemma28
date: 2026-0808-21:38
started: 2026-0808-21:05
finished: 2026-0808-21:38
related:
  - plans/r0045-plan-from-orchestrator-to-orchestrator-discharge-nineteen.md
---

# r0045 — agent2: `PRep.Lemma28` and `PRep.Lemma28AtU`

New file `ScottDomains/A2Lemma28.lean`, namespace `ScottDomains.R45.Agent2`,
17 declarations, 0 `sorry`, build 0 errors / 0 warnings
(`logs/compile-20260808-213449.agent2.log`, 1340 jobs, 1.6 s incremental).
Every declaration audited by `scripts/axioms.sh`; no `sorryAx` anywhere.

Measured against the **fixed** acceptance criterion (discharged = conclusion is
the claim with *exactly* the binders the `def` itself carries; "discharged at
`<binder>`" for an added instance binder; reduction; refutation; open):

| # | Claim | Binders on its own `def` | Status |
| - | ----- | ------------------------ | ------ |
| 1 | `ScottDomains.PRep.Lemma28` | `(U : Type u) [CompletePartialOrder U]` | **refuted** at those binders (`not_forall_lemma28`), and still refuted at `[Domain U] [BoundedComplete U]` (`not_forall_lemma28_bcd`); **reduced** to one hypothesis plus two added binders (`lemma28_of_universal`) |
| 2 | `ScottDomains.PRep.Lemma28AtU` | `: Prop` (an `abbrev` for `Lemma28 Dyadic.U`; no binders) | **discharged by agent4**, not by me. My contribution is `lemma28AtU_iff`, which measures the residue as tight |

## 1. `PRep.Lemma28` is refuted, not open

I read the `def` line, not the docstring:

    def Lemma28 (U : Type u) [CompletePartialOrder U] : Prop := …

The carrier is a parameter, so a discharge-shaped theorem for this row has type
`∀ U [CompletePartialOrder U], Lemma28 U`. **That proposition is false.**

    theorem not_forall_lemma28 :
        ¬ ∀ (U : Type) (inst : CompletePartialOrder U), @PRep.Lemma28 U inst

Counterexample: `Flat Empty`, the one-point cpo. Conjunct 7 (`(·)⊥`) fails, by a
cardinality count on the p-representability square. `Fp (Flat Empty)` is nonempty
— `ScottHom.id` is a finitary projection, which needs the `Domain` on the image
that `IsFinitaryProjection` demands and that `isFinitaryProjection_of_subsingleton`
supplies. Then `im(R p)` is a subtype of a subsingleton and has one point, while
`(im p)⊥` is `WithBot` of a nonempty type and has at least two. No `≃o` relates
them.

**This is exactly the "discharged at `<binder>`" trap, and it cannot be sprung
here.** Adding instance binders does not rescue the statement:

    theorem not_forall_lemma28_bcd :
        ¬ ∀ (U : Type) (inst : CompletePartialOrder U),
            @Domain U inst → @BoundedComplete U inst → @PRep.Lemma28 U inst

`Flat Empty` is an algebraic, countably based, bounded complete cpo
(`Flat.instDomain`, `Flat.instBoundedComplete`). So no class in `Domain.lean`
closes this row, and any future proof of it must be carrying an added hypothesis
that is not a class — which the next section names.

## 2. What `pairAtU` supplies, isolated to one proposition

The orchestrator asked precisely this. The answer is a single named Prop:

    def UniversalForBCD (U : Type) [CompletePartialOrder U] : Prop :=
      ∀ (V : Type) [CompletePartialOrder V] [Domain V] [BoundedComplete V],
        ∃ (fn : ScottHom U V) (gr : ScottHom V U),
          (∀ y, fn (gr y) = y) ∧ ∀ x, gr (fn x) ≤ x

Every bounded complete domain is a projection-retract of `U`. Three theorems fix
its role:

| # | Theorem | Content |
| - | ------- | ------- |
| 1 | `universalForBCD_dyadicU` | `PRepSum.pairAtU` **is** `UniversalForBCD Dyadic.U`, transposed — one line. So this Prop is exactly what §7.3's carrier has and a generic `U` does not, and it comes from `Atomless.thm27`, Theorem 27 at the atomless dyadic-interval domain |
| 2 | `not_universalForBCD_of_subsingleton` | a subsingleton cpo is not universal: `fn ∘ gr = id` makes `gr` injective, so the three-element `Flat Bool` cannot be a retract of a one-point cpo |
| 3 | `lemma28_of_universal` | `UniversalForBCD U` (plus `[Domain U] [BoundedComplete U]` and agent4's four) proves `PRep.Lemma28 U` |

Theorems 2 and 3 together are the sharp statement: the counterexample fails at
`UniversalForBCD` **and nowhere else**. Universality is not merely sufficient in
my proof, it is the exact thing the refutation exploits.

**Is it obtainable?** Not from any hypothesis this development can state as a
class — theorem 2 rules that out, since `Flat Empty` satisfies every class and
fails universality. It is obtainable only by naming a universal carrier, which is
Theorem 27's job and is what §7.3 does. So `PRep.Lemma28` at generic `U` is not
a gap to be closed; **it is a mis-stated row.** The paper's claim is
`Lemma28 Dyadic.U`, which is the separate row `Lemma28AtU`.

### Recommended inventory change (orchestrator's call, not mine)

`PRep.Lemma28` and `PRep.Lemma28AtU` are one claim counted twice. `Lemma28` is a
schema; its only true instance in the paper is at `Dyadic.U`. I changed no `def`.
The same shape very likely recurs in agent3's cluster: `LemThirty.Lemma30 W` is a
parametric `def` with `Lemma30AtV` as its instance, written — per `LemThirty.lean:210`
— deliberately to mirror `Lemma28`/`Lemma28AtU`. Worth checking before the count
is re-derived.

## 3. `Lemma28AtU`: my measurement, and the correction to the round's framing

    theorem lemma28AtU_iff :
        PRep.Lemma28AtU ↔
          IsPRepresentable Dyadic.U PRep.smythOp ∧ IsPRepresentable Dyadic.U PRep.hoareOp

Seven of the nine conjuncts hold over `Dyadic.U` unconditionally, so
`Lemma28AtU.lemma28AtU_of'`'s two hypotheses are **necessary as well as
sufficient**. The arity-9 → arity-2 chain had bottomed out.

**On the arity-2 → arity-4 question I was set: the restructure was correct, and
the "moved the obligation" framing — including my own first draft of this report
— is wrong.** Logically the four hypotheses of `lemma28AtU_of''` are stronger
than the two (`residue_of_powerdomainMap_obligations` proves the implication one
way; `lemma28AtU_iff` shows the two are equivalent to the goal, so the four are
sufficient but not necessary), because they name one particular representing
family where `IsPRepresentable` quantifies existentially. But agent4 discharged
all four, so the named family was the right one. Isolating those four is what
made them provable. Arity is not the measurement when the propositions change;
**provability is**, and it came out in favour of the decomposition. I have
written that reading into `A2Lemma28.lean`'s module docstring rather than the
earlier one.

`PRep.Lemma28AtU` is discharged by `ScottDomains.R45.Agent4`, not by me. As a
cross-check that the generic route reproduces it, `lemma28AtU_of_universal`
re-derives `Lemma28AtU` from agent4's four via `lemma28_of_universal` at
`Dyadic.U` — confirming that **none of the seven non-powerdomain conjuncts needs
`Dyadic.U` for anything except the retraction pair.** That is the measured
justification for the claim in section 2.

## 4. The stale blocker, re-derived — and a false-necessity claim I nearly repeated

r0038's recorded blocker, "no action of a map on a powerdomain", is gone.
`PowerdomainMap` supplies a **heterogeneous** `smyth (f : D → E) : D♯ → E♯`
(`:393`) with `smyth_id` (`:416`), `smyth_comp` (`:420`),
`scottContinuous_smyth` (`:411`), `map_le_map` (`:257`), `isProjection_smyth`
(`:427`), and the same list for `hoare` and `plotkin`. With agent4's discharges
the blocker is now **nil** at `Dyadic.U` and at every `[Domain U]`.

`PowerdomainMapRep.lean:42-48` says the image isomorphism "has to go through
`IsProjection.isCompactElement_iff` (Lemma 5)". **That is false**, as agent4
found. My own independent re-derivation before agent4's report landed reached the
same conclusion by the same route: factor `p = i ∘ e` through its image
(`e : U → im p`, `e x = ⟨p x, _⟩`; `i = Subtype.val`), then `smyth_comp` gives
`p♯ = i♯ ∘ e♯` and `smyth_id` with `e ∘ i = id` gives `e♯ ∘ i♯ = id`, so `i♯` is
a section and `e♯` a retraction and `range(p♯) = range(i♯)`. `K(im p)` never
appears. Two agents reaching this independently is worth recording: the necessity
sentence was not merely unproved, it was misleading enough to have cost earlier
rounds. Per the orchestrator's instruction I treated it as unverified and did not
edit the file, since agent4 owns the correction.

## 5. Declarations added, with axiom footprints

`scripts/axioms.sh`, run against the built `.olean`. None depends on `sorryAx`.
`Classical.choice` enters through the ambient noncomputable
`CompletePartialOrder (ScottHom α β)` instance; nothing here chooses.

| # | Declaration | Footprint |
| - | ----------- | --------- |
| 1 | `isCompactElement_of_subsingleton` | helper |
| 2 | `domain_of_subsingleton` | `[propext, Classical.choice, Quot.sound]` |
| 3 | `isProjection_of_subsingleton` | helper |
| 4 | `isFinitaryProjection_of_subsingleton` | `[propext, Classical.choice, Quot.sound]` |
| 5 | `not_nonempty_orderIso_of_subsingleton` | `[propext, Quot.sound]` — no choice |
| 6 | `not_isPRepresentable_liftOp` | `[propext, Classical.choice, Quot.sound]` |
| 7 | `not_lemma28_of_subsingleton` | `[propext, Classical.choice, Quot.sound]` |
| 8 | `subsingleton_flatEmpty` | helper |
| 9 | `domain_flatEmpty`, `boundedComplete_flatEmpty` | instance records |
| 10 | `not_lemma28_flatEmpty` | `[propext, Classical.choice, Quot.sound]` |
| 11 | `not_forall_lemma28` | `[propext, Classical.choice, Quot.sound]` |
| 12 | `not_forall_lemma28_bcd` | `[propext, Classical.choice, Quot.sound]` |
| 13 | `lemma28AtU_iff` | `[propext, Classical.choice, Quot.sound]` |
| 14 | `residue_of_powerdomainMap_obligations` | `[propext, Classical.choice, Quot.sound]` |
| 15 | `UniversalForBCD` | `def … : Prop` |
| 16 | `universalForBCD_dyadicU` | `[propext, Classical.choice, Quot.sound]` |
| 17 | `not_universalForBCD_of_subsingleton`, `not_universalForBCD_flatEmpty` | `[propext, Classical.choice, Quot.sound]` |
| 18 | `lemma28_of_universal` | `[propext, Classical.choice, Quot.sound]` |
| 19 | `lemma28AtU_of_universal` | `[propext, Classical.choice, Quot.sound]` |

Namespace `ScottDomains.R45.Agent2` throughout; file prefixed `A2`. No existing
file touched, so no merge conflict with any other stream.

## 6. What I did not do

* I did not weaken `Lemma28` or `Lemma28AtU`, and changed no existing `def`.
* I did not attempt the four `PowerdomainMap.Rep` obligations (agent4's), and
  did not edit `PowerdomainMapRep.lean`.
* `lemma28_of_universal` is **not** a discharge and I do not claim it as one. It
  adds two instance binders and one ordinary hypothesis to a claim whose own `def`
  carries one binder. Both additions are named above and both are shown to be
  load-bearing: the binders by `not_forall_lemma28_bcd`, the hypothesis by
  `not_universalForBCD_of_subsingleton`.
