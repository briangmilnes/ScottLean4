---
round: r0044
from: agent8
to: orchestrator
subject: false-claims
date: 2026-0808-20:34
started: 2026-0808-17:05
finished: 2026-0808-20:34
related:
  - plans/r0044-plan-from-orchestrator-to-orchestrator-specification-defects.md
  - analyses/property-coverage.2026-0808-11:59.orchestrator.md
  - analyses/property-coverage-remeasure.2026-0808-16:55.orchestrator.md
---

# r0044 — Class 4, the reading half: documentation prose whose claim is false

**Count: 7 false claims verified this round**, of which **4 are in live `.lean`
docstrings**, 2 are in `docs/PaperInventory.md`, and 1 is in this round's own
plan. Three of the seven were previously unknown (F2, F4's second half, F8);
four confirm or sharpen a claim another stream flagged.

**11 further claims were checked and found TRUE** and are listed below as
negative results. They must not be moved.

Every finding is backed either by an elaboration against the built `.olean`
(`scripts/a8-check.sh`) or by an exhaustive `grep` whose command is quoted.
No `.lean` file was edited.

## Instruments

| # | Script | What it does |
| - | ------ | ------------ |
| 1 | `scripts/a8-categorical-claims.sh` | Greps every `.lean` and `docs/*.md` for categorical prose — "not in Mathlib", "there is no", "the only", "never", "does not exist", "unproved". 221 hits. |
| 2 | `scripts/a8-doc-claims.py` | Pairs each `/-- … -/` docstring with the signature of the declaration it documents, so the prose CLAIM can be read against the TYPE. |
| 3 | `scripts/a8-check.sh` | Elaborates a scratch `.lean` against the built package. This is the evidence instrument: a claim about a declaration is settled by `#check`/`#print axioms`, never by a source line. |

Two shapes proved to have almost all the yield, and both were named in the
brief:

* **A docstring asserting a binder is required.** Refutable mechanically:
  delete the binder, re-run the same proof term, and see whether the kernel
  accepts. Two of the four live-`.lean` findings are this shape.
* **A module docstring recording "we searched and found nothing"** that a
  later round then made false by building the thing. Two findings.

### Measured precision

The sweep is a discovery aid, not a decision procedure. Of the **19** claims I
selected from its 221 hits and carried through to verification, **7 were false
and 12 were true** — a selection precision of **36.8%**. Reported precision on
the seven findings is 100% by construction: each is individually
kernel-checked or backed by a quoted exhaustive grep, and the twelve negatives
are reported below rather than discarded.

## Ranked findings

Ranked by severity: a false claim in a live `.lean` docstring outranks one in
a `docs/` file, which outranks one in a plan.

### F1 — `Powerdomain/BoundedComplete.lean:321–323`: a binder claimed consumed that is not

> "Unlike the `D♭` conjunct, both hypotheses on `D` are consumed:
> `[BoundedComplete α]` builds `a ⊔ b` and `[Domain α]` is what makes
> `Basis α` a countable pre-order in the first place."

**False.** `[Domain α]` is not consumed. Refuted by deletion: `lem13_smyth`'s
proof term re-run with the `[Domain α]` binder removed is accepted by the
kernel.

    theorem lem13_smyth_noDomain (α : Type u) [CompletePartialOrder α] [BoundedComplete α]
        (S : Set (Smyth.Powerdomain α)) (hS : BddAbove S) : ∃ I, IsLUB S I :=
      exists_isLUB_of_bddAbove_idealCompletion (fun _ _ h => smyth_exists_isLUB_pair h) hS

    'lem13_smyth_noDomain' depends on axioms: [propext, Classical.choice, Quot.sound]

No `sorryAx`. The file **contradicts itself eight lines later**: `:329–331`,
the docstring of `instBoundedCompleteSmyth`, says "`[Domain α]` is not needed,
since `Smyth.Powerdomain` does not take it and countability of `Basis α` is
not used to build a join." That sentence is the correct one. This is the
cleanest instance of the class in the tree — two sentences of one file,
mutually exclusive, ten lines apart.

Found by agent4's vacuity stream (branch `agent4`, commit `ce7bbae`);
independently confirmed here against the built `.olean`.

### F2 — `PRepFun.lean:658–664`: an absence the same file refutes, naming a declaration that does not exist

> "2. **`Domain (D ⊗ E)` does not exist.** `ClosureProperties.lean` has
> `lem10_smash …` and `lem17_smash …`, and the `IsAlgebraic` instances in the
> development are `Set X`, `ScottHom α β`, `α × β`, `WithBot α` and
> `IdealCompletion A` — the smash is not among them. `SmashObstruction` below
> names this as a `Prop`, so the gap is a statement the kernel elaborates
> rather than a sentence of prose."

**False twice over, and previously unknown.**

1. `Domain (D ⊗ E)` **does** exist, and is proved 334 lines below in the same
   file (`PRepFun.lean:992`):

       @ScottDomains.PRepFun.smashDomain : ∀ {α β} [CompletePartialOrder α]
         [CompletePartialOrder β] [ScottDomains.Domain α] [ScottDomains.Domain β],
         ScottDomains.Domain (ScottDomains.Smash α β)
       'ScottDomains.PRepFun.smashDomain' depends on axioms: [propext, Classical.choice, Quot.sound]

   together with `smashIsAlgebraic` at `:926`, which supplies the very
   `IsAlgebraic` instance the passage says is missing.

2. **`SmashObstruction` does not exist anywhere in the package.**
   `grep -rn "SmashObstruction" ScottDomains/ --include='*.lean'` returns
   exactly one hit — this docstring. So the sentence "the gap is a statement
   the kernel elaborates rather than a sentence of prose" is itself false: the
   gap is a sentence of prose naming a `Prop` that was never declared.

The **module** docstring of the same file, at `:104–109`, states the corrected
version in the past tense — "`Domain (D ⊗ E)` **did not** exist … `smashIsAlgebraic`
and `smashDomain` close that" — and `:49` lists `smashDomain` among what the
module supplies. The section docstring at `:652` was never updated when the
section it introduces closed the gap. Note the tense: `:655`'s companion claim
about `r ⊗ s` says "does not exist … This section builds it", which is
self-repairing; `:658`'s does not repair itself and points at a phantom.

### F3 — `FlatPowerdomain.lean:549–551`: a docstring promising a conjunct the statement lacks

> "**`(N⊥)♯` is isomorphic to the domain of sets `{N} ∪ P*f(N)` ordered by
> superset inclusion.** Stated as an order isomorphism **that carries every
> directed supremum**, as in `hoare_natBot_orderIso_powerset`."

**False**, and the docstring's own cross-reference makes the discrepancy
exact. The statement (`:552–554`) is

    theorem smyth_natBot_orderIso :
        ∃ e : SmythCarrier ≃o Smyth.Powerdomain NatBot,
          ∀ S : SmythCarrier, e S = smythOf S

— an order isomorphism plus a pointwise equation, with no supremum clause.
The declaration it names as the model, `hoare_natBot_orderIso_powerset`
(`:286–289`), *does* carry it:

    ∃ e : Hoare.Powerdomain NatBot ≃o Set ℕ,
      (∀ s : Set (Hoare.Powerdomain NatBot), DirectedOn (· ≤ ·) s →
        e (sSup s) = sSup (e '' s)) ∧ Domain (Set ℕ)

The missing conjunct is therefore named precisely:
`∀ s, DirectedOn (· ≤ ·) s → e (sSup s) = sSup (e '' s)`, and so is the
missing `Domain` conjunct. The claim is repairable either by weakening the
docstring or by strengthening the statement — `smythOrderIso` is an `≃o`, so
`OrderIso.map_sSup_of_directedOn` supplies the clause in one line, exactly as
`hoare_natBot_orderIso_powerset`'s proof term does.

Flagged in the brief; confirmed here, with the missing conjunct identified.

### F4 — `PowerdomainMap.lean:18–25`: a "zero hits" survey the same module falsifies, plus a mis-citation

> "Nine name variants (`fSharp`, `powerdomainMap`, `Powerdomain.map`,
> `hoareMap`, `smythMap`, `plotkinMap`, `mapPowerdomain`, `fFlat`,
> `fNatural`) returned zero hits … Two other modules had recorded the same
> absence for their own purposes: `PRepFun.lean:98` and
> `docs/PaperInventory.md` row 554."

**False in two independent ways.**

1. `ScottDomains.PowerdomainMap.map` is defined at `:167` of this very file.
   The header asserts the absence of a name the module then introduces. This
   is agent7's hand-off — correctly not counted by its sweep, since the name
   is cited *to say it is absent*, so name resolution is the wrong test.
2. **The cross-reference to `PRepFun.lean:98` is wrong.** `PRepFun.lean:98`
   reads "**`r ⊗ s` did not exist.** `grep` over every module finds no
   functorial action **on the smash** — `Isomorphism/Smash.lean` supplies only
   `smashComm` and `smashAssoc`." That is an absence claim about the *smash*,
   not about a powerdomain, and it is in the past tense with its own repair
   (`smashMap`) named in the same sentence. It never recorded "the same
   absence."

### F5 — `docs/PaperInventory.md:586`: the powerdomain-map absence, still in the present tense

> "`()♯` and `()♭` remain, and their obstruction is **not** the definability
> one earlier rounds recorded …: the development defines **no action of a map
> on either powerdomain**, so there is no `r ↦ r♯` to build the conjugating
> family from"

**False.** All three actions exist, with both functor laws and the projection
property:

    @ScottDomains.PowerdomainMap.smyth   : … → (D → E) → Smyth.Powerdomain D → Smyth.Powerdomain E
    @ScottDomains.PowerdomainMap.hoare   : … (the Hoare carrier)
    @ScottDomains.PowerdomainMap.plotkin : … → Plotkin.Powerdomain D → Plotkin.Powerdomain E
    @ScottDomains.PowerdomainMap.smyth_id       : smyth id = id
    @ScottDomains.PowerdomainMap.smyth_comp     : … smyth (g ∘ f) = smyth g ∘ smyth f
    @ScottDomains.PowerdomainMap.isProjection_smyth : …

`exists_unique_map` (`PowerdomainMap.lean:210`) is the paper's §5.3 sentence in
full. `PowerdomainMapRep.lean` then *spends* the action, reducing each of `()♯`
and `()♭` from "no formulation at all" to two named `Prop`s.

**Two corrections to the brief and to the other streams.** The live line is
**586**, not 554 — 554 is the Lemma 13 row and carries no such claim; the row
number has drifted and every citation of "row 554" in r0040 and r0043 reports
now points at the wrong row. And the correct companion site is *not*
`PRepFun.lean:98` (see F4.2): the only other live site is
`PowerdomainMap.lean:24`, which cites the stale row.

### F6 — `docs/PaperInventory.md:23` row 3: **91 is the wrong number**, and the categories are non-complementary

Row 3 reads, verbatim:

> "| 3 | **Unnumbered prose claims** | **146 stated by the paper**, of which
> the development proves 91 (r0040, measured section by section: §2/§3 45, §4
> 37, §5 17, §6 19, §7 28) … | 60 unstated — see row 2e | **146** |"

`146 − 91 = 55`, not 60. Resolved from the r0040 per-section data:

**146 is right.** `analyses/property-coverage.2026-0808-11:59.orchestrator.md:20–27`
gives the per-section table; its prose column is `45 + 37 + 17 + 19 + 28 =
146`. The table is internally consistent — properties `60+54+29+35+61 = 239`,
numbered `15+17+12+16+33 = 93`, and numbered + prose = properties in every row.

**60 is right.** The prose `N` (no Lean statement) column sums to
`22 + 12 + 9 + 4 + 13 = 60`. It is the global 62 minus the two *numbered* `N`
rows, which agent1's r0040 report identifies explicitly (line 39: "Two of the
24 `N` rows are conjuncts of Theorem 7; the other 22 are prose claims"). Row
3's cross-reference "see row 2e" is what makes 60 look wrong: **row 2e's 62 is
over all 239 properties; row 3's 60 is prose only.**

**91 is wrong, and it is not a prose figure at all.** It is the
numbered-results count, lifted verbatim from the same analysis — lines 50 and
142 both read "**91 of 93 numbered conjuncts are stated in some form**" — and
transcribed into the prose row as if it counted prose claims proved. Two
independent proofs:

1. The parenthetical that purports to justify it, "measured section by
   section: §2/§3 45, §4 37, §5 17, §6 19, §7 28", **sums to 146, not 91**.
   Those five numbers are the prose *total* column copied in. Nothing in r0040
   or r0043 supports 91 as a per-section prose sum.
2. Decomposing the prose column by label across the five r0040 agent reports
   gives `S+P` 70, `S+H` 1, `S≠` 5, `P` 10, `N` 60 — total 146. The
   reconstruction closes exactly against the global label totals at analysis
   lines 13–18 (`S+P` 136, `S+H` 15, `S≠` 16, `P` 10, `N` 62) on all five
   labels. So prose-*proved* is **70** and prose-*stated-in-some-form* is
   **86**. 91 is neither, and it **exceeds the maximum possible (86) by 5**.

**There is a second, category-level defect underneath the arithmetic.** r0040's
label set has five mutually exclusive values; "proves" is `S+P` alone and
"unstated" is `N` alone. Between them sit `S+H`, `S≠` and `P` — `1 + 5 + 10 =
16` prose rows. So **no correction to a single number makes
`146 − proved = unstated` true**: even with the correct 70, `146 − 70 = 76 ≠
60`. The row's two-column subtraction form is unsound whatever numbers fill it.

Exactly two consistent repairs exist. The orchestrator picks one; I have not
edited the file.

| # | Repair | Arithmetic |
| - | ------ | ---------- |
| 1 | change the middle column from *proved* to *stated*: "146 stated by the paper, of which **86** have a Lean statement of some kind; 60 unstated" | `146 − 86 = 60` ✓ |
| 2 | keep "proves" and abandon the two-column form: "146 prose claims = **70** `S+P` + 1 `S+H` + 5 `S≠` + 10 `P` + 60 `N`" | sums to 146 ✓ |

The r0043 remeasure does not revise any of the three figures: it re-checks
only the 62 `N` rows (36 now stated, 26 still `N`), so it is a later-dated
correction to **row 2e**, not to row 3. One consequence worth recording: after
r0043 the prose `N` figure of 60 is itself **stale** by roughly the 36 that
closed, so rows 2e and 3 report different dates even where both are
arithmetically correct.

### F7 — `docs/PaperInventory.md` row 569: an under-claim (relayed, not re-verified here)

The row qualifies Lemma 17 as over-hypothesized on `→` and `◦→` — two
conjuncts. agent4 proved by deletion-and-reproof that `lem17_hoare`,
`lem17_smyth` and `lem17_plotkin` each also carry an unnecessary `[Domain D]`,
so the qualification should name **five** conjuncts. Relayed from agent4; I did
not re-run the deletions, and it is not counted in my 7.

This is worth a separate label: **prose that admits a defect but understates
its extent**. An under-claim is invisible to a sweep for false assertions,
because the sentence is true as far as it goes.

### F8 — the r0044 plan itself, lines 143–144

> "`PaperInventory.md` row 554 and `PRepFun.lean:98` assert no powerdomain map
> action exists."

**Both halves are wrong.** Row 554 is the Lemma 13 row; the claim lives at row
**586** (F5). And `PRepFun.lean:98` asserts no functorial action **on the
smash**, in the past tense, naming its own repair in the same sentence (F4.2).
Reported per the plan's own standing rule that the plan is not evidence.

## Negative results — 11 claims checked and found TRUE

Do not move any of these. Each is reported because a sweep that only reports
hits has no measurable precision.

| # | Site | Claim | Evidence it is TRUE |
| - | ---- | ----- | ------------------- |
| 1 | `Universality.lean:88`, `SeparatedSum.lean:173` | "Mathlib has no `OrderIso.prodCongr`" | `#check @OrderIso.prodCongr` → `error: Unknown constant`. The `prodCongr`s in `Order/Hom/Lex.lean` and `Order/RelIso/Basic.lean` are for the **lexicographic** product, not the componentwise one. |
| 2 | `Atomless.lean:36`, `PaperInventory.md:585` | "Mathlib v4.32.2 has **zero** occurrences of `IsAtomless`" | `grep -rln "IsAtomless" .lake/packages/mathlib/Mathlib/` → 0 files. |
| 3 | `Effective/FunctionSpace.lean:335` | "`Mathlib/Computability/` mentions no `Nat.bitwise`" | `grep -rn "Nat.bitwise" …/Mathlib/Computability/` → 0 hits. |
| 4 | `Effective/FunctionSpace.lean:300` | "Mathlib v4.32.2 has no `Primcodable (Finset ℕ)` instance" | The nine Mathlib files mentioning `Primcodable` contain no `Finset` instance; `Computability/Primrec/List.lean` has zero `Finset` occurrences. |
| 5 | `Powerdomain/BoundedComplete.lean:28` | "There is no `lem13_plotkin`" | `grep -rn "lem13_plotkin"` → 0 declarations; only `lem13_hoare` and `lem13_smyth` exist. |
| 6 | `Audit/Powerdomains.lean:14`, `Audit/Foundations.lean:16` | "Nothing in the development imports this module" | `grep -rn "import ScottDomains.Audit"` → 0 hits; the root `ScottDomains.lean` does not name them either. |
| 7 | `UniversalDomain.lean:80`, `Projection.lean:82` | "there is no composition operation on `ScottHom.IsEmbeddingProjectionPair`" | The only three lemmas on it are `injective_embedding`, `surjective_projection`, `isProjection_comp` — none composes two pairs. |
| 8 | `PropertyM.lean:40` | "Iwamura's lemma … Mathlib does not carry (zero hits for `Iwamura\|Markowsky`)" | `grep -rlE "Iwamura\|Markowsky" …/Mathlib/` → 0 files. |
| 9 | `Powerdomain/BoundedComplete.lean:190–194` | `lem13_hoare`'s "`[BoundedComplete α]` is not consumed" | Deletion probe: `lem13_hoare` re-proved with `[BoundedComplete α]` removed, kernel accepted, `[propext, Classical.choice, Quot.sound]`. |
| 10 | `Audit/Powerdomains.lean:107` | "`lem13_hoare` needs **neither** `[Domain α]` nor `[BoundedComplete α]`" | Stronger deletion probe: `lem13_hoare_noDomain` with **both** binders removed elaborates and is accepted. I had expected `Hoare.Powerdomain α` to require `[Domain α]`; it does not. The claim is exactly right. |
| 11 | `Kleene/Uniform.lean:39–41` | strictness "is indispensable — without it `h(⊥)` need not be `⊥`" | Deletion probe **fails**, which is the confirmation: removing `hbot` from `map_iterate_bot` leaves `case zero ⊢ h ⊥ = ⊥` unsolved — precisely the deleted hypothesis. |

Rows 9–11 are the important ones methodologically: **a failed deletion is a
positive result about necessity**, and rows 3 and 4 of the brief's calibration
list show the converse. The deletion probe decides the shape in both
directions, which is why it should be the standard instrument for
hypothesis-necessity prose.

## Reproduction

    scripts/a8-categorical-claims.sh <out>            # the 221-hit candidate sweep
    scripts/a8-doc-claims.py '<regex>' <out>          # docstring paired with signature
    scripts/a8-check.sh <scratch.lean>                # elaborate against the built package

The three probe files are reproduced in full in the findings above (F1's
`lem13_smyth_noDomain`, F2's `#check @…smashDomain`, F5's `#check @…smyth`,
and negative results 9–11); each is a handful of lines and none touches a
package `.lean` file.

## Build state

No `.lean` file was edited; the only files added are the three `scripts/a8-*`
instruments and this report. Package build and counts re-verified before
reporting — see the closing section of the commit log.
