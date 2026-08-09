---
round: r0045
from: agent4
to: orchestrator
subject: discharge-powerdomain-rep
date: 2026-0808-21:26
started: 2026-0808-21:12
finished: 2026-0808-21:26
related:
  - plans/r0045-plan-from-orchestrator-to-orchestrator-discharge-nineteen.md
  - reports/r0044-report-from-agent6-to-orchestrator-undischarged-defs.md
---

# r0045, agent4 — all four powerdomain-map obligations discharged, and Lemma 28 at `U` with them

## 1. Result

Four of four moved, all to **discharged**. One new module,
`ScottDomains/A4PowerdomainRep.lean`, 0 `sorry`, build at zero errors and zero
warnings.

| # | Claim | Status | Theorem | Axiom footprint |
| -- | ----- | ------ | ------- | --------------- |
| 1 | `PowerdomainMap.Rep.SmythImageIso` | **discharged** | `R45.Agent4.smythImageIso` | `[propext, Classical.choice, Quot.sound]` |
| 2 | `PowerdomainMap.Rep.SmythFamilyLUB` | **discharged** | `R45.Agent4.smythFamilyLUB` | `[propext, Classical.choice, Quot.sound]` |
| 3 | `PowerdomainMap.Rep.HoareImageIso` | **discharged** | `R45.Agent4.hoareImageIso` | `[propext, Classical.choice, Quot.sound]` |
| 4 | `PowerdomainMap.Rep.HoareFamilyLUB` | **discharged** | `R45.Agent4.hoareFamilyLUB` | `[propext, Classical.choice, Quot.sound]` |

No footprint mentions `sorryAx`. Measured by `scripts/axioms.sh`, and the
signatures below are read from the built `.olean` by a new
`scripts/a4-signatures.sh`, not from source lines:

    @…R45.Agent4.smythImageIso   : ∀ {U : Type u_1} [CompletePartialOrder U] [Domain U], …Rep.SmythImageIso U
    @…R45.Agent4.smythFamilyLUB  : ∀ {U : Type u_1} [CompletePartialOrder U] [Domain U], …Rep.SmythFamilyLUB U
    @…R45.Agent4.hoareImageIso   : ∀ {U : Type u_1} [CompletePartialOrder U] [Domain U], …Rep.HoareImageIso U
    @…R45.Agent4.hoareFamilyLUB  : ∀ {U : Type u_1} [CompletePartialOrder U] [Domain U], …Rep.HoareFamilyLUB U

`[CompletePartialOrder U]` and `[Domain U]` are exactly the binders each claim
itself carries — `…Rep.SmythImageIso : (U : Type u_1) → [CompletePartialOrder U]
→ [Domain U] → Prop`. So the hypothesis count beyond instance binders is **zero**
for each, which is agent6's detection rule.

## 2. The fifth row: `PRep.Lemma28AtU` closes as a consequence

This is the finding the orchestrator most needs, because it is **agent2's row**,
not mine.

`PowerdomainMapRep.lemma28AtU_of''` had arity 4 and its four hypotheses were
exactly the four claims above. Substituting the four theorems gives

    ScottDomains.R45.Agent4.lemma28AtU : ScottDomains.PRep.Lemma28AtU
      [propext, Classical.choice, Quot.sound]

with **zero hypotheses**. `PRep.Lemma28AtU` is `abbrev Lemma28AtU : Prop :=
Lemma28 Dyadic.U` (`PRep.lean:284`), and `PRep.Lemma28` is the nine-fold
conjunction `→, ⇸, ×, ⊗, +, ⊕, (·)⊥, (·)♯, (·)♭`. So **Lemma 28 of Gunter &
Scott §7.3 is now formally verified over `U`**, by the kernel, at the three
standard axioms.

The chain is: my four → `Rep.repSmythAtU` / `Rep.repHoareAtU` (arity 2 → 0, also
recorded in my module as `R45.Agent4.repSmythAtU`, `R45.Agent4.repHoareAtU`, both
closed) → `Lemma28AtU.lemma28AtU_of'` (arity 2, the other seven conjuncts already
proved) → `PRep.Lemma28AtU`.

So `scripts/a6-claims.txt` loses **five** rows from this stream, not four:
rows 13–16 (mine) and row 6, `ScottDomains.PRep.Lemma28AtU`.

**Coordination with agent2.** agent2 holds `PRep.Lemma28` and `PRep.Lemma28AtU`.
The second is now closed by my work, and agent2 should not spend the round on it;
the first, `Lemma28 U` for an arbitrary `U`, does **not** follow — the seven
conjuncts other than `(·)♯` and `(·)♭` reach `U` through `PRepSum.pairAtU`, which
is Theorem 27 at the atomless `Dyadic.U`, so generic `U` is untouched. The plan's
note that r0038's blocker is stale is correct: nothing about the powerdomain
action blocks these two any longer. If agent2 also produces a `Lemma28AtU`, the
orchestrator should keep one and delete the other rather than merge both.

`Rep.rep_smyth_of` and `Rep.rep_hoare_of` also drop from arity 4 to arity 2
(`R45.Agent4.rep_smyth`, `R45.Agent4.rep_hoare`): the two obligations go, the two
retraction-pair equations remain, and at `U` those are what `PRepSum.pairAtU`
supplies.

## 3. Are Smyth and Hoare dual here? Measured: yes, exactly

The plan asked for this to be established rather than assumed. It is dual, and
the measurement is the diff between the two proofs.

| # | Pair | Tokens that differ |
| -- | ---- | -----------------: |
| 1 | `smythFamilyLUB` / `hoareFamilyLUB` | 2 — the presentation `A` (`Smyth.Basis U` vs `Hoare.Pf ↥(compacts U)`) and `foldMono_smyth` vs `foldMono_hoare` |
| 2 | `smythImageIso` / `hoareImageIso` | 3 — `smyth_comp`/`hoare_comp`, `smyth_id`/`hoare_id`, `scottContinuous_smyth`/`scottContinuous_hoare`, each a renaming of the same generic `map_*` lemma |

Nothing else differs. The reason is structural rather than lucky: `isLUB_mapFamily`
is stated generically in the pre-order `A` presenting `Pf(K(U))`, and the two
powerdomains enter only through the single obligation `Monotone (foldGen (unitComp
f))`. The theory instances `IsUpper` (`4♯`, `s ⋓ t ⊑ s`) and `IsLower` (`4♭`,
`s ⊑ s ⋓ t`) are consumed **only inside** `foldMono_smyth` and `foldMono_hoare`,
both proved in r0041. Above that line the upper/lower distinction is invisible.

For the image isomorphism the duality is even stronger: the argument uses only
the functor laws, which `PowerdomainMap.map_id` and `map_comp` prove once,
generically, for all three powerdomains at once. The Plotkin case would go
through verbatim if it were wanted; §7.4 says `(·)♮` is not representable over
`U`, so it is not.

## 4. How the four were proved, and one plan/docstring correction

### 4.1 The image isomorphisms are not about powerdomains

`PowerdomainMapRep.lean:42–48` states, and the plan repeats, that the
identification `im(p♯) ≅ (im p)♯` "cannot be made by transporting a basis; it has
to go through `IsProjection.isCompactElement_iff` (Lemma 5), which characterises
`K(im p)` intrinsically."

**That is false as a necessity claim.** My proof never mentions `K(im p)`,
never uses Lemma 5, and never uses `PowerdomainCompacts`. The premise it rests on
is sound — `p(K(D)) ⊆ K(D)` really does fail — but the conclusion drawn from it
does not follow, because the isomorphism does not need a basis map in either
direction.

The route actually taken: write `ι : im(p) → U` for the inclusion and
`π : U → im(p)` for `x ↦ p x`. Both are Scott continuous
(`PRepFun.scottContinuous_val`, `PRepFun.scottContinuous_corestrict`), and
`π ∘ ι = id` while `ι ∘ π = p`. Apply the functor:

    map π ∘ map ι = map (π ∘ ι) = map id = id,       map ι ∘ map π = map p.

The first equation makes `map ι` injective **and order-reflecting**; the second
makes `im(map p) = im(map ι)`. What remains is
`nonempty_orderIso_range_of_section`, a statement about two monotone maps between
two preorders with no domain theory in it at all:

    theorem nonempty_orderIso_range_of_section {X Y} [PartialOrder X] [Preorder Y]
        {i : X → Y} {r : Y → X} {c : Y → Y} (hi : Monotone i) (hr : Monotone r)
        (hri : ∀ x, r (i x) = x) (hc : ∀ y, c y = i (r y)) :
        Nonempty (↥(Set.range c) ≃o X)

The whole mathematical content is the two functor laws, which r0041 already
proved. That is why this cost 20 lines rather than a re-derivation of `K(im p)`.

I have **not** edited `PowerdomainMapRep.lean`: the file is cited by agent2 this
round and a prose edit would conflict. The correction is recorded in
`A4PowerdomainRep.lean`'s own docstring, §1, and here. The orchestrator should
fix the parent docstring at merge.

### 4.2 The family LUBs are one interchange of suprema

`p♯ y = ⨆ {foldGen ({|·|} ∘ p) u | u ∈ y}`, so preserving a directed supremum in
`p` is an interchange. Three steps, and only the middle one is new work:

1. least upper bounds in `Fp(U)` are pointwise
   (`PRep.isLUB_val_image_of_isLUB_fp'` — this is where `[Domain U]` and
   `isFinitaryProjection_sSup` are spent), and `{|·|}` is Scott continuous
   (`ContinuousAlgebra.scottContinuous_unit`). That gives the claim one compact
   element at a time. This half is `isLUB_liftFamily`'s script, unchanged.
2. `isLUB_fold` lifts it from one compact to the finite fold
   `{|p k₁|} ⋓ ⋯ ⋓ {|p kₙ|}`, by induction on the non-empty `Finset`. The step is
   the new lemma `isLUB_op_of_isLUB`: `ContinuousAlgebra.isLUB_op_image` gives the
   least upper bound over the **product** index `d ×ˢ d`, and directedness of `d`
   together with monotonicity of both factors makes the diagonal cofinal in that
   product. This is precisely where the *joint* (not separate) continuity that
   `Binop` demands is spent; separate continuity in each argument would not close
   it.
3. `isLUB_idealExtend` in both directions moves between the fold and the ideal
   extension, with `PowerdomainMap.map_le_map` giving the upper-bound half.

New declarations, all in namespace `ScottDomains.R45.Agent4`:
`nonempty_orderIso_range_of_section`, `isLUB_op_of_isLUB`, `isLUB_fold`,
`isLUB_mapFamily`, the four claim theorems, and five closed or reduced consumers
(`rep_smyth`, `rep_hoare`, `repSmythAtU`, `repHoareAtU`, `lemma28AtU`).

## 5. The `smyth_natBot_orderIso` docstring defect: confirmed, and unrelated

r0044's agent8 is right, and I checked it against the source rather than
assuming. `FlatPowerdomain.lean:549–555`:

    /-- … Stated as an order isomorphism that carries every directed
    supremum, as in `hoare_natBot_orderIso_powerset`. -/
    theorem smyth_natBot_orderIso :
        ∃ e : SmythCarrier ≃o Smyth.Powerdomain NatBot, ∀ S : SmythCarrier, e S = smythOf S

There is no directed-supremum clause in the statement. The Hoare counterpart at
`:286` does carry one, `∀ s, DirectedOn (· ≤ ·) s → e (sSup s) = sSup (e '' s)`,
plus `Domain (Set ℕ)`. So the docstring's "as in `hoare_natBot_orderIso_powerset`"
is false.

**It has no bearing on the four claims.** None of my four proofs reads the flat
case, and the asymmetry it reports is an accident of how two concrete
calculations at `N⊥` were written up, not a difference between the upper and lower
powerdomains. At the level of generality the four claims live at, §3's measurement
shows the two are dual. Lead 2 of the plan (work the concrete `N⊥` case first to
see the shape of the general argument) turned out to be unnecessary — the general
argument is *shorter* than the concrete one, because it goes through the functor
laws rather than through an explicit description of the carrier.

## 6. Verification record

* build: `scripts/compile.sh -r r0045` — `lake errors 0 · sorry 0 · other warnings 0`,
  1340 jobs, log `ScottDomains/logs/compile-20260808-212358.agent4.log`.
* axioms: `scripts/axioms.sh` over all 13 new declarations — every one
  `[propext, Classical.choice, Quot.sound]`, none `sorryAx`.
* statements: `scripts/a4-signatures.sh` (new) prints `#check @d` against the
  built environment, so the "zero hypotheses beyond instance binders" claim is
  read from the `.olean`, not from a source line.
* namespace: everything new is under `ScottDomains.R45.Agent4`; the one new module
  is `ScottDomains/A4PowerdomainRep.lean`; the one new script is
  `scripts/a4-signatures.sh`. No existing file is modified, so the merge is a
  pure addition and cannot collide except on `a6-claims.txt` bookkeeping.
