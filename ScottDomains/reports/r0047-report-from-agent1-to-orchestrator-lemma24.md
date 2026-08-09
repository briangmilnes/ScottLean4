---
round: r0047
from: agent1
to: orchestrator
subject: lemma24
date: 2026-0809-12:40
started: 2026-0809-12:05
finished: 2026-0809-12:40
related:
  - plans/r0047-plan-from-orchestrator-to-orchestrator-close-the-seven.md
  - reports/r0046-report-from-agent2-to-orchestrator-thm29normal.md
---

# r0047 agent1 — Gunter's Lemma 24 at `M(A)`

**The three questions, answered first.**

| # | Question | Answer |
| -- | -------- | ------ |
| 1 | Is Lemma 24 at `M(A)` proved? | **Yes** — `lemma24_MPair`, kernel-checked, `[propext, Classical.choice, Quot.sound]`. It is the first proof of it: Gunter proves Lemma 24 abstractly and records the `M(A)` form as an unproved remark |
| 2 | Is `R46.Agent2.HasNormalRealizations Ainf` discharged? | **No — it is refuted.** `not_hasNormalRealizations_Ainf`, kernel-checked. r0046's reduction is sound and its target is false |
| 3 | How many of the three dependent claims fell? | **Zero.** `Thm29Normal`, `Thm29SecondAtDomains` and `Lemma30AtV` are unchanged — still open, and now known to be unreachable through Gunter's Theorem 25 at this tower |

New file `ScottDomains/ScottDomains/A1Lemma24.lean`, 466 lines, 25 top-level
declarations (23 theorems, 2 `def`; 6 theorems and 1 `def` are `private`
helpers), namespace `ScottDomains.R47.Agent1`. Package: **1357 jobs, 0 errors, 0
warnings, 0 `sorry`**. No existing file was changed; no `def` was changed.

## 1. The plan's premise, measured against the printed text

The plan says the proof is published and is transcription rather than research.
Checked against `papers/Gunter 1987 Universal Profinite Domains.pdf`, pp. 20–23,
that is **wrong in a specific and important way**, and I state it only after
reading the printed pages.

| # | what p. 20–23 actually carries | status in the paper |
| -- | ----------------------------- | ------------------- |
| 1 | Lemma 24: *there is* a finite `A⁺ ▷ A` realizing every normal type over every `B ◁ A` | stated **and proved** (p. 21), by iterating Lemma 23 over an enumeration `Γ₁, …, Γₙ` of the normal types. The proof produces no explicit `A⁺` |
| 2 | `A⁺ = Ã_tp`, the pre-order on diagram types | property **asserted, not proved**: "If we let `A⁺ = Ã_tp` then there is a normal substructure `A' ◁ A⁺` … such that …" |
| 3 | `A⁺ = M(A)`, Scott's pair construction | **no theorem, no proof, no property claim.** The printed sentence is "This more order-theoretic way of doing things helps in *picturing* the universal domain as the limit of the posets `A ⊴ A⁺ ⊴ A⁺⁺ ⊴ ⋯`" |

So Gunter's *proof* of Lemma 24 does not transfer to `M(A)`, because it is not
about `M(A)`: it is an abstract iteration of Lemma 23 in which `A⁺` is whatever
the induction produced. r0046's row 4 was accurate; the plan's inference from it
— that the `M(A)` case is transcription — is not.

**This is a finding about the paper, not a printed defect.** Gunter claims
nothing false; he claims less than the plan reads into him. I have not added a
tenth entry to `docs/StatementRecovery.md`.

## 2. Lemma 24 at `M(A)`, proved

`lemma24_MPair` (line 215) is Gunter's Lemma 24 with `A⁺ = M(A)`, for an
arbitrary poset `α`:

```lean
theorem lemma24_MPair {B : Set α} (hBfin : B.Finite) (hB : B ◁ (Set.univ : Set α))
    (γ : Type*) [PartialOrder γ] (T : Set γ) (g : α → γ) (z : γ)
    (hg : ∀ a ∈ B, ∀ b ∈ B, (g a ≤ g b ↔ a ≤ b))
    (hgB : g '' B ◁ T) (hzB : insert z (g '' B) ◁ T) :
    ∃ m : MPair α,
      (∀ b ∈ B, (eta b ≤ m ↔ g b ≤ z) ∧ (m ≤ eta b ↔ z ≤ g b)) ∧
      insert m (eta '' B) ◁ (Set.univ : Set (MPair α))
```

The type is presented exactly as `R46.Agent2.HasNormalRealizations` presents it —
witnessing poset `γ`, finite `T`, order-reflecting `g`, point `z` — so the shapes
are directly comparable. `lemma24_Step` carries it through §7.4's identification
into `Step α = M(α)/≈`, which is the type the tower is built from.

Gunter's other clause, `A ◁ A⁺`, is `isNormalIn_eta_image_univ`.

The proof, and what it costs:

| # | step | content |
| -- | ---- | ------- |
| 1 | `eta_le_iff` | `η X ⊑ ⟨x, u⟩ ↔ X ⊑ x`. The identification disjunct is absorbed — it gives `X = x` |
| 2 | `le_eta_iff` | `⟨x, u⟩ ⊑ η X ↔ X ∈ ↑u`. The identification disjunct makes `↑u = ↑X ∋ X` |
| 3 | the witness | `⟨X₀, U⟩` with `X₀` the greatest element of `B ∩ ↓z` and `U = B ∩ ↑z`. `X₀` exists because `g''B ◁ T` makes `g''B ∩ ↓z` directed and `B` is finite (`SFP.exists_greatest_of_finite`); `X₀ ⊑` every member of `U` because `z` does |
| 4 | `isNormalIn_insert_eta_image` | `η''B ∪ {Z} ◁ M(A)`. The only hypothesis on `Z` is that **its cover lies in `B`** |

Three hypotheses of `HasNormalRealizations` are **not used**: `T.Finite`, and
`insert z (g''B) ◁ T` beyond its consequence `z ∈ T`. `B.Finite` is used exactly
once, for step 3's greatest element; step 4 needs neither `A` nor `B` finite.

Steps 1, 2 and 4 are on `[propext, Quot.sound]` only.

## 3. `HasNormalRealizations A∞` is false, and where the transfer breaks

Lemma 24 at `M(A)` is stated against the embedding `η : x ↦ (x, {x})` — §7.4's
own connecting map and the one Gunter's p. 23 remark uses. **`Colimit.lean`'s
tower does not use it**, and that is not an oversight: `Colimit.lean:47–68`
argues, correctly, that the colimit along `η` is not a fixed point of `M`, and
`stgEmb_ne_mk_eta` kernel-checks that `stgEmb 1 ≠ mk ∘ eta`. The tower's
connecting map is `stgEmb (n+1) = M(stgEmb n)`.

The two readings differ on pairs with an **empty cover**:

| # | element | image under `η` | image under `M(f)` |
| - | ------- | --------------- | ------------------ |
| 1 | `(x, ∅)` | `((x, ∅), {(x, ∅)})` | `(f x, ∅)` |

`(x, ∅)` is maximal in `M(A)` for every `A`: `(x, ∅) ⊑ (y, v)` forces `y = x` and
`↑v = ∅`, i.e. the same point after §7.4's identification. Under `η` that
maximality is destroyed one stage later (`exists_gt_mk_eta_pointB1`: `(b, ∅)` is
strictly above `η b`). Under `M(f)` the empty cover is carried along unchanged, so
maximality **persists forever** (`stgEmb_topElt`, `topElt_maximal`).

§7.4's own second-step element `b = (⊥, ∅)` is such a point.
`incl_pointB1_maximal` proves its image `β = incl 1 pointB1` is a maximal point of
`A∞`, and `range_incl_one` proves `{⊥, β} = im(incl 1)`, which
`isNormalIn_range_incl 1` already says is normal in `A∞`.

The refutation is then structural, not a contrived instance:

```lean
theorem not_hasNormalRealizations_of_maximal {a : α} (hne : a ≠ ⊥)
    (hA : ({⊥, a} : Set α) ◁ (Set.univ : Set α)) (hmax : ∀ w : α, a ≤ w → w = a) :
    ¬ R46.Agent2.HasNormalRealizations α
```

**The property forbids normal maximal points other than `⊥` outright.** The type
of a point strictly above `a` is normal — `Fin 3` realizes it, and the kernel
checked both `{0,1} ◁ Fin 3` and `{0,1,2} ◁ Fin 3`, so the refutation does not
turn on an unrealizable type — and no `α` with such a point can realize it.
`not_hasNormalRealizations_Ainf` is the instance at `a := β`.

`not_stagewise_realizations` composes it with
`R46.Agent2.hasNormalRealizations_of_stages`: the single-stage sentence r0046
called "the whole of what remains", and which `LemThirty.lean:426` names as the
missing universal property of `M`, is **also false at this tower**.

## 4. Per-claim status

| # | Claim | Status | Evidence |
| -- | ---- | ------ | -------- |
| 1 | Gunter's Lemma 24 at `M(A)` (`η''B ∪ {Z} ◁ M(A)` realizing every normal type) | **discharged** | `lemma24_MPair`, `lemma24_Step`, `isNormalIn_eta_image_univ` |
| 2 | `R46.Agent2.HasNormalRealizations Ainf` | **refuted** | `not_hasNormalRealizations_Ainf` |
| 3 | `hasNormalRealizations_of_stages`'s hypothesis (`LemThirty.lean:426`'s sentence) | **refuted** | `not_stagewise_realizations` |
| 4 | `LemThirty.Thm29Normal` | **open** — unchanged | not implied by anything refuted here |
| 5 | `LemThirty.Thm29SecondAtDomains` | **open** — unchanged | depends on 4 |
| 6 | `LemThirty.Lemma30AtV` | **open** — unchanged | depends on 4 |

Claim 1 is a discharge, not a "discharged at": it adds no instance binder to
anything, and it is a new theorem rather than a weakening of an existing claim.

**Claim 4 is not refuted, and I want that stated precisely.** `Thm29Normal` asks
for a normal embedding `K(E) → A∞` for every bifinite domain `E`; nothing forces
`β` to lie in that embedding's range, so `β`'s maximality does not contradict it.
What is now closed is the *route*: Gunter's Theorem 25 derives universality from
exactly the property refuted in claim 2, so `thm29Normal_of_hasNormalRealizations`
is a sound implication with an unsatisfiable hypothesis.

Axiom footprint: all 18 public theorems on `[propext, Classical.choice,
Quot.sound]`, five of them on `[propext, Quot.sound]` alone. No `sorryAx`
anywhere. `scripts/axioms.sh` was run over every public declaration.

## 5. The tension this exposes, for the next round

Two requirements are now known to pull in opposite directions, and each side is
kernel-checked:

| # | requirement | needs | supplied by |
| -- | ---------- | ----- | ----------- |
| 1 | `V ≅ V⁺` (`Colimit.isoPlus`), which every conjunct of Lemma 30 consumes | the `M(f)` tower | `Colimit.lean`, proved |
| 2 | Gunter's Theorem 25 hypothesis, which universality is derived from | a tower whose connecting map does not preserve maximality | `lemma24_MPair` at `η`, proved — and **refuted** at the `M(f)` tower |

§7.4 asserts both of one object. Gunter does not: his `V_A` is the `η`-colimit and
he never claims `V_A ≅ V_A⁺`; §7.4's Theorem 29 second sentence is what fuses the
fixed point to the universality. Three ways forward, in decreasing order of what
they would buy:

1. Prove `Thm29Normal` at `A∞` by a route that does not pass through Theorem 25.
2. Refute `Thm29Normal` at `A∞`, by exhibiting a bifinite `E` with no normal
   embedding `K(E) → A∞`. I did not attempt this; `β`'s maximality alone does not
   supply it.
3. Build the `η`-tower as a second object, prove its colimit universal from
   `lemma24_MPair`, and accept that it is not a fixed point of `M` — which
   discharges Theorem 29's second sentence for *that* carrier and leaves Lemma 30
   at `V`.

## 6. Two record corrections, not made in code

I changed no existing file, so these are reported rather than applied.

1. **`Colimit.lean:59` cites a declaration that does not exist.** The docstring
   says "`etaChain_not_wellDefined` exhibits the failure at the paper's own second
   stage with `u = ∅`". `grep` over `ScottDomains/` finds that name in exactly one
   place — that docstring. The kernel-checked witness for the divergence is
   `stgEmb_ne_mk_eta` (line 619), which proves something weaker but sufficient:
   the two connecting maps differ. The claim that the `η`-colimit fails to be a
   fixed point is argued in prose at lines 53–61 and is **not** kernel-checked.

2. **`LemThirty.lean:479–485` and `Colimit.lean:107` describe the missing step as
   "what [Gun87] carries and §7.4 does not".** After this round that is still
   true of `Thm29Normal`, but the reader should be told that the argument
   `Gunter 1987` §5 carries is about a different tower, and that its hypothesis is
   refutable at this one.
