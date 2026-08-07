---
round: r0032
from: agent4
to: orchestrator
subject: theorem-16-embedding
date: 2026-0806-21:05
started: 2026-0806-20:45
finished: 2026-0806-21:05
related:
  - plans/r0032-plan-from-orchestrator-to-agent4-theorem-16-embedding.md
  - reports/r0028-report-from-agent3-to-orchestrator-fp-fc-posets.md
---

# r0032 agent4 — Theorem 16's embedding conjunct is false

## Outcome

**Outcome 3 of the plan: the conjunct is refuted.** Theorem 16's second conjunct
— "the inclusion map `i : Fp(D) ↪ (D → D)` is an embedding" — is false as the
paper states it. The refutation is kernel-checked, with a concrete bifinite
witness `D`, and it subsumes outcomes 1 and 2: the paper's sketch cannot be
repaired, because the statement it aims at does not hold.

The refutation is of the **second conjunct only**. The same witness satisfies
Theorem 16's hypothesis and its first conjunct — `TwoMub.thm16_first_conjunct`
is `thm16 isBifinite` applied at the witness — so this is not a complaint about
bifiniteness.

## The definition of "embedding" used, and why

`ScottHom.IsEmbeddingProjectionPair` (`Projection.lean`, r0012), which
transcribes Gunter & Scott §3.1:

> A pair of continuous functions `g : D → E` and `f : E → D` is said to be an
> **embedding–projection pair** (`g` is the embedding and `f` is the projection)
> if they satisfy `f ∘ g = id_D` and `g ∘ f ⊑ id_E`.

So the conjunct asserts: there is a continuous `s : (D → D) → Fp(D)` with
`s ∘ i = id_{Fp(D)}` and `i ∘ s ⊑ id_{D→D}`.

Two reasons this is the right reading, not "order-embedding":

1. The paper's own sketch names `s`. Its last sentence is "the remaining steps
   required to verify that `f ↦ N_f` is a projection are straight-forward" —
   `f ↦ p_{N_f}` is the projection half of the pair.
2. Under the order-embedding reading the conjunct is true by `Iff.rfl`: the order
   on `Fp(D)` **is** the restriction of the pointwise order (`Fp.le_def`), so the
   sketch would have nothing to prove.

The main theorem is stated for an `s` assumed only **monotone**, which is strictly
weaker than continuous, so it refutes every strengthening. The
`IsEmbeddingProjectionPair` phrasing is derived from it as a corollary.

## Exact statements proved, kernel-accepted

All in `ScottDomains/ScottDomains/FinitaryProjectionEmbedding.lean`, namespace
`ScottDomains.FpEmbedding` (per the plan's clash rule). 520 lines, 44
declarations, **0 `sorry`**.

### The refutation

```lean
theorem TwoMub.not_exists_monotone_projection :
    ¬ ∃ s : ScottHom TwoMub TwoMub → ↥(Fp TwoMub),
        Monotone s ∧ (∀ p : ↥(Fp TwoMub), s p.val = p) ∧
          ∀ g : ScottHom TwoMub TwoMub, (s g).val ≤ g

theorem TwoMub.not_isEmbeddingProjectionPair
    (i : ScottHom ↥(Fp TwoMub) (ScottHom TwoMub TwoMub)) (hi : ∀ p, i p = p.val)
    (s : ScottHom (ScottHom TwoMub TwoMub) ↥(Fp TwoMub)) :
    ¬ ScottHom.IsEmbeddingProjectionPair i s
```

### The general obstruction (any cpo, no finiteness)

```lean
theorem isGreatest_of_section (s : ScottHom α α → ↥(Fp α)) (hmono : Monotone s)
    (hsec : ∀ p : ↥(Fp α), s p.val = p) (hproj : ∀ g : ScottHom α α, (s g).val ≤ g)
    (f : ScottHom α α) : IsGreatest {p : ↥(Fp α) | p.val ≤ f} (s f)
```

A projection `s` for the inclusion forces `{p ∈ Fp(D) | p ⊑ f}` to have a
**greatest** element for every continuous `f`. That is the whole reduction; the
witness then shows the greatest element need not exist.

### The criterion — the diagnosis of the paper's sketch

```lean
def stableCompacts (f : ScottHom α α) : Set α := {x ∈ compacts α | x ≤ f x}   -- the paper's S_f

theorem Fp.le_iff_fpBasis_subset_stableCompacts {p : ↥(Fp α)} {f : ScottHom α α} :
    p.val ≤ f ↔ fpBasis p ⊆ stableCompacts f

theorem stableCompacts_val (p : ↥(Fp α)) : stableCompacts p.val = fpBasis p
```

`p ⊑ f` holds **iff `im(p) ∩ K(D) ⊆ S_f`**. Forward because a projection fixes
its basis (`k = p(k) ⊑ f(k)`); backward because `p(x) = ⨆{k ∈ N | k ⊑ x}` and each
such `k` has `k ⊑ f(k) ⊑ f(x)`.

**This is the error in the sketch, stated exactly.** The paper takes `N_f` to be
the least normal set **containing** `S_f`. The criterion requires a normal set
**contained in** `S_f`. The two coincide precisely when `S_f` is normal.
`stableCompacts_val` shows the sketch's other half is fine: when `f` is a finitary
projection, `S_f = im(f) ∩ K(D)`, which is normal, so `N_f = S_f` and
`s(i(p)) = p` holds. r0028's agent3 diagnosed the failure at the level of a
minimal upper bound `m` with `m ⋢ f(m)`; the criterion says why no other `N_f`
repairs it — the *largest normal subposet inside* `S_f` need not exist.

### The witness

`TwoMub` = `{⊥, a, b, m₁, m₂}`: `a, b` incomparable, `m₁, m₂` the two incomparable
minimal upper bounds of `{a, b}`. Machine-checked shape:

```lean
theorem TwoMub.shape :
    (¬ TwoMub.a ≤ TwoMub.b ∧ ¬ TwoMub.b ≤ TwoMub.a) ∧
      (∀ z : TwoMub, (TwoMub.a ≤ z ∧ TwoMub.b ≤ z) ↔ (z = TwoMub.m₁ ∨ z = TwoMub.m₂)) ∧
      (¬ TwoMub.m₁ ≤ TwoMub.m₂ ∧ ¬ TwoMub.m₂ ≤ TwoMub.m₁)
```

It carries a `CompletePartialOrder` (`sSup` branches on **existence of a least
upper bound**, the proposition the field needs — not on directedness, per the
`ScottHom`/`Smash` rule), `Domain` (`domain_of_finite`), and

```lean
theorem TwoMub.isBifinite : IsBifinite TwoMub
```

— `K(D)` is the whole finite type and is normal in itself.

`f = λ x. m₁` (`TwoMub.fConst`), continuous because constant, and

```lean
theorem TwoMub.stableCompacts_fConst :
    stableCompacts fConst = {TwoMub.bot, TwoMub.a, TwoMub.b, TwoMub.m₁}
```

so `S_f` omits `m₂`. Two incomparable finitary projections below `f`:

```lean
def TwoMub.P₁ : ↥(Fp TwoMub)   -- basis {⊥, a, m₁}
def TwoMub.P₂ : ↥(Fp TwoMub)   -- basis {⊥, b, m₁}
theorem TwoMub.p₁_le_fConst : p₁ ≤ fConst
theorem TwoMub.p₂_le_fConst : p₂ ≤ fConst
theorem TwoMub.p₁_incomparable_p₂ : ¬ p₁ ≤ p₂ ∧ ¬ p₂ ≤ p₁
theorem TwoMub.not_isGreatest_below_fConst (q : ↥(Fp TwoMub)) :
    ¬ IsGreatest {p : ↥(Fp TwoMub) | p.val ≤ fConst} q
```

### The mathematical argument, in four lines

A greatest `q ∈ {p ∈ Fp(D) | p ⊑ f}` dominates `p₁` and `p₂`, so `q(a) ⊒ a` and
`q(b) ⊒ b`; `q ⊑ id` gives `q(a) = a`, `q(b) = b`. Monotonicity then puts both `a`
and `b` below `q(m₂)`, and `q ⊑ id` puts `q(m₂) ⊑ m₂`. The only element above `a`
and `b` and below `m₂` is `m₂`, so `q(m₂) = m₂`. But `q ⊑ f` gives
`q(m₂) ⊑ f(m₂) = m₁`, and `m₂ ⋢ m₁`. Contradiction.

Restated without the witness: any normal `N ⊆ K(D)` with `a, b ∈ N` contains
*every* minimal upper bound of `{a, b}` (`IsNormalIn.mem_of_isMinimalUpperBound`,
r0028), hence contains `m₂ ∉ S_f`. So `{⊥, a, m₁}` and `{⊥, b, m₁}` are two
**maximal** normal subposets inside `S_f` with no normal upper bound inside `S_f`,
and by the criterion `{p ∈ Fp(D) | p ⊑ f}` has two maximal elements and no
greatest one.

## `#print axioms`

Every declaration below depends on exactly `[propext, Classical.choice,
Quot.sound]`. **No `sorryAx`.** Verbatim from the build with the `#print axioms`
block in place (`ScottDomains/logs/compile-20260806-205933.agent4.log`):

```
'ScottDomains.FpEmbedding.TwoMub.not_exists_monotone_projection' depends on axioms: [propext, Classical.choice, Quot.sound]
'ScottDomains.FpEmbedding.TwoMub.not_isEmbeddingProjectionPair' depends on axioms: [propext, Classical.choice, Quot.sound]
'ScottDomains.FpEmbedding.TwoMub.not_isGreatest_below_fConst' depends on axioms: [propext, Classical.choice, Quot.sound]
'ScottDomains.FpEmbedding.TwoMub.stableCompacts_fConst' depends on axioms: [propext, Classical.choice, Quot.sound]
'ScottDomains.FpEmbedding.TwoMub.p₁_incomparable_p₂' depends on axioms: [propext, Classical.choice, Quot.sound]
'ScottDomains.FpEmbedding.TwoMub.shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'ScottDomains.FpEmbedding.TwoMub.thm16_first_conjunct' depends on axioms: [propext, Classical.choice, Quot.sound]
'ScottDomains.FpEmbedding.TwoMub.isBifinite' depends on axioms: [propext, Classical.choice, Quot.sound]
'ScottDomains.FpEmbedding.Fp.le_iff_fpBasis_subset_stableCompacts' depends on axioms: [propext, Classical.choice, Quot.sound]
'ScottDomains.FpEmbedding.stableCompacts_val' depends on axioms: [propext, Classical.choice, Quot.sound]
'ScottDomains.FpEmbedding.isGreatest_of_section' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The `#print axioms` block was removed before the final build so the committed
module emits no `info` diagnostics.

## Build

Verbatim final line from `scripts/compile.sh -r r0032`
(`ScottDomains/logs/compile-20260806-210004.agent4.log`):

```
compile: exit 0 · wall 0:01.52 · mem 1669 MiB single / 1810 MiB tree pss / 2470 MiB tree rss · jobs 1069 · diagnostics 0 · lake errors 0 · sorry 1 · other warnings 0
```

Zero errors, zero warnings, 1069 jobs. The one `sorry` is **pre-existing** and not
mine: `ScottDomains/Skeleton/Section6.lean:197`. `grep -c sorry` on
`FinitaryProjectionEmbedding.lean` is **0**.

## Reusable machinery added

Five general lemmas about finite posets, none specific to the witness; any future
finite counterexample in this development needs them.

| # | Declaration | Statement |
| -- | ---- | --- |
| 1 | `exists_upperBound_mem_of_finite` | a finite subset of a nonempty directed set has an upper bound inside that set |
| 2 | `isLUB_of_finite_directed` | a finite nonempty directed set has a greatest element, which is its least upper bound |
| 3 | `isCompactElement_of_finite` | in a finite poset every element is compact |
| 4 | `domain_of_finite` | a finite cpo is a `Domain` |
| 5 | `scottContinuous_of_monotone_of_finite` | on a finite poset, monotone implies Scott continuous |
| 6 | `isFinitaryProjection_of_finite` | on a finite cpo every projection is finitary |

## Files touched

One new file, exactly as the plan allotted:
`ScottDomains/ScottDomains/FinitaryProjectionEmbedding.lean`. No shared module
was modified — in particular `Skeleton/Section6b.lean` and
`FinitaryProjectionPoset.lean` are untouched. The lakefile's
`globs = ["ScottDomains", "ScottDomains.+"]` picks the new module up without an
edit to `ScottDomains.lean`.

## What the orchestrator should decide

1. **`Skeleton/Section6b.lean`'s `thm16` docstring is now out of date.** It says
   the second conjunct "is *not* stated here" because the paper's sketch "does
   not obviously produce the projection half". The truthful replacement is that
   the conjunct is **false**, with a pointer to
   `FinitaryProjectionEmbedding.lean`. That file is agent3's, so I did not edit
   it; the orchestrator should either make that edit on merge or assign it.
2. **Downstream uses of the conjunct.** No *theorem* depends on it. A grep for
   `IsEmbeddingProjectionPair` and `Fp(D) ↪` finds only `Projection.lean`'s
   definition, `UniversalDomain.lean`'s docstring cross-references, and two
   prose mentions: `Skeleton/Section6b.lean:36` (item 1 above) and
   `FinitaryProjectionPoset.lean:25`. The latter cites the conjunct as reason 1
   of 3 for installing the pointwise order on `Fp(D)`. That reason now rests on
   the *order-embedding* reading rather than the embedding–projection one, and
   reasons 2 and 3 there are untouched, so the design choice stands — but the
   sentence should be adjusted. Worth re-running the grep at merge time against
   the other r0032 agents' new files.
3. **`INDEX.md`** is not updated; it is a shared file and three other agents are
   adding modules this round, so I left it to avoid a merge conflict.
4. **The correct statement, if one is wanted.** By
   `Fp.le_iff_fpBasis_subset_stableCompacts`, the conjunct holds for a bifinite
   `D` exactly when for every continuous `f` there is a **greatest** normal
   subposet of `K(D)` contained in `S_f`. That is a genuine condition on `D`, not
   a consequence of bifiniteness; `TwoMub` violates it. Bounded complete domains
   satisfy it (there a bounded pair has a *least* upper bound, so `S_f` is normal
   and `N_f = S_f` works), which is likely the case the paper had in mind. I did
   not prove that; it is the natural next round if a positive statement is
   wanted.

## Nothing unproved

There is no remaining obstacle in this plan's scope. Every claim in the file is
kernel-accepted with no `sorry` and no `sorryAx`.
