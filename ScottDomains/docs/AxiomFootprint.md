# Axioms: what this development assumes

Dana Scott asked, of the Iwamura and Markowsky material: *no axiom of choice?
uses excluded middle? are we still using proof by contradiction somewhere?*

Short answers, each measured rather than recalled:

1. **We use the axiom of choice.** Every proof in the package does.
2. **We use excluded middle** — but not as a separate assumption. In Lean it is a
   *theorem* derived from choice, so it never appears in a footprint.
3. **Yes, proof by contradiction appears**: 51 `by_contra` sites across 16 of the
   100 modules.

The rest of this note says exactly what those three sentences mean, and — the
part that matters — what they do **not** mean.

## Lean's three axioms

Lean 4's kernel implements a dependent type theory with no axioms at all. Mathlib
admits exactly three on top of it, and `#print axioms` reports which of the three
a declaration's proof term actually reaches:

| # | Axiom | Statement | What it buys |
| -- | ----- | --------- | ------------ |
| 1 | `propext` | `(a ↔ b) → a = b` | propositional extensionality: equivalent propositions are equal |
| 2 | `Classical.choice` | `Nonempty α → α` | **the axiom of choice**, in its global-choice form |
| 3 | `Quot.sound` | `Quot.mk r a = Quot.mk r b` when `r a b` | quotient types compute |

A fourth constant, `sorryAx`, is what an incomplete proof reports. It is not an
axiom anyone adopts; it is the marker of a hole.

**`Classical.choice` is the axiom of choice.** There is no separate `Choice`
axiom to look for and no weaker form in play — Lean's is the strong,
type-theoretic version that extracts an inhabitant from a mere `Nonempty`
witness. So the answer to "no axiom of choice?" is: we use it, everywhere.

## Excluded middle is not an independent knob

This is the part worth stating precisely, because outside type theory the two
assumptions are usually varied independently.

In Lean, `Classical.em : ∀ p : Prop, p ∨ ¬p` is **proved, not assumed**. The
derivation is **Diaconescu's theorem** (Radu Diaconescu, 1975): choice together
with propositional extensionality and function extensionality yields excluded
middle. Lean's `Classical.em` follows exactly that route — `funext` is itself a
consequence of `Quot.sound`, so the three axioms in the table above deliver
classical logic outright.

The consequence for reading any footprint in this project: **excluded middle
never appears in `#print axioms` output, because it is not an axiom.** Its use is
already accounted for by `Classical.choice`. A declaration reporting
`[propext, Classical.choice, Quot.sound]` may be using choice, or excluded
middle, or only extensionality plus a quotient — the report does not separate
them.

Correspondingly, one cannot ask this development for "choice-free but classical"
or "constructive but with choice." Against a Mathlib base those combinations are
not available.

## What we measured

`scripts/axioms.sh` runs `#print axioms` against the built `.olean` files, so it
reports the elaborated term rather than anything a source comment claims.

### The four declarations Dana asked about

| # | Declaration | Axioms |
| -- | ---------- | ------ |
| 1 | `Iwamura.exists_chain_directed_cover` | `[propext, Classical.choice, Quot.sound]` |
| 2 | `Iwamura.hasChainSuprema_iff_hasDirectedSuprema` | `[propext, Classical.choice, Quot.sound]` |
| 3 | `Iwamura.hasDirectedSuprema_of_hasChainSuprema` | `[propext, Classical.choice, Quot.sound]` |
| 4 | `PropertyM.thm18_of_cor136` | `[propext, Classical.choice, Quot.sound]` |

### And the rest of the package

Every declaration audited across all rounds reports the same three. The footprint
is uniform: no declaration reaches fewer axioms, and none reaches `sorryAx` —
the package's `sorry` count is **0**, in 0 files, with the 38 remaining string
matches all docstring prose.

That uniformity is why `#print axioms` earns its place in this project's
tooling: as a **hole detector**, not as a measurement of logical strength. It
tells us no proof is secretly incomplete. It tells us almost nothing about how
much classical reasoning any particular proof needed.

### Source-level classical reasoning

`scripts/classical-usage.sh` measures the source rather than the footprint,
because the two answer different questions.

| # | Construct | Occurrences | Files |
| -- | -------- | ----------: | ----: |
| 1 | `by_cases` | 159 | 27 |
| 2 | `absurd` | 171 | 44 |
| 3 | `by_contra` | 51 | 16 |
| 4 | `open Classical` | 45 | 28 |
| 5 | `Classical.dec` | 17 | 4 |
| 6 | `not_not` | 7 | 3 |
| 7 | `exfalso` | 3 | 2 |
| 8 | `Classical.em` written explicitly | 0 | 0 |
| 9 | `Classical.byContradiction` written explicitly | 0 | 0 |
| 10 | `Classical.choice` written explicitly | 0 | 0 |

Rows 8–10 are zero: no proof in the package invokes choice or excluded middle by
name. The `Classical.choice` strings that a naive `grep` finds — 130 of them —
are all in docstrings recording prior `#print axioms` audits, chiefly
`IdealCompletion.lean` and `ContinuousAlgebra.lean`.

Reading the rest honestly:

* **`absurd` (171) is constructive.** It is `a → ¬a → b`, i.e. ex falso. Its
  presence says nothing about classicality. It is the largest row and the least
  informative.
* **`by_cases` (159) is constructive when the proposition is decidable** and
  classical otherwise, where it silently inserts `Classical.em` via
  `Classical.propDecidable`. We have not separated the two populations; doing so
  needs elaboration data, not `grep`.
* **`by_contra` (51) is the genuinely classical tactic** — assume `¬P`, derive
  `False`, conclude `P`. This is the row that answers Dana's last question
  affirmatively. It is concentrated: `Isomorphism/Copair.lean` and
  `Isomorphism/StrictCurry.lean` account for 7 of the sites between them, mostly
  discharging non-emptiness side conditions.
* **`Classical.dec` (17)** is where we take decidability classically rather than
  exhibiting an algorithm. This one has a known consequence in the development
  and it is not cosmetic — see the warning below.

## Where choice is essential, and where it is incidental

The distinction the footprint cannot draw, but the mathematics can.

**Iwamura's lemma genuinely needs choice.** The statement — every infinite
directed set `D` is the union of an increasing well-ordered family of directed
subsets each of cardinality strictly less than `|D|` — is proved by well-ordering
`D` in order type `|D|` and recursing transfinitely. The well-ordering theorem is
equivalent to AC over ZF. This is not an artifact of how we formalized it; it is
what the theorem is about.

**Markowsky's theorem inherits that.** "Every chain-complete poset is
directed-complete" is proved through Iwamura by transfinite induction on
cardinality, which is why the two arrived in the same module. Our
`hasChainSuprema_iff_hasDirectedSuprema` follows that route.

A caution on how far to push this: we have shown our *proof* uses choice, and
that the standard argument uses choice essentially. We have **not** shown the
theorem is unprovable without it. Establishing that a result is not a theorem of
ZF is an independence argument — it requires a model, and nothing in this
development or in `#print axioms` constitutes one. The literature on
choice-principle strength in domain theory is the place to settle it; we have
not consulted it and should not imply otherwise.

**By contrast, most of the package's choice use is incidental.**
`IdealCompletion.lean`'s own docstring records that `Classical.choice` enters
there "only through `idealSup`'s `dite`" — a case split on a decidable-in-
principle condition, taken classically for convenience. Everything downstream
inherits the axiom from that single spot. Removing it is plausible; nothing
depends on it mathematically.

So the uniform footprint hides a real gradient: two theorems that need choice,
and roughly 1,770 declarations that report it because they sit downstream of a
`dite` and a classical Mathlib base.

## The measurement's ceiling

**A footprint is an upper bound on non-constructive content, not a measurement of
it.** `#print axioms` walks the transitive closure of a proof term. Any Mathlib
lemma anywhere in that closure that happened to be proved classically puts
`Classical.choice` in the report, whether or not our argument needed it. Mathlib
is classical throughout and makes no attempt to be otherwise.

To answer "does *this mathematics* require choice" one would have to rebuild the
development over a constructive base and see what fails — a different project,
not a different script. We are not in a position to make constructivity claims
about any individual theorem here, and this document should not be cited as
though we were.

## One consequence that is not cosmetic

`Classical.dec` interacts with the effective-domain material in a way worth
flagging, because it has already produced a misleading result.

`EffectivePresentation` carries decidability fields. Because `Classical.dec`
supplies a `Decidable` instance for any proposition at no cost, **every domain
has an `EffectivePresentation` as currently rendered** —
`Effective.nonempty_effectivePresentation` proves exactly that. The structure is
therefore vacuous: two of r0043's `S+P` rows for Theorem 7 are proved through it
with their hypotheses unused.

The distinction the effective material actually needs is between `Decidable`
(data, freely obtainable classically) and `ComputablePred` (a genuine
computability claim). `RecursivePresentation`, which adds `RecursiveLE` and
`RecursiveNormal`, is the non-vacuous form; it is deliberately uninstantiated.

This is the sharpest illustration of the theme: the axiom footprint is uniform
and uninformative, while the *choice of how to encode decidability* silently
determined whether a theorem says anything.

## Reproducing these numbers

    scripts/axioms.sh ScottDomains.Iwamura.exists_chain_directed_cover …
    scripts/classical-usage.sh

The second writes `analyses/classical-usage.<stamp>.orchestrator.log` with the
full table and every `by_contra` call site. Note that a bare `grep` for `em `
returns 2,784 hits across 97 files; they are matches inside "them", "system" and
"problem" in prose, and the figure is meaningless. It is excluded above.
