# Ericson — Lars Ericson's Lean 4 formalizations of Dana Scott's papers

Vendored checkouts of four Lean 4 developments by **Lars Ericson**
(Catskills Research), each a formalization of one of Dana Scott's papers, plus
the interconversion between them. They sit here as *external reference material*
alongside this project's own `ScottDomains/`, which formalizes Gunter & Scott,
*Semantic Domains* (HTCS Vol. B, 1990).

The checkouts are **git-ignored** — this README and the build tooling are the
only tracked files. Re-fetch with `scripts/ericson-clone.sh`.

## The four repositories

| # | Repository | Scott paper | Lean files | Lean lines |
| -- | ---------- | ----------- | ---------: | ---------: |
| 1 | [scott1972](https://github.com/catskillsresearch/scott1972) | *Continuous Lattices* (1972) | 11 | 4,478 |
| 2 | [scott1980](https://github.com/catskillsresearch/scott1980) | *Lambda Calculus: Some Models, Some Philosophy* (1980) | 236 | 88,697 |
| 3 | [scott1982](https://github.com/catskillsresearch/scott1982) | *Domains for Denotational Semantics* (1982) | 41 | 12,088 |
| 4 | [scott_models](https://github.com/catskillsresearch/scott_models) | the interconversion between the three | 11 | 2,024 |

**107,287 lines of Lean across 299 files.**

## Ericson's account of the work

From his letter to Dana Scott, quoted for the design intent it records:

> I wrote 4 formalizations of your papers, for 1972, 1980, 1982, and an
> interconversion between them. I put the first in arXiv. The second was rejected
> by arXiv cs.LO moderators — 1500 pages of Lean code, and maybe they didn't like
> the AI proof notes. All of the Lean formalizations rigorously do every
> definition, theorem and example in your notes. Where there are "it is clear
> that" statements, these become "Factoids" that also get separate proofs. I have
> put them all in HAL.science and given up on arXiv because HAL.science, a French
> repository, may be more forgiving for long formalizations. Also the 1980 one
> may have been longer because I was switching around between models for economic
> reasons and the less capable models write longer proofs.

> Basically I viewed the whole project as 3 different ways of modeling untyped
> lambda calculus — so each is an independent modelling approach, using more or
> less classical logic (law of excluded middle, axiom of choice), and since all 3
> have the same goal, they should be interconvertible, and they are.

On possible extensions:

> In addition as extensions I guess that the equilogical spaces approach is in the
> same family and you could add that. Separately, 1967–1974 you were working on a
> model of axiomatic set theory and then later on in the 1990s you collaborated on
> algebraic set theory. So two different approaches for a topology influenced
> model of set theory. That's another related journey to formalize in Lean 4.

On Mathlib and on downstream reuse:

> I haven't approached Mathlib people about putting this into Mathlib. A final
> version that you approve of would definitely be appropriate for Mathlib. I
> should note that the 1972 and 1980 Lean codes from above repos were
> automatically copied into another project called
> [Lean Pool](https://github.com/Vilin97/lean-pool/tree/main/LeanPool/DomainTheory)
> run by Vasily Ilin. I think the goal of Lean Pool is just to get working Lean
> code as a training base for Axiom Math, which is a commercial project. They took
> the code and have been automatically "golfing" it, which is a Lean term for
> reducing the size of proofs. This reduction tends to make proofs more opaque
> because they will reduce a sequence of steps to `simp all`, which relies on the
> accumulated facts in Lean and Lean tactic automation to complete the proof.
> `simp all` proofs can be traced down to individual steps but that takes
> additional work.

Two points there bear directly on how this project reads the code. **"Factoid"
is Ericson's name for a step the paper asserts without proof** — an "it is clear
that" — given its own named theorem. That is the same problem this project
handles with `Prop`-valued claims and the `sorry`-invisible-claim census in
`ScottDomains/analyses/`, reached independently and named differently. And the
**golfing caveat is a warning about provenance**: the Lean Pool copies are not
these repositories, and a `simp_all` there may stand where a traced argument
stands here.

## Building

All four pin **toolchain `v4.30.0`** and **Mathlib revision
`c5ea00351c28e24afc9f0f84379aa41082b1188f`** — identical across the set. One
`.lake/packages` therefore serves all four, which matters: that directory is
**7.1 GiB** and the disk had 19 GiB free when these were assembled.
`scripts/ericson-build.sh` symlinks the shared copy from `scott1972` and builds
the named project:

    scripts/ericson-build.sh scott_models

Lake reads `.lake/packages` and writes only `.lake/build`, so sharing is safe.
The real per-project cost is the local build output.

### Measured

| # | Repo | Status | Jobs | Errors | Warnings | `sorry` | Disk |
| -- | --- | ------ | ---: | -----: | -------: | ------: | ---: |
| 1 | scott_models | built | 959 | 0 | 9 | **0** | 26 MiB |
| 2 | scott1972 | pre-built | — | — | — | — | 7.2 GiB incl. packages |
| 3 | scott1980 | not built | — | — | — | — | projected ~1.1 GiB |
| 4 | scott1982 | not built | — | — | — | — | projected ~155 MiB |

Rows 3–4 project linearly from row 1's 26 MiB for 2,024 lines; treat them as an
order of magnitude, not a measurement. Logs are written to `Ericson/logs/`
following the project `LoggingStandard`.

`sorry` is **0** in scott_models, in both the build output and the source — the
claim that the formalizations are complete holds for the one measured so far.

Six of scott_models' nine warnings are `automatically included section
variable(s) unused` — theorems carrying `[TopologicalSpace X]` or
`[TopologicalSpace Y]` binders they never use. That is the same
over-hypothesization defect class `ScottDomains/analyses/specification-defects…`
measured 26 instances of in this project's own code. Lean's linter reports it
automatically when the binder is a *section variable*; it does not when the
binder is explicit, which is why the r0044 sweep needed a deletion probe.

## Relation to this project

`ScottDomains/docs/ContinuousLatticeComparison.md` compares Ericson's 1972
continuous-lattice layer against this project's. The developments are
independent: different papers, different decades of Scott's work, and different
formalization strategies.
