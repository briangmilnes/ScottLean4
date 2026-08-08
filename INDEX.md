# ScottLean4 — File Index

The hub for the working files. Jump to any of these by ⌘-click (VS Code),
`C-x C-f` on the path via `ffap` (Emacs), or `M-.` on an `import` (lean4-mode).
See `CLAUDE.md` → "Repository workflow and file index."

## Playground — Lean 4 (Mathlib-enabled) demos and developments

- [Playground/Playground.lean](Playground/Playground.lean) — root aggregator (imports the library modules)
- [Playground/Playground/LambdaSmallStep.lean](Playground/Playground/LambdaSmallStep.lean) — untyped λ-calculus, de Bruijn, **full-β** small-step relation (0 `sorry`)
- [Playground/Playground/LambdaTheorems.lean](Playground/Playground/LambdaTheorems.lean) — metatheory: congruence, normal forms, non-termination; Church–Rosser is the one `sorry`
- [Playground/Playground/LambdaNamed.lean](Playground/Playground/LambdaNamed.lean) — named-variable λ-calculus with α as an equivalence relation
- [Playground/Playground/CartesianClosed.lean](Playground/Playground/CartesianClosed.lean) — a `Category` class and a `CartesianClosed` class specializing it (0 `sorry`)
- [Playground/Playground/HomogeneousFactoring.lean](Playground/Playground/HomogeneousFactoring.lean) — `ring`-certified factorizations of homogeneous polynomials
- [Playground/SageFactor.lean](Playground/SageFactor.lean) — `#eval` calls Sage to factor ℚ[x,y,z] forms; `ring` certifies (standalone scratch)
- [Playground/SageFactorProved.lean](Playground/SageFactorProved.lean) — couples Sage's factoring to a `ring`-checked theorem
- [Playground/ComputabilityDemo.lean](Playground/ComputabilityDemo.lean) — ℚ computable vs ℝ noncomputable, shown via `#eval`

## ScottDomains — Dana Scott's domain theory (Lean 4, Mathlib-enabled)

Separate project from Playground; the domain-theory development lives here.

- [ScottDomains/ScottDomains.lean](ScottDomains/ScottDomains.lean) — root module: commented imports of ωCPOs, CPOs, Scott continuity, the Scott topology, and fixed points
- [ScottDomains/ScottDomains/ExistingTheories.lean](ScottDomains/ScottDomains/ExistingTheories.lean) — clickable `#check` catalog of the Mathlib domain-theory definitions we build on (jump with `M-.` / F12 / ⌘-click)
- [ScottDomains/ScottDomains/WayBelow.lean](ScottDomains/ScottDomains/WayBelow.lean) — the way-below relation `≪` (Gunter & Scott §3.1), absent from Mathlib: definition + 7 theorems, including `x ≪ x ↔ IsCompactElement x` by `Iff.rfl`
- [ScottDomains/ScottDomains/Domain.lean](ScottDomains/ScottDomains/Domain.lean) — algebraic cpo (`IsAlgebraic`), **domain** (`Domain`, with the paper's countable-basis condition), and `BoundedComplete`; `x ≪ y` iff it factors through a compact element; `Domain Prop` as a satisfiability witness
- [ScottDomains/ScottDomains/Powerset.lean](ScottDomains/ScottDomains/Powerset.lean) — the paper's `P N` (p. 9): compact elements of `Set X` are exactly the finite subsets, hence `Domain (Set ℕ)` — the nondegenerate witness for the classes above
- [ScottDomains/ScottDomains/ScottHom.lean](ScottDomains/ScottDomains/ScottHom.lean) — the continuous function space `D → E`: `ScottHom`, the pointwise order, `CompletePartialOrder`, and `BoundedComplete` when `E` is — Theorem 7's first sentence in full
- [ScottDomains/ScottDomains/StepFunction.lean](ScottDomains/ScottDomains/StepFunction.lean) — the single step function `step k e` (Gunter & Scott, Theorem 7): continuity from `k` compact, the adjunction `step k e ≤ f ↔ e ≤ f k`, compactness in `D → E` from `e` compact
- [ScottDomains/ScottDomains/FunctionSpaceDomain.lean](ScottDomains/ScottDomains/FunctionSpaceDomain.lean) — **`D → E` is algebraic**: the step functions form a basis
- [ScottDomains/ScottDomains/CompactFunction.lean](ScottDomains/ScottDomains/CompactFunction.lean) — every compact function is a **finite** join of step functions
- [ScottDomains/ScottDomains/FunctionSpaceCountable.lean](ScottDomains/ScottDomains/FunctionSpaceCountable.lean) — `K(D → E)` is countable, and **Theorem 7**: `D → E` is a bounded complete domain (proved without assuming `D` bounded complete)
- [ScottDomains/ScottDomains/NormalSubposet.lean](ScottDomains/ScottDomains/NormalSubposet.lean) — the normal-subposet relation `N ◁ A` (§3.1) and **Lemma 4**, all four parts
- [ScottDomains/ScottDomains/Projection.lean](ScottDomains/ScottDomains/Projection.lean) — embedding–projection pairs and projections; an embedding is injective, a projection surjective
- [ScottDomains/ScottDomains/FinitaryProjection.lean](ScottDomains/ScottDomains/FinitaryProjection.lean) — finitary projections; `im(p)` as a cpo, and **Lemma 5** — the compacts of `im(p)` are `im(p) ∩ K(D)`
- [ScottDomains/ScottDomains/NormalProjection.lean](ScottDomains/ScottDomains/NormalProjection.lean) — `p_N(x) = ⨆{y ∈ N | y ⊑ x}`: continuous, a projection, and `im(p_N) ∩ K(D) = N`
- [ScottDomains/ScottDomains/Theorem6.lean](ScottDomains/ScottDomains/Theorem6.lean) — **Theorem 6**: normal substructures of `K(D)` correspond to the finitary projections
- [ScottDomains/ScottDomains/FixedPoint.lean](ScottDomains/ScottDomains/FixedPoint.lean) — **Theorem 1**: `⨆ₙ fⁿ(⊥)` is the least fixed point of a continuous `f` (Kleene, not Knaster–Tarski)
- [ScottDomains/ScottDomains/UniformFixedPoint.lean](ScottDomains/ScottDomains/UniformFixedPoint.lean) — **Theorem 3**, uniqueness half: every uniform fixed-point operator is `fix`
- **`Kleene/`** — §2's calculus, the part the paper states in prose: [FixContinuous.lean](ScottDomains/ScottDomains/Kleene/FixContinuous.lean) (`fix_D : (D → D) → D` is continuous, and `fixHom` bundles it) · [Uniform.lean](ScottDomains/ScottDomains/Kleene/Uniform.lean) (**Theorem 3's existence half**: `fix` *is* uniform, so `∃! F, F.IsUniform`) · [Extension.lean](ScottDomains/ScottDomains/Kleene/Extension.lean) (`f* : P S → P T`, monotone, union-preserving, continuous) · [Factorial.lean](ScottDomains/ScottDomains/Kleene/Factorial.lean) (§2.2's `N⊥`, `F` continuous but not strict, and `fix(F) = fact`) · [Grammar.lean](ScottDomains/ScottDomains/Kleene/Grammar.lean) (§2.2's three context-free grammars, their least solutions identified with the languages) · [Graph.lean](ScottDomains/ScottDomains/Kleene/Graph.lean) (the paper's `G_f`, its recovery equation, and its countability for `f : P N → P N`)
- [ScottDomains/ScottDomains/Product.lean](ScottDomains/ScottDomains/Product.lean) — `D × E` as a cpo (the one construction needing no case split) and **Lemma 8** parts 1–3
- [ScottDomains/ScottDomains/Currying.lean](ScottDomains/ScottDomains/Currying.lean) — **Lemma 8.4**: `D → (E → F) ≅ (D × E) → F`, completing Lemma 8
- [ScottDomains/ScottDomains/EffectivePresentation.lean](ScottDomains/ScottDomains/EffectivePresentation.lean) — §3.2's effective presentation: the basis enumeration with its two decidability conditions
- [ScottDomains/ScottDomains/ComputableFunction.lean](ScottDomains/ScottDomains/ComputableFunction.lean) — the paper's **computable function**, on Mathlib's `REPred` (r0031)
- [ScottDomains/ScottDomains/Effective/Powerset.lean](ScottDomains/ScottDomains/Effective/Powerset.lean) — §3.2 instantiated: an effective presentation of `P N` on the binary expansion, with both conditions decided by bitwise-or (r0041)
- [ScottDomains/ScottDomains/Effective/FunctionSpace.lean](ScottDomains/ScottDomains/Effective/FunctionSpace.lean) — **Theorem 7's second and third sentences**: effective presentations of `D → E` and `D ⊸ E`, plus the measurement that the `DecidablePred` reading gives *every* domain one (r0041)
- [ScottDomains/ScottDomains/Lift.lean](ScottDomains/ScottDomains/Lift.lean) — the lift `D⊥` as a cpo, on Mathlib's `WithBot`
- [ScottDomains/ScottDomains/StrictHom.lean](ScottDomains/ScottDomains/StrictHom.lean) — the strict function space `D →⊥ E` as a cpo
- [ScottDomains/ScottDomains/Smash.lean](ScottDomains/ScottDomains/Smash.lean) — §4.3's smash product `D ⊗ E`; its `sSup` branches on **landing in `NonBotPair`**, not on directedness — see the r0027 defect note in the module docstring
- [ScottDomains/ScottDomains/CoalescedSum.lean](ScottDomains/ScottDomains/CoalescedSum.lean) — §4.4's coalesced sum `D + E` as a cpo, guarded the same way
- [ScottDomains/ScottDomains/Bifinite.lean](ScottDomains/ScottDomains/Bifinite.lean) — §6.1's **Plotkin order** and **bifinite** domain
- [ScottDomains/ScottDomains/MinimalUpperBounds.lean](ScottDomains/ScottDomains/MinimalUpperBounds.lean) — minimal upper bounds, the operator `U` and its iterate `U^∞`, and a characterization of the Plotkin order the paper does not state
- [ScottDomains/ScottDomains/JungSFP.lean](ScottDomains/ScottDomains/JungSFP.lean) — steps 2 and 3 of **Theorem 18**: Jung 1989's **Lemma 2.13**, **Theorem 2.14** (bifinite or algebraic L-domain) and **Lemma 2.17** (the uncountable family `f_S`), plus his Proposition 1.9 and the bridge between minimality in `K(D)` and in `D`
- [ScottDomains/ScottDomains/JungNets.lean](ScottDomains/ScottDomains/JungNets.lean) — step 1 of **Theorem 18**: Jung 1989's **Theorem 1.37** (a dcpo with continuous function space is *bicomplete*) named as a `Prop` remainder, with the implication Jung leaves unproved — bicomplete ⟹ **property m**, by Zorn downwards — proved in full, discharging `JungSFP.lemma217`'s hypothesis by application
- [ScottDomains/ScottDomains/JungFinite.lean](ScottDomains/ScottDomains/JungFinite.lean) — step 4 and the assembly of **Theorem 18**: Jung 1989's **Lemma 1.29** (property M at pairs gives it at every finite set), **König's lemma** graded by `ℕ` in place of his Rado Selection Theorem, **Lemma 2.2** (`U^∞(A)` finite), and `thm18_of_propertyM` — Theorem 18 with his Theorem 1.37 and Corollary 1.36 as the two named open hypotheses
- [ScottDomains/ScottDomains/FinitaryProjectionPoset.lean](ScottDomains/ScottDomains/FinitaryProjectionPoset.lean) — `Fp(D)` and `Fc(D)` as posets; **Theorem 16**'s algebraic-lattice conjunct and **Lemma 20**
- [ScottDomains/ScottDomains/IdealCompletion.lean](ScottDomains/ScottDomains/IdealCompletion.lean) — **Theorem 11**: the ideal completion of a countable pre-order is a domain, and every domain so arises
- [ScottDomains/ScottDomains/UniversalDomain.lean](ScottDomains/ScottDomains/UniversalDomain.lean) — **Theorem 22** and **Lemma 23**: closures onto `P(ℕ)`, and *representable* as the paper defines it
- [ScottDomains/ScottDomains/RecursiveDomain.lean](ScottDomains/ScottDomains/RecursiveDomain.lean) — recursive domain equations, two formalizations of *universal domain*, and **Theorem 21** — with it, `D ≅ (D → D)`
- [ScottDomains/ScottDomains/Universality.lean](ScottDomains/ScottDomains/Universality.lean) — **Lemma 24** and **Theorem 25**: `P N` is universal, proved at cpo strength
- [ScottDomains/ScottDomains/ContinuousAlgebra.lean](ScottDomains/ScottDomains/ContinuousAlgebra.lean) — **Theorem 12**: the continuous algebra of signature (2), the theories `T♮`/`T♯`/`T♭`, and initiality of each powerdomain with existence *and* uniqueness
- [ScottDomains/ScottDomains/FinitaryProjectionEmbedding.lean](ScottDomains/ScottDomains/FinitaryProjectionEmbedding.lean) — **Theorem 16's embedding conjunct refuted**, kernel-checked, with the exact error in the paper's `S_f` sketch
- [ScottDomains/ScottDomains/ContinuousConstruction.lean](ScottDomains/ScottDomains/ContinuousConstruction.lean) — a continuous-function constructor needing neither bounded completeness nor algebraicity, and the reduction of Theorem 18's remaining cases
- [ScottDomains/ScottDomains/Powerdomain/BoundedComplete.lean](ScottDomains/ScottDomains/Powerdomain/BoundedComplete.lean) — **Lemma 13**, and the live witness lemmas for the repaired `idealSup`
- [ScottDomains/ScottDomains/Powerdomain/Universal.lean](ScottDomains/ScottDomains/Powerdomain/Universal.lean) — the product operator representable over `P N`, the hypothesis Lemma 24 needed
- [ScottDomains/ScottDomains/Universality.lean](ScottDomains/ScottDomains/Universality.lean) — §7.2's **Lemma 24** and **Theorem 25**: a non-trivial `D` with `D ≅ D × D ≅ D → D`, the image of a closure on `P(ℕ)`
- [ScottDomains/ScottDomains/Combinator.lean](ScottDomains/ScottDomains/Combinator.lean) — §7.2's **Theorem 26**: for every signature of positive arities, combinations `F₁…F_n` over `S`, `K`, `fst`, `snd` into which every continuous algebra on a retract of `D` embeds; and why the theorem is false when an arity is `0`
- [ScottDomains/ScottDomains/CombinatorRep.lean](ScottDomains/ScottDomains/CombinatorRep.lean) — §7.3's **Lemma 28** over an abstract carrier: `→`, `×` and `()⊥` representable from `Retracts U V` alone, with the counterexample refuting the closure reading of `⊗` and `⊕`
- [ScottDomains/ScottDomains/BifiniteUniversal.lean](ScottDomains/ScottDomains/BifiniteUniversal.lean) — §7.4's `M(A)` and `D⁺`, **Theorem 29's first sentence** (`D` bifinite ⟹ `D⁺` bifinite), and the two kernel-checked defects in the paper's printed pre-ordering, repaired against Gunter 1987
- [ScottDomains/ScottDomains/PRepresentable.lean](ScottDomains/ScottDomains/PRepresentable.lean) — §7.3's **p-representability** over `Fp(U)`, separated from `IsRepresentable` over `Fc(U)` by `eq_id_of_mem_Fp_of_mem_Fc`; the prerequisite for Lemma 30
- [ScottDomains/ScottDomains/Colimit.lean](ScottDomains/ScottDomains/Colimit.lean) — §7.4's chain `I ⊴ I⁺ ⊴ I⁺⁺ ⊴ ⋯`, its ω-colimit `A∞`, and **`V`** with `Domain V`, `IsBifinite V` and **`V ≅ V⁺`**; plus the kernel-checked defect that the connecting map cannot be §7.4's printed `x ↦ (x, {x})`, and the statements of Theorem 29's second sentence and Lemma 30's `→` conjunct, which `V` makes type-correct for the first time
- [ScottDomains/ScottDomains/Powerdomain/Hoare.lean](ScottDomains/ScottDomains/Powerdomain/Hoare.lean) · [Smyth.lean](ScottDomains/ScottDomains/Powerdomain/Smyth.lean) · [Plotkin.lean](ScottDomains/ScottDomains/Powerdomain/Plotkin.lean) — §5.2's three powerdomains, each `IdealCompletion (Pf K(D))` under its pre-order
- [ScottDomains/ScottDomains/Dyadic.lean](ScottDomains/ScottDomains/Dyadic.lean) — §7.3's universal domain `U`, the ideal completion of the dyadic half-open intervals under superset, with `K(U)` and bounded completeness; **Theorem 27** proved from `IsNormallyRepresented`, the paper's Boolean-algebra paragraph named as one `Prop`
- [ScottDomains/ScottDomains/Atomless.lean](ScottDomains/ScottDomains/Atomless.lean) — §7.3's Boolean-algebra paragraph, proved: `psi` embeds any countable poset with a least element and bounded joins onto a normal subposet of `U₀`, by a dyadic branch construction that uses neither Vaught's theorem nor a Boolean algebra; **Theorem 27 unconditionally** as `Atomless.thm27`
- **`Skeleton/`** — fixed statements proved in parallel, one file per agent: [Lemma10.lean](ScottDomains/ScottDomains/Skeleton/Lemma10.lean) (bounded completeness under the operators) · [Lemma17.lean](ScottDomains/ScottDomains/Skeleton/Lemma17.lean) (bifiniteness under them) · [Section6.lean](ScottDomains/ScottDomains/Skeleton/Section6.lean) (Prop 15, Lem 19, and Thm 18, still open) · [Section6b.lean](ScottDomains/ScottDomains/Skeleton/Section6b.lean) (Thm 16, Lem 20) · [Sum.lean](ScottDomains/ScottDomains/Skeleton/Sum.lean) (the `⊕` and `⊗` conjuncts) · [Recovered.lean](ScottDomains/ScottDomains/Skeleton/Recovered.lean) (Lemma 9 and Theorem 14, recovered from the PDF and both proved)
- [ScottDomains/ScottDomains/SFP.lean](ScottDomains/ScottDomains/SFP.lean) — **Theorem 14**, Plotkin's SFP characterization, in both directions: gap 2's bridge `im(p_N) = N` for finite normal `N`, the two finite-directed-set lemmas, `im(p) ⊆ K(D)` for a finite image, and the constant-`⊥` projection that makes `M` nonempty
- [ScottDomains/docs/StatementRecovery.md](ScottDomains/docs/StatementRecovery.md) — how Lemma 9 and Theorem 14 were recovered by decoding the paper's Type 3 fonts, and the two misprints that decoding exposed
- [ScottDomains/lakefile.toml](ScottDomains/lakefile.toml) — project config (pinned Mathlib v4.32.2)
- [ScottDomains/README.md](ScottDomains/README.md) — what the project develops, and the source paper
- [ScottDomains/papers/Gunter Scott 1990.pdf](ScottDomains/papers/Gunter%20Scott%201990.pdf) — **Gunter & Scott, "Semantic Domains" (HTCS Vol. B, 1990)** — the source paper (copy from D. Scott)
- [ScottDomains/papers/Gunter 1987 Universal Profinite Domains.pdf](ScottDomains/papers/Gunter%201987%20Universal%20Profinite%20Domains.pdf) — **Gunter, "Universal Profinite Domains" (Inf. & Comp. 72, 1987)** — carries the `A⁺` construction that §7.4 cites the unobtainable [Gun87] manuscript for; p. 23 attributes it to Scott
- [ScottDomains/papers/Gunter 1985 A Universal Domain Technique for Profinite Posets.pdf](ScottDomains/papers/Gunter%201985%20A%20Universal%20Domain%20Technique%20for%20Profinite%20Posets.pdf) — the ICALP'85 predecessor of the above
- [scripts/mpair-stages.py](scripts/mpair-stages.py) — enumerates `I, I⁺, I⁺⁺, I⁺⁺⁺` under two candidate readings of §7.4's pre-ordering; the paper's stated sizes 1, 2, 5, 20 select one and refute the other
- [ScottDomains/docs/PaperInventory.md](ScottDomains/docs/PaperInventory.md) — inventory of the paper's definitions & theorems (the work list) — [.pdf](ScottDomains/docs/PaperInventory.pdf)
- [ScottDomains/docs/Performance.md](ScottDomains/docs/Performance.md) — what a whole validation costs: time, memory, and how far the build parallelizes — [.pdf](ScottDomains/docs/Performance.pdf)
- [ScottDomains/plans/](ScottDomains/plans) · [ScottDomains/reports/](ScottDomains/reports) · [ScottDomains/prompts/](ScottDomains/prompts) — GRASE round artifacts: plans addressed to each agent, their reports back, and the session transcript one file per interaction
- ScottDomains/docs/SymbolMap — reference sheet: PDF garbling→Unicode (reading the paper) + symbol↔Unicode↔Lean input↔display (reading/writing the Lean) — [.tex](ScottDomains/docs/SymbolMap.tex) · [.pdf](ScottDomains/docs/SymbolMap.pdf)

## Notes (LaTeX source + compiled PDF)

- Category theory in Mathlib — [.tex](notes/CategoryTheoryInMathlib.tex) · [.pdf](notes/CategoryTheoryInMathlib.pdf)
- Scott domains in Lean/Mathlib — [.tex](notes/ScottDomainsInLean.tex) · [.pdf](notes/ScottDomainsInLean.pdf)
- Scott–Strachey criticisms — [.tex](notes/ScottStracheyCriticisms.tex) · [.pdf](notes/ScottStracheyCriticisms.pdf)
- Scott–Strachey criticisms — Gemini Deep Research report, re-typeset from a share link (prints empty in-browser) — [.tex](notes/ScottStracheyGeminiReport.tex) · [.pdf](notes/ScottStracheyGeminiReport.pdf)
- Dana Scott — biography — [.tex](notes/DanaScottBio.tex) · [.pdf](notes/DanaScottBio.pdf)
- Homogeneous factorization — [.tex](notes/HomogeneousFactorization.tex) · [.pdf](notes/HomogeneousFactorization.pdf)

## Polynomials

- Factoring: algorithms, representations, Mathlib — [.tex](polynomials/PolynomialFactoring.tex) · [.pdf](polynomials/PolynomialFactoring.pdf)
- Gemini's note — multivariate factorization over ℚ — [.tex](polynomials/Multivariate_Factorization_Notes.tex) · [.pdf](polynomials/Multivariate_Factorization_Notes.pdf)
- Kaltofen survey, *Polynomial Factorization 1987–1991* — [.pdf](polynomials/PolynomialFactorization.pdf)

## Docs

- [docs/Curriculum.md](docs/Curriculum.md)
- [docs/DanaScottPapers.md](docs/DanaScottPapers.md)
- [docs/ForDana.md](docs/ForDana.md)
- [docs/PapersToLeanStatus.md](docs/PapersToLeanStatus.md)
- [docs/ProofsAndTextInventory.md](docs/ProofsAndTextInventory.md)
- [docs/SoftwareInventory.md](docs/SoftwareInventory.md)

## Mathlib — category theory reading paths (pinned v4.32.2 snapshot)

- [mathlib/Mathlib/CategoryTheory/Category/Basic.lean](mathlib/Mathlib/CategoryTheory/Category/Basic.lean) — `Quiver` → `CategoryStruct` → `Category`
- [mathlib/Mathlib/CategoryTheory/Functor/Basic.lean](mathlib/Mathlib/CategoryTheory/Functor/Basic.lean) — functors
- [mathlib/Mathlib/CategoryTheory/NatTrans.lean](mathlib/Mathlib/CategoryTheory/NatTrans.lean) — natural transformations
- [mathlib/Mathlib/CategoryTheory/Monoidal/Closed/Cartesian.lean](mathlib/Mathlib/CategoryTheory/Monoidal/Closed/Cartesian.lean) — cartesian closed (CCC)

(For live goals / `M-.` into Mathlib, open the built copy under `Beeson/lean4/.lake/packages/mathlib/…`.)

## Scripts

- [scripts/gitcp.sh](scripts/gitcp.sh) — one-shot stage + commit + rebase + push (use this for all commits)
- [scripts/tex2pdf.sh](scripts/tex2pdf.sh) — compile a `.tex` to PDF (XeLaTeX, handles Unicode/Lean symbols)
- [scripts/lean2tex.sh](scripts/lean2tex.sh) — Lean → LaTeX helper
