# Papers → Lean: Download & Formalization Status

**Status: COMPLETE.** All 38 extractible Dana Scott papers formalized; the whole
`ScottLean` library compiles under a single `lake build`.

## Summary metrics

| Metric | Value |
|--------|------:|
| Scott papers downloaded (PDF) | **41 / 41** |
| — with extractible text layer | 38 |
| — scanned image only (need OCR) | 3 |
| Other papers downloaded (Coquand, CADE, LPTP, PFPL) | 4 |
| Dana Scott CMU Mathematica notebooks (Wayback) | 37 |
| **Lean modules generated & building** | **38** |
| — compiling **clean** (0 `sorry`) | 16 |
| — compiling **with `sorry`** | 22 |
| **Total proof holes (`sorry` terms)** | **100** |
| Whole-project `lake build` | **PASS** (Lean 4.32.2, 42 jobs, 0 errors) |

`sorry` counts are actual terms with comments stripped. **Caveat:** a few modules
(esp. the probabilistic/philosophy batch) state unproven results as `Prop`-valued
*target definitions* instead of `theorem … := sorry`, so they show 0 `sorry` yet
still contain open obligations. The "clean" count is therefore an upper bound on
"fully proved"; treat `sorry` count as a lower bound on remaining proof work.

## Per-module table (most proof holes first)

| Module | Lines | Proof holes | Status |
|--------|------:|------------:|--------|
| `Scott1970ExtendingTopologicalInterpretationII.lean` | 121 | 14 | with-sorry |
| `Scott1959ConstructingModels.lean` | 227 | 8 | with-sorry |
| `Scott1980RelatingTheoriesLambdaCalculus.lean` | 439 | 7 | with-sorry |
| `Scott1961MeasurableCardinals.lean` | 166 | 6 | with-sorry |
| `Scott1964InvariantBorelSets.lean` | 183 | 6 | with-sorry |
| `Scott1965DenumerablyLongFormulas.lean` | 192 | 6 | with-sorry |
| `Scott1958ConvergentSequences.lean` | 225 | 5 | with-sorry |
| `Scott2007AlgebraicInterpretationOfQuantifiers.lean` | 210 | 5 | with-sorry |
| `Scott1967IndependenceCH.lean` | 167 | 4 | with-sorry |
| `Scott1968ExtendingTopologicalInterpretation.lean` | 138 | 4 | with-sorry |
| `Scott1970AdviceOnModalLogic.lean` | 164 | 4 | with-sorry |
| `Scott1970ConstructiveValidity.lean` | 252 | 4 | with-sorry |
| `Scott1970OutlineMathematicalTheoryComputation.lean` | 357 | 4 | with-sorry |
| `Scott1972ContinuousLattices.lean` | 309 | 4 | with-sorry |
| `Scott1979IdentityAndExistence.lean` | 216 | 4 | with-sorry |
| `Scott1980LambdaCalculusModelsPhilosophy.lean` | 345 | 4 | with-sorry |
| `Scott1962AlgebrasOfSets.lean` | 151 | 3 | with-sorry |
| `Scott1982SomeOrderedSetsComputerScience.lean` | 366 | 3 | with-sorry |
| `Scott1967ExistenceAndDescription.lean` | 214 | 2 | with-sorry |
| `BenzmullerScott2016AxiomatizingCategoryTheoryInFreeLogic.lean` | 274 | 1 | with-sorry |
| `MyhillScott1971OrdinalDefinability.lean` | 162 | 1 | with-sorry |
| `ScottSuppes1958FoundationalAspectsTheoriesOfMeasurement.lean` | 227 | 1 | with-sorry |
| `BayerGonusBenzmullerScott2023CategoryTheoryInIsabelleHOL.lean` | 175 | 0 | clean (0) |
| `DataTypesAsLattices.lean` | 151 | 0 | clean (0) |
| `FourmanScott1979SheavesAndLogic.lean` | 221 | 0 | clean (0) |
| `Furber2021InterpretingLambdaCalculus.lean` | 172 | 0 | clean (0) |
| `RabinScottFiniteAutomata.lean` | 154 | 0 | clean (0) |
| `Scott1962QuinesIndividuals.lean` | 110 | 0 | clean (0) |
| `Scott1967DefinitionalSuggestionsAutomataTheory.lean` | 417 | 0 | clean (0) |
| `Scott1969BooleanModelsAndNonstandardAnalysis.lean` | 139 | 0 | clean (0) |
| `Scott1969OnCompletingOrderedFields.lean` | 195 | 0 | clean (0) |
| `Scott1971OnEngenderingAnIllusionOfUnderstanding.lean` | 153 | 0 | clean (0) |
| `Scott1974AxiomatizingSetTheory.lean` | 148 | 0 | clean (0) |
| `Scott1974DoesManyValuedLogicHaveAnyUse.lean` | 119 | 0 | clean (0) |
| `Scott1975CombinatorsAndClasses.lean` | 296 | 0 | clean (0) |
| `Scott1998ANewCategory.lean` | 185 | 0 | clean (0) |
| `TiemensScottBenzmullerBenda2019CategoricalAxiomatizationOfModeloids.lean` | 202 | 0 | clean (0) |
| `TypeTheoreticalAlternative.lean` | 181 | 0 | clean (0) |

## Downloaded papers not formalizable here (scanned image-only, need OCR)

- Scott–Strachey 1971, *Toward a Mathematical Semantics for Computer Languages*
- Scott 1973, *Models for Various Type-Free Calculi*
- Scott 1980, *The Presheaf Model for Set Theory*

## Other downloaded papers (non-Scott)

| Paper | Location | Artifact |
|-------|----------|----------|
| Coquand–Huet, *Calculus of Constructions* (1986) | `papers/` | PDF (HAL OA) |
| de Moura–Ullrich, Lean 4 (CADE 2021) | `tutorials/` | PDF (CC-BY) + `.lean` code extraction |
| Mesnard et al., LPTP (arXiv, CC-BY) | `FromGregoireRosu/` | PDF + `sqrt2.pl` |
| Harper, *PFPL* (abbreviated ed.) | `HarperBook/` (local) | PDF + `OUTLINE.md` + Ch.4 pilot `.lean` |

## Dana Scott's CMU courses (source of the notebooks)

- **Computational Projective Geometry** (Fall 1998) — CS 15-491/15-859, Math 21-450, Phil 80-414/714
- **15-499 Computational Algebra** (Fall 2000)

37 Mathematica notebooks recovered via the Internet Archive Wayback Machine into
`ScottClasses/` (see `ScottClasses/README.md` for per-file provenance).
