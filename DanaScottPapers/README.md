# Dana Scott papers — formalization proof status

Each of Dana Scott's papers (source PDF in this folder) is transcribed into a
Lean 4 module under [`../ScottLean/Scott/`](../ScottLean/Scott/). Status is
**kernel-checked** — every module re-elaborated with `lake env lean`.

**38/38 compile** · **16 fully proved** · 22 with holes · **100 open `sorry` goals** · 281 defs/thms.

Legend: **✅** = 0 holes · **🕳️ n** = n `sorry` goals open. The paper title links to its PDF; the last column links to the Lean module (long — scroll right).

| Defs | Holes | Year | Paper | Lean module |
|:----:|:-----:|:----:|-------|-------------|
| 10 | 🕳️ 5 | 1958 | [Convergent Sequences of Complete Theories dissertation](Scott-1958-Convergent-Sequences-of-Complete-Theories-dissertation.pdf) | [Scott1958ConvergentSequences.lean](../ScottLean/Scott/Scott1958ConvergentSequences.lean) |
| 7 | 🕳️ 1 | 1958 | [Foundational Aspects Theories of Measurement (Scott–Suppes)](Scott-Suppes-1958-Foundational-Aspects-Theories-of-Measurement.pdf) | [ScottSuppes1958FoundationalAspectsTheoriesOfMeasurement.lean](../ScottLean/Scott/ScottSuppes1958FoundationalAspectsTheoriesOfMeasurement.lean) |
| 3 | ✅ | 1959 | [Finite Automata and Their Decision Problems (Rabin–Scott)](Rabin-Scott-1959-Finite-Automata-and-Their-Decision-Problems.pdf) | [RabinScottFiniteAutomata.lean](../ScottLean/Scott/RabinScottFiniteAutomata.lean) |
| 8 | 🕳️ 8 | 1959 | [On Constructing Models for Arithmetic](Scott-1959-On-Constructing-Models-for-Arithmetic.pdf) | [Scott1959ConstructingModels.lean](../ScottLean/Scott/Scott1959ConstructingModels.lean) |
| 9 | 🕳️ 6 | 1961 | [Measurable Cardinals and Constructible Sets](Scott-1961-Measurable-Cardinals-and-Constructible-Sets.pdf) | [Scott1961MeasurableCardinals.lean](../ScottLean/Scott/Scott1961MeasurableCardinals.lean) |
| 6 | 🕳️ 3 | 1962 | [Algebras of Sets Binumerable](Scott-1962-Algebras-of-Sets-Binumerable.pdf) | [Scott1962AlgebrasOfSets.lean](../ScottLean/Scott/Scott1962AlgebrasOfSets.lean) |
| 2 | ✅ | 1962 | [Quines Individuals](Scott-1962-Quines-Individuals.pdf) | [Scott1962QuinesIndividuals.lean](../ScottLean/Scott/Scott1962QuinesIndividuals.lean) |
| 11 | 🕳️ 6 | 1964 | [Invariant Borel Sets](Scott-1964-Invariant-Borel-Sets.pdf) | [Scott1964InvariantBorelSets.lean](../ScottLean/Scott/Scott1964InvariantBorelSets.lean) |
| 8 | 🕳️ 6 | 1965 | [Logic with Denumerably Long Formulas](Scott-1965-Logic-with-Denumerably-Long-Formulas.pdf) | [Scott1965DenumerablyLongFormulas.lean](../ScottLean/Scott/Scott1965DenumerablyLongFormulas.lean) |
| 2 | 🕳️ 2 | 1967 | [Existence and Description in Formal Logic](Scott-1967-Existence-and-Description-in-Formal-Logic.pdf) | [Scott1967ExistenceAndDescription.lean](../ScottLean/Scott/Scott1967ExistenceAndDescription.lean) |
| 6 | 🕳️ 4 | 1967 | [Independence of the Continuum Hypothesis](Scott-1967-Independence-of-the-Continuum-Hypothesis.pdf) | [Scott1967IndependenceCH.lean](../ScottLean/Scott/Scott1967IndependenceCH.lean) |
| 9 | ✅ | 1967 | [Some Definitional Suggestions for Automata Theory](Scott-1967-Some-Definitional-Suggestions-for-Automata-Theory.pdf) | [Scott1967DefinitionalSuggestionsAutomataTheory.lean](../ScottLean/Scott/Scott1967DefinitionalSuggestionsAutomataTheory.lean) |
| 4 | 🕳️ 4 | 1968 | [Extending Topological Interpretation Intuitionistic Analysis](Scott-1968-Extending-Topological-Interpretation-Intuitionistic-Analysis.pdf) | [Scott1968ExtendingTopologicalInterpretation.lean](../ScottLean/Scott/Scott1968ExtendingTopologicalInterpretation.lean) |
| 1 | ✅ | 1969 | [Boolean Models and Nonstandard Analysis](Scott-1969-Boolean-Models-and-Nonstandard-Analysis.pdf) | [Scott1969BooleanModelsAndNonstandardAnalysis.lean](../ScottLean/Scott/Scott1969BooleanModelsAndNonstandardAnalysis.lean) |
| 2 | ✅ | 1969 | [On Completing Ordered Fields](Scott-1969-On-Completing-Ordered-Fields.pdf) | [Scott1969OnCompletingOrderedFields.lean](../ScottLean/Scott/Scott1969OnCompletingOrderedFields.lean) |
| 4 | 🕳️ 4 | 1970 | [Advice on Modal Logic](Scott-1970-Advice-on-Modal-Logic.pdf) | [Scott1970AdviceOnModalLogic.lean](../ScottLean/Scott/Scott1970AdviceOnModalLogic.lean) |
| 3 | 🕳️ 4 | 1970 | [Constructive Validity](Scott-1970-Constructive-Validity.pdf) | [Scott1970ConstructiveValidity.lean](../ScottLean/Scott/Scott1970ConstructiveValidity.lean) |
| 18 | 🕳️ 14 | 1970 | [Extending Topological Interpretation Intuitionistic Analysis II](Scott-1970-Extending-Topological-Interpretation-Intuitionistic-Analysis-II.pdf) | [Scott1970ExtendingTopologicalInterpretationII.lean](../ScottLean/Scott/Scott1970ExtendingTopologicalInterpretationII.lean) |
| 19 | 🕳️ 4 | 1970 | [Outline of a Mathematical Theory of Computation PRG2](Scott-1970-Outline-of-a-Mathematical-Theory-of-Computation-PRG2.pdf) | [Scott1970OutlineMathematicalTheoryComputation.lean](../ScottLean/Scott/Scott1970OutlineMathematicalTheoryComputation.lean) |
| 9 | ✅ | 1971 | [On Engendering an Illusion of Understanding](Scott-1971-On-Engendering-an-Illusion-of-Understanding.pdf) | [Scott1971OnEngenderingAnIllusionOfUnderstanding.lean](../ScottLean/Scott/Scott1971OnEngenderingAnIllusionOfUnderstanding.lean) |
| 3 | 🕳️ 1 | 1971 | [Ordinal Definability (Myhill–Scott)](Myhill-Scott-1971-Ordinal-Definability.pdf) | [MyhillScott1971OrdinalDefinability.lean](../ScottLean/Scott/MyhillScott1971OrdinalDefinability.lean) |
| 14 | 🕳️ 4 | 1972 | [Continuous Lattices](Scott-1972-Continuous-Lattices.pdf) | [Scott1972ContinuousLattices.lean](../ScottLean/Scott/Scott1972ContinuousLattices.lean) |
| 2 | ✅ | 1974 | [Axiomatizing Set Theory](Scott-1974-Axiomatizing-Set-Theory.pdf) | [Scott1974AxiomatizingSetTheory.lean](../ScottLean/Scott/Scott1974AxiomatizingSetTheory.lean) |
| 7 | ✅ | 1974 | [Does Many Valued Logic Have Any Use](Scott-1974-Does-Many-Valued-Logic-Have-Any-Use.pdf) | [Scott1974DoesManyValuedLogicHaveAnyUse.lean](../ScottLean/Scott/Scott1974DoesManyValuedLogicHaveAnyUse.lean) |
| 10 | ✅ | 1975 | [Combinators and Classes](Scott-1975-Combinators-and-Classes.pdf) | [Scott1975CombinatorsAndClasses.lean](../ScottLean/Scott/Scott1975CombinatorsAndClasses.lean) |
| 10 | ✅ | 1976 | [Data Types as Lattices](Scott-1976-Data-Types-as-Lattices.pdf) | [DataTypesAsLattices.lean](../ScottLean/Scott/DataTypesAsLattices.lean) |
| 5 | 🕳️ 4 | 1979 | [Identity and Existence in Intuitionistic Logic](Scott-1979-Identity-and-Existence-in-Intuitionistic-Logic.pdf) | [Scott1979IdentityAndExistence.lean](../ScottLean/Scott/Scott1979IdentityAndExistence.lean) |
| 3 | ✅ | 1979 | [Sheaves and Logic (Fourman–Scott)](Fourman-Scott-1979-Sheaves-and-Logic.pdf) | [FourmanScott1979SheavesAndLogic.lean](../ScottLean/Scott/FourmanScott1979SheavesAndLogic.lean) |
| 14 | 🕳️ 4 | 1980 | [Lambda Calculus Some Models Some Philosophy](Scott-1980-Lambda-Calculus-Some-Models-Some-Philosophy.pdf) | [Scott1980LambdaCalculusModelsPhilosophy.lean](../ScottLean/Scott/Scott1980LambdaCalculusModelsPhilosophy.lean) |
| 21 | 🕳️ 7 | 1980 | [Relating Theories of the Lambda Calculus](Scott-1980-Relating-Theories-of-the-Lambda-Calculus.pdf) | [Scott1980RelatingTheoriesLambdaCalculus.lean](../ScottLean/Scott/Scott1980RelatingTheoriesLambdaCalculus.lean) |
| 16 | 🕳️ 3 | 1982 | [Some Ordered Sets in Computer Science](Scott-1982-Some-Ordered-Sets-in-Computer-Science.pdf) | [Scott1982SomeOrderedSetsComputerScience.lean](../ScottLean/Scott/Scott1982SomeOrderedSetsComputerScience.lean) |
| 6 | ✅ | 1993 | [A Type Theoretical Alternative to ISWIM CUCH OWHY](Scott-1993-A-Type-Theoretical-Alternative-to-ISWIM-CUCH-OWHY.pdf) | [TypeTheoreticalAlternative.lean](../ScottLean/Scott/TypeTheoreticalAlternative.lean) |
| 5 | ✅ | 1998 | [A New Category](Scott-1998-A-New-Category.pdf) | [Scott1998ANewCategory.lean](../ScottLean/Scott/Scott1998ANewCategory.lean) |
| 5 | 🕳️ 5 | 2007 | [The Algebraic Interpretation of Quantifiers](Scott-2007-The-Algebraic-Interpretation-of-Quantifiers.pdf) | [Scott2007AlgebraicInterpretationOfQuantifiers.lean](../ScottLean/Scott/Scott2007AlgebraicInterpretationOfQuantifiers.lean) |
| 11 | 🕳️ 1 | 2016 | [Axiomatizing Category Theory in Free Logic (Benzmuller–Scott)](Benzmuller-Scott-2016-Axiomatizing-Category-Theory-in-Free-Logic.pdf) | [BenzmullerScott2016AxiomatizingCategoryTheoryInFreeLogic.lean](../ScottLean/Scott/BenzmullerScott2016AxiomatizingCategoryTheoryInFreeLogic.lean) |
| 2 | ✅ | 2019 | [Categorical Axiomatization of Modeloids (Tiemens et al.)](Tiemens-Scott-Benzmuller-Benda-2019-Categorical-Axiomatization-of-Modeloids.pdf) | [TiemensScottBenzmullerBenda2019CategoricalAxiomatizationOfModeloids.lean](../ScottLean/Scott/TiemensScottBenzmullerBenda2019CategoricalAxiomatizationOfModeloids.lean) |
| 5 | ✅ | 2021 | [Interpreting Lambda Calculus Domain Valued Random Variables (Furber et al.)](Furber-Mardare-Panangaden-Scott-2021-Interpreting-Lambda-Calculus-Domain-Valued-Random-Variables.pdf) | [Furber2021InterpretingLambdaCalculus.lean](../ScottLean/Scott/Furber2021InterpretingLambdaCalculus.lean) |
| 1 | ✅ | 2023 | [Category Theory in Isabelle HOL (Bayer et al.)](Bayer-Gonus-Benzmuller-Scott-2023-Category-Theory-in-Isabelle-HOL.pdf) | [BayerGonusBenzmullerScott2023CategoryTheoryInIsabelleHOL.lean](../ScottLean/Scott/BayerGonusBenzmullerScott2023CategoryTheoryInIsabelleHOL.lean) |

**Where the holes are:** Extending Topological Interpretation Intuitionistic Analysis II (14) · On Constructing Models for Arithmetic (8) · Relating Theories of the Lambda Calculus (7).

## Notes
- Kernel-checked 2026-08-01: all 38 modules compile with 0 errors; **holes** = Lean's
  *"declaration uses `sorry`"* count from `lake env lean <file>`.
- Rebuild all with `lake build` (root `ScottLean.lean` imports every module).
- `EXTRACTION_REPORT.md` (this folder) covers text-extraction quality per paper.
