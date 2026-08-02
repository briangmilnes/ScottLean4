# Dana Scott papers — formalization index & proof status

One row per Dana Scott paper: its **source PDF** (in this folder) linked to the
Lean 4 formalization under [`../ScottLean/Scott/`](../ScottLean/Scott/), with
**kernel-checked** proof status.

> **Status is kernel-checked** (2026-08-01): every module was re-elaborated with
> `lake env lean <file>`. **compiles** = 0 errors; **holes** = number of
> declarations Lean flags with its *"declaration uses `sorry`"* warning (the
> authoritative proof-hole count — a declaration is either fully proved or uses `sorry`).

**Scoreboard:** 38 formalizations · **38 compile / 0 fail** · **16 fully proved** (0 holes) · 22 with holes · 281 defs/thms · **100 `sorry`-declarations**.

| Year | Paper (source PDF) | Lean formalization | defs/thms | holes | status |
|------|--------------------|--------------------|:---------:|:-----:|--------|
| 1958 | [Scott-1958-Convergent-Sequences-of-Complete-Theories-dissertation](Scott-1958-Convergent-Sequences-of-Complete-Theories-dissertation.pdf) | [Scott1958ConvergentSequences.lean](../ScottLean/Scott/Scott1958ConvergentSequences.lean) | 10 | 5 | 🕳️ 5 hole(s) |
| 1958 | [Scott-Suppes-1958-Foundational-Aspects-Theories-of-Measurement](Scott-Suppes-1958-Foundational-Aspects-Theories-of-Measurement.pdf) | [ScottSuppes1958FoundationalAspectsTheoriesOfMeasurement.lean](../ScottLean/Scott/ScottSuppes1958FoundationalAspectsTheoriesOfMeasurement.lean) | 7 | 1 | 🕳️ 1 hole(s) |
| 1959 | [Rabin-Scott-1959-Finite-Automata-and-Their-Decision-Problems](Rabin-Scott-1959-Finite-Automata-and-Their-Decision-Problems.pdf) | [RabinScottFiniteAutomata.lean](../ScottLean/Scott/RabinScottFiniteAutomata.lean) | 3 | 0 | ✅ proved (0 holes) |
| 1959 | [Scott-1959-On-Constructing-Models-for-Arithmetic](Scott-1959-On-Constructing-Models-for-Arithmetic.pdf) | [Scott1959ConstructingModels.lean](../ScottLean/Scott/Scott1959ConstructingModels.lean) | 8 | 8 | 🕳️ 8 hole(s) |
| 1961 | [Scott-1961-Measurable-Cardinals-and-Constructible-Sets](Scott-1961-Measurable-Cardinals-and-Constructible-Sets.pdf) | [Scott1961MeasurableCardinals.lean](../ScottLean/Scott/Scott1961MeasurableCardinals.lean) | 9 | 6 | 🕳️ 6 hole(s) |
| 1962 | [Scott-1962-Algebras-of-Sets-Binumerable](Scott-1962-Algebras-of-Sets-Binumerable.pdf) | [Scott1962AlgebrasOfSets.lean](../ScottLean/Scott/Scott1962AlgebrasOfSets.lean) | 6 | 3 | 🕳️ 3 hole(s) |
| 1962 | [Scott-1962-Quines-Individuals](Scott-1962-Quines-Individuals.pdf) | [Scott1962QuinesIndividuals.lean](../ScottLean/Scott/Scott1962QuinesIndividuals.lean) | 2 | 0 | ✅ proved (0 holes) |
| 1964 | [Scott-1964-Invariant-Borel-Sets](Scott-1964-Invariant-Borel-Sets.pdf) | [Scott1964InvariantBorelSets.lean](../ScottLean/Scott/Scott1964InvariantBorelSets.lean) | 11 | 6 | 🕳️ 6 hole(s) |
| 1965 | [Scott-1965-Logic-with-Denumerably-Long-Formulas](Scott-1965-Logic-with-Denumerably-Long-Formulas.pdf) | [Scott1965DenumerablyLongFormulas.lean](../ScottLean/Scott/Scott1965DenumerablyLongFormulas.lean) | 8 | 6 | 🕳️ 6 hole(s) |
| 1967 | [Scott-1967-Some-Definitional-Suggestions-for-Automata-Theory](Scott-1967-Some-Definitional-Suggestions-for-Automata-Theory.pdf) | [Scott1967DefinitionalSuggestionsAutomataTheory.lean](../ScottLean/Scott/Scott1967DefinitionalSuggestionsAutomataTheory.lean) | 9 | 0 | ✅ proved (0 holes) |
| 1967 | [Scott-1967-Existence-and-Description-in-Formal-Logic](Scott-1967-Existence-and-Description-in-Formal-Logic.pdf) | [Scott1967ExistenceAndDescription.lean](../ScottLean/Scott/Scott1967ExistenceAndDescription.lean) | 2 | 2 | 🕳️ 2 hole(s) |
| 1967 | [Scott-1967-Independence-of-the-Continuum-Hypothesis](Scott-1967-Independence-of-the-Continuum-Hypothesis.pdf) | [Scott1967IndependenceCH.lean](../ScottLean/Scott/Scott1967IndependenceCH.lean) | 6 | 4 | 🕳️ 4 hole(s) |
| 1968 | [Scott-1968-Extending-Topological-Interpretation-Intuitionistic-Analysis](Scott-1968-Extending-Topological-Interpretation-Intuitionistic-Analysis.pdf) | [Scott1968ExtendingTopologicalInterpretation.lean](../ScottLean/Scott/Scott1968ExtendingTopologicalInterpretation.lean) | 4 | 4 | 🕳️ 4 hole(s) |
| 1969 | [Scott-1969-Boolean-Models-and-Nonstandard-Analysis](Scott-1969-Boolean-Models-and-Nonstandard-Analysis.pdf) | [Scott1969BooleanModelsAndNonstandardAnalysis.lean](../ScottLean/Scott/Scott1969BooleanModelsAndNonstandardAnalysis.lean) | 1 | 0 | ✅ proved (0 holes) |
| 1969 | [Scott-1969-On-Completing-Ordered-Fields](Scott-1969-On-Completing-Ordered-Fields.pdf) | [Scott1969OnCompletingOrderedFields.lean](../ScottLean/Scott/Scott1969OnCompletingOrderedFields.lean) | 2 | 0 | ✅ proved (0 holes) |
| 1970 | [Scott-1970-Advice-on-Modal-Logic](Scott-1970-Advice-on-Modal-Logic.pdf) | [Scott1970AdviceOnModalLogic.lean](../ScottLean/Scott/Scott1970AdviceOnModalLogic.lean) | 4 | 4 | 🕳️ 4 hole(s) |
| 1970 | [Scott-1970-Constructive-Validity](Scott-1970-Constructive-Validity.pdf) | [Scott1970ConstructiveValidity.lean](../ScottLean/Scott/Scott1970ConstructiveValidity.lean) | 3 | 4 | 🕳️ 4 hole(s) |
| 1970 | [Scott-1970-Extending-Topological-Interpretation-Intuitionistic-Analysis-II](Scott-1970-Extending-Topological-Interpretation-Intuitionistic-Analysis-II.pdf) | [Scott1970ExtendingTopologicalInterpretationII.lean](../ScottLean/Scott/Scott1970ExtendingTopologicalInterpretationII.lean) | 18 | 14 | 🕳️ 14 hole(s) |
| 1970 | [Scott-1970-Outline-of-a-Mathematical-Theory-of-Computation-PRG2](Scott-1970-Outline-of-a-Mathematical-Theory-of-Computation-PRG2.pdf) | [Scott1970OutlineMathematicalTheoryComputation.lean](../ScottLean/Scott/Scott1970OutlineMathematicalTheoryComputation.lean) | 19 | 4 | 🕳️ 4 hole(s) |
| 1971 | [Myhill-Scott-1971-Ordinal-Definability](Myhill-Scott-1971-Ordinal-Definability.pdf) | [MyhillScott1971OrdinalDefinability.lean](../ScottLean/Scott/MyhillScott1971OrdinalDefinability.lean) | 3 | 1 | 🕳️ 1 hole(s) |
| 1971 | [Scott-1971-On-Engendering-an-Illusion-of-Understanding](Scott-1971-On-Engendering-an-Illusion-of-Understanding.pdf) | [Scott1971OnEngenderingAnIllusionOfUnderstanding.lean](../ScottLean/Scott/Scott1971OnEngenderingAnIllusionOfUnderstanding.lean) | 9 | 0 | ✅ proved (0 holes) |
| 1972 | [Scott-1972-Continuous-Lattices](Scott-1972-Continuous-Lattices.pdf) | [Scott1972ContinuousLattices.lean](../ScottLean/Scott/Scott1972ContinuousLattices.lean) | 14 | 4 | 🕳️ 4 hole(s) |
| 1974 | [Scott-1974-Axiomatizing-Set-Theory](Scott-1974-Axiomatizing-Set-Theory.pdf) | [Scott1974AxiomatizingSetTheory.lean](../ScottLean/Scott/Scott1974AxiomatizingSetTheory.lean) | 2 | 0 | ✅ proved (0 holes) |
| 1974 | [Scott-1974-Does-Many-Valued-Logic-Have-Any-Use](Scott-1974-Does-Many-Valued-Logic-Have-Any-Use.pdf) | [Scott1974DoesManyValuedLogicHaveAnyUse.lean](../ScottLean/Scott/Scott1974DoesManyValuedLogicHaveAnyUse.lean) | 7 | 0 | ✅ proved (0 holes) |
| 1975 | [Scott-1975-Combinators-and-Classes](Scott-1975-Combinators-and-Classes.pdf) | [Scott1975CombinatorsAndClasses.lean](../ScottLean/Scott/Scott1975CombinatorsAndClasses.lean) | 10 | 0 | ✅ proved (0 holes) |
| 1976 | [Scott-1976-Data-Types-as-Lattices](Scott-1976-Data-Types-as-Lattices.pdf) | [DataTypesAsLattices.lean](../ScottLean/Scott/DataTypesAsLattices.lean) | 10 | 0 | ✅ proved (0 holes) |
| 1979 | [Fourman-Scott-1979-Sheaves-and-Logic](Fourman-Scott-1979-Sheaves-and-Logic.pdf) | [FourmanScott1979SheavesAndLogic.lean](../ScottLean/Scott/FourmanScott1979SheavesAndLogic.lean) | 3 | 0 | ✅ proved (0 holes) |
| 1979 | [Scott-1979-Identity-and-Existence-in-Intuitionistic-Logic](Scott-1979-Identity-and-Existence-in-Intuitionistic-Logic.pdf) | [Scott1979IdentityAndExistence.lean](../ScottLean/Scott/Scott1979IdentityAndExistence.lean) | 5 | 4 | 🕳️ 4 hole(s) |
| 1980 | [Scott-1980-Lambda-Calculus-Some-Models-Some-Philosophy](Scott-1980-Lambda-Calculus-Some-Models-Some-Philosophy.pdf) | [Scott1980LambdaCalculusModelsPhilosophy.lean](../ScottLean/Scott/Scott1980LambdaCalculusModelsPhilosophy.lean) | 14 | 4 | 🕳️ 4 hole(s) |
| 1980 | [Scott-1980-Relating-Theories-of-the-Lambda-Calculus](Scott-1980-Relating-Theories-of-the-Lambda-Calculus.pdf) | [Scott1980RelatingTheoriesLambdaCalculus.lean](../ScottLean/Scott/Scott1980RelatingTheoriesLambdaCalculus.lean) | 21 | 7 | 🕳️ 7 hole(s) |
| 1982 | [Scott-1982-Some-Ordered-Sets-in-Computer-Science](Scott-1982-Some-Ordered-Sets-in-Computer-Science.pdf) | [Scott1982SomeOrderedSetsComputerScience.lean](../ScottLean/Scott/Scott1982SomeOrderedSetsComputerScience.lean) | 16 | 3 | 🕳️ 3 hole(s) |
| 1993 | [Scott-1993-A-Type-Theoretical-Alternative-to-ISWIM-CUCH-OWHY](Scott-1993-A-Type-Theoretical-Alternative-to-ISWIM-CUCH-OWHY.pdf) | [TypeTheoreticalAlternative.lean](../ScottLean/Scott/TypeTheoreticalAlternative.lean) | 6 | 0 | ✅ proved (0 holes) |
| 1998 | [Scott-1998-A-New-Category](Scott-1998-A-New-Category.pdf) | [Scott1998ANewCategory.lean](../ScottLean/Scott/Scott1998ANewCategory.lean) | 5 | 0 | ✅ proved (0 holes) |
| 2007 | [Scott-2007-The-Algebraic-Interpretation-of-Quantifiers](Scott-2007-The-Algebraic-Interpretation-of-Quantifiers.pdf) | [Scott2007AlgebraicInterpretationOfQuantifiers.lean](../ScottLean/Scott/Scott2007AlgebraicInterpretationOfQuantifiers.lean) | 5 | 5 | 🕳️ 5 hole(s) |
| 2016 | [Benzmuller-Scott-2016-Axiomatizing-Category-Theory-in-Free-Logic](Benzmuller-Scott-2016-Axiomatizing-Category-Theory-in-Free-Logic.pdf) | [BenzmullerScott2016AxiomatizingCategoryTheoryInFreeLogic.lean](../ScottLean/Scott/BenzmullerScott2016AxiomatizingCategoryTheoryInFreeLogic.lean) | 11 | 1 | 🕳️ 1 hole(s) |
| 2019 | [Tiemens-Scott-Benzmuller-Benda-2019-Categorical-Axiomatization-of-Modeloids](Tiemens-Scott-Benzmuller-Benda-2019-Categorical-Axiomatization-of-Modeloids.pdf) | [TiemensScottBenzmullerBenda2019CategoricalAxiomatizationOfModeloids.lean](../ScottLean/Scott/TiemensScottBenzmullerBenda2019CategoricalAxiomatizationOfModeloids.lean) | 2 | 0 | ✅ proved (0 holes) |
| 2021 | [Furber-Mardare-Panangaden-Scott-2021-Interpreting-Lambda-Calculus-Domain-Valued-Random-Variables](Furber-Mardare-Panangaden-Scott-2021-Interpreting-Lambda-Calculus-Domain-Valued-Random-Variables.pdf) | [Furber2021InterpretingLambdaCalculus.lean](../ScottLean/Scott/Furber2021InterpretingLambdaCalculus.lean) | 5 | 0 | ✅ proved (0 holes) |
| 2023 | [Bayer-Gonus-Benzmuller-Scott-2023-Category-Theory-in-Isabelle-HOL](Bayer-Gonus-Benzmuller-Scott-2023-Category-Theory-in-Isabelle-HOL.pdf) | [BayerGonusBenzmullerScott2023CategoryTheoryInIsabelleHOL.lean](../ScottLean/Scott/BayerGonusBenzmullerScott2023CategoryTheoryInIsabelleHOL.lean) | 1 | 0 | ✅ proved (0 holes) |

## Notes
- **Kernel-checked**, not just text: all 38 modules **compile with 0 errors**; the `holes`
  column is the real count of declarations flagged with `sorry`, from `lake env lean`.
- This is lower than a raw text search for `sorry` (some occurrences are header-comment
  mentions). `defs/thms` is a textual size indicator (`theorem`/`lemma`/`example`).
- Regenerate: `lake env lean ScottLean/Scott/<Module>.lean` per file; the whole library
  also builds via `lake build` (root `ScottLean.lean` imports every module).
- `EXTRACTION_REPORT.md` (this folder) covers text-extraction quality per paper.
