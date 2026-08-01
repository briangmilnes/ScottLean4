# Dana Scott Papers — Download & Text-Extraction Report

Generated from the OA_PDFS manifest in `docs/DanaScottPapers.md`.
Text extracted with `pdftotext -layout`. A paper is marked SCANNED-IMAGE
when its extracted text layer has fewer than ~800 alphabetic characters
(image-only scan, no usable text layer).

| Paper | Downloaded (Y/N) | Is PDF (Y/N) | Text-extractible | approx char count |
|-------|:---:|:---:|:---:|---:|
| Scott-Suppes-1958-Foundational-Aspects-Theories-of-Measurement | Y | Y | YES | 35125 |
| Scott-1958-Convergent-Sequences-of-Complete-Theories-dissertation | Y | Y | YES | 65926 |
| Rabin-Scott-1959-Finite-Automata-and-Their-Decision-Problems | Y | Y | YES | 47658 |
| Scott-1959-On-Constructing-Models-for-Arithmetic | Y | Y | YES | 34115 |
| Scott-1961-Measurable-Cardinals-and-Constructible-Sets | Y | Y | YES | 7135 |
| Scott-1962-Quines-Individuals | Y | Y | YES | 9463 |
| Scott-1962-Algebras-of-Sets-Binumerable | Y | Y | YES | 8890 |
| Scott-1964-Invariant-Borel-Sets | Y | Y | YES | 18631 |
| Scott-1965-Logic-with-Denumerably-Long-Formulas | Y | Y | YES | 20131 |
| Scott-1967-Independence-of-the-Continuum-Hypothesis | Y | Y | YES | 41867 |
| Scott-1967-Existence-and-Description-in-Formal-Logic | Y | Y | YES | 29250 |
| Scott-1967-Some-Definitional-Suggestions-for-Automata-Theory | Y | Y | YES | 43188 |
| Scott-1968-Extending-Topological-Interpretation-Intuitionistic-Analysis | Y | Y | YES | 19950 |
| Scott-1969-Boolean-Models-and-Nonstandard-Analysis | Y | Y | YES | 9029 |
| Scott-1969-On-Completing-Ordered-Fields | Y | Y | YES | 8160 |
| Scott-1970-Advice-on-Modal-Logic | Y | Y | YES | 52965 |
| Scott-1970-Constructive-Validity | Y | Y | YES | 52561 |
| Scott-1970-Extending-Topological-Interpretation-Intuitionistic-Analysis-II | Y | Y | YES | 28600 |
| Scott-1970-Outline-of-a-Mathematical-Theory-of-Computation-PRG2 | Y | Y | YES | 28604 |
| Myhill-Scott-1971-Ordinal-Definability | Y | Y | YES | 13836 |
| Scott-1971-On-Engendering-an-Illusion-of-Understanding | Y | Y | YES | 41082 |
| Scott-Strachey-1971-Toward-a-Mathematical-Semantics-for-Computer-Languages | Y | Y | SCANNED-IMAGE | 0 |
| Scott-1972-Continuous-Lattices | Y | Y | YES | 46567 |
| Scott-1973-Models-for-Various-Type-Free-Calculi | Y | Y | SCANNED-IMAGE | 0 |
| Scott-1974-Axiomatizing-Set-Theory | Y | Y | YES | 14335 |
| Scott-1974-Does-Many-Valued-Logic-Have-Any-Use | Y | Y | YES | 15269 |
| Scott-1975-Combinators-and-Classes | Y | Y | YES | 28688 |
| Scott-1976-Data-Types-as-Lattices | Y | Y | YES | 127875 |
| Fourman-Scott-1979-Sheaves-and-Logic | Y | Y | YES | 143931 |
| Scott-1979-Identity-and-Existence-in-Intuitionistic-Logic | Y | Y | YES | 56827 |
| Scott-1980-Lambda-Calculus-Some-Models-Some-Philosophy | Y | Y | YES | 76862 |
| Scott-1980-Relating-Theories-of-the-Lambda-Calculus | Y | Y | YES | 54346 |
| Scott-1980-The-Presheaf-Model-for-Set-Theory | Y | Y | SCANNED-IMAGE | 0 |
| Scott-1982-Some-Ordered-Sets-in-Computer-Science | Y | Y | YES | 54160 |
| Scott-1993-A-Type-Theoretical-Alternative-to-ISWIM-CUCH-OWHY | Y | Y | YES | 52689 |
| Scott-1998-A-New-Category | Y | Y | YES | 32760 |
| Scott-2007-The-Algebraic-Interpretation-of-Quantifiers | Y | Y | YES | 38460 |
| Benzmuller-Scott-2016-Axiomatizing-Category-Theory-in-Free-Logic | Y | Y | YES | 29761 |
| Tiemens-Scott-Benzmuller-Benda-2019-Categorical-Axiomatization-of-Modeloids | Y | Y | YES | 38616 |
| Furber-Mardare-Panangaden-Scott-2021-Interpreting-Lambda-Calculus-Domain-Valued-Random-Variables | Y | Y | YES | 63757 |
| Bayer-Gonus-Benzmuller-Scott-2023-Category-Theory-in-Isabelle-HOL | Y | Y | YES | 32624 |

**41 of 41 downloaded; 38 have an extractible text layer.**

SCANNED-IMAGE (no usable text layer): Scott-Strachey-1971 (Toward a Mathematical Semantics), Scott-1973 (Models for Various Type-Free Calculi), Scott-1980 (The Presheaf Model for Set Theory).

## Lean formalization status

Pilot Lean 4 files (core Lean, no Mathlib) were generated for the 3 most
amenable extractible papers and **all verify** with `lake env lean`
(Lean/Lake 4.32.2):

| Paper | Lean file | Verification |
|-------|-----------|:---:|
| Rabin-Scott 1959, Finite Automata | `ScottLean/Scott/RabinScottFiniteAutomata.lean` | PASS |
| Scott 1976, Data Types as Lattices (Pω) | `ScottLean/Scott/DataTypesAsLattices.lean` | PASS |
| Scott 1993, Type-Theoretical Alternative | `ScottLean/Scott/TypeTheoreticalAlternative.lean` | PASS |

All other extractible papers: **text available, formalization TODO** (no Lean
fabricated for them). The 3 SCANNED-IMAGE papers have no usable text layer.
