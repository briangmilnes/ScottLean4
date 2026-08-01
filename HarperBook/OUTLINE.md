# PFPL — Section Map / Outline

**Book:** Robert Harper, *Practical Foundations for Programming Languages*, Second Edition. Cambridge University Press, 2016.
**Source used:** Author-authorized free "Abbreviated online edition, with corrections" — `https://www.cs.cmu.edu/~rwh/pfpl/abbrev.pdf` (linked from the official page `https://www.cs.cmu.edu/~rwh/pfpl.html`).
**Local files:** `HarperBook/PFPL.pdf` (the abbreviated draft), `HarperBook/PFPL.txt` (`pdftotext -layout` extraction, 11,820 lines).

## Legend / how to read this map

- `p.N` = book page number (as printed in the Table of Contents).
- `[txt Lnnnn]` = 1-based line in `PFPL.txt` where that chapter's body begins (anchor for driving generation).
- **`[body]`** = full chapter text is present in this abbreviated draft.
- *`[TOC only]`* = chapter is listed in the Table of Contents but its body is **omitted** from the free abbreviated edition (would require the full published book).

## IMPORTANT availability note

The free abbreviated edition contains the complete front matter and Table of Contents for all 19 parts / 49 chapters, but full **body text for only 17 chapters**:

> 1, 2, 3, 4, 5, 6, 9, 10, 11, 16, 19, 28, 29, 34, 35, 37, 40

Only these chapters can be faithfully rendered into Lean from this source. All other chapters below are marked *[TOC only]* — titles/pages are known, but their rules and definitions are not in this PDF. Appendices A and B are TOC-only as well.

Totals: **19 Parts, 49 Chapters (+2 appendices), ~300 numbered sections.**

---

## Part I — Judgments and Rules (p.1)

### 1. Abstract Syntax — p.3 **[body]** [txt L895]
- 1.1 Abstract Syntax Trees (p.4)
- 1.2 Abstract Binding Trees (p.6)
- 1.3 Notes (p.10)

### 2. Inductive Definitions — p.13 **[body]** [txt L1436]
- 2.1 Judgments (p.13)
- 2.2 Inference Rules (p.14)
- 2.3 Derivations (p.15)
- 2.4 Rule Induction (p.16)
- 2.5 Iterated and Simultaneous Inductive Definitions (p.18)
- 2.6 Defining Functions by Rules (p.19)
- 2.7 Notes (p.20)

### 3. Hypothetical and General Judgments — p.23 **[body]** [txt L2000]
- 3.1 Hypothetical Judgments (p.23) — 3.1.1 Derivability (p.23); 3.1.2 Admissibility (p.25)
- 3.2 Hypothetical Inductive Definitions (p.26)
- 3.3 General Judgments (p.28)
- 3.4 Generic Inductive Definitions (p.29)
- 3.5 Notes (p.30)

## Part II — Statics and Dynamics (p.33)

### 4. Statics — p.35 **[body]** [txt L2673]  ← pilot chapter (language E)
- 4.1 Syntax (p.35)
- 4.2 Type System (p.36)
- 4.3 Structural Properties (p.37)
- 4.4 Notes (p.39)

### 5. Dynamics — p.41 **[body]** [txt L3028]
- 5.1 Transition Systems (p.41)
- 5.2 Structural Dynamics (p.42)
- 5.3 Contextual Dynamics (p.44)
- 5.4 Equational Dynamics (p.46)
- 5.5 Notes (p.48)

### 6. Type Safety — p.51 **[body]** [txt L3630]
- 6.1 Preservation (p.52)
- 6.2 Progress (p.52)
- 6.3 Run-Time Errors (p.53)
- 6.4 Notes (p.55)

### 7. Evaluation Dynamics — p.57 *[TOC only]*
- 7.1 Evaluation Dynamics (p.57)
- 7.2 Relating Structural and Evaluation Dynamics (p.58)
- 7.3 Type Safety, Revisited (p.59)
- 7.4 Cost Dynamics (p.60)
- 7.5 Notes (p.61)

## Part III — Total Functions (p.63)

### 8. Function Definitions and Values — p.65 *[TOC only]*
- 8.1 First-Order Functions (p.65)
- 8.2 Higher-Order Functions (p.67)
- 8.3 Evaluation Dynamics and Definitional Equality (p.69)
- 8.4 Dynamic Scope (p.70)
- 8.5 Notes (p.71)

### 9. System T of Higher-Order Recursion — p.73 **[body]** [txt L3920]
- 9.1 Statics (p.73)
- 9.2 Dynamics (p.74)
- 9.3 Definability (p.76)
- 9.4 Undefinability (p.77)
- 9.5 Notes (p.79)

## Part IV — Finite Data Types (p.81)

### 10. Product Types — p.83 **[body]** [txt L4447]
- 10.1 Nullary and Binary Products (p.83)
- 10.2 Finite Products (p.85)
- 10.3 Primitive Mutual Recursion (p.86)
- 10.4 Notes (p.87)

### 11. Sum Types — p.89 **[body]** [txt L4831]
- 11.1 Nullary and Binary Sums (p.89)
- 11.2 Finite Sums (p.91)
- 11.3 Applications of Sum Types (p.92) — 11.3.1 Void and Unit (p.92); 11.3.2 Booleans (p.92); 11.3.3 Enumerations (p.93); 11.3.4 Options (p.94)
- 11.4 Notes (p.95)

## Part V — Types and Propositions (p.97)

### 12. Constructive Logic — p.99 *[TOC only]*
- 12.1 Constructive Semantics (p.100)
- 12.2 Constructive Logic (p.100) — 12.2.1 Provability (p.101); 12.2.2 Proof Terms (p.103)
- 12.3 Proof Dynamics (p.104)
- 12.4 Propositions as Types (p.105)
- 12.5 Notes (p.105)

### 13. Classical Logic — p.109 *[TOC only]*
- 13.1 Classical Logic (p.110) — 13.1.1 Provability and Refutability (p.110); 13.1.2 Proofs and Refutations (p.112)
- 13.2 Deriving Elimination Forms (p.114)
- 13.3 Proof Dynamics (p.115)
- 13.4 Law of the Excluded Middle (p.117)
- 13.5 The Double-Negation Translation (p.118)
- 13.6 Notes (p.119)

## Part VI — Infinite Data Types (p.121)

### 14. Generic Programming — p.123 *[TOC only]*
- 14.1 Introduction (p.123)
- 14.2 Polynomial Type Operators (p.123)
- 14.3 Positive Type Operators (p.126)
- 14.4 Notes (p.127)

### 15. Inductive and Coinductive Types — p.129 *[TOC only]*
- 15.1 Motivating Examples (p.129)
- 15.2 Statics (p.132) — 15.2.1 Types (p.133); 15.2.2 Expressions (p.133)
- 15.3 Dynamics (p.134)
- 15.4 Solving Type Equations (p.135)
- 15.5 Notes (p.136)

## Part VII — Variable Types (p.139)

### 16. System F of Polymorphic Types — p.141 **[body]** [txt L5458]
- 16.1 Polymorphic Abstraction (p.142)
- 16.2 Polymorphic Definability (p.145) — 16.2.1 Products and Sums (p.145); 16.2.2 Natural Numbers (p.146)
- 16.3 Parametricity Overview (p.147)
- 16.4 Notes (p.148)

### 17. Abstract Types — p.151 *[TOC only]*
- 17.1 Existential Types (p.151) — 17.1.1 Statics (p.152); 17.1.2 Dynamics (p.152); 17.1.3 Safety (p.153)
- 17.2 Data Abstraction (p.153)
- 17.3 Definability of Existential Types (p.155)
- 17.4 Representation Independence (p.155)
- 17.5 Notes (p.157)

### 18. Higher Kinds — p.159 *[TOC only]*
- 18.1 Constructors and Kinds (p.160)
- 18.2 Constructor Equality (p.161)
- 18.3 Expressions and Types (p.162)
- 18.4 Notes (p.163)

## Part VIII — Partiality and Recursive Types (p.165)

### 19. System PCF of Recursive Functions — p.167 **[body]** [txt L6027]
- 19.1 Statics (p.169)
- 19.2 Dynamics (p.170)
- 19.3 Definability (p.171)
- 19.4 Finite and Infinite Data Structures (p.173)
- 19.5 Totality and Partiality (p.174)
- 19.6 Notes (p.175)

### 20. System FPC of Recursive Types — p.177 *[TOC only]*
- 20.1 Solving Type Equations (p.178)
- 20.2 Inductive and Coinductive Types (p.179)
- 20.3 Self-Reference (p.180)
- 20.4 The Origin of State (p.182)
- 20.5 Notes (p.183)

## Part IX — Dynamic Types (p.185)

### 21. The Untyped λ-Calculus — p.187 *[TOC only]*
- 21.1 The λ-Calculus (p.187)
- 21.2 Definability (p.188)
- 21.3 Scott's Theorem (p.190)
- 21.4 Untyped Means Uni-Typed (p.192)
- 21.5 Notes (p.193)

### 22. Dynamic Typing — p.195 *[TOC only]*
- 22.1 Dynamically Typed PCF (p.196)
- 22.2 Variations and Extensions (p.199)
- 22.3 Critique of Dynamic Typing (p.201)
- 22.4 Notes (p.202)

### 23. Hybrid Typing — p.205 *[TOC only]*
- 23.1 A Hybrid Language (p.205)
- 23.2 Dynamic as Static Typing (p.207)
- 23.3 Optimization of Dynamic Typing (p.208)
- 23.4 Static Versus Dynamic Typing (p.210)
- 23.5 Notes (p.211)

## Part X — Subtyping (p.213)

### 24. Structural Subtyping — p.215 *[TOC only]*
- 24.1 Subsumption (p.215)
- 24.2 Varieties of Subtyping (p.216)
- 24.3 Variance (p.218)
- 24.4 Dynamics and Safety (p.223)
- 24.5 Notes (p.224)

### 25. Behavioral Typing — p.227 *[TOC only]*
- 25.1 Statics (p.228)
- 25.2 Boolean Blindness (p.234)
- 25.3 Refinement Safety (p.236)
- 25.4 Notes (p.237)

## Part XI — Dynamic Dispatch (p.241)

### 26. Classes and Methods — p.243 *[TOC only]*
- 26.1 The Dispatch Matrix (p.244)
- 26.2 Class-Based Organization (p.246)
- 26.3 Method-Based Organization (p.247)
- 26.4 Self-Reference (p.248)
- 26.5 Notes (p.250)

### 27. Inheritance — p.253 *[TOC only]*
- 27.1 Class and Method Extension (p.253)
- 27.2 Class-Based Inheritance (p.254)
- 27.3 Method-Based Inheritance (p.255)
- 27.4 Notes (p.256)

## Part XII — Control Flow (p.259)

### 28. Control Stacks — p.261 **[body]** [txt L6724]
- 28.1 Machine Definition (p.261)
- 28.2 Safety (p.263)
- 28.3 Correctness of the Stack Machine (p.264) — 28.3.1 Completeness (p.265); 28.3.2 Soundness (p.266)
- 28.4 Notes (p.267)

### 29. Exceptions — p.269 **[body]** [txt L7194]
- 29.1 Failures (p.269)
- 29.2 Exceptions (p.271)
- 29.3 Exception Values (p.272)
- 29.4 Notes (p.273)

### 30. Continuations — p.275 *[TOC only]*
- 30.1 Overview (p.275)
- 30.2 Continuation Dynamics (p.277)
- 30.3 Coroutines from Continuations (p.278)
- 30.4 Notes (p.281)

## Part XIII — Symbolic Data (p.283)

### 31. Symbols — p.285 *[TOC only]*
- 31.1 Symbol Declaration (p.286) — 31.1.1 Scoped Dynamics (p.286); 31.1.2 Scope-Free Dynamics (p.287)
- 31.2 Symbol References (p.288) — 31.2.1 Statics (p.288); 31.2.2 Dynamics (p.289); 31.2.3 Safety (p.289)
- 31.3 Notes (p.290)

### 32. Fluid Binding — p.293 *[TOC only]*
- 32.1 Statics (p.293)
- 32.2 Dynamics (p.294)
- 32.3 Type Safety (p.295)
- 32.4 Some Subtleties (p.296)
- 32.5 Fluid References (p.297)
- 32.6 Notes (p.299)

### 33. Dynamic Classification — p.301 *[TOC only]*
- 33.1 Dynamic Classes (p.301) — 33.1.1 Statics (p.301); 33.1.2 Dynamics (p.302); 33.1.3 Safety (p.303)
- 33.2 Class References (p.303)
- 33.3 Definability of Dynamic Classes (p.304)
- 33.4 Applications of Dynamic Classification (p.305) — 33.4.1 Classifying Secrets (p.305); 33.4.2 Exception Values (p.306)
- 33.5 Notes (p.307)

## Part XIV — Mutable State (p.309)

### 34. Modernized Algol — p.311 **[body]** [txt L7581]
- 34.1 Basic Commands (p.311) — 34.1.1 Statics (p.312); 34.1.2 Dynamics (p.313); 34.1.3 Safety (p.315)
- 34.2 Some Programming Idioms (p.316)
- 34.3 Typed Commands and Typed Assignables (p.317)
- 34.4 Notes (p.319)

### 35. Assignable References — p.323 **[body]** [txt L8371]
- 35.1 Capabilities (p.323)
- 35.2 Scoped Assignables (p.324)
- 35.3 Free Assignables (p.326)
- 35.4 Safety (p.328)
- 35.5 Benign Effects (p.330)
- 35.6 Notes (p.332)

### 36. Lazy Evaluation — p.335 *[TOC only]*
- 36.1 PCF By-Need (p.336)
- 36.2 Safety of PCF By-Need (p.338)
- 36.3 FPC By-Need (p.340)
- 36.4 Suspension Types (p.341)
- 36.5 Notes (p.343)

## Part XV — Parallelism (p.345)

### 37. Nested Parallelism — p.347 **[body]** [txt L9081]
- 37.1 Binary Fork-Join (p.347)
- 37.2 Cost Dynamics (p.350)
- 37.3 Multiple Fork-Join (p.353)
- 37.4 Bounded Implementations (p.355)
- 37.5 Scheduling (p.359)
- 37.6 Notes (p.360)

### 38. Futures and Speculations — p.363 *[TOC only]*
- 38.1 Futures (p.364) — 38.1.1 Statics (p.364); 38.1.2 Sequential Dynamics (p.364)
- 38.2 Speculations (p.365) — 38.2.1 Statics (p.365); 38.2.2 Sequential Dynamics (p.365)
- 38.3 Parallel Dynamics (p.366)
- 38.4 Pipelining With Futures (p.368)
- 38.5 Notes (p.369)

## Part XVI — Concurrency and Distribution (p.371)

### 39. Process Calculus — p.373 *[TOC only]*
- 39.1 Actions and Events (p.373)
- 39.2 Interaction (p.375)
- 39.3 Replication (p.377)
- 39.4 Allocating Channels (p.378)
- 39.5 Communication (p.380)
- 39.6 Channel Passing (p.383)
- 39.7 Universality (p.385)
- 39.8 Notes (p.386)

### 40. Concurrent Algol — p.389 **[body]** [txt L10187]
- 40.1 Concurrent Algol (p.390)
- 40.2 Broadcast Communication (p.392)
- 40.3 Selective Communication (p.394)
- 40.4 Free Assignables as Processes (p.396)
- 40.5 Notes (p.398)

### 41. Distributed Algol — p.399 *[TOC only]*
- 41.1 Statics (p.399)
- 41.2 Dynamics (p.402)
- 41.3 Safety (p.404)
- 41.4 Notes (p.404)

## Part XVII — Modularity (p.407)

### 42. Modularity and Linking — p.409 *[TOC only]*
- 42.1 Simple Units and Linking (p.409)
- 42.2 Initialization and Effects (p.410)
- 42.3 Notes (p.412)

### 43. Singleton Kinds and Subkinding — p.413 *[TOC only]*
- 43.1 Overview (p.414)
- 43.2 Singletons (p.414)
- 43.3 Dependent Kinds (p.416)
- 43.4 Higher Singletons (p.419)
- 43.5 Notes (p.421)

### 44. Type Abstractions and Type Classes — p.423 *[TOC only]*
- 44.1 Type Abstraction (p.424)
- 44.2 Type Classes (p.425)
- 44.3 A Module Language (p.428)
- 44.4 First- and Second-Class (p.432)
- 44.5 Notes (p.433)

### 45. Hierarchy and Parameterization — p.435 *[TOC only]*
- 45.1 Hierarchy (p.435)
- 45.2 Abstraction (p.438)
- 45.3 Hierarchy and Abstraction (p.440)
- 45.4 Applicative Functors (p.442)
- 45.5 Notes (p.443)

## Part XVIII — Equational Reasoning (p.445)

### 46. Equality for System T — p.447 *[TOC only]*
- 46.1 Observational Equivalence (p.447)
- 46.2 Logical Equivalence (p.450)
- 46.3 Logical and Observational Equivalence Coincide (p.452)
- 46.4 Some Laws of Equality (p.454) — 46.4.1 General Laws (p.454); 46.4.2 Equality Laws (p.455); 46.4.3 Induction Law (p.455)
- 46.5 Notes (p.456)

### 47. Equality for System PCF — p.457 *[TOC only]*
- 47.1 Observational Equivalence (p.457)
- 47.2 Logical Equivalence (p.458)
- 47.3 Logical and Observational Equivalence Coincide (p.458)
- 47.4 Compactness (p.461)
- 47.5 Lazy Natural Numbers (p.464)
- 47.6 Notes (p.465)

### 48. Parametricity — p.467 *[TOC only]*
- 48.1 Overview (p.467)
- 48.2 Observational Equivalence (p.468)
- 48.3 Logical Equivalence (p.469)
- 48.4 Parametricity Properties (p.474)
- 48.5 Representation Independence, Revisited (p.477)
- 48.6 Notes (p.478)

### 49. Process Equivalence — p.479 *[TOC only]*
- 49.1 Process Calculus (p.479)
- 49.2 Strong Equivalence (p.481)
- 49.3 Weak Equivalence (p.484)
- 49.4 Notes (p.485)

## Part XIX — Appendices (p.487)

- **A.** Answers to the Exercises — p.489 *[TOC only]*
- **B.** Background on Finite Sets — p.541 *[TOC only]*
