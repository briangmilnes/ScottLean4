# Gunter & Scott 1990 — Inventory of Definitions and Theorems

Source: **C. A. Gunter and D. S. Scott, "Semantic Domains,"** *Handbook of
Theoretical Computer Science* Vol. B, North-Holland, 1990, pp. 633–674
([`../papers/Gunter Scott 1990.pdf`](../papers/Gunter%20Scott%201990.pdf)).

This is the work list for the Lean formalization. Every definition and every one
of the paper's **30 numbered results** (Theorems / Lemmas / Proposition 1–30) is
listed in paper order. The **"In Lean / Mathlib?"** column is deliberately empty
— that is the next pass (we go looking in Mathlib together).

> Statements are paraphrased/de-garbled from the PDF (1990 Type-3 fonts render
> `→` as `!`, drop `fi` ligatures, and mangle math symbols), so read them as a
> guide to *what* each result is, not a verbatim quote. Notation: `⊑` order,
> `⨆` directed sup, `⊥` bottom, `≪` way-below, `K(D)` compact elements,
> `Fp(D)` finitary projections.

## §2 Recursive definitions of functions

| § | Kind | Ref | Concept / statement | In Lean / Mathlib? |
|---|------|-----|---------------------|--------------------|
| 2.1 | Def | — | **poset** (partially ordered set) |  |
| 2.1 | Def | — | **directed** subset `M`: every finite `u ⊆ M` has an upper bound in `M` |  |
| 2.1 | Def | — | **cpo**: a poset in which every directed `M` has a least upper bound `⨆M` |  |
| 2.1 | Def | — | **bottom** `⊥`: least element |  |
| 2.1 | Def | — | **monotone** function |  |
| 2.1 | Def | — | **continuous** function: monotone and `f(⨆M) = ⨆f(M)` for directed `M` |  |
| 2.1 | Thm | 1 | **Fixed-Point Theorem**: `D` cpo, `f : D → D` continuous ⟹ least fixed point `⨆ₙ fⁿ(⊥)` exists |  |
| 2.2 | Thm | 2 | **Schröder–Bernstein** for sets (injections both ways ⟹ bijection) |  |
| 2.3 | Def | — | **fixed-point operator** `F`: a (uniform) class of continuous functions choosing fixed points |  |
| 2.3 | Thm | 3 | The standard operator is the **unique uniform** fixed-point operator |  |

## §3 Effectively presented domains

| § | Kind | Ref | Concept / statement | In Lean / Mathlib? |
|---|------|-----|---------------------|--------------------|
| 3.1 | Def | — | **compact (finite) element** `x`: `x ⊑ ⨆M` (directed) ⟹ `x ⊑ y` for some `y ∈ M`; write `K(D)` |  |
| 3.1 | Def | — | **algebraic** cpo: every `x = ⨆{ x' ∈ K(D) : x' ⊑ x }` (directed) |  |
| 3.1 | Def | — | **domain** = algebraic cpo (this paper's central object) |  |
| 3.1 | Def | — | **way-below** `≪` (implicit; the approximation relation behind compactness) |  |
| 3.1 | Def | — | **bounded complete** poset: least element + every bounded subset has a sup |  |
| 3.1 | Def | — | **(countably based) algebraic lattice** |  |
| 3.1 | Def | — | **embedding–projection pair** `(g, f)` |  |
| 3.1 | Def | — | **projection**; **finitary projection** `p`: `p∘p = p ⊑ id`, `im(p)` a domain |  |
| 3.1 | Def | — | **normal subposet** / substructure |  |
| 3.1 | Lem | 4 | The poset `⟨P(C), ◁⟩` of (normal) substructures is a cpo with `{⊥}` least |  |
| 3.1 | Lem | 5 | `D` domain, `p` finitary projection ⟹ compact elements of `im(p)` are `{p(x) : x ∈ K(D)}` |  |
| 3.1 | Thm | 6 | For any domain `D`: **isomorphism** between the cpo of normal substructures and `Fp(D)` (finitary projections) |  |
| 3.1 | Thm | 7 | `D, E` bounded-complete domains ⟹ the function space `D → E` is a bounded-complete domain |  |
| 3.2 | Def | — | **effective presentation** `d : ℕ → K(D)` (surjection); **effectively presented domain** |  |

## §4 Operators and functions

| § | Kind | Ref | Concept / statement | In Lean / Mathlib? |
|---|------|-----|---------------------|--------------------|
| 4.1 | Def | — | **product** `D × E` |  |
| 4.2 | Def | — | **Church's λ-notation** (continuous function abstraction) |  |
| 4.3 | Def | — | **smash product** `D ⊗ E` |  |
| 4.4 | Def | — | **sum** `D + E`; **lift** `D⊥` |  |
| 4.1–4.4 | Lem | 8 | Currying/iso laws for function spaces over cpo's `D, E, F` |  |
| 4.1–4.4 | Lem | 9 | Product/function-space iso laws over cpo's `D, E, F` |  |
| 4.5 | Lem | 10 | `D, E` bounded complete ⟹ `D → E`, `D × E`, `D ⊗ E`, `D + E`, `D⊥` bounded complete (closure) |  |
| 4.5 | Thm | 11 | The **ideal completion** of a countable pre-order `⟨A, ⊢⟩` is a domain (every domain so arises) |  |
| 4.5 | Thm | 12 | Initiality/universal property of a continuous algebra `⟨E, …⟩` satisfying axioms `T` |  |
| 4.5 | Lem | 13 | `D` bounded complete ⟹ the two powerdomains `D]`, `D[` are bounded complete |  |
| 4.5 | Thm | 14 | Equivalent characterizations of a cpo `D` being an (algebraic / bounded-complete) domain |  |

## §5 Powerdomains

| § | Kind | Ref | Concept / statement | In Lean / Mathlib? |
|---|------|-----|---------------------|--------------------|
| 5.1 | Def | — | **powerdomain** intuition (non-deterministic outcomes) |  |
| 5.2 | Def | — | **Hoare (lower)**, **Smyth (upper)**, **Plotkin (convex)** powerdomains |  |
| 5.3 | — | — | Universal and closure properties of powerdomains (see also Lem 13, Lem 28/30) |  |

## §6 Bifinite (SFP) domains

| § | Kind | Ref | Concept / statement | In Lean / Mathlib? |
|---|------|-----|---------------------|--------------------|
| 6.1 | Def | — | **Plotkin order** / **bifinite (SFP) domain**: bilimit of finite pointed posets |  |
| 6.1 | Prop | 15 | Every bounded-complete domain is bifinite |  |
| 6.1 | Thm | 16 | `D` bifinite ⟹ `Fp(D)` (finitary projections) is an algebraic lattice |  |
| 6.2 | Lem | 17 | `D, E` bifinite ⟹ `D → E`, `D × E`, `D ⊗ E`, `D + E`, `D⊥` bifinite (closure — incl. function space) |  |
| 6.2 | Thm | 18 | If `D` and `D → D` are both domains, then `D` is bifinite |  |
| 6.2 | Lem | 19 | `D` domain, closure `r : D → D` (`r∘r = r ⊒ id`) ⟹ `im(r)` is a domain |  |
| 6.2 | Lem | 20 | `D` domain ⟹ `Fc(D)` (finitary closures) is a cpo |  |

## §7 Recursive definitions of domains (universal domain, `D∞`)

| § | Kind | Ref | Concept / statement | In Lean / Mathlib? |
|---|------|-----|---------------------|--------------------|
| 7 | Def | — | **recursive domain equation**; **universal domain** / `D∞` (inverse-limit solution) |  |
| 7 | Thm | 21 | If an operator `F` is **representable** over a cpo `U`, there is a domain `D` with `D ≅ F(D)` |  |
| 7 | Thm | 22 | For any countably-based algebraic lattice `L`, there is a closure `r : P(ℕ) → L` (`P(ℕ)` universal) |  |
| 7 | Lem | 23 | The function-space operator is representable over `P(ℕ)` |  |
| 7 | Lem | 24 | `U` non-trivial cpo; product + function-space representable over `U` ⟹ (setup for universality) |  |
| 7 | Thm | 25 | `U` non-trivial domain representing products & function spaces ⟹ `U` is **universal** |  |
| 7 | Thm | 26 | For any signature `(s₁,…,sₙ)` there are combinators `F₁,…,Fₙ` solving the domain equations |  |
| 7 | Thm | 27 | For any bounded-complete domain `D`, there is a projection of the universal domain onto `D` |  |
| 7 | Lem | 28 | Operators `→, ×, ⊗, +, ()⊥, ()], ()[` are representable over `U` |  |
| 7 | Thm | 29 | `D` bifinite ⟹ `D+` bifinite; solving `D ≅ D+` in the bifinite category |  |
| 7 | Lem | 30 | Operators `→, ×, ⊗, +, ()⊥, ()], ()[` are **p-representable** over the universal bifinite `V` |  |

---

**Totals:** ~30 definitions + **30 numbered results** (Theorems 1–3, 6, 7, 11, 12,
14, 16, 18, 21, 22, 25, 26, 27, 29; Lemmas 4, 5, 8, 9, 10, 13, 17, 19, 20, 23, 24,
28, 30; Proposition 15). Next: fill the **In Lean / Mathlib?** column — reuse what
Mathlib has (cpo, continuity, compact elements, fixed points), define the rest
(starting with `≪`).
