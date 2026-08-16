# EquilogicalSpaces

Lean 4 / Mathlib formalization of

> A. Bauer, L. Birkedal and D. S. Scott, **Equilogical Spaces**,
> *Theoretical Computer Science* **315**(1):35–59, 2004.

Source PDF: `ScottDomains/papers/Bauer Birkedal Scott 2004 Equilogical Spaces.pdf`
(Elsevier preprint, 2 March 2001, 27 pp., 40 references). Section and theorem
numbers in the Lean names are the printed ones.

**Goal: the entire paper, formalized and proved.** This file is the program
tracker. It records what the kernel has accepted, what is stated but owed, and
what is not yet stated — so progress is a measurement rather than an impression.

## Relation to `ScottLean/Scott/Scott1998ANewCategory.lean`

The paper's genesis is Scott's manuscript *A New Category?* (December 1996;
Version 2, 19 April 1998), which has its own formalization in the sibling
`ScottLean` library. **The two developments are independent** and stay that way:
that one is core Lean 4 with a hand-rolled `TopSpace`; this one is Mathlib-based.
Results here are attributed to the 2004 paper.

## Modules

| Module | Lines | `sorry` | Contents |
| ------ | ----: | ------: | -------- |
| `Basic.lean` | 201 | **0** | Definition 3.9; the category `Equ` |
| `SigmaTopology.lean` | 128 | 1 | Definition 3.4; **Theorem 3.5, proved** |
| `PartialEquilogical.lean` | 236 | 3 | Definition 3.11; the category `PEqu`; Theorems 3.6, 3.7, 3.12 stated |
| `Theorems3.lean` | 161 | 4 | Theorems 3.10, 3.13 stated; footnote 4 as a claim |
| **Total** | **726** | **8** | |

Build: `lake -d ~/projects/ScottLean4/ScottDomains build` — 1536 jobs, 0 errors.
Library `sorry` count 3 → 11 (the 3 pre-existing are in `Lemma30` and
`Effective/A3StepDecidable`).

## Proved

- **The category `Equ`** (`Basic.lean`, no proof holes). `Hom A B` is a genuine
  `Quotient` of `Equivariant A B` by `MapEquiv`; `id_comp`, `comp_id`, `assoc`
  are equalities *of classes*. `mapSetoid` discharges what the paper calls "an
  elementary exercise"; `comp_congr` is what lets composition descend.
- **The category `PEqu`** (`PartialEquilogical.lean`), same structure over a
  *partial* equivalence relation.
- **Theorem 3.5**, both halves: the Σ-topology on a complete lattice is `T₀`, and
  its specialization ordering is exactly `≤`. The `T₀` half is by citation —
  Mathlib's `Topology.IsScott.instT0Space` — restated under the paper's number so
  the dependency is visible. The specialization half is two short steps: forward
  by instantiating at `(Iic y)ᶜ`, backward because Scott opens are upper sets.
- `EquilogicalSpace.ofScottLattice` — what 3.5 is *for*: it makes a complete
  lattice an object of `Equ`, the `T₀` field filled by 3.5.

Two encoding decisions, deliberate and load-bearing:

1. **Morphisms are equivalence classes, not maps.** Stating the category laws up
   to `Eq` on representatives would be a different and false claim.
2. **`MapEquiv f g` relates `f` at `x` to `g` at `y` for distinct `≡`-related
   points**, per Definition 3.9(2) — not pointwise `f x ≡ g x`, which is
   strictly weaker. Consequences: `MapEquiv f f` *is* equivariance, so the
   relation is an equivalence only on equivariant maps; and `mapEquiv_trans`
   derives `A.Rel x x` from `A.Rel x y` instead of using reflexivity, which is
   exactly why the identical proof survives the weakening to a PER in
   `PartialEquilogical.lean`.

## Stated and owed — 8 `sorry`s

| Declaration | Paper | Module |
| ----------- | ----- | ------ |
| `sigmaOpen_iff_isOpen` | Def 3.4 ↔ Mathlib Scott | `SigmaTopology` |
| `bauerBirkedalScott04_theorem_3_6_embedding` | 3.6 Embedding | `PartialEquilogical` |
| `bauerBirkedalScott04_theorem_3_7_extension` | 3.7 Extension | `PartialEquilogical` |
| `bauerBirkedalScott04_theorem_3_12` | 3.12 `Equ ≃ PEqu` | `PartialEquilogical` |
| `…_theorem_3_10_hasLimits` | 3.10 | `Theorems3` |
| `…_theorem_3_10_hasColimits` | 3.10 | `Theorems3` |
| `…_theorem_3_10_hasFiniteProducts` | 3.10 | `Theorems3` |
| `bauerBirkedalScott04_theorem_3_13` | 3.13 cartesian closure | `Theorems3` |

Plus three `Prop`-valued claims, asserted nowhere:
`Theorem310RegularWellPowered`, `Theorem310RegularCoWellPowered`,
`Theorem310NotWellPowered`.

### The known obstruction in `sigmaOpen_iff_isOpen`

Definition 3.4 quantifies over **arbitrary** `S` with a **finite** `S₀ ⊆ S`;
Mathlib's Scott topology quantifies over **directed** sets. They agree on a
complete lattice, but the reverse direction needs the finite suprema of `S` to
form a directed set with supremum `⋁ S`, and the forward direction needs: a
finite subset of a directed set has an upper bound *inside* that set. **Neither
Mathlib nor this package appears to carry that second lemma** — searched
`Mathlib/Order/Directed.lean`, `Mathlib/Order/Bounds/Basic.lean`,
`ScottDomains/Domain.lean`, `ScottDomains/IdealCompletion.lean`. It has to be
proved by induction on the finite set. That is the next concrete task.

## Not yet stated

### §3, the remaining link

**Theorem 3.8: `ALat` is cartesian closed.** Needs a bundled category of
algebraic lattices. Most of the mathematical content already exists in this
package and should be reused rather than reproved:

- `ScottDomains/FunctionSpaceDomain.lean` — `IsAlgebraic (ScottHom α β)` for `α`
  algebraic and `β` algebraic and bounded complete. That is the exponential's
  carrier being an object.
- `ScottDomains/Currying.lean` — `D → (E → F) ≅ (D × E) → F`, the currying
  isomorphism, with the joint-vs-separate continuity argument already done.
- `ScottDomains/StepFunction.lean`, `ScottDomains/Product.lean`.

Definition 3.11 above deliberately uses the package's `ScottDomains.IsAlgebraic`
(over `CompletePartialOrder`, reached from `CompleteLattice` by
`CompleteLattice.toCompletePartialOrder`) rather than a Mathlib equivalent,
precisely so this interoperation is available.

### The dependency chain for the headline theorem

    3.5 ─┬─→ 3.6 (Embedding) ──┐
         └─→ 3.7 (Extension) ──┼─→ 3.12 (Equ ≃ PEqu) ──┐
                    3.8 (ALat ccc) ────────────────────┴─→ 3.13 (Equ ccc)

3.13 is *not* provable directly in `Equ`: `Equ` has no evident exponential,
which is the same reason `Top₀` is not cartesian closed. The paper's whole
device is to pass to `PEqu`, where the exponential's carrier is an algebraic
lattice and 3.8 applies. So 3.13 is the **last** thing to fall, not the first.

### §4, dependent type theory

`Assm(ALat)` (Def 4.1), `Mod(ALat)` (Def 4.2), Theorem 4.3
(`Equ ≃ PEqu ≃ Mod(ALat)`), Theorems 4.4–4.9 (ccc, finite limits, regular,
regular subobjects ↔ `𝒫X`, `Γ ⊣ ∇`, reflectivity), `UFam(Mod(ALat))` (Def 4.10),
Theorem 4.11 (split fibration ≃ codomain fibration), Theorem 4.12 (`𝒫` is a
split closed comprehension category, hence a model of dependent type theory).

Two of the paper's own results here are **negative** and must be formalized as
such, not skipped: the fibration of uniform modest sets over assemblies is
complete but cannot be shown essentially small — so there is no impredicative
universe as there is over a PCA; and `PER(ALat)` is not well-powered, so there is
no realizability topos. The paper leaves the latter open.

### §5, Kleene–Kreisel

Berger's separable/dense/codense totality, partial continuous predicates,
`PER(Dom)`, `DPER(Dom)`, the top-adding functor `T`, Theorem 5.1
(`DPER(Dom) ≃ PEqu`), Theorem 5.2 (products and exponentials agree with
totality), and the hierarchy `𝒩ⱼ = 𝒩ⱼ₋₁ → 𝒩₀` whose equivalence classes are the
Kleene–Kreisel countable functionals of pure type `j`.

## Footnote 4: `Equ` is not well-powered

> The authors are indebted to Peter Johnstone for pointing out that, contrary to
> the assertion made in Scott's original unpublished manuscript, `Equ` is *not*
> well powered, for there are fairly simple examples of objects in the category
> with an unbounded number of non-isomorphic subobjects.

Two consequences enforced in `Theorems3.lean`:

1. **No `WellPowered EquilogicalSpace` instance may be declared.** It is false,
   and an instance would let typeclass resolution silently prove things this
   category does not satisfy. Hence `regular` in every name.
2. `Theorem310NotWellPowered` is a claim `def`, **not** a `theorem … := sorry`.
   Discharging it needs Johnstone's counterexample, which the paper cites but
   does not exhibit; until then, reading "an unbounded number of non-isomorphic
   subobjects" as failure of `Small.{u}` is an unchecked encoding. A `sorry`
   asserts a statement is true as written; a claim `def` records it without
   asserting.

## Naming

`CLAUDE.md` fixes `<author><year?>_<kind>_<N>_<M>[_<semantic>]` for a result by
another author, and gives only single-author examples (`jung_theorem_1_37`,
`gunter87_lemma_24_MPair`). For three authors that is read here as
`bauerBirkedalScott04_theorem_3_13`. **The author slot is a reading of the rule,
not something the rule states** — flagged rather than assumed silently, and still
cheap to change.
