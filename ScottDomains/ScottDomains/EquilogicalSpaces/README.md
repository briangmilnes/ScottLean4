# EquilogicalSpaces

Lean 4 / Mathlib formalization of

> A. Bauer, L. Birkedal and D. S. Scott, **Equilogical Spaces**,
> *Theoretical Computer Science* **315**(1):35–59, 2004.

Source PDF: `ScottDomains/papers/Bauer Birkedal Scott 2004 Equilogical Spaces.pdf`
(Elsevier preprint, 2 March 2001, 27 pp., 40 references). Section and theorem
numbers used in the Lean names are the printed ones.

## Relation to `ScottLean/Scott/Scott1998ANewCategory.lean`

The paper's genesis is Scott's manuscript *A New Category?* (December 1996;
Version 2, 19 April 1998), which has its own formalization in the sibling
`ScottLean` library. **The two developments are independent** and are meant to
stay that way: that one is core Lean 4 with a hand-rolled `TopSpace` and no
Mathlib; this one is Mathlib-based and uses `CategoryTheory`. Results here are
attributed to the 2004 paper.

## Modules

| Module | Lines | `sorry` | Contents |
| ------ | ----: | ------: | -------- |
| `Basic.lean` | 201 | **0** | Definition 3.9: objects, equivariant maps, `MapEquiv`, and the category `Equ` |
| `Theorems3.lean` | 161 | 4 | Theorems 3.10 and 3.13 as obligations; footnote 4 as a claim |

Build: `lake -d ~/projects/ScottLean4/ScottDomains build`. The whole library
compiles at 1534 jobs, 0 errors.

## What is proved

`Basic.lean` carries no proof holes. Proved outright:

- `mapSetoid` — `MapEquiv` is an equivalence relation on the equivariant maps
  `A → B`. The paper calls this "an elementary exercise"; it is discharged here.
- `equCategory` — `Equ` is a `LargeCategory`, with `Hom A B` a genuine
  `Quotient` of `Equivariant A B` by `mapSetoid`, and `id_comp`, `comp_id`,
  `assoc` all proved as equalities of classes.
- `comp_congr` — composition respects `MapEquiv` in both arguments, which is
  what lets it descend to the quotient. Without it there is no category.

Two encoding points that are easy to get wrong, and are deliberate here:

1. **Morphisms are equivalence classes, not maps.** Stating the category laws up
   to `Eq` on representatives would be a different and false claim.
2. **`MapEquiv f g` relates `f` at `x` to `g` at `y` for distinct `≡`-related
   points**, per Definition 3.9(2) — not merely pointwise `f x ≡ g x`. The
   diagonal reading is strictly weaker. A consequence: `MapEquiv f f` *is* the
   equivariance of `f`, so the relation is an equivalence only on equivariant
   maps, never on bare continuous ones. `mapEquiv_trans` further derives
   `A.Rel x x` from `A.Rel x y` rather than taking it from reflexivity, so the
   same argument survives the move to partial equivalence relations in
   Definition 3.11.

## What is stated but not proved

Four `sorry`s, all in `Theorems3.lean`:

| Declaration | Paper | Statement |
| ----------- | ----- | --------- |
| `bauerBirkedalScott04_theorem_3_10_hasLimits` | 3.10 | `HasLimitsOfSize.{u,u} Equ` |
| `bauerBirkedalScott04_theorem_3_10_hasColimits` | 3.10 | `HasColimitsOfSize.{u,u} Equ` |
| `bauerBirkedalScott04_theorem_3_10_hasFiniteProducts` | 3.10 | `HasFiniteProducts Equ` |
| `bauerBirkedalScott04_theorem_3_13` | 3.13 | `∀ B, Functor.IsLeftAdjoint (prod.functor.obj B)` |

Theorem 3.13 is stated as an adjunction because that is how the paper states
cartesian closure in §2 — "the functor `· × B` is adjoint to `B → ·` for all
objects `B`" — and because this Mathlib revision has no `CartesianClosed` class:
it was refactored into `CartesianMonoidalCategory` + `MonoidalClosed`, which
would drag in chosen-product data the statement does not need.

Three `Prop`-valued claims, asserted nowhere:

- `Theorem310RegularWellPowered`, `Theorem310RegularCoWellPowered` — `Small.{u}`
  on `RegularSubobject` / `RegularQuotient`. Claims rather than instances because
  Mathlib has no `RegularWellPowered` class to instantiate.
- `Theorem310NotWellPowered` — footnote 4, below.

## Footnote 4: `Equ` is not well-powered

> The authors are indebted to Peter Johnstone for pointing out that, contrary to
> the assertion made in Scott's original unpublished manuscript, `Equ` is *not*
> well powered, for there are fairly simple examples of objects in the category
> with an unbounded number of non-isomorphic subobjects.

Two consequences enforced in `Theorems3.lean`:

1. **No `WellPowered EquilogicalSpace` instance may be declared**, however
   natural it looks beside the completeness instances. It is false, and an
   instance would let typeclass resolution silently prove things this category
   does not satisfy. This is why every name carries `regular`.
2. `Theorem310NotWellPowered` is a claim `def`, **not** a `theorem … := sorry`.
   Discharging it needs Johnstone's counterexample, which the paper cites but
   does not exhibit; until then, reading "an unbounded number of non-isomorphic
   subobjects" as failure of `Small.{u}` is an unchecked encoding. A `sorry`
   asserts the statement is true as written. A claim records it without
   asserting.

## Not yet formalized

Nothing below is stated in Lean. Writing statements for them would mean
inventing encodings these modules cannot yet express faithfully, so they are
listed rather than stubbed.

**§3, blocked on the Σ-topology and `PEqu`** — Definition 3.11 (`PEqu`:
algebraic lattices with partial equivalence relations), Theorem 3.5, Theorem 3.6
(Embedding), Theorem 3.7 (Extension), Theorem 3.8 (`ALat` is cartesian closed),
Theorem 3.12 (`Equ ≃ PEqu`). These four Scott facts are the actual proof spine:
3.12 is faithful by definition, full by 3.7, essentially surjective by 3.6, and
3.13 transports cartesian closure from 3.8. Formalizing 3.13 honestly means
formalizing these first.

**§4, dependent type theory** — `Assm(ALat)`, `Mod(ALat)`, Theorem 4.3
(`Equ ≃ PEqu ≃ Mod(ALat)`), Theorems 4.4–4.9, `UFam(Mod(ALat))`, and Theorem
4.12 (`𝒫` is a split closed comprehension category, hence a model of dependent
type theory). Note the paper's two *negative* results here: the fibration of
uniform modest sets over assemblies cannot be shown essentially small, so there
is no impredicative universe as there is over a PCA; and `PER(ALat)` is not
well-powered, so there is no realizability topos — left open in the paper.

**§5, Kleene–Kreisel** — Berger's dense/codense totality, `PER(Dom)`,
`DPER(Dom)`, Theorem 5.1 (`DPER(Dom) ≃ PEqu`), Theorem 5.2, and the hierarchy
`𝒩ⱼ = 𝒩ⱼ₋₁ → 𝒩₀` whose equivalence classes are the countable functionals of
pure type `j`.

## Naming

`CLAUDE.md` fixes `<author><year?>_<kind>_<N>_<M>[_<semantic>]` for a result by
another author and gives only single-author examples (`jung_theorem_1_37`,
`gunter87_lemma_24_MPair`). For three authors that is read here as
`bauerBirkedalScott04_theorem_3_13`. **The author slot is a reading of the rule,
not something the rule states** — flagged here rather than assumed silently, and
cheap to change while only two modules use it.
