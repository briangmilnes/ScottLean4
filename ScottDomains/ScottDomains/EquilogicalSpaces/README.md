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
| `SigmaTopology.lean` | 194 | **0** | Definition 3.4; **Theorems 3.4↔Scott and 3.5, proved** |
| `PartialEquilogical.lean` | 286 | 1 | Definition 3.11; the category `PEqu`; Defs 3.2 and **Theorem 3.6 proved**; 3.12 stated |
| `Extension.lean` | 189 | **0** | **Theorem 3.7, proved**; Σ-open subbasis, finite character, `continuous_of_preimage_memSet` |
| `CartesianClosure.lean` | 154 | **0** | **Theorem 3.13's currying step, proved**; what Theorem 3.8 still owes |
| `ALat.lean` | 196 | **0** | **the category `ALat`, proved**; `BoundedComplete` for `CompleteLattice`; `ScottHom` is a complete lattice |
| `ProductAlgebraic.lean` | 118 | **0** | **`IsAlgebraic (α × β)`, proved**; `AlgebraicLattice.prod` |
| `ALatProducts.lean` | 103 | **0** | **`HasFiniteProducts ALat`, proved**: terminal object and binary products |
| `ALatClosed.lean` | 132 | **0** | **Theorem 3.8, proved**: `(- × B) ⊣ (B ⟹ -)` |
| `Restriction.lean` | 114 | **0** | **the functor `R : PEqu ⥤ Equ` and its faithfulness, proved** |
| `PowersetRetract.lean` | 113 | **0** | **every algebraic lattice is a continuous retract of a powerset, proved** |
| `Theorems3.lean` | 161 | 4 | Theorems 3.10, 3.13 stated; footnote 4 as a claim |
| **Total** | **1961** | **5** | |

### Theorem 3.12: two of four pieces done

The paper's proof names three properties of the restriction functor. Following
that structure exactly keeps the remaining work named rather than diffuse:

| Piece | Status |
| ----- | ------ |
| the functor `R` | **proved** (`Restriction.lean`) |
| `R` faithful | **proved** — `MapEquiv` only tests maps at `≡`-related arguments, and `A.Rel x y` already forces `x` and `y` total |
| `R` full | the **retraction is now proved** (`PowersetRetract.lean`); what remains is transporting Theorem 3.7 along it — embed into `𝒫 (K L)`, extend there, retract back — and reading off fullness |
| `R` essentially surjective | owed: the witness is `𝒫 Ω_ℰ` with the relation transported along `nbhdFilter`, whose total part is `range nbhdFilter`, homeomorphic to `ℰ` by Theorem 3.6 (**proved**). `IsAlgebraic (Set X)` is available from `ScottDomains.Powerset`, so the witness *is* an object; what remains is building it and the isomorphism. |

Build: `lake -d ~/projects/ScottLean4/ScottDomains build` — 1546 jobs, 0 errors.

### Theorem 3.7, proved

`Extension.lean` discharges the Extension Theorem. `memSet a = { S | a ∈ S }` is
Σ-open; `f ⁻¹' (memSet a)` is therefore cut out on the subspace by an open
`V a ⊆ X`, and `g x = { a | x ∈ V a }` is the extension. Continuity is the
finite-character property: for Σ-open `U`,

    g ⁻¹' U = ⋃ { ⋂_{a ∈ F} V a  |  F finite, F ∈ U }

which is open because each inner intersection is finite. `⊆` uses
`exists_finite_subset_mem_of_isOpen`, `⊇` uses upward closure.

That finite subset comes from `sigmaOpen_iff_isOpen` — **Definition 3.4's literal
wording, with its arbitrary `S` and finite `S₀`, is exactly what the proof
needs**, and Mathlib's directed-set formulation would not have handed it over.
The bridging lemma proved in r0057 paid for itself here.
Library `sorry` count 3 → 10 (the 3 pre-existing are in `Lemma30` and
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
| `bauerBirkedalScott04_theorem_3_6_embedding` | 3.6 Embedding (topological half only) | `PartialEquilogical` |
| `bauerBirkedalScott04_theorem_3_7_extension` | 3.7 Extension | `PartialEquilogical` |
| `bauerBirkedalScott04_theorem_3_12` | 3.12 `Equ ≃ PEqu` | `PartialEquilogical` |
| `…_theorem_3_10_hasLimits` | 3.10 | `Theorems3` |
| `…_theorem_3_10_hasColimits` | 3.10 | `Theorems3` |
| `…_theorem_3_10_hasFiniteProducts` | 3.10 | `Theorems3` |
| `bauerBirkedalScott04_theorem_3_13` | 3.13 cartesian closure | `Theorems3` |

Plus three `Prop`-valued claims, asserted nowhere:
`Theorem310RegularWellPowered`, `Theorem310RegularCoWellPowered`,
`Theorem310NotWellPowered`.

### A lemma this development had to supply

`DirectedOn.exists_upperBound_of_finite` — a finite subset of a directed set has
an upper bound **inside that set** — is proved in `SigmaTopology.lean` by
induction on the finite subset, because neither Mathlib nor this package carries
it: searched `Mathlib/Order/Directed.lean`, `Mathlib/Order/Bounds/Basic.lean`,
`ScottDomains/Domain.lean`, `ScottDomains/IdealCompletion.lean`. Mathlib's
`Finset.exists_le` is the statement for a directed *order*, not a directed
*subset*, and it is the subset form Definition 3.4 needs. It is a candidate for
upstreaming.

It is what makes `sigmaOpen_iff_isOpen` go through, and that in turn is what lets
every later result be attacked through Definition 3.4's literal wording
(arbitrary `S`, finite `S₀`) rather than through Mathlib's directed-set
formulation.

## Not yet stated

### §3, Theorem 3.8 — partly done, see `CartesianClosure.lean`

The paper's proof of 3.13 names two halves. They are now separated, and one is
closed:

| Half | Source | Status |
| ---- | ------ | ------ |
| the currying isomorphism of algebraic lattices | `ScottDomains.Currying.scottHomCurry` | already in this package |
| that it preserves the partial equivalence relation | `scottHomCurry_homRel` | **proved** |

The paper calls the second half "self-proving … just a matter of unpacking the
definitions", and it is: the two sides are the same quantifier prefix with the
pair `(x, u)` split or joined, and the proof is a single term. `ProdRel` and
`HomRel` there are Definition 3.11's product and exponential relations, taken
unbundled so the result does not depend on the exponential being an object.

**Both items Theorem 3.8 previously owed are now done** — see `ALat.lean`:

1. `completeLattice_boundedComplete` — a complete lattice is bounded complete.
   One line, and sound because `CompleteLattice.toCompletePartialOrder` is
   defined with `sSup := sSup`, so the `SupSet` the `CompletePartialOrder`
   carries is literally the lattice's own and `isLUB_sSup` discharges the field
   with no compatibility condition. This is what had blocked Theorem 3.8 from
   using the package's own function-space result.
2. `AlgebraicLattice` and `alatCategory` — the bundled category, objects
   complete-and-algebraic lattices, morphisms `ScottHom`. Unlike `Equ` and
   `PEqu` the morphisms are honest functions rather than equivalence classes, so
   the laws are `ext`-then-`rfl`.

Together they yield `isAlgebraic_scottHom`, **proved by `inferInstance`**: the
exponential's carrier is an algebraic object. The `inferInstance` succeeding *is*
the evidence that item 1 unblocked `FunctionSpaceDomain`.

3. `scottHomCompleteLattice` — `ScottHom α β` is a complete lattice when `β` is,
   built on the package's **existing** `SupSet`, so no second one is introduced
   and no `SupSet` diamond arises.

   Why that works is worth recording. `ScottHom.lean` defines `sSup` by a `dite`
   on *continuity of the pointwise supremum*, not on directedness, and says so
   deliberately: "Directedness and boundedness are then two *sufficient*
   conditions, neither privileged in the definition." A complete-lattice codomain
   is a third such condition, and it makes the pointwise supremum continuous for
   **every** set — suprema commute, `⨆ᵢ ⨆ₓ = ⨆ₓ ⨆ᵢ`, unconditionally. So the
   `dite` always takes the positive branch and the `const ⊥` junk value never
   fires. One application of the package's own
   `scottContinuous_pointwiseSup_of_forall_isLUB` proves it.

   It is a **`def`, not an `instance`**, on purpose. Mathlib's
   `completeLatticeOfSup` documents itself as having "bad definitional
   properties": it sets `bot := sSup ∅`, whereas the package's
   `CompletePartialOrder (ScottHom α β)` sets `bot := const ⊥`. Those agree
   propositionally but not definitionally, and registering the instance globally
   would create an `OrderBot` diamond across a 1538-job library — the same hazard
   `ScottHom.lean` records as having broken an `Iff.rfl` in r0004. Opt in with
   `letI`. Proving `sSup ∅ = const ⊥` and hand-rolling `bot` would let it become
   a safe instance; that is the next small task.

4. `isAlgebraic_prod` — the product of two algebraic lattices is algebraic
   (`ProductAlgebraic.lean`). `ScottDomains.Product` supplied
   `CompletePartialOrder (α × β)` but not this, so `A × B` could not previously
   be an object of `ALat` at all. With it, `AlgebraicLattice.prod` exists.

   Directedness of `compactsBelow (x, y)` turns out to be free in the lattice
   setting: the join of two compacts below `(x, y)` is compact by the package's
   `isCompactElement_of_isLUB_pair`, and still below `(x, y)`. Only the
   least-upper-bound half needs product reasoning, through
   `isCompactElement_prod` — a pair of compacts is compact, the two coordinates
   being located in *different* members of the directed set and merged by
   directedness, the same move `Currying.lean` makes when it uncurries.

   Stated for complete **lattices**, not arbitrary algebraic cpos. Over a general
   cpo the join need not exist and directedness would instead need the
   *projection* direction — `(a, b)` compact implies `a` and `b` compact — which
   requires a separate argument through `(fun x => (x, b)) '' s`. `ALat` does not
   need it, so it is not proved; noted in the module in case the general case is
   ever wanted.

5. `HasFiniteProducts AlgebraicLattice` — **done** (`ALatProducts.lean`).
   `alatIsTerminal` exhibits `PUnit` as terminal, `prodIsLimit` exhibits
   `AlgebraicLattice.prod` as a binary product, and Mathlib's
   `hasFiniteProducts_of_has_binary_and_terminal` assembles the rest. No new
   mathematics: projections are `Morphism.prodFst`/`prodSnd`, the pairing is
   `Combinator.prodMkHom`, and every obligation is `ext` then `rfl` or a
   projection of a hypothesis.

   One piece of bundled-category friction worth knowing: typeclass search will
   **not** unfold `A ⟶ B` to `ScottHom A.carrier B.carrier`, so neither function
   application nor `DFunLike.congr_fun` works on a morphism written with `⟶`.
   `homFunLike` re-exports the instance and `hom_ext` the extensionality lemma;
   with those in place the limit proofs are one line each.

6. **Theorem 3.8 is proved** (`ALatClosed.lean`): `prodExpAdjunction` gives
   `(- × B) ⊣ (B ⟹ -)`, and `isLeftAdjoint_prodFunctorRight` states it in the
   paper's §2 phrasing — "the functor `· × B` is adjoint to `B → ·` for all
   objects `B`". No `sorry`.

   Two things were needed beyond the products. `scottContinuous_postcomp`:
   post-composing with a fixed `q` is Scott-continuous *as a map on the function
   space*, which is the exponential's morphism part. The package proves this for
   endomorphisms as `Skeleton.Lemma17.scottContinuous_compFun`; the argument
   generalizes verbatim to `q : β ⟶ γ`, which is what a functor between
   different objects needs. And `prodFunctorRight`, the concrete functor
   `X ↦ X × B`, built here rather than taken as Mathlib's
   `Limits.prod.functor.obj B` — the latter goes through `limit`, which selects
   a cone by `Classical.choice`, so it is *isomorphic* to `prodFan` but not
   *definitionally* it, and every naturality obligation would need transport
   before any `rfl` could fire. With the product on the nose they are all `rfl`.

   The adjunction itself is `scottHomCurry` from `ScottDomains.Currying`,
   packaged by `Adjunction.mkOfHomEquiv`.

`CartesianClosure.lean` still states only `Theorem38CurryingBijection` because
that is what *it* contains; the full Theorem 3.8 now lives in `ALatClosed.lean`.

Definition 3.11 deliberately uses the package's `ScottDomains.IsAlgebraic` (over
`CompletePartialOrder`, reached from `CompleteLattice` by
`CompleteLattice.toCompletePartialOrder`) rather than a Mathlib equivalent,
precisely so this interoperation is available. Also relevant:
`ScottDomains/StepFunction.lean`, `ScottDomains/Product.lean`.

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
