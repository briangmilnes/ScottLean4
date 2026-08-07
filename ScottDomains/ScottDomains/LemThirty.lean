import ScottDomains.Colimit
import ScottDomains.PRep
import ScottDomains.BifiniteUniversal
import ScottDomains.Powerdomain.Plotkin

/-!
# §7.4, Lemma 30: the ten operators, p-representable over `V`

Gunter & Scott, *Semantic Domains*, §7.4. The statement, read off page 43 of the
source PDF rendered at 600 dpi (`scripts/pdf-render.sh`, then
`scripts/pdf-crop.sh`) rather than from `pdftotext`:

> **Lemma 30** The following operators are p-representable over `V`:
> `→`, `⇸`, `×`, `⊗`, `+`, `⊕`, `(·)⊥`, `(·)♯`, `(·)♭`, `(·)♮`.

and the paper's own recipe for the tenth, on the same page:

> As with most of the other operators, to get a representation for `(·)♮`, take a
> pair of continuous functions `Φ♮ : V → V♮`, `Ψ♮ : V♮ → V` such that
> `Φ♮ ∘ Ψ♮ = id` and `Ψ♮ ∘ Φ♮ ⊑ id`. Then `R♮(p) = Ψ♮ ∘ (p♮) ∘ Φ♮` is a
> representation for the convex powerdomain operator.

## Ten, not nine, and the reading is from the image

`pdftotext` renders the operator line as `!, !, , ; +, ; ()?, ()], ()[, ()\`:
the Type 3 bitmap fonts carry no usable `ToUnicode` map, `→` and `⇸` both extract
as `!`, `×`, `⊗` and `⊕` extract as nothing, and `♯`, `♭`, `♮` extract as `]`,
`[`, `\`. At 600 dpi the line is unambiguous and reads

| # | Operator | This development |
| - | -------- | ---------------- |
| 1 | `→` | `PRep.funOp` |
| 2 | `⇸` | `PRep.strictFunOp` |
| 3 | `×` | `PRep.prodOp` |
| 4 | `⊗` | `PRep.smashOp` |
| 5 | `+` | `PRep.sepSumOp` |
| 6 | `⊕` | `PRep.coalSumOp` |
| 7 | `(·)⊥` | `PRep.liftOp` |
| 8 | `(·)♯` | `PRep.smythOp` |
| 9 | `(·)♭` | `PRep.hoareOp` |
| 10 | `(·)♮` | `plotkinOp`, defined below |

Lemma 30's list is Lemma 28's nine in the paper's own order with `(·)♮` appended,
and `lemma30_iff_lemma28_and_plotkin` records that as a kernel-checked
equivalence rather than as prose. Two further differences from Lemma 28 are
visible in the printed line: the carrier is §7.4's bifinite `V`, not §7.3's
bounded-complete `U`; and Lemma 30 spells out "**p**-representable", where
Lemma 28 says "representable" and relies on the redefinition four paragraphs
earlier. Both lemmas are therefore statements about `Fp`, and the second reading
removes the only doubt about Lemma 28 the earlier rounds recorded.

## `Colimit.lean`'s blocking note was stale, and is corrected

`Colimit.lean`'s docstring said the paper's other nine operators "are not present
in this development as functions `Cpo → Cpo` at all", so that `Lem30Arrow` was
the only type-correct conjunct. That was true when it was written and is false
now: `PRep.lean:147–190` defines all nine. Lemma 30 is statable in full, which is
what this file does first.

## The transfer from `U` to `V`, measured

The question worth more than any single conjunct is whether §7.3's per-operator
proofs transfer from `U` to `V`. **They transfer completely, and at zero proof
cost.** `PRep.rep_lift` and `PRep.rep_prod` are stated as

    theorem rep_lift [Domain U] {fn : ScottHom U (WithBot U)} {gr : ScottHom (WithBot U) U}
      (hfg : ∀ y, fn (gr y) = y) (hgf : ∀ x, gr (fn x) ≤ x) : IsPRepresentable U liftOp

over an arbitrary `{U : Type u} [CompletePartialOrder U]`. Nothing in either
statement or either proof mentions `Dyadic.U`, bounded completeness, atomless
Boolean algebras, or any other §7.3 fact: the whole content is the `Fp`
interface plus the paper's retraction pair, passed in as `hfg` and `hgf`. So the
instantiation at `U := V` is `Domain V` — which `Colimit.domain_V` supplies as an
instance — together with the pair. `rep_lift_V` and `rep_prod_V` below are those
two instantiations, and each is one `obtain` and one `exact`.

**Lemma 30 is therefore not ten fresh proofs.** It is `PRep`'s ten generic
schemes, of which two exist today and seven are this round's streams 3 and 4,
plus ten retraction pairs over `V`. The pairs are where the work is, and they are
where Theorem 29's second sentence is spent.

## Theorem 29's second sentence supplies eight of the ten pairs

The paper's recipe needs, for each operator `F`, a pair `Φ_F : V → F(V)`,
`Ψ_F : F(V) → V` with `Φ_F ∘ Ψ_F = id` and `Ψ_F ∘ Φ_F ⊑ id` — precisely
`ScottHom.IsEmbeddingProjectionPair Ψ_F Φ_F`, which is precisely the conclusion
of `Colimit.Thm29Second` at `E := F(V)`. Its one hypothesis is `IsBifinite F(V)`,
and that is **Lemma 17**, whose ten conjuncts (`ClosureProperties.lemma17`) are
the same ten operators as Lemma 30's. So

    Thm29Second + Lemma 17 ⟹ all ten retraction pairs over V,

except that two of Lemma 17's ten conjuncts carry an instance the others do not:

| # | Lemma 17 conjunct | Instances | At `V` |
| - | ----------------- | --------- | ------ |
| 1 | `lem17_fun` | `[Domain α] [Domain β] [BoundedComplete β]` | **blocked** |
| 2 | `lem17_strictFun` | `[Domain α] [Domain β] [BoundedComplete β]` | **blocked** |
| 3 | `lem17_prod`, `lem17_smash`, `lem17_sum`, `lem17_separated` | `[Domain α] [Domain β]` | available |
| 4 | `lem17_lift`, `lem17_plotkin`, `lem17_smyth`, `lem17_hoare` | `[Domain α]` | available |

Five of the eight available conjuncts land at a result this development proves to
be a domain, so they go through `Thm29SecondAtDomains`, which `Thm29Normal`
implies; `⊗`, `+` and `⊕` land at a type never proved algebraic here and so still
take the stronger `Colimit.Thm29Second`.

`BoundedComplete V` is not available and is not expected to be: `V` is universal
for bifinite domains, `PRep.boundedComplete_range` says a projection of a
bounded-complete domain is bounded complete, and not every bifinite domain is
bounded complete — so `Thm29Second` and `BoundedComplete V` cannot both hold.
`retracts_fun_of_boundedComplete` and `retracts_strictFun_of_boundedComplete`
state the two conjuncts with that instance made explicit rather than hidden, so
the obstruction is in the signature and not in a comment. It is not a defect of
Lemma 17: `ClosureProperties.lean`'s own docstring already records that
`[BoundedComplete β]` is an artifact of the development's route to `Domain (D → E)`
through Theorem 7's step functions, "a real open item, not a formality".

## What is proved here, and what is not

| # | Result | Status |
| - | ------ | ------ |
| 1 | `plotkinOp` — `(·)♮` as a function `Cpo → Cpo` | defined |
| 2 | `Lemma30` — the ten-fold conjunction, and `lemma30_of` | stated, arity checked by the kernel |
| 3 | `lemma30_iff_lemma28_and_plotkin` | proved |
| 4 | five retraction pairs over `V` from `Thm29SecondAtDomains` | proved |
| 5 | three more from the stronger `Colimit.Thm29Second` | proved |
| 6 | `rep_lift_V`, `rep_prod_V` — conjuncts 7 and 3 | proved from `Thm29SecondAtDomains` |
| 7 | `Thm29Normal ⟹ Thm29SecondAtDomains` | **proved** |
| 8 | `Thm29Normal` itself | not proved — this is [Gun87]'s content |

Theorem 29's second sentence is therefore no longer a paragraph away. What
remains is one proposition: `Thm29Normal`, that `A∞` is universal among the bases
of bifinite domains under normal embedding.
`exists_embeddingProjectionPair_of_thm29Normal` derives the whole sentence from
it in about sixty lines of ideal manipulation, and
`exists_stage_ge_of_finite` measures that the missing step is *not* the
stage-by-stage extension the round plan located it at — the stages are already
cofinal among finite subsets of `A∞`. No `sorry` appears in this file.

Two hypotheses turned out to be worth separating, and both separations are
recorded in signatures rather than in prose:

1. **`Colimit.Thm29Second` is stronger than the printed sentence, and the
   difference is real.** The paper says "`E` is any bifinite *domain*";
   `IsBifinite` alone is the Plotkin condition on `K(E)` and implies neither
   algebraicity nor a countable basis. `Thm29SecondAtDomains` restores the word.
   `countable_compacts_of_reflects` shows the word is load-bearing: `A∞` is
   countable, so no order-reflecting map into it has an uncountable source, and
   the version of `Thm29Normal` without `[Domain E]` is refutable rather than
   open. Inside the reduction proper, only the algebraicity half is spent.
2. **`⊗`, `+` and `⊕` are not known to be algebraic here.** Their retraction
   pairs therefore take `Colimit.Thm29Second` rather than
   `Thm29SecondAtDomains`. This is a gap next to Lemma 17, not next to
   Theorem 29.
-/

namespace ScottDomains.LemThirty

open ScottDomains ScottDomains.BifiniteUniversal ScottDomains.Colimit

universe u

/-! ## `(·)♮` as an operator on cpos

`PRep` defines nine of Lemma 30's ten operators. The tenth is missing there for a
reason the source gives: `(·)♮` is not in Lemma 28, because §7.4 opens by saying
"The convex powerdomain `(·)♮` cannot be representable over `U` because it does
not preserve bounded completeness." It is defined here, in the file that needs
it. -/

/-- **`(·)♮`**, the Plotkin (convex) powerdomain: the ideal completion of the
Egli–Milner pre-order on `Pf(K(D))`, `Plotkin.Powerdomain`.

Definable at a bare cpo, exactly as `PRep.smythOp` and `PRep.hoareOp` are:
`Plotkin.FinCompacts D` needs `[PartialOrder D]` for its order and
`[CompletePartialOrder D]` for its `OrderBot` (the singleton `{⊥}`), and
`IdealCompletion`'s `CompletePartialOrder` instance needs only `[Preorder]` and
`[OrderBot]` of the base. **`[Domain D]` is spent in exactly one place** —
`Plotkin.FinCompacts.instCountable`, which turns `Domain.countable_compacts` into
`Countable (FinCompacts D)`, which is the third and last hypothesis of Theorem 11
(`IdealCompletion.instDomain`). So the hypothesis buys the *result* being a
domain, not the type and not its cpo structure; `domain_plotkinOp` is that
measurement, and it is `inferInstance`. -/
noncomputable def plotkinOp (D : Cpo.{u}) : Cpo.{u} :=
  ⟨Plotkin.Powerdomain D.carrier, inferInstance⟩

@[simp] theorem plotkinOp_carrier (D : Cpo.{u}) :
    (plotkinOp D).carrier = Plotkin.Powerdomain D.carrier := rfl

/-- **Where `plotkinOp`'s `[Domain D]` goes.** The operator itself is defined
without it; the hypothesis is what makes the value a domain, through Theorem 11.
The same statement for `(·)♯` and `(·)♭` is `PRep.smythOp_eq` / `PRep.hoareOp_eq`
read together with `Plotkin.isDomain`. -/
theorem domain_plotkinOp (D : Cpo.{u}) [Domain D.carrier] : Domain (plotkinOp D).carrier :=
  show Domain (Plotkin.Powerdomain D.carrier) from inferInstance

/-! ## Lemma 30, as one ten-fold conjunction

Stated the way `PRep.Lemma28` is, and for the same reason: a `def … : Prop` whose
components the kernel counts, rather than a list in prose. This row of the
project's inventory has been recorded as nine and as ten in different rounds; a
conjunction cannot drift. -/

/-- **Lemma 30** (Gunter & Scott, §7.4): all ten operators are p-representable
over `W`, at `Fp(W)`.

The six binary conjuncts come first in the paper's own printed order — `→`, `⇸`,
`×`, `⊗`, `+`, `⊕` — then the four unary ones, `(·)⊥`, `(·)♯`, `(·)♭`, `(·)♮`.
The carrier is a parameter so that the proposition and its instantiation at §7.4's
`V` are separate declarations, as `PRep.Lemma28` and `PRep.Lemma28AtU` are. -/
def Lemma30 (W : Type u) [CompletePartialOrder W] : Prop :=
  IsPRepresentable₂ W PRep.funOp ∧
  IsPRepresentable₂ W PRep.strictFunOp ∧
  IsPRepresentable₂ W PRep.prodOp ∧
  IsPRepresentable₂ W PRep.smashOp ∧
  IsPRepresentable₂ W PRep.sepSumOp ∧
  IsPRepresentable₂ W PRep.coalSumOp ∧
  IsPRepresentable W PRep.liftOp ∧
  IsPRepresentable W PRep.smythOp ∧
  IsPRepresentable W PRep.hoareOp ∧
  IsPRepresentable W plotkinOp

/-- **Lemma 30 from its ten conjuncts.** Every conjunct is a named hypothesis;
the anonymous constructor forces the count to be exactly ten, so the arity of
this theorem *is* the kernel's check on the printed operator list. As a conjunct
is proved, its hypothesis is deleted and its proof substituted — which is what
`rep_lift_V` and `rep_prod_V` below are candidates for, once `Thm29Second`
is discharged. -/
theorem lemma30_of {W : Type u} [CompletePartialOrder W]
    (h_arrow : IsPRepresentable₂ W PRep.funOp)
    (h_strictArrow : IsPRepresentable₂ W PRep.strictFunOp)
    (h_prod : IsPRepresentable₂ W PRep.prodOp)
    (h_smash : IsPRepresentable₂ W PRep.smashOp)
    (h_sepSum : IsPRepresentable₂ W PRep.sepSumOp)
    (h_coalSum : IsPRepresentable₂ W PRep.coalSumOp)
    (h_lift : IsPRepresentable W PRep.liftOp)
    (h_smyth : IsPRepresentable W PRep.smythOp)
    (h_hoare : IsPRepresentable W PRep.hoareOp)
    (h_plotkin : IsPRepresentable W plotkinOp) :
    Lemma30 W :=
  ⟨h_arrow, h_strictArrow, h_prod, h_smash, h_sepSum, h_coalSum, h_lift, h_smyth, h_hoare,
    h_plotkin⟩

/-- **Lemma 30 is Lemma 28's list plus one conjunct**, at whatever carrier both
are read over. This is the sentence "the same nine plus `(·)♮`" turned into a
proposition the kernel checks; the two are not definitionally equal only because
the nesting of `∧` differs. -/
theorem lemma30_iff_lemma28_and_plotkin (W : Type u) [CompletePartialOrder W] :
    Lemma30 W ↔ PRep.Lemma28 W ∧ IsPRepresentable W plotkinOp := by
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀⟩
    exact ⟨⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩, h₁₀⟩
  · rintro ⟨⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩, h₁₀⟩
    exact ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀⟩

/-- Lemma 30 is a statement about §7.4's `V`, the bifinite universal domain
`Colimit.V` — not about §7.3's bounded-complete `U`, over which §7.4's opening
sentence says `(·)♮` *cannot* be representable. This abbreviation fixes the
carrier so the instantiation cannot drift, exactly as `PRep.Lemma28AtU` does. -/
abbrev Lemma30AtV : Prop := Lemma30 Colimit.V

/-! ## Theorem 29's second sentence at the paper's own hypothesis

`Colimit.Thm29Second` quantifies over every cpo `E` with `IsBifinite E`. The
paper's sentence says "`E` is any bifinite **domain**", and `IsBifinite` is only
the Plotkin condition on `K(E)` (`Bifinite.lean:62`) — it does not imply
algebraicity or a countable basis. So `Colimit.Thm29Second` as recorded in r0036
is *stronger* than the printed sentence, and the difference is not cosmetic:
`countable_compacts_of_reflects` below shows that `V`'s own basis is countable,
so a bifinite cpo with an uncountable basis cannot be a retract of `V` by any
embedding built from `A∞` at all. The word "domain" in the printed sentence is
load-bearing. -/

/-- **Theorem 29's second sentence**, at the paper's own "bifinite domain".
Implied by `Colimit.Thm29Second` (`thm29SecondAtDomains_of_thm29Second`) and
implied by `Thm29Normal` (`thm29SecondAtDomains_of_thm29Normal`, proved below). -/
def Thm29SecondAtDomains : Prop :=
  ∀ (E : Type) [CompletePartialOrder E] [Domain E], IsBifinite E →
    ∃ (g : ScottHom E V) (p : ScottHom V E), ScottHom.IsEmbeddingProjectionPair g p

/-- Dropping the `Domain` hypothesis strengthens the statement, so the r0036
form implies this one. -/
theorem thm29SecondAtDomains_of_thm29Second (h : Colimit.Thm29Second) :
    Thm29SecondAtDomains := fun E _ _ hE => h E hE

/-! ## The retraction pairs over `V`

Every one of the paper's ten recipes opens the same way: "take a pair of
continuous functions `Φ : V → F(V)`, `Ψ : F(V) → V` such that `Φ ∘ Ψ = id` and
`Ψ ∘ Φ ⊑ id`". That pair is an embedding–projection pair with `F(V)` embedded in
`V`, and it is exactly what Theorem 29's second sentence asserts exists for every
bifinite `E`. -/

section Retracts

/-- **`V` retracts onto `E`**: the paper's pair, spelled in the argument order
`PRep.rep_lift` and `PRep.rep_prod` consume. `gr` is the embedding `E → V` and
`fn` the projection `V → E`, so this is
`ScottHom.IsEmbeddingProjectionPair gr fn` with the conjunction unfolded. -/
def Retracts (E : Type) [CompletePartialOrder E] : Prop :=
  ∃ (gr : ScottHom E V) (fn : ScottHom V E), (∀ y, fn (gr y) = y) ∧ ∀ x, gr (fn x) ≤ x

/-- **Theorem 29's second sentence gives a retraction pair for every bifinite
`E`.** The whole of the reduction: `Thm29Second`'s conclusion *is* the pair, with
the conjunction of `IsEmbeddingProjectionPair` split. -/
theorem retracts_of_isBifinite (h : Colimit.Thm29Second) (E : Type) [CompletePartialOrder E]
    (hE : IsBifinite E) : Retracts E := by
  obtain ⟨g, p, hgp⟩ := h E hE
  exact ⟨g, p, hgp.1, hgp.2⟩

/-- The same reduction from the weaker hypothesis, for an `E` that is a domain.
Five of the ten operator results are domains in this development, so five of the
ten pairs go through this route and therefore follow from `Thm29Normal`
(`thm29SecondAtDomains_of_thm29Normal`). -/
theorem retracts_of_isDomain (h : Thm29SecondAtDomains) (E : Type)
    [CompletePartialOrder E] [Domain E] (hE : IsBifinite E) : Retracts E := by
  obtain ⟨g, p, hgp⟩ := h E hE
  exact ⟨g, p, hgp.1, hgp.2⟩

/-- Conjunct 7's pair, `(·)⊥`. `Domain (WithBot V)` is
`ClosureProperties.liftDomain`, an instance. -/
theorem retracts_lift (h : Thm29SecondAtDomains) : Retracts (WithBot V) :=
  retracts_of_isDomain h _ (lem17_lift isBifinite_V)

/-- Conjunct 3's pair, `×`. `Domain (V × V)` comes from
`PowerdomainRep.domain_prod`, which is a theorem rather than an instance. -/
theorem retracts_prod (h : Thm29SecondAtDomains) : Retracts (V × V) := by
  haveI : Domain (V × V) := PowerdomainRep.domain_prod
  exact retracts_of_isDomain h _ (lem17_prod isBifinite_V isBifinite_V)

/-- Conjunct 8's pair, `(·)♯`. The three powerdomains are ideal completions of a
countable pre-order, so `IdealCompletion.instDomain` applies. -/
theorem retracts_smyth (h : Thm29SecondAtDomains) : Retracts (Smyth.Powerdomain V) :=
  retracts_of_isDomain h _ (ClosureProperties.lem17_smyth isBifinite_V)

/-- Conjunct 9's pair, `(·)♭`. -/
theorem retracts_hoare (h : Thm29SecondAtDomains) : Retracts (Hoare.Powerdomain V) :=
  retracts_of_isDomain h _ (ClosureProperties.lem17_hoare isBifinite_V)

/-- Conjunct 10's pair, `(·)♮` — the pair the paper displays in full on page 43,
`Φ♮ : V → V♮` and `Ψ♮ : V♮ → V`. This is the conjunct §7.4 exists for, and
nothing beyond `Thm29Normal` stands in its way. -/
theorem retracts_plotkin (h : Thm29SecondAtDomains) : Retracts (Plotkin.Powerdomain V) :=
  retracts_of_isDomain h _ (ClosureProperties.lem17_plotkin isBifinite_V)

/-! ### The three pairs that need the stronger hypothesis, and why

`⊗`, `+` and `⊕` take `Colimit.Thm29Second` rather than `Thm29SecondAtDomains`,
because **this development never proves those three constructions algebraic.**
Measured over the whole library, `IsAlgebraic` instances exist for `ScottHom`,
`Set X`, `IdealCompletion` and `WithBot`, and `PowerdomainRep.domain_prod`
supplies the product; `Smash`, `CoalescedSum` and `SeparatedSum` have Lemma 10's
bounded completeness and Lemma 17's bifiniteness but no algebraicity and no
`Domain`. That is a gap in the neighbourhood of Lemma 17 that no round has
recorded, and it is independent of Theorem 29. -/

/-- Conjunct 4's pair, `⊗`. -/
theorem retracts_smash (h : Colimit.Thm29Second) : Retracts (Smash V V) :=
  retracts_of_isBifinite h _ (lem17_smash isBifinite_V isBifinite_V)

/-- Conjunct 5's pair, `+`. -/
theorem retracts_sepSum (h : Colimit.Thm29Second) :
    Retracts (ClosureProperties.SeparatedSum V V) :=
  retracts_of_isBifinite h _ (ClosureProperties.lem17_separated isBifinite_V isBifinite_V)

/-- Conjunct 6's pair, `⊕`. -/
theorem retracts_coalSum (h : Colimit.Thm29Second) : Retracts (CoalescedSum V V) :=
  retracts_of_isBifinite h _ (lem17_sum isBifinite_V isBifinite_V)

/-- Conjunct 1's pair, `→`, **with the extra instance the development's Lemma 17
needs made explicit.** `lem17_fun` carries `[BoundedComplete β]`, which `V` does
not have and — if `Thm29Second` holds — cannot have, since
`PRep.boundedComplete_range` would then force every bifinite domain to be
bounded complete. Stating it as an instance argument keeps the obstruction in the
signature. -/
theorem retracts_fun_of_boundedComplete (h : Colimit.Thm29Second) [BoundedComplete V] :
    Retracts (ScottHom V V) :=
  retracts_of_isBifinite h _ (lem17_fun isBifinite_V isBifinite_V)

/-- Conjunct 2's pair, `⇸`, with the same extra instance as conjunct 1's. -/
theorem retracts_strictFun_of_boundedComplete (h : Colimit.Thm29Second) [BoundedComplete V] :
    Retracts (StrictHom V V) :=
  retracts_of_isBifinite h _ (ClosureProperties.lem17_strictFun isBifinite_V isBifinite_V)

end Retracts

/-! ## The two conjuncts that are complete today

`PRep.rep_lift` and `PRep.rep_prod` are the only two of Lemma 28's nine schemes
already proved; streams 3 and 4 of this round are proving the rest. Both are
generic in the carrier, so instantiating them at `V` costs one `obtain` and one
`exact` each. That is the transfer measurement the round asked for, in the form
the kernel checks. -/

/-- **Conjunct 7 of Lemma 30: `(·)⊥` is p-representable over `V`**, given
Theorem 29's second sentence.

`PRep.rep_lift` at `U := V`. Its `[Domain U]` is `Colimit.domain_V`, found by
instance resolution; its two equations are `retracts_lift`'s. Nothing else about
`V` enters — which is the sense in which §7.3's proof transfers to §7.4's
carrier unchanged. -/
theorem rep_lift_V (h : Thm29SecondAtDomains) : IsPRepresentable V PRep.liftOp := by
  obtain ⟨_gr, _fn, hfg, hgf⟩ := retracts_lift h
  exact PRep.rep_lift hfg hgf

/-- **Conjunct 3 of Lemma 30: `×` is p-representable over `V`**, given
Theorem 29's second sentence. `PRep.rep_prod` at `U := V`. -/
theorem rep_prod_V (h : Thm29SecondAtDomains) : IsPRepresentable₂ V PRep.prodOp := by
  obtain ⟨_gr, _fn, hfg, hgf⟩ := retracts_prod h
  exact PRep.rep_prod hfg hgf

/-! ## What Theorem 29's second sentence still needs

`Colimit.Thm29Second` is unproved, and every result above that takes it as a
hypothesis is therefore conditional. The missing step is not the whole sentence:
`Colimit.lean` already supplies `isNormalIn_range_incl` (each stage `Stg n` is
normal in `A∞`), `exists_stage_of_finite` (a finite subset of `A∞` lies in one
stage), `instFiniteStg` (each stage is finite) and `isoPlus` (the fixed point
`V ≅ V⁺`, which discharges the sentence's own hypothesis `D ≅ D⁺`). What is
missing is one extension property, named below.

Given a bifinite `E`, `K(E)` is a Plotkin order, so it is the union of an
increasing chain of finite normal subposets `N₀ ◁ N₁ ◁ ⋯ ◁ K(E)`. An embedding
`E ⇄ V` is assembled from normal embeddings `Nᵢ → Stg nᵢ` that commute with both
chains. Producing `N₀ → Stg n₀` is immediate. Producing `Nᵢ₊₁ → Stg nᵢ₊₁` from
`Nᵢ → Stg nᵢ` is the step §7.4 defers in full to [Gun87], and it is exactly the
universal property of `M` among finite posets and normal embeddings. -/

/-- **Every finite subset of `A∞` lies in a stage, and in arbitrarily late
stages.** `exists_stage_of_finite` gives one stage; `incl_lift` moves a point of
`Stg m` to `Stg (max n m)` without changing its image in `A∞`, so the stage can
always be taken at or beyond a prescribed `n`.

This measures the plan's description of the missing step. The plan located the
gap at "extending a normal embedding of a finite normal subposet of `K(E)` into
`Stg n` to the next one into `Stg (n+1)`", and *that* statement — read as a
statement about subsets of `A∞` — is not a gap: the stages are already cofinal
among finite subsets, with no hypothesis on `N` or `N'` beyond finiteness, and
each stage is already normal in `A∞` (`isNormalIn_range_incl`). The gap is one
level earlier, at getting `K(E)` into `A∞` at all; `Thm29Normal` states it. -/
theorem exists_stage_ge_of_finite {S : Set Ainf} (hS : S.Finite) (n : ℕ) :
    ∃ m : ℕ, n ≤ m ∧ S ⊆ Set.range (incl m) := by
  obtain ⟨k, hk⟩ := exists_stage_of_finite hS
  refine ⟨max n k, le_max_left _ _, fun x hx => ?_⟩
  obtain ⟨y, rfl⟩ := hk hx
  exact ⟨liftStg (le_max_right n k) y, incl_lift (le_max_right n k) y⟩

/-- **The step Theorem 29's second sentence is missing.** For every bifinite `E`
there is an order-reflecting map of `K(E)` into `A∞` whose image is normal in
`A∞` — equivalently, `A∞` is universal among the bases of bifinite domains under
normal embedding. `Thm29Second` follows from this by Theorem 11 and transport
along the ideal completion; the chain-by-chain construction of the map, over the
tower of finite normal subposets of `K(E)`, is what [Gun87] carries and §7.4 does
not.

Order-reflection rather than monotonicity plus injectivity, because
`OrderEmbedding.ofMapLEIff` is the form the rest of `Colimit.lean` consumes
(`inclEmb`, `toCompactsEmb`). `[Domain E]` rather than `IsBifinite E` alone,
because `A∞` is countable (`Colimit.instCountableAinf`) and
`countable_compacts_of_reflects` turns that into countability of `K(E)`: without
the paper's word "domain" the statement is refutable, not merely unproved.
Recorded as a `Prop` rather than a `sorry`, per this development's convention:
the statement is fixed and citable, and nothing asserts it. -/
def Thm29Normal : Prop :=
  ∀ (E : Type) [CompletePartialOrder E] [Domain E], IsBifinite E →
    ∃ f : ↥(compacts E) → Ainf,
      (∀ a b, f a ≤ f b ↔ a ≤ b) ∧ Set.range f ◁ (Set.univ : Set Ainf)

/-! ## `Thm29Normal` suffices: the reduction, proved

Everything between a normal embedding `f : K(E) → A∞` and the embedding–projection
pair `E ⇄ V` is elementary manipulation of ideals, and it is carried out below.
The two maps are

| # | map | definition |
| - | --- | ---------- |
| 1 | `E → V` | `x ↦ ↓(f '' {k ∈ K(E) | k ⊑ x})` — `embIdeal ∘ idealOfElem` |
| 2 | `V → E` | `J ↦ ⨆ f⁻¹(J)` — `elemOfIdeal ∘ projIdeal` |

Each of the two hypotheses of `Thm29Normal` is spent exactly once and in a
different place:

* **order-reflection** gives `p ∘ g = id`, since `f k ⊑ f k'` collapses to
  `k ⊑ k'` and the ideal `{k | k ⊑ x}` is recovered on the nose;
* **normality of `range f`** gives directedness of `f⁻¹(J)`, which is what makes
  the projection well defined: two compacts with `f k₁, f k₂ ∈ J` are bounded in
  `J` by some `a`, and `range f ◁ A∞` at `a` returns a *third point of the range*
  between them and `a`.

Compactness of the members of `K(E)` is never used — the argument is about
ideals, not about compact approximation — and countability is never used either,
so the hypothesis is `[IsAlgebraic E]` rather than the paper's `[Domain E]`. -/

section Universality

variable {E : Type} [CompletePartialOrder E] {f : ↥(compacts E) → Ainf}

/-- An order-reflecting map is monotone. -/
theorem monotone_of_reflects (hf : ∀ a b, f a ≤ f b ↔ a ≤ b) : Monotone f :=
  fun _ _ hab => (hf _ _).mpr hab

/-- An order-reflecting map into a partial order is injective. -/
theorem injective_of_reflects (hf : ∀ a b, f a ≤ f b ↔ a ≤ b) : Function.Injective f :=
  fun _ _ hab => le_antisymm ((hf _ _).mp hab.le) ((hf _ _).mp hab.ge)

/-- **Why `Thm29Normal` carries the paper's word "domain".** `A∞` is countable
(`Colimit.instCountableAinf`), and an order-reflecting map into a countable type
has a countable source. So an `E` that is bifinite but has an uncountable basis
— an uncountable flat cpo is one — admits no such `f` at all, and the version of
`Thm29Normal` without `[Domain E]` is refutable rather than open. `IsBifinite`
alone is the Plotkin condition on `K(E)` and says nothing about its
cardinality. -/
theorem countable_compacts_of_reflects (hf : ∀ a b, f a ≤ f b ↔ a ≤ b) :
    Countable ↥(compacts E) :=
  (injective_of_reflects hf).countable

/-- **A normal embedding preserves `⊥`.** Normality supplies a point of the range
below `⊥`, which is therefore `⊥` itself; order-reflection then forces its
argument to be `⊥`. Nothing has to be assumed about `f` at `⊥` separately. -/
theorem map_bot_of_normal (hf : ∀ a b, f a ≤ f b ↔ a ≤ b)
    (hn : Set.range f ◁ (Set.univ : Set Ainf)) : f ⊥ = ⊥ := by
  obtain ⟨y, hyr, hyle⟩ := hn.nonempty (Set.mem_univ (⊥ : Ainf))
  obtain ⟨k, rfl⟩ := hyr
  have hk : k = ⊥ := le_antisymm ((hf k ⊥).mp ((Set.mem_Iic.mp hyle).trans bot_le)) bot_le
  exact le_antisymm (hk ▸ Set.mem_Iic.mp hyle) bot_le

/-! ### The embedding `E → V` -/

/-- `↓(f '' I)`: the down-set of `A∞` generated by the image of an ideal of
`K(E)`. -/
def embSet (f : ↥(compacts E) → Ainf) (I : IdealCompletion ↥(compacts E)) : Set Ainf :=
  {a | ∃ k ∈ I, a ≤ f k}

/-- `↓(f '' I)` is an ideal. Lower-closedness and non-emptiness are free;
directedness needs only that `f` is monotone, which order-reflection supplies. -/
theorem isIdeal_embSet (hf : ∀ a b, f a ≤ f b ↔ a ≤ b) (I : IdealCompletion ↥(compacts E)) :
    Order.IsIdeal (embSet f I) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro a b hba ⟨k, hk, hak⟩
    exact ⟨k, hk, hba.trans hak⟩
  · obtain ⟨k, hk⟩ := I.nonempty
    exact ⟨f k, k, hk, le_rfl⟩
  · rintro a ⟨k₁, hk₁, ha⟩ b ⟨k₂, hk₂, hb⟩
    obtain ⟨k, hk, h₁, h₂⟩ := I.directed k₁ hk₁ k₂ hk₂
    exact ⟨f k, ⟨k, hk, le_rfl⟩, ha.trans ((hf k₁ k).mpr h₁), hb.trans ((hf k₂ k).mpr h₂)⟩

/-- The ideal `↓(f '' I)` as a point of `V`. -/
def embIdeal (hf : ∀ a b, f a ≤ f b ↔ a ≤ b) (I : IdealCompletion ↥(compacts E)) : V :=
  IdealCompletion.ofIdeal (isIdeal_embSet hf I).toIdeal

@[simp] theorem mem_embIdeal {hf : ∀ a b, f a ≤ f b ↔ a ≤ b}
    {I : IdealCompletion ↥(compacts E)} {a : Ainf} :
    a ∈ embIdeal hf I ↔ ∃ k ∈ I, a ≤ f k := Iff.rfl

theorem embIdeal_mono (hf : ∀ a b, f a ≤ f b ↔ a ≤ b)
    {I J : IdealCompletion ↥(compacts E)} (hIJ : I ≤ J) : embIdeal hf I ≤ embIdeal hf J := by
  rintro a ⟨k, hk, hle⟩
  exact ⟨k, hIJ hk, hle⟩

/-! ### The projection `V → E` -/

/-- `f⁻¹(J)`: the compacts of `E` whose images lie in the ideal `J`. -/
def projSet (f : ↥(compacts E) → Ainf) (J : V) : Set ↥(compacts E) := {k | f k ∈ J}

/-- **`f⁻¹(J)` is an ideal, and this is where normality is spent.** Two members
`k₁, k₂` give `f k₁, f k₂ ∈ J`, bounded in `J` by directedness; normality of
`range f` at that bound returns `f k₃` between them and the bound, so `f k₃ ∈ J`
by lower-closedness and `k₁, k₂ ⊑ k₃` by order-reflection. Non-emptiness is
`map_bot_of_normal`. -/
theorem isIdeal_projSet (hf : ∀ a b, f a ≤ f b ↔ a ≤ b)
    (hn : Set.range f ◁ (Set.univ : Set Ainf)) (J : V) : Order.IsIdeal (projSet f J) := by
  refine ⟨?_, ⟨⊥, ?_⟩, ?_⟩
  · intro a b hba ha
    exact J.lower ((hf b a).mpr hba) ha
  · show f ⊥ ∈ J
    rw [map_bot_of_normal hf hn]
    exact IdealCompletion.bot_mem J
  · intro k₁ h₁ k₂ h₂
    obtain ⟨a, ha, hle₁, hle₂⟩ := J.directed (f k₁) h₁ (f k₂) h₂
    obtain ⟨y, ⟨hyr, hyle⟩, hd₁, hd₂⟩ :=
      hn.directedOn (Set.mem_univ a) (f k₁) ⟨⟨k₁, rfl⟩, Set.mem_Iic.mpr hle₁⟩
        (f k₂) ⟨⟨k₂, rfl⟩, Set.mem_Iic.mpr hle₂⟩
    obtain ⟨k₃, rfl⟩ := hyr
    exact ⟨k₃, J.lower (Set.mem_Iic.mp hyle) ha, (hf k₁ k₃).mp hd₁, (hf k₂ k₃).mp hd₂⟩

/-- The ideal `f⁻¹(J)` as a point of the ideal completion of `K(E)`. -/
def projIdeal (hf : ∀ a b, f a ≤ f b ↔ a ≤ b)
    (hn : Set.range f ◁ (Set.univ : Set Ainf)) (J : V) : IdealCompletion ↥(compacts E) :=
  IdealCompletion.ofIdeal (isIdeal_projSet hf hn J).toIdeal

@[simp] theorem mem_projIdeal {hf : ∀ a b, f a ≤ f b ↔ a ≤ b}
    {hn : Set.range f ◁ (Set.univ : Set Ainf)} {J : V} {k : ↥(compacts E)} :
    k ∈ projIdeal hf hn J ↔ f k ∈ J := Iff.rfl

/-! ### The two equations -/

/-- **`f⁻¹(↓(f '' I)) = I`** — the first equation of the pair, and the one
order-reflection buys. -/
theorem projIdeal_embIdeal (hf : ∀ a b, f a ≤ f b ↔ a ≤ b)
    (hn : Set.range f ◁ (Set.univ : Set Ainf)) (I : IdealCompletion ↥(compacts E)) :
    projIdeal hf hn (embIdeal hf I) = I := by
  ext k
  constructor
  · rintro ⟨k', hk', hle⟩
    exact I.lower ((hf k k').mp hle) hk'
  · intro hk
    exact ⟨k, hk, le_rfl⟩

/-- **`↓(f '' f⁻¹(J)) ⊑ J`** — the second equation of the pair, by
lower-closedness of `J` alone. -/
theorem embIdeal_projIdeal_le (hf : ∀ a b, f a ≤ f b ↔ a ≤ b)
    (hn : Set.range f ◁ (Set.univ : Set Ainf)) (J : V) :
    embIdeal hf (projIdeal hf hn J) ≤ J := by
  rintro a ⟨k, hk, hle⟩
  exact J.lower hle hk

/-! ### Continuity of both maps

Both are continuous for the same reason and by the same three lines: a directed
supremum in an ideal completion is the union (`IdealCompletion.mem_sSup_iff`),
and both maps are defined by a condition on a single member, so a member of the
image of the supremum already lies in the image of one ideal of the family. -/

theorem scottContinuous_embIdeal (hf : ∀ a b, f a ≤ f b ↔ a ≤ b) :
    ScottContinuous (embIdeal hf) := by
  intro d hne hd a ha
  refine ⟨?_, ?_⟩
  · rintro _ ⟨I, hI, rfl⟩
    exact embIdeal_mono hf (ha.1 hI)
  · intro J hJ x hx
    obtain ⟨k, hk, hle⟩ := hx
    have hae : a = sSup d := ha.unique hd.isLUB_sSup
    rw [hae] at hk
    obtain ⟨I, hI, hkI⟩ := (IdealCompletion.mem_sSup_iff hne hd).mp hk
    exact hJ ⟨I, hI, rfl⟩ ⟨k, hkI, hle⟩

theorem scottContinuous_projIdeal (hf : ∀ a b, f a ≤ f b ↔ a ≤ b)
    (hn : Set.range f ◁ (Set.univ : Set Ainf)) : ScottContinuous (projIdeal hf hn) := by
  intro d hne hd a ha
  refine ⟨?_, ?_⟩
  · rintro _ ⟨I, hI, rfl⟩
    exact fun k hk => ha.1 hI hk
  · intro J hJ k hk
    have hk' : f k ∈ a := hk
    have hae : a = sSup d := ha.unique hd.isLUB_sSup
    rw [hae] at hk'
    obtain ⟨I, hI, hkI⟩ := (IdealCompletion.mem_sSup_iff hne hd).mp hk'
    exact hJ ⟨I, hI, rfl⟩ hkI

/-! ### The embedding–projection pair -/

/-- **Theorem 29's second sentence follows from `Thm29Normal`.**

The one missing input is the normal embedding of `K(E)` into `A∞`; everything
after it is the composite of that embedding with Theorem 11's converse
isomorphism `E ≃o IdealCompletion K(E)`
(`IdealCompletion.orderIsoIdealCompletionCompacts`).

Of the two halves of "bifinite **domain**", **only algebraicity is spent below
this line**, on `elemOfIdeal_idealOfElem` and `idealOfElem_elemOfIdeal`. The
countable-basis half is spent one level up, inside `Thm29Normal` itself, where
`countable_compacts_of_reflects` shows it is not optional. -/
theorem exists_embeddingProjectionPair_of_thm29Normal (h : Thm29Normal)
    (E : Type) [CompletePartialOrder E] [Domain E] (hE : IsBifinite E) :
    ∃ (g : ScottHom E V) (p : ScottHom V E), ScottHom.IsEmbeddingProjectionPair g p := by
  obtain ⟨f, hf, hn⟩ := h E hE
  have hgc : ScottContinuous fun x : E => embIdeal hf (IdealCompletion.idealOfElem x) := by
    intro s hne hs x hx
    have h1 : IsLUB ((IdealCompletion.idealOfElem : E → _) '' s)
        (IdealCompletion.idealOfElem x) :=
      PRep.isLUB_orderIso_image IdealCompletion.orderIsoIdealCompletionCompacts hx
    have h2 : DirectedOn (· ≤ ·) ((IdealCompletion.idealOfElem : E → _) '' s) :=
      PRep.directedOn_orderIso_image IdealCompletion.orderIsoIdealCompletionCompacts hs
    have h3 := scottContinuous_embIdeal hf (hne.image _) h2 h1
    rwa [Set.image_image] at h3
  have hpc : ScottContinuous fun J : V =>
      IdealCompletion.elemOfIdeal (projIdeal hf hn J) := by
    intro s hne hs J hJ
    have h1 := scottContinuous_projIdeal hf hn hne hs hJ
    have h2 : DirectedOn (· ≤ ·) (projIdeal hf hn '' s) := by
      rintro _ ⟨I₁, hI₁, rfl⟩ _ ⟨I₂, hI₂, rfl⟩
      obtain ⟨I, hI, h₁, h₂⟩ := hs I₁ hI₁ I₂ hI₂
      exact ⟨projIdeal hf hn I, ⟨I, hI, rfl⟩, fun _ hk => h₁ hk, fun _ hk => h₂ hk⟩
    have h3 : IsLUB ((IdealCompletion.orderIsoIdealCompletionCompacts (D := E)).symm ''
        (projIdeal hf hn '' s))
        ((IdealCompletion.orderIsoIdealCompletionCompacts (D := E)).symm
          (projIdeal hf hn J)) :=
      PRep.isLUB_orderIso_image _ h1
    rwa [Set.image_image] at h3
  refine ⟨⟨_, hgc⟩, ⟨_, hpc⟩, fun x => ?_, fun J => ?_⟩
  · show IdealCompletion.elemOfIdeal (projIdeal hf hn
      (embIdeal hf (IdealCompletion.idealOfElem x))) = x
    rw [projIdeal_embIdeal hf hn, IdealCompletion.elemOfIdeal_idealOfElem]
  · show embIdeal hf (IdealCompletion.idealOfElem
      (IdealCompletion.elemOfIdeal (projIdeal hf hn J))) ≤ J
    rw [IdealCompletion.idealOfElem_elemOfIdeal]
    exact embIdeal_projIdeal_le hf hn J

/-- **`Thm29Normal ⟹ Thm29SecondAtDomains`.** The whole of Theorem 29's second
sentence, at the paper's own hypothesis that `E` is a bifinite *domain*, reduces
to the single statement that `A∞` is universal among the bases of bifinite
domains under normal embedding. That reduction is what this file proves; the
universality itself is what §7.4 defers to [Gun87].

Composing with `retracts_of_isDomain`, this makes five of Lemma 30's ten
retraction pairs — `×`, `(·)⊥`, `(·)♯`, `(·)♭`, `(·)♮` — consequences of
`Thm29Normal` alone. -/
theorem thm29SecondAtDomains_of_thm29Normal (h : Thm29Normal) : Thm29SecondAtDomains :=
  fun E _ _ hE => exists_embeddingProjectionPair_of_thm29Normal h E hE

/-- **Conjunct 7 of Lemma 30 from `Thm29Normal`.** The composite of
`thm29SecondAtDomains_of_thm29Normal`, `retracts_lift` and `PRep.rep_lift`. -/
theorem rep_lift_V_of_thm29Normal (h : Thm29Normal) : IsPRepresentable V PRep.liftOp :=
  rep_lift_V (thm29SecondAtDomains_of_thm29Normal h)

/-- **Conjunct 3 of Lemma 30 from `Thm29Normal`.** -/
theorem rep_prod_V_of_thm29Normal (h : Thm29Normal) : IsPRepresentable₂ V PRep.prodOp :=
  rep_prod_V (thm29SecondAtDomains_of_thm29Normal h)

end Universality

end ScottDomains.LemThirty
