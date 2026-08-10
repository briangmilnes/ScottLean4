import ScottDomains.Smash
import ScottDomains.CoalescedSum
import ScottDomains.StrictHom
import ScottDomains.Lift
import ScottDomains.Product
import ScottDomains.Bifinite
import ScottDomains.FinitaryProjectionPoset
import ScottDomains.SFP
import ScottDomains.Isomorphism.Smash
import ScottDomains.Isomorphism.Lift
import ScottDomains.Isomorphism.Copair
import ScottDomains.Isomorphism.StrictCurry
import ScottDomains.Isomorphism.Distribute
import ScottDomains.Isomorphism.Counterexample

/-!
# Lemma 9 and Theorem 14, recovered from the PDF

Two of Gunter & Scott's numbered results were recorded in
`docs/PaperInventory.md` as **not statable**: the 1990 Type-3 fonts drop every
glyph whose code is below `0x20`, and `pdftotext` renders `⊗`, `⊕`, `×`, `⊆` and
`∘` all as the same blank gap, so Lemma 9's operators were unreadable. Round
r0032 recovered both. The evidence — the raw extraction, the page content
stream decoded through the Computer Modern font encodings, and the rendered page
images — is in [`docs/StatementRecovery.md`](../../docs/StatementRecovery.md).

Round r0034 closed Lemma 9's six conjuncts and round r0036 closed Theorem 14, so
this file carries no `sorry`. The proofs live elsewhere — Lemma 9's under
`ScottDomains.Isomorphism` (five modules under `ScottDomains/Isomorphism/`),
Theorem 14's in [`ScottDomains/SFP.lean`](../SFP.lean) — and each theorem below
names the map or lemma that discharges it, so this file continues to read as the
statement of the results rather than as their proof.

## Confidence, per statement

The recovery method reads the PDF page content stream directly. The Type 3 fonts
carry no `ToUnicode` map, but their `/Encoding /Differences` name each glyph by
its own code (`/n0a`), and those codes are the standard TeX font codes, so the
bytes in the stream decode exactly: `\002` is `cmsy` `multiply` (`×`), `\n` is
`0x0A` `circlemultiply` (`⊗`), `\b` is `0x08` `circleplus` (`⊕`), `\016` is
`0x0E` `openbullet` — the small circle that, butted against `\041` `arrowright`,
forms the paper's strict-function arrow `◦→`. This is decoding, not inference:
the codes are read off the file, and the rendered page images agree.

* `lem9_1`, `lem9_2`, `lem9_4`, `lem9_6` — **certain**. Decoded character by
  character and confirmed against the page image.
* `lem9_3`, `lem9_5` — **inferred**. Here the decoding is equally certain but the
  *printed text is false*, and the correction is not free choice: for `lem9_3`
  the paper states the universal property that forces it three pages earlier, and
  for `lem9_5` only one completion typechecks against the left-hand side. Both
  printed forms are refuted by a finite counterexample in
  `docs/StatementRecovery.md`.
* `thm14` — **certain**. Theorem 14 is legible in the extraction once the `fi`
  ligature is restored; what was missing was not the text but the paper's *own*
  definition of bifinite, which this development had replaced by the
  characterization Theorem 14 proves equivalent to it. `IsBifiniteViaProjections`
  supplies the missing side, so the theorem has two distinct sides to relate.

## Isomorphism is `≃o`, and it is asserted as `Nonempty`

`Product.lean` fixes the reading of the paper's `≅` between cpo's: an order
isomorphism, since a bijection preserving the order automatically preserves
directed suprema. Lemma 9 asserts that an isomorphism *exists*, so each conjunct
is `Nonempty (_ ≃o _)` rather than a named map — the same choice `lem19` makes,
and for the same reason: fixing a particular map here would prejudge the proof.

## Operators

| Paper | Lean |
| ----- | ---- |
| `D × E` | `α × β` |
| `D ⊗ E` | `Smash α β` |
| `D ⊕ E` | `CoalescedSum α β` |
| `D → E` | `ScottHom α β` |
| `D ◦→ E` | `StrictHom α β` |
| `D⊥` | `WithBot α` |

**Owned by agent5** (round r0032). No declaration outside this file is edited.
-/

namespace ScottDomains.Recovered

variable {α β γ : Type*}

/-! ### Lemma 9 — the strict analogues of Lemma 8

> **Lemma 9** Let `D`, `E` and `F` be cpo's, then
> 1. `D ⊗ E ≅ E ⊗ D`,
> 2. `(D ⊗ E) ⊗ F ≅ D ⊗ (E ⊗ F)`,
> 3. `(E ⊕ F) ◦→ D ≅ (E ◦→ D) × (E ◦→ F)`,
> 4. `D ◦→ (E ◦→ F) ≅ (D ⊗ E) ◦→ F`,
> 5. `D ⊗ (E ⊕ F) ≅ (D ⊗ E) ⊕ (D ⊗ E)`
> 6. `D⊥ ◦→ E ≅ D → E`.

That is the printed text, decoded exactly. Items 3 and 5 are typeset with a
misprint each and are stated below in their corrected form; the other four are
stated as printed.
-/

section Lemma9

variable [CompletePartialOrder α] [CompletePartialOrder β] [CompletePartialOrder γ]

/-- **Lemma 9.1.** `D ⊗ E ≅ E ⊗ D` — the smash product is commutative.

Confidence **certain**. The operator is `\n` = `0x0A` = `cmsy` `circlemultiply`,
read from the page content stream; Lemma 8.1 one line above carries `\002` =
`0x02` = `multiply` in the identical position, which is what makes the pair of
lemmas the product laws and their smash analogues. -/
theorem lemma_9_1 : Nonempty (Smash α β ≃o Smash β α) :=
  ⟨Isomorphism.smashComm⟩

alias lem9_1 := lemma_9_1

/-- **Lemma 9.2.** `(D ⊗ E) ⊗ F ≅ D ⊗ (E ⊗ F)` — the smash product is
associative.

Confidence **certain**; same decoding as `lem9_1`. -/
theorem lemma_9_2 : Nonempty (Smash (Smash α β) γ ≃o Smash α (Smash β γ)) :=
  ⟨Isomorphism.smashAssoc⟩

alias lem9_2 := lemma_9_2

/-- **Lemma 9.3, corrected.** `(E ⊕ F) ◦→ D ≅ (E ◦→ D) × (F ◦→ D)` — the
coalesced sum is the coproduct in the category of pointed cpo's and strict
continuous maps, so the strict hom-functor carries it to a product.

Confidence **inferred**. The page *prints* `(E ⊕ F) ◦→ D ≅ (E ◦→ D) × (E ◦→ F)`,
and that is what the content stream contains — the recovery is not in doubt, the
typesetting is. The printed right-hand side is false, and its second factor does
not mention `D` at all. On the finite witness `D = E = Prop`, `F = Prop × Prop`
(both `Domain` instances here) the three cardinalities are: left side `10`,
printed right side `2 · 4 = 8`, corrected right side `2 · 5 = 10`. The corrected
form is not a guess — Gunter & Scott state it themselves three pages earlier, as
the universal property of `⊕`: "if `f : D ◦→ F` and `g : E ◦→ F` are strict
continuous functions, then there is a unique strict continuous function `[f, g]`
which completes the following diagram". Uniqueness of `[f, g]` in `f` and `g` is
exactly this isomorphism. -/
theorem lemma_9_3 :
    Nonempty (StrictHom (CoalescedSum β γ) α ≃o StrictHom β α × StrictHom γ α) :=
  ⟨Isomorphism.coalescedSumCopair⟩

alias lem9_3 := lemma_9_3

/-- **Lemma 9.4.** `D ◦→ (E ◦→ F) ≅ (D ⊗ E) ◦→ F` — strict currying; the smash
product is the tensor for which the strict function space is the internal hom.

Confidence **certain**. This is Lemma 8.4 (`scottHomCurry`, r0021) with `×`
replaced by `⊗` and `→` by `◦→` throughout, and the paper supplies the two maps
by name on the preceding page: `strict apply` and `strict curry`. -/
theorem lemma_9_4 :
    Nonempty (StrictHom α (StrictHom β γ) ≃o StrictHom (Smash α β) γ) :=
  ⟨Isomorphism.smashCurry⟩

alias lem9_4 := lemma_9_4

/-- **Lemma 9.5, corrected.** `D ⊗ (E ⊕ F) ≅ (D ⊗ E) ⊕ (D ⊗ F)` — the smash
product distributes over the coalesced sum.

Confidence **inferred**. The page prints `(D ⊗ E) ⊕ (D ⊗ E)` for the right-hand
side, with `F` never appearing; the content stream confirms the byte `E` in both
positions. That form is false. On the same witness as `lem9_3` —
`D = E = Prop`, `F = Prop × Prop`, where `Prop` has a single non-`⊥` element so
`Prop ⊗ X ≅ X` — the cardinalities are: left side `5`, printed right side `3`,
corrected right side `5`. Replacing the second `E` by `F` is the only completion
consistent with the left-hand side, and it is the standard distributive law. -/
theorem lemma_9_5 :
    Nonempty (Smash α (CoalescedSum β γ) ≃o CoalescedSum (Smash α β) (Smash α γ)) :=
  ⟨Isomorphism.smashDistribCoalescedSum⟩

alias lem9_5 := lemma_9_5

/-- **Lemma 9.6.** `D⊥ ◦→ E ≅ D → E` — lifting is left adjoint to the forgetful
functor from pointed cpo's and strict maps to cpo's and continuous maps. This is
the sentence §4.4 already makes operationally, with `up : D → D⊥` the unit and
`(·)†` the induced strict extension.

Confidence **certain**; decoded as `D` `\077` (`0x3F` = `perpendicular`,
subscript) `\016\041` `E` `\030=` `D` `\041` `E`. -/
theorem lemma_9_6 : Nonempty (StrictHom (WithBot α) β ≃o ScottHom α β) :=
  ⟨Isomorphism.liftStrictHomIso⟩

alias lem9_6 := lemma_9_6

end Lemma9

/-! ### Theorem 14 — the two definitions of bifinite agree

> **Theorem 14** The following are equivalent for any cpo `D`.
> 1. `D` is bifinite.
> 2. `D` is a domain and `K(D)` is a Plotkin order.

Both lines are legible in the extraction; the reason Theorem 14 was unstatable is
elsewhere. `Bifinite.lean` **defines** `IsBifinite` to be condition 2's second
conjunct, so stating Theorem 14 against it would be stating `P ↔ P`. The paper's
own definition, which condition 1 refers to, is a different sentence:

> **Definition:** Let `D` be a cpo. Let `M` be the set of finitary projections
> with finite image. Then `D` is said to be bifinite if `M` is countable,
> directed and `⨆M = id`.

`IsBifiniteViaProjections` is that sentence, and `thm14` is the equivalence.
-/

section Theorem14

variable [CompletePartialOrder α]

/-- `M` in the paper's definition of bifinite: the finitary projections whose
image is finite. -/
def finiteImageProjections (α : Type*) [CompletePartialOrder α] : Set (ScottHom α α) :=
  {p | ScottHom.IsFinitaryProjection p ∧ (Set.range ⇑p).Finite}

/-- **Bifinite, in Gunter & Scott's own words** (§6): `M` is countable, directed,
and `⨆M = id`.

`⨆M = id` is written `IsLUB … ScottHom.id` rather than with `sSup`, following
`Domain.lean` — `IsLUB` needs no `SupSet` and transfers across subtypes, and on
the directed `M` the two readings coincide. -/
def IsBifiniteViaProjections (α : Type*) [CompletePartialOrder α] : Prop :=
  (finiteImageProjections α).Countable ∧
    DirectedOn (· ≤ ·) (finiteImageProjections α) ∧
    IsLUB (finiteImageProjections α) ScottHom.id

/-- **Theorem 14.** For any cpo `D`, `D` is bifinite — in the paper's sense, that
the finitary projections of finite image are countable, directed and join to the
identity — if and only if `D` is a domain whose basis `K(D)` is a Plotkin order.

Confidence **certain**: the theorem's two lines survive the font damage intact,
and the only repair needed is the `fi` ligature in "bifinite".

Note what the two sides cost. The development has always had the right-hand side
(`Domain α ∧ IsBifinite α`, `IsBifinite` being `IsPlotkinOrder (compacts α)`) and
has used it as *the* definition throughout §6 — `prop15`, `thm18`, Lemma 17's
five conjuncts. Theorem 14 is what licenses that substitution, and it is the one
place the left-hand side is needed.

**Proved in r0036.** The proof is `SFP.thm14_forward` and `SFP.thm14_converse`
in [`ScottDomains/SFP.lean`](../SFP.lean); this file keeps the statement. Of the
four gaps r0034 measured, two were real and two were false constraints:

1. *The `Fp(D)` machinery is stated at `[Domain α]`.* **Dissolved.** The forward
   direction needs none of it. `toFp`, `fpBasis` and `Fp.le_iff_fpBasis_subset`
   all speak about `im(p) ∩ K(D)`, and on a *finite* image
   `im(p) ∩ K(D) = im(p)` (`SFP.range_inter_compacts_of_finite`), so the whole
   argument runs on `im(p)` inside `D` with no basis coordinate. The measurement
   the r0036 plan asked for is therefore moot: `toFp` does still need
   `[Domain α]`, because `isFinitaryProjection_normalHom` spends countability of
   `K(D)` on the basis of `im(p_N)`.
2. *Finite basis and finite image are different conditions.* **Real, and
   proved** as `SFP.range_normalHom_of_finite` (`SFP.range_toFp_eq` in the
   `Fp(D)` coordinates). `p_N(x) = ⨆(N ∩ ↓x)`, and for finite `N` the directed
   set `N ∩ ↓x` contains its own greatest element, which is that supremum — so
   `im(p_N) = N`. For infinite `N` the statement is false and only
   `im(p_N) ∩ K(D) = N` survives.
3. *`IsLUB` does not transfer from `Fp(D)` to `D → D`.* **Dissolved.** It is not
   transferred. `SFP.isLUB_id_of_normalHom_mem` argues in `ScottHom α α`
   directly: an upper bound `b` of `M` dominates `p_{⟨k⟩} x` for every compact
   `k ⊑ x`, and `k ⊑ p_{⟨k⟩} x`, so `x = ⨆(K(D) ∩ ↓x) ⊑ b x` by algebraicity.
4. *Two finite-combinatorial lemmas.* **Real, and proved** as
   `SFP.exists_upperBound_of_finite_subset` and `SFP.exists_greatest_of_finite`.

One ingredient the r0034 note did not list is needed: `M` must be **nonempty**,
because `IsCompactElement` quantifies over *nonempty* directed sets and the
forward direction applies it to `{p x | p ∈ M}`. Mathlib's `DirectedOn` is
vacuous on `∅`, so the paper's "directed" — which asks every finite subset,
including `∅`, for an upper bound in the set — is not recovered from the second
conjunct above. `SFP.isFinitaryProjection_const_bot` supplies the witness: the
constant-`⊥` map is the least finitary projection.

The forward direction is then the paper's own sketch, three sentences above the
theorem on printed page 30: each `p ∈ M` has compact image, `{p x | p ∈ M}` is a
directed set of compacts with least upper bound `x`, which gives `IsAlgebraic`;
`K(D) ⊆ ⋃_{p ∈ M} im(p)` gives countability; and a single `p` fixing a finite set
of compacts gives the Plotkin order via
`IsFinitaryProjection.isNormalIn_compacts`. -/
theorem theorem_14 : IsBifiniteViaProjections α ↔ Domain α ∧ IsBifinite α := by
  constructor
  · rintro ⟨hcount, hdir, hlub⟩
    exact SFP.thm14_forward (fun _ => Iff.rfl) hcount hdir hlub
  · rintro ⟨hdom, hbif⟩
    haveI := hdom
    exact SFP.thm14_converse hbif fun _ => Iff.rfl

alias thm14 := theorem_14

end Theorem14

end ScottDomains.Recovered
