import ScottDomains.JungNets

/-!
# r0038 audit evidence: the `JungNets` duplicate pair

Round r0038 classifies every theorem of `BifiniteUniversal`, `Colimit`,
`Lemma30`, `JungSFP`, `JungFinite`, `JungNets` and `ContinuousConstruction`.
This file carries the one piece of evidence that round produces which the kernel
checks rather than a table row: it converts "these two look the same" into a
checked claim.

(The sentence above is wrapped so that no line begins with the word `theorem` at
column 0. `scripts/counts.sh` and `scripts/module-counts.sh` match
`^(@\[…\] )?(theorem|lemma) `, which counts such a prose line as a declaration.
`JungNets.lean` has two of them, so its reported count of 12 is a real count of
10; see the r0038 report.)

`JungNets.lean` ends with two declarations,

    jung_lemma_2_17_of_jung_theorem_1_37       (h : Theorem137 D) (hAlg) (hCount) {a₁ a₂ : D}
                             (ha₁ : IsCompactElement a₁) (ha₂ : IsCompactElement a₂) :
                             (minimalUpperBounds (compacts D) {a₁, a₂}).Finite

    propertyM_pairs_of_jung_theorem_1_37 (h : Theorem137 D) (hAlg) (hCount) :
                             ∀ x₁ x₂ : D, IsCompactElement x₁ → IsCompactElement x₂ →
                             (minimalUpperBounds (compacts D) {x₁, x₂}).Finite

which differ only in whether the pair is bound by the implicit-argument telescope
or by an explicit `∀`. Each is one application of the other, and the two theorems
below are the two applications: neither proof does any work beyond re-binding.

`propertyM_pairs_from_lemma217`'s proof term is character-for-character the body
of `JungNets.propertyM_pairs_of_jung_theorem_1_37` itself, which is the sharpest form the
evidence can take — the declaration adds nothing to the one above it.

Measured citation status at commit time, by `scripts/bifinite-audit-citations.sh`:
`propertyM_pairs_of_jung_theorem_1_37` is mentioned nowhere in the package except at its own
declaration, and `jung_lemma_2_17_of_jung_theorem_1_37`'s only mention is inside
`propertyM_pairs_of_jung_theorem_1_37`'s proof. So the pair is uncited as a pair, and
retiring either member costs nothing that is presently consumed.

Nothing outside `plans/` and `reports/` imports this file. It adds two theorems
and no `sorry`, and changes no existing proof.
-/

namespace ScottDomains.Audit.Bifinite

open ScottDomains ScottDomains.JungNets

variable {D : Type*} [CompletePartialOrder D] [IsAlgebraic D]

/-- **`propertyM_pairs_of_jung_theorem_1_37` from `jung_lemma_2_17_of_jung_theorem_1_37`.** One application;
this is `JungNets.propertyM_pairs_of_jung_theorem_1_37`'s own proof term. -/
theorem propertyM_pairs_from_lemma217 (h : Theorem137 D) (hAlg : IsAlgebraic (ScottHom D D))
    (hCount : (compacts (ScottHom D D)).Countable) :
    ∀ x₁ x₂ : D, IsCompactElement x₁ → IsCompactElement x₂ →
      (minimalUpperBounds (compacts D) ({x₁, x₂} : Set D)).Finite :=
  fun _ _ hx₁ hx₂ => jung_lemma_2_17_of_jung_theorem_1_37 h hAlg hCount hx₁ hx₂

/-- **`jung_lemma_2_17_of_jung_theorem_1_37` from `propertyM_pairs_of_jung_theorem_1_37`.** The converse
application, which is what makes the two interderivable rather than one merely
following from the other. -/
theorem lemma217_from_propertyM_pairs (h : Theorem137 D) (hAlg : IsAlgebraic (ScottHom D D))
    (hCount : (compacts (ScottHom D D)).Countable)
    {a₁ a₂ : D} (ha₁ : IsCompactElement a₁) (ha₂ : IsCompactElement a₂) :
    (minimalUpperBounds (compacts D) ({a₁, a₂} : Set D)).Finite :=
  propertyM_pairs_of_jung_theorem_1_37 h hAlg hCount a₁ a₂ ha₁ ha₂

end ScottDomains.Audit.Bifinite
