/-
  Axiomatizing Category Theory in Free Logic (Lean 4 formalization)

  Faithful to:
    C. Benzmüller and D. S. Scott,
    "Axiomatizing Category Theory in Free Logic",
    arXiv:1609.01493, 2016.

  Source text extracted from:
    DanaScottPapers/Benzmuller-Scott-2016-Axiomatizing-Category-Theory-in-Free-Logic.txt

  Auto-generated faithful skeleton.

  This module transcribes the free-logic axiom systems for category theory
  developed in the paper.  Morphisms are objects of a raw domain `M` (the paper's
  type `i`).  A distinguished existence predicate `E : M → Prop` carves out the
  subdomain of *existing* (defined) objects; free variables and arbitrary terms
  (e.g. the partial composition `x ⊙ y`) may denote non-existing objects.

  We encode:
    * the free-logic primitives: existence `E`, the partial operations
      `dom`, `cod`, and composition `⊙` (Section 3);
    * Kleene equality `x ≂ y ≡ (E x ∨ E y) → x = y` and the non-reflexive
      existing identity `ExId x y ≡ E x ∧ E y ∧ x = y` (Section 3);
    * the identity-morphism predicate `IsId` (Section 3);
    * Axiom Sets I–VIII (Sections 4–10) as `structure … : Prop` bundles;
    * the constricted-inconsistency theorem for Axiom Set VII
      (`InconsistencyInteractiveVII`, Section 9.2), reconstructed faithfully
      from the interactive proof in the paper.

  Core Lean 4 only; no Mathlib.
-/

namespace BenzmullerScott2016

universe u

/-- Free-logic categorical signature (Section 3).  A raw domain `M`, an existence
    predicate `E`, and the three partial operations `dom`, `cod`, composition. -/
class FreeCat (M : Type u) where
  /-- Existence / definedness predicate (the paper's `E`). -/
  E   : M → Prop
  /-- Domain operation. -/
  dom : M → M
  /-- Codomain operation. -/
  cod : M → M
  /-- Morphism composition (partial); set-theoretic order `(x ⊙ y) a ≂ x (y a)`. -/
  comp : M → M → M

namespace FreeCat

variable {M : Type u} [FreeCat M]

@[inherit_doc] infixl:70 " ⊙ " => FreeCat.comp

/-- Kleene equality: `x ≂ y ≡ (E x ∨ E y) → x = y`.  An equivalence relation. -/
def KlEq (x y : M) : Prop := (E x ∨ E y) → x = y

@[inherit_doc] scoped infix:56 " ≂ " => KlEq

/-- Existing identity `x ≃ y ≡ E x ∧ E y ∧ x = y`.  Symmetric and transitive but,
    unlike Kleene equality, *not* reflexive. -/
def ExId (x y : M) : Prop := E x ∧ E y ∧ x = y

/-- Identity-morphism predicate (Section 3): `I i` holds iff `i` acts as a
    two-sided (Kleene) identity wherever the composite exists. -/
def IsId (e : M) : Prop :=
  (∀ x : M, E (e ⊙ x) → KlEq (e ⊙ x) x) ∧
  (∀ x : M, E (x ⊙ e) → KlEq (x ⊙ e) x)

/-! ### Basic properties of Kleene equality (Section 3, `lemma … by blast`). -/

theorem KlEq.refl (x : M) : x ≂ x := fun _ => rfl

theorem KlEq.symm {x y : M} (h : x ≂ y) : y ≂ x :=
  fun hxy => (h hxy.symm).symm

theorem KlEq.trans {x y z : M} (hxy : x ≂ y) (hyz : y ≂ z) : x ≂ z := by
  intro h
  rcases h with hx | hz
  · have hxy' : x = y := hxy (Or.inl hx)
    have hy : E y := hxy' ▸ hx
    exact hxy'.trans (hyz (Or.inl hy))
  · have hyz' : y = z := hyz (Or.inr hz)
    have hy : E y := hyz' ▸ hz
    exact (hxy (Or.inr hy)).trans hyz'

/-- Existing identity implies Kleene equality (Section 3). -/
theorem ExId.toKlEq {x y : M} (h : ExId x y) : x ≂ y := fun _ => h.2.2

end FreeCat

open FreeCat

/-! ## Axiom Set I (Section 4)

    The most basic axiom set: a partial, strict composition generalizing the
    monoid axioms, with left/right identities postulated existentially. -/
structure AxiomSetI (M : Type u) [FreeCat M] : Prop where
  /-- `S i` — Strictness. -/
  Si : ∀ x y : M, E (x ⊙ y) → (E x ∧ E y)
  /-- `E i` — Existence (the ← direction). -/
  Ei : ∀ x y : M,
        (E x ∧ E y ∧ ∃ z : M, (z ⊙ z ≂ z) ∧ (x ⊙ z ≂ x) ∧ (z ⊙ y ≂ y)) → E (x ⊙ y)
  /-- `A i` — Associativity. -/
  Ai : ∀ x y z : M, x ⊙ (y ⊙ z) ≂ (x ⊙ y) ⊙ z
  /-- `C i` — Codomain (existence of a left identity). -/
  Ci : ∀ y : M, ∃ i : M, IsId i ∧ (i ⊙ y ≂ y)
  /-- `D i` — Domain (existence of a right identity). -/
  Di : ∀ x : M, ∃ j : M, IsId j ∧ (x ⊙ j ≂ x)

/-! ## Axiom Set II (Section 5)

    Skolemizes the identities of Axiom Set I into total `dom`/`cod` functions. -/
structure AxiomSetII (M : Type u) [FreeCat M] : Prop where
  /-- `S ii` — Strictness (extended to `dom`, `cod`). -/
  Sii : ∀ x y : M,
        (E (x ⊙ y) → (E x ∧ E y)) ∧ (E (dom x) → E x) ∧ (E (cod y) → E y)
  /-- `E ii` — Existence. -/
  Eii : ∀ x y : M,
        (E x ∧ E y ∧ ∃ z : M, (z ⊙ z ≂ z) ∧ (x ⊙ z ≂ x) ∧ (z ⊙ y ≂ y)) → E (x ⊙ y)
  /-- `A ii` — Associativity. -/
  Aii : ∀ x y z : M, x ⊙ (y ⊙ z) ≂ (x ⊙ y) ⊙ z
  /-- `C ii` — Codomain. -/
  Cii : ∀ y : M, E y → (IsId (cod y) ∧ (cod y ⊙ y ≂ y))
  /-- `D ii` — Domain. -/
  Dii : ∀ x : M, E x → (IsId (dom x) ∧ (x ⊙ dom x ≂ x))

/-! ## Axiom Set III (Section 6)

    Simplifies the existence axiom using the Skolem functions `dom`, `cod`. -/
structure AxiomSetIII (M : Type u) [FreeCat M] : Prop where
  Siii : ∀ x y : M,
        (E (x ⊙ y) → (E x ∧ E y)) ∧ (E (dom x) → E x) ∧ (E (cod y) → E y)
  /-- `E iii` — Existence: `E (x ⊙ y) ← (dom x ≂ cod y ∧ E (cod y))`. -/
  Eiii : ∀ x y : M, ((dom x ≂ cod y) ∧ E (cod y)) → E (x ⊙ y)
  Aiii : ∀ x y z : M, x ⊙ (y ⊙ z) ≂ (x ⊙ y) ⊙ z
  Ciii : ∀ y : M, E y → (IsId (cod y) ∧ (cod y ⊙ y ≂ y))
  Diii : ∀ x : M, E x → (IsId (dom x) ∧ (x ⊙ dom x ≂ x))

/-! ## Axiom Set IV (Section 7)

    Simplifies `C`/`D`; the existence axiom is strengthened to an equivalence. -/
structure AxiomSetIV (M : Type u) [FreeCat M] : Prop where
  Siv : ∀ x y : M,
        (E (x ⊙ y) → (E x ∧ E y)) ∧ (E (dom x) → E x) ∧ (E (cod y) → E y)
  /-- `E iv` — Existence (now an equivalence). -/
  Eiv : ∀ x y : M, E (x ⊙ y) ↔ ((dom x ≂ cod y) ∧ E (cod y))
  Aiv : ∀ x y z : M, x ⊙ (y ⊙ z) ≂ (x ⊙ y) ⊙ z
  /-- `C iv` — Codomain. -/
  Civ : ∀ y : M, cod y ⊙ y ≂ y
  /-- `D iv` — Domain. -/
  Div : ∀ x : M, x ⊙ dom x ≂ x

/-! ## Axiom Set V (Section 8) — Scott's system (≈ Freyd–Scedrov, corrected)

    Uses the non-reflexive existing identity `ExId` in the existence axiom `S3`. -/
structure AxiomSetV (M : Type u) [FreeCat M] : Prop where
  /-- `S1` — Strictness of `dom`. -/
  S1 : ∀ x : M, E (dom x) → E x
  /-- `S2` — Strictness of `cod`. -/
  S2 : ∀ y : M, E (cod y) → E y
  /-- `S3` — Existence: `E (x ⊙ y) ↔ dom x ≃ cod y` (existing identity `≃`). -/
  S3 : ∀ x y : M, E (x ⊙ y) ↔ ExId (dom x) (cod y)
  /-- `S4` — Associativity. -/
  S4 : ∀ x y z : M, x ⊙ (y ⊙ z) ≂ (x ⊙ y) ⊙ z
  /-- `S5` — Domain. -/
  S5 : ∀ x : M, x ⊙ dom x ≂ x
  /-- `S6` — Codomain. -/
  S6 : ∀ y : M, cod y ⊙ y ≂ y

/-! ## Axiom Set VI (Section 9.1) — Freyd–Scedrov with `≃` in A1. -/
structure AxiomSetVI (M : Type u) [FreeCat M] : Prop where
  A1  : ∀ x y : M, E (x ⊙ y) ↔ ExId (dom x) (cod y)
  A2a : ∀ x : M, cod (dom x) ≂ dom x
  A2b : ∀ y : M, dom (cod y) ≂ cod y
  A3a : ∀ x : M, x ⊙ dom x ≂ x
  A3b : ∀ y : M, cod y ⊙ y ≂ y
  A4a : ∀ x y : M, dom (x ⊙ y) ≂ dom ((dom x) ⊙ y)
  A4b : ∀ x y : M, cod (x ⊙ y) ≂ cod (x ⊙ (cod y))
  A5  : ∀ x y z : M, x ⊙ (y ⊙ z) ≂ (x ⊙ y) ⊙ z

/-! ## Axiom Set VII (Section 9.2) — Freyd–Scedrov with Kleene `≂` in A1.

    Identical to Axiom Set VI except that `A1` uses Kleene equality instead of the
    existing identity.  In free logic (free variables ranging over all objects)
    this small change causes a *constricted inconsistency*: assuming a
    non-existing object yields falsity. -/
structure AxiomSetVII (M : Type u) [FreeCat M] : Prop where
  /-- `A1` — Existence with **Kleene** equality (the source of inconsistency). -/
  A1  : ∀ x y : M, E (x ⊙ y) ↔ (dom x ≂ cod y)
  A2a : ∀ x : M, cod (dom x) ≂ dom x
  A2b : ∀ y : M, dom (cod y) ≂ cod y
  A3a : ∀ x : M, x ⊙ dom x ≂ x
  A3b : ∀ y : M, cod y ⊙ y ≂ y
  A4a : ∀ x y : M, dom (x ⊙ y) ≂ dom ((dom x) ⊙ y)
  A4b : ∀ x y : M, cod (x ⊙ y) ≂ cod (x ⊙ (cod y))
  A5  : ∀ x y z : M, x ⊙ (y ⊙ z) ≂ (x ⊙ y) ⊙ z

/-! ## Axiom Set VIII (Section 10)

    Freyd–Scedrov with variables restricted to existing objects (free-logic `∀`)
    plus explicit strictness (`B0a`, `B0b`, `B0c`), restoring equivalence to V. -/
structure AxiomSetVIII (M : Type u) [FreeCat M] : Prop where
  /-- `B0a` — Strictness of composition. -/
  B0a : ∀ x y : M, E (x ⊙ y) → (E x ∧ E y)
  /-- `B0b` — Strictness of `dom`. -/
  B0b : ∀ x : M, E (dom x) → E x
  /-- `B0c` — Strictness of `cod`. -/
  B0c : ∀ y : M, E (cod y) → E y
  /-- Free-logic `∀`: axioms range over existing objects only. -/
  B1  : ∀ x y : M, E x → E y → (E (x ⊙ y) ↔ (dom x ≂ cod y))
  B2a : ∀ x : M, E x → (cod (dom x) ≂ dom x)
  B2b : ∀ y : M, E y → (dom (cod y) ≂ cod y)
  B3a : ∀ x : M, E x → (x ⊙ dom x ≂ x)
  B3b : ∀ y : M, E y → (cod y ⊙ y ≂ y)
  B4a : ∀ x y : M, E x → E y → (dom (x ⊙ y) ≂ dom ((dom x) ⊙ y))
  B4b : ∀ x y : M, E x → E y → (cod (x ⊙ y) ≂ cod (x ⊙ (cod y)))
  B5  : ∀ x y z : M, E x → E y → E z → (x ⊙ (y ⊙ z) ≂ (x ⊙ y) ⊙ z)

/-! ## The constricted inconsistency of Axiom Set VII (Section 9.2)

    Reconstruction of `InconsistencyInteractiveVII`.  From the axioms `A1`, `A2a`,
    `A3a` alone, the assumption that some object fails to exist yields falsity. -/
theorem InconsistencyInteractiveVII {M : Type u} [FreeCat M]
    (ax : AxiomSetVII M) (hNEx : ∃ a : M, ¬ E a) : False := by
  obtain ⟨a, ha⟩ := hNEx
  -- (2) A3a a :  a ⊙ dom a ≂ a
  have h2 : a ⊙ dom a ≂ a := ax.A3a a
  -- (3) hence a ⊙ dom a is not defined: if it were, a would be too.
  have h3 : ¬ E (a ⊙ dom a) := by
    intro hE
    have heq : a ⊙ dom a = a := h2 (Or.inl hE)
    exact ha (heq ▸ hE)
  -- (5) A2a a :  cod (dom a) ≂ dom a ; take its symmetric form.
  have h5 : dom a ≂ cod (dom a) := KlEq.symm (ax.A2a a)
  -- (4) A1 a (dom a) :  E (a ⊙ dom a) ↔ dom a ≂ cod (dom a)
  have h4 : E (a ⊙ dom a) ↔ (dom a ≂ cod (dom a)) := ax.A1 a (dom a)
  -- (7) therefore a ⊙ dom a *is* defined — contradicting (3).
  exact h3 (h4.mpr h5)

/-- Corollary: under Axiom Set VII every object exists (composition is total),
    so the theory collapses to a monoid (Section 9.2). -/
theorem AxiomSetVII.allExist {M : Type u} [FreeCat M] (ax : AxiomSetVII M) :
    ∀ x : M, E x := by
  intro x
  cases Classical.em (E x) with
  | inl h => exact h
  | inr h => exact (InconsistencyInteractiveVII ax ⟨x, h⟩).elim

/-! ## Sample equivalence fragments

    The paper proves the full mutual equivalence of Axiom Sets I–VI (mostly via
    Sledgehammer/`metis`).  We record two of the trivial projection directions and
    leave the automation-dependent directions as explicit obligations. -/

/-- `S4`/`S5`/`S6` of Axiom Set V are exactly `A iv`/`D iv`/`C iv` of IV: the
    associativity, domain, and codomain axioms coincide.  (Trivial direction.) -/
theorem AxiomSetV.assoc {M : Type u} [FreeCat M] (ax : AxiomSetV M) :
    ∀ x y z : M, x ⊙ (y ⊙ z) ≂ (x ⊙ y) ⊙ z := ax.S4

/-- Axiom Set V implies the codomain/domain equations of Axiom Set IV. -/
theorem AxiomSetV.civ_div {M : Type u} [FreeCat M] (ax : AxiomSetV M) :
    (∀ y : M, cod y ⊙ y ≂ y) ∧ (∀ x : M, x ⊙ dom x ≂ x) :=
  ⟨ax.S6, ax.S5⟩

/-- Full equivalence of Axiom Sets V and IV (Section 8).
    TODO: the `E iv ↔ S3` direction relies on the paper's `metis` proofs and is
    left as an obligation — no proof is fabricated. -/
theorem AxiomSetV_iff_IV (M : Type u) [FreeCat M] :
    Nonempty (AxiomSetV M) ↔ Nonempty (AxiomSetIV M) := by
  sorry -- TODO: reconstruct the mutual implications proved by Sledgehammer.

end BenzmullerScott2016
