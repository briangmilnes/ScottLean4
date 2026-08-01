/-
  Axiomatizing Set Theory — Scott's cumulative-levels axiomatization
  (Accumulation, Restriction, Reflection)

  Faithful to:
    D. Scott, "Axiomatizing Set Theory",
    Proceedings of Symposia in Pure Mathematics 13, Part II (1974), 207-214.

  Source text extracted from:
    DanaScottPapers/Scott-1974-Axiomatizing-Set-Theory.txt

  Auto-generated faithful skeleton (core Lean 4 only; no Mathlib).

  Scott gives a strikingly economical axiomatization of Zermelo–Fraenkel set
  theory built on the intuition of a cumulative hierarchy of *levels* (partial
  universes) `V`.  Variables `a, b, …` range over sets, `x, y, …` over
  arbitrary objects, and `V, V′, …` over levels.  The primitives are
  membership `∈`, sethood, and the (definable, but here primitive) notion of a
  level.  The axioms:

    Grammar        ∀x,y[ x ∈ y → ∃a(y = a) ]         (y is a set)
    Extensionality ∀a,b[ ∀x(x∈a ↔ x∈b) → a = b ]
    Comprehension  ∀a ∃b ∀x[ x∈b ↔ x∈a ∧ Φ(x) ]      (schema)
    Accumulation   ∀V′∀x[ x∈V′ ↔ ¬∃a(x=a) ∨ ∃V∈V′(x∈V ∨ x⊆V) ]
    Restriction    ∀x ∃V[ x ∈ V ]                     (foundation)
    Reflection     ∃V ∀x∈V[ Φ(x) ↔ Φ^V(x) ]           (schema ⟹ infinity+replacement)

  From Accumulation and Restriction *alone* Scott derives that the levels are
  linearly — indeed well — ordered, that ∈ is well-founded, and that unions
  and (conditional) power sets exist; Reflection then delivers infinity and
  replacement.  We encode the axioms as a `class` and prove the first
  deduction — transitivity/(1): `V ∈ V′ → V ⊆ V′` — which the paper obtains
  "as an immediate consequence of the accumulation axiom".  The remaining
  derived results are stated as targets.

  The reflection schema is encoded shallowly: a "formula with relativizable
  quantifiers" is a map `Φ : (Obj → Prop) → Obj → Prop`, whose first argument
  is the predicate cutting the quantifier domain.  `Φ (fun _ => True)` is the
  full formula and `Φ (· ∈ V)` its relativization `Φ^V`.
-/

namespace AxiomatizingSetTheory

/-- Scott's cumulative-levels axiomatization.  `Obj` is the domain of all
    objects; `Mem` is `∈`; `IsSet` distinguishes sets from atoms; `IsLevel`
    picks out the levels (partial universes). -/
class ScottSetTheory (Obj : Type) where
  /-- Membership `∈`. -/
  Mem : Obj → Obj → Prop
  /-- Sethood: distinguishes sets from set-theoretic atoms. -/
  IsSet : Obj → Prop
  /-- Levelhood: picks out the levels (partial universes) `V`. -/
  IsLevel : Obj → Prop
  /-- Grammar (unnamed in the paper): `x ∈ y → y is a set`. -/
  grammar : ∀ {x y}, Mem x y → IsSet y
  /-- Each level is a set. -/
  level_isSet : ∀ {V}, IsLevel V → IsSet V
  /-- Extensionality: a set is determined by its elements. -/
  ext : ∀ {a b}, IsSet a → IsSet b → (∀ x, Mem x a ↔ Mem x b) → a = b
  /-- Comprehension (schema): every definable subcollection of a set is a set. -/
  comprehension : ∀ (a : Obj), IsSet a → ∀ (Φ : Obj → Prop),
      ∃ b, IsSet b ∧ ∀ x, Mem x b ↔ (Mem x a ∧ Φ x)
  /-- Accumulation: a level is exactly the accumulation of all members and
      subsets of all earlier levels (plus all non-sets).  `x ⊆ V` is written
      out as `∀ w, w ∈ x → w ∈ V`. -/
  accumulation : ∀ (V' : Obj), IsLevel V' → ∀ x,
      (Mem x V' ↔ ((¬ IsSet x) ∨
        ∃ V, IsLevel V ∧ Mem V V' ∧ (Mem x V ∨ (∀ w, Mem w x → Mem w V))))
  /-- Restriction: every object belongs to some level (⟺ foundation). -/
  restriction : ∀ x, ∃ V, IsLevel V ∧ Mem x V
  /-- Reflection (schema): some level `V` reflects every property `Φ`.
      `Φ (fun _ => True)` is `Φ`; `Φ (fun y => Mem y V)` is `Φ^V`. -/
  reflection : ∀ (Φ : (Obj → Prop) → Obj → Prop),
      ∃ V, IsLevel V ∧ ∀ x, Mem x V →
        (Φ (fun _ => True) x ↔ Φ (fun y => Mem y V) x)

namespace ScottSetTheory

variable {Obj : Type} [T : ScottSetTheory Obj]

@[inherit_doc] scoped infix:50 " ∈ₛ " => ScottSetTheory.Mem

/-- The subset relation `x ⊆ y` induced by `∈`. -/
def Sub (x y : Obj) : Prop := ∀ z, Mem z x → Mem z y

@[inherit_doc] scoped infix:50 " ⊆ₛ " => Sub

/-! ## First deduction: (1) `V ∈ V′ → V ⊆ V′`

    "as an immediate consequence of the accumulation axiom we have
     V ∈ V′ → V ⊆ V′.  This implies that the 'less than' relation among
     levels is transitive." -/

/-- (1) Levels are transitive under `∈`: if `V ∈ V′` (both levels) then
    `V ⊆ V′`.  Proved directly from Accumulation. -/
theorem level_mem_sub {V V' : Obj} (hV : IsLevel V) (hV' : IsLevel V')
    (h : Mem V V') : Sub V V' := by
  intro z hz
  -- unfold `z ∈ V'` via accumulation, choosing the witnessing earlier level `V`
  exact (T.accumulation V' hV' z).mpr (Or.inr ⟨V, hV, h, Or.inl hz⟩)

/-- Restated as transitivity of the level ordering `∈`: `V ∈ V′` and
    `W ∈ V` imply `W ∈ V′` (this is the content of (1)). -/
theorem level_trans {V V' W : Obj} (hV : IsLevel V) (hV' : IsLevel V')
    (h1 : Mem V V') (h2 : Mem W V) : Mem W V' :=
  level_mem_sub hV hV' h1 W h2

/-! ## Further derived results (targets)

    Scott derives all of the following from the axioms above.  We record the
    statements; the proofs (some intricate, "putting a paradox to work") are
    left as targets. -/

/-- (2) Irreflexivity of the level ordering: no level is a member of itself.
    Proved via the Russell set `{x ∈ V : x ∉ x}`. -/
def irreflexivity : Prop := ∀ V : Obj, IsLevel V → ¬ Mem V V
-- TODO: prove using comprehension (form `{x ∈ V : x ∉ x}`) and accumulation.

/-- (5) Full ∈-foundation / well-foundedness schema:
    every nonempty definable class has an ∈-minimal element. -/
def foundation : Prop :=
  ∀ (Φ : Obj → Prop), (∃ x, Φ x) →
    ∃ x, Φ x ∧ ¬ ∃ y, Mem y x ∧ Φ y
-- TODO: prove from restriction + the "grounded classes" paradox.

/-- (7) The levels are linearly ordered by `∈` (hence, with (1)+(6),
    well-ordered). -/
def levels_linear : Prop :=
  ∀ V V' : Obj, IsLevel V → IsLevel V' → Mem V V' ∨ V = V' ∨ Mem V' V
-- TODO: prove by the double reflection argument of the paper.

/-- (8) Elements have (conditional) power sets: if `a` belongs to some level,
    the collection of its subsets is a set. -/
def power_set : Prop :=
  ∀ a : Obj, (∃ V, IsLevel V ∧ Mem a V) →
    ∃ b, IsSet b ∧ ∀ c, Mem c b ↔ Sub c a
-- TODO: prove from (7) and comprehension.

/-- Reflection ⟹ Fraenkel replacement (12): for every set `a`, some level
    bounds the images chosen by a functional relation on `a`. -/
def replacement : Prop :=
  ∀ (a : Obj) (Ψ : Obj → Obj → Prop), IsSet a →
    ∃ V, IsLevel V ∧ ∀ x, Mem x a → (∃ y, Ψ x y) → ∃ y, Mem y V ∧ Ψ x y
-- TODO: derive from `reflection` (Scott's (11) ⟹ (12)).

end ScottSetTheory

end AxiomatizingSetTheory
