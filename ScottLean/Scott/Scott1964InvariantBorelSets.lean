/-
  Invariant Borel Sets (Lean 4 faithful skeleton)

  Faithful to:
    Dana Scott, "Invariant Borel Sets",
    Fundamenta Mathematicae 56 (1964), pp. 117-128.

  Source text extracted from:
    DanaScottPapers/Scott-1964-Invariant-Borel-Sets.txt

  This is an auto-generated faithful skeleton.  It transcribes the core formal
  objects of the paper:

    * The setting (Section 1, p. 117): `N = {0,1,2,…}`; a group `Γ` of
      permutations of `N`, acting on the Cantor space `2^N`; the induced
      equivalence `f₀ ≡ f₁ (Γ)`.  The condition on `Γ` is that it be a *closed
      subgroup* of `N!` (all permutations) in the Baire-space topology (p. 117).
    * "Cantor's Lemma" (p. 118-119): a back-and-forth lemma giving `f₀ = f₁ (Γ)`
      from a binary relation `R` on finite sequences with the four properties
      (i)-(iv).
    * The `Γ`-Borel equivalence `⟨f₀,s⟩ ≡ ⟨f₁,t⟩ (Γ-Borel)` on `2^N × N^k`
      and `Γ`-invariance of subsets of `2^N × N^k` (p. 120-121).
    * MAIN THEOREM (p. 122-123): if `Γ` is a closed subgroup of `N!`, then the
      relation `f₀ ≡ f₁ (Γ)` partitions `2^N` into the minimal `Γ`-invariant
      sets, each of which is a Borel subset of `2^N`.
    * Section 2 application: the isomorphism types of countable relational
      structures (`S₂`, binary relations on subsets of `N`) are Borel; solving
      Kuratowski's problem for order types of sets of rationals.

  Core Lean 4 only; no Mathlib.  Topology, the Borel σ-field and "closed" are
  stated abstractly via predicates/parameters.  Deep results are `sorry`.
-/

namespace Scott1964

/-! ## The group action on Cantor space -/

/-- `N`, the non-negative integers. -/
abbrev N := Nat

/-- A point of Cantor space `2^N` (characteristic function of a subset of `N`). -/
abbrev Cantor := N → Bool

/-- A permutation of `N`: a bijection given with its inverse. -/
structure Perm where
  toFun    : N → N
  invFun   : N → N
  left_inv  : ∀ n, invFun (toFun n) = n
  right_inv : ∀ n, toFun (invFun n) = n

/-- The identity permutation. -/
def Perm.id : Perm where
  toFun := fun n => n
  invFun := fun n => n
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- Composition of permutations. -/
def Perm.comp (g h : Perm) : Perm where
  toFun := fun n => g.toFun (h.toFun n)
  invFun := fun n => h.invFun (g.invFun n)
  left_inv := by intro n; simp [g.left_inv, h.left_inv]
  right_inv := by intro n; simp [g.right_inv, h.right_inv]

/-- A subgroup `Γ ⊆ N!` of permutations, given as a membership predicate closed
    under identity, composition and inverse. -/
structure Subgroup where
  mem       : Perm → Prop
  id_mem    : mem Perm.id
  comp_mem  : ∀ g h, mem g → mem h → mem (g.comp h)
  inv_mem   : ∀ g, mem g →
                mem { toFun := g.invFun, invFun := g.toFun,
                      left_inv := g.right_inv, right_inv := g.left_inv }

/-- The action of a permutation on a point of `2^N`: `f ∘ g` (p. 118, "`f ∘ g`
    is the characteristic function of the inverse image"). -/
def act (f : Cantor) (g : Perm) : Cantor := fun n => f (g.toFun n)

/-- The equivalence `f₀ ≡ f₁ (Γ)` (p. 118): `f₁ = f₀ ∘ g` for some `g ∈ Γ`. -/
def GammaEquiv (Γ : Subgroup) (f₀ f₁ : Cantor) : Prop :=
  ∃ g : Perm, Γ.mem g ∧ f₁ = act f₀ g

/-- `GammaEquiv` is an equivalence relation (p. 118). -/
theorem gammaEquiv_refl (Γ : Subgroup) (f : Cantor) : GammaEquiv Γ f f :=
  ⟨Perm.id, Γ.id_mem, by funext n; rfl⟩

theorem gammaEquiv_symm (Γ : Subgroup) (f₀ f₁ : Cantor) :
    GammaEquiv Γ f₀ f₁ → GammaEquiv Γ f₁ f₀ := by
  sorry -- TODO symmetry of ≡ (Γ)

theorem gammaEquiv_trans (Γ : Subgroup) (f₀ f₁ f₂ : Cantor) :
    GammaEquiv Γ f₀ f₁ → GammaEquiv Γ f₁ f₂ → GammaEquiv Γ f₀ f₂ := by
  sorry -- TODO transitivity of ≡ (Γ)

/-! ## Closed subgroups and invariant / Borel sets

    Topology is abstracted: a `BorelStructure` supplies the predicate `IsBorel`
    on subsets of `2^N` (closed under complement and countable unions), and
    `IsClosedSubgroup` marks the closed subgroups of `N!` (p. 117: `Γ` is closed
    in the Baire-space topology on `N!`). -/

/-- The abstract Borel σ-field on Cantor space, plus the notion of a closed
    subgroup of `N!`. -/
structure BorelStructure where
  IsBorel         : (Cantor → Prop) → Prop
  borel_compl     : ∀ S, IsBorel S → IsBorel (fun f => ¬ S f)
  borel_iUnion    : ∀ S : Nat → (Cantor → Prop), (∀ n, IsBorel (S n)) →
                      IsBorel (fun f => ∃ n, S n f)
  IsClosedSubgroup : Subgroup → Prop

/-- A subset `S ⊆ 2^N` is *`Γ`-invariant* (p. 120-123): closed under the action
    of every `g ∈ Γ`. -/
def GammaInvariant (Γ : Subgroup) (S : Cantor → Prop) : Prop :=
  ∀ f g, Γ.mem g → S f → S (act f g)

/-- A *minimal `Γ`-invariant set* (p. 117): a non-empty invariant set including
    no smaller non-empty invariant set — exactly an orbit of a single point. -/
def MinimalInvariant (Γ : Subgroup) (S : Cantor → Prop) : Prop :=
  (∃ f, S f) ∧ GammaInvariant Γ S ∧
    ∀ T, GammaInvariant Γ T → (∀ f, T f → S f) → (∃ f, T f) → (∀ f, S f → T f)

/-- The orbit of a point `f₀` under `Γ` is `{ f | f ≡ f₀ (Γ) }`. -/
def orbit (Γ : Subgroup) (f₀ : Cantor) : Cantor → Prop :=
  fun f => GammaEquiv Γ f₀ f

/-! ## Cantor's Lemma and the main theorem -/

/-- "Cantor's Lemma" (p. 118).  Let `Γ` be a closed subgroup and `f₀ f₁ ∈ 2^N`.
    Suppose `R` is a binary relation on finite integer sequences with
    `⟨⟩ R ⟨⟩` and the four back-and-forth properties (i)-(iv).  Then
    `f₀ ≡ f₁ (Γ)`.  We package the sequences as `List N` and take the four
    properties as a single hypothesis `H`. -/
theorem cantor_lemma (B : BorelStructure) (Γ : Subgroup)
    (_hclosed : B.IsClosedSubgroup Γ) (f₀ f₁ : Cantor)
    (R : List N → List N → Prop) (_hnil : R [] [])
    (_H : True) :  -- placeholder for the back-and-forth conditions (i)-(iv)
    GammaEquiv Γ f₀ f₁ := by
  sorry -- TODO Cantor's Lemma (back-and-forth construction of the permutation)

/-- MAIN THEOREM (p. 123).  If `Γ` is a closed subgroup of `N!`, then the
    relation `f₀ ≡ f₁ (Γ)` partitions `2^N` into the minimal `Γ`-invariant sets,
    each of which is a Borel subset of `2^N`.  Concretely: every orbit is a
    minimal invariant set and is Borel. -/
theorem orbits_are_borel (B : BorelStructure) (Γ : Subgroup)
    (_hclosed : B.IsClosedSubgroup Γ) (f₀ : Cantor) :
    MinimalInvariant Γ (orbit Γ f₀) ∧ B.IsBorel (orbit Γ f₀) := by
  sorry -- TODO Main Theorem (orbits under a closed subgroup are Borel)

/-- Remark (p. 123).  The theorem cannot be strengthened: the graph
    `{ ⟨f₀,f₁⟩ | f₀ ≡ f₁ (Γ) }` need not be a Borel subset of `2^N × 2^N`
    (it is analytic; for certain closed `Γ` it is not Borel). -/
theorem equivalence_graph_not_always_borel :
    ∃ (B : BorelStructure) (Γ : Subgroup),
      B.IsClosedSubgroup Γ ∧
      ¬ (∃ IsBorel2 : (Cantor × Cantor → Prop) → Prop,
           IsBorel2 (fun p => GammaEquiv Γ p.1 p.2)) := by
  sorry -- TODO the equivalence graph is analytic but not Borel in general

/-! ## Section 2.  Isomorphism types of countable structures are Borel -/

/-- Binary relational structures `S₂` on subsets of `N` (p. 122): a subset `A`
    of `N` and a relation `R ⊆ A × A`, coded inside `P(N) × P(N×N)`. -/
structure BinaryStructure where
  A  : N → Prop
  R  : N → N → Prop

/-- Isomorphism of binary structures (p. 122): a bijection `h : A ↔ B` with
    `x R y ↔ h x S h y`. -/
def IsoStructure (X Y : BinaryStructure) : Prop :=
  ∃ (h h' : N → N),
    (∀ a, X.A a → Y.A (h a)) ∧ (∀ b, Y.A b → X.A (h' b)) ∧
    (∀ a, X.A a → h' (h a) = a) ∧ (∀ b, Y.A b → h (h' b) = b) ∧
    (∀ a b, X.A a → X.A b → (X.R a b ↔ Y.R (h a) (h b)))

/-- THEOREM (p. 123).  Each isomorphism type of a countable binary relational
    structure is a Borel subset of the space `S₂` of such structures.  Stated via
    an abstract Borel predicate on `S₂`. -/
theorem isomorphism_types_borel
    (IsBorelS2 : (BinaryStructure → Prop) → Prop) (X₀ : BinaryStructure) :
    IsBorelS2 (fun X => IsoStructure X X₀) := by
  sorry -- TODO isomorphism types are Borel (via the main theorem)

end Scott1964
