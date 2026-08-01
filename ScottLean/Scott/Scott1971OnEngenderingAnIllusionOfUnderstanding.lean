/-
  On Engendering an Illusion of Understanding — the theory of
  conditional assertion (multiple-conclusion consequence relations)

  Faithful to:
    D. Scott, "On Engendering an Illusion of Understanding",
    The Journal of Philosophy 68(21):787-807, 1971.

  Source text extracted from:
    DanaScottPapers/Scott-1971-On-Engendering-an-Illusion-of-Understanding.txt

  Auto-generated faithful skeleton (core Lean 4 only; no Mathlib).

  Much of this paper is philosophical: a critique — echoing Quine — of
  strict implication and the "illusion of understanding" engendered by
  modal contexts.  It has, however, a genuine formal core (Section II),
  which is what we transcribe here.

  Scott founds bivalent logic on two notions: a *valuation* v : S → {0,1}
  and a *conditional assertion*  α ⊢ β  between finite sets of statements.
  Given a set V of "intended valuations", he defines (p. 796):

     α ⊢ β   iff   every v ∈ V making every statement in α true
                   makes at least one statement in β true.

  He then isolates the three laws that axiomatize this relation (p. 796):

     (R) Reflexivity:   α ⊢ β    whenever α ∩ β ≠ ∅
     (M) Monotonicity:  α ⊢ β    ⟹  α,α' ⊢ β,β'
     (T) Transitivity (cut): α ⊢ β,A  and  α,A ⊢ β  ⟹  α ⊢ β

  We take statements to be an arbitrary type `S`, valuations to be maps
  `S → Bool`, and finite sets to be `List S` (order and repetition are
  immaterial to `Entails`).  We PROVE (R), (M), (T) hold for the semantic
  definition, and record the soundness/completeness statement (Scott's
  representation theorem) as a `Prop`-valued target with a TODO.
-/

namespace OnEngendering

/-- A valuation assigns a truth value (`Bool`) to every statement.
    `1 = true`, `0 = false` in Scott's notation. -/
abbrev Val (S : Type) := S → Bool

/-- The semantic conditional assertion determined by a set `V` of intended
    valuations (Scott, p. 796):

      α ⊢ β  iff  for every intended valuation `v` that makes every
      statement of `α` true, `v` makes at least one statement of `β` true.

    Finite subsets are modelled as `List`s. -/
def Entails {S : Type} (V : Val S → Prop) (α β : List S) : Prop :=
  ∀ v, V v → (∀ A ∈ α, v A = true) → ∃ B ∈ β, v B = true

/-! ## The three laws (R), (M), (T)

    These are provable directly from the definition of `Entails`; they hold
    for *every* choice of intended valuations `V`. -/

/-- **(R) Reflexivity.**  If a statement `A` lies in both `α` and `β`, then
    `α ⊢ β`.  (Scott states this as "α ⊢ β if α ∩ β ≠ ∅".) -/
theorem entails_refl {S : Type} (V : Val S → Prop) {α β : List S}
    {A : S} (hα : A ∈ α) (hβ : A ∈ β) : Entails V α β := by
  intro v _ htrue
  exact ⟨A, hβ, htrue A hα⟩

/-- **(M) Monotonicity.**  Enlarging both sides preserves entailment:
    `α ⊢ β` implies `α ++ α' ⊢ β ++ β'`. -/
theorem entails_mono {S : Type} (V : Val S → Prop) {α α' β β' : List S}
    (h : Entails V α β) : Entails V (α ++ α') (β ++ β') := by
  intro v hv htrue
  have hα : ∀ A ∈ α, v A = true := fun A hA => htrue A (List.mem_append_left _ hA)
  obtain ⟨B, hBβ, hvB⟩ := h v hv hα
  exact ⟨B, List.mem_append_left _ hBβ, hvB⟩

/-- **(T) Transitivity / the cut rule.**  From `α ⊢ β, A` and `α, A ⊢ β`
    infer `α ⊢ β`.  This is the rule Scott stresses "cannot be eliminated". -/
theorem entails_cut {S : Type} (V : Val S → Prop) {α β : List S} {A : S}
    (h1 : Entails V α (A :: β)) (h2 : Entails V (A :: α) β) :
    Entails V α β := by
  intro v hv hα
  obtain ⟨C, hCmem, hvC⟩ := h1 v hv hα
  rcases List.mem_cons.mp hCmem with hCA | hCβ
  · -- C = A, so `v A = true`; feed `A :: α` to the second premise.
    subst hCA
    have hAα : ∀ X ∈ (C :: α), v X = true := by
      intro X hX
      rcases List.mem_cons.mp hX with hXA | hXα
      · exact hXA ▸ hvC
      · exact hα X hXα
    exact h2 v hv hAα
  · exact ⟨C, hCβ, hvC⟩

/-! ## Consistent valuations and the representation theorem

    "Given ⊢, we say a valuation v is consistent with ⊢ (v ∈ ‖⊢‖) iff
     whenever α ⊢ β and v makes all of α true, it makes some of β true."
    (Scott, p. 797.)

    Scott's representation theorem: an abstract relation `E` on finite sets
    satisfying (R), (M), (T) is exactly the semantic entailment relation
    determined by its own set of consistent valuations.  The nontrivial
    direction ("if not α ⊢ β then some consistent v makes α true, β false")
    needs the axiom of choice in the uncountable case. -/

/-- `v` is consistent with an abstract consequence relation `E`. -/
def Consistent {S : Type} (E : List S → List S → Prop) (v : Val S) : Prop :=
  ∀ α β, E α β → (∀ A ∈ α, v A = true) → ∃ B ∈ β, v B = true

/-- The set of valuations consistent with `E` (Scott's `‖⊢‖`). -/
def consistentVals {S : Type} (E : List S → List S → Prop) : Val S → Prop :=
  fun v => Consistent E v

/-- **Soundness half** of the representation theorem: if `E α β` holds, then
    `α ⊢ β` under the intended valuations `consistentVals E`.  This direction
    is immediate from the definition of consistency. -/
theorem entails_of_rel {S : Type} (E : List S → List S → Prop)
    {α β : List S} (h : E α β) : Entails (consistentVals E) α β := by
  intro v hv hα
  exact hv α β h hα

/-- **Completeness half** (Scott's representation theorem, hard direction):
    a relation satisfying (R), (M), (T) is recovered from its consistent
    valuations.  Proof needs a maximal-valuation construction (AC in the
    uncountable case); left as a target. -/
def representation_theorem : Prop :=
  ∀ (S : Type) (E : List S → List S → Prop),
    -- E satisfies (R), (M), (T):
    (∀ α β A, A ∈ α → A ∈ β → E α β) →
    (∀ α α' β β', E α β → E (α ++ α') (β ++ β')) →
    (∀ α β A, E α (A :: β) → E (A :: α) β → E α β) →
    -- then E is exactly semantic entailment by its consistent valuations:
    ∀ α β, E α β ↔ Entails (consistentVals E) α β

-- TODO: prove `representation_theorem` (the hard "⟸" direction constructs,
-- for α ⊬ β, a consistent valuation true on α and false on β; countable case
-- is a stepwise construction, general case uses the axiom of choice).

/-! ## The Gentzen-style connective rules (Section III)

    Scott notes each connective is governed independently by a two-sided rule;
    e.g. conjunction `∧` is fixed by the three assertions (p. 799):

        A, B ⊢ A∧B      A∧B ⊢ A      A∧B ⊢ B

    from which `v(A ∧ B) = true ↔ v A = true ∧ v B = true` for every
    consistent `v`.  We record the conjunction rule as a predicate on `E`. -/

/-- The three conditional assertions Scott gives for conjunction. -/
def ConjRule {S : Type} (E : List S → List S → Prop) (and : S → S → S) : Prop :=
  ∀ A B, E [A, B] [and A B] ∧ E [and A B] [A] ∧ E [and A B] [B]

end OnEngendering
