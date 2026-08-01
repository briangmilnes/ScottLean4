/-
  Dana Scott, "Some Definitional Suggestions for Automata Theory"
  Journal of Computer and System Sciences 1, 187-212 (1967).

  Auto-generated faithful skeleton (Lean 4 core; no Mathlib).

  This file transcribes the *core definitional framework* of Scott's paper.  The
  paper's central methodological proposal is the strict SEPARATION of the concept
  of a *program* (a linguistic object, Section 1) from the concept of a *machine*
  (a bundle of partial functions, Section 2), the two being brought together only
  in the notion of a *computation* (Section 3).  A further thesis of the paper is
  that everything can be done *deterministically*: "each instruction leads to a
  well-determined next instruction" (p. 205).  We make that determinism a proved
  theorem here (`Step.deterministic`, `Computes.deterministic`).

  Transcribed pieces:
    * Section 1  : instructions (four forms) and Definition 1.1 (a program).
    * Section 2  : Definition 2.1 (a machine), Definition 2.2 (a system of machines).
    * Section 3  : Definition 3.1 (a completed computation), Definition 3.2 (the
                   partial function computed by a program on a machine),
                   Definition 3.3 (equivalence of programs),
                   Definition 3.4 ([effective] reducibility / equivalence of machines).
    * Section 4  : Definition 4.1 (machine with standard input/output), as a shape.
    * Section 5  : Definition 5.1 (decidable), 5.2 (acceptable), 5.3 (generable),
                   and the inclusions decidable ⊆ acceptable ⊆ generable.

  Conventions (Section 2).  Scott writes `f : A → B` for a *partial* function and
  introduces the symbol Ω for "the undefined", with `f(Ω) = Ω`.  We model a partial
  function `A → B` by `A → Option B`, taking `none` for Ω; the equation `f(Ω) = Ω`
  is then `Option.bind`'s behaviour on `none`.  Predicates are partial functions
  into `{T, F}`, modelled as `A → Option Bool` (`T = true`, `F = false`).
-/

namespace Scott1967

variable {Lbl Fn Pr : Type}

/-! ## Section 1.  Instructions and programs.

    "an instruction is a string of one of the following four forms:
        start : go to L
        L : do F; go to L'
        L : if P then go to L' else go to L''
        L : halt
     where L, L', L'' ∈ 𝓛 and F ∈ 𝓕 and P ∈ 𝓟."

    `𝓛 = Lbl` (labels), `𝓕 = Fn` (operation symbols), `𝓟 = Pr` (test symbols). -/
inductive Instruction (Lbl Fn Pr : Type) where
  | startGoto  (target : Lbl)
  | doGoto     (label : Lbl) (f : Fn) (next : Lbl)
  | ifThenElse (label : Lbl) (p : Pr) (thenL elseL : Lbl)
  | halt       (label : Lbl)

/-- Whether an instruction is *the* start instruction. -/
def Instruction.isStart : Instruction Lbl Fn Pr → Prop
  | .startGoto _ => True
  | _            => False

/-- Whether an instruction "begins with" the label `l`.  The start instruction
    begins with no label (it begins with the keyword `start`). -/
def Instruction.beginsWith : Instruction Lbl Fn Pr → Lbl → Prop
  | .startGoto _,        _ => False
  | .doGoto L _ _,       l => L = l
  | .ifThenElse L _ _ _, l => L = l
  | .halt L,             l => L = l

/-- Whether the label `l` occurs anywhere in an instruction. -/
def Instruction.mentions : Instruction Lbl Fn Pr → Lbl → Prop
  | .startGoto t,          l => t = l
  | .doGoto L _ L',        l => L = l ∨ L' = l
  | .ifThenElse L _ L' L'',l => L = l ∨ L' = l ∨ L'' = l
  | .halt L,               l => L = l

/-- **Definition 1.1.**  "A program is a finite set H of instructions containing
    exactly one start instruction and containing for each label that occurs
    anywhere in any instruction in H exactly one instruction that begins with
    that label."

    Faithful transcription: a finite list of instructions (finiteness), with a
    unique start instruction and, for each occurring label, a unique instruction
    beginning with it. -/
def WellFormed (H : List (Instruction Lbl Fn Pr)) : Prop :=
  (∃ i, i ∈ H ∧ i.isStart) ∧
  (∀ i ∈ H, ∀ j ∈ H, i.isStart → j.isStart → i = j) ∧
  (∀ l, (∃ i, i ∈ H ∧ i.mentions l) →
        (∃ i, i ∈ H ∧ i.beginsWith l ∧ ∀ j ∈ H, j.beginsWith l → j = i))

/-! ### Resolved programs (the operational view).

    A well-formed program associates, to each label `L` that begins an
    instruction, exactly one instruction body, and it has a unique start target.
    For the operational semantics of Section 3 we use this resolved form
    directly: `body L` is the (unique) instruction beginning with `L`, and
    `start` is the label named in the start instruction `start : go to start`. -/
inductive Body (Lbl Fn Pr : Type) where
  | op   (f : Fn) (next : Lbl)
  | test (p : Pr) (thenL elseL : Lbl)
  | halt

structure Program (Lbl Fn Pr : Type) where
  start : Lbl                      -- label named in the unique start instruction
  body  : Lbl → Body Lbl Fn Pr     -- the unique instruction beginning with each label

/-! ## Section 2.  Machines.

    **Definition 2.1.**  "A machine is a function 𝔐 defined on the set
    {I} ∪ 𝓕 ∪ 𝓟 ∪ {O} for which there exist sets X (the input set), M (the
    memory set), and Y (the output set) such that
        (i)   𝔐_I : X → M ;
        (ii)  𝔐_F : M → M,        for all F ∈ 𝓕 ;
        (iii) 𝔐_P : M → {T,F},    for all P ∈ 𝓟 ;  and
        (iv)  𝔐_O : M → Y."

    The sets X, M, Y are "uniquely determined by the machine 𝔐"; here they are
    honest fields.  All four are partial functions (Section 2 conventions), so
    their codomains are wrapped in `Option`. -/
structure Machine (Fn Pr : Type) where
  X : Type
  M : Type
  Y : Type
  input  : X → Option M          -- 𝔐_I : X → M
  op     : Fn → M → Option M     -- 𝔐_F : M → M      (for each F ∈ 𝓕)
  test   : Pr → M → Option Bool  -- 𝔐_P : M → {T,F}  (for each P ∈ 𝓟)
  output : M → Option Y          -- 𝔐_O : M → Y

/-- **Definition 2.2.**  "A system of machines is a sequence 𝔐⁽¹⁾, 𝔐⁽²⁾, ... of
    machines for which there exist sets X and Y such that the input set of each
    𝔐⁽ⁿ⁾ is Xⁿ while all the 𝔐⁽ⁿ⁾ have the same output set Y."

    `Xⁿ` is `Fin n → X`; the constraints are recorded as type equalities. -/
structure MachineSystem (Fn Pr : Type) where
  X : Type
  Y : Type
  mach : Nat → Machine Fn Pr
  input_pow   : ∀ n, (mach n).X = (Fin n → X)   -- input set of 𝔐⁽ⁿ⁾ is Xⁿ
  output_same : ∀ n, (mach n).Y = Y             -- all share output set Y

/-! ## Section 3.  Computations.

    A configuration during a computation is a pair `(L, m)` of a current label
    `L` of `H` and a current memory element `m ∈ M`, matching the alternating
    sequence `L₀, m₀, L₁, m₁, ...` of Definition 3.1. -/

/-- One step of a computation, transcribing the two non-terminal clauses of
    **Definition 3.1**:

    * an operation instruction `Lᵢ : do F; go to L'` with `𝔐_F(mᵢ) ≠ Ω`:
      `Lᵢ₊₁ = L'` and `mᵢ₊₁ = 𝔐_F(mᵢ)`;
    * a test instruction `Lᵢ : if P then go to L' else go to L''` with
      `𝔐_P(mᵢ) ≠ Ω`: `mᵢ₊₁ = mᵢ`, and `Lᵢ₊₁ = L'` if `𝔐_P(mᵢ) = T`, else
      `Lᵢ₊₁ = L''` if `𝔐_P(mᵢ) = F`.

    A halt instruction admits no step (the computation is *completed* there). -/
inductive Step (H : Program Lbl Fn Pr) (𝔐 : Machine Fn Pr) :
    (Lbl × 𝔐.M) → (Lbl × 𝔐.M) → Prop where
  | op {L f L' m m'} :
      H.body L = Body.op f L' → 𝔐.op f m = some m' →
      Step H 𝔐 (L, m) (L', m')
  | test_true {L p L' L'' m} :
      H.body L = Body.test p L' L'' → 𝔐.test p m = some true →
      Step H 𝔐 (L, m) (L', m)
  | test_false {L p L' L'' m} :
      H.body L = Body.test p L' L'' → 𝔐.test p m = some false →
      Step H 𝔐 (L, m) (L'', m)

/-- The reflexive/transitive closure of `Step`: `Reaches c c'` holds when there
    is a (possibly empty) run of steps from `c` to `c'`.  A completed computation
    (Definition 3.1) is such a run from a start configuration to a halt one. -/
inductive Reaches (H : Program Lbl Fn Pr) (𝔐 : Machine Fn Pr) :
    (Lbl × 𝔐.M) → (Lbl × 𝔐.M) → Prop where
  | refl (a) : Reaches H 𝔐 a a
  | step {a b c} : Step H 𝔐 a b → Reaches H 𝔐 b c → Reaches H 𝔐 a c

/-- **Definition 3.2.**  "The (partial) function computed by a program H on a
    machine 𝔐 is that function ψ_H : X → Y such that for x ∈ X, ψ_H(x) ≠ Ω if and
    only if there is a computation L₀, m₀, ..., Lₙ, mₙ such that m₀ = 𝔐_I(x) and
    𝔐_O(mₙ) ≠ Ω, in which case ψ_H(x) = 𝔐_O(mₙ)."

    We render `ψ_H(x) = y` as the relation `Computes H 𝔐 x y`.  That it is a
    genuine (partial) function is `Computes.deterministic` below. -/
def Computes (H : Program Lbl Fn Pr) (𝔐 : Machine Fn Pr)
    (x : 𝔐.X) (y : 𝔐.Y) : Prop :=
  ∃ (m0 : 𝔐.M) (Ln : Lbl) (mn : 𝔐.M),
    𝔐.input x = some m0 ∧
    Reaches H 𝔐 (H.start, m0) (Ln, mn) ∧
    H.body Ln = Body.halt ∧
    𝔐.output mn = some y

/-! ### Determinism ("each instruction leads to a well-determined next one").

    Scott stresses (p. 205) that in a deterministic program each instruction
    leads to a well-determined next instruction; "Given a value of m₀, ... the
    rest of the computation sequence is strictly determined" (p. 193).  We prove
    this: `Step` is a partial function, hence `Computes` is too. -/

variable {H : Program Lbl Fn Pr} {𝔐 : Machine Fn Pr}

/-- The step relation is deterministic: at most one successor configuration. -/
theorem Step.deterministic {a b c} (h1 : Step H 𝔐 a b) (h2 : Step H 𝔐 a c) :
    b = c := by
  cases h1 with
  | op hb hop =>
    cases h2 with
    | op hb2 hop2 =>
      rw [hb] at hb2
      injection hb2 with hf hL
      subst hf; subst hL
      rw [hop] at hop2
      injection hop2 with hm
      subst hm; rfl
    | test_true hb2 _  => rw [hb] at hb2; simp at hb2
    | test_false hb2 _ => rw [hb] at hb2; simp at hb2
  | test_true hb ht =>
    cases h2 with
    | op hb2 _ => rw [hb] at hb2; simp at hb2
    | test_true hb2 _ =>
      rw [hb] at hb2
      injection hb2 with hp hL1 hL2
      subst hL1; subst hL2; rfl
    | test_false hb2 hf2 =>
      rw [hb] at hb2
      injection hb2 with hp hL1 hL2
      subst hp; subst hL1; subst hL2
      rw [ht] at hf2
      simp at hf2
  | test_false hb hf =>
    cases h2 with
    | op hb2 _ => rw [hb] at hb2; simp at hb2
    | test_true hb2 ht2 =>
      rw [hb] at hb2
      injection hb2 with hp hL1 hL2
      subst hp; subst hL1; subst hL2
      rw [hf] at ht2
      simp at ht2
    | test_false hb2 _ =>
      rw [hb] at hb2
      injection hb2 with hp hL1 hL2
      subst hL1; subst hL2; rfl

/-- A halt configuration is terminal: no step leaves it. -/
theorem no_step_of_halt {L m c} (h : H.body L = Body.halt) :
    ¬ Step H 𝔐 (L, m) c := by
  intro hs
  cases hs with
  | op hb _         => rw [h] at hb; simp at hb
  | test_true hb _  => rw [h] at hb; simp at hb
  | test_false hb _ => rw [h] at hb; simp at hb

/-- `Reaches` is transitive (composition of runs). -/
theorem Reaches.trans {a b c} :
    Reaches H 𝔐 a b → Reaches H 𝔐 b c → Reaches H 𝔐 a c := by
  intro h1
  induction h1 with
  | refl _ => intro h2; exact h2
  | step hs _ ih => intro h2; exact Reaches.step hs (ih h2)

/-- From a terminal configuration, `Reaches` can only be the empty run. -/
theorem eq_of_reaches_terminal {a c} (hter : ∀ b, ¬ Step H 𝔐 a b)
    (hr : Reaches H 𝔐 a c) : a = c := by
  cases hr with
  | refl _        => rfl
  | step hs _     => exact absurd hs (hter _)

/-- Cofinality of runs in a deterministic system: any two runs from a common
    start are comparable.  (This is the confluence property behind determinism.) -/
theorem reaches_cofinal {a b c} (h1 : Reaches H 𝔐 a b) :
    Reaches H 𝔐 a c → Reaches H 𝔐 b c ∨ Reaches H 𝔐 c b := by
  induction h1 with
  | refl _ => intro h2; exact Or.inl h2
  | step hs hbc ih =>
      intro h2
      cases h2 with
      | refl _ => exact Or.inr (Reaches.step hs hbc)
      | step hs2 hrest =>
          have heq := Step.deterministic hs hs2
          subst heq
          exact ih hrest

/-- **Determinism of Definition 3.2.**  `ψ_H` really is a (partial) function:
    a program on a machine computes at most one output for a given input. -/
theorem Computes.deterministic {x : 𝔐.X} {y1 y2 : 𝔐.Y}
    (h1 : Computes H 𝔐 x y1) (h2 : Computes H 𝔐 x y2) : y1 = y2 := by
  obtain ⟨m0, Ln1, mn1, hin1, hr1, hh1, ho1⟩ := h1
  obtain ⟨m0', Ln2, mn2, hin2, hr2, hh2, ho2⟩ := h2
  rw [hin1] at hin2
  injection hin2 with hm0
  subst hm0
  have hter1 : ∀ b, ¬ Step H 𝔐 (Ln1, mn1) b := fun _ => no_step_of_halt hh1
  have hter2 : ∀ b, ¬ Step H 𝔐 (Ln2, mn2) b := fun _ => no_step_of_halt hh2
  have hmneq : mn1 = mn2 := by
    rcases reaches_cofinal hr1 hr2 with h | h
    · exact congrArg Prod.snd (eq_of_reaches_terminal hter1 h)
    · exact (congrArg Prod.snd (eq_of_reaches_terminal hter2 h)).symm
  subst hmneq
  rw [ho1] at ho2
  exact Option.some.inj ho2

/-! ### Equivalence and reducibility. -/

/-- **Definition 3.3.**  "Two programs H and H' are equivalent if and only if for
    all machines 𝔐, ψ_H = ψ_H'." -/
def ProgEquiv (H H' : Program Lbl Fn Pr) : Prop :=
  ∀ (𝔐 : Machine Fn Pr) (x : 𝔐.X) (y : 𝔐.Y),
    Computes H 𝔐 x y ↔ Computes H' 𝔐 x y

/-- **Definition 3.4.**  "A machine 𝔐 is reducible to a machine 𝔐' if and only if
    corresponding to each program H one can find a program H' such that
    ψ_H = ψ_{H'}."  (Definition 3.4 requires the input and output sets of the two
    machines to be respectively equal; we carry these as `hX`, `hY` and transport
    inputs/outputs along them.  The bracketed "effective" variant is a
    meta-level refinement not modelled here.) -/
def MachineReducible (𝔐 𝔐' : Machine Fn Pr)
    (hX : 𝔐.X = 𝔐'.X) (hY : 𝔐.Y = 𝔐'.Y) : Prop :=
  ∀ (H : Program Lbl Fn Pr), ∃ (H' : Program Lbl Fn Pr),
    ∀ (x : 𝔐.X) (y : 𝔐.Y),
      Computes H 𝔐 x y ↔ Computes H' 𝔐' (hX ▸ x) (hY ▸ y)

/-- Two machines are equivalent when each is reducible to the other. -/
def MachineEquiv (𝔐 𝔐' : Machine Fn Pr)
    (hX : 𝔐.X = 𝔐'.X) (hY : 𝔐.Y = 𝔐'.Y) : Prop :=
  MachineReducible (Lbl := Lbl) 𝔐 𝔐' hX hY ∧
  MachineReducible (Lbl := Lbl) 𝔐' 𝔐 hX.symm hY.symm

/-! ## Section 4.  Machines with standard input/output.

    **Definition 4.1.**  "A machine 𝔐 is a (unary) machine with standard
    input/output if and only if its input/output sets are both Σ* and its memory
    set is of the form M = M₀ × Σ* × Σ*, where, in addition, for some fixed
    m₀ ∈ M₀,  𝔐_I(τ) = (m₀, Λ, τ)  and  𝔐_O((m, σ, τ)) = σ ..."

    We record the *shape* required by Definition 4.1.  Strings over the alphabet
    Σ are `List Σ`; the empty string Λ is `[]`.  (The coordinate-wise restriction
    on the operations/tests — write-only output, read/erase-only input — is noted
    in the paper's prose and not carried in this shape record.) -/
structure StandardIO (Fn Pr : Type) where
  Sigma   : Type
  M0      : Type
  m0      : M0
  machine : Machine Fn Pr
  hX : machine.X = List Sigma                        -- input set is Σ*
  hY : machine.Y = List Sigma                        -- output set is Σ*
  hM : machine.M = (M0 × List Sigma × List Sigma)    -- memory is M₀ × Σ* × Σ*

/-! ## Section 5.  Sets.

    Section 5 singles out three classes of subsets of Σ* by *how a program on the
    machine answers membership*.  Following the paper we let a distinguished
    output value `yA` play the role of "a" (used for `T`, "true"/accepted) and
    `yB` the role of "b" (used for `F`, "false"); "we have used a to stand for T
    (true) and b for F (false)".  Membership of `x` in the subset `S` is `S x`. -/

/-- **Definition 5.1.**  "A subset S ⊆ Σ* is called decidable on 𝔐 if and only if
    there is a program H such that for all τ ∈ Σ*:  ψ_H(τ) = a if τ ∈ S, and
    ψ_H(τ) = b if τ ∉ S." -/
def DecidableSet (𝔐 : Machine Fn Pr) (S : 𝔐.X → Prop) (yA yB : 𝔐.Y) : Prop :=
  ∃ H : Program Lbl Fn Pr, ∀ x : 𝔐.X,
    (S x → Computes H 𝔐 x yA) ∧ (¬ S x → Computes H 𝔐 x yB)

/-- **Definition 5.2.**  "A subset S ⊆ Σ* is called acceptable on 𝔐 if and only if
    there is a program H such that for all τ ∈ Σ*:  ψ_H(τ) = a if and only if
    τ ∈ S." -/
def AcceptableSet (𝔐 : Machine Fn Pr) (S : 𝔐.X → Prop) (yA : 𝔐.Y) : Prop :=
  ∃ H : Program Lbl Fn Pr, ∀ x : 𝔐.X,
    (Computes H 𝔐 x yA ↔ S x)

/-- **Definition 5.3.**  "A subset S ⊆ Σ* is called generable on 𝔐 if and only if
    there is a program H and an integer n > 0 such that for all τ ∈ Σ*:
    ψ⁽ⁿ⁾_H(τ, ξ₁, ..., ξₙ₋₁) = a for some ξ₁, ..., ξₙ₋₁ ∈ Σ* if and only if τ ∈ S."

    `ψ⁽ⁿ⁾_H` is the function computed by `H` on the n-ary member `𝔐⁽ⁿ⁾` of the
    system of machines (Definition 2.2).  We take that n-ary computation relation
    `psi H n τ ξs y` as a parameter, with `ξs` the list `ξ₁,...,ξₙ₋₁` of the
    `n-1` auxiliary inputs (so `ξs.length = n - 1`). -/
def GenerableSet (𝔐 : Machine Fn Pr)
    (psi : Program Lbl Fn Pr → Nat → 𝔐.X → List 𝔐.X → 𝔐.Y → Prop)
    (S : 𝔐.X → Prop) (yA : 𝔐.Y) : Prop :=
  ∃ (H : Program Lbl Fn Pr) (n : Nat), 0 < n ∧
    ∀ x : 𝔐.X,
      (∃ ξs : List 𝔐.X, ξs.length = n - 1 ∧ psi H n x ξs yA) ↔ S x

/-- "Clearly every decidable set is acceptable" (p. 204).  The witnessing program
    for decidability already witnesses acceptability, using `yA ≠ yB` and the fact
    (Definition 3.2 / `Computes.deterministic`) that `ψ_H` is a partial function. -/
theorem acceptable_of_decidable {𝔐 : Machine Fn Pr} {S : 𝔐.X → Prop} {yA yB : 𝔐.Y}
    (hne : yA ≠ yB) (h : DecidableSet (Lbl := Lbl) 𝔐 S yA yB) :
    AcceptableSet (Lbl := Lbl) 𝔐 S yA := by
  obtain ⟨H, hH⟩ := h
  refine ⟨H, fun x => ⟨fun hc => ?_, fun hs => (hH x).1 hs⟩⟩
  rcases Classical.em (S x) with hs | hns
  · exact hs
  · exact absurd (Computes.deterministic hc ((hH x).2 hns)) hne

/-- "and every acceptable set is generable (because n = 1 is allowed in
    Definition 5.3)" (p. 204).  With `n = 1` there are no auxiliary inputs, and
    the n-ary member `𝔐⁽¹⁾` of the system coincides with the base machine; we
    record that coincidence as the compatibility hypothesis `hcompat`. -/
theorem generable_of_acceptable {𝔐 : Machine Fn Pr}
    (psi : Program Lbl Fn Pr → Nat → 𝔐.X → List 𝔐.X → 𝔐.Y → Prop)
    (hcompat : ∀ (H : Program Lbl Fn Pr) (x : 𝔐.X) (y : 𝔐.Y),
        psi H 1 x [] y ↔ Computes H 𝔐 x y)
    {S : 𝔐.X → Prop} {yA : 𝔐.Y}
    (h : AcceptableSet (Lbl := Lbl) 𝔐 S yA) :
    GenerableSet 𝔐 psi S yA := by
  obtain ⟨H, hH⟩ := h
  refine ⟨H, 1, Nat.one_pos, fun x => ?_⟩
  constructor
  · rintro ⟨ξs, hlen, hpsi⟩
    cases ξs with
    | nil =>
        have hc := (hcompat H x yA).1 hpsi
        exact (hH x).1 hc
    | cons a as => simp at hlen
  · intro hs
    refine ⟨[], rfl, ?_⟩
    exact (hcompat H x yA).2 ((hH x).2 hs)

end Scott1967
