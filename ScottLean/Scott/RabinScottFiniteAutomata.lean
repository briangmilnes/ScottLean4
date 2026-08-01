/-
  Rabin-Scott Finite Automata (Lean 4 formalization, pilot)

  Faithful to:
    M. O. Rabin and D. Scott, "Finite Automata and Their Decision Problems",
    IBM Journal of Research and Development 3(2):114-125, 1959.
    (1976 ACM Turing Award paper; introduces nondeterministic finite automata.)

  Source text extracted from:
    DanaScottPapers/Rabin-Scott-1959-Finite-Automata-and-Their-Decision-Problems.pdf

  This file transcribes the core objects of Sections 1 and 5:
    * Definition 1  : a (finite, deterministic) automaton A = (S, M, s0, F),
                      and the recursive extension of the move function M to tapes.
    * Definition 2  : the set of tapes T(A) accepted by A.
    * Definition 9  : a nondeterministic automaton A = (S, M, S0, F).
    * Definition 10 : the set of tapes accepted by a nondeterministic automaton.
    * Definition 11 : the "subset construction" D(A), an ordinary automaton.
    * Theorem 11    : T(A) = T(D(A)).

  Core Lean 4 only; no Mathlib.  A "tape" over the alphabet is `List Sigma`,
  matching Scott's tapes as finite sequences of symbols (empty tape = `[]`).
-/

namespace RabinScott

/-! ## Definition 1. Deterministic finite automaton

    "A (finite) automaton over the alphabet Sigma is a system A = (S, M, s0, F),
     where S is a finite non-empty set (the internal states), M is a function
     defined on S x Sigma with values in S (the table of transitions), s0 is an
     element of S (the initial state), and F is a subset of S (the designated
     final states)."

    We take `S` and `Sigma` as arbitrary types.  `F` is represented by its
    characteristic predicate `S -> Prop`. -/
structure DFA (S Sigma : Type) where
  M  : S → Sigma → S      -- table of transitions (the "moves")
  s0 : S                  -- initial state
  F  : S → Prop           -- designated final states

/-- The move function `M` extended from `S x Sigma` to `S x T` by the recursion
    of Definition 1:
        M(s, [])      = s
        M(s, x ++ [u]) = M(M(s, x), u).
    Reading a tape left-to-right, symbol by symbol.  We fold over the tape. -/
def DFA.run {S Sigma : Type} (A : DFA S Sigma) (s : S) : List Sigma → S
  | []      => s
  | u :: xs => A.run (A.M s u) xs

/-- `Mext A x = M(s0, x)`: the state reached from the initial state on tape `x`. -/
def DFA.Mext {S Sigma : Type} (A : DFA S Sigma) (x : List Sigma) : S :=
  A.run A.s0 x

/-- The useful property noted right after Definition 1:
        M(s, x ++ y) = M(M(s, x), y). -/
theorem DFA.run_append {S Sigma : Type} (A : DFA S Sigma) (s : S) :
    ∀ (x y : List Sigma), A.run s (x ++ y) = A.run (A.run s x) y := by
  intro x
  induction x generalizing s with
  | nil => intro y; rfl
  | cons u xs ih =>
      intro y
      simp only [List.cons_append, DFA.run]
      exact ih (A.M s u) y

/-! ## Definition 2. The set of tapes accepted by a DFA

    "The set of tapes accepted or defined by the automaton A, in symbols T(A),
     is the collection of tapes x with M(s0, x) in F." -/
def DFA.accepts {S Sigma : Type} (A : DFA S Sigma) (x : List Sigma) : Prop :=
  A.F (A.Mext x)

/-- `T(A)`, the definable set, as a predicate on tapes. -/
def DFA.language {S Sigma : Type} (A : DFA S Sigma) : List Sigma → Prop :=
  A.accepts

/-! ## Definition 9. Nondeterministic finite automaton

    "A nondeterministic (finite) automaton over Sigma is a system
     A = (S, M, S0, F) where S is a finite set, M is a function of S x Sigma
     with values in the set of all subsets of S, and S0 and F are subsets of S."

    Subsets of `S` are represented by predicates `S -> Prop`. -/
structure NFA (S Sigma : Type) where
  M  : S → Sigma → S → Prop   -- M s u s' : s' is a possible successor of s on u
  S0 : S → Prop               -- set of initial states
  F  : S → Prop               -- designated final states

/-! ## Definition 10. Acceptance by a nondeterministic automaton

    "The set T(A) of tapes accepted by A is the collection of all tapes
     x = u0 u1 ... u_{n-1} for which there exists a sequence s0, s1, ..., sn of
     internal states such that
        (i)   s0 is in S0;
        (ii)  s_i is in M(s_{i-1}, u_{i-1})   for i = 1,...,n;
        (iii) s_n is in F."

    We express the existence of such a run by folding the transition relation
    over the tape: `runNFA A cur x` is the set of states reachable after reading
    `x`, where `cur` is the set (predicate) of currently-possible states. -/
def NFA.runNFA {S Sigma : Type} (A : NFA S Sigma) :
    (S → Prop) → List Sigma → (S → Prop)
  | cur, []      => cur
  | cur, u :: xs =>
      A.runNFA (fun s' => ∃ s, cur s ∧ A.M s u s') xs

/-- Definition 10 acceptance: some final state is reachable from `S0` on `x`. -/
def NFA.accepts {S Sigma : Type} (A : NFA S Sigma) (x : List Sigma) : Prop :=
  ∃ s, A.runNFA A.S0 x s ∧ A.F s

/-! ## Definition 11. The subset construction D(A)

    "Let A = (S, M, S0, F) be a nondeterministic automaton.  D(A) is the system
     (T, N, t0, G) where T is the set of all subsets of S, N is a function on
     T x Sigma such that N(t, u) is the union of the sets M(s, u) for s in t,
     t0 = S0, and G is the set of all subsets of S containing at least one
     member of F."

    States of `D(A)` are subsets of `S`, i.e. `S -> Prop`.  This is an ordinary
    (deterministic) automaton over the same alphabet. -/
def NFA.determinize {S Sigma : Type} (A : NFA S Sigma) : DFA (S → Prop) Sigma where
  -- N(t, u) = { s' | exists s, t s and M s u s' }
  M  := fun t u => fun s' => ∃ s, t s ∧ A.M s u s'
  -- t0 = S0
  s0 := A.S0
  -- G = { t | exists s, t s and F s }
  F  := fun t => ∃ s, t s ∧ A.F s

/-- The determinized automaton's `run` from a subset `t` reproduces `runNFA`.
    (Both are the same left fold of the "union of successors" step.) -/
theorem NFA.run_determinize {S Sigma : Type} (A : NFA S Sigma) :
    ∀ (x : List Sigma) (t : S → Prop),
      (A.determinize).run t x = A.runNFA t x := by
  intro x
  induction x with
  | nil => intro t; rfl
  | cons u xs ih => intro t; simpa [DFA.run, NFA.runNFA, NFA.determinize] using ih _

/-! ## Theorem 11.  T(A) = T(D(A)).

    "If A is a nondeterministic automaton, then T(A) = T(D(A))."

    With acceptance defined as above this is now a definitional consequence of
    `run_determinize`: the accepting set of `D(A)` (a state-subset containing a
    member of `F`, reached from `S0`) coincides with `NFA.accepts`. -/
theorem NFA.subset_construction_correct {S Sigma : Type} (A : NFA S Sigma)
    (x : List Sigma) :
    (A.determinize).accepts x ↔ A.accepts x := by
  unfold DFA.accepts DFA.Mext NFA.accepts
  rw [NFA.run_determinize]
  rfl

end RabinScott
