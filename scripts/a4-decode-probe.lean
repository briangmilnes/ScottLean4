/-
r0049 / agent4 — evidence that the `Denumerable (Finset _)` decoding is a program.

Run with:  scripts/a3-run-lean.sh a4-decode-probe

Why this file exists, and why the checks are `#eval` rather than `by decide`.
r0045's `Effective/A1FlatRecursive.lean` closes its "the procedures run" checks
with `decide`, which is the strong form of the evidence: the *kernel* reduces the
decision procedure, so it cannot be a `Classical.dec`. That form is unavailable
for any `Denumerable` decoding in Mathlib v4.32.2, and the obstruction is one
declaration deep — the last `example` below fails:

    example : Nat.sqrt 5 = 2 := by decide
    -- Tactic `decide` failed … reduction got stuck at `(Nat.sqrt 5).beq 2`

`Nat.sqrt` is compiled by well-founded recursion, `Nat.unpair` calls it, and every
`Denumerable` decoding of a pair, a list or a `Finset` goes through `Nat.unpair`.
So the compiled evaluator runs these and the kernel does not; the `Primrec` facts
in `Effective/A4Recursion.lean` are the kernel-checked content, and this file is
evidence of the weaker, executable kind.

Expected output:
  [0, 1, 2]
  [(0, 0), (0, 1), (1, 0)]
  [(0, []), (1, [(0, 0)]), (2, [(0, 0), (0, 1)]), (3, [(0, 1)]), …]
-/
import ScottDomains.Effective.A4Recursion

open ScottDomains.R49.Agent4

-- The decoded index list of the 5th finite set of naturals.
#eval idxList 5

-- The same coding at `ℕ × ℕ` — the one the step-function enumeration runs over.
#eval decodeList (ℕ × ℕ) 5

-- The first thirty finite sets of index pairs, decoded.
#eval (List.range 30).map fun n => (n, decodeList (ℕ × ℕ) n)

-- The membership test the `Primrec` facts are about, run.
#eval (List.range 8).map fun x => (x, decide (x ∈ idxList 5))
