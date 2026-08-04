import Mathlib.Tactic
open Lean Elab Command Parser

/-!
# `sage_factor`: Sage discovers, `ring` certifies — coupled in one command

The earlier `SageFactor.lean` ran Sage at `#eval` time and then made you *hand-copy*
the factors into a separate `example … := by ring`. This closes that gap.

`sage_factor name : "poly"` is a **command elaborator**. At *compile time* it:

1. shells out to `sage` to factor `poly` over ℚ[x,y,z]      — uncertified (Sage's word),
2. prints the factorization,                                 — for the reader,
3. parses Sage's stdout as a Lean term (the surface syntaxes coincide), and
4. declares `theorem name (x y z : ℚ) : poly = <sage-output> := by ring`
   so the **kernel** checks the identity.                    — certified.

Steps 1–2 are the uncertified oracle; step 4 is the certificate. They are now one
command, so the factors that get proved are exactly the factors Sage produced —
there is no hand transcription to get wrong.

Run standalone (needs `sage` on PATH):  `lake env lean SageFactorProved.lean`
-/

/- The polynomial variables the theorems range over. The externally-parsed
identifiers coming back from Sage resolve against *these* (file-scope) binders,
which sidesteps the macro-hygiene mismatch you'd hit by introducing binders
inside the quotation. Only the variables a given form actually mentions are
bound in its theorem. -/
variable (x y z : ℚ)

/-- `sage_factor name : "poly"` — see the module docstring. Emits a real
`theorem name` whose proof is `ring` over the factors Sage returns. -/
elab "sage_factor " name:ident " : " poly:str : command => do
  let polyStr := poly.getString
  -- (1) uncertified: ask Sage
  let out ← IO.Process.output {
    cmd := "sage"
    args := #["-c", s!"R.<x,y,z> = QQ[]; print(factor({polyStr}))"]
  }
  if out.exitCode != 0 then
    throwError "sage exited {out.exitCode}: {out.stderr}"
  let factored := out.stdout.replace "\n" ""   -- Sage prints one line + newline
  -- (2) print it
  logInfo m!"Sage (uncertified):  {polyStr}  =  {factored}"
  -- (3) parse both sides as Lean terms (Sage/Lean surface syntaxes coincide here)
  let env ← getEnv
  let lhs : TSyntax `term ← match runParserCategory env `term polyStr with
    | .ok s => pure ⟨s⟩
    | .error e => throwError "cannot parse the polynomial as a Lean term: {e}"
  let rhs : TSyntax `term ← match runParserCategory env `term factored with
    | .ok s => pure ⟨s⟩
    | .error e => throwError "cannot parse Sage's output as a Lean term: {e}"
  -- (4) certified: declare the theorem and let `ring` (hence the kernel) check it.
  -- autoImplicit off: a scope mismatch now errors loudly instead of silently
  -- auto-binding a fresh `ℕ` variable and proving the wrong theorem.
  elabCommand (← `(command|
    set_option autoImplicit false in
    theorem $name : $lhs = $rhs := by ring))

/-! ## Use it. Each line proves a theorem; no factors are typed by hand. -/

sage_factor cube_diff       : "x^3 - y^3"
#check @cube_diff
#print axioms cube_diff       -- shows exactly which axioms the kernel used

sage_factor fermat3         : "x^3 + y^3 + z^3 - 3*x*y*z"
#check @fermat3

sage_factor quartic         : "x^4 - y^4 + x^2*z^2 - y^2*z^2"
#check @quartic

-- The theorems are ordinary Lean facts. `cube_diff` mentions only x,y, so its
-- signature is `∀ (x y : ℚ), …` — use it like any lemma.
example (a b : ℚ) : a^3 - b^3 = (a - b) * (a^2 + a*b + b^2) := cube_diff a b
