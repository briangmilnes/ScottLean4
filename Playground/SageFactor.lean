import Mathlib.Tactic

/-!
# Factoring ℚ[x,y,z] homogeneous forms: Sage discovers, `ring` certifies

Two halves, and the distinction is the whole point.

* `sageFactor` shells out to the `sage` executable (`IO.Process.output`) and
  prints Sage's factorization. `#eval` runs it. This is **uncertified** — you are
  trusting Sage's answer, not a Lean proof. Requires `sage` on PATH
  (`brew install --cask sage`).
* The `example`s below take those very factors and let the **kernel** check the
  identity `f = g * h` with `ring`. *That* is the certified factorization.

Standalone scratch — NOT imported into the Playground library (the `#eval`s error
until Sage is installed, and this file is only meaningful when run directly:
`lake env lean SageFactor.lean`).
-/

/-! ## Uncertified: ask Sage to factor (an `IO` action `#eval` can run) -/

/-- Ask Sage to factor `poly` over ℚ[x,y,z]; returns Sage's printed factorization.
Uncertified: this is Sage's word, not a Lean proof. -/
def sageFactor (poly : String) : IO String := do
  let out ← IO.Process.output {
    cmd := "sage"
    args := #["-c", s!"R.<x,y,z> = QQ[]; print(factor({poly}))"]
  }
  if out.exitCode != 0 then
    throw <| IO.userError s!"sage exited {out.exitCode}: {out.stderr}"
  return out.stdout

-- A homogeneous cubic form -> Sage returns a (homogeneous) linear x quadratic split.
#eval do IO.println (← sageFactor "x^3 + y^3 + z^3 - 3*x*y*z")
-- (x + y + z) * (x^2 - x*y + y^2 - x*z - y*z + z^2)

#eval do IO.println (← sageFactor "x^3 - y^3")
-- (x - y) * (x^2 + x*y + y^2)

/-! ## Certified: hand those factors to `ring` — the kernel checks the identity -/

-- Homogeneous cubic (deg 3) = linear (deg 1) x quadratic (deg 2): homogeneity preserved.
example (x y z : ℚ) :
    x^3 + y^3 + z^3 - 3*x*y*z
      = (x + y + z) * (x^2 - x*y - x*z + y^2 - y*z + z^2) := by ring

example (x y : ℚ) :
    x^3 - y^3 = (x - y) * (x^2 + x*y + y^2) := by ring

-- A homogeneous quartic (deg 4) in three variables: deg-2 x deg-2, homogeneity preserved.
example (x y z : ℚ) :
    x^4 - y^4 + x^2*z^2 - y^2*z^2 = (x^2 - y^2) * (x^2 + y^2 + z^2) := by ring

-- ...and fully: two linear (deg 1) forms times a quadratic (deg 2) form.
example (x y z : ℚ) :
    x^4 - y^4 + x^2*z^2 - y^2*z^2 = (x - y) * (x + y) * (x^2 + y^2 + z^2) := by ring
