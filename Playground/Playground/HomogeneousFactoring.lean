import Mathlib.Tactic

/-!
# Factoring homogeneous polynomials in Lean 4

A *homogeneous* polynomial (a "form") has every term of the same total degree.
In two variables, `x^2 - y^2` (degree 2) and `x^3 - y^3` (degree 3) are forms.

Lean has no `Factor` command that *discovers* a factorization (unlike a computer
algebra system). Instead you *state* the factored identity and let the `ring`
tactic *verify* it. `ring` is a decision procedure for commutative-ring
equalities: it normalizes both sides to a canonical polynomial form and checks
they are identical. So "factoring" in Lean is: **propose the factors, then
`ring` confirms**.
-/

variable {R : Type*} [CommRing R] (x y z : R)

/-! ## Verifying factorizations with `ring` -/

-- Degree-2 form: a difference of squares splits into two linear forms.
example : x^2 - y^2 = (x - y) * (x + y) := by ring

-- Degree-2 form: a perfect-square trinomial.
example : x^2 + 2*x*y + y^2 = (x + y)^2 := by ring

-- Degree-3 forms.
example : x^3 - y^3 = (x - y) * (x^2 + x*y + y^2) := by ring
example : x^3 + y^3 = (x + y) * (x^2 - x*y + y^2) := by ring

-- A genuinely *ternary* quadratic form (degree 2 in x, y, z) that factors:
-- into the linear forms `x` and `y - z` — the two lines x = 0 and y = z.
example : x*y - x*z = x * (y - z) := by ring

/-! ## Factoring as *divisibility*

"(x - y) is a factor of x^2 - y^2" means `(x - y) ∣ (x^2 - y^2)`.
The divisibility witness *is* the cofactor, and `ring` proves the equation.
Here the whole proof is a term: an anonymous constructor `⟨cofactor, proof⟩`.
-/

example : (x - y) ∣ (x^2 - y^2) := ⟨x + y, by ring⟩
example : (x + y) ∣ (x^2 - y^2) := ⟨x - y, by ring⟩

/-! ## Expanding a proposed product with `ring_nf`

`ring` proves a stated equality; `ring_nf` *normalizes* (multiplies out) an
expression, so you can watch a product expand back into the form. Put the cursor
after this line and read the Infoview to see the normalized right-hand side.
-/

example : (x - y) * (x + y) = x^2 - y^2 := by ring_nf

/-! ## Projective-geometry note

A binary quadratic form factoring into two *linear* forms is a **degenerate
conic** — a pair of lines. `x^2 - y^2 = (x - y)(x + y)` is the pair `x = y`
and `x = -y`. Non-degenerate conics correspond to *irreducible* forms. The
formal objects live in Mathlib as `MvPolynomial` with `MvPolynomial.IsHomogeneous`,
where irreducibility and factorization become theorems rather than `ring`
identities.
-/
