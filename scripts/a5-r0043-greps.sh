#!/usr/bin/env bash
# a5-r0043-greps.sh — re-run r0040's §7 concept greps against the tree as it
# stands after r0041 and r0042, so each of the 13 `N` rows is re-labelled from a
# fresh measurement rather than from the r0040 transcript.
#
# Why this exists: r0043 re-measures, and a row may stay `N` only after three
# greps that are reported. The three greps per row are the SAME three r0040 ran
# (so the two measurements are comparable), plus, for the rows the plan flags as
# possibly moved, extra probes aimed at the r0041 modules (Flat, Morphism,
# PowerdomainMap). The project forbids chaining shell commands; this runs the
# whole battery in one allowlisted invocation and writes a labelled transcript.
#
# Usage: a5-r0043-greps.sh <out-file>
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
src="$root/ScottDomains/ScottDomains"
out="$1"
mkdir -p "$(dirname "$out")"

probe () {
  echo "=== $1 :: $2 ===" >> "$out"
  grep -rn -- "$2" "$src" --include=*.lean >> "$out" 2>/dev/null || echo "(no match)" >> "$out"
}

: > "$out"

# ---- row 1: the full simple binary tree is a solution of T ≅ T + T
probe "R1 g1 solvable"        "IsSolvable\|Solves "
probe "R1 g2 solvable-sum"    "IsSolvable.*sepSum"
probe "R1 g3 binaryTree"      "binaryTree"

# ---- row 2: a composition of representable operators is representable
probe "R2 g1"                 "IsRepresentable.comp"
probe "R2 g2"                 "isRepresentable_comp"
probe "R2 g3"                 "[Rr]epresentable.*compos"
probe "R2 x1 Morphism-comp"   "Morphism.*comp\|comp.*Morphism"

# ---- row 3: X ≅ X × I⊤ has (I⊤)^N as a solution, and (I⊤)^N ≅ P N
probe "R3 g1 twoPoint"        "twoPoint\|TwoPoint\|Sierpinski"
probe "R3 g2 iso-powerset"    "Set ℕ ≃o"
probe "R3 g3 Prop-power"      "ℕ → Prop"

# ---- row 7: the constant operator X ↦ L is representable over P N
probe "R7 g1 constOp"         "constOp"
probe "R7 g2 rep-const"       "isRepresentable_const"
probe "R7 g3 prose"           "constant operator"
probe "R7 x1 const-anything"  "[Cc]onstOp\|constFun\|const_rep\|repConst"

# ---- row 11: lambda equation 1, alpha
probe "R11 g1 conv-names"     "alpha\|beta_\|eta_conv\|_beta\|_eta\b"
probe "R11 g2 term-syntax"    "LamTerm\|inductive Term"
probe "R11 g3 subst"          "subst"

# ---- row 13: lambda equation 3, eta
probe "R13 g1 lam_app"        "lam_app"
probe "R13 g2 eta_law"        "eta_law"
probe "R13 g3 _eta"           "_eta\b"

# ---- row 16: lambda equation 6, surjective pairing
probe "R16 g1 pair_fst_snd"   "pair_fst_snd"
probe "R16 g2 prose"          "surjective pairing"
probe "R16 g3 lam_app"        "lam_app"

# ---- row 17: equations 3 and 6 are independent of the other four
probe "R17 g1 independen"     "independen"
probe "R17 g2 pointwise"      "pointwise pair"
probe "R17 g3 LambdaModel"    "LambdaModel"

# ---- row 18: the pointwise pairing equation is independent, and has a model
probe "R18 g1 pointwise"      "pointwise pair"
probe "R18 g2 independen"     "independen"
probe "R18 g3 LambdaModel"    "LambdaModel"

# ---- row 19: (· + ·)⊤ is representable over P N
probe "R19 g1 WithTop"        "WithTop"
probe "R19 g2 sumTop"         "sumTop\|topSum"
probe "R19 g3 prose"          "unmotivated\|gets in the way"

# ---- row 20: B = U₀ ∪ {∅} is a countable atomless Boolean algebra
probe "R20 g1 BooleanAlgebra" "[Bb]ooleanAlgebra"
probe "R20 g2 IsAtomless"     "IsAtomless"
probe "R20 g3 Vaught"         "Vaught"

# ---- row 21: i : x ↦ ↑x is a monotone injection preserving existing lubs
probe "R21 g1 upperClosure"   "upperClosure"
probe "R21 g2 Ici"            "Ici"
probe "R21 g3 principal"      "principalFilter"

# ---- row 23: X ≅ N⊥ + (X → X) has a solution, represented over U
probe "R23 g1 Nbot"           "N⊥"
probe "R23 g2 WithBot"        "WithBot ℕ"
probe "R23 g3 lazynat"        "LazyNat\|natOp\|NatBot"
probe "R23 x1 Flat-nat"       "Flat ℕ"
probe "R23 x2 morphism-sum"   "Morphism.*sepSum\|sepSum.*Morphism\|morphSepSum"
probe "R23 x3 solves-flat"    "Solves.*Flat\|IsSolvable.*Flat"

# ---- P rows the plan asks about: Thm 26 arity 0, Thm29Second falsity
probe "P-thm26 arity0"        "arity 0\|arity zero\|thm26_false\|thm26_arity\|nullary"
probe "P-thm29 false"         "Thm29Second.*false\|thm29Second_false\|not_thm29Second\|uncountable.*flat"

# ---- new-module declaration surfaces the plan names
probe "NEW Flat decls"        "^\(def\|theorem\|lemma\|instance\|structure\|abbrev\) *[A-Za-z]*[Ff]lat"
probe "NEW natural-op"        "♮\|plotkinOp"

wc -l "$out"
