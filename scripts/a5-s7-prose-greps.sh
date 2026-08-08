#!/usr/bin/env bash
# a5-s7-prose-greps.sh — run the concept greps that r0040's §7 coverage audit
# needs before it may label a paper property "not stated".
#
# Why this exists: the round's rule is that an `N` label carries a burden of
# proof — the concept must be searched for under at least three names, and the
# three must be reported. That is one grep per name over the whole development,
# a dozen or so per property, and the project forbids chaining shell commands.
# This runs the whole battery in one allowlisted invocation and writes a labelled
# transcript the report can quote.
#
# Usage: a5-s7-prose-greps.sh <out-file>
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
src="$root/ScottDomains/ScottDomains"
out="$1"
mkdir -p "$(dirname "$out")"

probe () {
  echo "=== $1 ===" >> "$out"
  grep -rn -- "$2" "$src" --include=*.lean >> "$out" 2>/dev/null || echo "(no match)" >> "$out"
}

: > "$out"

# P1  full simple binary tree solving T ≅ T + T
probe "P1 sumOp-solvable"        "IsSolvable.*sepSum"
probe "P1 solves-sum"            "Solves.*[Ss]um"
probe "P1 binaryTree"            "binaryTree"

# P2  a composition of representable operators is representable
probe "P2 IsRepresentable.comp"  "IsRepresentable.comp"
probe "P2 isRepresentable_comp"  "isRepresentable_comp"
probe "P2 rep.*comp"             "[Rr]epresentable.*compos"

# P3  X ≅ X × I⊤ has (I⊤)^N as a solution; (I⊤)^N ≅ P N
probe "P3 Prop-power"            "Prop *→ *Prop\|Bool)ᴺ\|ℕ → Prop"
probe "P3 iso-powerset"          "Set ℕ ≃o"
probe "P3 twoPoint"              "twoPoint\|TwoPoint\|Sierpinski"

# P6  constant operator X ↦ L representable over P N
probe "P6 constOp"               "constOp"
probe "P6 isRepresentable_const" "isRepresentable_const"
probe "P6 constant operator"     "constant operator"

# P7  X ↦ D representable over U iff D is a closure of U
probe "P7 iff-closure"           "IsRepresentable.*↔\|↔.*IsClosureOf"
probe "P7 representable_iff"     "representable_iff"

# P8  I ≅ I → I, the trivial solution
probe "P8 PUnit-funSpace"        "PUnit"
probe "P8 Unit"                  "Unit ≃o\|trivial cpo"

# P9  the six lambda-calculus equations
probe "P9 alpha/beta/eta"        "alpha\|beta_\|eta_conv\|_beta\|_eta\b"
probe "P9 LambdaModel"           "LambdaModel"
probe "P9 fst_pair/snd_pair"     "fst_pair\|snd_pair\|pair_fst_snd"

# P10 equations 3 and 6 independent of the others
probe "P10 independent"          "independen"

# P11 pointwise pairing equation
probe "P11 pointwise pairing"    "pointwise pair"

# P14 (·+·)⊤ representable over P N
probe "P14 withTop-sum"          "WithTop"
probe "P14 sum-top"              "sumTop\|topSum\|( +  )⊤"

# P17 X ≅ N⊥ + (X → X) has a solution
probe "P17 flat naturals"        "WithBot ℕ\|flat\b"
probe "P17 lazy nat"             "LazyNat\|natOp\|NatBot"

# P18 (·)♮ cannot be representable over U
probe "P18 not-bc"               "does not preserve bounded\|not bounded complete"
probe "P18 plotkin-U"            "plotkinOp.*U\|Plotkin.*Dyadic"
probe "P18 convex-not"           "convex powerdomain cannot\|cannot be representable"

# P19 element counts of I⁺⁺ and I⁺⁺⁺
probe "P19 twenty"               "20 elements\|twenty"
probe "P19 five"                 "five elements\|5 elements"
probe "P19 card"                 "Fintype.card.*Stg\|card_Stg"

# P20 the R♮ recipe
probe "P20 repPlotkin"           "repPlotkin\|rep_plotkin"
probe "P20 plotkinFamily"        "plotkinFamily"

wc -l "$out"
