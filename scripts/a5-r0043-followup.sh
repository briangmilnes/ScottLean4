#!/usr/bin/env bash
# a5-r0043-followup.sh — the second battery of r0043's §7 re-measurement.
#
# Why this exists: the first battery (a5-r0043-greps.sh) reproduces r0040's three
# greps per row so the two measurements are comparable. This one adds the probes
# that r0041's new modules make worth running — a symmetric form of the row-3 iso
# grep (r0040 searched only `Set ℕ ≃o`, which misses `… ≃o Set ℕ`), the full list
# of solvability statements in the package, and the operator-action surface of
# `Morphism`/`PowerdomainMap` that the plan asks be checked for the constant
# operator and for composition. Read-only over the sources.
#
# Usage: a5-r0043-followup.sh <out-file>
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

# row 3, symmetric: r0040's grep was `Set ℕ ≃o` only
probe "R3 sym iso"            "≃o Set ℕ"
probe "R3 I-top"              "I⊤\|Itop\|topOf\|WithTop PUnit"

# row 1 / row 23: the complete list of solvability statements
probe "SOLV theorem-lines"    "IsSolvable\.\|: IsSolvable\|IsSolvable\.{"
probe "SOLV recursiveDomain"  "recursiveDomain"

# row 23: is the equation X ≅ N⊥ + (X → X) anywhere, as an operator?
probe "R23 operator"          "sepSum.*funSpace\|funSpace.*sepSum"
probe "R23 NatBot-rep"        "NatBot.*[Rr]epresentable\|[Rr]epresentable.*NatBot"
probe "R23 flat-rep"          "Flat.*IsRepresentable\|IsRepresentable.*Flat"

# row 2 / row 7: the operator-action surface the plan names
probe "OPS PowerdomainMap"    "def .*\(sharp\|flat\|natural\|smythMap\|hoareMap\|plotkinMap\)"
probe "OPS const"             "def const\|constHom\|Cpo.const"
probe "OPS opComp"            "opComp\|compOp\|IsRepresentable₂.comp"

# the two P rows
probe "P26 refutation"        "Theorem 26 is \|not Lean-checked\|is \*\*false\*\*"
probe "P26 decl"              "thm26.*false\|false.*thm26"

wc -l "$out"
