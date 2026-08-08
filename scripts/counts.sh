#!/bin/zsh
# counts.sh — the development's size metrics, in one place so that every report
# and every inventory update measures the same way.
#
# Usage: scripts/counts.sh
#
# Emits modules, lines, theorem-ish declarations, and open `sorry`s. "Theorem-ish"
# is a line starting with `theorem` or `lemma`, optionally preceded by one
# attribute group — the rule `docs/PaperInventory.md` row 5 cites.
set -e
cd "${0:A:h}/.."
pkg="ScottDomains/ScottDomains"

# Note: `modules`, `lines` and several other plain names are read-only specials
# in zsh once zsh/parameter is loaded, so every local here is prefixed.
srcfiles=(${(f)"$(find $pkg -name '*.lean' | sort)"})
n_modules=$#srcfiles
n_lines=$(cat $srcfiles | wc -l | tr -d ' ')
# Counted by scripts/lean-decls.py, not by grep. The grep rule this replaced
# counted declarations inside `/- … -/` block comments and docstring prose lines
# beginning "theorem"/"lemma", and missed `protected theorem` — three defects
# found independently by five agents in r0038's audit, netting an over-count of
# 10. See that script's header; it is a lexer, not a parser, so a load-bearing
# number should still come from the Lean environment.
n_decls=$(python3 "${0:A:h}/lean-decls.py" --count $srcfiles)
n_files_with_sorry=$(grep -lE '^\s*sorry\s*$' $srcfiles 2>/dev/null | wc -l | tr -d ' ')
n_sorry=$(grep -hE '^\s*sorry\s*$' $srcfiles 2>/dev/null | wc -l | tr -d ' ')

print -- "modules:  $n_modules"
print -- "lines:    $n_lines"
print -- "theorems: $n_decls"
print -- "sorry:    $n_sorry in $n_files_with_sorry file(s)"
grep -nE '^\s*sorry\s*$' $srcfiles 2>/dev/null | sed "s|$PWD/||"
