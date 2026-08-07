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
n_decls=$(grep -hE '^(@\[[^]]*\] )?(theorem|lemma) ' $srcfiles | wc -l | tr -d ' ')
n_files_with_sorry=$(grep -lE '^\s*sorry\s*$' $srcfiles 2>/dev/null | wc -l | tr -d ' ')
n_sorry=$(grep -hE '^\s*sorry\s*$' $srcfiles 2>/dev/null | wc -l | tr -d ' ')

print -- "modules:  $n_modules"
print -- "lines:    $n_lines"
print -- "theorems: $n_decls"
print -- "sorry:    $n_sorry in $n_files_with_sorry file(s)"
grep -nE '^\s*sorry\s*$' $srcfiles 2>/dev/null | sed "s|$PWD/||"
