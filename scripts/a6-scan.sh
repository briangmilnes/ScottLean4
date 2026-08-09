#!/bin/zsh
# a6-scan.sh — the r0044 Class-3 lexical sweep: every declaration in the package,
# by kind, written to analyses/ so the counts in the report are reproducible.
#
# Usage: scripts/a6-scan.sh <outdir>
#
# Emits, into <outdir>:
#   a6-all-decls.tsv     path:line<TAB>kind<TAB>name<TAB>attrs, every declaration
#   a6-axioms.tsv        the `axiom` declarations (r0044 expects zero)
#   a6-defs.tsv          the `def`/`abbrev` declarations
#   a6-structures.tsv    the `structure`/`class` declarations
#   a6-simp.tsv          every declaration carrying an attribute group with simp
#
# Read-only: it touches no `.lean` file. Exists because the sweep needs a `find`
# feeding a python program feeding several greps — a compound command, which
# cannot be allowlisted, per CLAUDE.md's shell discipline.
set -e
cd "${0:A:h}/.."
pkg="ScottDomains/ScottDomains"
out="${1:?usage: scripts/a6-scan.sh <outdir>}"
mkdir -p "$out"

srcfiles=(${(f)"$(find $pkg -name '*.lean' | sort)"})
print -- "modules: $#srcfiles"

python3 "${0:A:h}/a6-decls.py" $srcfiles > "$out/a6-all-decls.tsv"
grep -P '\taxiom\t'                "$out/a6-all-decls.tsv" > "$out/a6-axioms.tsv"     || true
grep -P '\t(def|abbrev)\t'         "$out/a6-all-decls.tsv" > "$out/a6-defs.tsv"       || true
grep -P '\t(structure|class)\t'    "$out/a6-all-decls.tsv" > "$out/a6-structures.tsv" || true
grep -P '\tsimp\b|\[simp' "$out/a6-all-decls.tsv" > "$out/a6-simp.tsv" || true

print -- "all decls:  $(wc -l < $out/a6-all-decls.tsv)"
print -- "axiom:      $(wc -l < $out/a6-axioms.tsv)"
print -- "def/abbrev: $(wc -l < $out/a6-defs.tsv)"
print -- "struct/cls: $(wc -l < $out/a6-structures.tsv)"
print -- "simp-tagged:$(wc -l < $out/a6-simp.tsv)"
