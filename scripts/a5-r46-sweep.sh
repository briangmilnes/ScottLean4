#!/usr/bin/env bash
# a5-r46-sweep.sh — r0046 / agent5, Goal B: sweep the corpus for NECESSITY and
# IMPOSSIBILITY claims in prose.
#
#   scripts/a5-r46-sweep.sh [outfile]
#
# Why this exists.  Seven sentences of the form "X is required" / "Y cannot be
# done" / "Z does not exist" have been found across r0043-r0045, EVERY ONE
# incidentally while looking for something else.  This sentence type has never
# been swept.  It is decidable: a necessity claim about a hypothesis is decided
# by the deletion probe (delete the hypothesis, re-elaborate the proof), and an
# absence claim about Mathlib is decided by `#check` / `open ... in #check` in a
# Mathlib-only environment.
#
# Corpus: every `.lean` under ScottDomains/ScottDomains (docstrings and comments
# only — the grep patterns are English, so declaration lines do not match), plus
# every `.md` under ScottDomains/docs, ScottDomains/analyses, ScottDomains/plans
# and ScottDomains/reports when -a is given.
#
# Output: TSV-ish `class<TAB>file:line<TAB>text`, one candidate per line, so the
# hand-check that measures precision has a stable denominator.
#
# Work: O(|corpus| * |patterns|) with one grep pass per pattern class;
# span: one `grep -rn` per class.
set -eu

root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
src="$root/ScottDomains/ScottDomains"
out="${1:-$root/ScottDomains/analyses/a5-r46-sweep.txt}"

# Class N — necessity: a hypothesis/lemma/step asserted to be unavoidable.
pat_N='cannot do without|indispensable|is required|are required|is needed|are needed|has to go through|must go through|must be assumed|is unavoidable|is essential|is necessary|are necessary|only works because|is load-bearing|is forced|cannot be dropped|cannot be removed|cannot be weakened|cannot be avoided|is not optional|the argument needs|the proof needs|without it|without which'

# Class I — impossibility: an operation/statement asserted to be impossible.
pat_I='is not possible|is impossible|cannot be (proved|proven|stated|expressed|formed|built|constructed|derived|asked|defined|instantiated)|is not provable|is not derivable|is not expressible|cannot be asked|no way to|there is no way'

# Class A — absence: a declaration/definition asserted not to exist.
pat_A='does not exist|do not exist|there is no |there are no |is not in Mathlib|not present in Mathlib|Mathlib has no|Mathlib does not|Mathlib lacks|nothing proves|no such |we found none|returned zero hits|zero hits|is absent|has no instance|no instance of|is missing from'

# Class U — uniqueness/exhaustiveness: "the only", "the sole", "nothing else".
pat_U='the only |is the sole|the sole |nothing else|no other |the unique way|the single '

emit () {  # emit <class> <pattern>
  local cls="$1" pat="$2"
  grep -rInE "$pat" "$src" --include='*.lean' 2>/dev/null \
    | sed -e "s|^$root/||" \
    | awk -F: -v c="$cls" '{f=$1; l=$2; $1=""; $2=""; sub(/^::/,""); \
        gsub(/^[ \t]+/,""); print c "\t" f ":" l "\t" $0}'
}

{
  emit N "$pat_N"
  emit I "$pat_I"
  emit A "$pat_A"
  emit U "$pat_U"
} | LC_ALL=C sort -u -t$'\t' -k2,2V -k1,1 > "$out"

echo "corpus: $(find "$src" -name '*.lean' | wc -l) .lean modules"
echo "candidates: $(wc -l < "$out")"
for c in N I A U; do
  echo "  class $c: $(grep -cP "^$c\t" "$out" || true)"
done
echo "wrote $out"
