#!/bin/zsh
# unused-theorems.sh — which theorem names are never mentioned anywhere in the
# development except at their own declaration?
#
# Why this exists: `counts.sh` says 1308 theorem-ish declarations against a paper
# with 30 numbered results. That ratio alone cannot distinguish necessary support
# from speculative API. A theorem that nothing cites is either (a) a paper claim,
# which is terminal by design and *should* have no callers, (b) a headline result
# other work builds on later, or (c) API written for a caller that never
# appeared. Round r0020 did this audit by hand over 37 modules and found 16
# uncited theorems, of which 6 were case (c) and were commented out. The
# development has since doubled twice; this does the same measurement mechanically.
#
# Method: collect every `theorem`/`lemma` name (the counts.sh rule), then count
# occurrences of each name across all sources. A name occurring exactly once is
# mentioned only at its own declaration. Namespace-qualified uses are matched
# because the search is on the final component as a whole word.
#
# LIMITS, stated because the number is easy to over-read:
#   * a name used only inside its own file's proofs still counts as used;
#   * `simp`/`aesop` may fire a lemma without naming it, so a tagged lemma
#     reported here is not necessarily dead — the `simp` column of
#     scripts/module-counts.sh is the cross-check;
#   * final-component matching can collide across namespaces (two `map_bot`s),
#     which makes this under-report rather than over-report.
# So treat the output as a candidate list for review, never as a delete list.
#
# Usage: scripts/unused-theorems.sh [--names-only]
set -e
cd "${0:A:h}/.."
pkg="$HOME/projects/ScottProjects/ScottDomains/ScottDomains"

srcfiles=(${(f)"$(find $pkg -name '*.lean' | sort)"})

tmpnames=$(mktemp /tmp/thm-names-XXXXXX)
tmpall=$(mktemp /tmp/thm-all-XXXXXX)

# Declaration lines -> bare final-component names.
grep -hE '^(@\[[^]]*\] )?(theorem|lemma) ' $srcfiles \
  | sed -E 's/^(@\[[^]]*\] )?(theorem|lemma) +//; s/[ ({:\[].*$//; s/^.*\.//' \
  | sort -u > $tmpnames

cat $srcfiles > $tmpall

n_names=$(wc -l < $tmpnames | tr -d ' ')
n_unused=0

print -r -- "# theorem names mentioned only at their own declaration"
print -r -- "# (candidates for review, NOT a delete list — see the script header)"
while read -r nm; do
  [[ -z "$nm" ]] && continue
  c=$(grep -c -w -F -- "$nm" $tmpall || true)
  if (( c <= 1 )); then
    where=$(grep -l -E "^(@\[[^]]*\] )?(theorem|lemma) +($nm|[A-Za-z0-9_.]*\.$nm)[ ({:\[]" $srcfiles | head -1)
    print -r -- "${where#$pkg/}: $nm"
    n_unused=$((n_unused + 1))
  fi
done < $tmpnames

print -r -- ""
print -r -- "unused-theorems: $n_unused of $n_names distinct names occur only once"
rm -f $tmpnames $tmpall
