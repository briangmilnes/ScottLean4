#!/usr/bin/env bash
# numbered-status.sh — for each of Gunter & Scott's 30 numbered results, list the
# declarations in this package that carry its number.
#
# Why: the package names numbered results four different ways — `thm11`,
# `theorem1`, `lem17_fun`, `lemma28` — so no single grep finds them and the
# status of a given numbered result cannot be read off a filename. This prints
# every declaration whose name carries each number, so `docs/Status.md` is
# written from measured data rather than from recollection, and can be re-derived
# when the tree changes.
#
# Reads the comment-aware declaration list, so a declaration commented out in a
# `/- … -/` block is not counted (the defect r0038 found in the old grep rule).
#
# Output: analyses/numbered-status.<stamp>.orchestrator.tsv
#   number <TAB> count <TAB> declarations (comma separated, unqualified)

set -uo pipefail
root=/home/milnes/projects/ScottLean4
pkg="$HOME/projects/ScottProjects/ScottDomains"
out="$pkg/analyses/numbered-status.$(date +%Y%m%d-%H%M%S).orchestrator.tsv"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

find "$pkg/ScottDomains" -name '*.lean' -print0 \
  | xargs -0 python3 "$root/scripts/lean-decls.py" --list \
  | cut -f2 | sort -u > "$work/decls.txt"

{
  printf 'number\tcount\tdeclarations\n'
  for n in $(seq 1 30); do
    # A declaration belongs to numbered result n when its name carries one of the
    # paper's heading words followed by <n>, with <n> not extended by another
    # digit -- so `thm1` does not swallow `thm11`, `thm12`, `thm137`.
    #
    # `prop|proposition|cor|corollary` were added in r0048. The first version of
    # this script matched only thm/theorem/lem/lemma, and so reported result 15
    # as carried by no declaration -- when it is `Skeleton/Section6.lean`'s
    # `prop15`, present and proved since that file was written. Gunter & Scott
    # number Propositions in the same sequence as Theorems and Lemmas, so a
    # heading-word alternation that omits them under-reports.
    #
    # False positives were measured before widening, not assumed: the complete
    # set of prop/cor-numbered identifiers in the package is prop15, prop122,
    # cor136, Prop134, thm137, and over n in 1..30 the widened pattern adds
    # exactly one hit (prop15 at n=15) and no false positive -- prop122 and
    # cor136 are Jung's numbering and fail on the trailing-digit guard.
    pat="(thm|theorem|lem|lemma|prop|proposition|cor|corollary)_?${n}([^0-9]|\$)"
    hits=$(grep -iE "$pat" "$work/decls.txt" | paste -sd, -)
    c=$(grep -icE "$pat" "$work/decls.txt")
    printf '%s\t%s\t%s\n' "$n" "$c" "${hits:-—}"
  done
} > "$out"

echo "wrote $out"
awk -F'\t' 'NR>1 && $2==0 {print "  no declaration carries number " $1}' "$out"
