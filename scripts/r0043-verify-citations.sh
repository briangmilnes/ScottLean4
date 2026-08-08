#!/usr/bin/env bash
# r0043-verify-citations.sh — check that every declaration name the r0043 reports
# cite as S+P evidence actually exists as a declaration in the tree.
#
# Why this exists: r0043's product is the set of rows that moved N -> S+P, and the
# plan admits only "you name the declaration and confirm it exists" as evidence.
# The failure mode is a cited name that does not elaborate. It is not
# hypothetical: r0038 found two files asserting false things about themselves,
# and r0043's own agent3 found FlatPowerdomain.lean:34 naming two declarations
# (smyth_oneBot_eq_bot, smyth_bot_eq_bot) that do not exist.
#
# Method: extract every backticked identifier from the five r0043 reports, keep
# those that look like Lean declaration names, and test each against the
# comment-aware declaration list produced by lean-decls.py over the whole
# package. Prints the names with no matching declaration.
#
# Known blind spot: lean-decls.py lists top-level declarations, not structure or
# class FIELDS. So axioms carried as fields read as unresolved even though they
# exist -- op_comm and op_idem are fields of IsSemilattice, app_lam a field of
# Combinator.LambdaModel. Check a snake_case miss against the structure bodies
# before calling it a false citation.
#
# Also expect legitimate misses for names an agent cites as a ZERO-HIT grep, i.e.
# as evidence that something is absent. Unresolved is the correct outcome there.
#
# Output: analyses/r0043-citations.<stamp>.orchestrator.log

set -uo pipefail

root=/home/milnes/projects/ScottLean4
pkg="$root/ScottDomains"
stamp=$(date +%Y%m%d-%H%M%S)
out="$pkg/analyses/r0043-citations.$stamp.orchestrator.log"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

# The universe of real declaration names, comment-aware. lean-decls.py --list
# emits "path:line<TAB>name" with the name unqualified (no namespace prefix), so
# take field 2.
find "$pkg/ScottDomains" -name '*.lean' -print0 \
  | xargs -0 python3 "$root/scripts/lean-decls.py" --list \
  | cut -f2 | sort -u > "$work/decls.txt"

# Every backticked token in the five r0043 reports.
cat "$pkg"/reports/r0043-report-from-agent*.md > "$work/reports.txt"
grep -o '`[A-Za-z_][A-Za-z0-9_.'"'"'₀-₉]*`' "$work/reports.txt" \
  | tr -d '`' | sort -u > "$work/cited.txt"

# Keep only plausible declaration names: must contain a lowercase letter and be
# longer than 3 chars, which drops bare namespaces (Flat, ScottHom) and labels
# (S, P, N). A cited name matches if it appears as a full declaration name or as
# the tail of one (reports often drop the namespace prefix).
: > "$work/missing.txt"
: > "$work/found.txt"
while read -r name; do
  case "$name" in
    ???|??|?) continue ;;
  esac
  case "$name" in
    *[a-z]*) ;;
    *) continue ;;
  esac
  # decls.txt holds unqualified names; reports cite either the bare name or a
  # namespace-qualified one, so compare against the cited name's last component.
  tail="${name##*.}"
  if grep -qxF "$name" "$work/decls.txt" || grep -qxF "$tail" "$work/decls.txt"; then
    echo "$name" >> "$work/found.txt"
  else
    echo "$name" >> "$work/missing.txt"
  fi
done < "$work/cited.txt"

{
  echo "# r0043 citation check — $(date '+%Y-%m-%d %H:%M:%S %z')"
  echo
  echo "declarations in package : $(wc -l < "$work/decls.txt")"
  echo "backticked tokens cited : $(wc -l < "$work/cited.txt")"
  echo "resolved to a declaration: $(wc -l < "$work/found.txt")"
  echo "no matching declaration  : $(wc -l < "$work/missing.txt")"
  echo
  echo "## unresolved tokens"
  echo "# Most are prose, file names, tactics or Mathlib lemmas, not claims."
  echo "# Read for any that is cited AS the evidence for an S+P row."
  echo
  cat "$work/missing.txt"
} > "$out"

echo "wrote $out"
grep -c . "$work/missing.txt" | sed 's/^/unresolved tokens: /'
