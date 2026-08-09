#!/bin/zsh
# a6-env-scan.sh — run `scripts/a6-query.lean` against the BUILT package
# environment: every package module imported into one file, then the
# metaprogram enumerates axioms, Prop-valued `def`s, structures and their
# constructor uses.
#
# Usage: scripts/a6-env-scan.sh <output-file> [body.lean]
#   body.lean   metaprogram to run (default scripts/a6-query.lean); pass
#               scripts/a6-probe.lean for the debug companion.
#
# It generates the import prologue from the module tree (so a module added later
# is picked up automatically), concatenates `scripts/a6-query.lean`, and runs
# `lake env lean` on the result — one command, per CLAUDE.md's shell discipline,
# with no `.lean` file in the package touched. The temp file goes in /tmp because
# it must not sit under `ScottDomains/ScottDomains/`, where `lake build` and
# `counts.sh` would see it.
set -e
cd "${0:A:h}/.."
root="$PWD"
pkg="$root/ScottDomains"
out="${1:?usage: scripts/a6-env-scan.sh <output-file> [body.lean]}"
body="${2:-$root/scripts/a6-query.lean}"

tmp="$(mktemp /tmp/a6-query-XXXXXX.lean)"
trap 'rm -f "$tmp"' EXIT

# ScottDomains/ScottDomains/A/B.lean  ->  import ScottDomains.A.B
for f in ${(f)"$(find $pkg/ScottDomains -name '*.lean' | sort)"}; do
  rel="${f#$pkg/}"
  rel="${rel%.lean}"
  print -- "import ${rel//\//.}" >> "$tmp"
done
print -- "import ScottDomains" >> "$tmp"
cat "$body" >> "$tmp"

cd "$pkg"
lake env lean "$tmp" > "$out" 2>&1 || true
print -- "wrote $out ($(wc -l < $out) lines)"
