#!/usr/bin/env bash
# a2-crop-list.sh — render several rectangular crops of a PDF in one invocation.
#
# Why this exists: r0039 agent2 has eight commutative diagrams to transcribe on
# pages 19-30 of `Gunter Scott 1990.pdf`. Each needs a 300 dpi crop so the
# operator names (smash, unsmash, strict_curry, ext) and the solid-vs-dashed
# arrows can be read; guessing them from a 150 dpi whole-page render is not
# good enough. pdf-crop.sh renders one region per call, so eight calls; this
# loops instead, which the project's shell rule says belongs in scripts/.
#
# Each SPEC is page:x:y:w:h:name, in pixels at the given dpi.
#
# Usage: a2-crop-list.sh <pdf> <dpi> <out-dir> <SPEC> [<SPEC> ...]
set -euo pipefail
pdf="$1"; dpi="$2"; out="$3"; shift 3
mkdir -p "$out"
for spec in "$@"; do
  IFS=: read -r p x y w h name <<<"$spec"
  pdftoppm -png -r "$dpi" -f "$p" -l "$p" -x "$x" -y "$y" -W "$w" -H "$h" "$pdf" "$out/$name"
done
ls -la "$out"
