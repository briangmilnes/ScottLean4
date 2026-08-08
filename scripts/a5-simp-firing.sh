#!/bin/zsh
# a5-simp-firing.sh — r0038 agent5 audit: does a module's own `@[simp]` tag do any
# work inside that module?
#
# Why this exists: the audit's `A` label asks whether removing a `simp` tag changes
# the build, and r0020 answered that question by commenting the declarations out
# and rebuilding — which found three tagged lemmas that had never fired. This round
# forbids editing any `.lean` file, so the experiment is run on a COPY in the
# scratch tree and elaborated with `lake env lean`, which reads the already-built
# `.olean`s of the module's imports and writes nothing into the package.
#
# Method: copy `ScottDomains/<Module>.lean`, delete the leading attribute group on
# declaration lines that contains `simp` (the same line shape `counts.sh` and
# `module-counts.sh` use as this project's counting rule), and elaborate the copy.
# A control run elaborates the unmodified copy first, so a failure is attributable
# to the stripped tags rather than to the harness.
#
# WHAT THE RESULT MEANS, and what it does not:
#   * exit 0 on the stripped copy => the tags do NO work inside this module.
#     For a LEAF module (nothing imports it) that settles the question entirely.
#     For a module with importers it does not: the tag may still fire downstream,
#     and only a full `lake build` with the tag removed in place would show that.
#   * a nonzero exit names the goals that actually needed the tag.
#
# Usage: scripts/a5-simp-firing.sh <Module> [<Module> ...]
set -e
cd "${0:A:h}/.."
pkg="ScottDomains/ScottDomains"
out="/tmp/claude-1000/-home-milnes-projects-ScottLean4/ab3f8bb9-d928-40ef-b45c-b2c8efc2bd0e/scratchpad/simp-firing"
mkdir -p $out

for m in "$@"; do
  src="$pkg/$m.lean"
  ctl="$out/$m.control.lean"
  exp="$out/$m.stripped.lean"
  cp $src $ctl
  awk '{ if ($0 ~ /^@\[[^]]*simp[^]]*\] (theorem|lemma) /) sub(/^@\[[^]]*\] /, ""); print }' \
    $src > $exp
  n=$(grep -c '' $exp || true)
  stripped=$(grep -cE '^@\[[^]]*simp[^]]*\] (theorem|lemma) ' $src || true)
  if (( stripped == 0 )); then
    print -r -- "=== $m: no simp tags, nothing to measure"
    continue
  fi

  print -r -- "=== $m: $stripped simp tags stripped, $n lines"

  if lake -d ScottDomains env lean $ctl > $out/$m.control.out 2>&1; then
    print -r -- "  control:  elaborates, exit 0"
  else
    print -r -- "  control:  FAILED — harness problem, result below is not usable"
    continue
  fi

  if lake -d ScottDomains env lean $exp > $out/$m.stripped.out 2>&1; then
    print -r -- "  stripped: elaborates, exit 0 — the $stripped tags do no work inside $m"
  else
    print -r -- "  stripped: FAILED — $(grep -c 'error:' $out/$m.stripped.out) errors; the tags are load-bearing inside $m"
    grep -m 5 'error:' $out/$m.stripped.out || true
  fi
done
