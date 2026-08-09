#!/bin/zsh
# a4-structures.sh — enumerate every `structure`, `class`, `inductive` and
# `def`-returning-`Prop` in agent4's r0044 area, with file and line.
#
# Usage: scripts/a4-structures.sh
#
# Why it exists (r0044, Class 2, instrument 3): the vacuity mechanism the plan
# names — `Classical.dec` freely inhabiting `EffectivePresentation` — is invisible
# to `#lint`'s `unusedArguments`, because the structure IS used in the statement
# and the proof. Catching it needs the complementary question "is an instance of
# this structure derivable for EVERY type?", which first needs the list of
# structures to ask it of. This is a lexical enumeration (grep), used only to
# generate candidates; every candidate is then decided in the Lean environment by
# a probe file, never from the source line.
set -e
root="${0:A:h}"
files=(${(f)"$($root/a4-area.sh)"})
print -- "=== structure / class / inductive ==="
grep -nE '^\s*(@\[[^]]*\]\s*)?(private\s+|protected\s+|noncomputable\s+)*(structure|class|inductive|abbrev)\b' $files || true
print -- ""
print -- "=== def … : Prop / def … : … → Prop ==="
grep -nE '^\s*(@\[[^]]*\]\s*)?(private\s+|protected\s+|noncomputable\s+)*def\b.*\bProp\b' $files || true
