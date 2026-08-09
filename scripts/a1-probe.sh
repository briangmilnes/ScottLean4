#!/bin/zsh
# a1-probe.sh — elaborate an arbitrary Lean probe file against the built package,
# as ONE allowlisted command. The probe lives OUTSIDE ScottDomains/ (scratchpad),
# so nothing in the package is edited and `lake build` is untouched.
#
# Why this exists (r0044, Class 1, agent1): classifying an `S≠` row as
# "under-specified by an unnecessary hypothesis" is a claim that the hypothesis
# can be deleted. That claim is only evidence if the kernel accepts the proof
# without it. This runs the probe that decides it.
#
# usage: scripts/a1-probe.sh <absolute-path-to-probe.lean>
set -e
cd "${0:A:h}/.."
pkg="$PWD/ScottDomains"
probe="$1"
[[ -f "$probe" ]] || { print -u2 "a1-probe.sh: no such file: $probe"; exit 2 }
cd "$pkg"
lake env lean "$probe"
