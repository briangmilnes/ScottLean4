#!/usr/bin/env bash
# a3-r50-cites.sh — re-locate, after the r0050 phase-1 edits, each docstring line
# the agent3 report cites as the attribution evidence for a renamed declaration.
# Line numbers shift when an `alias` is inserted above, so the report's citations
# are regenerated from the post-edit files rather than from the pre-edit reads.
set -u
ROOT=/home/milnes/projects/ScottLean4-agent3/ScottDomains/ScottDomains
grep -n "Jung 1989, Proposition 1.22" "$ROOT/JungBicomplete.lean"
grep -n "Lemma 1.29 over" "$ROOT/JungFinite.lean"
grep -n "A poset .D. with property m" "$ROOT/JungFinite.lean"
grep -n "Jung 1989, Lemma 2.2" "$ROOT/JungFinite.lean"
grep -n "Theorem 18. If .D. and" "$ROOT/JungFinite.lean" "$ROOT/PropertyM.lean" "$ROOT/Thm18.lean"
grep -n "Jung 1989, Theorem 1.37" "$ROOT/JungNets.lean"
grep -n "The minimal remaining obligation" "$ROOT/JungNets.lean"
grep -n "reduced to Theorem 1.37" "$ROOT/JungNets.lean"
grep -n "with its property-m hypothesis discharged" "$ROOT/JungNets.lean" "$ROOT/PropertyM.lean"
grep -n "Property M at every pair of compact elements" "$ROOT/JungNets.lean"
grep -n "Jung 1989, Lemma 2.13" "$ROOT/JungSFP.lean"
grep -n "Jung 1989, Theorem 2.14" "$ROOT/JungSFP.lean"
grep -n "Jung 1989, Lemma 2.17" "$ROOT/JungSFP.lean"
grep -n "now implies" "$ROOT/Iwamura.lean"
grep -n "two forms of Jung's Theorem 1.37" "$ROOT/Iwamura.lean"
grep -n "The obligation this round is left with" "$ROOT/Iwamura.lean"
grep -n "The remaining obligation, in its weakest named form" "$ROOT/PropertyM.lean"
grep -n "Spreen, .The largest Cartesian closed" "$ROOT/PropertyM.lean"
grep -n "Claim 3 discharged\|Claim 2 discharged\|Claim 1 discharged\|Cross-check, not a new result" "$ROOT/A5Thm137.lean"
grep -n "Gunter & Scott, .Semantic Domains., .6.2, printed page 33" "$ROOT/Thm18.lean"
grep -n "Theorem 14 The following are equivalent\|Theorem 14, .1 . 2\|Theorem 14, .2 . 1" "$ROOT/SFP.lean"
grep -n "Theorem 16 If .D. is bifinite" "$ROOT/FinitaryProjectionEmbedding.lean"
grep -n "Theorem 21 If an operator" "$ROOT/RecursiveDomain.lean"
grep -n "Jung 1989, Theorem 1.2" "$ROOT/Iwamura.lean"
grep -n "Markowsky's theorem\*\*" "$ROOT/Iwamura.lean"
