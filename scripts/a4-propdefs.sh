#!/bin/zsh
# a4-propdefs.sh — for each `Prop`-valued `def` in agent4's r0044 area, count its
# uses across the whole package and show every line that mentions it.
#
# Usage: scripts/a4-propdefs.sh
#
# Why it exists (r0044, Class 2, instrument 2'): a hypothesis that is never
# discharged anywhere makes every theorem taking it *unexercised*; a hypothesis
# that is provable outright makes every theorem taking it *unconditional*, which
# is the `EffectivePresentation` shape. Both are invisible to
# `#lint only unusedArguments`, which reports only hypotheses that occur in
# neither the type nor the proof. This lists the call sites so each `def` can be
# put in one of the three buckets by reading them.
#
# Work: O(#propdefs × package size) greps; span: sequential.
set -e
here="${0:A:h}"
pkg="$here/../ScottDomains/ScottDomains"
names=(
  ScottDomains.FlatPowerdomain.SmythTrivial:SmythTrivial
  ScottDomains.FlatPowerdomain.Ple:Ple
  ScottDomains.FlatOmega.omegaTest:omegaTest
  ScottDomains.ClosureProperties.SelectsGreatest:SelectsGreatest
  ScottDomains.PowerdomainMap.Rep.SmythImageIso:SmythImageIso
  ScottDomains.PowerdomainMap.Rep.SmythFamilyLUB:SmythFamilyLUB
  ScottDomains.PowerdomainMap.Rep.HoareImageIso:HoareImageIso
  ScottDomains.PowerdomainMap.Rep.HoareFamilyLUB:HoareFamilyLUB
  ScottDomains.Smyth.finsetLE:finsetLE
)
for entry in $names; do
  short=${entry##*:}
  print -- "=== $short ==="
  grep -rn "\b$short\b" $pkg --include='*.lean' || print -- "  (no occurrence)"
  print -- ""
done
