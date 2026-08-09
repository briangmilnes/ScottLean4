#!/bin/zsh
# a2-r0044-sneq-check.sh — elaborate every declaration cited by the r0044 Class-1
# split of the `S≠` rows in §5, §6 and §7, and print each one's *elaborated* type
# (`#check @d`) together with its axiom dependencies (`#print axioms d`).
#
# Why this exists: r0044's evidence rule forbids quoting a Lean statement off a
# source line. A row is classified under-specified / incorrectly specified /
# deliberately divergent by comparing the paper's sentence with the proposition
# the *kernel* holds, which is what `#check @d` prints — every implicit binder,
# every instance argument, and every unfolded notation made explicit. The r0040
# and r0043 reports name several of these declarations with a namespace they do
# not have (`ClosureProperties.lem17_fun` is `ScottDomains.lem17_fun`); running
# this script is what catches that.
#
# The module list is hard-coded rather than derived from the declaration names,
# because for six of the thirteen the namespace path is NOT the module path.
#
# usage: scripts/a2-r0044-sneq-check.sh        (no arguments; the set is fixed)
set -e
cd "${0:A:h}/.."
pkg="$PWD/ScottDomains"

tmp="$(mktemp /tmp/a2-r0044-XXXXXX.lean)"
trap 'rm -f "$tmp"' EXIT

for m in \
  ScottDomains.FlatPowerdomain \
  ScottDomains.Section62 \
  ScottDomains.FinitaryProjectionEmbedding \
  ScottDomains.Skeleton.Lemma17 \
  ScottDomains.ClosureProperties \
  ScottDomains.ClosureProperties.StrictFunction \
  ScottDomains.JungFinite \
  ScottDomains.PowerdomainMap \
  ScottDomains.Universality \
  ScottDomains.Combinator \
  ScottDomains.BifiniteUniversal \
  ScottDomains.Colimit \
  ScottDomains.Skeleton.Section6 \
  ScottDomains.Skeleton.Recovered
do
  print -- "import $m" >> "$tmp"
done

print -- "" >> "$tmp"
print -- "set_option pp.numericTypes false" >> "$tmp"
print -- "set_option pp.coercions true" >> "$tmp"
print -- "" >> "$tmp"

# §5 (r0043 agent3 row 18), §6 (r0040 agent4 rows 3-5 + p9b, r0043 row p16),
# §7 (r0040 agent5 rows 6-11 + row 27).  Two extra declarations are checked as
# controls: `Skeleton.Section6.lem19` (the weaker duplicate r0040 named) and the
# §5 rows 25-27 adjudication targets.
for d in \
  ScottDomains.Flat.plotkin_le_iff \
  ScottDomains.Flat.plotkin_printed_clause_one_fails \
  ScottDomains.Section62.thm16_positive \
  ScottDomains.FpEmbedding.TwoMub.not_isEmbeddingProjectionPair \
  ScottDomains.lem17_fun \
  ScottDomains.ClosureProperties.lem17_strictFun \
  ScottDomains.JungFinite.mubDiff_nonempty \
  ScottDomains.PowerdomainMap.isProjection_plotkin \
  ScottDomains.Universality.lem24 \
  ScottDomains.Universality.thm25 \
  ScottDomains.Combinator.thm26 \
  ScottDomains.BifiniteUniversal.eta_le_eta_iff \
  ScottDomains.Colimit.stgEmb_ne_mk_eta \
  ScottDomains.Combinator.thm26_subalgebra \
  ScottDomains.Combinator.thm26_retract \
  ScottDomains.ClosureProperties.lemma17 \
  ScottDomains.Flat.smyth_oneBot_eq_bot_eq_unit_bot \
  ScottDomains.Flat.hoare_oneBot_eq_one \
  ScottDomains.Flat.hoare_oneBot_ne_bot \
  ScottDomains.Flat.plotkin_three_distinct
do
  print -- "#check @$d" >> "$tmp"
  print -- "#print axioms $d" >> "$tmp"
done

# Definitions the classifications turn on, printed rather than checked.
for d in \
  ScottDomains.Section62.HasGreatestStableNormal \
  ScottDomains.ScottHom.IsProjection \
  ScottDomains.ScottHom.IsFinitaryProjection \
  ScottDomains.Recovered.IsBifiniteViaProjections \
  ScottDomains.Colimit.stgEmb
do
  print -- "#print $d" >> "$tmp"
done

cd "$pkg"
lake env lean "$tmp"
