#!/bin/zsh
# a4-area.sh — print the absolute paths of the modules assigned to agent4's
# r0044 Class 2 stream, so every later measurement is taken over the same set.
#
# Usage: scripts/a4-area.sh
#
# Area (from plans/r0044-…-specification-defects.md): the powerdomain and
# flat-cpo modules — `Flat*`, `Powerdomain*` (both the top-level modules and the
# `Powerdomain/` tree), `ContinuousAlgebra`, and the Plotkin/Smyth/Hoare
# material. `ClosureProperties/Powerdomain.lean` and `Audit/Powerdomains.lean`
# are included because they are powerdomain modules by name and content;
# `Powerset.lean` is included because `P N` is the powerdomain material's
# standing witness domain.
set -e
pkg="${0:A:h}/../ScottDomains/ScottDomains"
for f in \
  Flat.lean FlatOmega.lean FlatPowerdomain.lean FlatSection6.lean \
  Powerdomain/BoundedComplete.lean Powerdomain/Hoare.lean \
  Powerdomain/Plotkin.lean Powerdomain/Smyth.lean Powerdomain/Universal.lean \
  PowerdomainCompacts.lean PowerdomainMap.lean PowerdomainMapRep.lean \
  ContinuousAlgebra.lean ClosureProperties/Powerdomain.lean \
  Audit/Powerdomains.lean Powerset.lean
do
  print -- "${pkg:A}/$f"
done
