#!/usr/bin/env bash
# a3-r50-decls2.sh — recall check for a3-r50-decls.sh: any line in agent3's r0050
# module set that introduces a declaration (theorem/lemma/def/abbrev/instance/
# structure/inductive/class/alias) anywhere on the line, with a digit in the name,
# including indented and attribute-prefixed forms. Used to confirm the column-0
# scan missed nothing.
set -u
ROOT=/home/milnes/projects/ScottLean4-agent3/ScottDomains/ScottDomains
FILES="JungBicomplete.lean JungCor136.lean JungFinite.lean JungNets.lean JungSFP.lean Iwamura.lean PropertyM.lean Thm18.lean SFP.lean A5Thm137.lean FinitaryProjectionEmbedding.lean RecursiveDomain.lean"
for f in $FILES; do
  grep -nE '(^|[[:space:]]|\])(theorem|lemma|def|abbrev|instance|structure|inductive|class|alias) +[A-Za-z_][A-Za-z_.]*[0-9]' "$ROOT/$f" \
    | sed "s|^|$f:|"
done
