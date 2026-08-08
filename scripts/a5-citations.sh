#!/bin/zsh
# a5-citations.sh — r0038 agent5 audit: for every theorem/lemma in the §7
# representability stack, count the *uses* of its name across the whole package
# and name the modules that use it.
#
# Why this exists: the audit's `S` label requires naming a citing declaration and
# its `U` label requires showing there is none. scripts/unused-theorems.sh answers
# only the boolean "occurs once", over the whole development, with final-component
# matching that collides across namespaces. This is the finer instrument the §7
# stack needs: it separates same-file uses from cross-module uses, because a
# lemma used only inside its own file is support for that file's headline result,
# while a lemma used nowhere at all is a `U` candidate.
#
# Method: build one flattened index `module<TAB>line<TAB>text` over the package,
# then for each name grep that index word-wise and drop the row that is the name's
# own declaration. Cost: one O(lines) pass plus 403 O(lines) scans, versus 403
# directory walks.
#
# LIMIT, same as unused-theorems.sh: matching is on the final name component, so
# two same-named lemmas in different namespaces mask each other. That makes this
# UNDER-report deadness. A zero here is strong evidence; a nonzero is weak.
#
# Output: TSV — name<TAB>module<TAB>uses_total<TAB>uses_own_module<TAB>citing-modules(csv)
# Usage: scripts/a5-citations.sh
set -e
cd "${0:A:h}/.."
pkg="ScottDomains/ScottDomains"

idx=$(mktemp /tmp/a5-idx-XXXXXX)
for f in ${(f)"$(find $pkg -name '*.lean' | sort)"}; do
  m=${f#$pkg/}; m=${m%.lean}
  # Column 4 is the line with comments blanked out, so a mention that occurs only
  # inside a docstring ("used by X") is not miscounted as a use. Block-comment
  # nesting depth is tracked; `--` line comments are truncated.
  awk -v M="$m" '
    {
      raw = $0; code = $0; out = ""
      i = 1
      while (i <= length(code)) {
        two = substr(code, i, 2)
        if (depth > 0) {
          if (two == "-/") { depth--; i += 2; continue }
          if (two == "/-") { depth++; i += 2; continue }
          i++; continue
        }
        if (two == "/-") { depth++; i += 2; continue }
        if (two == "--") { break }
        out = out substr(code, i, 1); i++
      }
      printf "%s\t%d\t%s\t%s\n", M, NR, raw, out
    }' $f >> $idx
done

"${0:A:h}"/a5-decls.sh | while IFS=$'\t' read -r m ln simp nm stmt; do
  hits=$(grep -w -F -- "$nm" $idx || true)
  filtered=$(print -r -- "$hits" | grep -v "^$m	$ln	" || true)
  if [[ -z "$filtered" ]]; then
    printf '%s\t%s\t0\t0\t-\n' "$nm" "$m"
    continue
  fi
  code=$(print -r -- "$filtered" | cut -f1,2,4 | grep -w -F -- "$nm" || true)
  tot=$(print -r -- "$code" | grep -c . || true)
  own=$(print -r -- "$code" | grep -c "^$m	" || true)
  if (( tot == 0 )); then
    printf '%s\t%s\t0\t0\t-\n' "$nm" "$m"
    continue
  fi
  mods=$(print -r -- "$code" | cut -f1 | sort -u | tr '\n' ',')
  printf '%s\t%s\t%s\t%s\t%s\n' "$nm" "$m" "$tot" "$own" "${mods%,}"
done

rm -f $idx
