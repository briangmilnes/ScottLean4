#!/bin/zsh
# agent2-uses.sh — count *proof and statement* uses of each theorem declared in
# agent2's r0038 audit area, with Lean comments removed first.
#
# Why this exists: `agent2-citations.sh` (and `unused-theorems.sh`) count every
# textual occurrence of a name, and this development documents itself heavily —
# module docstrings and declaration docstrings name other theorems constantly.
# A theorem mentioned three times in prose and never applied in a tactic block is
# uncited for the audit's purpose (label `U`), but both earlier scripts report it
# as used. This strips `--` line comments, `/- … -/` block comments and
# `/-- … -/` / `/-! … -/` docstrings before counting, so what remains is code:
# declaration signatures, `have`/`calc` statements and tactic scripts.
#
# It also reports `dup`, the number of *declarations* anywhere in the package
# whose final name component equals this one. `dup > 1` means the count is a
# union over namespaces and must be resolved by hand — that is the known
# under-reporting mode of `unused-theorems.sh`, made visible instead of implicit.
#
# Output is TSV: name, module, simp, dup, self, other, citers — where `self` and
# `other` are code occurrences outside the declaration's own signature line.
#
# Method note: the comment stripper is a line-oriented state machine over nesting
# depth of `/-` … `-/`. It is an approximation (a `/-` inside a string literal
# would fool it); the development contains no such literal, and the counts are a
# candidate list for hand review exactly as `unused-theorems.sh`'s are.
#
# Usage: scripts/agent2-uses.sh
set -e
cd "${0:A:h}/.."
pkg="ScottDomains/ScottDomains"

mods=(Projection FinitaryProjection NormalSubposet NormalProjection Theorem6 \
      FinitaryProjectionPoset FinitaryProjectionEmbedding Bifinite \
      MinimalUpperBounds Section62 SFP)

allsrc=(${(f)"$(find $pkg -name '*.lean' | sort)"})

work=$(mktemp -d /tmp/agent2-uses-XXXXXX)

strip_comments() {
  awk '
    {
      line = $0; out = ""; i = 1; n = length(line)
      while (i <= n) {
        two = substr(line, i, 2)
        if (depth == 0 && two == "--") { break }
        if (two == "/-") { depth++; i += 2; continue }
        if (two == "-/") { if (depth > 0) depth--; i += 2; continue }
        if (depth == 0) { out = out substr(line, i, 1) }
        i++
      }
      print out
    }
  ' "$1"
}

# Build the comment-stripped mirror of every source file.
for g in $allsrc; do
  m=${g#$pkg/}
  d="$work/${m:h}"
  [[ "${m:h}" == "$m" ]] && d="$work"
  mkdir -p "$d"
  strip_comments "$g" > "$work/$m"
done

# All declaration final-name components in the package, for the duplicate check.
grep -hE '^(@\[[^]]*\] )?(theorem|lemma) ' $allsrc \
  | sed -E 's/^(@\[[^]]*\] )?(theorem|lemma) +//; s/[ ({:\[].*$//; s/^.*\.//' \
  | sort > "$work/.allnames"

print -r -- "name\tmodule\tsimp\tdup\tself\tother\tciters"
for m in $mods; do
  f="$pkg/$m.lean"
  while IFS= read -r line; do
    simp="-"
    [[ "$line" == @\[*simp* ]] && simp="simp"
    nm=$(print -r -- "$line" | sed -E 's/^(@\[[^]]*\] )?(theorem|lemma) +//; s/[ ({:\[].*$//')
    short="${nm##*.}"
    dup=$(grep -c -x -F -- "$short" "$work/.allnames" || true)
    self=0; other=0; citers=""
    for g in $allsrc; do
      gm=${g#$pkg/}
      c=$(grep -c -w -F -- "$short" "$work/$gm" || true)
      (( c == 0 )) && continue
      if [[ "$gm" == "$m.lean" ]]; then
        d=$(grep -cE "^(@\[[^]]*\] )?(theorem|lemma) +($short|[A-Za-z0-9_.]*\.$short)([ ({:\[]|$)" "$work/$gm" || true)
        self=$(( c - d ))
      else
        other=$(( other + c ))
        citers="$citers $gm:$c"
      fi
    done
    print -r -- "$short\t$m\t$simp\t$dup\t$self\t$other\t$citers"
  done < <(grep -hE '^(@\[[^]]*\] )?(theorem|lemma) ' "$f")
done

rm -rf "$work"
