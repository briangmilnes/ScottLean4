#!/bin/zsh
# module-counts.sh — per-module size and declaration counts, with the *kinds* of
# declaration separated.
#
# Why this exists: `counts.sh` reports one number for the whole development
# (1308 theorem-ish declarations against a paper with 30 numbered results). That
# number alone cannot say whether the development is carrying necessary support
# or speculative API, because it does not distinguish a paper result from a
# `simp` lemma about a coercion. This breaks the same counting rule out per
# module and per kind so `docs/PropertiesVsTheorems.md` can be built from
# measurement rather than impression.
#
# "Theorem-ish" is counted exactly as counts.sh counts it — a line starting with
# `theorem` or `lemma`, optionally preceded by one attribute group — so the
# totals here sum to the total there. `def`/`abbrev`/`instance`/`structure` are
# reported separately and are NOT part of that total.
#
# Usage: scripts/module-counts.sh [--csv]
set -e
cd "${0:A:h}/.."
pkg="ScottDomains/ScottDomains"

fmt=${1:---table}
srcfiles=(${(f)"$(find $pkg -name '*.lean' | sort)"})

[[ $fmt == --csv ]] && print -r -- "module,lines,theorems,simp_theorems,private_theorems,defs,instances"
[[ $fmt == --table ]] && printf "%-46s %6s %6s %6s %6s %6s %6s\n" \
  module lines thms simp priv defs inst

tot_lines=0; tot_thms=0; tot_simp=0; tot_priv=0; tot_defs=0; tot_inst=0
for f in $srcfiles; do
  m=${f#$pkg/}
  l=$(wc -l < $f | tr -d ' ')
  t=$(grep -cE '^(@\[[^]]*\] )?(theorem|lemma) ' $f || true)
  s=$(grep -cE '^@\[[^]]*simp[^]]*\] (theorem|lemma) ' $f || true)
  p=$(grep -cE '^private (theorem|lemma) ' $f || true)
  d=$(grep -cE '^(noncomputable )?(def|abbrev) ' $f || true)
  i=$(grep -cE '^(noncomputable )?instance' $f || true)
  if [[ $fmt == --csv ]]; then
    print -r -- "$m,$l,$t,$s,$p,$d,$i"
  else
    printf "%-46s %6d %6d %6d %6d %6d %6d\n" $m $l $t $s $p $d $i
  fi
  tot_lines=$((tot_lines + l)); tot_thms=$((tot_thms + t)); tot_simp=$((tot_simp + s))
  tot_priv=$((tot_priv + p)); tot_defs=$((tot_defs + d)); tot_inst=$((tot_inst + i))
done

if [[ $fmt == --table ]]; then
  printf "%-46s %6d %6d %6d %6d %6d %6d\n" TOTAL \
    $tot_lines $tot_thms $tot_simp $tot_priv $tot_defs $tot_inst
fi
