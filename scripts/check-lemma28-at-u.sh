#!/bin/zsh
# check-lemma28-at-u.sh — how many of Lemma 28's nine conjuncts hold over the
# paper's own carrier once r0037's two Lemma 28 streams are put together?
#
# agent3 (ScottDomains.PRepFun) proved `→`, `⇸` and `⊗` conditionally on the
# paper's retraction pair. agent4 (ScottDomains.PRepSum) derived that pair at
# `Dyadic.U` from the now-unconditional `Atomless.thm27`, as `pairAtU`, and used
# it to land four conjuncts at `U`. Neither could do the other's half: agent3
# deliberately did not attempt the instantiation, to avoid colliding with agent4.
#
# So the join is the orchestrator's, and `lake build` cannot report it — it never
# imports two unrelated modules into one environment. This elaborates the three
# instantiations directly, in one allowlisted command with no chaining.
#
# The per-conjunct obligation is Theorem 27's: the operator's *result* must be a
# bounded complete domain. `Domain` comes from agent3's new `strictHomDomain` and
# `smashDomain`; bounded completeness is Lemma 10, which is why agent4's report
# says Lemma 10 and Lemma 28 compose.
set -e
cd "${0:A:h}/.."
pkg="$PWD/ScottDomains"

src=$(mktemp /tmp/lemma28-at-u-XXXXXX.lean)
cat > "$src" <<'LEAN'
import ScottDomains.PRepFun
import ScottDomains.PRepSum

open ScottDomains

/-- `→` is p-representable over the paper's `U`, with no hypothesis. -/
theorem repArrowAtU : BifiniteUniversal.IsPRepresentable₂ Dyadic.U PRep.funOp := by
  haveI : Domain (ScottHom Dyadic.U Dyadic.U) := inferInstance
  haveI : BoundedComplete (ScottHom Dyadic.U Dyadic.U) := inferInstance
  obtain ⟨_fn, _gr, hfg, hgf⟩ := PRepSum.pairAtU (ScottHom Dyadic.U Dyadic.U)
  exact PRepFun.rep_arrow hfg hgf

/-- `⇸` is p-representable over the paper's `U`, with no hypothesis. -/
theorem repStrictArrowAtU : BifiniteUniversal.IsPRepresentable₂ Dyadic.U PRep.strictFunOp := by
  haveI : Domain (StrictHom Dyadic.U Dyadic.U) := PRepFun.strictHomDomain
  haveI : BoundedComplete (StrictHom Dyadic.U Dyadic.U) := lem10_strict
  obtain ⟨_fn, _gr, hfg, hgf⟩ := PRepSum.pairAtU (StrictHom Dyadic.U Dyadic.U)
  exact PRepFun.rep_strictArrow hfg hgf

/-- `⊗` is p-representable over the paper's `U`, with no hypothesis. -/
theorem repSmashAtU : BifiniteUniversal.IsPRepresentable₂ Dyadic.U PRep.smashOp := by
  haveI : Domain (Smash Dyadic.U Dyadic.U) := PRepFun.smashDomain
  haveI : BoundedComplete (Smash Dyadic.U Dyadic.U) := lem10_smash
  obtain ⟨_fn, _gr, hfg, hgf⟩ := PRepSum.pairAtU (Smash Dyadic.U Dyadic.U)
  exact PRepFun.rep_smash hfg hgf

#print axioms repArrowAtU
#print axioms repStrictArrowAtU
#print axioms repSmashAtU
LEAN

cd "$pkg"
lake env lean "$src"
echo "Lemma 28 at U: agent3's three conjuncts lift, taking the count 4 of 9 -> 7 of 9"
