/-
r0049, agent7 — re-measure the thirteen `S≠` rows attributable to this
development, plus the two `S≠` rows that r0047 moved, against the **built**
environment rather than against the r0044 reports.

NOT part of the package: it lives in `scripts/`, outside
`ScottDomains/ScottDomains/`, so `lake build` never elaborates it and
`scripts/counts.sh` never counts it. Run it with

    scripts/a1-probe.sh /home/milnes/projects/ScottLean4-agent7/scripts/a7-r49-rows.lean

Why it exists: the round's evidence rule is that the plan is not evidence and
recorded blockers are re-derived. r0044 measured the rows one round before
r0047 removed `[BoundedComplete β]` from six declarations, so the row table in
that report is stale by construction. Every type below is `#check @d` against the
`.olean`, never read off a source line, and every axiom footprint is
`#print axioms` in the same run.
-/
import ScottDomains.Kleene.Graph
import ScottDomains.JungSFP
import ScottDomains.PRepFun
import ScottDomains.ClosureProperties
import ScottDomains.JungFinite
import ScottDomains.PowerdomainMap
import ScottDomains.Universality
import ScottDomains.Combinator
import ScottDomains.A4Lemma17Fun
import ScottDomains.A4FunctionSpaceBifinite
import ScottDomains.A7Thm26Arity
import ScottDomains.A7SneqRows

section Rows

-- row 45 — the recovery equation
#check @ScottDomains.Kleene.sSup_recoverAt
#check @ScottDomains.R49.Agent7.sSup_recoverAt_bcFree
#print axioms ScottDomains.R49.Agent7.sSup_recoverAt_bcFree
#print axioms ScottDomains.R49.Agent7.directedOn_recoverAt_bcFree
#print axioms ScottDomains.R49.Agent7.eq_of_graphPairs_eq_bcFree
#print axioms ScottDomains.R49.Agent7.sSup_recoverAt_imp_old
#print axioms ScottDomains.R49.Agent7.eq_of_graphPairs_eq_imp_old

-- row 53 — the existential witness
#check @ScottDomains.JungSFP.lemma213

-- row 59 — the strict step functions
#check @ScottDomains.PRepFun.strictHomIsAlgebraic

-- rows Lemma 17 `→` and `⊸` — r0047's removals
#check @ScottDomains.lem17_fun
#check @ScottDomains.ClosureProperties.lem17_strictFun
#check @ScottDomains.R47.Agent4.lem17_fun
#check @ScottDomains.R47.Agent4.lem17_strictFun

-- row p9b — the stabilizing index
#check @ScottDomains.JungFinite.mubDiff_nonempty
#check @ScottDomains.mubClosure_subset_of_isNormalIn
#check @ScottDomains.R49.Agent7.exists_mubIter_eq_succ_of_isNormalIn
#print axioms ScottDomains.R49.Agent7.exists_mubIter_eq_succ_of_isNormalIn
#print axioms ScottDomains.R49.Agent7.mubIter_subset_of_isNormalIn
#print axioms ScottDomains.R49.Agent7.finite_mubClosure_of_isNormalIn

-- row p16 — the Lemma 17 `♮` sketch
#check @ScottDomains.PowerdomainMap.isProjection_plotkin
#print ScottDomains.ScottHom.IsProjection
#print ScottDomains.ScottHom.IsFinitaryProjection

-- rows Lemma 24 a/b and Theorem 25 a/b/c — "is a domain"
#check @ScottDomains.Universality.lem24
#check @ScottDomains.Universality.thm25

-- row Theorem 26 — the positivity binder
#check @ScottDomains.Combinator.thm26
#check @ScottDomains.R49.Agent7.Thm26Printed
#check @ScottDomains.R49.Agent7.not_thm26Printed_of_two_zero_arities
#print axioms ScottDomains.R49.Agent7.not_thm26Printed_of_two_zero_arities
#print axioms ScottDomains.R49.Agent7.not_thm26_statement_of_zero_arity
#print axioms ScottDomains.R49.Agent7.isAlgEmbedding_const_of_subsingleton
#print axioms ScottDomains.R49.Agent7.isSubalgebraOf_range
#print axioms ScottDomains.R49.Agent7.combEval_eq_of_zero_arity
#print axioms ScottDomains.R49.Agent7.exists_map_eq

end Rows
