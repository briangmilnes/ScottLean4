/- a1-r52-sigs.lean — body for `scripts/a6-env-scan.sh`: print the exact
elaborated signature of every claim `def` round r0052 converts and of every
reduction theorem it proves the derived claims through.

Written because the binder lists come from `variable` blocks spread over several
sections; reading them off the source risks getting an implicit/instance binder
wrong, and the new `_unproven` theorems have to state them exactly. -/

#check @ScottDomains.LemThirty.Theorem29Normal
#check @ScottDomains.LemThirty.Theorem29SecondAtDomains
#check @ScottDomains.LemThirty.Lemma30AtV
#check @ScottDomains.Colimit.Lemma30Arrow
#check @ScottDomains.Effective.StepFunctionsDecidable
#check @ScottDomains.Effective.Theorem7ArrowRecursive
#check @ScottDomains.Effective.Theorem7StrictRecursive
#check @ScottDomains.R49.Agent3.ScottHomCRecursive
#check @ScottDomains.R49.Agent3.StrictHomCRecursive
#check @ScottDomains.R49.Agent3.StrictStepFunctionsDecidable

#check @ScottDomains.LemThirty.theorem_29_secondAtDomains_of_thm29Normal
#check @ScottDomains.R49.Agent6.lemma_30_atV_of_thm29Normal
#check @ScottDomains.R45.Agent3.lemma_30_arrow_of_lemma30AtV
#check @ScottDomains.R49.Agent3.stepFunctionsDecidable_of_scottHomC
#check @ScottDomains.R47.Agent2.theorem_7_arrowRecursive_of_scottHomC
#check @ScottDomains.R49.Agent3.strictStepFunctionsDecidable_of_strictHomC
#check @ScottDomains.R49.Agent3.theorem_7_strictRecursive_of_residue
#check @ScottDomains.R47.Agent3.preservesRecursivePresentation_arrowOp_iff
