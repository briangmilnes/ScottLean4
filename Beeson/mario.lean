import tactic.core

section

open lean lean.parser

@[user_command] meta def axioms_all (_ : interactive.parse $ tk "#axioms_all") : parser unit :=
do info ← option.is_some <$> optional (tk "?"),
  e ← get_env,
  e.fold (return ()) (λ d rest, do
    when (e.in_current_file d.to_name) (do
      when info $ emit_command_here ("#eval tactic.trace `" ++ d.to_name.to_string) $> (),
      emit_command_here ("#print axioms " ++ d.to_name.to_string) $> ()),
    rest)


meta def environment.is_builtin (env : environment) (n : name) : bool :=
env.is_inductive n || env.is_recursor n || env.is_constructor n ||
to_bool (n ∈ [``quot, ``quot.lift, ``quot.ind, ``quot.mk])

meta def tactic.get_axioms_used_aux (env : environment) : name →
  list name × name_set → tactic (list name × name_set)
| n p@(l, ns) := if ns.contains n then pure p else do
  d ← env.get n,
  let ns := ns.insert n,
  let process (v : expr) : tactic (list name × name_set) := (do
    v.fold (pure (l, ns)) $ λ e _ r, r >>= λ p,
      if e.is_constant then tactic.get_axioms_used_aux e.const_name p else pure p),
  match d with
  | (declaration.defn _ _ _ v _ _) := process v
  | (declaration.thm _ _ _ v)      := process v.get
  | _ := pure $ if env.is_builtin n then (l, ns) else (n::l, ns)
  end

meta def tactic.get_axioms_used (n : name) : tactic (list name) :=
do env ← tactic.get_env,
  prod.fst <$> tactic.get_axioms_used_aux env n ([], mk_name_set)



@[user_attribute]
meta def intuit_attr : user_attribute unit unit :=
{ name   := `intuit,
  descr  := "intuit",
  after_set := some $ λ n _ _, do
    l ← tactic.get_axioms_used n,
    guard (``classical.choice ∉ l) <|>
    tactic.fail "ERROR: classical axioms used" }

end 
/- 
#eval tactic.get_axioms_used `classical.em >>= tactic.trace
 -- [propext, quot.sound, classical.choice]


@[intuit] theorem bad (p) : ¬ (p ↔ ¬ p) := -- fail
by by_cases p; simp

@[intuit] theorem good (p) : ¬ (p ↔ ¬ p) := -- ok
λ h, have ¬ p, from λ i, h.1 i i, this (h.2 this)
-/ 