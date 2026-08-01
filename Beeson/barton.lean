import tactic.core

section

open lean lean.parser

@[user_command] meta def axioms_all2 (_ : interactive.parse $ tk "#axioms_all") : parser unit :=
do e ← get_env,
   e.fold (return ()) (λ d rest, do
     when (e.in_current_file d.to_name)
       (do emit_command_here ("#check @" ++ d.to_name.to_string),
           emit_command_here ("#print axioms " ++ d.to_name.to_string),
           return ()),
     rest),
   return ()

end