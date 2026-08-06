import ScottDomains

/-!
# Existing theories — the Mathlib domain-theory definitions we build on, made clickable

`import` brings in whole *modules*, not individual symbols, so the root module
names no definitions to jump to.  This file names the key definition of each
**existing** Mathlib theory in a `#check`, turning it into a clickable table of
contents (the *new* Scott-domain classes we define will get their own files):
put the cursor on any name and go to its Mathlib definition —
`M-.` (Emacs lean4-mode), or F12 / ⌘-click (VS Code).
-/

-- Approximation order and limits of approximations
#check @OmegaCompletePartialOrder     -- ωCPO: chains have least upper bounds
#check @CompletePartialOrder           -- dcpo: directed sets have least upper bounds

-- Continuity (preserves directed suprema)
#check @ScottContinuous
#check @ScottContinuousOn

-- The Scott topology (for it, Scott-continuity = topological continuity)
#check @Topology.IsScott
#check @Topology.IsScottHausdorff

-- Recursion as least/greatest fixed points (Knaster–Tarski / Kleene)
#check @OrderHom.lfp
#check @OrderHom.gfp
