/-
ScottDomains — Dana Scott's domain theory in Lean 4 / Mathlib.

Root module of the ScottDomains library, split out from `Playground` so the
domain-theory development lives on its own.  It re-exports the Mathlib
foundations we build on.  For what Mathlib does and does not provide (there is no
packaged "Scott domain", and no D∞), see `notes/ScottDomainsInLean.pdf`.

NOTE on Lean syntax: `import` lines must come before any declaration, so this
header is a plain block comment (not a `/-! -/` module docstring, which would
have to follow the imports).
-/

-- ω-complete partial orders (ωCPOs) and ω-continuous maps: the directed-complete
-- order structure underlying denotational semantics (limits of approximations).
import Mathlib.Order.OmegaCompletePartialOrder

-- Complete partial orders (directed-complete): the dcpo layer sitting above ωCPOs.
import Mathlib.Order.CompletePartialOrder

-- Scott continuity: monotone maps preserving directed suprema.  The Mathlib
-- file's docstring credits Dana Scott by name.
import Mathlib.Order.ScottContinuity

-- The Scott topology on an ordered type (opens are upper sets inaccessible by
-- directed suprema); for it, Scott-continuity IS topological continuity.
import Mathlib.Topology.Order.ScottTopology

-- Knaster–Tarski and Kleene least/greatest fixed points (`OrderHom.lfp`/`gfp`,
-- `LawfulFix`): Scott's account of recursion as the least fixed point ⨆ₙ fⁿ(⊥).
import Mathlib.Order.FixedPoints
