/-
r0046 / agent5, Goal B — **the Mathlib-absence probe.**

NOT part of the package. Lives in `scripts/`, outside `ScottDomains/ScottDomains/`,
so `lake build` never sees it and `scripts/counts.sh` never counts it.
Run: `scripts/a5-r46-probe.sh scripts/a5-r46-mathlib.lean`.

**What it decides.** The sweep `scripts/a5-r46-sweep.sh` found 48 sentences of
class A — "Mathlib has no X", "Mathlib does not carry X", "there is no X". Each
is a decidable claim about the *whole* Mathlib environment, so this file imports
`Mathlib` (not the package root `ScottDomains`, which re-exports five Mathlib
order files and nothing else) and asks the elaborator.

The decision rule: `#check @Foo` on an absent constant is an **error**
("unknown identifier"), on a present one prints its type. `example ... := by
exact?`-free `#check` keeps this a pure name-resolution question, which is
exactly what "Mathlib has no `Foo`" asserts. Where the claim is about a
*statement* rather than a name, the probe writes the statement as an `example`
and lets `exact?`/`infer_instance` decide it.

Work: O(#claims) name resolutions; span: one elaboration of one file.
-/
import Mathlib

namespace A5R46Mathlib

/-! ## A2 — `Universality.lean:88`: "Mathlib has no `OrderIso.prodCongr`"

r0044's agent8 checked this and recorded it TRUE. Re-checked here so this round
does not have to take r0044's word for it. Expected: unknown constant. -/

-- #check @OrderIso.prodCongr   -- uncomment to see the error; kept commented so
                                -- the rest of the file elaborates.

/-- The *statement* `OrderIso.prodCongr` would have. If Mathlib carries it under
another name, `exact?` finds it; if the search fails the absence claim survives a
stronger test than name resolution. -/
example {α β γ δ : Type} [Preorder α] [Preorder β] [Preorder γ] [Preorder δ]
    (f : α ≃o γ) (g : β ≃o δ) : (α × β) ≃o (γ × δ) := by
  exact?

/-! ## A1 — `Effective/FunctionSpace.lean:300`: "Mathlib v4.32.2 has no
`Primcodable (Finset ℕ)` instance, so `ComputablePred` cannot be asked of a
predicate on `Finset ℕ` at all"

r0045's agent1 reported this FALSE via `Primcodable.ofDenumerable`. Decided here
by typeclass synthesis, which is the operative question: `ComputablePred p` for
`p : Finset ℕ → Prop` elaborates iff the instance is synthesizable. -/

/-- Instance synthesis, the exact question the claim answers "no" to. -/
example : Primcodable (Finset ℕ) := by infer_instance

/-- The stronger form: `ComputablePred` *can* be asked of a predicate on
`Finset ℕ`. If this elaborates, the sentence "cannot be asked … at all" is false
as written. -/
example (p : Finset ℕ → Prop) : Prop := ComputablePred p

/-- And the class is *inhabited* on `Finset ℕ`, not merely well-formed — so
"cannot be asked … at all" fails at both readings. -/
example : ComputablePred (fun _ : Finset ℕ => True) :=
  ComputablePred.computable_iff.2 ⟨fun _ => true, Computable.const true, by simp⟩

/-! ## A3 — `Effective/FunctionSpace.lean:335`: "**Mathlib has no bitwise
computability at all** — `Mathlib/Computability/` mentions no `Nat.bitwise`, and
there is no `Primrec` route through `binaryRec`"

The operative statement is the one the docstring says would be needed:
`Computable fun p : ℕ × ℕ => p.1 ||| p.2`. -/

example : Computable fun p : ℕ × ℕ => p.1 ||| p.2 := by
  exact?

/-! ## A4 — `ScottHom.lean:17`: "Mathlib has no dcpo function space. Its bundled
continuous-function type is `OmegaCompletePartialOrder.ContinuousHom` (`α →𝒄 β`),
which is ω-continuous … `ScottContinuous` is a predicate with composition and
constant lemmas but no bundled type and no closure result for suprema."

Three sub-claims, each a name-resolution question. -/

-- Sub-claim: the ω-continuous bundled type exists (asserted present).
#check @OmegaCompletePartialOrder.ContinuousHom
-- Sub-claim: `ScottContinuous` is a predicate (asserted present, unbundled).
#check @ScottContinuous
-- Sub-claim: composition and constant lemmas exist (asserted present).
#check @ScottContinuous.comp

/-! ## A6/A7 — `ComputableFunction.lean:70,87`: "Mathlib v4.32.2's `REPred` API is
five lemmas — `of_eq`, `Partrec.dom_re`, `ComputablePred.to_re`,
`computable_iff_re_compl_re`, `computable_iff_re_compl_re'` — and has neither
[conjunction nor projection]"; and `rePred_comp`: "Mathlib does not state it".

The five named lemmas are checked present; then the two asserted-absent
statements are posed as `example`s. -/

#check @REPred
#check @REPred.of_eq
#check @Partrec.dom_re
#check @ComputablePred.to_re
#check @ComputablePred.computable_iff_re_compl_re

/-- Asserted absent: r.e. predicates closed under conjunction. -/
example {σ : Type} [Primcodable σ] {p q : σ → Prop} (hp : REPred p) (hq : REPred q) :
    REPred fun a => p a ∧ q a := by
  exact?

/-- Asserted absent: r.e. predicates closed under projection along `ℕ`. -/
example {σ : Type} [Primcodable σ] {p : σ × ℕ → Prop} (hp : REPred p) :
    REPred fun a : σ => ∃ n, p (a, n) := by
  exact?

/-- `ComputableFunction.lean:87` — `rePred_comp`, asserted "Mathlib does not
state it". The development's own proof is `Partrec.comp hp hg`; the question is
whether a *named* Mathlib lemma states the composite. -/
example {σ τ : Type} [Primcodable σ] [Primcodable τ] {p : τ → Prop}
    (hp : REPred p) {g : σ → τ} (hg : Computable g) : REPred fun a => p (g a) := by
  exact?

/-! ## A8 — `JungNets.lean:102,146`: Iwamura's lemma, "chain-complete ⟺
directed-complete", asserted absent. The survey in that file records
`grep -rn "Iwamura\|Markowsky" Mathlib/` → 0 hits, and that
`ChainCompletePartialOrder` has an instance to `OmegaCompletePartialOrder` but
**none** to `CompletePartialOrder`. The instance half is decidable here. -/

#check @ChainCompletePartialOrder

/-- Asserted absent: the instance chain-complete ⟹ directed-complete. -/
example (α : Type) [PartialOrder α] [ChainCompletePartialOrder α] :
    CompletePartialOrder α := by
  exact?

/-! ## A5 — `Flat.lean:27`: "Mathlib has no discrete-order type synonym to feed
`WithBot`". A discrete-order synonym would be a type `T X` with `LE (T X)`
definitionally `Eq`/the discrete partial order. -/

-- Mathlib's order type synonyms, for the record: `OrderDual`, `Lex`,
-- `Antisymmetrization`, `WithBot`, `WithTop`. None is a discretization.
#check @OrderDual
#check @WithBot
#check @Antisymmetrization

end A5R46Mathlib
