/-!
r0044 / agent3 — Class 2 (vacuity) instrument 3: **hypothesis deletion**.

Instrument 2 (`scripts/a3-vacuity-body.lean`) is a static analysis: it reports
binders that occur in neither the statement nor the proof term (SECTION 1), and
theorem binders that are data, occur in the proof, but occur nowhere in the
statement (SECTION 2).  SECTION 1 needs no further evidence — a binder occurring
in neither is removable by strengthening, which is a theorem of the calculus, and
is what Batteries' `unusedArguments` linter is documented to detect.

SECTION 2 does need further evidence, and this file supplies it.  A theorem
`∀ (h : T), Q` with `h ∉ Q` is no stronger than `Q` exactly when `T` is inhabited
for every instantiation of the ambient binders.  Each `example` below restates a
SECTION 2 candidate **with the hypothesis deleted** and proves it.  An `example`
that elaborates is a machine-checked demonstration that the deleted hypothesis
bought nothing; one that fails to elaborate exonerates the theorem.

Each block also records the paper row it belongs to, since the point of the sweep
is whether an `S+P` label is honest.

Generated into `scripts/a3-delete.lean` by `scripts/a3-gen.sh`; run with
`scripts/a3-run-lean.sh a3-delete`.
-/

namespace A3Delete

open ScottDomains ScottDomains.Effective

variable {α β : Type*} [CompletePartialOrder α] [Domain α]
  [CompletePartialOrder β] [Domain β] [BoundedComplete β]

/-! ### Row 13 — Theorem 7, second sentence (`Effective.theorem7_arrow`)

The theorem is `(d : EffectivePresentation α) → (e : EffectivePresentation β) →
Nonempty (EffectivePresentation (ScottHom α β))`.  `d` and `e` are used in its
proof term (they build `scottHom`'s step-function enumeration), so it is not
proof-vacuous.  The question SECTION 2 raises is whether the *statement* needs
them.  `Domain (ScottHom α β)` is a registered instance
(`FunctionSpaceCountable`), so `nonempty_effectivePresentation` applies directly:
-/
example : Nonempty (EffectivePresentation (ScottHom α β)) :=
  nonempty_effectivePresentation _

/-! ### Rows for `theorem7_strict` and `operator_preserves_effectivePresentation`

Both are SECTION 1 hits (hypotheses `_d`, `_e` dead in the proof term as well).
The deleted-hypothesis forms, for completeness: -/
example [Domain (StrictHom α β)] : Nonempty (EffectivePresentation (StrictHom α β)) :=
  nonempty_effectivePresentation _

example {γ : Type*} [CompletePartialOrder γ] [Domain γ] :
    Nonempty (EffectivePresentation γ) :=
  nonempty_effectivePresentation _

/-! ### The control: `EffectivePresentation` is inhabited, `RecursivePresentation` is not

The first `example` is the trivial-inhabitedness fact that makes the three above
work.  The second is *commented out* deliberately: `RecursivePresentation` has no
term in this development, so an analogous `example` does not elaborate, which is
the check that the distinction instrument 3 draws is a real one and not an
artifact of the method. -/
example (γ : Type*) [CompletePartialOrder γ] [Domain γ] :
    Nonempty (EffectivePresentation γ) :=
  nonempty_effectivePresentation γ

-- example (γ : Type*) [CompletePartialOrder γ] [Domain γ] :
--     Nonempty (RecursivePresentation γ) := by exact?   -- no term exists

/-! ### The eight Skeleton rows are NOT this failure mode

`lem10_prod`, `lem10_lift`, `lem10_strict`, `lem10_sum`, `lem17_prod`,
`lem17_lift`, `lem17_sum`, `lem17_smash` each carry a dead `[Domain _]` (and
`lem10_strict` a dead `[BoundedComplete α]`).  Those are SECTION 1 hits — the
hypothesis is redundant, so the theorem proved is *stronger* than the one
stated.  That is the opposite of vacuity and must not be counted as it.  The
check that `Domain` is not itself freely inhabited: it is a `Prop`-valued class
carrying `IsAlgebraic` plus `Set.Countable (compacts α)`, neither of which
`Classical.dec` supplies.  A witness that it is a real assumption — a
`CompletePartialOrder` that is not a `Domain` — is `Set ℝ` under `⊆`, whose
compact elements are the finite subsets of `ℝ`, an uncountable family; stated
here rather than proved, and flagged as such. -/

section SkeletonDeletion

variable {α β : Type*} [CompletePartialOrder α] [BoundedComplete α]
  [CompletePartialOrder β] [BoundedComplete β]

/-- `lem10_prod` with both `[Domain _]` binders deleted, proved by its own proof
script verbatim.  One machine-checked instance of the eight Skeleton section-1
rows; the other seven follow by the same strengthening step, since a binder
occurring in neither the type nor the value is removable in the calculus. -/
example : BoundedComplete (α × β) where
  isLUB_sSup_of_bddAbove s hs := by
    have hsup : (sSup s : α × β) = (sSup (Prod.fst '' s), sSup (Prod.snd '' s)) := rfl
    rw [isLUB_prod, hsup]
    exact ⟨isLUB_sSup_of_bddAbove (bddAbove_fst_image hs),
      isLUB_sSup_of_bddAbove (bddAbove_snd_image hs)⟩

end SkeletonDeletion

/-! ### What the underscore convention does *not* mean

agent2 reports `lem17_fun (_h₁ …) (_h₂ …)` with both underscore-prefixed
hypotheses used at `Skeleton/Lemma17.lean:422-423`.  This area supplies the same
datum independently: `lem17_prod (_h₁ : IsBifinite α) (_h₂ : IsBifinite β)` names
both hypotheses with a leading underscore and uses both, and the instrument's
section 1 flags only that theorem's `[Domain α]` and `[Domain β]` — not `_h₁` or
`_h₂`.  The instrument computes occurrence in the proof term and never reads the
binder's name; the `(underscored)` marker in its output is an annotation on a hit
already established by occurrence, never a reason for one. -/

end A3Delete
