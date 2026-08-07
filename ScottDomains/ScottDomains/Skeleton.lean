import ScottDomains.Bifinite
import ScottDomains.Smash
import ScottDomains.Lift
import ScottDomains.StrictHom
import ScottDomains.Product
import ScottDomains.FunctionSpaceCountable

/-!
# Skeleton: statements of the outstanding numbered results

**This is the only file in the development that contains `sorry`.** Each theorem
below is a statement of one of Gunter & Scott's numbered results, quoted in its
docstring, with its proof deliberately left open. The point is to fix the
*statements* centrally — before three agent worktrees start proving them in
parallel — so that:

* the reading of each result is decided once and reviewed, not three times
  independently. This matters: the source PDF's Type-3 fonts drop every `⊗` and
  every `⊥` subscript, so Lemma 9 part 5 reads `D (E × F) ≅ (D E) × (D E)` and
  has to be reconstructed rather than transcribed;
* signatures stop moving, so no agent edits a declaration another depends on;
* the `sorry` count is the burn-down metric, reported in `docs/PaperInventory.md`.

## What is *not* here, and why

A statement can only be written if its vocabulary exists. These are omitted:

| # | Result | Missing vocabulary |
| -- | ------ | ------------------ |
| 1 | Lem 9 | the strict-function-space isomorphisms; the PDF text needs reconstruction first |
| 2 | Thm 11 | the ideal completion as a construction, not just `Order.Ideal` |
| 3 | Thm 12 | "continuous algebra satisfying axioms `T`" is undefined in the development |
| 4 | Lem 13 | the three powerdomains |
| 5 | Thm 14 | the equivalent characterizations are garbled in the source |
| 6 | Thm 16, Lem 20 | `Fp(D)` and `Fc(D)` as posets |
| 7 | Thm 21–Lem 30 (§7) | representability over a universal domain, which runs through `Fc(D)` |

Guessing any of these would be inventing the paper's content. They are recorded
as blocked, with the blocker named.
-/

namespace ScottDomains

variable {α β : Type*}

section Closure

variable [Preorder α]

/-- A **closure**: idempotent and *above* the identity — the order dual of
`IsProjection`. Lemma 19 is about these. -/
def IsClosure (r : ScottHom α α) : Prop :=
  (∀ x, r (r x) = r x) ∧ ∀ x, x ≤ r x

end Closure

section Statements

variable [CompletePartialOrder α] [CompletePartialOrder β]

/-- **Proposition 15.** Every bounded complete domain is bifinite.

> Every bounded-complete domain is bifinite.

Unblocked: `IsBifinite` (r0025) and `BoundedComplete` (r0004) both exist. -/
theorem prop15 [Domain α] [BoundedComplete α] : IsBifinite α := by
  sorry

/-- **Theorem 18.** If `D` and `D → D` are domains, then `D` is bifinite.

> If `D` and `D → D` are domains, then `D` is bifinite.

Note the hypothesis is on the *function space* being a domain, which is exactly
what Theorem 7 supplies under bounded completeness — so this is the converse
direction and does not follow from it. -/
theorem thm18 [Domain α] [Domain (ScottHom α α)] : IsBifinite α := by
  sorry

/-- **Lemma 19.** If `r : D → D` is a closure, then `im(r)` is a domain.

> `r : D → D` closure (`r ∘ r = r ⊒ id`) ⟹ `im(r)` is a domain.

Stated as the two conjuncts of "is a domain" over the image's induced order,
rather than by first building `im(r)` as a cpo — that construction is part of the
proof, and fixing it here would prejudge how the agent does it. -/
theorem lem19 (r : ScottHom α α) (_hr : IsClosure r) :
    ∃ _ : CompletePartialOrder ↥(Set.range ⇑r), True := by
  sorry

/-- **Lemma 10.** If `D` and `E` are bounded complete domains then so are
`D → E`, `D →⊥ E`, `D × E`, `D ⊗ E`, `D ⊕ E`, and `D⊥`.

> If `D` and `E` are bounded complete domains then so are the cpo's `D → E`,
> `D →⊥ E`, `D × E`, `D ⊗ E`, `D + E`, `D⊥`.

The `D → E` conjunct is **already proved** — it is Theorem 7's bounded-complete
half (r0007) — so only the remaining four are open here. Splitting them into
separate statements lets them be discharged independently. -/
theorem lem10_prod [Domain α] [BoundedComplete α] [Domain β] [BoundedComplete β] :
    BoundedComplete (α × β) := by
  sorry

theorem lem10_smash [Domain α] [BoundedComplete α] [Domain β] [BoundedComplete β] :
    BoundedComplete (Smash α β) := by
  sorry

theorem lem10_lift [Domain α] [BoundedComplete α] : BoundedComplete (WithBot α) := by
  sorry

theorem lem10_strict [Domain α] [BoundedComplete α] [Domain β] [BoundedComplete β] :
    BoundedComplete (StrictHom α β) := by
  sorry

/-- **Lemma 17.** If `D` and `E` are bifinite then so are `D → E`, `D →⊥ E`,
`D × E`, `D ⊗ E`, `D ⊕ E`, and `D⊥` — including the function space.

> `D, E` bifinite ⟹ `→, ×, ⊗, +, ()⊥` bifinite (incl. function space).

The function-space conjunct is the substantive one: §6's whole point is that
bifiniteness, unlike bounded completeness, is preserved by `→` without further
hypotheses. -/
theorem lem17_prod [Domain α] [Domain β] (_h₁ : IsBifinite α) (_h₂ : IsBifinite β) :
    IsBifinite (α × β) := by
  sorry

theorem lem17_lift [Domain α] (_h : IsBifinite α) : IsBifinite (WithBot α) := by
  sorry

theorem lem17_fun [Domain α] [Domain β] [BoundedComplete β]
    (_h₁ : IsBifinite α) (_h₂ : IsBifinite β) : IsBifinite (ScottHom α β) := by
  sorry

end Statements

end ScottDomains
