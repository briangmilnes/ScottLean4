import ScottDomains.ClosureProperties.SeparatedSum
import ScottDomains.ClosureProperties.StrictFunction
import ScottDomains.ClosureProperties.Powerdomain
import ScottDomains.Skeleton.Lemma10
import ScottDomains.Skeleton.Sum

/-!
# Lemma 10 and Lemma 17, each stated as one theorem

Gunter & Scott, *Semantic Domains*, §4.5 and §6.2, quoted from the source PDF:

> **Lemma 10** If `D` and `E` are bounded complete domains then so are the cpo's
> `D → E`, `D →⊥ E`, `D × E`, `D ⊗ E`, `D + E`, `D ⊕ E`, `D⊥`.

> **Lemma 17** If `D` and `E` are bifinite domains, then so are the cpo's
> `D → E`, `D →⊥ E`, `D × E`, `D ⊗ E`, `D + E`, `D ⊕ E`, `D⊥`, `D♮`, `D♯` and
> `D♭`.

Each lemma is a **conjunction over a list of operators**, and until r0034 the
development held its conjuncts as separate theorems in three files, which is how
two of them went missing without the loss being visible: `+` (the separated sum,
`D⊥ ⊕ E⊥`) was read as a second name for `⊕` (the coalesced sum), and the three
powerdomain conjuncts were dropped from the paper extraction together with the
glyphs `♮`, `♯` and `♭` — `pdftotext` renders them `\`, `]` and `[`.

The two theorems below close that hole by construction: the conjunct count is
part of the statement, so a missing conjunct is a type error rather than an
absence. Nothing here is a new proof — each conjunct is a named theorem proved
elsewhere, listed here in the paper's order.

| # | operator | Lemma 10 | Lemma 17 |
| - | -------- | -------- | -------- |
| 1 | `D → E`  | `ScottHom`'s `BoundedComplete` instance (Theorem 7, r0007) | `lem17_fun` (r0027) |
| 2 | `D →⊥ E` | `lem10_strict` (r0027) | `lem17_strictFun` (r0034) |
| 3 | `D × E`  | `lem10_prod` (r0027) | `lem17_prod` (r0027) |
| 4 | `D ⊗ E`  | `lem10_smash` (r0027) | `lem17_smash` (r0028) |
| 5 | `D + E`  | `lem10_separated` (r0034) | `lem17_separated` (r0034) |
| 6 | `D ⊕ E`  | `lem10_sum` (r0028) | `lem17_sum` (r0028) |
| 7 | `D⊥`     | `lem10_lift` (r0027) | `lem17_lift` (r0027) |
| 8 | `D♮`     | — | `lem17_plotkin` (r0034) |
| 9 | `D♯`     | — | `lem17_smyth` (r0034) |
| 10 | `D♭`    | — | `lem17_hoare` (r0034) |

## The hypotheses are the paper's, and no more

Lemma 10 is stated for *bounded complete domains*, which in this development is
the instance pair `[Domain _] [BoundedComplete _]` (`Domain.lean` — the paper
composes two separate predicates and never names the composite).

Lemma 17 is stated for *bifinite domains*, and `IsBifinite` is `Prop`-valued, so
it appears as an explicit hypothesis rather than an instance. Two extra instance
arguments appear that the paper's sentence does not name:

* `[BoundedComplete β]` — needed by the `→` and `→⊥` conjuncts only, and not by
  the paper's argument for them either: it is what makes `D → E` a *domain* at
  all in the development's construction (Theorem 7), through the step-function
  decomposition of a compact function. §6 exists because bifiniteness does not
  need it, and removing this hypothesis is a real open item, not a formality.
* `[Domain _]` on each operand — the countability half is what Theorem 11
  consumes to make the three powerdomains domains.

The three powerdomain conjuncts are unary: they are claims about `D` alone, so
they are stated at `α`.
-/

namespace ScottDomains.ClosureProperties

open ScottDomains

universe u

variable {α β : Type u} [CompletePartialOrder α] [CompletePartialOrder β]

/-- **Lemma 10, all seven conjuncts.** If `D` and `E` are bounded complete
domains then so are `D → E`, `D →⊥ E`, `D × E`, `D ⊗ E`, `D + E`, `D ⊕ E` and
`D⊥`. Each component is the theorem named in the module docstring's table; the
value of the conjunction is that the count is checked by the kernel. -/
theorem lemma10 [Domain α] [BoundedComplete α] [Domain β] [BoundedComplete β] :
    BoundedComplete (ScottHom α β) ∧
    BoundedComplete (StrictHom α β) ∧
    BoundedComplete (α × β) ∧
    BoundedComplete (Smash α β) ∧
    BoundedComplete (SeparatedSum α β) ∧
    BoundedComplete (CoalescedSum α β) ∧
    BoundedComplete (WithBot α) :=
  ⟨inferInstance, lem10_strict, lem10_prod, lem10_smash, lem10_separated, lem10_sum, lem10_lift⟩

/-- **Lemma 17, all ten conjuncts.** If `D` and `E` are bifinite domains then so
are `D → E`, `D →⊥ E`, `D × E`, `D ⊗ E`, `D + E`, `D ⊕ E`, `D⊥`, `D♮`, `D♯` and
`D♭`. -/
theorem lemma17 [Domain α] [Domain β] [BoundedComplete β]
    (h₁ : IsBifinite α) (h₂ : IsBifinite β) :
    IsBifinite (ScottHom α β) ∧
    IsBifinite (StrictHom α β) ∧
    IsBifinite (α × β) ∧
    IsBifinite (Smash α β) ∧
    IsBifinite (SeparatedSum α β) ∧
    IsBifinite (CoalescedSum α β) ∧
    IsBifinite (WithBot α) ∧
    IsBifinite (Plotkin.Powerdomain α) ∧
    IsBifinite (Smyth.Powerdomain α) ∧
    IsBifinite (Hoare.Powerdomain α) :=
  ⟨lem17_fun h₁ h₂, lem17_strictFun h₁ h₂, lem17_prod h₁ h₂, lem17_smash h₁ h₂,
    lem17_separated h₁ h₂, lem17_sum h₁ h₂, lem17_lift h₁,
    lem17_plotkin h₁, lem17_smyth h₁, lem17_hoare h₁⟩

end ScottDomains.ClosureProperties
