# ScottDomains

A Lean 4 / Mathlib formalization of **domain theory**, developed directly from
one paper:

> **C. A. Gunter and D. S. Scott, "Semantic Domains,"** in *Handbook of
> Theoretical Computer Science*, Volume B (ed. J. van Leeuwen), North-Holland,
> 1990, pp. 633–674.

That paper is our **specification**. We work through its development in order —

1. §2 cpo's and the Fixed-Point Theorem
2. §3 effectively presented domains (compact elements, algebraic, bounded-complete, finitary projections)
3. §4 operators and functions (products, smash products, sums, lifts, function spaces)
4. §5 powerdomains
5. §6 bifinite (SFP) domains
6. §7 recursive definitions of domains (`D∞`)

— formalizing each definition and theorem in Lean, **reusing Mathlib** where it
already provides a piece and **defining the rest** (notably the way-below
relation `≪`, which Mathlib lacks).

The paper — a copy provided by **D. Scott** himself, whose distribution to us is
permitted under the publisher's author terms — is in
[`papers/Gunter Scott 1990.pdf`](papers/Gunter%20Scott%201990.pdf).

## Layout

- [`ScottDomains.lean`](ScottDomains.lean) — root module; re-exports the Mathlib foundations we build on.
- [`ScottDomains/ExistingTheories.lean`](ScottDomains/ExistingTheories.lean) — clickable `#check` catalog of the Mathlib pieces we reuse.
- [`docs/PaperInventory.md`](docs/PaperInventory.md) — every definition and theorem in the paper, with a column for its Lean/Mathlib status (the work list).
- [`papers/`](papers/) — the source paper.

## Status

Framing complete: the project builds green (`lake build` → 924 jobs, 0 errors,
0 `sorry`). The domain-theory development itself — the classes, the `≪`
relation, and the theorems — is **not yet started**. `docs/PaperInventory.md` is
the plan, mapped section-by-section to the paper; the next step is to fill in its
"In Lean / Mathlib?" column, then formalize.
