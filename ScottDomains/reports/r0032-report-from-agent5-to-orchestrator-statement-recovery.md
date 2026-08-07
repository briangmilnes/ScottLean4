---
round: r0032
from: agent5
to: orchestrator
subject: statement-recovery
date: 2026-0806-21:30
started: 2026-0806-20:45
finished: 2026-0806-21:30
related:
  - plans/r0032-plan-from-orchestrator-to-agent5-statement-recovery.md
---

# r0032 agent5 — Lemma 9 and Theorem 14 recovered

**Both results are recovered. Nothing is rated unrecoverable.** Seven statements
landed with `sorry` bodies; the "not yet statable" count goes down by two
results, and the two inventory rows should change from `✗ not statable` to
`✗ prove`.

## Method: the glyphs are in the file, not missing from it

The plan's premise was that the characters are gone. They are not. `pdftotext`
drops them.

The PDF carries 18 embedded Type 3 bitmap fonts with `Custom` encoding and **no
`ToUnicode` map** (`pdffonts`). Their `/Encoding /Differences` arrays name every
glyph by its own code and nothing else (`0 /n00 /n01 /n02 /n03 8 /n08 10 /n0a
…`), so `pdftotext` has nothing to map `/n0a` to: codes ≥ `0x20` leak through as
ASCII — which is the whole of `SymbolMap.tex` Table A — and **codes < `0x20` are
dropped silently**, which is why `×`, `⊗`, `⊕`, `⊆` and `∘` are one blank gap.

But the codes are the standard TeX font codes, pinned by the leaked ASCII
(`0x21`→`→`, `0x32`→`∈`, `0x3F`→`⊥`, `0x76`→`⊑`, `0x68/0x69`→`⟨⟩` — all
`cmsy10` positions). So the page content stream decodes exactly. Extract it with
`mutool clean -d` + `mutool show -b`, decode each `Tj` against `cmsy10` /
`cmr10` / `cmmi10`, and the text comes back character for character. Rendering
the same page with `pdftocairo -png -r 300` and reading the image is the
independent check; it agrees everywhere.

Two findings that only this method yields: `≅` is set as `∼` (`0x18`) raised over
a `=` on the next line, and the **strict function arrow is two glyphs** —
`openbullet` (`0x0E`) butted onto `arrowright` (`0x21`), printing `o—→`. Both
`→` and `◦→` extract as `!`, so the extraction of Lemma 9 conflates two different
function spaces. That is the load-bearing distinction the plan warned to look
for, and it is the analogue of r0029's `Pf`-is-non-empty finding.

## Per result

| # | Result | Confidence | One-line justification |
| -- | ------ | ---------- | ---------------------- |
| 1 | Lemma 9.1 `D ⊗ E ≅ E ⊗ D` | **certain** | operator is `\n` = `0x0A` `circlemultiply`; Lemma 8.1 one line above carries `\002` = `multiply` in the identical position |
| 2 | Lemma 9.2 `(D ⊗ E) ⊗ F ≅ D ⊗ (E ⊗ F)` | **certain** | same decoding |
| 3 | Lemma 9.3 `(E ⊕ F) ◦→ D ≅ (E ◦→ D) × (F ◦→ D)` | **inferred** | printed `(E ◦→ D) × (E ◦→ F)` is false (10 vs 8 elements on `D = E = Prop`, `F = Prop × Prop`); the correction is the universal property of `⊕` the paper states three pages earlier |
| 4 | Lemma 9.4 `D ◦→ (E ◦→ F) ≅ (D ⊗ E) ◦→ F` | **certain** | decoded; the paper introduces `strict apply` / `strict curry` for it on the preceding page |
| 5 | Lemma 9.5 `D ⊗ (E ⊕ F) ≅ (D ⊗ E) ⊕ (D ⊗ F)` | **inferred** | printed `(D ⊗ E) ⊕ (D ⊗ E)` is false (5 vs 3 on the same witness); `F` occurs on the left and the second `E` is the only position it can occupy |
| 6 | Lemma 9.6 `D⊥ ◦→ E ≅ D → E` | **certain** | decoded `D` `0x3F` `0x0E 0x21` `E` `0x18 =` `D` `0x21` `E` |
| 7 | Theorem 14 `IsBifiniteViaProjections α ↔ Domain α ∧ IsBifinite α` | **certain** | the text was never garbled — only the `fi` ligature is dropped |

**The two misprints are refuted, not merely doubted.** One witness triple of
finite domains the development already carries instances for — `D = E = Prop`,
`F = Prop × Prop` — refutes both printed forms by cardinality and confirms both
corrected forms:

| # | Item | Left | Printed right | Corrected right |
| -- | ---- | ---: | ------------: | --------------: |
| 1 | 9.3 | 10 | 8 | 10 |
| 2 | 9.5 | 5 | 3 | 5 |

An order isomorphism is a bijection, so a cardinality mismatch settles it. These
two counts are the reason 9.3 and 9.5 are rated *inferred* rather than *certain*
and not the reverse: the reading of the page is certain; the paper is wrong.

**Theorem 14's blocker was misdiagnosed.** The inventory says "the list of
characterizations is garbled". The list is two items, is not garbled, and is
about bifiniteness, not about algebraic-or-bounded-complete domains:

> **Theorem 14** The following are equivalent for any cpo `D`.
> 1. `D` is bifinite.
> 2. `D` is a domain and `K(D)` is a Plotkin order.

What actually blocked it: `Bifinite.lean` **defines** `IsBifinite` to be
condition 2's second conjunct, so stating Theorem 14 against it is `P ↔ P`.
Condition 1 refers to the paper's own definition one page earlier — "Let `M` be
the set of finitary projections with finite image. Then `D` is said to be
bifinite if `M` is countable, directed and `⨆M = id`" — which the development did
not have. `Recovered.IsBifiniteViaProjections` supplies it from parts that
already existed (`ScottHom.IsFinitaryProjection` r0013, `ScottHom.id` r0028), and
`thm14` is the equivalence. It is the one result that licenses §6's use of the
Plotkin-order condition as the definition throughout.

## What is in `Recovered.lean`, and what is not

In: all seven statements above, as `lem9_1`…`lem9_6` and `thm14`, plus the two
supporting definitions `finiteImageProjections` and `IsBifiniteViaProjections`.
Every declaration is in `namespace ScottDomains.Recovered` (plan rule 4).

Not in: **nothing**. No conjunct of either result is rated unrecoverable, so
none is withheld.

Two things I deliberately did *not* state, to keep the `sorry` count honest:
the printed forms of 9.3 and 9.5 as refutations (`¬ Nonempty (… ≃o …)`). They
are provable — the counts above were enumerated exhaustively — and would be two
more `sorry`s claiming results the plan did not ask for. The arguments are in
the doc; stating them in Lean is available as a follow-up if you want the
kernel to hold the refutations.

`≅` is rendered `Nonempty (_ ≃o _)`: `Product.lean` already fixes `≅` as an
order isomorphism, and Lemma 9 asserts one *exists*, so naming a particular map
would prejudge the proof — the choice `lem19` makes for the same reason.

## Incidental finding: four inventory rows undercount their conjuncts

The same two dropped glyphs are missing from four other rows, written from the
same broken extraction. Decoded, the paper's lists are:

| # | Result | Paper's list | Conjuncts | Inventory |
| -- | ------ | ------------ | --------: | --------- |
| 1 | Lemma 10 | `D → E, D ◦→ E, D × E, D ⊗ E, D + E, D ⊕ E, D⊥` | 7 | "6 of 6" |
| 2 | Lemma 17 | + `D♮, D♯, D♭` on the same seven | 10 | "5 of 5" |
| 3 | Lemma 28 | `→, ◦→, ×, ⊗, +, ⊕, (·)⊥, (·)♯, (·)♭` | 9 | 7 listed |
| 4 | Lemma 30 | + `(·)♮` | 10 | 7 listed |

Two consequences, neither cosmetic:

1. **`+` and `⊕` are different operators and the development has `⊕`.** The paper
   defines `D ⊕ E` (coalesced) in §4.4 and `D + E = D⊥ ⊕ E⊥` (separated); both
   appear in every list. `lem10_sum` and `lem17_sum` range over
   `CoalescedSum α β`, so they prove the `⊕` conjuncts, not the `+` conjuncts the
   inventory attributes to them. The `+` conjuncts are unstated and should be
   cheap — `D + E` unfolds to `D⊥ ⊕ E⊥`, so each follows from the `⊕` and `()⊥`
   conjuncts already proved.
2. **Lemma 17's three powerdomain conjuncts are absent** from both the row and
   `Skeleton/Lemma17.lean`. All three powerdomains exist (r0029), so they are
   statable now.

No proved statement is wrong; the rows count the wrong denominator. Lemma 10
stands at 6 of 7 and Lemma 17 at 5 of 10. I did not touch `PaperInventory.md` —
I own only `Skeleton/Recovered.lean` and `docs/StatementRecovery.md`; correcting
it is yours.

## Measurements

| # | Quantity | Value |
| -- | -------- | ----- |
| 1 | `sorry` added | **7** (6 Lemma 9 conjuncts + 1 Theorem 14) |
| 2 | `sorry` in the development | 8 (7 mine + `thm18`, pre-existing) |
| 3 | Results moved out of "not statable" | **2 of 2** |
| 4 | Conjuncts recovered | 7 — 5 certain, 2 inferred, **0 unrecoverable** |
| 5 | Files created | 2: `ScottDomains/Skeleton/Recovered.lean` (219 lines), `docs/StatementRecovery.md` (439 lines) |
| 6 | Files modified | 0 |
| 7 | Build | 1067 jobs, 0 errors, 0 warnings other than the 8 `sorry`s |

Final `lake build` line, verbatim from
`ScottDomains/logs/compile-20260806-212928.agent5.log`:

```
compile: exit 0 · wall 0:02.75 · mem 1642 MiB single / 1767 MiB tree pss / 2427 MiB tree rss · jobs 1067 · diagnostics 0 · lake errors 0 · sorry 8 · other warnings 0
```

The build compiled clean on the first attempt; the second run above is after the
docstring edits that added the counterexample figures.

Elaborated statements were checked with `#check @lem9_1 … @thm14` under
`lake env lean` to confirm each resolves to the intended type with the intended
instances — e.g. `lem9_3 : Nonempty (StrictHom (CoalescedSum β γ) α ≃o
StrictHom β α × StrictHom γ α)`, not something that unified away.

## Commits

| # | SHA | Subject |
| -- | --- | ------- |
| 1 | `594f660` | r0032 agent5: recover Lemma 9 and Theorem 14 from the PDF — `Skeleton/Recovered.lean`, `docs/StatementRecovery.md`, build logs |
| 2 | `652d067` | r0032 agent5: report |
| 3 | (this commit) | r0032 agent5: correct the report's own SHA for row 2 — it was written before the commit existed |

Branch `agent5`, not pushed and no upstream set, per plan rule 5.
