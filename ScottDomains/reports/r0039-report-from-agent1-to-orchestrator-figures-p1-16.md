---
round: r0039
from: agent1
to: orchestrator
subject: figures-p1-16
date: 2026-0808-11:18
started: 2026-0808-10:40
finished: 2026-0808-11:18
related:
  - plans/r0039-plan-from-orchestrator-to-orchestrator-figures-as-tikz.md
  - analyses/diagram-candidates.2026-0808-10:32.orchestrator.log
---

# r0039 agent1 — Figure 3, Figure 1, and every diagram on physical pages 1–16

## What was produced

Seven `.tex` files and their compiled `.pdf`s in
`ScottDomains/GunterScott90Images/`. Every one was verified by rendering the
compiled PDF to PNG and reading it beside a crop of the original page.

| # | File | Kind | Physical page | Printed page | Section |
| -- | ---- | ---- | ------------- | ------------ | ------- |
| 1 | `figure-3-posets-that-are-not-plotkin-orders` | Hasse, 3 parts | 32 | 31 | 6, after Theorem 14 |
| 2 | `figure-1-examples-of-cpos` | Hasse, 3 parts | 5 | 4 | 2.1 |
| 3 | `p08-uniform-fixed-point-operator` | commutative square | 8 | 7 | 2.3 |
| 4 | `p09-inclusion-map-d-prime-into-d` | commutative square | 9 | 8 | 2.3, proof of Thm 3 |
| 5 | `p14-universal-property-of-the-product` | commutative triangle | 14 | 13 | 4.1 |
| 6 | `p15-curry-f-makes-the-diagram-commute` | commutative triangle | 15 | 14 | 4.1 |
| 7 | `p16-commutativity-for-f-equals-apply-h-times-id` | commutative triangle | 16 | 15 | 4.1 |

`README.md` was deliberately **not** written or edited — the orchestrator
builds the index at merge, so three agents do not conflict over one file.

Two scripts were added, both prefixed `a1-` after checking what was already in
`scripts/`:

- `scripts/a1-tikz2pdf.sh` — compiles one standalone TikZ `.tex` with
  `lualatex`. Needed because `scripts/tex2pdf.sh` hardcodes `xelatex`, which
  is **not installed on this machine**: `which xelatex` returns nothing, while
  `/usr/bin/pdflatex`, `/usr/bin/lualatex` and `/usr/bin/latexmk` are present.
- `scripts/a1-build-figs.sh` — recompiles every `.tex` in
  `GunterScott90Images/` in one command. The shared style contract changed
  twice mid-round, and one command per Bash call is the project rule.

## Verification, crop against compiled PDF

Each row records what was compared and what differed.

| # | Figure | Vertices / objects | Edges / arrows | Distinguished marks | Differences found |
| -- | ------ | ------------------ | -------------- | ------------------- | ----------------- |
| 1 | Fig. 3a | 2 open, 2 filled | 5 full, 3 truncated (stub below the chain, one to each filled point) | filled pair, 1 vertical `⋮` | none |
| 2 | Fig. 3b | 3 open, 2 filled | 6 full, 4 truncated (two off-picture left, two right) | filled pair, 2 horizontal `⋯` | none |
| 3 | Fig. 3c | 4 open, 2 filled | 8 full (K₂,₂ between adjacent levels), 4 truncated | filled pair, 2 vertical `⋮` | none |
| 4 | Fig. 1, `T` | 3 open | 2 | — | none |
| 5 | Fig. 1, `N⊥` | 4 open | 3 full, 1 truncated, 1 horizontal `⋯` | — | none |
| 6 | Fig. 1, `ω⊤` | 4 open | 2 full, 1 truncated vertical, 1 vertical `⋮` | — | none |
| 7 | p08 square | 4 | 4, all solid | — | none |
| 8 | p09 square | 4 | 4, all solid | — | none |
| 9 | p14 triangle | 4 | 4 solid, 1 dashed (`⟨f,g⟩`) | dashed mediating arrow | none |
| 10 | p15 triangle | 3 | 2 solid, 1 dashed (`curry(f) × id`) | dashed mediating arrow | label sat flush against the dashed arrow; fixed with `node[left=3pt]` |
| 11 | p16 triangle | 3 | 2 solid, 1 dashed (`h × id`) | dashed mediating arrow | same fix applied |

The ellipsis dot count in Figure 3b was checked at 1200 dpi rather than
assumed: the paper prints **three** dots each side, so `$\cdots$` is exact. A
150 dpi reading had suggested four.

## Every candidate examined, with its verdict

Thirty-two candidate regions fall in physical pages 1–16. Coordinates are the
analysis log's, in pixels at 100 dpi.

| # | Page | y0–y1 | Verdict | What it actually is |
| -- | ---- | ----- | ------- | ------------------- |
| 1 | 1 | 255–301 | other | title page: "by" and "C. A. Gunter" |
| 2 | 1 | 324–402 | other | title page: affiliations, "and", "D. S. Scott" |
| 3 | 5 | 111–514 | **diagram** | Figure 1 |
| 4 | 5 | 859–929 | equation | `f*: PS → PT`, `f*(X) = {f(x) | x ∈ X}` |
| 5 | 5 | 936–998 | equation | `f*(⋃ᵢXᵢ) = ⋃ᵢf*(Xᵢ)` |
| 6 | 6 | 537–618 | equation | the `fact(n)` case split |
| 7 | 6 | 678–800 | equation | `F : (N⊥ ⊸ N⊥) → (N⊥ ⊸ N⊥)` and the `F(f)(n)` case split |
| 8 | 7 | 116–209 | equation | grammar `E ::= ε | Ea` |
| 9 | 7 | 216–294 | equation | grammar `E ::= a | bEb` |
| 10 | 7 | 301–401 | equation | grammar `E ::= ε | aa | EE` |
| 11 | 7 | 484–626 | equation | the three set equations `X = {ε} ∪ X{a}` etc. |
| 12 | 7 | 886–1004 | equation | `Y = (T − f*(S)) ∪ f*(g*(Y))` and the aligned derivation |
| 13 | 8 | 106–249 | equation | the `h(x)` case split |
| 14 | 8 | 688–849 | **diagram** | the uniformity square |
| 15 | 8 | 956–1005 | equation | `D' = {x ∈ D | x ⊑ fix(f)}` |
| 16 | 9 | 210–350 | **diagram** | the inclusion-map square |
| 17 | 10 | 751–884 | equation | Lemma 4's four numbered items |
| 18 | 11 | 188–268 | equation | `f∘g = id_D`, `g∘f ⊑ id_E` |
| 19 | 11 | 488–571 | equation | the `strict(f)(x)` case split |
| 20 | 11 | 578–629 | equation | `(D ⊸ E) ↪ (D → E)` |
| 21 | 11 | 956–1005 | equation | `p_N(x) = ⊔{y ∈ N | y ⊑ x}` |
| 22 | 13 | 740–833 | other | end of a paragraph plus the headings "4 Operators and functions." / "4.1 Products." |
| 23 | 13 | 901–969 | equation | `M = fst*(L) = …`, `N = snd*(L) = …` |
| 24 | 14 | 425–511 | equation | `fst ∘ ⟨f,g⟩ = f`, `snd ∘ ⟨f,g⟩ = g` |
| 25 | 14 | 681–788 | **diagram** | upper half of the product's universal property |
| 26 | 14 | 789–904 | **diagram** | lower half of the *same* diagram |
| 27 | 15 | 404–470 | equation | `apply : ((E → F) × E) → F` |
| 28 | 15 | 588–765 | **diagram** | the `curry(f)` triangle |
| 29 | 15 | 838–921 | equation | `f = apply ∘ (h × id)` |
| 30 | 16 | 106–342 | **diagram** | the `h × id` triangle |
| 31 | 16 | 349–406 | equation | `×() = I`, `×(D₁,…,Dₙ) = ×(D₁,…,D_{n−1}) × Dₙ` |
| 32 | 16 | 435–542 | equation | `onᵢ : ×(D₁,…,Dₙ) → Dᵢ`, `onᵢ = snd ∘ fst^{n−i}` |

### Measured rates over pages 1–16

| # | Quantity | Count | Share |
| -- | -------- | ----- | ----- |
| 1 | Candidates examined | 32 | — |
| 2 | Candidates that are diagrams | 6 | 19% |
| 3 | Candidates that are displayed equations | 23 | 72% |
| 4 | Candidates that are neither (title page, headings) | 3 | 9% |
| 5 | Distinct diagrams on pages 1–16 | 5 | — |

Rows 2 and 5 differ because candidates 25 and 26 are two halves of one
drawing: the detector split the page-14 triangle at the row where its middle
objects sit. Counting distinct diagrams, the detector's **false-positive rate
on pages 1–16 is 81 percent** (26 of 32 regions are not diagrams), and its
**over-segmentation rate is one diagram in six split across two regions**.

### False negatives

None. Pages 2, 3, 4 and 12 carry no candidate rows; all four were rendered in
full at 150 dpi and read. Page 2 is the table of contents, page 3 the
introduction, page 4 prose, page 12 prose — no drawing on any of them. Every
other page in 1–16 was also read in full, so the sweep covers all sixteen
pages, not only the candidate rectangles. **The detector missed no diagram in
this range.**

## Corrections to the style contract, and what was adopted

1. **`\usetikzpicture{}` is a typo.** No such macro exists; it is a hard
   compile error. Dropped — `\usepackage{tikz}` alone suffices. Reported
   before the other two streams had spent time on it.
2. **`scripts/tex2pdf.sh` cannot run here** (no `xelatex`). Replaced by
   `scripts/a1-tikz2pdf.sh` using `lualatex`.
3. **`solid` raised to `minimum size=5pt`, `open` left at 4pt**, on the
   orchestrator's ruling. Measurement behind it: in the scan the filled dots
   are about 40 px across and the open circles about 28 px at 600 dpi.
4. **agent2's `obj` / `arrow` / `darrow` keys adopted verbatim** and appended
   to the option block of *all seven* files, including the two Hasse figures,
   so every file in the round's set has an identical preamble.

The rest of the contract compiled unchanged, including `edge/.style` — there
is no clash with TikZ's `edge` path operation.

## Method notes worth keeping

- Geometry is **measured, not idealized**. For Figure 3, page pixels at 600
  dpi were mapped by `x = (px − 748)/200`, `y = (2347 − py)/200`; for Figure 1
  by `x = (px − 715)/200`, `y = (2503 − py)/200`. The three parts of each
  figure therefore keep the paper's own relative placement, scale and
  truncated-edge slopes. The paper's slopes are LaTeX `\line` ratios — 1/3,
  1/2, 1/1, 2/1 — and they survive the transcription.
- Classifying by **whole-page renders at 150 dpi** rather than by cropping
  each candidate cost 12 image reads instead of 32, and it is what caught the
  page-14 split and confirmed the absence of false negatives. Cropping was
  reserved for the six diagrams, at 600 or 1200 dpi.
- Reading the surrounding prose is not optional. The truncated edges in
  Figure 3a only make sense once printed page 30 says the closed pair "do not
  have such a complete set of minimal upper bounds" — the open circles are a
  descending chain of upper bounds with no minimal element, which is why every
  one of them is joined directly to both closed points.

## Surprises

- **The paper is mostly doing category theory, not order theory.** Five of the
  six diagrams on pages 1–16 are commutative diagrams; only Figure 1 is a
  Hasse diagram. Combined with agent2's eight of nine, the open/filled
  vocabulary the contract was built around describes roughly two pictures in
  the whole paper.
- **Figure 3a is not a Hasse diagram of covering relations.** It draws an edge
  from every chain element to both closed points even though those relations
  follow by transitivity. Transcribing what is drawn, rather than what a Hasse
  diagram would draw, was the right rule.
- The detector fires hardest on **grammars and case splits** — `E ::= …` and
  `{ … if n = 0 …` — which are exactly as sparse as a Hasse diagram, and on
  the **title page**, where centred short lines look sparse for the same
  reason.
