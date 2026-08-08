---
round: r0039
from: agent3
to: orchestrator
subject: figures-p34-44
date: 2026-0808-11:24
started: 2026-0808-10:42
finished: 2026-0808-11:24
related:
  - plans/r0039-plan-from-orchestrator-to-orchestrator-figures-as-tikz.md
  - analyses/diagram-candidates.2026-0808-10:32.orchestrator.log
---

# r0039 agent3 — pages 34–44 redrawn as TikZ

## Headline

`I⁺⁺` has **5 elements**, as the plan predicted. The full transcribed counts are
**I⁺ 2, I⁺⁺ 5, I⁺⁺⁺ 20**, 27 vertices and 33 edges in all. Nothing was adjusted
to reach those numbers: they were measured, and then found stated verbatim in
the paper's own prose on printed page 42, which the r0039 candidate log had not
quoted.

Four other results are worth the orchestrator's attention before merge, each
expanded below:

1. **Figure 4's edges do not exist in `Gunter Scott 1990.pdf`.** Page 44 renders
   as 27 unconnected dots in both poppler and mupdf. They were recovered from a
   different file, the 1989 tech report, which is already in `papers/`.
2. The paper's prose independently confirms the open/filled reading and the
   counts, and the transcription passes a structural check the paper implies.
3. `find-diagrams.py` missed a real diagram on page 41.
4. Of 17 candidate regions in my range, **3 are diagrams and 14 are not** — a
   82% false-positive rate on this range.

## Figure 4: the edges are gone from the source PDF

Page 44 of `Gunter Scott 1990.pdf` draws 27 circles and no lines. This is not a
crop artefact and not a renderer bug:

| # | Measurement | Result |
| - | ----------- | ------ |
| 1 | `mutool draw -F trace`, page 44 | text operators only; **no path operators**; fonts T8, T13, T14, T15, T20, all Type 3 |
| 2 | `pdffonts -f 44 -l 44` | five Type 3 fonts, none of them a rule or line font |
| 3 | `pdfimages -list -f 44 -l 44` | one 2550x3298 JBIG2 mask, **30 bytes** — blank |
| 4 | `pdftoppm -r 300` and `mutool draw -r 200` | both render 27 circles, zero lines |

The file is an Adobe Paper Capture rebuild. That process turns repeated shapes
into Type 3 glyphs and leaves everything else in a residual raster layer. The
circles repeat 27 times and became glyphs 14 (open) and 15 (filled) of font T14;
the connecting lines are all different lengths and angles, so they went to the
residual layer, and that layer is the 30-byte stub. **The lines were destroyed
when the file was made.** This also explains the candidate log's row for page
44: 697 px tall but only 94 inked rows, which is what a Hasse diagram with no
edges looks like.

The same figure appears as Figure 1.4, physical page 54, of
`ScottDomains/papers/Gunter Mosses Scott 1989 Semantic Domains and Denotational
Semantics MS-CIS-89-16.pdf` — already in the repo. That file is a genuine scan
and its lines are intact.

So the figure was built from two sources, and the `.tex` header says so:

- **Vertices from the 1990 trace, exactly.** Every coordinate in the file is
  `(trace point − (119.76, 251.75)) / 40`, so the drawing is the published
  paper's own placement to the point.
- **Edges from the 1989 scan.** All 27 circle centres there were measured with
  `scripts/a3-find-circles.py`, then every vertex pair was tested for ink along
  the whole segment by `scripts/a3-find-edges.py`. Reading a 20-vertex fan by
  eye is not reliable; the pair test is, and it has a large margin, because a
  segment between non-adjacent vertices crosses white paper almost at once.

`scripts/a3-map-vertices.py` fits an affine between the two drawings. The three
columns agree to under 1 pt, so the vertex sets are the same drawing — but the
1990 version **raised the right-hand arm (R5, R6) and the extra `I⁺⁺` vertex by
one 36 pt step** and moved several satellites. The 1990 positions are used, as
that is the paper being transcribed.

The 1990 grid then corroborates the vertex-to-vertex assignment independently:
C1, R4, R5, R6 come out exactly collinear at slope 2, and L6, C5, R2 and
L5, C3, R1 at slope −1. Those are precisely the three long pairs the segment
test had reported as covered "via" a middle vertex, so two independent methods
agree on which pairs are single edges and which are compositions.

## What the paper says, and a check it implies

Printed page 42, section 7.4, states the counts outright:

> "At the second step, `I⁺`, there are elements a = (⊥,{⊥}) and b = (⊥,∅) with
> b ⊢ a. At the third step there are five elements (a,{a}); (a,{b}); (b,{b});
> (b,∅); (a,∅) which form the partially ordered set `I⁺⁺` pictured in Figure 4.
> Note that there is another element (a,{a,b}) ∈ M(I⁺) but this satisfies
> (a,{a}) ⊢ (a,{a,b}) and (a,{a,b}) ⊢ (a,{a}) so we have identified these
> elements in the picture. The next step `I⁺⁺⁺` has 20 elements (up to
> equivalence in the sense just mentioned) and it is also pictured in Figure 4."

That sentence about identifying (a,{a,b}) with (a,{a}) is exactly the
identification at issue between the adopted reading and the Smyth reading. The
transcription and the prose agree: 1, 2, 5, 20.

The same paragraph also fixes what the filled circles mean:

> "It should be noted that each stage of the construction is embedded in the
> next one by the map x ↦ (x,{x}). The closed circles in the figure are
> intended to give a hint of how this embedding looks."

That yields a check the transcription must pass and does. The filled vertices
number 1, 2, 5 in `I⁺`, `I⁺⁺`, `I⁺⁺⁺` — the sizes of the preceding stage. And
the order induced on the five filled vertices of `I⁺⁺⁺` (C1, C3, C5, C7, R5)
comes out as the chain C1 < C3 < C5 < C7 with R5 covering only C1 — a 4-chain
with one extra atom, which is `I⁺⁺` on the nose. R5 is incomparable to C3
because R1 sits *below* both. Had a single edge been mis-transcribed, this
isomorphism would almost certainly have failed.

## Candidate verdicts — every region examined

Method: each page 34–43 was rendered whole at 150 dpi and read as an image, so
each page's candidates were classified together and the page was also swept for
diagrams the detector never proposed. Page 44 was handled as above.

| # | Page | Region (y, 100 dpi) | Verdict | What it actually is |
| - | ---- | ------------------- | ------- | ------------------- |
| 1 | 34 | 854–907 | other | the Lemma 19 statement, two lines of italic text |
| 2 | 35 | 232–311 | **diagram** | commutative square, `representable over a cpo` |
| 3 | 35 | 487–561 | displayed equation | `R : Fc(U) × Fc(U) → Fc(U)` and the `im(R(r,s))` display |
| 4 | 36 | 425–488 | displayed equation | the `Φ→` / `Ψ→` pair |
| 5 | 36 | 674–836 | displayed equation | the seven-line aligned computation of `(R→(r,s) ∘ R→(r,s))(x)` |
| 6 | 37 | 233–340 | displayed equation | `x = Ψ→(s ∘ (Φ→(x)) ∘ r)` |
| 7 | 37 | 344–430 | displayed equation | three-line aligned block ending `= x` |
| 8 | 37 | 476–562 | displayed equation | the `Φ×` / `Ψ×` pair |
| 9 | 37 | 689–774 | displayed equation | the `Φ_L` / `Ψ_L` pair |
| 10 | 39 | 116–263 | displayed equation | numbered equation list, items 4–6 |
| 11 | 40 | 189–271 | displayed equation | the definitions of `S` and `K` |
| 12 | 41 | 165–262 | displayed equation | the `F_1 … F_n` combination list |
| 13 | 41 | 620–773 | **diagram** | commutative square, `p-representable over a cpo` |
| 14 | 42 | 620–705 | displayed equation | the `Φ₊` / `Ψ₊` pair |
| 15 | 43 | 690–767 | other | two short prose lines before Lemma 30 |
| 16 | 43 | 836–919 | displayed equation | the `Φ♮` / `Ψ♮` pair |
| 17 | 44 | 106–803 | **diagram** | Figure 4 |

**3 diagrams, 12 displayed equations, 2 other.** False-positive rate on this
range: 14 of 17, or 82%. The plan's expectation that displayed equations are the
dominant false positive holds exactly. Its height≥200 filter would have kept
only row 17 here and discarded both commutative squares, whose regions are 79
and 153 px tall.

## Detector misses

| # | Page | Where | What | Redrawn |
| - | ---- | ----- | ---- | ------- |
| 1 | 41 | y≈945–985, 100 dpi | the picture of a typical element of the basis `U₀` — a line with three half-open intervals inked thick | **yes** |
| 2 | 34 | y≈415–430, 100 dpi | the labelled arrow chain `T₀ →^{e₀} T₁ →^{e₁} T₂ →^{e₂} ⋯` | no |
| 3 | 40 | y≈780–935, 100 dpi | the multi-line `ρ(a) = pair(a) …` fixed-point display | no |

Miss 1 is a genuine false negative and is now drawn. It is one glyph row tall,
so it could never clear a height threshold, but it is unmistakably a picture.
The detector separates by ink density over *rows*; a wide, short picture is
invisible to it. If the orchestrator wants a second pass, width and aspect ratio
would catch this class.

Misses 2 and 3 are recorded for completeness but are not diagrams by the rule I
applied: anything that is ordinary inline math once typeset is a displayed
equation. `T₀ →^{e₀} T₁ ⋯` is `\stackrel{e_0}{\longrightarrow}` on one line and
has no two-dimensional structure; the commutative squares and the interval
picture do. Page 38 was also read and correctly has neither a candidate nor a
diagram.

## Deliverables

Into `ScottDomains/GunterScott90Images/`, one `.tex` and one `.pdf` each:

| # | File | Page (phys/printed) | Section | Name from |
| - | ---- | ------------------- | ------- | --------- |
| 1 | `figure-4-a-domain-for-representing-operators-on-bifinites` | 44 / 43 | 7.4 | the paper's caption |
| 2 | `p35-operator-representable-over-a-cpo` | 35 / 34 | 7.1 | "…is *representable* over a cpo U if and only if there is a continuous function R_F which completes the following diagram (up to isomorphism):" |
| 3 | `p41-operator-p-representable-over-a-cpo` | 41 / 40 | 7.3 | "…is *p-representable* over a cpo U if and only if there is a continuous function R_F which completes the following diagram (up to isomorphism):" |
| 4 | `p41-a-typical-element-of-the-basis-u0` | 41 / 40 | 7.3 | "As the basis U₀ of our domain we take finite (non-empty) unions of half open intervals [r,t) = {s ∈ S \| r ≤ s < t}. A typical element would look like" |

`README.md` was deliberately not touched, per the orchestrator's instruction
that it builds the index at merge.

Style contract as amended in flight: `\usetikzpicture{}` dropped, `solid` at
5 pt against `open` at 4 pt, and the `obj` / `arrow` / `darrow` keys appended.
All four files carry the identical option block, including the keys they do not
use, so the set is uniform. Compilation is `scripts/a1-tikz2pdf.sh`, copied from
agent1's worktree; `scripts/tex2pdf.sh` is unusable here (no `xelatex`).

## Verification — compiled PDF read against the original crop

Done for all four, by rendering each output PDF and reading it beside the crop.

| # | Figure | Checked | Result |
| - | ------ | ------- | ------ |
| 1 | Figure 4 | 27 vertices, 8 filled / 19 open, 33 edges, per-vertex degree | matches. Vertex layout also checked against the 1990 dots directly: all 11 distinct x values and all 8 row heights line up |
| 2 | p35 square | 4 objects, 4 arrows, 3 solid + 1 dashed, arrow directions | matches |
| 3 | p41 square | 4 objects, 4 arrows, 3 solid + 1 dashed, arrow directions | matches |
| 4 | p41 intervals | 7 `[`, 7 `)`, 3 thick runs, thin runs of 1, 2, 1, 1 cells | matches |

Differences found and what was done:

- **Figure 4 against the 1989 scan**: the right arm and the extra `I⁺⁺` vertex
  sit one 36 pt step lower in 1989 than in 1990. Not corrected — 1990 is the
  paper being transcribed, and the output was re-checked against the 1990 dot
  render instead, where it matches.
- **Both squares**: arrow labels were initially at TikZ's default 3 pt
  clearance; the paper sets them 11 pt clear (measured, 46–48 px on a 300 dpi
  crop). Changed to `above=5pt` / `left=5pt` / `right=5pt` and recompiled.
- **Interval picture**: brackets were 23% too tall against the cell width
  (ratio 0.59 rendered against 0.48 measured in the paper). `scale=0.8` added
  and recompiled. One residual difference remains: the `)` and `[` of each pair
  are slightly further apart than the paper's 3.6 pt, because each `\Big`
  delimiter carries its own width; the thick runs are correspondingly a few
  percent short of the paper's 92% of a cell.
- No difference was found in any count.

## Scripts added

All in `scripts/`, prefixed `a3-`, each with a docstring giving what it measures
and why it exists. Existing scripts were checked first; `pdf-crop.sh`,
`pdf-render.sh` and `pdf-find-page.sh` were reused unchanged.

| # | Script | Purpose |
| - | ------ | ------- |
| 1 | `a3-find-circles.py` | locate open-circle and filled-disc vertices in a scanned Hasse diagram by 32-point ring sampling |
| 2 | `a3-ring-profile.py` | radial ink profile about a point, to calibrate the ring radius for the above |
| 3 | `a3-map-vertices.py` | affine-map the 1989 scan's measured circles into 1990 page coordinates and match them |
| 4 | `a3-find-edges.py` | recover the covering relation by testing every vertex pair for ink along the whole segment |
| 5 | `a3-render-range.sh` | render a page range to PNGs in one command |
| 6 | `a1-tikz2pdf.sh` | copied from agent1's worktree, unmodified |

`a3-find-circles.py` needed calibrating: R=13 and R=17 both found only the eight
filled discs, because an open circle's stroke sits in the annulus 21–23 px at
600 dpi. That is what `a3-ring-profile.py` exists to have measured rather than
guessed. At R=22 it returns 27 vertices, 8 filled and 19 open — the 1990 trace's
counts exactly, which is the first sign the two drawings share a vertex set.

## For the other streams

agent1 and agent2 should know that the 1989 tech report
(`Gunter Mosses Scott 1989 … MS-CIS-89-16.pdf`) is a clean scan of the same
text. Any figure in the 1990 file that renders with missing rules can be
recovered there; `scripts/pdf-find-page.sh` locates the corresponding page by
caption text. Whether Figures 1, 2 and 3 lost rules the same way I did not
check — arrow glyphs and circle glyphs survive the Paper Capture rebuild, only
picture-mode rules were dropped, so a figure built from arrows is unaffected.
