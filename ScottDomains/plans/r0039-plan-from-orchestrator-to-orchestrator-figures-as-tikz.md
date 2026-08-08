---
round: r0039
from: orchestrator
to: orchestrator
subject: figures-as-tikz
date: 2026-0808-10:32
status: pending
related:
  - analyses/diagram-candidates.2026-0808-10:32.orchestrator.log
  - GunterScott90Images/README.md
---

# r0039 — Redraw the paper's diagrams as TikZ, one PDF each

## Why redraw rather than crop

Cropping a 1990 scan yields bitmap fragments carrying scan noise, at one fixed
resolution, with whatever text happens to sit inside the rectangle. Redrawing
gives vector PDFs at any size, no surrounding text by construction, a caption
under our control, and figures that can be `\input` into this project's own
documents. The diagrams are Hasse diagrams — dots, lines, a few labels — so the
transcription is bounded work.

Three measurements settled that extraction is not available, all recorded in
`scripts/find-diagrams.py`'s docstring:

1. `pdfimages -list` reports one embedded image per page, each a near-empty JBIG2
   mask of 30–486 bytes. **There are no embedded figures.**
2. `mutool draw -F trace` on page 32 reports 1430 glyphs, 223 spans, one image
   and **zero path operators** — the diagrams are TeX line/circle-font glyphs,
   not vector art.
3. `pdffonts` names every Type 3 font `T8`–`T20` with Custom encoding, so the
   font cannot discriminate diagram glyphs from text glyphs.

## What exists to build on

`analyses/diagram-candidates.2026-0808-10:32.orchestrator.log` — 78 candidate
regions in pixels at 100 dpi. **They are candidates, not diagrams:** the detector
separates by ink density, so it fires on displayed equations too. Filtering to
height ≥ 200 leaves eight, and those eight contain all four numbered figures.

`scripts/pdf-crop.sh <pdf> <page> <dpi> <x> <y> <w> <h> <out>` renders a region
to PNG so it can be read as an image. Coordinates are pixels at the chosen dpi,
so a candidate row scales directly: at `-r 100` use the numbers as printed.

## Stream 4 — the completeness sweep

Streams 1–3 work the **78 detected candidate regions**. `find-diagrams.py`
requires a region at least 40 px tall at 100 dpi with at least 25 sparse rows, so
a small inline picture — two dots and an arrow — is invisible to it. That is a
false-negative rate nobody has measured, and no amount of care inside streams 1–3
closes it, because they are reading a list the detector produced.

**agent4 therefore looks at all 44 pages and produces a census by eye.** The
partition with the other streams is exact and leaves no overlap:

* streams 1–3 own every region **in** the candidate list;
* **stream 4 owns every picture the detector never flagged.**

So agent4 transcribes only what it finds missing, and its census is the authority
on how complete the round is.

Method: render each page whole at low resolution — 80–100 dpi is enough to see
*that* a picture is there — read it, and record for every page what pictures it
contains. Cross-check each against the candidate list. Work in batches of about
eight pages and commit the partial census after each, so that running out of
context loses one batch rather than the round.

Deliverable: `analyses/`-bound material goes to the orchestrator, so agent4
writes `reports/r0039-report-from-agent4-to-orchestrator-page-census.md` with one
row per page: pictures present, whether each is in the candidate list, and which
stream owns it. Plus `.tex`/`.pdf` for any it transcribes.

## The three streams

Figure 3 is the pilot. It is the figure the development leans on most — its three
parts are the three cases of Theorem 18 — and its output fixes the house style
for the other two streams.

| # | Agent | Pages | Figures |
| -- | ----- | ----- | ------- |
| 1 | agent1 | **32 first**, then 1–16 | **Figure 3**, then Figure 1 (p5), then any confirmed diagram in 1–16 |
| 2 | agent2 | 17–31, 33 | Figure 2 (p21), plus confirmed diagrams — candidates on 17–22, 26, 27, 29, 30, 33 |
| 3 | agent3 | 34–44 | Figure 4 (p44), plus confirmed diagrams — candidates on 34–37, 39–43 |

## The style contract — identical across streams

Defined here rather than in a shared file so no stream waits on another. Every
figure is a standalone document compiled by `scripts/tex2pdf.sh`:

```latex
\documentclass[border=6pt]{standalone}
\usepackage{tikz}
\usetikzpicture{}                  % (no extra libraries unless a figure needs them)
\begin{document}
\begin{tikzpicture}[
  x=1cm, y=1cm,
  every node/.style={inner sep=1pt},
  open/.style={circle, draw, fill=white, minimum size=4pt, inner sep=0pt},
  solid/.style={circle, draw, fill=black, minimum size=4pt, inner sep=0pt},
  edge/.style={draw, line width=0.4pt}]
  % vertices, then edges, then labels
\end{tikzpicture}
\end{document}
```

Rules that make the set coherent:

1. **Open circle = a point the paper draws hollow; filled = drawn solid.** In
   Figure 3 the closed circles are the distinguished pair, and that distinction
   is the whole content of the caption — never flatten it.
2. **No surrounding prose in the figure.** The only text inside the `tikzpicture`
   is what the paper prints inside the picture: part labels `a.`, `b.`, `c.`,
   element names, and ellipses `⋯` where the paper shows a continuation.
3. **The figure's name is a `\caption`-free comment in the `.tex` and the
   filename**, not text baked into the drawing.
4. Vertical order is the partial order: higher on the page is higher in `⊑`.

## Naming

Numbered figures: `figure-N-<slug>.tex` / `.pdf`, slug from the paper's own
caption.

**Unnamed diagrams take their name from the prose that introduces them** — the
sentence in which the picture is `pictured`, `see`, or `of the form`. Record in
the `.tex` header comment: physical page, printed page, the quoted sentence, and
the section. Example shape: `p20-ideal-completion-of-a-preorder.tex`. Prefer the
paper's own words over an invented description.

## Deliverables

Into `ScottDomains/GunterScott90Images/`:

1. one `.tex` per confirmed diagram, and its compiled `.pdf`;
2. an updated `README.md` table: file, figure name, physical page, printed page,
   source sentence for unnamed ones, and what the development uses it for;
3. **a report** `reports/r0039-report-from-agentN-to-orchestrator-figures-<range>.md`
   listing every candidate the agent examined and its verdict — diagram,
   displayed equation, or other — so the false-positive rate of
   `find-diagrams.py` is measured rather than assumed.

The existing full-page PNG renders are superseded and should be **deleted** by
whichever agent replaces a given figure, not left beside the new PDFs.

## Method

1. Read the candidate rows for your pages from the analysis log.
2. `scripts/pdf-crop.sh` each at 300 dpi (multiply the 100 dpi numbers by 3) and
   **read the PNG as an image**. This is the only reliable way to see the
   drawing — the Type 3 glyphs defeat text extraction.
3. Classify: diagram, displayed equation, or other. Equations are the expected
   false positives; say so and move on.
4. For each diagram, transcribe vertices and edges, write the `.tex`, compile.
5. **Compare the compiled PDF against the crop** by reading both images. Vertex
   count, edge count and the open/filled distinction must match. Say in the
   report that you did this, and what differed.

## Process rules

1. One command per Bash call; never chain; never `cd`.
2. `Edit`/`Write` only — no heredocs, **no `sed -i`** (the orchestrator broke this
   rule writing the detector; it is still the rule).
3. New scripts go in `scripts/` prefixed with your stream name, after checking
   what is there. `pdf-crop.sh`, `pdf-render.sh`, `pdf-section.sh`,
   `pdf-find-page.sh`, `tex2pdf.sh`, `md2pdf.sh` already exist.
4. Commit at every stopping point with your worktree's `scripts/gitcp.sh`; do not
   push.
5. **The plan is not evidence.** If a candidate the plan calls a figure is an
   equation, or the detector missed a diagram, say so — the false-positive and
   false-negative rates are a deliverable.
6. Your worktree may carry uncommitted r0038 audit work on its branch. Leave it
   alone; this round's files are in a different directory and must not touch it.

## Orchestrator steps

1. Commit this plan and the candidate log; fast-forward the worktrees.
2. Launch three agents.
3. **Review agent1's Figure 3 first**, against the crop, before the other two
   streams have spent much — the pilot exists so the style can be corrected once
   rather than three times.
4. Merge, rebuild the README index, and record the detector's measured
   false-positive rate in `find-diagrams.py`'s docstring.
