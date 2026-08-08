# The diagrams of Gunter & Scott 1990, redrawn as TikZ

Every picture in [`../papers/Gunter Scott 1990.pdf`](../papers/Gunter%20Scott%201990.pdf),
transcribed to a standalone `.tex` and compiled to a `.pdf` beside it. Round
r0039, four agents.

Rebuild any one with [`../../scripts/a1-tikz2pdf.sh <file.tex>`](../../scripts/a1-tikz2pdf.sh),
or the whole set with [`../../scripts/a1-build-figs.sh`](../../scripts/a1-build-figs.sh).

## Why redrawn rather than extracted

Three measurements, all recorded in
[`../../scripts/find-diagrams.py`](../../scripts/find-diagrams.py):

1. `pdfimages -list` reports one embedded image per page, each a near-empty JBIG2
   mask of 30–486 bytes. **There are no embedded figures to extract.**
2. `mutool draw -F trace` reports glyphs and spans and **zero path operators** —
   the pictures are TeX line- and circle-font glyphs, not vector art.
3. `pdffonts` names every Type 3 font `T8`–`T20` with Custom encoding, so the
   font cannot separate picture glyphs from text glyphs either.

Cropping the scan would give bitmap fragments at one resolution carrying whatever
text fell inside the rectangle. Redrawing gives vector PDFs at any size, no
surrounding text by construction, and figures that can be `\input` into this
project's own documents.

## Completeness

**20 pictures, and the count is measured rather than assumed.** agent4 rendered
all 44 pages and read each as an image: 20 pictures on 16 pages, **28 pages carry
no picture at all**. The detector `find-diagrams.py` proposed 78 candidate
regions, of which 20 are pictures — **precision 25.6%**, the rest displayed
equations, itemized formula lists, grammars and the title page. It missed
exactly one, the one-glyph-tall interval picture on page 41: **recall 95%**.

One borderline call is recorded rather than hidden: page 34's arrow chain
`T₀ →e₀ T₁ →e₁ T₂ ⋯` is classified as display math, not a drawn picture. Call it
the other way and the set is 21.

| # | Kind | Count |
| -- | ---- | ----: |
| 1 | numbered figures | 4 |
| 2 | commutative diagrams | 15 |
| 3 | interval-line picture | 1 |

## The set

| # | File | Picture | Physical / printed page | Used by |
| -- | ---- | ------- | ----------------------- | ------- |
| 1 | `figure-1-examples-of-cpos` | **Figure 1** — Examples of cpo's: `T`, `N⊥`, `ω⊤` | 5 / 4 | `Powerset.lean`, `Lift.lean` |
| 2 | `figure-2-the-lift-of-a-cpo` | **Figure 2** — The lift of a cpo | 21 / 20 | `Lift.lean` |
| 3 | `figure-3-posets-that-are-not-plotkin-orders` | **Figure 3** — parts a, b, c | 32 / 31 | the three cases of **Theorem 18**; `MinimalUpperBounds.lean`, `JungSFP`, `JungFinite` |
| 4 | `figure-4-a-domain-for-representing-operators-on-bifinites` | **Figure 4** — `I⁺`, `I⁺⁺`, `I⁺⁺⁺` | 44 / 43 | §7.4's stage tower; `Colimit.lean` |
| 5 | `p08-uniform-fixed-point-operator` | the uniform fixed-point operator | 8 / 7 | **Theorem 3**, `UniformFixedPoint.lean` |
| 6 | `p09-inclusion-map-d-prime-into-d` | the inclusion `D′ ↪ D` | 9 / 8 | §3.1 |
| 7 | `p14-universal-property-of-the-product` | universal property of `D × E` | 14 / 13 | **Lemma 8**, `Product.lean` |
| 8 | `p15-curry-f-makes-the-diagram-commute` | `curry(f)` commutes | 15 / 14 | **Lemma 8.4**, `Currying.lean` |
| 9 | `p16-commutativity-for-f-equals-apply-h-times-id` | `f = apply ∘ (h × id)` | 16 / 15 | `Currying.lean` |
| 10 | `p19-f-smash-g-completes-the-following-diagram` | `f ⊗ g` | 19 / 18 | §4.3, `Smash.lean` |
| 11 | `p19-f-circ-unsmash-completes-the-following-diagram` | `f ∘ unsmash` | 19 / 18 | §4.3 |
| 12 | `p19-strict-curry-and-strict-apply-commute` | strict curry / strict apply | 19 / 18 | `StrictHom.lean`, **Lemma 9.4** |
| 13 | `p20-f-g-completes-the-following-diagram` | `[f,g]` on the coalesced sum | 20 / 19 | §4.4, `CoalescedSum.lean` |
| 14 | `p21-f-dagger-completes-the-following-diagram` | `f†` on the lift | 21 / 20 | §4.4, `Lift.lean` |
| 15 | `p22-h-completes-the-following-diagram` | `h` on the separated sum | 22 / 21 | `ClosureProperties/SeparatedSum.lean` |
| 16 | `p29-ext-f-completes-the-following-diagram` | `ext(f)` | 29 / 28 | §5.3, `ContinuousAlgebra.lean` |
| 17 | `p30-f-natural-completes-the-following-diagram` | `f♮`, the free continuous algebra | 30 / 29 | **Theorem 12**, `ContinuousAlgebra.lean` |
| 18 | `p35-operator-representable-over-a-cpo` | *representable* over a cpo | 35 / 34 | §7.1, `UniversalDomain.lean` |
| 19 | `p41-a-typical-element-of-the-basis-u0` | a typical element of the basis `U₀` | 41 / 40 | §7.3, `Dyadic.lean` |
| 20 | `p41-operator-p-representable-over-a-cpo` | *p-representable* over a cpo | 41 / 40 | §7.3, `PRepresentable.lean`, **Lemma 28** |

Each `.tex` header records the physical page, the printed page, the section, and
the paper's own sentence introducing the picture. Rows 5–20 are named from that
sentence rather than from an invented description.

## Two findings from the transcription

**Figure 4's edges do not exist in the 1990 file.** Page 44 renders as 27
unconnected dots in both poppler and mupdf; the trace shows zero path operators
and the page's raster layer is a **30-byte** JBIG2 stub. The file is an Adobe
Paper Capture rebuild: the 27 circles repeat, so they became Type 3 glyphs and
survived, while the lines are all different lengths and angles, so they went to a
residual layer that is empty. **The lines were destroyed when the file was made.**
They were recovered from the 1989 tech report
[`../papers/Gunter Mosses Scott 1989 …MS-CIS-89-16.pdf`](../papers/), a clean scan
of the same figure — vertices from the 1990 trace, edges by measuring all 27
circle centres and testing every vertex pair for ink along the whole segment.

Two independent checks then confirmed the result: the 1990 grid makes the three
long pairs that the segment test rejected exactly collinear, and the paper's own
remark that the closed circles "give a hint of how this embedding looks" holds —
the five filled vertices of `I⁺⁺⁺` induce a 4-chain with one extra atom, which is
`I⁺⁺` on the nose. Element counts: **`I⁺` 2, `I⁺⁺` 5, `I⁺⁺⁺` 20**, matching the
paper's own 1, 2, 5, 20 and so selecting the adopted reading of §7.4's pre-order
over the Smyth reading's 21.

**The damage is confined to page 44.** Figures 1 and 3 were checked against the
1990 file directly and their rules are intact, so their transcriptions stand.

## Verification

Every figure was checked by reading its compiled PDF against a 300 dpi crop of
the original and comparing vertex, edge, arrow, dashed-arrow and open/filled
counts. Two agents independently transcribed row 19 without knowing it — the only
accidental replication in the set — and **their drawings agree**: 7 intervals, 3
thickened at positions 2, 4 and 6, 14 delimiters. The duplicate was removed and
the agreement is the round's strongest single quality signal.

## Style

One `standalone` + `tikz` document per picture. `open` circles at 4 pt, `solid`
at 5 pt — the filled/open distinction is the entire content of Figure 3's
caption. `obj`, `arrow` and `darrow` for the commutative diagrams, where solid
versus dashed carries the same weight: a solid arrow is a map the paper gives, a
dashed one the unique map being asserted to exist. Geometry is **measured from
the page, not idealized**, so relative placement, scale and the paper's `\line`
ratio slopes survive; and Figure 3 is transcribed as *drawn*, edges and all,
rather than reduced to the covering relation a Hasse diagram would show.
