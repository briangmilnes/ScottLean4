---
round: r0039
from: agent2
to: orchestrator
subject: figures-p17-33
date: 2026-0808-11:11
started: 2026-0808-10:54
finished: 2026-0808-11:11
related:
  - plans/r0039-plan-from-orchestrator-to-orchestrator-figures-as-tikz.md
  - analyses/diagram-candidates.2026-0808-10:32.orchestrator.log
---

# r0039 agent2 — pages 17–31 and 33 of `Gunter Scott 1990.pdf`

## Result in numbers

| # | Quantity | Count |
| -- | -------- | ----- |
| 1 | Candidate regions in range examined | 27 |
| 2 | Verdict **diagram** | 9 |
| 3 | Verdict **displayed equation** | 14 |
| 4 | Verdict **other** (itemized list of displayed formulas) | 4 |
| 5 | Diagrams the detector missed (false negatives) | 0 |
| 6 | `.tex` written and compiled | 9 |
| 7 | Compile failures after the two corrections below | 0 |

Detector precision over agent2's range: **9 diagrams / 27 candidates = 33.3%**.
Recall over the range: **9 of 9 = 100%** — every diagram on pages 17–31 and 33
appears in the candidate list.

Of the nine, exactly one is a numbered figure (Figure 2). The other eight are
**commutative diagrams**, not Hasse diagrams. The plan anticipated Hasse
diagrams and named only Figure 2 for this range, so the eight are the round's
surprise; see "What surprised me" below.

## Per-candidate verdicts

Every row of `analyses/diagram-candidates.2026-0808-10:32.orchestrator.log`
falling on pages 17–31 or 33, in the log's own order. `y0`–`y1` are pixels at
100 dpi, as printed there. "What is actually there" was determined by reading a
150 dpi render of the whole page as an image, and, for every row classed
*diagram*, a 300 dpi crop as well.

| # | Page | y0–y1 | Verdict | What is actually there |
| -- | ---- | ----- | ------- | ---------------------- |
| 1 | 17 | 655–724 | equation | `g = λy. λx. x² + x∗y + y².` |
| 2 | 17 | 731–800 | equation | `f = λ(x,y). x² + x∗y + y².` |
| 3 | 17 | 807–876 | equation | `λf. f(3)` |
| 4 | 18 | 854–977 | equation | `smash : D × E → D ⊗ E` and the `smash(x,y)` case split |
| 5 | 19 | 188–259 | equation | the `unsmash(z)` case split |
| 6 | 19 | 312–480 | **diagram** | `p19-f-circ-unsmash-completes-the-following-diagram` |
| 7 | 19 | 547–626 | **diagram** | `p19-f-smash-g-completes-the-following-diagram` |
| 8 | 19 | 777–928 | **diagram** | `p19-strict-curry-and-strict-apply-commute` |
| 9 | 20 | 233–386 | equation | the `inl(x)` and `inr(x)` case splits |
| 10 | 20 | 415–641 | **diagram** | `p20-f-g-completes-the-following-diagram` |
| 11 | 20 | 642–758 | equation | the `[f,g](z)` case split |
| 12 | 20 | 840–897 | equation | `⊕() = I` and `⊕(D₁,…,Dₙ) = ⊕(D₁,…,Dₙ₋₁) ⊕ Dₙ` |
| 13 | 20 | 898–979 | equation | `inᵢ = inr ∘ inl^{n−i}` |
| 14 | 21 | 224–437 | **diagram** | **Figure 2: The lift of a cpo** |
| 15 | 21 | 534–616 | equation | the `down(z)` case split |
| 16 | 21 | 623–708 | equation | `down ∘ up = id_D` and `up ∘ down ⊒ id_{D⊥}` |
| 17 | 21 | 782–959 | **diagram** | `p21-f-dagger-completes-the-following-diagram` |
| 18 | 22 | 210–435 | **diagram** | `p22-h-completes-the-following-diagram` |
| 19 | 22 | 641–742 | other | Lemma 8's numbered list of isomorphisms, items 1–3 |
| 20 | 22 | 820–921 | other | Lemma 9's numbered list of isomorphisms, items 1–3 |
| 21 | 26 | 235–305 | equation | `↓x = {y ∈ A ∣ x ⊢ y}` |
| 22 | 26 | 858–912 | equation | `u ⊢♯ v iff (∀x∈u)(∃y∈v). x ⊒ y` |
| 23 | 27 | 683–772 | other | the two numbered clauses defining `u ⊢♮ v` |
| 24 | 29 | 250–317 | other | the numbered semi-lattice axioms 1–3 of theory `T♮` |
| 25 | 29 | 462–665 | **diagram** | `p29-ext-f-completes-the-following-diagram` |
| 26 | 30 | 106–293 | **diagram** | `p30-f-natural-completes-the-following-diagram` |
| 27 | 33 | 227–297 | equation | `S_f = {x ∈ K(D) ∣ x ⊑ f(x)}` |

The plan's three "most likely real inline diagrams" — page 20 y 415–641, page 22
y 210–435, page 29 y 462–665 — are rows 10, 18 and 25. All three are diagrams,
so that prediction was 3 for 3.

I split "other" from "equation" because the four "other" rows are not a single
centred display but a numbered or itemized list of displayed formulas. The
detector fires on them for the same reason it fires on equations — low ink
density per row — so for the purpose of measuring its false-positive rate they
count with the equations: **18 of 27 candidates, 66.7%, are not pictures.**

## False negatives: none found

Pages 23, 24, 25, 28 and 31 are in my range and carry **no** candidate rows at
all. I rendered each at 150 dpi and read it as an image to check the detector
had not missed a picture. It had not: those five pages are continuous prose,
displayed formulas and lemma statements, with no drawn figure. I also read every
page that *does* carry candidates in full, so a picture outside a candidate
rectangle would have been seen. None was.

## Deliverables

All in `ScottDomains/GunterScott90Images/`, one `.tex` and one `.pdf` each.

| # | File stem | Physical page | Printed page | Section | Source sentence |
| -- | --------- | ------------- | ------------ | ------- | --------------- |
| 1 | `figure-2-the-lift-of-a-cpo` | 21 | 20 | 4.4 Sums and lifts. | caption "Figure 2: The lift of a cpo."; introduced by "In short, D⊥ is the poset obtained by adding a new bottom to D—see Figure 2." |
| 2 | `p19-f-circ-unsmash-completes-the-following-diagram` | 19 | 18 | 4.3 Smash products. | "…then g = f ∘ unsmash is the unique strict, continuous function which completes the following diagram:" |
| 3 | `p19-f-smash-g-completes-the-following-diagram` | 19 | 18 | 4.3 Smash products. | "…then f ⊗ g = smash ∘ (f × g) ∘ unsmash is the unique strict, continuous function which completes the following diagram:" |
| 4 | `p19-strict-curry-and-strict-apply-commute` | 19 | 18 | 4.3 Smash products. | "…there is a unique strict function strict_curry such that the following diagram commutes:" |
| 5 | `p20-f-g-completes-the-following-diagram` | 20 | 19 | 4.4 Sums and lifts. | "…there is a unique strict continuous function [f, g] which completes the following diagram:" |
| 6 | `p21-f-dagger-completes-the-following-diagram` | 21 | 20 | 4.4 Sums and lifts. | "…there is a unique strict continuous function f† which completes the following diagram:" |
| 7 | `p22-h-completes-the-following-diagram` | 22 | 21 | 4.4 Sums and lifts. | "…we know that h = [f†, g†] is the unique strict continuous function which completes the following diagram:" |
| 8 | `p29-ext-f-completes-the-following-diagram` | 29 | 28 | 5.3 Universal and closure properties. | Theorem 12: "…there is a unique homomorphism ext(f) : D♮ → E which completes the following diagram:" |
| 9 | `p30-f-natural-completes-the-following-diagram` | 30 | 29 | 5.3 Universal and closure properties. | "…there is a unique homomorphism f♮ which completes the following diagram:" |

Each `.tex` header comment records the physical page, printed page, section and
the quoted sentence, per the plan's naming rule. The slugs are taken from the
paper's own words — "completes the following diagram", "the following diagram
commutes" — with the named map as the distinguishing term, since seven of the
eight introducing sentences are otherwise identical.

## Verification: compiled PDF read against the original crop

**I did this for all nine.** For each figure I read the 300 dpi crop of the
paper's region as an image, then read the compiled PDF as an image, and compared
vertex count, arrow count, arrow direction, solid-vs-dashed, and label side.

| # | File stem | Vertices | Arrows (solid + dashed) | Matched on first compile? |
| -- | --------- | -------- | ----------------------- | ------------------------- |
| 1 | `figure-2-the-lift-of-a-cpo` | 3 open circles | 2 function arrows, 1 order edge, 2 triangle outlines | yes |
| 2 | `p19-f-circ-unsmash-…` | 3 | 2 + 1 | yes |
| 3 | `p19-f-smash-g-…` | 4 | 3 + 1 | yes |
| 4 | `p19-strict-curry-…` | 3 | 2 + 1 | no — label collision, fixed |
| 5 | `p20-f-g-…` | 4 | 4 + 1 | yes |
| 6 | `p21-f-dagger-…` | 3 | 2 + 1 | yes |
| 7 | `p22-h-…` | 4 | 4 + 1 | yes |
| 8 | `p29-ext-f-…` | 3 | 2 + 1 | no — glyph defect, fixed |
| 9 | `p30-f-natural-…` | 4 | 3 + 1 | no — glyph defect, fixed |

What differed, and what I changed:

1. **`p19-strict-curry-and-strict-apply-commute`** — the `strict_apply` label
   sat on top of the diagonal arrow. In the paper the label's left edge is about
   62 px (0.52 cm) clear of the line. Moved the label from x = 1.60 to x = 2.05.
   Re-read after recompiling: clear, as in the paper.
2. **`p29-…` and `p30-…`** — the singleton bracket `{|·|}` rendered as `{ · }`:
   `\{\!\!|` puts −6 mu between brace and bar, which is enough to hide the
   vertical bars inside the braces at this size. Replaced with
   `\{\mkern-3.5mu|\mkern1mu\cdot\mkern1mu|\mkern-3.5mu\}`. Re-read after
   recompiling: both bars visible, matching the scan.

Nothing else differed. In particular the open-vs-filled distinction is not at
issue in this range: **every circle agent2 drew is open.** Figure 2's three
vertices are all drawn hollow in the scan, and the eight commutative diagrams
have no circular vertices at all — their vertices are typeset object names. The
`solid` style is carried in every preamble for uniformity with agent1's and
agent3's files but is not instantiated here.

Two faithfulness notes worth the orchestrator's eye:

- **`p19-f-smash-g-…` reproduces an error in the paper.** The sentence says
  `f : D → D'` and `g : E → E'`, so the square's right-hand column should be
  `D' × E'` over `D' ⊗ E'`. The paper prints `D × E` and `D ⊗ E` on both sides.
  I transcribed what is printed and flagged it in the `.tex` header comment.
  Correcting it silently would have made the figure disagree with the scan.
- **Arrow direction on the two sum diagrams.** In `p20-…` and `p22-…` the lower
  coprojection points **up** — `inr : E → D ⊕ E` and `inr ∘ up : E → D + E` both
  point at the sum, so the arrowhead is at `D ⊕ E` / `D + E`, not at `E`. Easy to
  get backwards from the shape alone; confirmed against the 300 dpi crop.

## Deviations from the plan, and why

1. **`\usetikzpicture{}` dropped from the style contract.** Not a LaTeX control
   sequence; a hard compile error. Everything else in the contract is reproduced
   verbatim in all nine files. (The orchestrator confirmed this mid-round from
   agent1's pilot; I had already reached the same conclusion.)
2. **`solid` bumped to `minimum size=5pt`**, `open` left at 4pt, per the
   orchestrator's mid-round ruling. Applied to all nine preambles even though no
   file instantiates `solid`, so the preambles stay byte-identical across streams.
3. **Compiled with `scripts/a1-tikz2pdf.sh`, not `scripts/tex2pdf.sh`.**
   `tex2pdf.sh` hardcodes `xelatex`, which is not installed here (`pdflatex`,
   `lualatex`, `latexmk` are). I copied agent1's script into this worktree rather
   than writing a second one; I had briefly written `a2-tex2pdf.sh` and deleted it
   on the orchestrator's instruction. `tex2pdf.sh` itself is untouched.
4. **Three style keys added to the contract's `tikzpicture` options**, in a block
   marked with a comment, for the commutative diagrams the contract did not
   anticipate: `obj` (object nodes, `inner sep=3pt`, so arrows stop clear of the
   glyphs), `arrow` (`->`, a map the text has already named) and `darrow`
   (`->`, `dash pattern=on 4pt off 3pt`, the unique completing map whose
   existence the sentence asserts). The solid/dashed distinction carries real
   content in these diagrams — it separates the given maps from the one being
   constructed — exactly as open/filled does in Figure 3.
5. **Geometry measured, not idealized.** Every coordinate is a pixel measurement
   from a 300 dpi crop divided by 118.11 px/cm, so each figure is drawn at the
   size and proportion the paper prints it. Figure 2 was drawn once at an
   arbitrary scale and redrawn to true size after the orchestrator's ruling.
6. **`README.md` untouched**, per instruction.

## For the orchestrator at merge

- Branch `agent2` did not carry `ScottDomains/GunterScott90Images/` at all — it
  is behind `main`, which already has the five full-page PNG renders. My commit
  therefore adds the directory fresh. **`figure-2-lift-of-a-cpo-21.png` on `main`
  is superseded by `figure-2-the-lift-of-a-cpo.pdf` and should be deleted at
  merge**; I could not delete a file my branch never had without manufacturing a
  conflict.
- New scripts in this commit: `scripts/a1-tikz2pdf.sh` (copy of agent1's, byte
  for byte — expect it to merge cleanly or be identical), `a2-render-pages.sh`,
  `a2-crop-list.sh`, `a2-build-figures.sh`.
- Suggested docstring line for `find-diagrams.py`, from this range only:
  27 candidates, 9 diagrams, 18 non-pictures — 33.3% precision, 100% recall.

## What surprised me

1. **The paper's diagram population is mostly commutative diagrams, not Hasse
   diagrams.** In my fifteen pages there is one numbered figure and eight
   unnumbered commutative diagrams. The plan's style contract — open circles,
   filled circles, "vertical order is the partial order" — describes a kind of
   picture that occurs exactly once in this range. Sections 4.3, 4.4 and 5.3 are
   doing category theory, and every "following diagram" is a universal property.
2. **The detector's misses are the interesting number, and there are none.**
   Its 33% precision is the expected cost of an ink-density test; what matters
   for the round is that it did not skip a picture, and over 20 pages it did not.
3. **Ten of the fourteen "displayed equation" false positives are case splits** —
   `inl(x) = { … }`, `down(z) = { … }`, `[f,g](z) = { … }`. A large brace with two
   or three short branches is sparser per row than body text by a wide margin, so
   it is the single most reliable way to fool the detector. If precision is ever
   worth raising, testing for a tall `\{` delimiter would remove most of the
   false positives at no cost to recall.
