# Figures from Gunter & Scott 1990

Rendered from [`../ScottDomains/papers/Gunter Scott 1990.pdf`](../ScottDomains/papers/Gunter%20Scott%201990.pdf)
by [`../scripts/extract-figures.sh`](../scripts/extract-figures.sh) at 300 dpi.
Re-run that script with a dpi argument to regenerate at another resolution.

## Why these are renders, not extractions

`pdfimages -list` on the source reports one embedded image per page, and every
one is a 2550×3298 JBIG2 grayscale mask of **30–486 bytes** — near-empty
full-page scan layers. There are no embedded figures to extract. The paper's
figures are drawn with the same Type 3 bitmap fonts and vector line art that
carry its mathematics, which is also why `pdftotext` mangles its operator glyphs
(`♮`/`♯`/`♭` extract as `\`/`]`/`[`, `→` and `⇸` both as `!`). Rendering the page
is the only way to get the picture, and the same reason `../scripts/pdf-render.sh`
exists for reading the glyphs.

## Contents

| # | File | Figure | Physical page | Printed page |
| -- | ---- | ------ | ------------- | ------------ |
| 1 | `figure-1-examples-of-cpos-05.png` | 1 — Examples of cpo's | 5 | 4 |
| 2 | `figure-2-lift-of-a-cpo-21.png` | 2 — The lift of a cpo | 21 | 20 |
| 3 | `figure-3-posets-not-plotkin-orders-32.png` | 3 — Posets that are not Plotkin orders | 32 | 31 |
| 4 | `figure-3-crop-32.png` | 3, the drawing alone without surrounding text | 32 | 31 |
| 5 | `figure-4-domain-for-operators-on-bifinites-44.png` | 4 — A domain for representing operators on bifinites | 44 | 43 |

Each page was confirmed by locating the figure's **caption** on it, not a
reference to it. That distinction cost one wrong pass: grepping for "Figure 3"
returns physical pages 31 and 33, which merely mention it, while all three parts
sit together on page 32.

## What each figure is used for in the development

**Figure 3 is the one that matters most.** Its three parts are the three cases of
Theorem 18, and they are why `MinimalUpperBounds.lean` exists:

| # | Part | Condition | Where it appears |
| -- | ---- | --------- | ---------------- |
| 1 | 3a | a pair with **no complete** set of minimal upper bounds — the failure of Jung's *property m* | `JungNets.HasCompleteMub`; Jung's Theorem 1.37 supplies property m |
| 2 | 3b | a pair with a complete but **infinite** set — the failure of *property M* | `JungSFP.lemma217`, the cardinality argument |
| 3 | 3c | `U^∞(u)` **infinite** for `u` the two closed circles | `JungFinite.lemma22`, Jung's Lemma 2.2 |

Section62.lean calls Plotkin's result "the 2/3 SFP Theorem" precisely because it
settles 3a and 3b and not 3c.

**Figure 4** pictures `I⁺⁺`, the second stage of §7.4's tower. Its element count
is load-bearing: the paper's own stage sizes 1, 2, 5, **20** are what select the
adopted reading of §7.4's pre-order over the rival Smyth reading, which gives
1, 2, 5, **21**. See `Colimit.lean` and `scripts/mpair-stages.py`.

**Figures 1 and 2** are the introductory examples — `N⊥`, the flat cpos, and the
lift — corresponding to `Powerset.lean` and `Lift.lean`.
