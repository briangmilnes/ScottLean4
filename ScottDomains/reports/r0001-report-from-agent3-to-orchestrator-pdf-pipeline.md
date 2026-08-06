---
round: r0001
from: agent3
to: orchestrator
subject: pdf-pipeline
date: 2026-0806-13:05
started: 2026-0806-12:28
finished: 2026-0806-13:05
related: plans/r0001-plan-from-orchestrator-to-orchestrator-toolchain-audit.md
---

# r0001 — A3: LaTeX and Markdown-to-PDF pipeline

Scope executed: plan Part 2, Subagent A3, items 1–5. No file under
`scripts/` or `ScottDomains/docs/` was modified; every render was written to the
session scratchpad. Nothing was installed and nothing ran as root. Raw log:
`ScottDomains/logs/md2pdf.2026-0806-12:56.agent3.log`.

## 1. Reproduction — two independent defects, not one

`scripts/md2pdf.sh ScottDomains/docs/PaperInventory.md <scratch>` fails before
LaTeX is reached.

**D2a — interpreter absent.**

    $ ./scripts/md2pdf.sh ScottDomains/docs/PaperInventory.md $SCRATCH
    /bin/bash: line 1: ./scripts/md2pdf.sh: cannot execute: required file not found
    exit 127

`scripts/md2pdf.sh` line 1 is `#!/bin/zsh`; `which zsh` returns nothing on this
host. The script also uses the zsh-only parameter expansion `${0:A:h}` on line 23
to locate `md-pdf-header.tex`, so changing only the shebang to `#!/bin/bash` is
not sufficient.

**D2b — fonts absent.** Running the same pandoc invocation under bash reaches
lualatex and fails there. Verbatim:

    Error producing PDF.
    ! Package fontspec Error: The font "STIXTwoText" cannot be found.

    For immediate help type H <return>.
     ...

    l.67 ...o Text}[RawFeature={fallback=scottfallback}]

    exit 43

The lualatex log carries 12 `! Package fontspec Error` lines — 6 for
`STIXTwoText`, 6 for `Menlo` — and terminates with `Fatal error occurred, no
output PDF file produced!`. Measurement: 0 pages, 0 bytes. The failure is total,
not degraded; there is no "before" tofu count for the current header on this
host because no PDF exists to count in.

## 2. TeX Live coverage

`dpkg -l` over the six packages the plan names:

| # | Package | State | Note |
| - | ------- | ----- | ---- |
| 1 | `texlive-latex-extra` | installed 2023.20240207-1 | — |
| 2 | `texlive-luatex` | installed 2023.20240207-1 | — |
| 3 | `fonts-texgyre` | installed 20180621-6 | plus `fonts-texgyre-math` |
| 4 | `texlive-fonts-extra` | **not installed** | candidate 2023.20240207-1 |
| 5 | `texlive-science` | **not installed** | candidate 2023.20240207-1 |
| 6 | `fonts-stix` | **not installed** | candidate 1.1.1-5 |

Also present: `texlive-base`, `texlive-binaries`, `texlive-fonts-recommended`,
`texlive-latex-base`, `texlive-latex-recommended`, `texlive-pictures`,
`texlive-plain-generic`, `fonts-lmodern`, `lmodern`.

**Correction to the plan's Part 3 row 2.** `fonts-stix` does *not* supply STIX
Two. I downloaded the candidate `.deb` as a user and read the family names out of
its OTFs with `fc-query`: it ships STIX **1.1.1**, families `STIX`, `STIXGeneral`,
`STIX Math`, `STIXNonUnicode`, `STIXSizeOneSym` … `STIXVariants`. The strings
`STIX Two Text` and `STIX Two Math` appear nowhere in it. Installing `fonts-stix`
would not fix the header.

`STIXTwoText-Regular.otf` is shipped on Ubuntu noble by **`texlive-fonts-extra`**
(confirmed via the `packages.ubuntu.com` contents index). That package is
629 MB compressed / 1.73 GB installed — 5.2 MB of which is the font the pipeline
actually needs.

Two install lines, in preference order:

    # cheap: 5.2 MB, no root, exactly the two families the header names
    mkdir -p ~/.local/share/fonts && cd /tmp \
      && curl -LO https://mirrors.ctan.org/fonts/stix2-otf.zip \
      && unzip -j stix2-otf.zip 'stix2-otf/*.otf' -d ~/.local/share/fonts \
      && fc-cache -f

    # distribution route: root, 1.73 GB installed
    sudo apt-get install texlive-fonts-extra

Only one further root command is required, for D2a:

    sudo apt-get install zsh

`texlive-science` is not needed by any of `md2pdf.sh`, `tex2pdf.sh` or
`SymbolMap.tex`; `fonts-stix` is not needed at all.

## 3. Proposed header

Proposed file: scratchpad `md-pdf-header.tex`. **Not applied to the repo.**
Diff against `scripts/md-pdf-header.tex` (86 lines added, 2 replaced):

```diff
--- scripts/md-pdf-header.tex
+++ (proposed)
@@ -1,13 +1,99 @@
 % Font setup for md2pdf.sh (lualatex). STIX Two Text reads well but lacks some
 % symbols (⊥ ≈ ✗ …) and Menlo lacks others (≪); register a per-glyph fallback to
 % STIX Two Math then Apple Symbols so nothing renders as a blank box.
+%
+% One file, two platforms. The macOS setup names four families — STIX Two Text,
+% Menlo, Arial Unicode MS, Apple Symbols — and the last three ship only with
+% macOS. \directlua asks luaotfload's font-name database whether each family
+% resolves to a file. When all four resolve, the macOS block runs and its effect
+% is identical to the previous header. Otherwise the Linux block runs: STIX Two
+% Text (CTAN stix2-otf, Debian texlive-fonts-extra) when installed, DejaVu Serif
+% otherwise; DejaVu Sans Mono for code; and a fallback chain built from whichever
+% of STIX Two Math, DejaVu Sans, Noto Sans Symbols2 are present. If the probe API
+% is unavailable the macOS block is chosen, so an older luaotfload cannot change
+% what the two macs already render.
+%
+% Note: no `#' may appear inside \directlua — TeX doubles a catcode-6 `#' when it
+% stringifies the chunk, so Lua's length operator must be replaced by a counter.
 \usepackage{luaotfload}
+
 \directlua{
-  luaotfload.add_fallback("scottfallback", {
-    "STIX Two Math:mode=base;",
-    "Arial Unicode MS:mode=base;",
-    "Apple Symbols:mode=base;"
-  })
+  local db = fonts and fonts.names
+  local probe = db and (db.lookup_font_name or db.resolve_name)
+  function scott_font_present(name)
+    if not probe then return false end
+    local ok, res = pcall(probe, {name = name, lookup = "name"})
+    return (ok and res) and true or false
+  end
+  function scott_have(name)
+    tex.sprint(scott_font_present(name) and "1" or "0")
+  end
+  function scott_is_macos()
+    if not probe then tex.sprint("1") return end
+    tex.sprint((scott_font_present("Menlo")
+            and scott_font_present("Apple Symbols")
+            and scott_font_present("Arial Unicode MS")
+            and scott_font_present("STIX Two Text")) and "1" or "0")
+  end
+  function scott_add_fallback(...)
+    local t, n = {}, 0
+    for _, name in ipairs({...}) do
+      if scott_font_present(name) then
+        n = n + 1
+        t[n] = name .. ":mode=base;"
+      end
+    end
+    if n > 0 then luaotfload.add_fallback("scottfallback", t) end
+    tex.sprint(n > 0 and "1" or "0")
+  end
 }
-\setmainfont{STIX Two Text}[RawFeature={fallback=scottfallback}]
-\setmonofont{Menlo}[Scale=MatchLowercase, RawFeature={fallback=scottfallback}]
+
+\newif\ifscottmacos
+\ifnum\directlua{scott_is_macos()}=1\relax \scottmacostrue \fi
+
+\ifscottmacos
+%%% macOS branch — effect identical to the pre-2026-08 header.
+  \directlua{
+    luaotfload.add_fallback("scottfallback", {
+      "STIX Two Math:mode=base;",
+      "Arial Unicode MS:mode=base;",
+      "Apple Symbols:mode=base;"
+    })
+  }
+  \setmainfont{STIX Two Text}[RawFeature={fallback=scottfallback}]
+  \setmonofont{Menlo}[Scale=MatchLowercase, RawFeature={fallback=scottfallback}]
+\else
+%%% Linux branch — same fallback discipline over families Debian/Ubuntu ships.
+  \newif\ifscottfallback
+  \ifnum\directlua{scott_add_fallback("STIX Two Math", "DejaVu Sans",
+                                      "Noto Sans Symbols2")}=1\relax
+    \scottfallbacktrue
+  \fi
+  \ifscottfallback
+    \ifnum\directlua{scott_have("STIX Two Text")}=1\relax
+      \setmainfont{STIX Two Text}[RawFeature={fallback=scottfallback}]
+    \else
+      \setmainfont{DejaVu Serif}[RawFeature={fallback=scottfallback}]
+    \fi
+    \ifnum\directlua{scott_have("DejaVu Sans Mono")}=1\relax
+      \setmonofont{DejaVu Sans Mono}[Scale=MatchLowercase,
+                                     RawFeature={fallback=scottfallback}]
+    \else
+      \setmonofont{Latin Modern Mono}[Scale=MatchLowercase,
+                                      RawFeature={fallback=scottfallback}]
+    \fi
+  \else
+%%%% no fallback family installed: set the fonts without the RawFeature, since
+%%%% naming an unregistered fallback table makes the font itself unloadable.
+    \ifnum\directlua{scott_have("STIX Two Text")}=1\relax
+      \setmainfont{STIX Two Text}
+    \else
+      \setmainfont{DejaVu Serif}
+    \fi
+    \ifnum\directlua{scott_have("DejaVu Sans Mono")}=1\relax
+      \setmonofont{DejaVu Sans Mono}[Scale=MatchLowercase]
+    \else
+      \setmonofont{Latin Modern Mono}[Scale=MatchLowercase]
+    \fi
+  \fi
+\fi
```

### macOS branch is byte-identical

Comparison performed programmatically, not by eye: extract the executable lines
(non-comment, non-blank, leading indentation stripped) of the current header and
of the proposed macOS branch plus the hoisted `\usepackage{luaotfload}`, then
`diff -u`. Result: **10 of 10 lines match byte for byte, empty diff.**

### The discriminator was tested, not assumed

Three cases, each running the header's selection prologue under a controlled
`fonts.names.lookup_font_name`:

| # | Case | Probe answers | Branch selected |
| - | ---- | ------------- | --------------- |
| 1 | `mac` | Menlo, Apple Symbols, Arial Unicode MS, STIX Two Text all resolve | `macos` |
| 2 | `linux` | real probe on this host — none of the four resolve | `linux` |
| 3 | `noprobe` | `lookup_font_name` and `resolve_name` both `nil` | `macos` |

Case 3 matters: if a future or older luaotfload drops the probe API, the header
falls back to the macOS block, so no plausible failure of the test can change
what the two macs render.

### Two defects found while writing the header

Both are recorded because either one silently produces a broken PDF.

1. **`#` inside `\directlua`.** The obvious Lua idiom `t[#t+1] = …` fails: TeX
   stringifies the chunk with catcode-6 `#` doubled, so Lua receives `t[##t+1]`
   and raises `attempt to get length of a number value`. The chunk aborts,
   `scott_add_fallback` never registers, and the next line dies with
   `luaotfload-fallback.lua:81: Unknown fallback table scottfallback` followed by
   `Font … not loadable: metric data not found or bad`. The proposed header uses
   an explicit counter instead.
2. **Naming an unregistered fallback table makes the font itself unloadable.**
   `RawFeature={fallback=scottfallback}` is not ignored when `scottfallback` does
   not exist — it makes `\setmainfont` fail outright. Hence the
   `\ifscottfallback` arm that omits `RawFeature` when no fallback family is
   installed.

## 4. Tofu measurement

Test corpus, generated programmatically: the 38 code points named in the `U+`
column of `ScottDomains/docs/SymbolMap.tex` Table B, unioned with the 41 distinct
non-ASCII characters literally present in `SymbolMap.tex`,
`ScottDomains/docs/PaperInventory.md` and `INDEX.md` — **58 distinct code
points**, rendered one per table row plus one run-together stress line.

Two independent instruments, in agreement on every configuration:

- lualatex/luaotfload `Missing character:` warnings, forced into the log with
  `\tracinglostchars=3` (a measurement-only include, not part of the header);
- `pdftotext -enc UTF-8` on the rendered PDF, checking each of the 58 code points
  is recoverable from the text layer.

| # | Configuration | Document | exit | Missing character | pages | bytes |
| - | ------------- | -------- | ---- | ----------------- | ----- | ----- |
| 1 | current header, no STIX Two | PaperInventory | 43 | n/a — no PDF | 0 | 0 |
| 2 | current header, no STIX Two | INDEX | 43 | n/a — no PDF | 0 | 0 |
| 3 | current header, no STIX Two | SymbolCorpus | 43 | n/a — no PDF | 0 | 0 |
| 4 | proposed header, no STIX Two | PaperInventory | 1 | 7 | 4 | 107,958 |
| 5 | proposed header, no STIX Two | INDEX | 0 | **0** | 2 | 74,476 |
| 6 | proposed header, no STIX Two | SymbolCorpus | 1 | 4 | 2 | 54,527 |
| 7 | proposed header, STIX Two present | PaperInventory | 0 | **0** | 4 | 78,500 |
| 8 | proposed header, STIX Two present | INDEX | 0 | **0** | 2 | 45,630 |
| 9 | proposed header, STIX Two present | SymbolCorpus | 0 | **0** | 2 | 34,285 |

Rows 1–3 are the "before" number: the current header renders nothing at all here,
so the tofu count is undefined rather than large.

Rows 4–6, the proposed header with only the fonts already on this host: 11 tofu
occurrences over the three documents, spanning exactly **2 distinct glyphs** —
9 × `⨆` (U+2A06 N-ARY SQUARE UNION OPERATOR) and 2 × `⨅` (U+2A05 N-ARY SQUARE
INTERSECTION OPERATOR). Neither DejaVu Serif, DejaVu Sans nor Noto Sans Symbols2
carries them, and they are the two directed-join operators the formalization is
about. `pdftotext` independently reports the same two code points as the only
ones of the 58 not recoverable — 56 of 58 recovered.

Rows 7–9, the proposed header with the CTAN `stix2-otf` families made visible via
`OSFONTDIR` (with `TEXMFVAR` redirected to the scratchpad, so neither the system
font path nor `~/.texlive2023` was modified): **0 `Missing character` warnings,
exit 0, and 58 of 58 code points recovered by `pdftotext`.** The repo's
acceptance criterion of 0 tofu is met.

So the "after" measurement is **not** blocked on a root install: the STIX Two
route that satisfies the criterion (`~/.local/share/fonts` + `fc-cache`) needs no
privilege at all. What remains blocked on root is `sudo apt-get install zsh`,
without which `scripts/md2pdf.sh` cannot be invoked as written.

## 5. Round trip and file sizes

Embedded fonts of the corpus PDF under the STIX Two configuration, from
`pdffonts` — every face embedded, subsetted, and carrying a Unicode map, so text
selection and search work in Preview and Safari:

    ILKUIP+STIXTwoText-Regular    CID Type 0C   Identity-H  emb=yes sub=yes uni=yes
    YQXEPT+STIXTwoText-Bold       CID Type 0C   Identity-H  emb=yes sub=yes uni=yes
    OTKFRV+STIXTwoMath-Regular    CID Type 0C   Identity-H  emb=yes sub=yes uni=yes
    DEPOOY+DejaVuSans             CID TrueType  Identity-H  emb=yes sub=yes uni=yes

Against the committed `ScottDomains/docs/PaperInventory.pdf`, which was rendered
on a mac with the current header:

| # | Artifact | pages | bytes | text faces |
| - | -------- | ----- | ----- | ---------- |
| 1 | committed `PaperInventory.pdf` (macOS) | 4 | 76,816 | STIXTwoText ×3, Menlo ×2, STIXTwoMath, ArialUnicodeMS |
| 2 | Linux render, proposed header + STIX Two | 4 | 78,500 | STIXTwoText ×2, STIXTwoMath, DejaVuSans |
| 3 | committed `SymbolMap.pdf` (macOS) | 2 | 33,994 | STIXTwoText, STIXTwoMath, Menlo |
| 4 | Linux render, `INDEX.md`, proposed header + STIX Two | 2 | 45,630 | — |

Same page count and same body typeface as the macOS artifact; the 1,684-byte
difference and the face list reflect DejaVu Sans Mono standing in for Menlo in
code spans and DejaVu Sans covering a small number of symbol glyphs. Every glyph
is present in both. The round trip Dana needs — Markdown in, PDF out, opens with
correct symbols — holds, with one qualification I cannot discharge from here:
opening in macOS Preview and Safari must be checked on a mac. The Unicode-mapped,
fully embedded font set above is the objective precondition for it, and the page
geometry matches the artifacts the macs already produce.

## 6. What the user must run

| # | Need | Command | Privilege |
| - | ---- | ------- | --------- |
| 1 | `md2pdf.sh` interpreter | `sudo apt-get install zsh` | root |
| 2 | STIX Two families | `mkdir -p ~/.local/share/fonts && cd /tmp && curl -LO https://mirrors.ctan.org/fonts/stix2-otf.zip && unzip -j stix2-otf.zip 'stix2-otf/*.otf' -d ~/.local/share/fonts && fc-cache -f` | **user** |
| 3 | STIX Two, distribution route (alternative to 2) | `sudo apt-get install texlive-fonts-extra` | root, 1.73 GB |
| 4 | Apply the header | copy the scratchpad `md-pdf-header.tex` over `scripts/md-pdf-header.tex` | user |

Plan Part 3 row 2 (`sudo apt-get install fonts-stix`) should be struck: it
installs STIX 1.x, which does not provide `STIX Two Text` or `STIX Two Math`.
`texlive-science` is not required by anything in this pipeline.

Deferred, not fixed, because it changes a script the macs run: `scripts/md2pdf.sh`
would work unchanged on both platforms after item 1. Making it interpreter-neutral
instead means replacing `#!/bin/zsh` with `#!/bin/bash` **and** `${0:A:h}` with
`$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)`; that is a two-line edit but it
alters a file both macs execute, so it is left to the orchestrator to decide.

## 7. Acceptance criteria (plan Part 4)

- Criterion 3, `md2pdf.sh` exits 0 with 0 tofu: the LaTeX half is met —
  0 `Missing character` warnings and 58/58 code points recovered, exit 0, once
  STIX Two is present. The wrapper half needs `zsh` installed before
  `scripts/md2pdf.sh` itself can be invoked.
- Criterion 4, macOS rendering unchanged: the macOS branch is byte-identical to
  the current header over all 10 executable lines (empty `diff -u`), the
  discriminator selects it whenever the four macOS families resolve, and it is
  also the default when the probe API is missing. Confirmation on an actual mac
  is still the user's step.
