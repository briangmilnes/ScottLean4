# Statement recovery — Lemma 9 and Theorem 14

Round **r0032**, agent5. Source:
**C. A. Gunter and D. S. Scott, "Semantic Domains,"** *Handbook of Theoretical
Computer Science* Vol. B, North-Holland, 1990, pp. 633–674
([`../papers/Gunter Scott 1990.pdf`](../papers/Gunter%20Scott%201990.pdf)).

`docs/PaperInventory.md` recorded two of the paper's thirty numbered results as
**not statable**, because `pdftotext` cannot read them:

| # | Result | Recorded blocker |
| -- | ------ | ---------------- |
| 1 | Lemma 9 | "the PDF drops every `⊗` and every `⊥`, so which operators the laws range over is unreadable" |
| 2 | Theorem 14 | "the list of characterizations is garbled" |

Both are now recovered. The statements are in
[`../ScottDomains/Skeleton/Recovered.lean`](../ScottDomains/Skeleton/Recovered.lean),
open (`sorry`); this file is the evidence.

Result, in one line each: **Lemma 9 — six conjuncts, four certain and two
inferred (the page carries two misprints, each refuted by a finite
counterexample). Theorem 14 — certain; the text was never garbled, and what was
missing was the paper's own definition of *bifinite*, which the development had
replaced by the characterization Theorem 14 proves equivalent to it.**

---

## 1. Why the text is unreadable, and what reads it

The PDF's 47 pages carry 18 embedded **Type 3** fonts, all with
`/Encoding` `Custom` and, per `pdffonts`, **no `uni` (ToUnicode) map**:

```
name                                 type              encoding         emb sub uni
------------------------------------ ----------------- ---------------- --- --- ---
T19                                  Type 3            Custom           yes no  no
T18                                  Type 3            Custom           yes no  no
...
```

These are dvips-era bitmap fonts. Their `/Encoding /Differences` arrays name
every glyph by its own code and nothing else — page 22's math-symbol font
(object `25`) begins

```
/Differences [ 0 /n00 /n01 /n02 /n03 8 /n08 10 /n0a 14 /n0e /n0f
    18 /n12 /n13 /n14 24 /n18 33 /n21 /n22 /n23 50 /2 54 /6 /7 /8 /9
    59 /n3b 62 /n3e /n3f 77 /M 80 /P 85 /U 91 /n5b /n5c 96 /n60
    102 /f /g /h /i /j 118 /v /w ]
```

so `pdftotext` has nothing to map `/n0a` to. Codes at or above `0x20` leak
through as their ASCII character — which is the whole of the project's
`SymbolMap.tex` Table A (`!` for `→`, `v` for `⊑`, `?` for `⊥`, `2` for `∈`,
`h`/`i` for `⟨`/`⟩`) — and **codes below `0x20` are dropped silently**, leaving a
blank gap. That is why `×`, `⊗`, `⊕`, `⊆` and `∘` are all indistinguishable in
the extraction.

**The codes are recoverable, because they are the standard TeX font codes.** The
`/Differences` names are the codes in hex, and the leaked ASCII pins the
encoding: `0x21` → `→`, `0x32` → `∈`, `0x38` → `∀`, `0x39` → `∃`, `0x3E` → `⊤`,
`0x3F` → `⊥`, `0x76` → `⊑`, `0x77` → `⊒`, `0x68`/`0x69` → `⟨`/`⟩`. Every one of
those is `cmsy10`'s position for that glyph. So the font is `cmsy10`, and the
dropped codes read off its table:

| Code | `cmsy10` glyph name | Symbol | Appears in the stream as |
| ---- | ------------------- | ------ | ------------------------ |
| `0x01` | `periodcentered` | `·` | `\001` |
| `0x02` | `multiply` | `×` | `\002` |
| `0x08` | `circleplus` | `⊕` | `\b` |
| `0x0A` | `circlemultiply` | `⊗` | `\n` |
| `0x0E` | `openbullet` | `◦` | `\016` |
| `0x12` | `reflexsubset` | `⊆` | `\022` |
| `0x18` | `similar` | `∼` | `\030` |

Two consequences worth stating. `≅` is set as `∼` (`0x18`, raised 12 units) over
a `=` from the text font on the next line — which is why the extraction shows a
bare `=` at the start of a line. And the paper's **strict function arrow** is not
one glyph: it is `openbullet` (`0x0E`) followed by `arrowright` (`0x21`) at an
offset of 15 units, i.e. `◦` butted onto `→`, printing as `o—→`. Both `→` and
`◦→` extract as `!`, so the extraction of Lemma 9 conflates two different
function spaces.

The method used here is therefore:

1. `mutool clean -d -i -f "papers/Gunter Scott 1990.pdf" out.pdf <page>` to
   decompress one page's content stream;
2. `mutool show -b out.pdf <contents-obj>` to dump it;
3. decode each `Tj`/`TJ` string against the `cmsy10` / `cmr10` / `cmmi10` tables,
   tracking the current `Tf`. (`0x0B`–`0x0F` in the *text* fonts are the
   `ff fi fl ffi ffl` ligatures — the other half of the damage: `de\fne` is
   `define`, `bi\fnite` is `bifinite`.)
4. `pdftocairo -png -r 300` on the same page, to read the printed page directly
   and confirm the decode independently of every font table above.

Steps 1–3 give an exact transcription; step 4 is the independent check. Both
agree on every character reported below.

---

## 2. Lemma 9

### 2.1 Raw extraction, verbatim

`pdftotext -layout` on page 22 (printed p. 21), lines 820–843 of the output —
Lemma 8 included, because the two lemmas are the comparison that settles the
question:

```
Lemma 8 Let D, E and F be cpo's, then
  1. D  E 
           = E  D,
  2. (D  E )  F 
                  = D  (E  F ),
  3. D ! (E  F ) 
                  = (D ! E )  (D ! F ),
  4. D ! (E ! F ) 
                  = (D  E ) ! F . I
Lemma 9 Let D, E and F be cpo's, then
  1. D E 
         = E D,
  2. (D E ) F 
              = D (E F ),
  3. (E  F ) ! D 
                   = (E ! D)  (E ! F ),
  4. D !(E ! F ) 
                   = (D E ) ! F ,
  5. D (E  F ) 
                = (D E )  (D E )
```

and the continuation on page 23 (printed p. 22):

```
     6. D? ! E 
                = D ! EI.
```

Every operator in Lemma 9 is a blank gap, and the two arrows `→` and `◦→` are
both `!`. This is what "not statable" meant.

### 2.2 The content stream

Page 22's decompressed content stream, Lemma 8 item 1 (`/T3_4` is the `cmsy10`
font, object `25`; `/T3_2` is `cmmi10`; `/T3_1` is `cmr10`):

```
(1.)Tj
/T3_2 1 Tf   60 0 Td   (D)Tj
/T3_4 1 Tf   49 0 Td   (\002)Tj          <- 0x02 multiply       ×
/T3_2 1 Tf   45 0 Td   (E)Tj
/T3_4 1 Tf   49 -12 Td (\030)Tj          <- 0x18 similar        ∼   (raised)
/T3_1 1 Tf   0 14 TD   (=)Tj             <-                     =   (so: ≅)
/T3_2 1 Tf   48 -2 Td  (E)Tj
/T3_4 1 Tf   46 0 Td   (\002)Tj          <- ×
/T3_2 1 Tf   46 0 Td   (D)Tj
```

and Lemma 9 item 1, in the identical shape:

```
(1.)Tj
/T3_2 1 Tf   60 0 Td   (D)Tj
/T3_4 1 Tf   49 0 Td   (\n)Tj            <- 0x0A circlemultiply  ⊗
/T3_2 1 Tf   45 0 Td   (E)Tj
/T3_4 1 Tf   49 -12 Td (\030)Tj
/T3_1 1 Tf   T*        (=)Tj
/T3_2 1 Tf   48 -2 Td  (E)Tj
/T3_4 1 Tf   46 0 Td   (\n)Tj            <- ⊗
/T3_2 1 Tf   46 0 Td   (D)Tj
```

Lemma 9 item 3 introduces the other two operators:

```
(3.)Tj
/T3_1 1 Tf   60 0 Td   (\()Tj
/T3_2 1 Tf            (E)Tj
/T3_4 1 Tf   64 0 Td   (\b)Tj            <- 0x08 circleplus      ⊕
/T3_2 1 Tf   45 0 Td   (F)Tj
/T3_1 1 Tf   35 0 Td   (\))Tj
/T3_4 1 Tf   26 0 Td   (\016)Tj          <- 0x0E openbullet      ◦
             15 0 Td   (!)Tj             <- 0x21 arrowright      →   (so: ◦→)
/T3_2 1 Tf   53 0 Td   (D)Tj
```

This is not inference. `\002`, `\n`, `\b`, `\016` and `\041` are bytes in the
file, and their meanings are fixed by `cmsy10`'s published encoding.

### 2.3 The decoded text

```
Lemma 8 Let D , E and F be cpo's, then
  1. D × E ≅ E × D ,
  2. (D × E ) × F ≅ D × (E × F ),
  3. D → (E × F ) ≅ (D → E ) × (D → F ),
  4. D → (E → F ) ≅ (D × E ) → F .

Lemma 9 Let D , E and F be cpo's, then
  1. D ⊗ E ≅ E ⊗ D ,
  2. (D ⊗ E ) ⊗ F ≅ D ⊗ (E ⊗ F ),
  3. (E ⊕ F ) ◦→ D ≅ (E ◦→ D ) × (E ◦→ F ),
  4. D ◦→ (E ◦→ F ) ≅ (D ⊗ E ) ◦→ F ,
  5. D ⊗ (E ⊕ F ) ≅ (D ⊗ E ) ⊕ (D ⊗ E )
  6. D⊥ ◦→ E ≅ D → E .
```

The rendered page image (`pdftocairo -png -r 300`, page 22) shows exactly this,
character for character, with the arrow drawn as `o—→`.

### 2.4 What `◦→` means, in the paper's words

Decoded page 8 (printed p. 7), §2.1:

> A function `f : D → E` is said to be **strict** if `f(⊥) = ⊥`. We will usually
> write `f : D ◦→ E` to indicate that `f` is strict. […] With this ordering, the
> poset of continuous functions `D → E` is itself a cpo. Similarly, the poset of
> strict continuous functions `D ◦→ E` is also a cpo.

The paper uses `◦→` 46 times, including in the operator lists of Lemma 10
("`D → E`, `D ◦→ E`, `D × E`, `D ⊗ E`, `D + E`, `D ⊕ E`, `D⊥`") and Lemmas 28
and 30 ("The following operators are representable over `U`: `→`, `◦→`, `×`,
`⊗`, `+`, `⊕`, `(·)⊥`, `(·)♯`, `(·)♭`"). Lemma 10's list, already formalized in
`Skeleton/Lemma10.lean` as `→`, `→⊥`, `×`, `⊗`, `+`, `⊥`, is independent
corroboration that this reading of the operator set is the one the development
has been using all along.

### 2.5 The two misprints

Items 3 and 5 are decoded with certainty and are **false as printed**. The
witness is one triple of finite domains the development already carries
instances for: `D = E = Prop` (two elements, `⊥ = False`) and `F = Prop × Prop`
(four elements). `Prop` has exactly one non-`⊥` element, so `Prop ⊗ X ≅ X`;
and `|E ⊕ F| = 1 + 3 + 1 = 5`.

| # | Item | Left side | Printed right side | Corrected right side |
| -- | ---- | --------: | -----------------: | -------------------: |
| 1 | 3 | `10` | `2 · 4 = 8` | `2 · 5 = 10` |
| 2 | 5 | `5` | `1 + 1 + 1 = 3` | `1 + 3 + 1 = 5` |

(Cardinalities of strict-hom sets counted by enumerating strict monotone maps;
on a finite poset every monotone map is continuous, so that is the whole set.)

An order isomorphism is a bijection, so a cardinality mismatch refutes it. The
printed forms are therefore not merely suspect — they are false.

**Item 3's correction is the paper's own theorem, three pages earlier.** Decoded
page 20 (printed p. 19), §4.4:

> Moreover, if `f : D ◦→ F` and `g : E ◦→ F` are strict continuous functions,
> then there is a unique strict continuous function `[f, g]` which completes the
> following diagram […]

That is precisely `(D ⊕ E) ◦→ F ≅ (D ◦→ F) × (E ◦→ F)`: the coalesced sum is the
coproduct in the category of pointed cpo's and strict continuous maps, so the
strict hom-functor carries it to a product. Under Lemma 9's naming of the
variables that reads `(E ⊕ F) ◦→ D ≅ (E ◦→ D) × (F ◦→ D)`. The misprint is a
transposition: the printed `(E ◦→ F)` should be `(F ◦→ D)`.

**Item 5's correction is forced by the left-hand side.** `F` appears on the left
of item 5 and nowhere on the printed right, and the second `E` is the only
position it can occupy. `D ⊗ (E ⊕ F) ≅ (D ⊗ E) ⊕ (D ⊗ F)` is the standard
distributivity of the smash product over the coalesced sum, and it is what the
cardinalities above confirm.

Item 4's correction is *not* needed: `D ◦→ (E ◦→ F) ≅ (D ⊗ E) ◦→ F` is exactly
what the paper sets up on the preceding page, where `strict apply` and
`strict curry` are introduced against the diagram over `(E ◦→ F) ⊗ E`.

### 2.6 Recovered statement, with confidence

| # | Item | Recovered | Confidence |
| -- | ---- | --------- | ---------- |
| 1 | 9.1 | `D ⊗ E ≅ E ⊗ D` | **certain** |
| 2 | 9.2 | `(D ⊗ E) ⊗ F ≅ D ⊗ (E ⊗ F)` | **certain** |
| 3 | 9.3 | `(E ⊕ F) ◦→ D ≅ (E ◦→ D) × (F ◦→ D)` | **inferred** — printed `(E ◦→ D) × (E ◦→ F)`, refuted above; correction is the paper's own universal property of `⊕` |
| 4 | 9.4 | `D ◦→ (E ◦→ F) ≅ (D ⊗ E) ◦→ F` | **certain** |
| 5 | 9.5 | `D ⊗ (E ⊕ F) ≅ (D ⊗ E) ⊕ (D ⊗ F)` | **inferred** — printed `(D ⊗ E) ⊕ (D ⊗ E)`, refuted above; only completion consistent with the left side |
| 6 | 9.6 | `D⊥ ◦→ E ≅ D → E` | **certain** |

Nothing in Lemma 9 is **unrecoverable**. All six are stated in
`Skeleton/Recovered.lean` as `lem9_1` … `lem9_6`.

The inventory's blocker — "the PDF drops every `⊗` and every `⊥`" — was accurate
about the symptom and wrong about the prognosis: the glyphs are dropped by
`pdftotext`, not absent from the file.

---

## 3. Theorem 14

### 3.1 Raw extraction, verbatim

`pdftotext -layout` on page 31 (printed p. 30), lines 1166–1173:

```
on the basis of a domain which characterizes the domain as being bi nite. Recall that N / A for
posets N and A if N \ # x is directed for every x 2 A.
De nition: A poset A is a Plotkin order if, for every  nite subset u  A, there is a  nite set N /A
with u  N . I

Theorem 14 The following are equivalent for any cpo D.
     1. D is bi nite.
     2. D is a domain and K (D) is a Plotkin order. I
```

**Theorem 14 is not garbled.** The only damage is the dropped `fi` ligature
(`bi nite` → `bifinite`, `De nition` → `Definition`, ` nite` → `finite`), the
`⊆` gaps in the surrounding definition, and `/` for `◁`, `\` for `∩`, `#` for
`↓`. The decoded text and the rendered page image both give:

> **Theorem 14** The following are equivalent for any cpo `D`.
> 1. `D` is bifinite.
> 2. `D` is a domain and `K(D)` is a Plotkin order. ∎

Confidence **certain**.

### 3.2 The real blocker was elsewhere

The inventory's entry, "Equivalent characterizations of an (algebraic/BC) domain
— the list of characterizations is garbled", is wrong on two counts: the list is
two items, not garbled, and it is about **bifiniteness**, not about
algebraic-or-bounded-complete domains.

What makes Theorem 14 hard to *state* is that the development already has both
sides — and has collapsed them. `Bifinite.lean` reads

```lean
def IsBifinite (α : Type*) [CompletePartialOrder α] : Prop :=
  IsPlotkinOrder (compacts α)
```

which is condition **2**'s second conjunct taken as the definition. Stating
Theorem 14 against it would be stating `P ↔ P`. Condition **1** refers to the
paper's own definition, one page earlier — decoded page 30 (printed p. 29):

> **Definition:** Let `D` be a cpo. Let `M` be the set of finitary projections
> with finite image. Then `D` is said to be bifinite if `M` is countable,
> directed and `⨆M = id`. ∎

(`⨆` here is the `cmex10` big-operator glyph, which `pdftotext` renders `F`; the
project's `SymbolMap.tex` Table A already records that mapping. On this line the
glyph is dropped altogether, but it survives eight lines further on — "together
with the fact that the set `M` is directed and `⨆M = id`" — so the reading is
fixed by the paper's own repetition.)

That definition is what `Skeleton/Recovered.lean` supplies, as
`IsBifiniteViaProjections`:

```lean
def finiteImageProjections (α : Type*) [CompletePartialOrder α] : Set (ScottHom α α) :=
  {p | ScottHom.IsFinitaryProjection p ∧ (Set.range ⇑p).Finite}

def IsBifiniteViaProjections (α : Type*) [CompletePartialOrder α] : Prop :=
  (finiteImageProjections α).Countable ∧
    DirectedOn (· ≤ ·) (finiteImageProjections α) ∧
    IsLUB (finiteImageProjections α) ScottHom.id
```

Every ingredient already existed: `ScottHom.IsFinitaryProjection` (r0013),
`ScottHom.id` (r0028). `⨆M = id` is written with `IsLUB` rather than `sSup`,
following `Domain.lean` — `IsLUB` needs no `SupSet` and transfers across
subtypes, and on the directed `M` the two readings coincide.

### 3.3 Recovered statement

| # | Result | Recovered | Confidence |
| -- | ------ | --------- | ---------- |
| 1 | Theorem 14 | `IsBifiniteViaProjections α ↔ (Domain α ∧ IsBifinite α)` | **certain** |

Stated as `thm14`. Note what it buys: §6 has used the right-hand side as *the*
definition throughout — `prop15`, `thm18`, Lemma 17's five conjuncts — and
Theorem 14 is the one result that licenses that substitution.

---

## 4. Summary

| # | Result | Conjuncts | Certain | Inferred | Unrecoverable | Lean |
| -- | ------ | --------: | ------: | -------: | ------------: | ---- |
| 1 | Lemma 9 | 6 | 4 | 2 | 0 | `lem9_1`…`lem9_6` |
| 2 | Theorem 14 | 1 | 1 | 0 | 0 | `thm14` + `IsBifiniteViaProjections` |

Seven `sorry`-bodied statements, zero results left unstatable, and two rows of
`docs/PaperInventory.md` that should change from `✗ not statable` to `✗ prove`.

### 4.1 Incidental: four inventory rows undercount their conjuncts

The same two dropped glyphs — `◦→` (`0x0E` `0x21`) and `⊕` (`0x08`) — are
missing from four other rows of `docs/PaperInventory.md`, which were written
from the same broken extraction. Decoded, the paper's operator lists are:

| # | Result | Paper's list, decoded | Conjuncts | Inventory says |
| -- | ------ | --------------------- | --------: | -------------- |
| 1 | Lemma 10 | `D → E, D ◦→ E, D × E, D ⊗ E, D + E, D ⊕ E, D⊥` | 7 | "`→,×,⊗,+,()⊥`", "6 of 6" |
| 2 | Lemma 17 | `D → E, D ◦→ E, D × E, D ⊗ E, D + E, D ⊕ E, D⊥, D♮, D♯, D♭` | 10 | "`→,×,⊗,+,()⊥`", "5 of 5" |
| 3 | Lemma 28 | `→, ◦→, ×, ⊗, +, ⊕, (·)⊥, (·)♯, (·)♭` | 9 | "`→,×,⊗,+,()⊥,()],()[`" |
| 4 | Lemma 30 | `→, ◦→, ×, ⊗, +, ⊕, (·)⊥, (·)♯, (·)♭, (·)♮` | 10 | "`→,×,⊗,+,()⊥,()],()[`" |

Two corrections follow, and neither is cosmetic.

**`+` and `⊕` are different operators, and the development has `⊕`.** The paper
defines the coalesced sum `D ⊕ E` in §4.4 and the separated sum by
`D + E = D⊥ ⊕ E⊥` — both appear in every list above. `CoalescedSum` is `⊕`, so
`lem10_sum` and `lem17_sum`, which range over `CoalescedSum α β`, prove the `⊕`
conjuncts, not the `+` conjuncts the inventory attributes to them. The `+`
conjuncts are not stated. They should be cheap — `D + E` unfolds to
`D⊥ ⊕ E⊥`, so each follows from the `⊕` conjunct and the `()⊥` conjunct, both
already proved.

**Lemma 17's three powerdomain conjuncts are absent.** `D♮`, `D♯` and `D♭` — the
convex, upper and lower powerdomains — are in the paper's list and in neither the
inventory row nor `Skeleton/Lemma17.lean`. All three powerdomains exist in the
development (r0029), so these are statable now.

Counting `→` (proved r0007) with the five in `Skeleton/Lemma10.lean` and
`Skeleton/Sum.lean`, Lemma 10 stands at **6 of 7** and Lemma 17 at **5 of 10**,
not 6 of 6 and 5 of 5. No proved statement is wrong; the rows count the wrong
denominator. Correcting them is the orchestrator's call — this round's agent5
owns only `Skeleton/Recovered.lean` and this file.

## 5. Reproducing the evidence

```
pdftotext -layout "papers/Gunter Scott 1990.pdf" -            # the broken extraction
pdffonts  "papers/Gunter Scott 1990.pdf"                      # 18 Type 3 fonts, no uni
mutool clean -d -i -f "papers/Gunter Scott 1990.pdf" p22.pdf 22
mutool show p22.pdf pages                                     # -> page object
mutool show p22.pdf <page-obj>                                # -> /Contents, /Font map
mutool show -b p22.pdf <contents-obj>                         # the byte-exact stream
pdftocairo -png -r 300 -f 22 -l 22 "papers/Gunter Scott 1990.pdf" p22
```

Pages: **Lemma 8 and Lemma 9 items 1–5** are PDF page 22 (printed p. 21);
**Lemma 9 item 6 and Lemma 10** are page 23 (printed p. 22); the **definition of
bifinite** is page 30 (printed p. 29); **Theorem 14** and the definition of a
Plotkin order are page 31 (printed p. 30). The `cmsy10` codes used above are
`0x01` `·`, `0x02` `×`, `0x08` `⊕`, `0x0A` `⊗`, `0x0E` `◦`, `0x12` `⊆`,
`0x18` `∼`, `0x21` `→`, `0x3F` `⊥`.
