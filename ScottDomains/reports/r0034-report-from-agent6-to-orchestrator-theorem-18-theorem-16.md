---
round: r0034
from: agent6
to: orchestrator
subject: theorem-18-theorem-16
date: 2026-0806-23:13
started: 2026-0806-22:41
finished: 2026-0806-23:13
related:
  - plans/r0034-plan-from-orchestrator-to-agent6-theorem-18-theorem-16.md
  - reports/r0031-report-from-agent3-to-orchestrator-theorem-18.md
  - reports/r0032-report-from-agent3-to-orchestrator-theorem-16
---

# r0034 agent6 — Theorem 16's positive form proved; Theorem 18's obstruction written, with a complete proof recovered from Jung

## Headline

`thm16_positive` is proved, and so is the stronger bounded-complete form
`thm16_positive_isEmbeddingProjectionPair`, which is the literal negation of
r0032's refutation.

**Theorem 18 did not fall. `thm18` is untouched and still `sorry`; I added
none.** The plan's alternative deliverable — a written obstruction with the
failing step named — is delivered, in the module docstring and below. Two
outcomes that must not be conflated:

* **[Smy83a] was not obtained and is not machine-retrievable.** Smyth's own case
  analysis is *not* recovered. The evidence is below; the recommendation is to
  stop hunting it.
* **A complete, checkable proof of the same statement was recovered — Jung's,
  not Smyth's.** It uses machinery that did not exist in 1983, so it is a
  different proof of the same theorem and nothing in it may be cited to
  [Smy83a].

Either way the round's real question is answered: the reason all three prior
rounds failed is now exact rather than conjectural, and the missing step has a
name.

## Measurement

| # | Quantity | Value |
| -- | -------- | ----- |
| 1 | Full build | `Build completed successfully (1073 jobs).` |
| 2 | Errors | 0 |
| 3 | Warnings beyond `sorry` | 0 |
| 4 | `sorry` in the development | **8**, unchanged — see the correction below |
| 5 | New module | `ScottDomains/Section62.lean`, 462 lines, 16 declarations (3 definitions, 13 theorems) |
| 6 | Files edited outside the new module | **0** |
| 7 | New `sorry` added | 0 |
| 8 | Axioms | `[propext, Classical.choice, Quot.sound]` or a subset on every new result; `sorryAx`: **0**. `apply_eq_self_of_mem_mubClosure` depends on no axioms at all |
| 9 | Build cost | wall 0.72 s incremental (5.94 s cold-cache full), peak RSS 1716 MiB single process |
| 10 | Papers added | 2, in `ScottDomains/papers/` |
| 11 | Commits (branch `agent6`) | `7d158b8`, `bb52f31` — not pushed, as instructed |

### Two stale statements of the `sorry` count, and a measurement trap

`docs/PaperInventory.md` row 6 already reads **8** and is correct, as does the
round-plan commit `9fc4522`. Two places contradict it and should be corrected:

* this round's plan, whose acceptance criterion reads "**either** `thm18` proved
  — taking the development to **0 `sorry`**"; proving `thm18` takes it to 7;
* `docs/PaperInventory.md` §6.2 row (line 425), which still calls `thm18` "**the
  development's only `sorry`**".

The measurement trap behind it is worth recording. `Skeleton/Recovered.lean`
carries 7 live `sorry`s (Lemma 9.1–9.6, Theorem 14) that a **targeted** build
never reports, because that file is outside the import closure of most targets:
`scripts/compile.sh -r r0034 ScottDomains.Section62` builds 847 jobs and reports
1 `sorry`, while `scripts/compile.sh -r r0034` with no target builds **1073 jobs
and reports all 8**. Any "N `sorry` remaining" claim must come from an untargeted
build or from `scripts/counts.sh`; both report 8.

`thm18` is the last `sorry` in the §6 line, not the last in the development.

## Part 2 — Theorem 16's positive form: proved

`ScottDomains.Section62.HasGreatestStableNormal` states the hypothesis in the
paper's own vocabulary: for every continuous `f`, the normal subposets of `K(D)`
contained in `S_f = {x ∈ K(D) | x ⊑ f(x)}` have a **greatest** member. Three
results:

1. `thm16_positive` — the hypothesis is sufficient. It produces `s : (D → D) →
   Fp(D)` with `s ∘ i = id`, `i ∘ s ⊑ id`, and `s` monotone. This is the literal
   negation of `FpEmbedding.TwoMub.not_exists_monotone_projection`, so the two
   now read as one dichotomy.
2. `hasGreatestStableNormal_of_boundedComplete` — every bounded complete domain
   satisfies it, because `S_f` is *itself* normal (`stableCompacts_isNormalIn`).
   Bounded completeness is spent exactly once: for `k₁, k₂ ∈ S_f` bounded by `x`,
   `f(k₁ ⊔ k₂)` bounds both `k₁` and `k₂`, so the join is again in `S_f`. That is
   the directedness `IsNormalIn` asks for. `stableCompacts_isNormalIn` needs no
   countability and is stated `omit [Domain α]`.
3. `thm16_positive_isEmbeddingProjectionPair` — over a bounded complete domain the
   conjunct holds **in full**, as an embedding–projection pair in the paper's
   §3.1 sense. This required proving `s` Scott continuous
   (`scottContinuous_fpOfStable`): for directed `d` with least upper bound `f`,
   `S_f = ⋃_{g ∈ d} S_g`, because `k ⊑ f(k) = ⨆_{g ∈ d} g(k)` and compactness of
   `k` puts `k ⊑ g(k)` for a single `g`. `ScottHom.isLUB_eval_image_of_isLUB` is
   the bridge.

Its statement is deliberately the exact negation of
`TwoMub.not_isEmbeddingProjectionPair`, down to passing the inclusion in as `i`
with `hi : ∀ p, i p = p.val` — that is how the refutation avoids committing to a
cpo structure on `Fp(D)`, and matching it lets the two be read against each
other line by line. The refutation was not restated or re-derived.

`TwoMub` fails the hypothesis for the reason r0032 identified: `{⊥, a, m₁}` and
`{⊥, b, m₁}` are two *maximal* normal subposets inside `S_{λx.m₁}` with none
above both. It is also not bounded complete, so result 2 is consistent with it.

## Part 1 — Theorem 18: which of [Smy83a]'s steps I could and could not recover

### [Smy83a] is not machine-retrievable — stop hunting it

*The largest cartesian closed category of domains*, TCS **27** (1983) 109–119,
DOI `10.1016/0304-3975(83)90095-6`, PII `0304397583900956`. Crossref was needed
to get the DOI right — the suffix is `-6`, not `-2`. Unpaywall and OpenAlex both
report it open access ("bronze") with ScienceDirect as the *only* location on
record, and Elsevier's content API confirms `openaccess=1`. Retrieval fails
anyway: ScienceDirect returns **HTTP 403** behind a Cloudflare challenge on the
landing page, `/pdf` and `/pdfft`, with and without browser headers; the content
API returns 401 without a key; CORE's three records all carry empty download
URLs; and every Wayback capture of the `/pdf` URL is the interstitial challenge
page. The archived landing page's own metadata reads `displayViewFullText:
false` — a legacy scan that never had HTML full text to archive. It needs a
browser session or an institutional proxy.

**Smyth's paper is not in `papers/` and I did not work around the block.** My own
attempt was one `curl` that returned 403; the fuller enumeration above comes from
the round's literature search, which tried ten routes.

Gunter & Scott give **no** proof: §6.2 was re-read from the project PDF, Theorem
18's proof box is empty, and Figure 3 is a line diagram carrying no argument. The
UPenn preprint (Gunter, Mosses & Scott, MS-CIS-89-16, 1989) is the same — it is
committed on the orchestrator's checkout at `ScottDomains/papers/Gunter Mosses
Scott 1989 Semantic Domains and Denotational Semantics MS-CIS-89-16.pdf` and will
reach this branch on merge. There is no point mining Gunter–Scott further.

Three sources that *were* obtained and are committed on this branch:

* `ScottDomains/papers/Jung 1989 Cartesian Closed Categories of Domains.pdf` —
  A. Jung, CWI Tract 66 (1989). §2.1 is titled **"The theorem of Smyth"** and
  proves the statement as Theorem 2.3. **This is the complete proof, and it is
  Jung's own** — see the attribution warning below.
* `ScottDomains/papers/Abramsky Jung Domain Theory 1994.pdf` — Abramsky & Jung,
  *Domain Theory*, Handbook of Logic in Computer Science Vol. 3, §4.3.
* `ScottDomains/papers/Plotkin 1981 Post-graduate lectures in advanced domain
  theory (Pisa notes).pdf` — the origin of the problem. Plotkin states the
  conjecture Smyth settled, and proves cases (a) and (b) together by König's
  Lemma as his "2/3 SFP Theorem" — 2/3 because it settles Figures 3a and 3b and
  not 3c. **I verified both quotations against the retrieved file rather than
  taking them from a secondary source**; the `fi`/`ffi` ligatures drop in
  extraction, so "i" reads "iff" and "nite" reads "finite".

### The proof, recovered in full

Jung's Theorem 2.3 is Theorem 18 with a *weaker* hypothesis — `D` need only be an
algebraic dcpo with least element, and only the function space need have a
countable basis:

> **Theorem 2.3 (M. B. Smyth 1983)** If `D` is an algebraic dcpo with least
> element and if `[D → D]` is ω-algebraic then `D` is bifinite.

Jung's *property m* is Gunter & Scott's Figure 3a excluded (every finite set has
a complete set of minimal upper bounds); *property M* adds Figure 3b (finitely
many of them); `U ⁿ`/`U ^∞` are the development's `mubIter`/`mubClosure` and
Figure 3c is `U ^∞` infinite. Five steps:

| # | Step | Jung | Recovered? | In the development |
| -- | ---- | ---- | ---------- | ------------------ |
| 1 | `[D → D]` continuous ⟹ property m (Figure 3a) | Theorem 1.37 | yes, statement and proof | absent; proof uses ordinals, bicompleteness and interpolation |
| 2 | `[D → D]` algebraic ⟹ `D` bifinite **or** `D` is an algebraic L-domain | Lemma 2.13, Theorem 2.14 | yes, with the explicit `f_A` family | **absent — this is the gap** |
| 3 | `[D → D]` ω-algebraic ⟹ property M (Figure 3b) | Lemma 2.17 | yes, with the explicit `f_S` family | absent |
| 4 | property M ⟹ `U ^∞(A)` finite (Figure 3c) | Lemma 2.2 | yes | ingredients present; **two steps proved this round** |
| 5 | property m + `U ^∞` finite ⟹ bifinite | Theorem 1.32 (Plotkin) | yes | **`isBifinite_iff_mubClosure`, r0028** |

Every step of *a* proof was recovered. What I could **not** recover is Smyth's
own argument: everything above is Jung's, which Jung presents as a
reconstruction ("Smyth's proof of the first part utilizes three lemmas"), and
step 3 in particular is Jung *supplying* a proof of Smyth's second lemma rather
than transcribing one.

**This matters for attribution and I initially got it too weak.** Jung's `f_S`
family **cannot** be Smyth's: it is monotone only because Lemma 2.13 has forced
`D` to be an algebraic L-domain, and L-domains are Jung's own 1988–89
contribution. What is attested of Smyth's own case-(b) lemma — from Jung's §2.1
summary and independently from Spreen, *The largest Cartesian closed category of
domains, considered constructively*, MSCS **15** (2005) 299–321, DOI
`10.1017/s0960129504004591` — is only the **conclusion**, that infinitely many
minimal upper bounds force uncountably many compact elements in the function
space. The cardinality mechanism is Smyth's; the particular uncountable family is
not. Spreen gives a third variant indexed by `ω^ω` rather than by `2^{mub}`.

For a formalization that is good news: **no family is canonical, so a future
round may pick whichever is cheapest to verify** rather than trying to reproduce
a specific one.

### Why three rounds failed, exactly — the answer the plan asked for

**Step 3 is a cardinality argument, not a perturbation.** Given compact `a₁, a₂`
with `mub{a₁, a₂}` infinite, Jung defines for **every subset** `S ⊆ mub{a₁, a₂}`

    f_S x = ⊥   if x ⋣ a₁ and x ⋣ a₂ ;   a₁  if x ⊒ a₁, x ⋣ a₂ ;
            a₂  if x ⋣ a₁ and x ⊒ a₂ ;   b₁  if x ⊒ s for some s ∈ S ;   b₂ otherwise

and shows each is a *minimal* upper bound of the compact step functions
`a₁ ↘ a₁` and `a₂ ↘ a₂`, hence compact, with `f_S ≠ f_{S'}` for `S ≠ S'`. That is
`2^ℵ⁰` compact elements of `D → D`, contradicting countability of `K(D → D)`.

**`f_S` is monotone only because step 2 has already forced `D` to be an
algebraic L-domain**, so that any element above both `a₁` and `a₂` is above
*exactly one* element of `mub{a₁, a₂}` (Jung's own justification, in the proof of
Lemma 2.17). This is the point at which the construction is Jung's rather than
Smyth's, per the attribution warning above.

That uniqueness is **precisely the side condition r0031 reported as
unavailable.** r0031 recorded the failing case as needing `g k₁ ⊑ g (x_{m₀+1})`,
with "a domain that is not bounded complete has no join to compare them at". The
development was trying to discharge that condition *directly*. It is not
directly dischargeable — it is false in general. Jung's proof reaches it only
after the bifurcation of step 2 has restricted `D` to the L-domains, where it
holds. **The missing prerequisite is Lemma 2.13, which the development does not
have in any form.** Three variants failed at the same point because they were all
attacking a statement that is false without a case split nobody had made.

Two further measurements, both from the recovered proof:

* **All three failed variants used only algebraicity of `D → D`, never
  `Domain.countable_compacts` of the function space. No such argument can
  succeed.** Abramsky & Jung §4.3: "Forming the function space of an L-domain may
  in general increase the cardinality of the basis"; their Theorem 4.3.4 says
  every cartesian closed full subcategory of `ALG⊥` is contained in `B` **or
  `aL`**, and only Theorem 4.3.5, which restricts cardinality, forces `B`.
  Without countability Theorem 18 is **false**, the algebraic L-domains being the
  counterexamples. The Lean statement `thm18 [Domain α] [Domain (ScottHom α α)]`
  is correct as written and its second `Domain` instance is load-bearing —
  specifically its `countable_compacts` field, which no attempt has yet touched.
* r0031's (★) is confirmed equivalent to Theorem 18 rather than below it, as that
  round's audit said. Jung's proof never passes through it. Grinding on (★) was
  correctly diagnosed as circular.

### What I proved toward it

Step 4's induction and its terminal contradiction — the two parts of Lemma 2.2
that need no new machinery. Both are stated for a bare `[PartialOrder α]` and a
plain function, because that is all the arguments use.

* `apply_eq_self_of_mem_mubIter` / `apply_eq_self_of_mem_mubClosure` — **a
  deflation that fixes `u` fixes all of `U ^∞(u)`.** This is Jung's "since `f` is
  below the identity it must also fix minimal upper bounds … and by induction it
  keeps all elements of `U ^∞(A)` fixed". The successor case is r0031's
  `minimalUpperBounds_subset_image` argument run for the fixed point instead of
  the image. Depends on **no axioms**.
* `not_isCompactElement_of_isLUB_strictMono` — **the least upper bound of a
  strictly ascending sequence is never compact**, the contradiction Lemma 2.2
  ends on.
* `directedOn_range_of_monotone` — the small supporting fact.

### Costed plan for the next round

Step 5 is done (r0028). Step 4 needs two more pieces: Rado's Selection Theorem
(Jung's Theorem 2.1, proved from Tychonoff; König's lemma against
`Domain.countable_compacts` is the cheaper substitute here) and Jung's Corollary
1.36, `f ≪ g` in `[D → D]` implies `f(d) ≪ g(d)`. The deflation `f` itself is
r0031's `exists_isCompactElement_le`, already proved. **Step 4 is the cheapest
remaining step and is genuinely close.**

Steps 1, 2 and 3 are each a substantial development. Step 2 is the critical path
and needs the L-domain notion (`↓x` a complete lattice for every `x`), which the
development does not define. My recommendation is to take step 4 to completion
first — it is self-contained, it makes r0031's module pay off, and it converts
the §6 `sorry` from "no known route" to "three named lemmas remaining".

**If that route is completed it should be stated and cited as Jung's theorem,
under Jung's hypotheses, not as a proof of [Smy83a].** Jung's Theorem 2.3 has a
*weaker* hypothesis than Gunter & Scott's Theorem 18 — `D` need only be an
algebraic dcpo with least element — so it implies `thm18` as stated and could
discharge that `sorry`; but the docstring and any report must say whose proof it
is.

I did **not** generate a fourth variant of the perturbation argument, and I added
no `sorry`.

## Files

* `ScottDomains/ScottDomains/Section62.lean` — new, 462 lines. Namespace
  `ScottDomains.Section62` throughout; no other file touched, so nothing can
  collide with the round's other five agents.
* `ScottDomains/papers/Jung 1989 Cartesian Closed Categories of Domains.pdf`
* `ScottDomains/papers/Abramsky Jung Domain Theory 1994.pdf`
* `ScottDomains/papers/Plotkin 1981 Post-graduate lectures in advanced domain
  theory (Pisa notes).pdf`

## Recommendation

Merge. The module is self-contained and kernel-accepted, it adds no `sorry`, and
it touches no other file. `thm16_positive` and
`thm16_positive_isEmbeddingProjectionPair` close out Theorem 16 as a settled
pair with r0032's refutation. The Theorem 18 material is the plan's obstruction
deliverable and stands independently of whether the next round pursues it: the
module docstring names the failing step, records that [Smy83a] is unobtainable,
and carries a complete alternative proof architecture with citations — correctly
attributed to Jung — so a future agent starts from a checkable argument rather
than re-deriving one.

Also worth acting on independently of §6: `docs/PaperInventory.md`'s §6.2 row
still calls `thm18` "the development's only `sorry`", contradicting its own row 6.
I did not edit that file — it is shared, and five other agents are writing this
round.
