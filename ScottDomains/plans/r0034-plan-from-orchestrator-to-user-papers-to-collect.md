---
round: r0034
from: orchestrator
to: user
subject: papers-to-collect
date: 2026-0807-00:15
status: pending
related:
  - plans/r0034-plan-from-orchestrator-to-orchestrator-six-way-remaining.md
  - reports/r0034-report-from-agent5-to-orchestrator-theorem-29-lemma-30.md
---

# r0034 — Papers to collect by hand

Sources the machine cannot retrieve, blocking specific numbered results. Each row
says what it blocks, so a partial collection is still useful — rows 1 and 2 are
the two that matter.

Destination for every file: **`ScottDomains/papers/`**, committed. Citations in
this project use the paper's own bibliography keys (`[Smy83a]`, `[Gun87]`), so
name files descriptively and cite by key.

## Blocking

| # | Reference | Full citation | Blocks | Why the machine cannot get it |
| -- | --------- | ------------- | ------ | ----------------------------- |
| 1 | `[Smy83a]` | M. Smyth. **The largest cartesian closed category of domains.** *Theoretical Computer Science* **27**:109–119, 1983. DOI `10.1016/0304-3975(83)90095-6`, PII `0304397583900956` | **Theorem 18** — the development's oldest `sorry`, open since r0027 | Legally open access (Elsevier Open Archive; Unpaywall and OpenAlex both report `is_oa=true`, bronze) but served **only** from ScienceDirect, which returns 403 behind a Cloudflare challenge on the landing page, `/pdf` and `/pdfft`, with and without browser headers. Elsevier's content API confirms `openaccess=1` but needs a key for full text. CORE holds three records, all with empty download URLs and 403 from their S3 store. Every Wayback capture of the PDF URL is 12 KB of interstitial HTML, and the archived landing page's own JSON says `displayViewFullText:false` — this legacy scan never had HTML full text. **Needs a browser session or an institutional proxy.** |
| 2 | `[Gun87]` | C. A. Gunter. **Sets and the semantics of bounded nondeterminism.** *Manuscript*, 1987 | **Theorem 29's second sentence** (universality) and **`V`**, and therefore all ten conjuncts of **Lemma 30** | Unpublished manuscript. Absent from Gunter's own publication list; nothing under that title on the web. §7.4 contains no proof of Theorem 29 at all — it states the theorem and points here. This one may require **asking Gunter directly**; it may not exist in any public form |

## Worth having, not blocking

| # | Reference | Full citation | Why |
| -- | --------- | ------------- | --- |
| 3 | `[Gun86]` | C. A. Gunter. **The largest first-order axiomatizable cartesian closed category of domains.** In A. Meyer, editor, *Logic in Computer Science*, pages 142–148. IEEE Computer Society, June 1986 | The UPenn preprint says "a similar result for the bounded complete domains can be found in [Gun86]" — the bounded-complete analogue of Theorem 18. If Theorem 18 stays open, this is the nearest provable neighbour |
| 4 | — | C. A. Gunter. **Profinite Domains** (PhD thesis, Carnegie Mellon, 1985) | The long-form source behind the two Gunter papers already collected; likely carries the `A⁺` construction in full, which is what `V` needs |
| 5 | `[Plo76]` | G. D. Plotkin. **A powerdomain construction.** *SIAM Journal of Computing* **5**:452–487, 1976 | The original for §5's Plotkin powerdomain. All three powerdomains are built and Theorem 12 is proved without it, so this is for checking wording, not for unblocking |
| 6 | `[SP82]` | M. Smyth and G. D. Plotkin. **The category-theoretic solution of recursive domain equations.** *SIAM Journal of Computing* **11**:761–783, 1982 | The inverse-limit machinery. §7 builds no `D∞`, so this is background — but it is the standard reference if `V`'s ω-colimit is built by hand |

## Already collected — do not duplicate

`ScottDomains/papers/` currently holds:

| # | File |
| -- | ---- |
| 1 | `Gunter Scott 1990.pdf` — the paper being formalized |
| 2 | `Gunter Mosses Scott 1989 … MS-CIS-89-16.pdf` — the 126-page UPenn preprint of the same chapter, carrying Theorem 18 with an empty proof box and the Figure 1.3 three-configuration discussion |
| 3 | `Gunter 1987 Universal Profinite Domains.pdf` (agent5's branch) |
| 4 | `Gunter 1985 A Universal Domain Technique for Profinite Posets.pdf` (agent5's branch) |
| 5 | `Jung 1989 Cartesian Closed Categories of Domains.pdf` (agent6's branch) |
| 6 | `Abramsky Jung Domain Theory 1994.pdf` (agent6's branch) |

Rows 3–6 land in `main` when those branches merge.

## One caution on substitutes

Jung's Lemma 2.17 is **not** Smyth's case-(b) argument, and must not be cited as
though it were. Jung's `f_S` construction depends on his own Lemma 2.13 — an
infinite `mub(A)` forces `D` to be an algebraic L-domain, so anything above
`a₁, a₂` dominates exactly one mub — and that is what makes `f_S` monotone.
Smyth had no L-domain machinery in 1983, and Jung states he is *supplying* a
proof of Smyth's second lemma, not transcribing it. Collecting row 1 is the only
way to know what Smyth actually argued.
