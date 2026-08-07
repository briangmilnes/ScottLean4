---
round: r0036
from: orchestrator
to: agent2
subject: theorem-18
date: 2026-0807-08:32
status: pending
related:
  - plans/r0036-plan-from-orchestrator-to-orchestrator-five-way-open-results.md
---

# r0036 stream 2 — agent2 — Theorem 18

Worktree `/home/milnes/projects/ScottLean4-agent2`, branch `agent2`.
Namespace **`ScottDomains.JungSFP`**.

## The goal

`ScottDomains/Skeleton/Section6.lean:196` — the development's oldest `sorry`:

    theorem thm18 : ... -- D and D → D domains ⟹ D bifinite

## Read this first: the round is not blocked on `[Smy83a]`

Four prior rounds treated Theorem 18 as research blocked on Smyth's 1983 paper,
which is unobtainable (bronze open access, publisher-only, confirmed against
OpenAlex and Semantic Scholar). **That framing is obsolete.** r0034's agent6
recovered a complete proof from **Jung 1989, which is on disk** at
`ScottDomains/papers/Jung 1989 Cartesian Closed Categories of Domains.pdf`, and
wrote the whole route into `ScottDomains/Section62.lean:142–229`. Read that
section before anything else. `[Smy83a]` is needed for *attribution* only, and
Section62 argues that the construction cannot be Smyth's anyway.

Jung's Theorem 2.3 is Theorem 18 under a **weaker** hypothesis: `D` need only be
an algebraic dcpo with least element, and only the function space need have a
countable basis.

## The five steps, and which are absent

| # | Step | Jung's number | In the development |
| -- | ---- | ------------- | ------------------ |
| 1 | `[D → D]` continuous ⟹ `K(D)` has property m (Fig 3a) | Theorem 1.37 | **absent** |
| 2 | `[D → D]` algebraic ⟹ `D` bifinite **or** `D` is an algebraic L-domain | Lemma 2.13, Theorem 2.14 | **absent — this is the gap** |
| 3 | `[D → D]` ω-algebraic ⟹ `K(D)` has property M (Fig 3b) | Lemma 2.17 | **absent** |
| 4 | property M ⟹ `U^∞(A)` finite (Fig 3c) | Lemma 2.2 | partially proved — `apply_eq_self_of_mem_mubClosure` and `not_isCompactElement_of_isLUB_strictMono` |
| 5 | property m + `U^∞` finite ⟹ bifinite | Theorem 1.32 (Plotkin) | ✓ `isBifinite_iff_mubClosure`, r0028 |

Terminology map, already established in Section62: Jung's *property m* is "every
finite `A` has a complete set of minimal upper bounds"; *property M* is m plus
"finitely many minimal upper bounds". `U ⁿ` and `U^∞` are the development's
`mubIter` and `mubClosure`.

## Schedule step 2 first — it is the load-bearing one

Three earlier rounds failed at the same place, and Section62 diagnoses it
exactly. Step 3's uncountable family `f_S` is monotone **only because step 2 has
already forced `D` to be an algebraic L-domain**, giving "any element above both
`a₁` and `a₂` is above exactly one element of `mub{a₁,a₂}`". r0031 tried to
discharge that side condition directly; it is not directly dischargeable, because
it is **false in general** and true only after step 2's bifurcation. So step 2 is
not one of three equal tasks — it is the prerequisite the other two failures were
missing.

Two consequences recorded in Section62, both of which constrain the work:

- No argument using only algebraicity of `D → D` can succeed. **Without
  countability Theorem 18 is false**, the algebraic L-domains being the
  counterexamples (Abramsky & Jung Theorem 4.3.4 vs. 4.3.5). Every candidate
  proof must spend `Domain.countable_compacts` of the function space somewhere,
  and step 3 is where.
- r0031's (★) is *equivalent* to Theorem 18, not below it. Do not reintroduce it.

## The uncountable family is not canonical — pick the cheapest

Section62 records three: Jung's `2^{mub{a₁,a₂}}`-indexed `f_S`; Smyth's attested
conclusion only (the mechanism, not the family); and Spreen's `ω^ω`-indexed
variant (*The largest Cartesian closed category of domains, considered
constructively*, MSCS 15 (2005) 299–321). **No family is canonical, so choose
whichever is cheapest to put under the kernel**, and say in the report which one
and why. Injectivity of `S ↦ f_S` plus `K(D → D)` countable is the whole
cardinality argument; the expensive part is proving each `f_S` continuous and
minimal among upper bounds of the two compact step functions.

## Acceptance, ranked

1. `thm18` proved, `sorry` removed. Development goes to 1 `sorry` (or 0 with
   stream 1).
2. Steps 1, 2 and 3 proved as named theorems, with step 4 completed, and the
   assembly left stated — a short, precisely-located remainder.
3. **Step 2 alone — Jung's Lemma 2.13 and Theorem 2.14** — the bifurcation into
   "bifinite or algebraic L-domain". This needs `IsLDomain` defined, which the
   development does not have. This is a complete deliverable on its own and
   retires the obstacle that stopped three rounds.
4. Step 4 finished (Rado's Selection Theorem or König's lemma against
   `Domain.countable_compacts`, plus Jung's Corollary 1.36 `f(d) ≪ d`), which is
   the least entangled of the four absent steps.

Land the largest complete item. **Do not leave a new `sorry`**; an unproved step
goes in the docstring as an obstruction, in the form `Section62.lean` already
uses — that file is the template for how to write one.

## Process rules

1. Namespace `ScottDomains.JungSFP` for every new declaration. Do **not** add to
   `ScottDomains.Section62`, which is r0034's and is on `main`.
2. `Edit`/`Write` only. Never a heredoc, never `sed -i`.
3. One command per `Bash` call. Never chain, never `cd`.
4. Multi-step work becomes a script in `scripts/` — standing-authorized.
5. Build with `/home/milnes/projects/ScottLean4-agent2/scripts/compile.sh -r r0036`.
6. Read Jung 1989 directly. Abramsky & Jung 1994 §4.3 and Plotkin's Pisa notes are
   also in `ScottDomains/papers/` and carry the same material.
7. **This plan is not evidence.** The source wins; say so in the report.
8. Commit on `agent2` at every stopping point, including with build errors, using
   `/home/milnes/projects/ScottLean4-agent2/scripts/gitcp.sh "<message>" <paths>`.
   Do not push.
9. Write `reports/r0036-report-from-agent2-to-orchestrator-theorem-18.md` with
   `started:`/`finished:`, the `sorry` count before and after, and which of the
   five steps closed.
