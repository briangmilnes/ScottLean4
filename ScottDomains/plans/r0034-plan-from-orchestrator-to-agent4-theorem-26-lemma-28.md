---
round: r0034
from: orchestrator
to: agent4
subject: theorem-26-lemma-28
date: 2026-0806-22:35
status: pending
related:
  - plans/r0034-plan-from-orchestrator-to-orchestrator-six-way-remaining.md
  - plans/r0034-plan-from-orchestrator-to-agent3-universal-domain-theorem-27.md
---

# r0034 agent4 — Theorem 26 and Lemma 28

Namespace: **`ScottDomains.Combinator`**.

## Part 1 — Theorem 26

For any signature `(s₁,…,s_n)`, there are combinators `F₁,…,F_n` solving the
equations. No new carrier is needed; the machinery exists:

- **Theorem 21** (r0029, `ScottDomains.Recursive.thm21`): `F` representable over a
  cpo `U` ⟹ a domain `D` with `D ≅ F(D)`.
- `IsRepresentable₂.diag` (r0029), which with Lemma 23 already yields
  `recursiveDomain_funSpace`, the reflexive domain `D ≅ (D → D)`.
- `Recursive.Solves` / `IsSolvable` (r0029) are the vocabulary for "solving the
  equations"; state Thm 26 in those terms rather than minting new ones.

The step to design is the *signature*: `n` equations over `n` unknowns, each a
formal operator expression. Decide whether to index by `Fin n` or by a general
finite type, and say why in the docstring — the rest of §7 will reuse it.

## Part 2 — Lemma 28, proved over an abstract carrier

The seven operators `→, ×, ⊗, +, ()⊥, ()♯, ()♭` are representable over `U`.

`U` is **agent3's deliverable this round**, so do not wait on it and do not build
your own. Prove each operator representable over an *abstract* carrier satisfying
the interface Lemma 24 and Theorem 25 already use, then instantiate at agent3's
`U` after the merge.

This decoupling is sound because of a measured fact from r0032: **Lem 24 and Thm
25 were proved at cpo strength** — `Universality.lem24`, `Universality.thm25` —
with no step spending algebraicity or countability. The interface they need is
therefore weak, and seven representability proofs should not require `U`'s
specific structure. If one of them *does*, that is a real finding: name which
operator and which property of `U` it needs, and report it. Do not silently
assume `U`.

Note the operator spellings: `()♯` and `()♭` are the Smyth and Hoare powerdomains
(`pdftotext` renders `♯`/`♭` as `]`/`[`), and `+` is a different operator from the
coalesced sum `⊕`.

## Acceptance criteria

1. `thm26` proved.
2. Seven representability proofs over the abstract carrier, each named for its
   operator.
3. Instantiation at `U` **deferred to the merge and named as such in the report**
   — an unfinished instantiation is expected and is not a `sorry`. Do not add one.
4. `scripts/compile.sh -r r0034` reports 0 errors and 0 warnings beyond `sorry`.

## Process rules

1. **Namespace `ScottDomains.Combinator`** for every new declaration.
2. **Edit/Write only — never heredocs.**
3. **One command per Bash call. Never chain, never `cd`.**
4. Multi-step work becomes a script in `scripts/` — standing-authorized.
5. **Read the PDF, not the paraphrase.**
6. **Commit to branch `agent4` with `scripts/gitcp.sh`; do not push.**
7. Write `reports/r0034-report-from-agent4-to-orchestrator-theorem-26-lemma-28.md`
   with `started:`/`finished:`, the measured counts, and the exact interface your
   abstract carrier assumes — the orchestrator needs it to do the instantiation
   at merge time.
