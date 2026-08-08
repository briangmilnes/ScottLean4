# Property coverage — does every property the paper asserts have a Lean statement?

Round r0040, five agents, all five sections. Tier 2: the per-property tables are
in `reports/r0040-report-from-agentN-…`, this file merges them.

## 1. The answer

**The paper asserts 239 properties. 62 of them — 26% — have no Lean statement of
any kind.**

| # | Label | Count | Share |
| -- | ----- | ----: | ----: |
| 1 | `S+P` stated and proved | 136 | 56.9% |
| 2 | `S+H` stated, proof open | 15 | 6.3% |
| 3 | `S≠` stated, but not the paper's statement | 16 | 6.7% |
| 4 | `P` prose only, never under the kernel | 10 | 4.2% |
| 5 | `N` **not stated** | **62** | **25.9%** |
| — | **total** | **239** | |

| # | Section | Properties | numbered | prose | `N` |
| -- | ------- | ----: | ----: | ----: | ----: |
| 1 | §2, §3 (agent1) | 60 | 15 | 45 | **24** |
| 2 | §4 → Lemma 10 (agent2) | 54 | 17 | 37 | 12 |
| 3 | Thm 11 → §5 (agent3) | 29 | 12 | 17 | 9 |
| 4 | §6 (agent4) | 35 | 16 | 19 | 4 |
| 5 | §7 (agent5) | 61 | 33 | 28 | 13 |
| — | **total** | **239** | **93** | **146** | **62** |

**`PaperInventory.md` row 2e recorded this as "≥ 1".** The measurement is 62.

## 2. Why the old number was 1, and why it could only ever have been small

Two agents diagnosed the same selection bias independently. `PaperInventory.md`
row 3's prose-claim list was assembled **from claims the development proves** —
every entry names a Lean declaration — so a claim with no declaration could never
enter it. The list was structurally incapable of recording a gap, and was then
used as the coverage denominator.

The scale of the error: row 3 attributes **2** prose claims to §4; §4 states
**37**. It attributes **11** to §2/§3; they state **45**. It has **no §5 entry at
all**; §5 states 17. §7 states 28. Total prose claims 13 → **146**.

r0038 could not have found this. That round went development → paper and asked of
each of 1298 theorems what it serves; such a search finds a theorem serving
nothing but **never a property served by nothing**, because nothing points at the
gap. `sorry` cannot find it either: a `sorry` is a hole in a *stated* theorem.

## 3. The numbered results are nearly all stated — the gaps are prose

**91 of 93 numbered conjuncts are stated in some form.** Only two are `N`, and
they are the two halves of one sentence:

* **Theorem 7's second sentence** — `D → E` is effectively presented — and
* **its twin**, "similar facts hold for `D ⊸ E`", carrying the same claim to the
  strict function space.

agent1's finding is stronger than r0038's: **`EffectivePresentation` is never
instantiated at any type at all.** No domain in the development has an effective
presentation — not the function space, not `P N`. §3.2 is definitional only, and
that is the real reason `ComputableFunction.lean` is imported by nothing and is
absent from `ScottDomains.lean`. Two further §3.2 claims are also `N`: the
step-function decidability step inside Theorem 7's proof, and "all of these
operators preserve the property of having an effective presentation" — the claim
that carries §3.2 across §§4–7.

## 4. The 62 gaps by root cause

| # | Cause | Rows | Note |
| -- | ----- | ---: | ---- |
| 1 | **§4's morphism-level algebra is absent** | 11 | every object §4 defines exists and every closure property is proved, but there is no general `f × g`, `f ⊗ g`, `f ⊕ g`, `f + g`, and no multiary notation — only `U`-specialised versions built for §7 |
| 2 | **worked example objects are never constructed** | 8 | `N⊥`, `ω`, `ω⊤`, `Q`, `[0,1]`; `ℝ` occurs **0** times in the package. §5's seven `N⊥` powerdomain calculations rest on this |
| 3 | **no functorial action on a powerdomain** | 2 | no `f♮`/`f♯`/`f♭`; the same missing operation r0038 identified as the blocker for Lemma 28's `()♯`/`()♭`, now confirmed from the paper's side |
| 4 | **§2.1–§2.3 example calculus and applications** | 6 | including §2.2's factorial and grammar applications, and `kleeneFix` never bundled as a `ScottHom` so neither its continuity nor its uniformity is stated |
| 5 | **effective presentation** | 4 | §3, above |
| 6 | **§7.2's λ-calculus equations and independence claims** | 5 | no λ-term syntax; `Comb` is variable-free |
| 7 | **§6 proof-sketch steps the development deliberately skips** | 4 | it works from Theorem 14's characterization instead. Only two are claims the paper makes in its own voice |
| 8 | remainder | 22 | §7.1/§7.3 solvability and representability claims, §4's `up ∘ down ⊒ id`, and others; see the per-agent tables |

**Cheapest to close, named by the agents:** the separated-sum universal property
is *one line* — `coalescedSumCopair` at `D⊥`, `E⊥` composed with
`liftStrictHomIso`, both already proved, composite never declared. And `(T × T)♮`
not bounded complete is four elements with all four sets printed in the paper.

## 5. Rulings the streams made, and their consistency

* **A refutation decides a claim; it does not state it.** Lemma 9's items 3 and 5
  are false as printed and the development proves kernel-checked negations at
  `PUnit`-based witnesses — that is `S≠`, not `S+P` and not `N`. **Lemma 9 is 4
  of 6 as printed.** agent4 applied the same rule to Theorem 16's second
  conjunct. Two streams, one rule, reached independently.
* **A conjunct stated only inside a conjunction is stated.** Lemma 28 is 7 of 9
  proved but **9 of 9 stated**; Lemma 30 is 0 of 10 proved but **10 of 10
  stated**. Reading a proved-count as coverage would invert the meaning.
* **`ClosureProperties.lemma17` carries `[BoundedComplete β]` in its signature**,
  so all ten conjuncts inherit it *through that declaration*; the eight clean
  ones are clean only via their individual declarations.
* **`lem19` is weaker than the paper in both directions** — cpo not domain, and
  the paper's `[Domain α]` hypothesis absent. The paper's statement is
  `FinitaryProjectionPoset.IsClosure.domain_range`. A misleading duplicate, not a
  coverage gap; r0038 flagged it across an area boundary and agent4 confirmed it.

## 6. Conjunct counts that moved

| # | Result | Was | Is | Why |
| -- | ------ | --: | -: | --- |
| 1 | Theorem 1 | 1 | **2** | the printed conclusion is a conjunction: least fixed point **and** below every fixed point |
| 2 | Theorem 7 | 4 | **4, different** | the listed four are components of *one* conjunct; the real four are `D → E` bounded complete domain, `D → E` effectively presented, and the same pair for `D ⊸ E` |
| 3 | Lemma 24 | 1 | **2** | "`E ≅ E × E` **and** `D ≅ D → E`" |
| 4 | Theorem 25 | 1 | **3** | "`D ≅ D × D ≅ D → D` **and** `D` is the image of a closure on `U`" |
| — | numbered total | 87 | **93** | |

Lemma 28's 9 and Lemma 30's 10 were confirmed, not re-derived — that list is
settled by three 600 dpi reads across two rounds.

## 7. Documentation defects found

1. **Sectioning is wrong in both docs, in three places.** Theorem 14 is §6.1, not
   §4.5 (agent3). Lemmas 19 and 20 are §7.1 printed page 33, not §6 — found
   independently by agent4 and agent5. Theorem 11 is §5.2; Theorem 12 and Lemma
   13 are §5.3.
2. **`PaperInventory.md:483` names a declaration that does not exist.** Theorem 2
   is `Function.Embedding.schroeder_bernstein`, not `Function.schroeder_bernstein`.
   The row's own note records correcting an earlier draft's
   `Function.Embedding.schroederBernstein` — that draft had the namespace right
   and the casing wrong, and the correction fixed the casing and broke the
   namespace.
3. **Theorem 11's "and its converse" is wrong** — the paper states no converse;
   `thm11_converse` is a development addition.
4. **`PRepresentable.lean` carries two stale docstring claims**, both invisible to
   `lake build`: that Lemma 28 is the `Fc` notion, and that `V` does not exist.
   r0038 flagged the first; it has not been fixed.
5. **Three pairs of duplicate definitions** in §4, each with continuity proved
   twice: `ScottHom.pair`/`Combinator.prodMkHom`, `smashPair`/`smashCollapse`,
   `smashVal`/`smashEmbed`.
6. **No declaration composes Theorem 18's two remaining propositions.**
   `scripts/check-thm18-composition.sh` proves the composition typechecks, but a
   script is not a library theorem.

## 8. What this does and does not mean

It does **not** mean the formalization is 26% incomplete in any sense that
matters to the paper's mathematics. **91 of 93 numbered conjuncts are stated**,
and the two that are not are one sentence about effective presentations. The 62
are overwhelmingly the paper's *worked examples, motivating remarks and proof
sketches* — the prose a reader needs and a formalization can decline to carry.

What it does mean is that the project has been quoting a coverage figure derived
from its own output. "24 of 29 numbered results" remains true and remains the
right headline. "100 paper properties" was never a measurement, and the
theorems-per-property ratio computed from it — 13.0 : 1 — is wrong; against 239
properties it is **5.4 : 1**.

## 9. Actions

1. Replace `PaperInventory.md` row 2e's "≥ 1" with **62**, and row 3's 13 with
   **146**; restate the numbered total as 93.
2. Restate `PropertiesVsTheorems.md` §1 and its ratio: 1298 / 239 = **5.4 : 1**.
3. Fix the three sectioning errors and the `schroeder_bernstein` name.
4. Fix `PRepresentable.lean`'s two stale docstrings — flagged twice now.
5. Close the two cheap gaps: the separated-sum universal property (one line) and
   `(T × T)♮` not bounded complete (four elements).
6. Decide whether to state Theorem 7's second sentence — the only numbered gap,
   and the one that would let §3.2 stop being definitional.
