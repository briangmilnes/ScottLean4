import ScottDomains.FinitaryProjectionEmbedding
import ScottDomains.MinimalUpperBounds

/-!
# §6.2: Theorem 16's positive form, and Theorem 18's proof architecture

Gunter & Scott, *Semantic Domains*, §6.2, quoted from the source PDF:

> **Theorem 16** If `D` is bifinite, then the poset `Fp(D)` of finitary
> projections on `D` is an algebraic lattice and the inclusion map
> `i : Fp(D) ↪ (D → D)` is an embedding.

The sentence has two conjuncts and this development has settled both, in
opposite directions:

* the first, "`Fp(D)` is an algebraic lattice", is `ScottDomains.theorem_16`
  (`Skeleton/Section6b.lean`, r0028) — proved;
* the second, "`i : Fp(D) ↪ (D → D)` is an embedding", is **false**, refuted by
  the kernel in `ScottDomains/FinitaryProjectionEmbedding.lean` (r0032) at the
  five-element bifinite domain `TwoMub`.

This file supplies the missing third piece: the **hypothesis under which the
refuted conjunct does hold**, and its proof. The pair of results is then a single
settled statement rather than two loose ends — the conjunct is not simply wrong,
it is wrong at exactly the domains where `S_f` has no greatest normal subposet,
and bounded complete domains are never among them.

## The exact criterion, and what it costs

`FinitaryProjectionEmbedding.lean` records the criterion that diagnoses the
paper's sketch, `Fp.le_iff_fpBasis_subset_stableCompacts`:

> For `p ∈ Fp(D)` with basis `N = im(p) ∩ K(D)`, and `f : D → D` continuous,
> `p ⊑ f` **if and only if** `N ⊆ S_f`, where `S_f = {x ∈ K(D) | x ⊑ f(x)}`.

So a section `s : (D → D) → Fp(D)` of the inclusion exists exactly when, for
every continuous `f`, the normal subposets of `K(D)` contained in `S_f` have a
**greatest** member: that member is `s(f)`'s basis. The paper's sketch instead
builds the least normal set *containing* `S_f`, which is the opposite inclusion;
the two agree only when `S_f` is itself normal.

`HasGreatestStableNormal` below is that condition, stated in the paper's own
vocabulary. Two facts about it are proved here:

1. `theorem_16_positive` — the condition is **sufficient**. It produces a map
   `s : (D → D) → Fp(D)` with `s ∘ i = id` and `i ∘ s ⊑ id`, monotone. This is
   the literal negation of `TwoMub.not_exists_monotone_projection`, so the two
   statements together are a dichotomy and not a pair of unrelated facts.
2. `hasGreatestStableNormal_of_boundedComplete` — every **bounded complete**
   domain satisfies it, with `S_f` itself the greatest member
   (`stableCompacts_isNormalIn`). Bounded completeness is spent exactly once, on
   the least upper bound `k₁ ⊔ k₂` of two members of `S_f`: `f(k₁ ⊔ k₂)` bounds
   both, so the join is again in `S_f`, which is directedness.

The condition is also **necessary** — `isGreatest_fp_le_of_hasGreatestStableNormal`
runs in the direction that matters, and the refutation supplies the converse
failure — so the hypothesis is not an artifact chosen to make a proof go through.

Under bounded completeness the section is moreover **Scott continuous**
(`scottContinuous_fpOfStable`), so the paper's conjunct holds in full, as an
embedding–projection pair: `theorem_16_positive_isEmbeddingProjectionPair`. Its
statement is the exact negation of `TwoMub.not_isEmbeddingProjectionPair`,
including the way the inclusion `i` is passed in as a hypothesis with its
defining equation `hi : ∀ p, i p = p.val` — that is how the refutation avoids
committing to a cpo structure on `Fp(D)`, and the positive form matches it so the
two can be read against each other line by line.

Continuity is where the argument uses that `K(D)` consists of compact elements a
second time: for a directed family `T` with least upper bound `f`,
`S_f = ⋃_{g ∈ T} S_g`, because `k ⊑ f(k) = ⨆_{g ∈ T} g(k)` and compactness of `k`
puts `k ⊑ g(k)` for a single `g`. `isLUB_eval_image_of_isLUB` is the bridge.

## Scope

Nothing here restates or re-derives the refutation, which is kernel-checked in
`FinitaryProjectionEmbedding.lean`. `TwoMub` fails `HasGreatestStableNormal`
precisely because `{⊥, a, m₁}` and `{⊥, b, m₁}` are two *maximal* normal
subposets inside `S_{λx.m₁}` with no normal subposet above both — and it is not
bounded complete, which is consistent with the second result above.

# Theorem 18: a complete proof recovered — Jung's, not Smyth's

> **Theorem 18** If `D` and `D → D` are domains, then `D` is bifinite.
> "The theorem is due to Smyth and its proof may be found in [Smy83a]."

`ScottDomains.theorem_18` (`Skeleton/Section6.lean`) has been the development's only
open `sorry` in the §6 line since r0027, and three rounds (r0029–r0031) failed on
the same monotonicity side condition. r0034 read the sources rather than
re-deriving. Two results, which must not be conflated:

* **[Smy83a] itself was not obtained**, and on the evidence below is not
  machine-retrievable. Smyth's own case analysis is therefore *not* recovered.
* **A complete, checkable proof of the same theorem was recovered** — Jung's.
  It uses machinery Smyth did not have, so it is a different proof of the same
  statement, and nothing below may be attributed to [Smy83a].

Either way the reason the perturbation route failed is now exact rather than
conjectural, which is the round's deliverable.

## Sources

[Smy83a] is *The largest cartesian closed category of domains*, Theoretical
Computer Science **27** (1983) 109–119, DOI `10.1016/0304-3975(83)90095-6`, PII
`0304397583900956`. Unpaywall and OpenAlex both report it open access ("bronze")
with ScienceDirect as the *only* location on record, and Elsevier's content API
confirms `openaccess=1`; but ScienceDirect returns **HTTP 403** behind a
Cloudflare challenge on the landing page, `/pdf` and `/pdfft`, with and without
browser headers, the content API returns 401 without a key, CORE's three records
all carry empty download URLs, and every Wayback capture of the `/pdf` URL is the
interstitial challenge page. The archived landing page's own metadata says
`displayViewFullText: false` — this is a legacy scan that never had HTML full
text to archive. It needs a browser session or an institutional proxy.
**Do not spend further rounds hunting it.** It is not in `ScottDomains/papers/`.

Three sources that *are* obtained and committed there:

* `papers/Jung 1989 Cartesian Closed Categories of Domains.pdf` — A. Jung,
  *Cartesian Closed Categories of Domains*, CWI Tract 66 (1989). §2.1 is titled
  "The theorem of Smyth" and proves the statement as Theorem 2.3. **This is the
  complete proof**, and it is Jung's own; see the attribution warning below.
* `papers/Abramsky Jung Domain Theory 1994.pdf` — S. Abramsky and A. Jung,
  *Domain Theory*, Handbook of Logic in Computer Science Vol. 3; §4.3 gives the
  same material as the classification theorems 4.3.3–4.3.5.
* `papers/Plotkin 1981 Post-graduate lectures in advanced domain theory (Pisa
  notes).pdf` — the origin of the problem, and the source of cases (a) and (b) in
  their original form. Plotkin states the conjecture Smyth settled verbatim (the
  `fi`/`ffi` ligatures drop in extraction, so "i" reads "iff" and "nite" reads
  "finite"):

  > **Conjecture.** If `D` and `(D→D)` are ω-algebraic then `D` is strongly
  > algebraic. If true this would imply that SFP is the largest subcategory of
  > the ω-algebraic cpos closed under [exponentiation].

  and proves cases (a) and (b) together, by König's Lemma:

  > **Theorem 6 The 2/3 SFP Theorem.** The Lawson topology on `D` is compact iff
  > every `U({a,b})` with `a, b` finite is both complete and finite.

  "2/3" because it settles Figures 3a and 3b and not 3c. Both quotations were
  checked against the retrieved file, not taken from a secondary source.

## The proof, and the terminology map

Jung's Theorem 2.3 is Theorem 18 with a *weaker* hypothesis: `D` need only be an
algebraic dcpo with least element, and only the **function space** need have a
countable basis.

> **Theorem 2.3 (M. B. Smyth 1983)** If `D` is an algebraic dcpo with least
> element and if `[D → D]` is ω-algebraic then `D` is bifinite.

Jung's *property m* is "every finite `A` has a **complete** set of minimal upper
bounds" — Gunter & Scott's Figure 3a. *Property M* is property m together with
"every finite `A` has **finitely many** minimal upper bounds" — Figure 3b. `U ⁿ`
and `U ^∞` are the development's `mubIter` and `mubClosure`; Figure 3c is
`U ^∞(A)` infinite. The proof is four steps:

| # | Step | Jung | In this development |
| -- | ---- | ---- | ------------------- |
| 1 | `[D → D]` continuous ⟹ `K(D)` has property m (Figure 3a) | Theorem 1.37 | absent |
| 2 | `[D → D]` algebraic ⟹ `D` bifinite **or** `D` is an algebraic L-domain | Lemma 2.13, Theorem 2.14 | **absent — this is the gap** |
| 3 | `[D → D]` ω-algebraic ⟹ `K(D)` has property M (Figure 3b) | Lemma 2.17 | absent |
| 4 | property M ⟹ `U ^∞(A)` finite (Figure 3c) | Lemma 2.2 | ingredients present; two steps proved below |
| 5 | property m + `U ^∞` finite ⟹ bifinite | Theorem 1.32 (Plotkin) | **`isBifinite_iff_mubClosure`, r0028** |

## Why three rounds failed, exactly

Step 3 is where countability is spent, and it is a **cardinality argument**, not a
perturbation. Given compact `a₁, a₂` with `mub{a₁, a₂}` infinite, Jung defines for
**every subset** `S ⊆ mub{a₁, a₂}` a function

    f_S x = ⊥   if x ⋣ a₁ and x ⋣ a₂ ;   a₁  if x ⊒ a₁, x ⋣ a₂ ;
            a₂  if x ⋣ a₁ and x ⊒ a₂ ;   b₁  if x ⊒ s for some s ∈ S ;   b₂ otherwise

and shows each `f_S` is a *minimal* upper bound of the compact step functions
`a₁ ↘ a₁` and `a₂ ↘ a₂`, hence compact, with `f_S ≠ f_{S'}` for `S ≠ S'`. That is
`2 ^ℵ⁰` compact elements of `D → D`, contradicting countability of `K(D → D)`.

**Attribution warning — `f_S` is Jung's construction and cannot be Smyth's.** It
is monotone only because step 2 has already forced `D` to be an algebraic
L-domain, so that "any element above both `a₁` and `a₂` is above *exactly one*
element of `mub{a₁, a₂}`" (Jung, proof of Lemma 2.17). L-domains are Jung's own
1988–89 contribution and did not exist in 1983; Jung's wording is that he
*supplies* a proof of Smyth's second lemma, not that he transcribes one. Cite this
family as Jung's, never as [Smy83a]'s. What is attested of Smyth's own lemma —
from Jung's §2.1 summary and independently from Spreen, *The largest Cartesian
closed category of domains, considered constructively*, MSCS **15** (2005)
299–321 — is only the **conclusion**: infinitely many minimal upper bounds imply
the function space has uncountably many compact elements. The cardinality
mechanism is Smyth's; the particular uncountable family is not. Spreen gives a
third variant, indexed by `ω^ω` rather than by `2^{mub}`. For a formalization
that is good news: **no family is canonical, so pick whichever is cheapest to
verify.**

The L-domain uniqueness is precisely the side condition r0031 reported as
unavailable — its report records the failing case as needing `g k₁ ⊑ g
(x_{m₀+1})` where "a domain that is not bounded complete has no join to compare
them at". The development was trying to discharge that condition directly. It is
not dischargeable directly: it is *false* in general, and Jung's proof reaches it
only after the bifurcation of step 2 has restricted `D` to the L-domains, where
it holds. **The missing prerequisite is Lemma 2.13, which the development does
not have in any form.**

Two further measurements on the failed rounds, both from the recovered proof:

* All three variants used only algebraicity of `D → D`, never
  `Domain.countable_compacts` of the function space. No such argument can succeed:
  Abramsky & Jung, §4.3, "Forming the function space of an L-domain may in general
  increase the cardinality of the basis"; Theorem 4.3.4 says every cartesian
  closed full subcategory of `ALG⊥` is contained in `B` **or `aL`**, and only
  Theorem 4.3.5, which restricts cardinality, forces `B`. Without countability
  Theorem 18 is **false**, the algebraic L-domains being the counterexamples.
* r0031's (★) — "a compact deflation `g ⊑ id` has finite image on the upper
  bounds of `u`" — is indeed equivalent to Theorem 18 rather than below it, as
  that round's audit said. Jung's proof never passes through it.

## What is proved here

Step 4's induction and its terminal contradiction, which are the two parts of
Lemma 2.2 that need no new machinery. Jung's Lemma 2.2 runs: Rado's Selection
Theorem extracts from an infinite `U ^∞(A)` an infinite chain `C ⊆ U ^∞(A)`; a
compact `f ≪ id` fixing `A` fixes all of `U ^∞(A)`, hence fixes `⨆C`; but
Corollary 1.36 gives `f(d) ≪ d` for every `d`, making `⨆C` compact, which an
infinite strictly ascending chain cannot have as its least upper bound.

`apply_eq_self_of_mem_mubClosure` is the middle step — a deflation fixing `u`
fixes `U ^∞(u)` — and `not_isCompactElement_of_isLUB_strictMono` is the last. What
remains for step 4 is Rado's Selection Theorem (or König's lemma against
`Domain.countable_compacts`) and Corollary 1.36; the deflation `f` itself is
r0031's `exists_isCompactElement_le`, already proved.
-/

namespace ScottDomains.Section62

open ScottDomains ScottDomains.FpEmbedding

variable {α : Type*}

section Sufficient

variable [CompletePartialOrder α] [Domain α]

/-- **The hypothesis under which Theorem 16's second conjunct holds.** For every
continuous `f : D → D`, the normal subposets of `K(D)` contained in
`S_f = {x ∈ K(D) | x ⊑ f(x)}` have a greatest member.

This is the condition the paper's sketch needs and does not have. It is stated as
"greatest", not "maximal": `TwoMub` has maximal ones and no greatest one, which
is exactly the refutation. -/
def HasGreatestStableNormal (α : Type*) [CompletePartialOrder α] [Domain α] : Prop :=
  ∀ f : ScottHom α α, ∃ N : Set α, N ◁ compacts α ∧ N ⊆ stableCompacts f ∧
    ∀ N' : Set α, N' ◁ compacts α → N' ⊆ stableCompacts f → N' ⊆ N

/-- **The hypothesis, transported through Theorem 6.** A greatest normal subposet
inside `S_f` is the same thing as a greatest finitary projection below `f`: the
correspondence `N ↦ p_N` (`toFp`) is an order isomorphism onto `Fp(D)`
(`Fp.le_iff_fpBasis_subset`), and `Fp.le_iff_fpBasis_subset_stableCompacts`
identifies "below `f`" with "basis inside `S_f`".

This is the step that the refutation blocks in the other direction:
`isGreatest_of_section` shows a monotone section forces such a greatest element to
exist, and `TwoMub.not_isGreatest_below_fConst` shows it need not. -/
theorem isGreatest_fp_le_of_hasGreatestStableNormal (h : HasGreatestStableNormal α)
    (f : ScottHom α α) : ∃ p : ↥(Fp α), IsGreatest {q : ↥(Fp α) | q.val ≤ f} p := by
  obtain ⟨N, hN, hNS, hmax⟩ := h f
  refine ⟨toFp hN, ?_, fun q hq => ?_⟩
  · show (toFp hN).val ≤ f
    refine le_of_fpBasis_subset_stableCompacts ?_
    rw [fpBasis_toFp]
    exact hNS
  · refine Fp.le_iff_fpBasis_subset.mpr ?_
    rw [fpBasis_toFp]
    exact hmax _ (fpBasis_isNormalIn q) (fpBasis_subset_stableCompacts hq)

/-- **Theorem 16's second conjunct, positively.** If every `S_f` has a greatest
normal subposet, then the inclusion `i : Fp(D) ↪ (D → D)` *does* have a section
`s` below the identity — the two equations `s ∘ i = id` and `i ∘ s ⊑ id` that make
`(i, s)` an embedding–projection pair, with `s` monotone.

This is the literal negation of `ScottDomains.FpEmbedding.TwoMub.not_exists_monotone_projection`,
which refutes the same three conjuncts at a bifinite `D` where the hypothesis
fails. Read together: the conjunct is equivalent to `HasGreatestStableNormal`, and
bounded complete domains are on the true side of it
(`hasGreatestStableNormal_of_boundedComplete`).

The three components are all read off the greatest element `s f`:
membership gives `i ∘ s ⊑ id`; the upper-bound half applied to `s f ⊑ f ⊑ g`
gives monotonicity; and applied to `p ⊑ p` together with membership it gives
`s (i p) = p` by antisymmetry. -/
theorem theorem_16_positive (h : HasGreatestStableNormal α) :
    ∃ s : ScottHom α α → ↥(Fp α),
      Monotone s ∧ (∀ p : ↥(Fp α), s p.val = p) ∧ ∀ g : ScottHom α α, (s g).val ≤ g := by
  choose s hs using isGreatest_fp_le_of_hasGreatestStableNormal h
  refine ⟨s, fun f g hfg => ?_, fun p => ?_, fun g => (hs g).1⟩
  · exact (hs g).2 (le_trans (hs f).1 hfg)
  · exact le_antisymm (hs p.val).1 ((hs p.val).2 (le_refl p.val))

end Sufficient

section BoundedComplete

variable [CompletePartialOrder α] [Domain α] [BoundedComplete α]

omit [Domain α] in
/-- **In a bounded complete domain `S_f` is itself normal in `K(D)`.**

`S_f ⊆ K(D)` by definition and `⊥ ∈ S_f` supplies nonemptiness. Directedness
below any `x` is where bounded completeness is spent, once: two members `k₁, k₂`
of `S_f` below `x` are bounded, so `c = k₁ ⊔ k₂` exists; it is compact by
`isCompactElement_of_isLUB_pair`, it is below `x` because `x` bounds the pair, and
it is in `S_f` because `f(c)` is an upper bound of `{k₁, k₂}` — each `kᵢ ⊑ f(kᵢ)`
by membership and `f(kᵢ) ⊑ f(c)` by monotonicity — so the least upper bound `c`
lies below `f(c)`.

This is the exact point at which `TwoMub` differs: there `{a, b}` is bounded but
has no least upper bound, and `S_{λx.m₁} ∩ ↓m₂ = {⊥, a, b}` is not directed.

Countability of `K(D)` is not used, so the statement is `omit [Domain α]`: this is
a fact about bounded complete *algebraic* cpos. -/
theorem stableCompacts_isNormalIn (f : ScottHom α α) : stableCompacts f ◁ compacts α := by
  refine ⟨fun _ hk => hk.1, fun x _ => ⟨⟨⊥, ⟨isCompactElement_bot, bot_le⟩, bot_le⟩, ?_⟩⟩
  rintro k₁ ⟨⟨hk₁c, hk₁f⟩, hk₁x⟩ k₂ ⟨⟨hk₂c, hk₂f⟩, hk₂x⟩
  have hbdd : BddAbove ({k₁, k₂} : Set α) := by
    refine ⟨x, ?_⟩
    rintro y (rfl | rfl)
    · exact hk₁x
    · exact hk₂x
  have hlub : IsLUB ({k₁, k₂} : Set α) (sSup ({k₁, k₂} : Set α)) := isLUB_sSup_of_bddAbove hbdd
  have h₁ : k₁ ≤ sSup ({k₁, k₂} : Set α) := hlub.1 (Set.mem_insert _ _)
  have h₂ : k₂ ≤ sSup ({k₁, k₂} : Set α) := hlub.1 (Set.mem_insert_of_mem _ rfl)
  refine ⟨sSup ({k₁, k₂} : Set α), ⟨⟨isCompactElement_of_isLUB_pair hk₁c hk₂c hlub, ?_⟩, ?_⟩,
    h₁, h₂⟩
  · refine hlub.2 ?_
    rintro y (rfl | rfl)
    · exact hk₁f.trans (f.monotone h₁)
    · exact hk₂f.trans (f.monotone h₂)
  · refine hlub.2 ?_
    rintro y (rfl | rfl)
    · exact hk₁x
    · exact hk₂x

/-- **Every bounded complete domain satisfies the hypothesis**, with `S_f` itself
the greatest normal subposet inside `S_f` — a set is trivially the greatest subset
of itself once it is known to be normal.

Note that this is not a vacuous instance of the hypothesis: bounded complete
domains are bifinite (`ScottDomains.proposition_15`), so Theorem 16's own hypothesis holds
at them and its second conjunct is a real statement there. -/
theorem hasGreatestStableNormal_of_boundedComplete : HasGreatestStableNormal α :=
  fun f => ⟨stableCompacts f, stableCompacts_isNormalIn f, subset_rfl, fun _ _ hN' => hN'⟩

/-- The section itself, `f ↦ p_{S_f}`. Under bounded completeness this is the
paper's `f ↦ p_{N_f}` with the inclusion repaired: `N_f` is `S_f`, not the least
normal set containing it, and the two coincide here because `S_f` is already
normal. -/
noncomputable def fpOfStable (f : ScottHom α α) : ↥(Fp α) := toFp (stableCompacts_isNormalIn f)

@[simp] theorem fpBasis_fpOfStable (f : ScottHom α α) :
    fpBasis (fpOfStable f) = stableCompacts f := fpBasis_toFp _

/-- `i ∘ s ⊑ id`: the projection determined by `S_f` lies below `f`, by the
criterion, since its basis is `S_f`. -/
theorem fpOfStable_le (f : ScottHom α α) : (fpOfStable f).val ≤ f :=
  le_of_fpBasis_subset_stableCompacts (by rw [fpBasis_fpOfStable])

/-- `S_f` grows with `f`, so `f ↦ p_{S_f}` is monotone. -/
theorem monotone_fpOfStable : Monotone (fpOfStable (α := α)) := by
  intro f g hfg
  refine Fp.le_iff_fpBasis_subset.mpr ?_
  rw [fpBasis_fpOfStable, fpBasis_fpOfStable]
  rintro k ⟨hkc, hkf⟩
  exact ⟨hkc, hkf.trans (hfg k)⟩

/-- **The section is Scott continuous.** For a nonempty directed `d` with least
upper bound `f`, `S_f = ⋃_{g ∈ d} S_g`.

`⊇` is monotonicity. `⊆` is the only place compactness of the basis is spent a
second time: `k ∈ S_f` means `k ⊑ f(k)`, and `isLUB_eval_image_of_isLUB` makes
`f(k)` the least upper bound of the directed set `{g(k) | g ∈ d}`, so compactness
of `k` produces a single `g ∈ d` with `k ⊑ g(k)`, that is `k ∈ S_g`.

Translated through `Fp.le_iff_fpBasis_subset` — under which the order on `Fp(D)`
*is* inclusion of bases — that union statement is exactly the least-upper-bound
property of `p_{S_f}` over the image of `d`. -/
theorem scottContinuous_fpOfStable : ScottContinuous (fpOfStable (α := α)) := by
  intro d hne hd f hf
  refine ⟨?_, fun q hq => ?_⟩
  · rintro _ ⟨g, hg, rfl⟩
    exact monotone_fpOfStable (hf.1 hg)
  · refine Fp.le_iff_fpBasis_subset.mpr ?_
    rw [fpBasis_fpOfStable]
    rintro k ⟨hkc, hkf⟩
    obtain ⟨_, ⟨g, hg, rfl⟩, hkg⟩ :=
      hkc ((fun h : ScottHom α α => h k) '' d) (f k) (hne.image _)
        (ScottHom.directedOn_eval_image hd k) (ScottHom.isLUB_eval_image_of_isLUB hd hf k) hkf
    have hle : fpBasis (fpOfStable g) ⊆ fpBasis q :=
      Fp.le_iff_fpBasis_subset.mp (hq ⟨g, hg, rfl⟩)
    refine hle ?_
    rw [fpBasis_fpOfStable]
    exact ⟨hkc, hkg⟩

/-- The section as a morphism of the function space. -/
noncomputable def fpSection : ScottHom (ScottHom α α) ↥(Fp α) :=
  ⟨fpOfStable, scottContinuous_fpOfStable⟩

/-- **Theorem 16's second conjunct, in full, over a bounded complete domain.** The
inclusion `i : Fp(D) ↪ (D → D)` *is* an embedding: `(i, fpSection)` is an
embedding–projection pair in the paper's §3.1 sense,
`ScottHom.IsEmbeddingProjectionPair`.

The statement is the exact negation of
`ScottDomains.FpEmbedding.TwoMub.not_isEmbeddingProjectionPair`, down to the way
the inclusion is supplied — as a `ScottHom` `i` together with its defining
equation `hi : ∀ p, i p = p.val`. Neither side assumes a cpo structure on
`Fp(D)`; `ScottHom` needs only preorders, and `↥(Fp α)` carries the pointwise
order it inherits as a subtype.

The round trip `fpSection (i p) = p` is the sketch's own correct half: for a
finitary projection `p`, `S_p = im(p) ∩ K(D)` (`stableCompacts_val`), so the two
bases agree and `Fp.le_iff_fpBasis_subset` gives equality by antisymmetry. -/
theorem theorem_16_positive_isEmbeddingProjectionPair
    (i : ScottHom ↥(Fp α) (ScottHom α α)) (hi : ∀ p, i p = p.val) :
    ScottHom.IsEmbeddingProjectionPair i (fpSection (α := α)) := by
  refine ⟨fun p => ?_, fun g => ?_⟩
  · show fpOfStable (i p) = p
    have hb : fpBasis (fpOfStable (i p)) = fpBasis p := by
      rw [fpBasis_fpOfStable, hi p, stableCompacts_val]
    exact le_antisymm (Fp.le_iff_fpBasis_subset.mpr hb.subset)
      (Fp.le_iff_fpBasis_subset.mpr hb.symm.subset)
  · show i (fpOfStable g) ≤ g
    rw [hi (fpOfStable g)]
    exact fpOfStable_le g

end BoundedComplete

/-! ## Theorem 18, step 4: two parts of Jung's Lemma 2.2

Both are stated for a bare `[PartialOrder α]` and a plain function `g`, because
that is all the arguments use — no cpo structure, no algebraicity, and no
countability. They are the parts of case (c) — Figure 3c — that the development
can reach today, following Jung's Lemma 2.2. -/

section Theorem18

variable [PartialOrder α] {A u : Set α} {g : α → α}

/-- **A deflation that fixes `u` fixes every stage `Uⁿ(u)`.** Jung, *Cartesian
Closed Categories of Domains*, Lemma 2.2: "Since `f` is below the identity it must
also fix minimal upper bounds of subsets of `A` and by induction we see that in
fact it keeps all elements of `U ^∞(A)` fixed."

Induction on `n`. The successor case is the argument of r0031's
`minimalUpperBounds_subset_image`, run for the fixed point rather than the image:
for `m` a minimal upper bound of a finite `v ⊆ Uⁿ(u)`, the inductive hypothesis
makes every `k ∈ v` satisfy `k = g k ⊑ g m`, so `g m` is again an upper bound of
`v` lying in `A`; `g m ⊑ m` is the deflation law, and minimality of `m` then forces
`m ⊑ g m`.

`hgA` — that `g` maps `A` into `A` — is what keeps `g m` inside `upperBoundsIn A v`
so that minimality of `m` applies to it. -/
theorem apply_eq_self_of_mem_mubIter (hmono : Monotone g) (hgle : ∀ z, g z ≤ z)
    (hgA : ∀ z ∈ A, g z ∈ A) (hu : ∀ k ∈ u, g k = k) :
    ∀ n, ∀ m ∈ mubIter A u n, g m = m := by
  intro n
  induction n with
  | zero => exact hu
  | succ n ih =>
    rintro m (hm | ⟨v, hvN, -, hmub, hmin⟩)
    · exact ih m hm
    · have hgm : g m ∈ upperBoundsIn A v := by
        refine ⟨hgA m hmub.1, fun k hk => ?_⟩
        rw [← ih k (hvN hk)]
        exact hmono (hmub.2 hk)
      exact le_antisymm (hgle m) (hmin hgm (hgle m))

/-- **A deflation that fixes `u` fixes the whole mub-closure `U ^∞(u)`.** Every
member lies in some stage, and `apply_eq_self_of_mem_mubIter` fixes each stage. -/
theorem apply_eq_self_of_mem_mubClosure (hmono : Monotone g) (hgle : ∀ z, g z ≤ z)
    (hgA : ∀ z ∈ A, g z ∈ A) (hu : ∀ k ∈ u, g k = k) {m : α} (hm : m ∈ mubClosure A u) :
    g m = m := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hm
  exact apply_eq_self_of_mem_mubIter hmono hgle hgA hu n m hn

/-- The range of a monotone sequence is directed: `max` supplies the upper
bound. -/
theorem directedOn_range_of_monotone {x : ℕ → α} (hx : Monotone x) :
    DirectedOn (· ≤ ·) (Set.range x) := by
  rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
  exact ⟨x (max m n), ⟨max m n, rfl⟩, hx (le_max_left m n), hx (le_max_right m n)⟩

/-- **The terminal contradiction of Jung's Lemma 2.2.** The least upper bound of a
*strictly* ascending sequence is never compact: compactness applied to the
sequence's own range returns some `x n` with `c ⊑ x n`, and `x (n+1) ⊑ c` then
gives `x (n+1) ⊑ x n`, contradicting strictness.

In Lemma 2.2 the chain `C` is produced inside an infinite `U ^∞(A)` by Rado's
Selection Theorem, is fixed pointwise by the compact deflation `f`
(`apply_eq_self_of_mem_mubClosure`), and therefore has `f (⨆C) = ⨆C`; Corollary
1.36's `f(d) ≪ d` then makes `⨆C` compact, which this rules out. -/
theorem not_isCompactElement_of_isLUB_strictMono {x : ℕ → α} (hx : StrictMono x) {c : α}
    (hc : IsLUB (Set.range x) c) : ¬ IsCompactElement c := by
  intro hcc
  obtain ⟨_, ⟨n, rfl⟩, hcz⟩ :=
    hcc (Set.range x) c ⟨x 0, 0, rfl⟩ (directedOn_range_of_monotone hx.monotone) hc le_rfl
  have hle : x (n + 1) ≤ x n := (hc.1 ⟨n + 1, rfl⟩).trans hcz
  exact absurd (lt_of_lt_of_le (hx (Nat.lt_succ_self n)) hle) (lt_irrefl _)

end Theorem18

end ScottDomains.Section62
