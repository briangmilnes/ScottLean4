import ScottDomains.A3Lemma30Schemes

/-!
# r0047, agent5: the unfinished proofs — the `S+H` rows re-measured, and the
# conjunct-1/2 obstruction made absolute

`S+H` in this project's label set means the paper's property is **stated as the
paper states it** and the **proof is open**. r0040 measured 15 such rows and
r0043 added 1, and `PaperInventory.md` has carried **16** ever since. No round
between r0040 and this one re-measured them: r0043 re-checked only the `N` rows
and r0044 only the `S≠` rows.

**Re-measured against this tree, the count is 12.** The derivation, row by row,
is in `reports/r0047-report-from-agent5-to-orchestrator-unfinished-proofs.md`.
Four of the sixteen are stale:

| # | Row | r0040/r0043 label | Now | Evidence in this tree |
| -- | --- | ----------------- | --- | --------------------- |
| 1 | Thm 18 (§6) | `S+H` | `S+P` | `Skeleton.Section6.theorem_18`, no `Prop` hypothesis |
| 2 | Lem 28, `(·)♯` | `S+H` | `S+P` | `R45.Agent4.repSmythAtU`, arity 0 |
| 3 | Lem 28, `(·)♭` | `S+H` | `S+P` | `R45.Agent4.repHoareAtU`, arity 0 |
| 4 | `StepFunctionsDecidable` | `S+H` | not an `S+H` row | a `Prop`-valued `def` nobody attempted; r0043 recorded it as "the nearest fit" and flagged that the taxonomy conflates the two |

The remaining **12 are §7 alone**, and `scripts/a5-r47-conditional.sh` measures
that this is the *whole* conditional surface of the package: every declaration in
the library that takes an open or refuted claim as a hypothesis lives in
`Colimit.lean`, `Lemma30.lean`, `A3Thm29.lean`, `A3Lemma30Schemes.lean` or
`Effective/FunctionSpace.lean`. **No `S+H` row has appeared in §§2–6 since
r0040** — the six rounds of edits since that measurement added none.

## The 12 rows have exactly two missing inputs

Ten of the twelve follow from `Theorem29Normal` alone, and `nine_props_ten_rows` below
is the kernel's record of it — nine propositions covering ten inventory rows,
because the prose row "`R♮(p) = Ψ♮ ∘ (p♮) ∘ Φ♮` represents the convex powerdomain"
and Lemma 30's tenth conjunct are the same Lean proposition.

The other two are Lemma 30's conjuncts 1 (`→`) and 2 (`⇸`).

## What this module adds: the conjunct-1/2 obstruction, sharpened

`Lemma30.retracts_fun_of_boundedComplete` and
`retracts_strictFun_of_boundedComplete` are the development's only route to those
two conjuncts. They take **two** hypotheses, `Colimit.Theorem29Second` and
`[BoundedComplete V]`, and both are dead:

1. `Colimit.Theorem29Second` is **refuted** (`R45.Agent3.not_thm29Second`), so those
   two declarations are vacuous as they stand. Five further declarations in
   `Lemma30.lean` are vacuous for the same reason; three of the five
   (`retracts_smash`, `retracts_sepSum`, `retracts_coalSum`) already have
   non-vacuous successors in `A3Thm29.lean`, and these two do not.
2. Repairing them to the live hypothesis does not help, and
   `not_thm29SecondAtDomains_and_boundedComplete_V` is the kernel's record of
   why: `{Theorem29SecondAtDomains, BoundedComplete V}` is a **contradictory**
   hypothesis set, by `R45.Agent3.not_boundedComplete_V`. `A3Thm29.lean:356-363`
   states this consequence in prose; here it is a theorem.

So conjuncts 1 and 2 are not merely open — the existing route cannot be repaired,
only replaced.

## Locating the remaining step: `¬ BoundedComplete V`, unconditionally

`not_boundedComplete_V` is conditional on `Theorem29SecondAtDomains`, which is itself
open. An **unconditional** `¬ BoundedComplete Colimit.V` would settle conjuncts 1
and 2's route dead regardless of how Theorem 29 turns out. This module reduces
that to a finite, purely order-theoretic fact.

`not_boundedComplete_idealCompletion` is the general half: an ideal completion is
not bounded complete as soon as its base pre-order carries **one pair with two
distinct minimal upper bounds**. The argument is short and is the standard one —
if `I` were the least upper bound of `↓a` and `↓b`, directedness of the ideal `I`
produces a `d ∈ I` above both, `I ≤ ↓c₁` and `I ≤ ↓c₂` put `d` below both minimal
bounds, and minimality collapses `c₁ = c₂`.

`V` is `IdealCompletion Ainf` (`Colimit.lean:770`), so
`not_boundedComplete_V_of_two_mubs` instantiates it. **The missing input is named
exactly**: two elements of `Colimit.Ainf` with two distinct minimal upper bounds.
This is a finite check inside one stage `Stg n` — the stages are finite
(`instFiniteStg`) and normal in `Ainf` (`isNormalIn_range_incl`), and a normal
subposet preserves minimal upper bounds, which is what `◁` is for.

**Where the witness is not**, by hand computation and *not* by the kernel — stated
so the next reader can check it rather than repeat it. `Stg (n+1)` is
`Step (Stg n) = Antisymmetrization (MPair (Stg n))` (`Colimit.lean:373, 446`), and
`m ≤ n` is `n.base ∈ m.upper ∨ (m.base = n.base ∧ m.upper = n.upper)`
(`MPair.le_iff`).

* `Stg 1` has **two** elements, `mpair_punit_eq`'s `pointA = (⊥,{⊥})` and
  `pointB = (⊥,∅)`, with `pointA < pointB`.
* `Stg 2` has **five**. The six pairs over that two-chain `{a < b}` are
  `(a,∅)`, `(a,{a})`, `(a,{b})`, `(a,{a,b})`, `(b,∅)`, `(b,{b})`; `(a,{a})` and
  `(a,{a,b})` generate the same up-set and are identified by
  `MPair.equiv_of_upper_eq`. Writing the classes `⊥ = [(a,{a})]`, `p = [(a,∅)]`,
  `q = [(a,{b})]`, `r = [(b,{b})]`, `s = [(b,∅)]`, the order is `⊥` below all,
  `q ≤ r ≤ s`, and `p` above nothing but `⊥`. Every pair with an upper bound
  there has a **least** one, so no witness occurs.

So the witness, if it exists, is at `Stg 3` or later, and finding it is arithmetic
on a finite poset rather than domain theory.
-/

namespace ScottDomains.R47.Agent5

open ScottDomains ScottDomains.BifiniteUniversal ScottDomains.PRep
open ScottDomains.Colimit ScottDomains.Lemma30

universe u

/-! ## 1. Ten of the twelve rows, from one missing input -/

/-- **Ten `S+H` rows from `Theorem29Normal` alone**, as one proposition the kernel
checks.

Nine conjuncts covering ten rows of the property inventory: row 23 is Theorem
29's second sentence at the paper's own hypothesis, rows 26–33 are Lemma 30's
conjuncts 3–10, and the prose row "`R♮(p)` represents the convex powerdomain" is
Lemma 30's tenth conjunct restated, so it is carried by the same conjunct.

The hypothesis is `Theorem29Normal` **exactly as stated, with no added instance
binder** — the composition is `Lemma30.theorem_29_secondAtDomains_of_thm29Normal`
with `R46.Agent3.eight_conjuncts_of_thm29Normal`. Rows 24 and 25, Lemma 30's
conjuncts 1 and 2, are the two this does not reach; §2 below is why. -/
theorem nine_props_ten_rows (h : Lemma30.Theorem29Normal) :
    Lemma30.Theorem29SecondAtDomains ∧
    IsPRepresentable₂ V PRep.prodOp ∧
    IsPRepresentable₂ V PRep.smashOp ∧
    IsPRepresentable₂ V PRep.sepSumOp ∧
    IsPRepresentable₂ V PRep.coalSumOp ∧
    IsPRepresentable V PRep.liftOp ∧
    IsPRepresentable V PRep.smythOp ∧
    IsPRepresentable V PRep.hoareOp ∧
    IsPRepresentable V Lemma30.plotkinOp :=
  ⟨Lemma30.theorem_29_secondAtDomains_of_thm29Normal h,
    R46.Agent3.eight_conjuncts_of_thm29Normal h⟩

/-! ## 2. Conjuncts 1 and 2: the route is contradictory, not merely open -/

/-- **`Theorem29SecondAtDomains` and `BoundedComplete V` cannot both hold.**

`A3Thm29.lean:356-363` draws this consequence in prose — "those two conjuncts are
unreachable here for as long as Theorem 29's second sentence is assumed" — from
`R45.Agent3.not_boundedComplete_V`. This is that sentence as a theorem.

Its force: repairing `Lemma30.retracts_fun_of_boundedComplete` from the refuted
`Colimit.Theorem29Second` to the live `Theorem29SecondAtDomains`, which is what
`A3Thm29.lean` did for `⊗`, `+` and `⊕`, **would not help** — the repaired
statement would still have an uninhabitable hypothesis set. Lemma 30's conjuncts
1 and 2 need a different route to `Domain (ScottHom V V)`, not a repaired one. -/
theorem not_thm29SecondAtDomains_and_boundedComplete_V :
    ¬ (Lemma30.Theorem29SecondAtDomains ∧ BoundedComplete Colimit.V) :=
  fun h => R45.Agent3.not_boundedComplete_V h.1 h.2

/-! ## 3. Reducing `¬ BoundedComplete V` to a finite check in `Ainf`

The general fact first, with no reference to this development's carriers: a base
pre-order with a non-unique minimal upper bound has a non-bounded-complete ideal
completion. -/

/-- **An ideal completion with two distinct minimal upper bounds over one pair is
not bounded complete.**

`c₁` and `c₂` are upper bounds of `{a, b}`, each minimal among the upper bounds of
that pair, and distinct. Then `↓a` and `↓b` are bounded above in
`IdealCompletion A` — by `↓c₁` — and have no least upper bound.

The proof is four steps. If `I` is the least upper bound, then `a ∈ I` and
`b ∈ I` because `↓a ≤ I` and `↓b ≤ I`; an ideal is **directed**
(`IdealCompletion.directed`), so some `d ∈ I` lies above both; `↓c₁` and `↓c₂`
are upper bounds of the pair, so `I` lies below each, putting `d ≤ c₁` and
`d ≤ c₂`; and `d` is itself an upper bound of `{a, b}`, so minimality of `c₁`
gives `c₁ ≤ d ≤ c₂` and minimality of `c₂` gives `c₂ ≤ d ≤ c₁`. Antisymmetry then
contradicts `c₁ ≠ c₂`.

Minimality is spelled out as an implication rather than through
`minimalUpperBounds` so that the hypothesis can be discharged by a direct finite
computation at a stage of the colimit, which is how the missing witness will be
supplied. -/
theorem not_boundedComplete_idealCompletion
    {A : Type u} [PartialOrder A] [OrderBot A] {a b c₁ c₂ : A}
    (ha₁ : a ≤ c₁) (hb₁ : b ≤ c₁) (ha₂ : a ≤ c₂) (hb₂ : b ≤ c₂)
    (hmin₁ : ∀ d, a ≤ d → b ≤ d → d ≤ c₁ → c₁ ≤ d)
    (hmin₂ : ∀ d, a ≤ d → b ≤ d → d ≤ c₂ → c₂ ≤ d)
    (hne : c₁ ≠ c₂) :
    ¬ BoundedComplete (IdealCompletion A) := by
  intro hbc
  haveI := hbc
  -- The pair of principal ideals, and the two bounds it is caught between.
  have hub₁ : (IdealCompletion.principal c₁ : IdealCompletion A) ∈
      upperBounds ({IdealCompletion.principal a, IdealCompletion.principal b} :
        Set (IdealCompletion A)) := by
    rintro _ (rfl | rfl)
    · exact IdealCompletion.principal_le_iff.mpr ha₁
    · exact IdealCompletion.principal_le_iff.mpr hb₁
  have hub₂ : (IdealCompletion.principal c₂ : IdealCompletion A) ∈
      upperBounds ({IdealCompletion.principal a, IdealCompletion.principal b} :
        Set (IdealCompletion A)) := by
    rintro _ (rfl | rfl)
    · exact IdealCompletion.principal_le_iff.mpr ha₂
    · exact IdealCompletion.principal_le_iff.mpr hb₂
  obtain ⟨I, hI⟩ := exists_isLUB_of_bddAbove (s := ({IdealCompletion.principal a,
    IdealCompletion.principal b} : Set (IdealCompletion A))) ⟨_, hub₁⟩
  -- `a` and `b` are members of the least upper bound.
  have haI : a ∈ I := IdealCompletion.principal_le_iff.mp (hI.1 (Set.mem_insert _ _))
  have hbI : b ∈ I :=
    IdealCompletion.principal_le_iff.mp (hI.1 (Set.mem_insert_of_mem _ rfl))
  -- Directedness of the ideal produces a single element above both.
  obtain ⟨d, hdI, had, hbd⟩ := I.directed a haI b hbI
  -- and `I` sits below each of the two minimal bounds, so `d` does too.
  have hdc₁ : d ≤ c₁ := hI.2 hub₁ hdI
  have hdc₂ : d ≤ c₂ := hI.2 hub₂ hdI
  exact hne (le_antisymm ((hmin₁ d had hbd hdc₁).trans hdc₂)
    ((hmin₂ d had hbd hdc₂).trans hdc₁))

/-- **`V` is not bounded complete as soon as `Ainf` has one non-unique minimal
upper bound**, with no appeal to Theorem 29.

`Colimit.V` is `IdealCompletion Colimit.Ainf` (`Colimit.lean:770`), so this is
the previous theorem at that base. Discharging its hypothesis would make Lemma
30's conjuncts 1 and 2 unreachable by `PRepFun.rep_arrow` and
`rep_strictArrow` **unconditionally**, where
`R45.Agent3.not_boundedComplete_V` reaches the same conclusion only under the
open `Theorem29SecondAtDomains`.

**This is the missing input, named exactly**: two elements of `Ainf` with two
distinct minimal upper bounds. `Ainf` is the antisymmetrization of the colimit of
the finite stages `Stg n`, each normal in `Ainf` (`isNormalIn_range_incl`), and a
normal subposet preserves minimal upper bounds — so a witness inside any single
stage transports, and the check is finite. -/
theorem not_boundedComplete_V_of_two_mubs {a b c₁ c₂ : Colimit.Ainf}
    (ha₁ : a ≤ c₁) (hb₁ : b ≤ c₁) (ha₂ : a ≤ c₂) (hb₂ : b ≤ c₂)
    (hmin₁ : ∀ d, a ≤ d → b ≤ d → d ≤ c₁ → c₁ ≤ d)
    (hmin₂ : ∀ d, a ≤ d → b ≤ d → d ≤ c₂ → c₂ ≤ d)
    (hne : c₁ ≠ c₂) :
    ¬ BoundedComplete Colimit.V :=
  not_boundedComplete_idealCompletion ha₁ hb₁ ha₂ hb₂ hmin₁ hmin₂ hne

/-- **The conjunct-1/2 route is dead once `Ainf` has a non-unique minimal upper
bound**, stated at the declaration that consumes it. `PRepFun.rep_arrow` requires
`[BoundedComplete U]`; at `U := V` that instance cannot exist. -/
theorem no_boundedComplete_instance_V_of_two_mubs {a b c₁ c₂ : Colimit.Ainf}
    (ha₁ : a ≤ c₁) (hb₁ : b ≤ c₁) (ha₂ : a ≤ c₂) (hb₂ : b ≤ c₂)
    (hmin₁ : ∀ d, a ≤ d → b ≤ d → d ≤ c₁ → c₁ ≤ d)
    (hmin₂ : ∀ d, a ≤ d → b ≤ d → d ≤ c₂ → c₂ ≤ d)
    (hne : c₁ ≠ c₂) :
    IsEmpty (BoundedComplete Colimit.V) :=
  ⟨not_boundedComplete_V_of_two_mubs ha₁ hb₁ ha₂ hb₂ hmin₁ hmin₂ hne⟩

end ScottDomains.R47.Agent5
