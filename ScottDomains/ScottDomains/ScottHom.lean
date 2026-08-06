import ScottDomains.Domain

/-!
# The continuous function space `D → E` as a cpo

Gunter & Scott, *Semantic Domains*, Theorem 7, first sentence of the proof:

> Proof: (Sketch) It is not hard to see that `D → E` is a bounded complete cpo
> whenever `E` is. To prove that `D → E` is a domain we must demonstrate its
> basis. … These are called step functions …

This file formalizes the cpo structure. The step-function basis, bounded
completeness of the function space, and Theorem 7 itself are separate work:
bounded completeness needs suprema of *bounded* rather than *directed* families,
whose continuity argument is not the one below.

Mathlib has no dcpo function space. Its bundled continuous-function type is
`OmegaCompletePartialOrder.ContinuousHom` (`α →𝒄 β`), which is ω-continuous —
built on chains, not directed sets — and the paper is directed throughout.
`ScottContinuous` is a predicate with composition and constant lemmas but no
bundled type and no closure result for suprema.

## The one real proof

`scottContinuous_pointwiseSup`: the pointwise supremum of a *directed* set `d` of
Scott-continuous functions is Scott-continuous. The obvious route — expand both
sides into iterated suprema and exchange them — needs a directedness argument for
each intermediate set, and is avoidable. Writing `F x = sSup ((· x) '' d)`:

1. the evaluation image is directed, because `d` is directed pointwise;
2. `F` is monotone, by `DirectedOn.sSup_le` on that image;
3. `F a` bounds `F '' s`, from 2;
4. `F a` is least: for an upper bound `u` of `F '' s` it suffices that `f a ≤ u`
   for each `f ∈ d`; continuity of `f` reduces that to `f x ≤ u` for `x ∈ s`, and
   `f x ≤ F x ≤ u`.

No exchange, and no auxiliary directedness beyond step 1. The argument also holds
for `d = ∅`, where every appeal to `DirectedOn.sSup_le` is vacuous.

## Why `sSup` needs a case split

`CompletePartialOrder` extends `SupSet`, so `sSup` must return a `ScottHom` for
*every* set of functions — but the pointwise supremum need not be continuous.
`sSup` is therefore defined by `dite` on **continuity of the pointwise
supremum**, returning the constant-`⊥` function otherwise, since continuity is
precisely the condition under which the pointwise supremum is the right answer.
Directedness and boundedness are two sufficient conditions for it, proved
separately as `scottContinuous_pointwiseSup` and
`scottContinuous_pointwiseSup_of_bddAbove`; `coe_sSup_of_directed` and
`coe_sSup_of_bddAbove` strip the `dite` for downstream use. The cost is a
`Classical.choice` dependency in the instance.

Branching on directedness instead — as an earlier version of this file did —
makes `BoundedComplete (ScottHom α β)` false as stated, because a bounded set of
functions need not be directed and `sSup` would return the junk value on it.

`⊥` is a plain definition (`ScottHom.const ⊥`) rather than an `OrderBot`
instance, and the `CompletePartialOrder` instance splices the `PartialOrder` and
`SupSet` instances already in scope. Declaring a standalone `OrderBot` and then a
`CompletePartialOrder` that re-derives one would leave two `LE` instances with no
reason to be identified — the instance diamond that broke an `Iff.rfl` in r0004.
-/

namespace ScottDomains

variable {α β : Type*}

/-- A Scott-continuous function bundled with its continuity proof: the objects of
`D → E`. `α` needs only a `Preorder`; Scott continuity constrains `f` on the
directed subsets of `α` that have suprema and does not require `α` to be
complete. -/
structure ScottHom (α β : Type*) [Preorder α] [Preorder β] where
  /-- The underlying function. -/
  toFun : α → β
  /-- The underlying function is Scott continuous. -/
  scottContinuous' : ScottContinuous toFun

namespace ScottHom

section Preorder

variable [Preorder α] [Preorder β]

instance : FunLike (ScottHom α β) α β where
  coe := toFun
  coe_injective := by intro f g h; cases f; cases g; congr

/- UNUSED — commented out, kept for reading. The standard Mathlib idiom for
relating a structure's raw field to its `FunLike` coercion. Nothing here ever
touches `.toFun` directly — every proof goes through the coercion — so it never
fired. Keep the shape in mind: in Mathlib-style files this lemma is what stops
`simp` from leaving goals stated in terms of the underlying field.

@[simp] theorem toFun_eq_coe (f : ScottHom α β) : f.toFun = ⇑f := rfl
-/

@[ext] theorem ext {f g : ScottHom α β} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

theorem scottContinuous (f : ScottHom α β) : ScottContinuous ⇑f := f.scottContinuous'

theorem monotone (f : ScottHom α β) : Monotone ⇑f := f.scottContinuous.monotone

/-- The constant function, Scott continuous by `ScottContinuous.const`. Used both
as the least element of the function space and as the junk value of `sSup` on a
non-directed set. -/
def const (b : β) : ScottHom α β := ⟨Function.const α b, ScottContinuous.const b⟩

/- UNUSED — commented out, kept for reading. `const` itself *is* used — it is the
junk value of `sSup` and the `⊥` of the function space — but always as a term,
never rewritten through this equation.

@[simp] theorem coe_const (b : β) : ⇑(const b : ScottHom α β) = Function.const α b := rfl
-/

end Preorder

section PartialOrder

variable [Preorder α] [PartialOrder β]

/-- The pointwise order. -/
instance : PartialOrder (ScottHom α β) :=
  PartialOrder.lift (fun f => ⇑f) DFunLike.coe_injective

theorem le_def {f g : ScottHom α β} : f ≤ g ↔ ∀ x, f x ≤ g x := Iff.rfl

end PartialOrder

section CompletePartialOrder

variable [Preorder α] [CompletePartialOrder β]

/-- Evaluation carries a directed set of functions to a directed set of values.
This is the only place the pointwise order is unfolded. -/
theorem directedOn_eval_image {d : Set (ScottHom α β)} (hd : DirectedOn (· ≤ ·) d)
    (x : α) : DirectedOn (· ≤ ·) ((fun f : ScottHom α β => f x) '' d) := by
  rintro _ ⟨f, hf, rfl⟩ _ ⟨g, hg, rfl⟩
  obtain ⟨h, hh, hfh, hgh⟩ := hd f hf g hg
  exact ⟨h x, ⟨h, hh, rfl⟩, hfh x, hgh x⟩

/-- Evaluation carries a set of functions bounded above to a set of values
bounded above. -/
theorem bddAbove_eval_image {d : Set (ScottHom α β)} (hd : BddAbove d) (x : α) :
    BddAbove ((fun f : ScottHom α β => f x) '' d) := by
  obtain ⟨g, hg⟩ := hd
  refine ⟨g x, ?_⟩
  rintro _ ⟨f, hf, rfl⟩
  exact hg hf x

/-- The pointwise supremum of a set of Scott-continuous functions is
Scott-continuous as soon as `sSup` is the least upper bound of every evaluation
image. The four steps of the module docstring, in order.

Directedness is not what the argument needs — only that each evaluation image
attains its least upper bound at `sSup`. Stating it this way lets the directed
case and the bounded case share one script. -/
theorem scottContinuous_pointwiseSup_of_forall_isLUB {d : Set (ScottHom α β)}
    (h : ∀ x : α, IsLUB ((fun f : ScottHom α β => f x) '' d)
      (sSup ((fun f : ScottHom α β => f x) '' d))) :
    ScottContinuous fun x => sSup ((fun f : ScottHom α β => f x) '' d) := by
  have hmono : Monotone fun x => sSup ((fun f : ScottHom α β => f x) '' d) := by
    intro x y hxy
    refine (h x).2 ?_
    rintro _ ⟨f, hf, rfl⟩
    exact le_trans (f.monotone hxy) ((h y).1 ⟨f, hf, rfl⟩)
  intro s hne hs a ha
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hmono (ha.1 hx)
  · intro u hu
    refine (h a).2 ?_
    rintro _ ⟨f, hf, rfl⟩
    refine (f.scottContinuous hne hs ha).2 ?_
    rintro _ ⟨x, hx, rfl⟩
    exact le_trans ((h x).1 ⟨f, hf, rfl⟩) (hu ⟨x, hx, rfl⟩)

/-- The directed case: `DirectedOn.isLUB_sSup` supplies the hypothesis. -/
theorem scottContinuous_pointwiseSup {d : Set (ScottHom α β)}
    (hd : DirectedOn (· ≤ ·) d) :
    ScottContinuous fun x => sSup ((fun f : ScottHom α β => f x) '' d) :=
  scottContinuous_pointwiseSup_of_forall_isLUB fun x => (directedOn_eval_image hd x).isLUB_sSup

/-- The bounded case, when `E` is bounded complete: `isLUB_sSup_of_bddAbove`
supplies the hypothesis. This is what makes `D → E` bounded complete. -/
theorem scottContinuous_pointwiseSup_of_bddAbove [BoundedComplete β]
    {d : Set (ScottHom α β)} (hd : BddAbove d) :
    ScottContinuous fun x => sSup ((fun f : ScottHom α β => f x) '' d) :=
  scottContinuous_pointwiseSup_of_forall_isLUB fun x =>
    isLUB_sSup_of_bddAbove (bddAbove_eval_image hd x)

open Classical in
/-- Suprema are pointwise exactly when the pointwise supremum is continuous;
otherwise the value is the constant-`⊥` function. `SupSet` is total and
continuity is not, so some case split is forced — and continuity is the right
condition to split on, because it is precisely what makes the pointwise supremum
the correct answer. Directedness and boundedness are then two *sufficient*
conditions, neither privileged in the definition.

Branching on directedness instead would make `BoundedComplete (ScottHom α β)`
false as stated: a bounded set of functions need not be directed, and `sSup`
would return the junk value on it. -/
noncomputable instance : SupSet (ScottHom α β) where
  sSup d :=
    if h : ScottContinuous fun x => sSup ((fun f : ScottHom α β => f x) '' d) then ⟨_, h⟩
    else const ⊥

/-- The defining equation of `sSup`, with the case split discharged. Downstream
proofs use this and never see the `dite`. -/
theorem coe_sSup_of_continuous {d : Set (ScottHom α β)}
    (h : ScottContinuous fun x => sSup ((fun f : ScottHom α β => f x) '' d)) (x : α) :
    (sSup d) x = sSup ((fun f : ScottHom α β => f x) '' d) := by
  classical
  simp only [SupSet.sSup, dif_pos h]
  rfl

/-- The other branch: when the pointwise supremum is not continuous, `sSup` is the
constant-`⊥` function. Needed by any argument that must account for *every* set,
not only the directed ones. -/
theorem sSup_eq_const_bot {d : Set (ScottHom α β)}
    (h : ¬ ScottContinuous fun x => sSup ((fun f : ScottHom α β => f x) '' d)) :
    sSup d = const ⊥ := by
  classical
  simp only [SupSet.sSup, dif_neg h]

theorem coe_sSup_of_directed {d : Set (ScottHom α β)} (hd : DirectedOn (· ≤ ·) d) (x : α) :
    (sSup d) x = sSup ((fun f : ScottHom α β => f x) '' d) :=
  coe_sSup_of_continuous (scottContinuous_pointwiseSup hd) x


theorem coe_sSup_of_bddAbove [BoundedComplete β] {d : Set (ScottHom α β)}
    (hd : BddAbove d) (x : α) :
    (sSup d) x = sSup ((fun f : ScottHom α β => f x) '' d) :=
  coe_sSup_of_continuous (scottContinuous_pointwiseSup_of_bddAbove hd) x

/-- `D → E` is a cpo: directed sets of continuous functions have least upper
bounds, computed pointwise. The parents are spliced from the instances already in
scope so that no second `LE (ScottHom α β)` is created. -/
noncomputable instance : CompletePartialOrder (ScottHom α β) :=
  { (inferInstance : PartialOrder (ScottHom α β)),
    (inferInstance : SupSet (ScottHom α β)) with
    bot := const ⊥
    bot_le := fun _ _ => bot_le
    lubOfDirected := fun d hd => by
      constructor
      · intro f hf x
        dsimp only
        rw [coe_sSup_of_directed hd]
        exact (directedOn_eval_image hd x).le_sSup ⟨f, hf, rfl⟩
      · intro g hg x
        dsimp only
        rw [coe_sSup_of_directed hd]
        refine (directedOn_eval_image hd x).sSup_le ?_
        rintro _ ⟨f, hf, rfl⟩
        exact hg hf x }

/-- A least upper bound in the function space is a least upper bound pointwise.
The bridge from statements about `D → E` to statements about `E`: identify the
bound with `sSup` by uniqueness, then compute `sSup` pointwise.

Must come after the `CompletePartialOrder` instance — `DirectedOn.isLUB_sSup`
needs it to even elaborate. -/
theorem isLUB_eval_image_of_isLUB {d : Set (ScottHom α β)} (hd : DirectedOn (· ≤ ·) d)
    {F : ScottHom α β} (hF : IsLUB d F) (x : α) :
    IsLUB ((fun f : ScottHom α β => f x) '' d) (F x) := by
  have hFs : F = sSup d := hF.unique (DirectedOn.isLUB_sSup hd)
  rw [hFs, coe_sSup_of_directed hd]
  exact (directedOn_eval_image hd x).isLUB_sSup

/-! ### No instance diamond

The `PartialOrder` and `SupSet` inside the `CompletePartialOrder` instance are
*definitionally* the standalone instances, not re-derived copies. Were they not,
`f ≤ g` would elaborate to two different propositions depending on which instance
was in scope — the failure that broke an `Iff.rfl` in `Domain.lean`. These two
lines fail to typecheck if the splice is ever undone. -/

example : (inferInstance : PartialOrder (ScottHom α β)) =
    CompletePartialOrder.toPartialOrder := rfl

example : (inferInstance : SupSet (ScottHom α β)) = CompletePartialOrder.toSupSet := rfl

/-- `D → E` is bounded complete whenever `E` is — the rest of Theorem 7's first
sentence. Suprema of bounded sets are pointwise, by the same argument as for
directed sets with `isLUB_sSup_of_bddAbove` in place of `DirectedOn.isLUB_sSup`. -/
instance [BoundedComplete β] : BoundedComplete (ScottHom α β) where
  isLUB_sSup_of_bddAbove d hd := by
    constructor
    · intro f hf x
      dsimp only
      rw [coe_sSup_of_bddAbove hd]
      exact (isLUB_sSup_of_bddAbove (bddAbove_eval_image hd x)).1 ⟨f, hf, rfl⟩
    · intro g hg x
      dsimp only
      rw [coe_sSup_of_bddAbove hd]
      refine (isLUB_sSup_of_bddAbove (bddAbove_eval_image hd x)).2 ?_
      rintro _ ⟨f, hf, rfl⟩
      exact hg hf x

end CompletePartialOrder

end ScottHom

end ScottDomains
