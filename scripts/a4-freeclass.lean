/-
a4-freeclass.lean — r0044 Class 2 instrument, part C: decide which classes of
agent4's area are **freely inhabitable**, i.e. carry an instance for every object
of their ambient context.

This is the question that catches the `EffectivePresentation` mechanism, which
`#lint only unusedArguments` cannot see: there the hypothesis *is* used, and the
defect is that `Classical.dec` inhabits it at no cost, so the theorem's stated
restriction excludes nothing.  Free inhabitability is a property of the class, so
the 15-class census produced by `scripts/a4-hyps.lean` is decided once per class
here rather than once per theorem.

Every verdict below is kernel-checked — a `theorem` for FREE, a named
counterexample already in the package for NOT FREE.  Nothing is read off a source
line.

Run with `scripts/a4-run-freeclass.sh`.
-/
open ScottDomains ScottDomains.ContinuousAlgebra

namespace A4Free

universe u

/-! ## FREE — an instance exists for every object of the ambient context -/

/-- `DecidableEq α` is free for every type, by `Classical.decEq`.  This is the
exact shape of the `EffectivePresentation` defect: a decidability hypothesis that
excludes nothing.  Three declarations of the area carry one —
`ContinuousAlgebra.fold_union`, `fold_image`, `FinSets.toFinset_union` — and in
all three it is a *computation* hypothesis needed to write `Finset.union` /
`Finset.image` in the statement, not a claim of effectiveness.  Deciding whether
that is a defect is a question about what the declaration claims, which the
report answers; the freeness itself is settled here. -/
theorem free_decidableEq (α : Type u) : Nonempty (DecidableEq α) :=
  ⟨Classical.decEq α⟩

/-- `Binop E` is free for every cpo `E`: the first projection is Scott continuous,
so **every** cpo carries a continuous algebra of signature `(2)`.  Consequence: a
theorem of the form "there is a continuous algebra structure on `X`" would be
vacuous.  The area states none — `instBinopIdealCompletion` supplies the paper's
specific `⋓`, and the content is carried by the `IsSemilattice` / `IsUpper` /
`IsLower` instances proved *of that operation*. -/
theorem free_binop (E : Type u) [CompletePartialOrder E] : Nonempty (Binop E) :=
  ⟨{ op := fun a _ => a
     scottContinuous_op := by
       intro S _ hd p hp
       have h := (isLUB_prod.mp hp).1
       exact ⟨fun _ hx => by
                obtain ⟨q, hq, rfl⟩ := hx
                exact h.1 ⟨q, hq, rfl⟩,
              fun _ hb => h.2 fun _ hx => by
                obtain ⟨q, hq, rfl⟩ := hx
                exact hb ⟨q, hq, rfl⟩⟩ }⟩

/-- `Smyth.Basis D` is free for every cpo with a least element: `{⊥}` is a
non-empty finite set of compacts.  Same verdict as `Binop`, same reason it is
harmless — the area's theorems quantify over a *given* basis element and assert
nothing of the form "a basis exists". -/
theorem free_smythBasis (D : Type u) [CompletePartialOrder D] :
    Nonempty (Smyth.Basis D) :=
  ⟨{ toFinset := {⟨(⊥ : D), isCompactElement_bot⟩}, nonempty' := ⟨_, Finset.mem_singleton_self _⟩ }⟩

/-! ## NOT FREE — a counterexample already in the package

`ScottDomains.FlatSection6.not_boundedComplete_plotkin_TT` exhibits a cpo that is
a `Domain` and is **not** `BoundedComplete`, so `[BoundedComplete α]` is a genuine
restriction and not decoration.  `FlatSection6.section6_witness` packages it with
the two positive facts. -/

end A4Free

#check @ScottDomains.Flat.not_boundedComplete_plotkin_TT

namespace A4Free

/-- The first projection as a `Binop`, named so that its `op` reduces. -/
@[reducible] def fstBinop (E : Type u) [CompletePartialOrder E] : Binop E where
  op a _ := a
  scottContinuous_op := by
    intro S _ hd p hp
    have h := (isLUB_prod.mp hp).1
    exact ⟨fun _ hx => by obtain ⟨q, hq, rfl⟩ := hx; exact h.1 ⟨q, hq, rfl⟩,
           fun _ hb => h.2 fun _ hx => by obtain ⟨q, hq, rfl⟩ := hx; exact hb ⟨q, hq, rfl⟩⟩

/-- `IsSemilattice` is **not** free over an arbitrary `Binop`: at the first
projection on `Flat Bool`, commutativity fails.  So `[IsSemilattice E]`,
`[IsUpper E]` and `[IsLower E]` restrict the operation rather than decorate it. -/
theorem not_free_isSemilattice :
    ¬ ∀ (E : Type) (_ : CompletePartialOrder E) (_ : Binop E), IsSemilattice E := by
  intro h
  letI b : Binop (Flat Bool) := fstBinop (Flat Bool)
  have := (h (Flat Bool) inferInstance b).op_comm (Flat.up true) (Flat.up false)
  have hb : ∀ a c : Flat Bool, (Binop.op a c : Flat Bool) = a := fun _ _ => rfl
  rw [hb, hb] at this
  exact absurd this (by decide)

end A4Free
