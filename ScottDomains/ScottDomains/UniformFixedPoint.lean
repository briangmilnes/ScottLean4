import ScottDomains.FixedPoint
import ScottDomains.ScottHom

/-!
# Theorem 3: `fix` is the unique uniform fixed-point operator

Gunter & Scott, *Semantic Domains*, §2.3:

> **Definition:** A fixed point operator `F` is a class of continuous functions
> `F_D : (D → D) → D` such that, for each cpo `D` and continuous `f : D → D`, we
> have `F_D(f) = f(F_D(f))`.

> Let us say that a fixed point operator `F` is **uniform** if, for any pair of
> continuous functions `f : D → D` and `g : E → E` and strict continuous function
> `h : D → E` which makes [the square] commute, we have `h(F_D(f)) = F_E(g)`.

> **Theorem 3** `fix` is the unique uniform fixed point operator.

## The formalization decision

"A class of continuous functions indexed by all cpos" is not a function in Lean:
it is a family over a universe of types. `FixedPointOperator.{u}` is therefore a
structure whose field takes a type `D : Type u` **and** a `CompletePartialOrder D`
instance, and returns a map `ScottHom D D → D`. Uniformity quantifies over two
such types at once. Nothing here bumps universes: the subtype `↓fix(f)` that the
proof needs lives in the same `Type u` as `D`.

The paper also asks each `F_D` to be continuous. That hypothesis is **not used**
by the uniqueness proof and is therefore not part of the structure; adding it
would weaken the theorem.

## The proof

Given a uniform `F`, a cpo `D` and continuous `f`, the paper restricts attention
to `D₀ = {x | x ⊑ fix(f)}`:

* `D₀` is a cpo — closed under directed suprema because `fix(f)` bounds it, and
  containing `⊥`;
* `f` restricts to `f₀ : D₀ → D₀`, since `x ⊑ fix f` gives
  `f x ⊑ f (fix f) = fix f`;
* the inclusion `i : D₀ → D` is strict and continuous, and `i ∘ f₀ = f ∘ i`;
* so uniformity gives `i (F_{D₀}(f₀)) = F_D(f)`;
* and `f₀` has **exactly one** fixed point, namely `fix f`: any fixed point of
  `f₀` is a fixed point of `f` below `fix f`, and `fix f` is the least one.

Hence `F_D(f) = fix f`.
-/

namespace ScottDomains

universe u

section Iic

variable {α : Type*} [CompletePartialOrder α] {a : α}

theorem directedOn_val_image_subtype {p : α → Prop} {s : Set (Subtype p)}
    (hs : DirectedOn (· ≤ ·) s) : DirectedOn (· ≤ ·) (Subtype.val '' s) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  obtain ⟨z, hz, hxz, hyz⟩ := hs x hx y hy
  exact ⟨z.val, ⟨z, hz, rfl⟩, hxz, hyz⟩

/-- A directed set below `a` has its supremum below `a`. -/
theorem sSup_val_image_le {s : Set ↥(Set.Iic a)} (hs : DirectedOn (· ≤ ·) s) :
    sSup (Subtype.val '' s) ≤ a := by
  refine (directedOn_val_image_subtype hs).sSup_le ?_
  rintro _ ⟨x, _, rfl⟩
  exact x.2

open Classical in
/-- Suprema in `↓a`, computed in `D` when they stay below `a`. The case split is
forced by `SupSet`'s totality, exactly as in `ScottHom`; on a directed set the
first branch always applies. -/
noncomputable def IicSup (a : α) (s : Set ↥(Set.Iic a)) : ↥(Set.Iic a) :=
  if h : sSup (Subtype.val '' s) ≤ a then ⟨_, h⟩ else ⟨⊥, bot_le⟩

theorem coe_IicSup_of_le {s : Set ↥(Set.Iic a)} (h : sSup (Subtype.val '' s) ≤ a) :
    (IicSup a s).val = sSup (Subtype.val '' s) := by
  classical
  simp only [IicSup, dif_pos h]

/-- **`↓a` is a cpo**: it contains `⊥` and is closed under directed suprema. -/
@[reducible] noncomputable def IicCpo (a : α) : CompletePartialOrder ↥(Set.Iic a) :=
  { (inferInstance : PartialOrder ↥(Set.Iic a)) with
    sSup := IicSup a
    bot := ⟨⊥, bot_le⟩
    bot_le := fun _ => bot_le
    lubOfDirected := fun s hs => by
      have hle := sSup_val_image_le hs
      constructor
      · intro x hx
        show x.val ≤ (IicSup a s).val
        rw [coe_IicSup_of_le hle]
        exact (directedOn_val_image_subtype hs).le_sSup ⟨x, hx, rfl⟩
      · intro u hu
        show (IicSup a s).val ≤ u.val
        rw [coe_IicSup_of_le hle]
        refine (directedOn_val_image_subtype hs).sSup_le ?_
        rintro _ ⟨x, hx, rfl⟩
        exact hu hx }

end Iic

/-- A **fixed point operator**: a family `F_D : (D → D) → D` indexed by every cpo
in a universe, whose value is always a fixed point. -/
structure FixedPointOperator where
  /-- The operator at each cpo. -/
  op : ∀ (D : Type u) [CompletePartialOrder D], ScottHom D D → D
  /-- Its value is a fixed point. -/
  isFixedPt : ∀ (D : Type u) [CompletePartialOrder D] (f : ScottHom D D),
    f (op D f) = op D f

/-- **Uniformity**: a strict continuous `h` making the square commute transports
the operator's value. -/
def FixedPointOperator.IsUniform (F : FixedPointOperator.{u}) : Prop :=
  ∀ (D E : Type u) [CompletePartialOrder D] [CompletePartialOrder E]
    (f : ScottHom D D) (g : ScottHom E E) (h : ScottHom D E),
    h ⊥ = ⊥ → (∀ x, h (f x) = g (h x)) → h (F.op D f) = F.op E g

/-- `fix` itself, as a fixed point operator. -/
noncomputable def kleeneOperator : FixedPointOperator.{u} where
  op _ _ f := kleeneFix ⇑f
  isFixedPt _ _ f := map_kleeneFix f.scottContinuous

/-- **Theorem 3.** Every uniform fixed point operator is `fix`.

The proof is the paper's: restrict to `↓fix(f)`, where `f` has `fix(f)` as its
*unique* fixed point, and let uniformity transport the operator's value along the
inclusion. -/
theorem theorem3 (F : FixedPointOperator.{u}) (hF : F.IsUniform)
    (D : Type u) [CompletePartialOrder D] (f : ScottHom D D) :
    F.op D f = kleeneFix ⇑f := by
  have hfa : ⇑f (kleeneFix ⇑f) = kleeneFix ⇑f := map_kleeneFix f.scottContinuous
  letI : CompletePartialOrder ↥(Set.Iic (kleeneFix ⇑f)) := IicCpo _
  -- Least upper bounds in `↓fix(f)` are least upper bounds in `D`.
  have key : ∀ {s : Set ↥(Set.Iic (kleeneFix ⇑f))} {u : ↥(Set.Iic (kleeneFix ⇑f))},
      DirectedOn (· ≤ ·) s → IsLUB s u → IsLUB (Subtype.val '' s) u.val := by
    intro s u hs hu
    have hEq : u = IicSup (kleeneFix ⇑f) s := hu.unique (CompletePartialOrder.lubOfDirected s hs)
    rw [hEq, coe_IicSup_of_le (sSup_val_image_le hs)]
    exact (directedOn_val_image_subtype hs).isLUB_sSup
  -- `f` restricts to `↓fix(f)`.
  have hrestrict : ∀ x : ↥(Set.Iic (kleeneFix ⇑f)), f x.val ≤ kleeneFix ⇑f := fun x =>
    le_of_le_of_eq (f.monotone x.2) hfa
  let f₀ : ScottHom ↥(Set.Iic (kleeneFix ⇑f)) ↥(Set.Iic (kleeneFix ⇑f)) :=
    ⟨fun x => ⟨f x.val, hrestrict x⟩, by
      intro s hne hs u hu
      have hcont := f.scottContinuous (hne.image _) (directedOn_val_image_subtype hs) (key hs hu)
      constructor
      · rintro _ ⟨x, hx, rfl⟩
        exact f.monotone (hu.1 hx)
      · intro v hv
        show ⇑f u.val ≤ v.val
        refine hcont.2 ?_
        rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        exact hv ⟨x, hx, rfl⟩⟩
  -- The inclusion is continuous and strict.
  let i : ScottHom ↥(Set.Iic (kleeneFix ⇑f)) D :=
    ⟨Subtype.val, fun _ _ hs _ hu => key hs hu⟩
  -- Uniformity transports the value along the inclusion.
  have huniform := hF _ _ f₀ f i rfl (fun _ => rfl)
  -- The operator's value on `↓fix(f)` is a fixed point of `f₀`, hence `fix f`.
  have hyval : ⇑f (F.op _ f₀).val = (F.op _ f₀).val :=
    congrArg Subtype.val (F.isFixedPt _ f₀)
  rw [← huniform]
  exact le_antisymm (F.op _ f₀).2 ((theorem1 f.scottContinuous).2 hyval)

/-- `fix` is itself uniform is left to the reader by the paper; what Theorem 3
establishes is that **no other** uniform operator exists. Combined with
`kleeneOperator`, the uniform fixed point operator is unique if it exists. -/
theorem eq_kleeneOperator_op (F : FixedPointOperator.{u}) (hF : F.IsUniform)
    (D : Type u) [CompletePartialOrder D] (f : ScottHom D D) :
    F.op D f = kleeneOperator.op D f := theorem3 F hF D f

end ScottDomains
