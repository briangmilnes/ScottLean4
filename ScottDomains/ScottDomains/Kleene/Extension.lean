import ScottDomains.Powerset
import ScottDomains.ScottHom

/-!
# `f*`, the extension of a set function to powersets

Gunter & Scott, *Semantic Domains*, §2.1 (printed pp. 4–5):

> Given sets `S`, `T` and function `f : S → T` we define the *extension* of `f`
> to be the function `f* : P S → P T` given by taking
> `f*(X) = {f(x) | x ∈ X}` for each subset `X ⊆ S`. The function `f*` is monotone
> and, for any collection `X_i` of subsets of `S`, we have
> `f*(⋃ᵢ Xᵢ) = ⋃ᵢ f*(Xᵢ)`. In particular, `f*` is continuous.

Three assertions — monotone, union-preserving, continuous — and the r0040 audit
found no Lean statement for any of them (its row N9: `monotone_image`,
`image_sUnion`, `fStar` all grep to 0 in the package). `f*` is not decoration:
it is the operator the paper's own proof of Theorem 2 (Schröder–Bernstein) is
written in, `Y ↦ (T − f*(S)) ∪ f*(g*(Y))`.

## `ScottContinuous` on powersets, once

`scottContinuous_set_iff` is the working characterization used here and by
`Kleene/Grammar.lean`: on `P S` an operator is Scott continuous exactly when it
is monotone and carries the union of a nonempty directed family into the union of
its images. The reverse inclusion is free from monotonicity, so only one
inclusion ever has to be checked, and directedness is available where it is
needed.

`f*` preserves *arbitrary* unions, so its continuity does not use directedness at
all — the paper's "in particular" is exactly that observation.
-/

namespace ScottDomains.Kleene

variable {S T : Type*}

/-! ### Least upper bounds in `P S` -/

/-- `⋃₀ d` is the least upper bound of `d` in `P S`. -/
theorem isLUB_sUnion (d : Set (Set S)) : IsLUB d (⋃₀ d) :=
  ⟨fun _ hX _ hy => ⟨_, hX, hy⟩, fun _ hu _ hy => by
    obtain ⟨X, hX, hyX⟩ := hy
    exact hu hX hyX⟩

/-- One inclusion of Scott continuity on powersets, extracted from the
`IsLUB` form. -/
theorem sUnion_image_of_scottContinuous {F : Set S → Set T} (hF : ScottContinuous F)
    {d : Set (Set S)} (hne : d.Nonempty) (hd : DirectedOn (· ≤ ·) d) :
    F (⋃₀ d) ⊆ ⋃₀ (F '' d) :=
  (hF hne hd (isLUB_sUnion d)).2 fun _ hY _ hz => by
    obtain ⟨X, hX, rfl⟩ := hY
    exact ⟨F X, ⟨X, hX, rfl⟩, hz⟩

/-- **Scott continuity on powersets, in the form this development checks it.**
An operator on `P S` is Scott continuous exactly when it is monotone and carries
the union of a nonempty directed family into the union of the images. -/
theorem scottContinuous_set_iff {F : Set S → Set T} :
    ScottContinuous F ↔ Monotone F ∧ ∀ d : Set (Set S), d.Nonempty →
      DirectedOn (· ≤ ·) d → F (⋃₀ d) ⊆ ⋃₀ (F '' d) := by
  constructor
  · intro hF
    exact ⟨hF.monotone, fun _ hne hd => sUnion_image_of_scottContinuous hF hne hd⟩
  · rintro ⟨hmono, h⟩ d hne hd a ha
    constructor
    · rintro _ ⟨X, hX, rfl⟩
      exact hmono (ha.1 hX)
    · intro u hu
      have hsub : a ⊆ ⋃₀ d := ha.2 (isLUB_sUnion d).1
      refine (hmono hsub).trans ((h d hne hd).trans ?_)
      rintro y ⟨_, ⟨X, hX, rfl⟩, hy⟩
      exact hu ⟨X, hX, rfl⟩ hy

/-! ### `f*` -/

/-- The paper's `f* : P S → P T`, `f*(X) = {f(x) | x ∈ X}`. -/
def extension (f : S → T) (X : Set S) : Set T := f '' X

theorem extension_eq (f : S → T) (X : Set S) : extension f X = {y | ∃ x ∈ X, f x = y} := rfl

/-- **`f*` is monotone.** -/
theorem monotone_extension (f : S → T) : Monotone (extension f) :=
  fun _ _ h => Set.image_mono h

/-- **`f*(⋃ᵢ Xᵢ) = ⋃ᵢ f*(Xᵢ)`**, the paper's indexed form. -/
theorem extension_iUnion {ι : Sort*} (f : S → T) (X : ι → Set S) :
    extension f (⋃ i, X i) = ⋃ i, extension f (X i) :=
  Set.image_iUnion

/-- The same over an arbitrary family of subsets, which is what continuity
needs. No directedness and no nonemptiness. -/
theorem extension_sUnion (f : S → T) (d : Set (Set S)) :
    extension f (⋃₀ d) = ⋃₀ (extension f '' d) := by
  ext y
  constructor
  · rintro ⟨x, ⟨X, hX, hxX⟩, rfl⟩
    exact ⟨extension f X, ⟨X, hX, rfl⟩, ⟨x, hxX, rfl⟩⟩
  · rintro ⟨_, ⟨X, hX, rfl⟩, ⟨x, hxX, rfl⟩⟩
    exact ⟨x, ⟨X, hX, hxX⟩, rfl⟩

/-- **In particular, `f*` is continuous** — the paper's inference, with the
union law as its only input. -/
theorem scottContinuous_extension (f : S → T) : ScottContinuous (extension f) :=
  scottContinuous_set_iff.mpr
    ⟨monotone_extension f, fun d _ _ => le_of_eq (extension_sUnion f d)⟩

/-- `f*` as an element of `P S → P T`. -/
def extensionHom (f : S → T) : ScottHom (Set S) (Set T) :=
  ⟨extension f, scottContinuous_extension f⟩

@[simp] theorem extensionHom_apply (f : S → T) (X : Set S) : extensionHom f X = f '' X := rfl

end ScottDomains.Kleene
