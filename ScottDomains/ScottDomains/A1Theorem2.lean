import ScottDomains.Kleene.Grammar

/-!
# Theorem 2: Schröder–Bernstein, by the paper's own fixed-point proof

Gunter & Scott, *Semantic Domains*, §2.2, **printed folio 6, physical PDF page 7**
of `papers/Gunter Scott 1990.pdf`; the proof runs onto **printed folio 7, physical
page 8**. Read from a 600 dpi rendering, not from `pdftotext` — this file's Type 3
bitmap fonts extract `→` as `!`.

The printed statement, verbatim (the paper prints "Schroder-Bernstein", without
the umlaut):

> *The Schroder-Bernstein Theorem.* As a set-theoretic application of the Fixed
> Point Theorem we offer the proof of the following:
>
> **Theorem 2 (Schroder-Bernstein)** *Let `S` and `T` be sets. If `f : S → T` and
> `g : T → S` are injections, then there is a bijection `h : S → T`.*

and the printed proof, verbatim:

> **Proof:** The function `Y ↦ (T − f*(S)) ∪ f*(g*(Y))` from `P T` to `P T` is
> easily seen to be continuous with respect to the inclusion ordering. Hence, by
> the Fixed Point Theorem, there is a subset
>
> `Y = (T − f*(S)) ∪ f*(g*(Y))`.
>
> In particular, `T − Y = f*(S − g*(Y))` since
>
> `T − Y = T − ((T − f*(S)) ∪ f*(g*(Y))) = (T − (T − f*(S))) ∩ (T − (f*(g*(Y))))`
> `      = f*(S) ∩ (T − (f*(g*(Y)))) = f*(S − g*(Y))`
>
> Now define `h : S → T` by
>
> `h(x) = y` if `x = g(y)` for some `y ∈ Y`; `h(x) = f(x)` otherwise.
>
> This makes sense because `g` is an injection. Moreover, `h` itself is an
> injection since `f` and `g` are injections. To see that it is a surjection,
> suppose `y ∈ T`. If `y ∈ Y`, then `h(g(y)) = y`. If `y ∉ Y`, then
> `y ∈ f*(S − g*(Y))`, so `y = f(x) = h(x)` for some `x`. Thus `h` is a bijection.

## Why this file exists

`docs/Status.md` recorded Theorem 2 as "not quoted anywhere in the tree or the
docs", and `scripts/numbered-status.sh` found no declaration carrying it.
`docs/PaperInventory.md` row 2.2 does map it to Mathlib's
`Function.Embedding.schroeder_bernstein`, but that is Zermelo's transfinite proof,
not the paper's: it is proved from `OrderHom.lfp` (Knaster–Tarski over a complete
lattice), whereas Gunter & Scott derive it from **Theorem 1**, the Kleene
fixed-point theorem for a *cpo* and a *continuous* map. `FixedPoint.lean`'s own
docstring records that neither theorem implies the other. So the paper's Theorem 2
is a distinct result-with-proof, and citing the Mathlib lemma does not discharge
it.

`Kleene/Extension.lean:18` already says `f*` "is the operator the paper's own
proof of Theorem 2 (Schröder–Bernstein) is written in" — that operator was built
there and never used. This file uses it.

## Where the work is

Continuity of `sbOp` is three lines: it is a constant union a composite of two
copies of `f*`, and `Kleene/Extension.lean` proved `f*` continuous (from
preservation of *arbitrary* unions, so directedness is never spent).

The content is `sbFix_sdiff`, the paper's four-line set computation
`T − Y = f*(S − g*(Y))`, whose last step is the only place `f`'s injectivity is
used before `h` is built (`Set.image_sdiff`). `g`'s injectivity is spent exactly
once, in surjectivity, to identify the `y'` chosen at `g y` with `y`.

`h` is defined by `dite` on `x ∈ g*(Y)`, taking the witness with `Exists.choose`.
That construction needs **no** `[Nonempty T]`: `Function.invFun g` would have
needed it, and adding it would have been a weakening of the printed statement.
-/

namespace ScottDomains.R48.Agent1

open ScottDomains ScottDomains.Kleene

variable {S T : Type*}

/-! ### The operator `Y ↦ (T − f*(S)) ∪ f*(g*(Y))` on `P T` -/

/-- The paper's operator, verbatim: `Y ↦ (T − f*(S)) ∪ f*(g*(Y))` from `P T` to
`P T`. With `S` and `T` as types, the paper's set `S` is `Set.univ`. -/
def sbOp (f : S → T) (g : T → S) (Y : Set T) : Set T :=
  (Set.univ \ extension f Set.univ) ∪ extension f (extension g Y)

/-- **The operator is continuous with respect to the inclusion ordering** — the
paper's "easily seen". A constant union the composite `f* ∘ g*`, and `f*` is
continuous by `Kleene.scottContinuous_extension`. -/
theorem scottContinuous_sbOp (f : S → T) (g : T → S) : ScottContinuous (sbOp f g) :=
  scottContinuous_union (ScottContinuous.const _)
    ((scottContinuous_extension g).comp (scottContinuous_extension f))

/-- **"Hence, by the Fixed Point Theorem, there is a subset `Y = (T − f*(S)) ∪
f*(g*(Y))`."** This is Theorem 1 applied to `sbOp`; the paper needs only that a
fixed point exists, so the leastness half is not consumed below. -/
noncomputable def sbFix (f : S → T) (g : T → S) : Set T := kleeneFix (sbOp f g)

theorem isLeast_sbFix (f : S → T) (g : T → S) :
    IsLeast {Y | sbOp f g Y = Y} (sbFix f g) :=
  theorem1 (scottContinuous_sbOp f g)

theorem sbOp_sbFix (f : S → T) (g : T → S) : sbOp f g (sbFix f g) = sbFix f g :=
  (isLeast_sbFix f g).1

/-! ### `T − Y = f*(S − g*(Y))` -/

/-- Membership in `f*(X)`, unfolded once so the `dite` below has an `Exists` to
choose from. -/
theorem mem_extension_iff (g : T → S) (Y : Set T) (x : S) :
    x ∈ extension g Y ↔ ∃ y, y ∈ Y ∧ g y = x := Iff.rfl

/-- **The paper's set computation.** For any fixed point `Y` of the operator,
`T − Y = f*(S − g*(Y))`. This is where `f`'s injectivity enters: the last of the
paper's four steps is `f*(S) ∩ (T − f*(g*(Y))) = f*(S − g*(Y))`, which is
`Set.image_sdiff`. -/
theorem sbFix_sdiff {f : S → T} {g : T → S} (hf : Function.Injective f) {Y : Set T}
    (hY : sbOp f g Y = Y) :
    Set.univ \ Y = extension f (Set.univ \ extension g Y) := by
  have himg : extension f (Set.univ \ extension g Y)
      = Set.range f \ extension f (extension g Y) := by
    show f '' (Set.univ \ extension g Y) = _
    rw [Set.image_sdiff hf, Set.image_univ]
    rfl
  have hconst : Set.univ \ extension f Set.univ = (Set.range f)ᶜ := by
    show Set.univ \ (f '' Set.univ) = _
    rw [Set.image_univ, ← Set.compl_eq_univ_sdiff]
  have hYeq : Y = (Set.range f)ᶜ ∪ extension f (extension g Y) := by
    conv_lhs => rw [← hY]
    show (Set.univ \ extension f Set.univ) ∪ extension f (extension g Y) = _
    rw [hconst]
  rw [himg]
  ext y
  constructor
  · rintro ⟨-, hy⟩
    rw [hYeq] at hy
    simp only [Set.mem_union, not_or, Set.mem_compl_iff, not_not] at hy
    exact ⟨hy.1, hy.2⟩
  · rintro ⟨hy1, hy2⟩
    refine ⟨Set.mem_univ y, ?_⟩
    rw [hYeq]
    simp only [Set.mem_union, not_or, Set.mem_compl_iff, not_not]
    exact ⟨hy1, hy2⟩

/-! ### `h(x) = y` if `x = g(y)` for some `y ∈ Y`, and `f(x)` otherwise -/

open Classical in
/-- The paper's `h : S → T`. "This makes sense because `g` is an injection" — the
witness is chosen rather than inverted, so the definition needs no `[Nonempty T]`,
and `g`'s injectivity is spent only where the paper spends it, in surjectivity. -/
noncomputable def sbBij (f : S → T) (g : T → S) (Y : Set T) (x : S) : T :=
  if hx : ∃ y, y ∈ Y ∧ g y = x then hx.choose else f x

theorem sbBij_pos (f : S → T) {g : T → S} {Y : Set T} {x : S}
    (hx : ∃ y, y ∈ Y ∧ g y = x) :
    sbBij f g Y x ∈ Y ∧ g (sbBij f g Y x) = x := by
  rw [sbBij, dif_pos hx]
  exact hx.choose_spec

theorem sbBij_neg (f : S → T) {g : T → S} {Y : Set T} {x : S}
    (hx : ¬ ∃ y, y ∈ Y ∧ g y = x) : sbBij f g Y x = f x :=
  dif_neg hx

/-- If `x` is outside `g*(Y)` then `f x` is outside `Y` — the step that makes the
two branches of `h` land in disjoint parts of `T`. Immediate from
`sbFix_sdiff`. -/
theorem apply_notMem_of_notMem {f : S → T} {g : T → S} (hf : Function.Injective f)
    {Y : Set T} (hY : sbOp f g Y = Y) {x : S} (hx : ¬ ∃ y, y ∈ Y ∧ g y = x) :
    f x ∉ Y := by
  have : f x ∈ Set.univ \ Y := by
    rw [sbFix_sdiff hf hY]
    exact ⟨x, ⟨Set.mem_univ x, fun hc => hx ((mem_extension_iff g Y x).mp hc)⟩, rfl⟩
  exact this.2

/-! ### Theorem 2 -/

/-- **Theorem 2 (Schroder-Bernstein).** *Let `S` and `T` be sets. If `f : S → T`
and `g : T → S` are injections, then there is a bijection `h : S → T`.*

Gunter & Scott, *Semantic Domains*, printed folio 6 (physical PDF page 7).

The bijection produced is the paper's own `h`, built from the fixed point that
Theorem 1 supplies for the operator `Y ↦ (T − f*(S)) ∪ f*(g*(Y))` — not Mathlib's
`Function.Embedding.schroeder_bernstein`, which routes through Knaster–Tarski. -/
theorem theorem2 (f : S → T) (g : T → S) (hf : Function.Injective f)
    (hg : Function.Injective g) : ∃ h : S → T, Function.Bijective h := by
  have hY : sbOp f g (sbFix f g) = sbFix f g := sbOp_sbFix f g
  refine ⟨sbBij f g (sbFix f g), ?_, ?_⟩
  · -- "`h` itself is an injection since `f` and `g` are injections."
    intro x₁ x₂ hx
    by_cases h1 : ∃ y, y ∈ sbFix f g ∧ g y = x₁
    · obtain ⟨hm1, he1⟩ := sbBij_pos f h1
      by_cases h2 : ∃ y, y ∈ sbFix f g ∧ g y = x₂
      · obtain ⟨-, he2⟩ := sbBij_pos f h2
        rw [← he1, ← he2, hx]
      · rw [hx, sbBij_neg f h2] at hm1
        exact absurd hm1 (apply_notMem_of_notMem hf hY h2)
    · by_cases h2 : ∃ y, y ∈ sbFix f g ∧ g y = x₂
      · obtain ⟨hm2, -⟩ := sbBij_pos f h2
        rw [← hx, sbBij_neg f h1] at hm2
        exact absurd hm2 (apply_notMem_of_notMem hf hY h1)
      · rw [sbBij_neg f h1, sbBij_neg f h2] at hx
        exact hf hx
  · -- "To see that it is a surjection, suppose `y ∈ T`."
    intro y
    by_cases hyY : y ∈ sbFix f g
    · -- "If `y ∈ Y`, then `h(g(y)) = y`."
      refine ⟨g y, ?_⟩
      obtain ⟨-, he⟩ := sbBij_pos f (⟨y, hyY, rfl⟩ : ∃ z, z ∈ sbFix f g ∧ g z = g y)
      exact hg he
    · -- "If `y ∉ Y`, then `y ∈ f*(S − g*(Y))`, so `y = f(x) = h(x)` for some `x`."
      have hmem : y ∈ Set.univ \ sbFix f g := ⟨Set.mem_univ y, hyY⟩
      rw [sbFix_sdiff hf hY] at hmem
      obtain ⟨x, hx, rfl⟩ := hmem
      exact ⟨x, sbBij_neg f fun hc => hx.2 ((mem_extension_iff g (sbFix f g) x).mpr hc)⟩

end ScottDomains.R48.Agent1
