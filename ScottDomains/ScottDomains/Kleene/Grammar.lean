import ScottDomains.FixedPoint
import ScottDomains.Kleene.Extension

/-!
# §2.2's second application: context-free grammars

Gunter & Scott, *Semantic Domains*, §2.2 (printed pp. 5–6). Three grammars over
an alphabet `Σ`, read off the printed page:

> 1. `E ::= ε | Ea` defines the strings of `a`'s (including the empty string `ε`).
> 2. `E ::= a | bEb` defines strings consisting either of the letter `a` alone or
>    a string of `n` `b`'s followed by an `a` followed by `n` more `b`'s.
> 3. `E ::= ε | aa | EE` defines strings of `a`'s of even length.
>
> We may use the Fixed Point Theorem to provide a precise explanation of the
> semantics of these grammars. Since the operations `X ↦ {ε} ∪ X{a}`,
> `X ↦ {a} ∪ {b}X{b}`, and `X ↦ {ε} ∪ {a}{a} ∪ XX` are all continuous in the
> variable `X`, it follows from the Fixed Point Theorem that equations such as
> … all have least solutions. These solutions are the languages defined by the
> grammars.

Three assertions, and the r0040 audit found no Lean statement for any of them
(its row N12: `grammar`, `contextFree`, `CFG`, `concatenation`, `Kleene star` all
grep to 0 in the package). This file states and proves all three: continuity of
each operator, existence of a least solution by Theorem 1, and the
identification of that solution with the language the paper names.

## Where the work is

Continuity is cheap through `scottContinuous_set_iff`: `P Σ*` is a powerset, and
each operator is built from constants, `∪`, and concatenation. Only the third
grammar's `X X` needs directedness — for `u ∈ X` and `v ∈ Y` the witness
`u ++ v ∈ Z Z` requires a single `Z ∈ M` above both — and that is precisely why
the Fixed Point Theorem is stated for *directed* families rather than for
arbitrary ones.

The identification of the solution is two inclusions, and they use the two halves
of Theorem 1 separately:

* `fix ⊆ L` from `kleeneFix_le`, since each `L` is a pre-fixed point of its
  operator;
* `L ⊆ fix` by induction on the string, using `fix = g(fix)` from
  `map_kleeneFix` to take one derivation step at a time.

No distinctness of `a` and `b` is assumed anywhere: the characterizations hold as
stated even when the alphabet has one letter.
-/

namespace ScottDomains.Kleene

variable {σ : Type*}

/-! ### Concatenation of languages -/

/-- Concatenation, the paper's juxtaposition `A B`. -/
def concat (A B : Set (List σ)) : Set (List σ) := {w | ∃ u ∈ A, ∃ v ∈ B, w = u ++ v}

theorem mem_concat {A B : Set (List σ)} {w : List σ} :
    w ∈ concat A B ↔ ∃ u ∈ A, ∃ v ∈ B, w = u ++ v := Iff.rfl

theorem append_mem_concat {A B : Set (List σ)} {u v : List σ} (hu : u ∈ A) (hv : v ∈ B) :
    u ++ v ∈ concat A B := ⟨u, hu, v, hv, rfl⟩

theorem concat_mono {A A' B B' : Set (List σ)} (hA : A ⊆ A') (hB : B ⊆ B') :
    concat A B ⊆ concat A' B' := by
  rintro _ ⟨u, hu, v, hv, rfl⟩
  exact append_mem_concat (hA hu) (hB hv)

/-! ### The continuity combinators these three operators need -/

variable {S T : Type*}

/-- A union of two continuous operators is continuous. -/
theorem scottContinuous_union {F G : Set S → Set T} (hF : ScottContinuous F)
    (hG : ScottContinuous G) : ScottContinuous fun X => F X ∪ G X := by
  refine scottContinuous_set_iff.mpr
    ⟨fun _ _ h => Set.union_subset_union (hF.monotone h) (hG.monotone h), ?_⟩
  intro d hne hd y hy
  rcases hy with hy | hy
  · obtain ⟨_, ⟨X, hX, rfl⟩, hyX⟩ := sUnion_image_of_scottContinuous hF hne hd hy
    exact ⟨F X ∪ G X, ⟨X, hX, rfl⟩, Or.inl hyX⟩
  · obtain ⟨_, ⟨X, hX, rfl⟩, hyX⟩ := sUnion_image_of_scottContinuous hG hne hd hy
    exact ⟨F X ∪ G X, ⟨X, hX, rfl⟩, Or.inr hyX⟩

/-- `X ↦ X B` is continuous. Arbitrary unions suffice; directedness is unused. -/
theorem scottContinuous_concat_right (B : Set (List σ)) :
    ScottContinuous fun X : Set (List σ) => concat X B := by
  refine scottContinuous_set_iff.mpr ⟨fun _ _ h => concat_mono h subset_rfl, ?_⟩
  rintro d _ _ _ ⟨u, ⟨X, hX, huX⟩, v, hv, rfl⟩
  exact ⟨concat X B, ⟨X, hX, rfl⟩, append_mem_concat huX hv⟩

/-- `X ↦ A X B` is continuous — the shape grammar 2 needs. -/
theorem scottContinuous_concat_sandwich (A B : Set (List σ)) :
    ScottContinuous fun X : Set (List σ) => concat A (concat X B) := by
  refine scottContinuous_set_iff.mpr
    ⟨fun _ _ h => concat_mono subset_rfl (concat_mono h subset_rfl), ?_⟩
  rintro d _ _ _ ⟨u, hu, _, ⟨v, ⟨X, hX, hvX⟩, t, ht, rfl⟩, rfl⟩
  exact ⟨concat A (concat X B), ⟨X, hX, rfl⟩,
    append_mem_concat hu (append_mem_concat hvX ht)⟩

/-- `X ↦ X X` is continuous. **This is the one operator whose continuity uses
directedness**: the two factors are drawn from possibly different members of the
family, and a single member above both is what puts the concatenation back in the
image. -/
theorem scottContinuous_concat_diag :
    ScottContinuous fun X : Set (List σ) => concat X X := by
  refine scottContinuous_set_iff.mpr ⟨fun _ _ h => concat_mono h h, ?_⟩
  rintro d _ hd _ ⟨u, ⟨X, hX, huX⟩, v, ⟨Y, hY, hvY⟩, rfl⟩
  obtain ⟨Z, hZ, hXZ, hYZ⟩ := hd X hX Y hY
  exact ⟨concat Z Z, ⟨Z, hZ, rfl⟩, append_mem_concat (hXZ huX) (hYZ hvY)⟩

/-! ### The three grammars -/

variable (a b : σ)

/-- `X ↦ {ε} ∪ X{a}`, from `E ::= ε | Ea`. -/
def gram1 (X : Set (List σ)) : Set (List σ) := {[]} ∪ concat X {[a]}

/-- `X ↦ {a} ∪ {b}X{b}`, from `E ::= a | bEb`. -/
def gram2 (X : Set (List σ)) : Set (List σ) := {[a]} ∪ concat {[b]} (concat X {[b]})

/-- `X ↦ {ε} ∪ {a}{a} ∪ XX`, from `E ::= ε | aa | EE`. -/
def gram3 (X : Set (List σ)) : Set (List σ) :=
  ({[]} ∪ concat {[a]} {[a]}) ∪ concat X X

/-- **The first operator is continuous in `X`.** -/
theorem scottContinuous_gram1 : ScottContinuous (gram1 a) :=
  scottContinuous_union (ScottContinuous.const _) (scottContinuous_concat_right _)

/-- **The second operator is continuous in `X`.** -/
theorem scottContinuous_gram2 : ScottContinuous (gram2 a b) :=
  scottContinuous_union (ScottContinuous.const _) (scottContinuous_concat_sandwich _ _)

/-- **The third operator is continuous in `X`.** -/
theorem scottContinuous_gram3 : ScottContinuous (gram3 a) :=
  scottContinuous_union (ScottContinuous.const _) scottContinuous_concat_diag

/-! ### The three equations have least solutions

This is the Fixed Point Theorem applied three times; the paper draws exactly this
inference. -/

/-- `X = {ε} ∪ X{a}` has a least solution. -/
theorem isLeast_gram1 : IsLeast {X | gram1 a X = X} (kleeneFix (gram1 a)) :=
  theorem1 (scottContinuous_gram1 a)

/-- `X = {a} ∪ {b}X{b}` has a least solution. -/
theorem isLeast_gram2 : IsLeast {X | gram2 a b X = X} (kleeneFix (gram2 a b)) :=
  theorem1 (scottContinuous_gram2 a b)

/-- `X = {ε} ∪ {a}{a} ∪ XX` has a least solution. -/
theorem isLeast_gram3 : IsLeast {X | gram3 a X = X} (kleeneFix (gram3 a)) :=
  theorem1 (scottContinuous_gram3 a)

/-! ### The solutions are the languages defined by the grammars -/

/-- The strings of `a`'s, `{aⁿ | n ∈ N}`. -/
def langStar (a : σ) : Set (List σ) := {w | ∃ n : ℕ, w = List.replicate n a}

/-- `{bⁿ a bⁿ | n ∈ N}`. -/
def langNest (a b : σ) : Set (List σ) :=
  {w | ∃ n : ℕ, w = List.replicate n b ++ a :: List.replicate n b}

/-- The strings of `a`'s of even length, `{a²ⁿ | n ∈ N}`. -/
def langEven (a : σ) : Set (List σ) := {w | ∃ n : ℕ, w = List.replicate (2 * n) a}

/-- **Grammar 1's least solution is the language of strings of `a`'s.** -/
theorem kleeneFix_gram1 : kleeneFix (gram1 a) = langStar a := by
  have hfix : gram1 a (kleeneFix (gram1 a)) = kleeneFix (gram1 a) :=
    map_kleeneFix (scottContinuous_gram1 a)
  refine le_antisymm ?_ ?_
  · refine kleeneFix_le (scottContinuous_gram1 a).monotone (le_of_eq ?_)
    ext w
    constructor
    · rintro (hw | ⟨u, ⟨n, rfl⟩, _, hv, rfl⟩)
      · exact ⟨0, hw⟩
      · rw [Set.mem_singleton_iff] at hv
        subst hv
        exact ⟨n + 1, List.replicate_succ'.symm⟩
    · rintro ⟨n, rfl⟩
      cases n with
      | zero => exact Or.inl rfl
      | succ k =>
        refine Or.inr ?_
        rw [List.replicate_succ']
        exact append_mem_concat ⟨k, rfl⟩ rfl
  · rintro _ ⟨n, rfl⟩
    induction n with
    | zero => exact hfix ▸ Or.inl rfl
    | succ k ih =>
      refine hfix ▸ Or.inr ?_
      rw [List.replicate_succ']
      exact append_mem_concat ih rfl

/-- **Grammar 2's least solution is `{bⁿ a bⁿ}`.** -/
theorem kleeneFix_gram2 : kleeneFix (gram2 a b) = langNest a b := by
  have hfix : gram2 a b (kleeneFix (gram2 a b)) = kleeneFix (gram2 a b) :=
    map_kleeneFix (scottContinuous_gram2 a b)
  have hb : ∀ n : ℕ, List.replicate n b ++ [b] = b :: List.replicate n b := by
    intro n
    rw [← List.replicate_succ', List.replicate_succ]
  have hstep : ∀ n : ℕ, [b] ++ ((List.replicate n b ++ a :: List.replicate n b) ++ [b]) =
      List.replicate (n + 1) b ++ a :: List.replicate (n + 1) b := by
    intro n
    simp only [List.replicate_succ, List.cons_append, List.nil_append, List.append_assoc,
      hb n]
  refine le_antisymm ?_ ?_
  · refine kleeneFix_le (scottContinuous_gram2 a b).monotone (le_of_eq ?_)
    ext w
    constructor
    · rintro (hw | ⟨u, hu, _, ⟨v, ⟨n, rfl⟩, t, ht, rfl⟩, rfl⟩)
      · rw [Set.mem_singleton_iff] at hw
        exact ⟨0, by simp [hw]⟩
      · rw [Set.mem_singleton_iff] at hu ht
        subst hu; subst ht
        exact ⟨n + 1, hstep n⟩
    · rintro ⟨n, rfl⟩
      cases n with
      | zero => exact Or.inl (by simp)
      | succ k =>
        refine Or.inr ?_
        rw [← hstep k]
        exact append_mem_concat rfl (append_mem_concat ⟨k, rfl⟩ rfl)
  · rintro _ ⟨n, rfl⟩
    induction n with
    | zero => exact hfix ▸ Or.inl (by simp)
    | succ k ih =>
      refine hfix ▸ Or.inr ?_
      rw [← hstep k]
      exact append_mem_concat rfl (append_mem_concat ih rfl)

/-- **Grammar 3's least solution is the language of strings of `a`'s of even
length.** -/
theorem kleeneFix_gram3 : kleeneFix (gram3 a) = langEven a := by
  have hfix : gram3 a (kleeneFix (gram3 a)) = kleeneFix (gram3 a) :=
    map_kleeneFix (scottContinuous_gram3 a)
  have haa : [a, a] = List.replicate (2 * 1) a := by simp [List.replicate_succ]
  refine le_antisymm ?_ ?_
  · refine kleeneFix_le (scottContinuous_gram3 a).monotone (le_of_eq ?_)
    ext w
    constructor
    · rintro ((hw | ⟨u, hu, v, hv, rfl⟩) | ⟨u, ⟨m, rfl⟩, v, ⟨n, rfl⟩, rfl⟩)
      · exact ⟨0, by simpa using hw⟩
      · rw [Set.mem_singleton_iff] at hu hv
        subst hu; subst hv
        exact ⟨1, haa⟩
      · exact ⟨m + n, by rw [Nat.mul_add, List.replicate_add]⟩
    · rintro ⟨n, rfl⟩
      cases n with
      | zero => exact Or.inl (Or.inl (by simp))
      | succ k =>
        refine Or.inr ?_
        have : 2 * (k + 1) = 2 * k + 2 * 1 := by omega
        rw [this, List.replicate_add]
        exact append_mem_concat ⟨k, rfl⟩ ⟨1, rfl⟩
  · rintro _ ⟨n, rfl⟩
    induction n with
    | zero => exact hfix ▸ Or.inl (Or.inl (by simp))
    | succ k ih =>
      have hmem : List.replicate (2 * 1) a ∈ kleeneFix (gram3 a) := by
        refine hfix ▸ Or.inl (Or.inr ?_)
        rw [← haa]
        exact ⟨[a], rfl, [a], rfl, rfl⟩
      refine hfix ▸ Or.inr ?_
      have : 2 * (k + 1) = 2 * k + 2 * 1 := by omega
      rw [this, List.replicate_add]
      exact append_mem_concat ih hmem

end ScottDomains.Kleene
