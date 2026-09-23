import Mathlib

namespace TaoExercise9_9_5

open Set

/-!
============================================================
Proposition 9.9.15

If E ⊆ ℝ is bounded and
f : E → ℝ is uniformly continuous,
then f(E) is bounded.

Since f has domain E as a subtype,
f(E) is simply Set.range f.
============================================================
-/

theorem proposition_9_9_15
    (E : Set ℝ)
    (f : E → ℝ)
    (hE : Bornology.IsBounded E)
    (hf : UniformContinuous f) :
    Bornology.IsBounded (Set.range f) := by

  /-
  Step 1:
  A bounded subset of ℝ has compact closure.
  -/

  have hCompactClosure :
      IsCompact (closure E) := by
    exact hE.isCompact_closure

  /-
  Step 2:
  Hence closure E is totally bounded.
  -/

  have hClosureTotallyBounded :
      TotallyBounded (closure E) := by
    exact hCompactClosure.totallyBounded

  /-
  Step 3:
  Therefore E itself is totally bounded.
  -/

  have hETotallyBounded :
      TotallyBounded E := by
    exact TotallyBounded.subset
      subset_closure
      hClosureTotallyBounded

  /-
  Step 4:
  Regard E as a type.  The subtype map

      E → ℝ

  is a uniform embedding.

  Pulling E back by this map gives all of the subtype E.
  -/

  have hDomainTotallyBounded :
      TotallyBounded (Set.univ : Set E) := by

    have hpre :
        TotallyBounded
          (Subtype.val ⁻¹' E : Set E) := by
      exact totallyBounded_preimage
        isUniformEmbedding_subtype_val.isUniformInducing
        hETotallyBounded

    have hpreEq :
        (Subtype.val ⁻¹' E : Set E) = Set.univ := by
      ext x
      constructor
      · intro hx
        trivial
      · intro hx
        exact x.property

    rw [hpreEq] at hpre

    exact hpre

  /-
  Step 5:
  Uniform continuity sends totally bounded sets
  to totally bounded sets.
  -/

  have hImageTotallyBounded :
      TotallyBounded (f '' (Set.univ : Set E)) := by
    exact hDomainTotallyBounded.image hf

  /-
  Step 6:
  The image of the whole subtype is Set.range f.
  -/

  have hRangeTotallyBounded :
      TotallyBounded (Set.range f) := by

    have hImageEq :
        f '' (Set.univ : Set E) = Set.range f := by
      ext y

      constructor

      · intro hy
        rcases hy with ⟨x, hx, rfl⟩
        exact ⟨x, rfl⟩

      · intro hy
        rcases hy with ⟨x, rfl⟩
        exact ⟨x, Set.mem_univ x, rfl⟩

    rw [← hImageEq]

    exact hImageTotallyBounded

  /-
  Step 7:
  Every totally bounded subset of a metric space
  is bounded.
  -/

  exact hRangeTotallyBounded.isBounded


/-!
============================================================
Exercise 9.9.5
============================================================
-/

theorem exercise_9_9_5
    (E : Set ℝ)
    (f : E → ℝ)
    (hE : Bornology.IsBounded E)
    (hf : UniformContinuous f) :
    Bornology.IsBounded (Set.range f) := by

  exact proposition_9_9_15
    E
    f
    hE
    hf

end TaoExercise9_9_5
