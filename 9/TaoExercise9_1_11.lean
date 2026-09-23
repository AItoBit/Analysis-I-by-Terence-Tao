import Mathlib

namespace TaoExercise9_1_11

open Set

/-!
============================================================
Bounded subset of ℝ
============================================================
-/

def IsBoundedSet (X : Set ℝ) : Prop :=
  ∃ M : ℝ,
    0 < M ∧
    ∀ x : ℝ, x ∈ X →
      -M ≤ x ∧ x ≤ M


/-!
============================================================
Closed symmetric interval
============================================================
-/

theorem closed_Icc_symm
    (M : ℝ) :
    IsClosed (Set.Icc (-M) M) := by

  exact isClosed_Icc


/-!
============================================================
If X ⊆ [-M,M], then closure X ⊆ [-M,M]
============================================================
-/

theorem closure_subset_Icc
    (X : Set ℝ)
    (M : ℝ)
    (hXM :
      X ⊆ Set.Icc (-M) M) :
    closure X ⊆ Set.Icc (-M) M := by

  exact closure_minimal
    hXM
    (closed_Icc_symm M)


/-!
============================================================
Exercise 9.1.11
============================================================
-/

theorem exercise_9_1_11
    (X : Set ℝ)
    (hX : IsBoundedSet X) :
    IsBoundedSet (closure X) := by

  rcases hX with ⟨M, hMpos, hM⟩

  have hSubset :
      X ⊆ Set.Icc (-M) M := by

    intro x hx

    exact hM x hx

  have hClosureSubset :
      closure X ⊆ Set.Icc (-M) M := by

    exact closure_subset_Icc
      X
      M
      hSubset

  refine ⟨M, hMpos, ?_⟩

  intro x hx

  exact hClosureSubset hx


end TaoExercise9_1_11
