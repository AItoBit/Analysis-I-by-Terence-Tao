import Mathlib

namespace TaoExercise9_1_7

open Set

/-!
============================================================
Union of two closed sets
============================================================
-/

theorem union_two_closed
    (X Y : Set ℝ)
    (hX : IsClosed X)
    (hY : IsClosed Y) :
    IsClosed (X ∪ Y) := by

  exact hX.union hY


/-!
============================================================
Finite union of closed sets
============================================================

`Fin n` represents the indices

    0, 1, ..., n - 1.

Thus `A : Fin n → Set ℝ` is a family of n subsets
of the real line.
-/

theorem finite_union_closed
    {n : ℕ}
    (A : Fin n → Set ℝ)
    (hA : ∀ i : Fin n, IsClosed (A i)) :
    IsClosed (⋃ i : Fin n, A i) := by

  exact isClosed_iUnion_of_finite hA


/-!
============================================================
The case n = 2
============================================================
-/

theorem two_sets_closed
    (X₁ X₂ : Set ℝ)
    (hX₁ : IsClosed X₁)
    (hX₂ : IsClosed X₂) :
    IsClosed (X₁ ∪ X₂) := by

  exact hX₁.union hX₂


/-!
============================================================
Closure formulation corresponding to Tao's proof
============================================================
-/

theorem closure_union_of_closed
    (X Y : Set ℝ)
    (hX : IsClosed X)
    (hY : IsClosed Y) :
    closure (X ∪ Y) = X ∪ Y := by

  have hClosed :
      IsClosed (X ∪ Y) := by
    exact hX.union hY

  exact hClosed.closure_eq


/-!
============================================================
Exercise 9.1.7
============================================================
-/

theorem exercise_9_1_7
    {n : ℕ}
    (A : Fin n → Set ℝ)
    (hA : ∀ i : Fin n, IsClosed (A i)) :
    IsClosed (⋃ i : Fin n, A i) := by

  exact isClosed_iUnion_of_finite hA

end TaoExercise9_1_7
