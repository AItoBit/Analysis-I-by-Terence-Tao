import Mathlib

namespace TaoExercise9_1_6

open Set

/-!
============================================================
Exercise 9.1.6

1. The closure of X is closed.
2. If Y is closed and X ⊆ Y, then closure X ⊆ Y.
============================================================
-/

theorem closure_is_closed
    (X : Set ℝ) :
    IsClosed (closure X) := by
  exact isClosed_closure


theorem closure_subset_closed_superset
    (X Y : Set ℝ)
    (hXY : X ⊆ Y)
    (hYclosed : IsClosed Y) :
    closure X ⊆ Y := by

  exact closure_minimal hXY hYclosed


/-!
============================================================
The closure is the smallest closed set containing X
============================================================
-/

theorem closure_is_smallest_closed
    (X : Set ℝ) :
    IsClosed (closure X)
      ∧
    X ⊆ closure X
      ∧
    ∀ Y : Set ℝ,
      X ⊆ Y →
      IsClosed Y →
      closure X ⊆ Y := by

  constructor

  · exact isClosed_closure

  constructor

  · exact subset_closure

  · intro Y hXY hYclosed

    exact closure_minimal hXY hYclosed


/-!
============================================================
Idempotence of closure

This corresponds to

    closure (closure X) = closure X.
============================================================
-/

theorem closure_closure_eq
    (X : Set ℝ) :
    closure (closure X) = closure X := by

  exact isClosed_closure.closure_eq


/-!
============================================================
Version following Tao's argument more explicitly
============================================================
-/

theorem exercise_9_1_6
    (X : Set ℝ) :
    IsClosed (closure X)
      ∧
    (∀ Y : Set ℝ,
      IsClosed Y →
      X ⊆ Y →
      closure X ⊆ Y) := by

  constructor

  · exact isClosed_closure

  · intro Y hYclosed hXY

    exact closure_minimal hXY hYclosed

end TaoExercise9_1_6
