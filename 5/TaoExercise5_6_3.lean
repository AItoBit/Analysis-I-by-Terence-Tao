import Mathlib

namespace TaoExercise5_6_3

/--
Exercise 5.6.3, following Tao's proof by cases.
-/
theorem exercise_5_6_3
    (x : ℝ) :
    |x| = Real.sqrt (x ^ 2) := by

  by_cases hx0 : x = 0

  /-
  Case 1: x = 0.
  -/
  · subst x
    norm_num

  /-
  x ≠ 0, so either x > 0 or x < 0.
  -/
  · rcases lt_or_gt_of_ne hx0 with hxneg | hxpos

    /-
    Case 2: x < 0.

    Then |x| = -x, and sqrt(x²) = |x|.
    -/
    · have habs :
          |x| = -x := by
        exact abs_of_neg hxneg

      rw [habs]

      have hsqrt :
          Real.sqrt (x ^ 2) = |x| := by
        exact Real.sqrt_sq_eq_abs x

      rw [hsqrt, abs_of_neg hxneg]

    /-
    Case 3: x > 0.

    Then |x| = x, and sqrt(x²) = |x|.
    -/
    · have habs :
          |x| = x := by
        exact abs_of_pos hxpos

      rw [habs]

      have hsqrt :
          Real.sqrt (x ^ 2) = |x| := by
        exact Real.sqrt_sq_eq_abs x

      rw [hsqrt, abs_of_pos hxpos]

end TaoExercise5_6_3
