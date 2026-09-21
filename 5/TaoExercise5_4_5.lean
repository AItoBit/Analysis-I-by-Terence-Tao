import Mathlib

namespace TaoExercise5_4_5

/--
Exercise 5.4.5 / Proposition 5.4.14.

Given real numbers `x < y`, there exists a rational number `q`
such that

    x < q < y.
-/
theorem exercise_5_4_5
    (x y : ℝ)
    (hxy : x < y) :
    ∃ q : ℚ,
      x < (q : ℝ) ∧
      (q : ℝ) < y := by

  exact exists_rat_btwn hxy

end TaoExercise5_4_5
