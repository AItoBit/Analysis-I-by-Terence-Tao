import Mathlib

namespace TaoExercise2_3_4

/--
Exercise 2.3.4

For all natural numbers a and b,

    (a + b)^2 = a^2 + 2ab + b^2.
-/
theorem square_of_sum (a b : ℕ) :
    (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  calc
    (a + b) ^ 2
        = (a + b) * (a + b) := by
            rw [pow_two]

    _ = (a + b) * a + (a + b) * b := by
          rw [Nat.mul_add]

    _ = (a * a + b * a) + (a * b + b * b) := by
          rw [Nat.add_mul, Nat.add_mul]

    _ = a * a + 2 * a * b + b * b := by
          ring

    _ = a ^ 2 + 2 * a * b + b ^ 2 := by
          rw [pow_two, pow_two]

end TaoExercise2_3_4
