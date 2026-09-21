import Mathlib

namespace TaoExercise2_2_4

/--
Exercise 2.2.4 (a)

For every natural number b, we have 0 ≤ b.
-/
theorem part_a_zero_le (b : ℕ) :
    0 ≤ b := by
  exact Nat.zero_le b


/--
Exercise 2.2.4 (b)

If a > b, then succ a > b.
-/
theorem part_b_succ_gt_of_gt (a b : ℕ)
    (h : a > b) :
    Nat.succ a > b := by
  omega


/--
Exercise 2.2.4 (c)

If a = b, then succ a > b.
-/
theorem part_c_succ_gt_of_eq (a b : ℕ)
    (h : a = b) :
    Nat.succ a > b := by
  subst b
  exact Nat.lt_succ_self a

end TaoExercise2_2_4
