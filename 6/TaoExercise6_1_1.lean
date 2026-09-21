import Mathlib

namespace TaoExercise6_1_1

/--
Exercise 6.1.1.

If a real sequence satisfies

    a (n + 1) > a n

for every natural number `n`, then whenever `m > n`,

    a m > a n.
-/
theorem exercise_6_1_1
    (a : ℕ → ℝ)
    (hstep : ∀ n : ℕ, a n < a (n + 1))
    {n m : ℕ}
    (hnm : n < m) :
    a n < a m := by

  induction m with

  /-
  m = 0 is impossible because n < 0.
  -/
  | zero =>
      omega

  /-
  Suppose the theorem is known for m.
  Prove it for m + 1.
  -/
  | succ m ih =>

      by_cases hnmEq : n = m

      /-
      If n = m, this is exactly the hypothesis

          a m < a (m + 1).
      -/
      · subst n

        simpa [Nat.succ_eq_add_one] using hstep m

      /-
      Otherwise, from n < m + 1 and n ≠ m we get n < m.
      -/
      · have hnm' :
            n < m := by
          omega

        have hih :
            a n < a m := by
          exact ih hnm'

        have hmnext :
            a m < a (m + 1) := by
          exact hstep m

        have htrans :
            a n < a (m + 1) := by
          exact lt_trans hih hmnext

        simpa [Nat.succ_eq_add_one] using htrans

end TaoExercise6_1_1
