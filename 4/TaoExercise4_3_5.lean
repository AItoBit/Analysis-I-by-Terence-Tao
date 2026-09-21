import Mathlib

namespace TaoExercise4_3_5

/--
Exercise 4.3.5.

For every positive natural number `N`,

    2^N ≥ N.
-/
theorem exercise_4_3_5
    (N : ℕ)
    (hN : 0 < N) :
    N ≤ 2 ^ N := by

  induction N using Nat.case_strong_induction_on with

  /-
  Base case N = 0 cannot occur because hN says N > 0.
  -/
  | hz =>
      omega

  /-
  Inductive step.
  -/
  | hi N ih =>

      by_cases hNzero : N = 0

      /-
      Then the current value is N+1 = 1.
      -/
      · subst hNzero
        norm_num

      /-
      Now N > 0.
      -/
      · have hNpos : 0 < N := by
          exact Nat.pos_of_ne_zero hNzero

        have hIH :
            N ≤ 2 ^ N := by
          exact ih N (by omega) hNpos

        calc
          N + 1
              ≤ N + N := by
                  omega

          _ ≤ 2 ^ N + 2 ^ N := by
                omega

          _ = 2 ^ N * 2 := by
                ring

          _ = 2 ^ (N + 1) := by
                rw [pow_succ]

end TaoExercise4_3_5
