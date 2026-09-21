import Mathlib

namespace TaoExercise5_4_4

/--
Exercise 5.4.4.

For every positive real number `x`, there exists a positive natural
number `N` such that

    x > 1 / N > 0.
-/
theorem exercise_5_4_4
    (x : ℝ)
    (hx : 0 < x) :
    ∃ N : ℕ,
      0 < N ∧
      (1 : ℝ) / N < x ∧
      0 < (1 : ℝ) / N := by

  /-
  By the Archimedean property, choose N such that

      1/x < N.
  -/
  obtain ⟨N, hN⟩ :=
    exists_nat_gt (1 / x)

  /-
  Since 1/x > 0 and 1/x < N, we have N > 0.
  -/
  have hinvx :
      (0 : ℝ) < 1 / x := by
    positivity

  have hNposR :
      (0 : ℝ) < N := by
    linarith

  have hNpos :
      0 < N := by
    exact_mod_cast hNposR

  /-
  From

      1/x < N

  and x > 0, obtain

      1 < N*x.
  -/
  have hNx :
      (1 : ℝ) < (N : ℝ) * x := by
    exact (div_lt_iff₀ hx).mp hN

  /-
  Hence

      1/N < x.
  -/
  have hInvLt :
      (1 : ℝ) / N < x := by
    apply (div_lt_iff₀ hNposR).2
    nlinarith [hNx]

  /-
  Also 1/N > 0 because N > 0.
  -/
  have hInvPos :
      (0 : ℝ) < (1 : ℝ) / N := by
    positivity

  exact ⟨N, hNpos, hInvLt, hInvPos⟩

end TaoExercise5_4_4
