import Mathlib

namespace TaoExercise10_1_5

theorem hasDerivAt_pow_nat
    (n : ℕ)
    (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => y ^ n)
      ((n : ℝ) * x ^ (n - 1))
      x := by

  change
    HasDerivAt
      (id ^ n)
      ((n : ℝ) * x ^ (n - 1))
      x

  simpa using (hasDerivAt_id x).pow n


theorem differentiableAt_pow_nat
    (n : ℕ)
    (x : ℝ) :
    DifferentiableAt ℝ
      (fun y : ℝ => y ^ n)
      x := by

  exact (hasDerivAt_pow_nat n x).differentiableAt


theorem differentiable_pow_nat
    (n : ℕ) :
    Differentiable ℝ
      (fun x : ℝ => x ^ n) := by

  intro x

  exact differentiableAt_pow_nat n x


theorem deriv_pow_nat
    (n : ℕ)
    (x : ℝ) :
    deriv (fun y : ℝ => y ^ n) x =
      (n : ℝ) * x ^ (n - 1) := by

  exact (hasDerivAt_pow_nat n x).deriv


theorem exercise_10_1_5
    (n : ℕ) :
    Differentiable ℝ
      (fun x : ℝ => x ^ n)
      ∧
    ∀ x : ℝ,
      deriv (fun y : ℝ => y ^ n) x =
        (n : ℝ) * x ^ (n - 1) := by

  constructor

  · exact differentiable_pow_nat n

  · intro x

    exact deriv_pow_nat n x

end TaoExercise10_1_5
