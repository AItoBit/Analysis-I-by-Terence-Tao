import Mathlib

namespace TaoExercise10_1_6

open Set

/-!
============================================================
Exercise 10.1.6

For an integer n < 0, the function

    f(x) = x^n

is differentiable on ℝ \ {0}, and

    f'(x) = n * x^(n - 1).
============================================================
-/

theorem hasDerivAt_zpow_of_ne_zero
    (n : ℤ)
    (x : ℝ)
    (hx : x ≠ 0) :
    HasDerivAt
      (fun y : ℝ => y ^ n)
      ((n : ℝ) * x ^ (n - 1))
      x := by

  exact hasDerivAt_zpow n x (Or.inl hx)


/-!
The function x ↦ x^n is differentiable at every
nonzero real number.
-/

theorem differentiableAt_zpow_of_ne_zero
    (n : ℤ)
    (x : ℝ)
    (hx : x ≠ 0) :
    DifferentiableAt ℝ
      (fun y : ℝ => y ^ n)
      x := by

  exact
    (hasDerivAt_zpow_of_ne_zero n x hx).differentiableAt


/-!
Differentiability on ℝ \ {0}.
-/

theorem differentiableOn_zpow_nonzero
    (n : ℤ) :
    DifferentiableOn ℝ
      (fun x : ℝ => x ^ n)
      ({0}ᶜ : Set ℝ) := by

  intro x hx

  have hx0 : x ≠ 0 := by
    simpa using hx

  exact
    (differentiableAt_zpow_of_ne_zero n x hx0).differentiableWithinAt


/-!
Derivative formula at every nonzero point.
-/

theorem deriv_zpow_of_ne_zero
    (n : ℤ)
    (x : ℝ)
    (hx : x ≠ 0) :
    deriv (fun y : ℝ => y ^ n) x =
      (n : ℝ) * x ^ (n - 1) := by

  exact
    (hasDerivAt_zpow_of_ne_zero n x hx).deriv


/-!
============================================================
Proposition in the form of Tao's exercise.

The hypothesis n < 0 records that we are specifically
in the negative-integer case.
============================================================
-/

theorem exercise_10_1_6
    (n : ℤ)
    (hn : n < 0) :
    DifferentiableOn ℝ
        (fun x : ℝ => x ^ n)
        ({0}ᶜ : Set ℝ)
      ∧
    ∀ x : ℝ,
      x ∈ ({0}ᶜ : Set ℝ) →
      deriv (fun y : ℝ => y ^ n) x =
        (n : ℝ) * x ^ (n - 1) := by

  have hn_nonpos : n ≤ 0 := le_of_lt hn

  constructor

  · exact differentiableOn_zpow_nonzero n

  · intro x hx

    have hx0 : x ≠ 0 := by
      simpa using hx

    exact deriv_zpow_of_ne_zero n x hx0

end TaoExercise10_1_6
