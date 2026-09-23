import Mathlib

namespace TaoExercise10_2_1

/-!
============================================================
Proposition 10.2.6

If f has a local extremum at x₀ and is differentiable
at x₀, then f'(x₀) = 0.
============================================================
-/

/-!
Local maximum case.
-/

theorem localMax_derivative_eq_zero
    (f : ℝ → ℝ)
    (x₀ L : ℝ)
    (hmax : IsLocalMax f x₀)
    (hf : HasDerivAt f L x₀) :
    L = 0 := by

  exact hmax.hasDerivAt_eq_zero hf


/-!
Local minimum case.
-/

theorem localMin_derivative_eq_zero
    (f : ℝ → ℝ)
    (x₀ L : ℝ)
    (hmin : IsLocalMin f x₀)
    (hf : HasDerivAt f L x₀) :
    L = 0 := by

  exact hmin.hasDerivAt_eq_zero hf


/-!
Local extremum case.
-/

theorem localExtremum_derivative_eq_zero
    (f : ℝ → ℝ)
    (x₀ L : ℝ)
    (hext : IsLocalExtr f x₀)
    (hf : HasDerivAt f L x₀) :
    L = 0 := by

  exact hext.hasDerivAt_eq_zero hf


/-!
============================================================
Version written using deriv.
============================================================
-/

theorem localMax_deriv_eq_zero
    (f : ℝ → ℝ)
    (x₀ : ℝ)
    (hmax : IsLocalMax f x₀) :
    deriv f x₀ = 0 := by

  exact hmax.deriv_eq_zero


theorem localMin_deriv_eq_zero
    (f : ℝ → ℝ)
    (x₀ : ℝ)
    (hmin : IsLocalMin f x₀) :
    deriv f x₀ = 0 := by

  exact hmin.deriv_eq_zero


/-!
============================================================
Proposition 10.2.6
============================================================
-/

theorem proposition_10_2_6
    (f : ℝ → ℝ)
    (x₀ L : ℝ)
    (hext : IsLocalMax f x₀ ∨ IsLocalMin f x₀)
    (hf : HasDerivAt f L x₀) :
    L = 0 := by

  rcases hext with hmax | hmin

  · exact hmax.hasDerivAt_eq_zero hf

  · exact hmin.hasDerivAt_eq_zero hf


/-!
============================================================
Exercise 10.2.1
============================================================
-/

theorem exercise_10_2_1
    (f : ℝ → ℝ)
    (x₀ L : ℝ)
    (hext : IsLocalMax f x₀ ∨ IsLocalMin f x₀)
    (hf : HasDerivAt f L x₀) :
    L = 0 := by

  exact proposition_10_2_6
    f
    x₀
    L
    hext
    hf

end TaoExercise10_2_1
