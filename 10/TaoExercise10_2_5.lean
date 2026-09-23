import Mathlib

namespace TaoExercise10_2_5

open Set

/-!
============================================================
Corollary 10.2.9 — Mean Value Theorem

If f is continuous on [a,b] and differentiable on (a,b),
then there exists x₀ ∈ (a,b) such that

    f'(x₀) = (f(b) - f(a)) / (b - a).
============================================================
-/

theorem corollary_10_2_9
    (f : ℝ → ℝ)
    (a b : ℝ)
    (hab : a < b)
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hf_diff : DifferentiableOn ℝ f (Set.Ioo a b)) :
    ∃ x₀ ∈ Set.Ioo a b,
      deriv f x₀ =
        (f b - f a) / (b - a) := by

  exact exists_deriv_eq_slope
    f
    hab
    hf_cont
    hf_diff


/-!
============================================================
Version with an explicit derivative function f'
============================================================
-/

theorem corollary_10_2_9_hasDerivAt
    (f f' : ℝ → ℝ)
    (a b : ℝ)
    (hab : a < b)
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hf_deriv :
      ∀ x ∈ Set.Ioo a b,
        HasDerivAt f (f' x) x) :
    ∃ x₀ ∈ Set.Ioo a b,
      f' x₀ =
        (f b - f a) / (b - a) := by

  exact exists_hasDerivAt_eq_slope
    f
    f'
    hab
    hf_cont
    hf_deriv


/-!
============================================================
Exercise 10.2.5
============================================================
-/

theorem exercise_10_2_5
    (f : ℝ → ℝ)
    (a b : ℝ)
    (hab : a < b)
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hf_diff : DifferentiableOn ℝ f (Set.Ioo a b)) :
    ∃ x₀ ∈ Set.Ioo a b,
      deriv f x₀ =
        (f b - f a) / (b - a) := by

  exact corollary_10_2_9
    f
    a
    b
    hab
    hf_cont
    hf_diff

end TaoExercise10_2_5
