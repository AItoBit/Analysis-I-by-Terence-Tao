import Mathlib

namespace TaoExercise11_5_1

open Set
open intervalIntegral

theorem exercise_11_5_1
    {a b : ℝ}
    (hab : a < b)
    (f : ℝ → ℝ)
    (hcont : ContinuousOn f (Icc a b))
    (hnonneg :
      ∀ x ∈ Icc a b,
        0 ≤ f x)
    (hint :
      (∫ x in a..b, f x) = 0) :
    ∀ x ∈ Icc a b,
      f x = 0 := by

  intro x hx

  have hfx_nonneg :
      0 ≤ f x := by
    exact hnonneg x hx

  apply le_antisymm

  · by_contra hnot

    have hfx_pos :
        0 < f x := by
      exact lt_of_not_ge hnot

    have hpositive :
        0 < ∫ y in a..b, f y := by

      exact intervalIntegral.integral_pos
        hab
        hcont
        (by
          intro y hy
          exact hnonneg y ⟨le_of_lt hy.1, hy.2⟩)
        ⟨x, hx, hfx_pos⟩

    rw [hint] at hpositive

    exact (lt_irrefl 0) hpositive

  · exact hfx_nonneg

end TaoExercise11_5_1
