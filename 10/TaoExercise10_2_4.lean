import Mathlib

namespace TaoExercise10_2_4

open Set

/-!
============================================================
Theorem 10.2.7 — Rolle's theorem
============================================================
-/

theorem theorem_10_2_7
    (g : ℝ → ℝ)
    (a b : ℝ)
    (hab : a < b)
    (hg_cont : ContinuousOn g (Set.Icc a b))
    (hg_diff : DifferentiableOn ℝ g (Set.Ioo a b))
    (hend : g a = g b) :
    ∃ x ∈ Set.Ioo a b,
      deriv g x = 0 := by

  exact exists_deriv_eq_zero
    hab
    hg_cont
    hend


/-!
============================================================
Version with an explicit derivative function g'
============================================================
-/

theorem theorem_10_2_7_hasDerivAt
    (g g' : ℝ → ℝ)
    (a b : ℝ)
    (hab : a < b)
    (hg_cont : ContinuousOn g (Set.Icc a b))
    (hend : g a = g b)
    (hg_diff :
      ∀ x : ℝ,
        x ∈ Set.Ioo a b →
        HasDerivAt g (g' x) x) :
    ∃ x ∈ Set.Ioo a b,
      g' x = 0 := by

  exact exists_hasDerivAt_eq_zero
    hab
    hg_cont
    hend
    hg_diff


/-!
============================================================
Exercise 10.2.4
============================================================
-/

theorem exercise_10_2_4
    (g : ℝ → ℝ)
    (a b : ℝ)
    (hab : a < b)
    (hg_cont : ContinuousOn g (Set.Icc a b))
    (hg_diff : DifferentiableOn ℝ g (Set.Ioo a b))
    (hend : g a = g b) :
    ∃ x ∈ Set.Ioo a b,
      deriv g x = 0 := by

  exact theorem_10_2_7
    g
    a
    b
    hab
    hg_cont
    hg_diff
    hend

end TaoExercise10_2_4
