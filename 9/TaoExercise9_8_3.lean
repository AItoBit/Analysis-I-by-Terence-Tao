import Mathlib

namespace TaoExercise9_8_3

open Set

theorem exercise_9_8_3
    (a b : ℝ)
    (hab : a < b)
    (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc a b))
    (hinj : Set.InjOn f (Set.Icc a b)) :
    StrictMonoOn f (Set.Icc a b) ∨
      StrictAntiOn f (Set.Icc a b) := by

  exact
    ContinuousOn.strictMonoOn_of_injOn_Icc'
      (le_of_lt hab)
      hf
      hinj

end TaoExercise9_8_3
