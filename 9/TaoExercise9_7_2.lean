import Mathlib

namespace TaoExercise9_7_2

open Set

/-!
============================================================
Exercise 9.7.2

Every continuous function

    f : [0,1] → [0,1]

has a fixed point.
============================================================
-/

theorem exercise_9_7_2
    (f : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1)
    (hf : Continuous f) :
    ∃ x : Set.Icc (0 : ℝ) 1,
      f x = x := by

  let a : Set.Icc (0 : ℝ) 1 :=
    ⟨0, by
      constructor <;> norm_num⟩

  let b : Set.Icc (0 : ℝ) 1 :=
    ⟨1, by
      constructor <;> norm_num⟩

  have hab :
      a ≤ b := by
    change (0 : ℝ) ≤ 1
    norm_num

  have ha :
      a ≤ f a := by
    change (0 : ℝ) ≤ (f a : ℝ)
    exact (f a).property.1

  have hb :
      f b ≤ b := by
    change (f b : ℝ) ≤ (1 : ℝ)
    exact (f b).property.2

  have hfOn :
      ContinuousOn f (Set.Icc a b) := by
    exact hf.continuousOn

  obtain ⟨x, hx, hfix⟩ :=
    exists_mem_Icc_isFixedPt
      hfOn
      hab
      ha
      hb

  exact ⟨x, hfix⟩

end TaoExercise9_7_2
