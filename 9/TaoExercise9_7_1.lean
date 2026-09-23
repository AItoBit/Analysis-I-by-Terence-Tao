import Mathlib

namespace TaoExercise9_7_1

open Set

/-!
============================================================
Corollary 9.7.4

If f is continuous on [a,b], then its image is exactly

    [m, M]

where m is the minimum value and M is the maximum value.

Mathlib expresses these endpoints as

    sInf (f '' Icc a b)
    sSup (f '' Icc a b).
============================================================
-/

theorem corollary_9_7_4
    (f : ℝ → ℝ)
    (a b : ℝ)
    (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    f '' Set.Icc a b =
      Set.Icc
        (sInf (f '' Set.Icc a b))
        (sSup (f '' Set.Icc a b)) := by

  exact hf.image_Icc hab


/-!
============================================================
Named minimum and maximum
============================================================
-/

noncomputable def minimumValue
    (f : ℝ → ℝ)
    (a b : ℝ) : ℝ :=
  sInf (f '' Set.Icc a b)


noncomputable def maximumValue
    (f : ℝ → ℝ)
    (a b : ℝ) : ℝ :=
  sSup (f '' Set.Icc a b)


theorem image_eq_Icc_minimum_maximum
    (f : ℝ → ℝ)
    (a b : ℝ)
    (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    f '' Set.Icc a b =
      Set.Icc
        (minimumValue f a b)
        (maximumValue f a b) := by

  unfold minimumValue maximumValue

  exact hf.image_Icc hab


/-!
============================================================
Every value between the minimum and maximum is attained
============================================================
-/

theorem intermediate_value_between_extrema
    (f : ℝ → ℝ)
    (a b y : ℝ)
    (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b))
    (hy :
      y ∈ Set.Icc
        (minimumValue f a b)
        (maximumValue f a b)) :
    ∃ c : ℝ,
      c ∈ Set.Icc a b ∧
      f c = y := by

  have hImage :
      f '' Set.Icc a b =
        Set.Icc
          (minimumValue f a b)
          (maximumValue f a b) := by
    exact image_eq_Icc_minimum_maximum
      f a b hab hf

  have hyImage :
      y ∈ f '' Set.Icc a b := by
    rw [hImage]
    exact hy

  rcases hyImage with ⟨c, hc, hfc⟩

  refine ⟨c, hc, ?_⟩

  exact hfc


/-!
============================================================
Every function value lies between m and M
============================================================
-/

theorem value_between_extrema
    (f : ℝ → ℝ)
    (a b x : ℝ)
    (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b))
    (hx : x ∈ Set.Icc a b) :
    f x ∈ Set.Icc
      (minimumValue f a b)
      (maximumValue f a b) := by

  have hImage :
      f '' Set.Icc a b =
        Set.Icc
          (minimumValue f a b)
          (maximumValue f a b) := by
    exact image_eq_Icc_minimum_maximum
      f a b hab hf

  rw [← hImage]

  exact ⟨x, hx, rfl⟩


/-!
============================================================
Exercise 9.7.1
============================================================
-/

theorem exercise_9_7_1
    (f : ℝ → ℝ)
    (a b : ℝ)
    (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    f '' Set.Icc a b =
      Set.Icc
        (minimumValue f a b)
        (maximumValue f a b) := by

  exact image_eq_Icc_minimum_maximum
    f a b hab hf

end TaoExercise9_7_1
