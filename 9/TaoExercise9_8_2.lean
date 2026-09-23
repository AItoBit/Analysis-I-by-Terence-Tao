import Mathlib

namespace TaoExercise9_8_2

open Set

/-!
============================================================
Counterexample

Define f : [0,2] → ℝ by

    f(x) = x       if x < 1
    f(x) = x + 1   if x ≥ 1.

This function is strictly increasing, hence monotone,
but it skips every value in [1,2). In particular,
it never takes the value 3/2.
============================================================
-/

noncomputable def jumpFunction :
    Set.Icc (0 : ℝ) 2 → ℝ :=
  fun x =>
    if (x : ℝ) < 1
    then (x : ℝ)
    else (x : ℝ) + 1


/-!
============================================================
Endpoint values
============================================================
-/

theorem jumpFunction_zero :
    jumpFunction ⟨0, by constructor <;> norm_num⟩ = 0 := by
  norm_num [jumpFunction]


theorem jumpFunction_two :
    jumpFunction ⟨2, by constructor <;> norm_num⟩ = 3 := by
  norm_num [jumpFunction]


/-!
============================================================
The function is strictly increasing
============================================================
-/

theorem jumpFunction_strictMono :
    StrictMono jumpFunction := by

  intro x y hxy

  have hxyReal :
      (x : ℝ) < (y : ℝ) := by
    exact hxy

  by_cases hx :
      (x : ℝ) < 1

  · by_cases hy :
        (y : ℝ) < 1

    · have hfx :
          jumpFunction x = (x : ℝ) := by
        simp [jumpFunction, hx]

      have hfy :
          jumpFunction y = (y : ℝ) := by
        simp [jumpFunction, hy]

      rw [hfx, hfy]

      exact hxyReal

    · have hfx :
          jumpFunction x = (x : ℝ) := by
        simp [jumpFunction, hx]

      have hfy :
          jumpFunction y = (y : ℝ) + 1 := by
        simp [jumpFunction, hy]

      rw [hfx, hfy]

      linarith

  · by_cases hy :
        (y : ℝ) < 1

    · have hxlt :
          (x : ℝ) < 1 := by
        exact lt_trans hxyReal hy

      exact (hx hxlt).elim

    · have hfx :
          jumpFunction x = (x : ℝ) + 1 := by
        simp [jumpFunction, hx]

      have hfy :
          jumpFunction y = (y : ℝ) + 1 := by
        simp [jumpFunction, hy]

      rw [hfx, hfy]

      linarith


/-!
============================================================
Hence it is also monotone
============================================================
-/

theorem jumpFunction_monotone :
    Monotone jumpFunction := by
  exact jumpFunction_strictMono.monotone


/-!
============================================================
The value 3/2 is never attained
============================================================
-/

theorem jumpFunction_ne_three_halves
    (x : Set.Icc (0 : ℝ) 2) :
    jumpFunction x ≠ (3 / 2 : ℝ) := by

  by_cases hx :
      (x : ℝ) < 1

  · have hfx :
        jumpFunction x = (x : ℝ) := by
      simp [jumpFunction, hx]

    intro h

    rw [hfx] at h

    linarith

  · have hxge :
        1 ≤ (x : ℝ) := by
      exact le_of_not_gt hx

    have hfx :
        jumpFunction x = (x : ℝ) + 1 := by
      simp [jumpFunction, hx]

    intro h

    rw [hfx] at h

    linarith


theorem three_halves_not_in_range :
    ¬ ∃ x : Set.Icc (0 : ℝ) 2,
        jumpFunction x = (3 / 2 : ℝ) := by

  rintro ⟨x, hx⟩

  exact jumpFunction_ne_three_halves x hx


/-!
============================================================
3/2 lies between f(0) and f(2)
============================================================
-/

theorem three_halves_between_endpoint_values :
    jumpFunction ⟨0, by constructor <;> norm_num⟩
      <
    (3 / 2 : ℝ)
      ∧
    (3 / 2 : ℝ)
      <
    jumpFunction ⟨2, by constructor <;> norm_num⟩ := by

  rw [jumpFunction_zero, jumpFunction_two]

  constructor <;> norm_num


/-!
============================================================
Exercise 9.8.2

The intermediate value conclusion fails even though
the function is strictly monotone.
============================================================
-/

theorem exercise_9_8_2 :
    StrictMono jumpFunction
      ∧
    Monotone jumpFunction
      ∧
    jumpFunction ⟨0, by constructor <;> norm_num⟩ = 0
      ∧
    jumpFunction ⟨2, by constructor <;> norm_num⟩ = 3
      ∧
    ¬ ∃ x : Set.Icc (0 : ℝ) 2,
        jumpFunction x = (3 / 2 : ℝ) := by

  refine ⟨jumpFunction_strictMono,
    jumpFunction_monotone,
    jumpFunction_zero,
    jumpFunction_two,
    ?_⟩

  exact three_halves_not_in_range

end TaoExercise9_8_2
