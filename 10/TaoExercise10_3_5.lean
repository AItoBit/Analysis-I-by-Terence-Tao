import Mathlib

namespace TaoExercise10_3_5

open Set

/-!
============================================================
The disconnected domain
============================================================
-/

def X : Set ℝ :=
  Set.Icc (-2 : ℝ) (-(3 / 2 : ℝ)) ∪
    Set.Icc (3 / 2 : ℝ) 2


/-!
============================================================
The function

    F(x) = x^3 - 3x
============================================================
-/

def F (x : ℝ) : ℝ :=
  x ^ 3 - 3 * x


/-!
============================================================
Derivative
============================================================
-/

theorem F_hasDerivAt
    (x : ℝ) :
    HasDerivAt F (3 * x ^ 2 - 3) x := by

  have hpow :
      HasDerivAt
        (fun y : ℝ => y ^ 3)
        (3 * x ^ 2)
        x := by

    change
      HasDerivAt
        (id ^ (3 : ℕ))
        (3 * x ^ 2)
        x

    simpa using (hasDerivAt_id x).pow 3

  have hlin :
      HasDerivAt
        (fun y : ℝ => 3 * y)
        3
        x := by

    simpa using (hasDerivAt_id x).const_mul 3

  unfold F

  exact hpow.sub hlin


theorem F_differentiable :
    Differentiable ℝ F := by

  intro x

  exact (F_hasDerivAt x).differentiableAt


theorem F_differentiableOn_X :
    DifferentiableOn ℝ F X := by

  intro x hx

  exact
    (F_hasDerivAt x).differentiableAt.differentiableWithinAt


theorem F_deriv
    (x : ℝ) :
    deriv F x = 3 * x ^ 2 - 3 := by

  exact (F_hasDerivAt x).deriv


/-!
============================================================
The derivative is strictly positive on X
============================================================
-/

theorem F_deriv_pos_on_X :
    ∀ x ∈ X,
      0 < deriv F x := by

  intro x hx

  rw [F_deriv]

  rcases hx with hxLeft | hxRight

  /-
  Left component:

      -2 ≤ x ≤ -3/2

  hence x < -1.
  -/

  · have hx1 :
        x + 1 < 0 := by
      linarith [hxLeft.2]

    have hx2 :
        x - 1 < 0 := by
      linarith [hxLeft.2]

    have hprod :
        0 < (x + 1) * (x - 1) := by
      exact mul_pos_of_neg_of_neg hx1 hx2

    nlinarith

  /-
  Right component:

      3/2 ≤ x ≤ 2

  hence x > 1.
  -/

  · have hx1 :
        0 < x - 1 := by
      linarith [hxRight.1]

    have hx2 :
        0 < x + 1 := by
      linarith [hxRight.1]

    have hprod :
        0 < (x - 1) * (x + 1) := by
      exact mul_pos hx1 hx2

    nlinarith


/-!
============================================================
Two points of X violating strict monotonicity
============================================================
-/

theorem left_point_mem :
    (-(3 / 2 : ℝ)) ∈ X := by

  left

  constructor

  · norm_num

  · exact le_rfl


theorem right_point_mem :
    (3 / 2 : ℝ) ∈ X := by

  right

  constructor

  · exact le_rfl

  · norm_num


theorem endpoint_order :
    (-(3 / 2 : ℝ)) < (3 / 2 : ℝ) := by
  norm_num


theorem F_left_value :
    F (-(3 / 2 : ℝ)) = 9 / 8 := by
  norm_num [F]


theorem F_right_value :
    F (3 / 2 : ℝ) = -(9 / 8 : ℝ) := by
  norm_num [F]


/-!
============================================================
F is NOT strictly increasing on X
============================================================
-/

theorem F_not_strictMonoOn :
    ¬ StrictMonoOn F X := by

  intro hmono

  have hbad :
      F (-(3 / 2 : ℝ)) <
        F (3 / 2 : ℝ) := by

    exact hmono
      left_point_mem
      right_point_mem
      endpoint_order

  rw [F_left_value, F_right_value] at hbad

  norm_num at hbad


/-!
============================================================
Exercise 10.3.5
============================================================
-/

theorem exercise_10_3_5 :
    DifferentiableOn ℝ F X
      ∧
    (∀ x ∈ X,
      0 < deriv F x)
      ∧
    ¬ StrictMonoOn F X := by

  exact
    ⟨F_differentiableOn_X,
     F_deriv_pos_on_X,
     F_not_strictMonoOn⟩

end TaoExercise10_3_5
