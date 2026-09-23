import Mathlib

namespace TaoExercise10_3_3

def F (x : ℝ) : ℝ :=
  x ^ 3


/-!
============================================================
F(x) = x^3 is strictly increasing
============================================================
-/

theorem F_strictMono :
    StrictMono F := by

  intro x y hxy

  unfold F

  have hdiffPos :
      0 < y - x := by
    linarith

  have hdiffNe :
      x - y ≠ 0 := by
    linarith

  have hsqDiff :
      0 < (x - y) ^ 2 := by
    exact sq_pos_of_ne_zero hdiffNe

  have hsqSum :
      0 ≤ (x + y) ^ 2 := by
    exact sq_nonneg (x + y)

  have hquad :
      0 < x ^ 2 + x * y + y ^ 2 := by
    nlinarith

  have hprod :
      0 <
        (y - x) *
          (x ^ 2 + x * y + y ^ 2) := by
    exact mul_pos hdiffPos hquad

  have hfactor :
      y ^ 3 - x ^ 3 =
        (y - x) *
          (x ^ 2 + x * y + y ^ 2) := by
    ring

  rw [← hfactor] at hprod

  linarith


/-!
============================================================
Derivative of x^3
============================================================
-/

theorem F_hasDerivAt
    (x : ℝ) :
    HasDerivAt F (3 * x ^ 2) x := by

  unfold F

  change
    HasDerivAt
      (id ^ (3 : ℕ))
      (3 * x ^ 2)
      x

  simpa using (hasDerivAt_id x).pow 3


/-!
============================================================
F is differentiable everywhere
============================================================
-/

theorem F_differentiable :
    Differentiable ℝ F := by

  intro x

  exact (F_hasDerivAt x).differentiableAt


/-!
============================================================
F'(0) = 0
============================================================
-/

theorem F_deriv_zero :
    deriv F 0 = 0 := by

  have h :
      deriv F 0 = 3 * (0 : ℝ) ^ 2 := by
    exact (F_hasDerivAt 0).deriv

  simpa using h


/-!
============================================================
Exercise 10.3.3

There exists a differentiable, strictly increasing function
whose derivative at zero is zero.

The canonical example is F(x) = x^3.
============================================================
-/

theorem exercise_10_3_3 :
    StrictMono F
      ∧
    Differentiable ℝ F
      ∧
    deriv F 0 = 0 := by

  exact
    ⟨F_strictMono,
     F_differentiable,
     F_deriv_zero⟩

end TaoExercise10_3_3
