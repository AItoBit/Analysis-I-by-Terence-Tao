import Mathlib

namespace TaoExercise10_2_2

open Set

/-!
============================================================
The function on (-1,1)

    f(x) = 1 - |x|

which is equivalent to

    x + 1     if x ≤ 0
   -x + 1     if x > 0.
============================================================
-/

def f :
    Set.Ioo (-1 : ℝ) 1 → ℝ :=
  fun x => 1 - abs (x : ℝ)


def zeroPoint :
    Set.Ioo (-1 : ℝ) 1 :=
  ⟨0, by
    constructor <;> norm_num⟩


/-!
============================================================
Continuity
============================================================
-/

theorem f_continuous :
    Continuous f := by
  unfold f
  fun_prop


/-!
============================================================
Global maximum at zero
============================================================
-/

theorem f_zero :
    f zeroPoint = 1 := by
  norm_num [f, zeroPoint]


theorem f_le_one
    (x : Set.Ioo (-1 : ℝ) 1) :
    f x ≤ 1 := by

  unfold f

  have h :
      0 ≤ abs (x : ℝ) := abs_nonneg _

  linarith


theorem f_global_maximum_at_zero :
    ∀ x : Set.Ioo (-1 : ℝ) 1,
      f x ≤ f zeroPoint := by

  intro x

  rw [f_zero]

  exact f_le_one x


/-!
============================================================
Ambient function

We use the same formula on all of ℝ in order to discuss
the derivative at zero.
============================================================
-/

def F (x : ℝ) : ℝ :=
  1 - abs x


/-!
============================================================
Tao-style derivative definition
============================================================
-/

def HasDerivativeAtTao
    (f : ℝ → ℝ)
    (x₀ L : ℝ) : Prop :=
  ∀ ε : ℝ,
    0 < ε →
    ∃ δ : ℝ,
      0 < δ ∧
      ∀ x : ℝ,
        x ≠ x₀ →
        abs (x - x₀) ≤ δ →
        abs
            ((f x - f x₀) / (x - x₀) - L) ≤ ε


def DifferentiableAtTao
    (f : ℝ → ℝ)
    (x₀ : ℝ) : Prop :=
  ∃ L : ℝ,
    HasDerivativeAtTao f x₀ L


/-!
============================================================
Difference quotient on the right

For x > 0,

       (F(x)-F(0))/x = -1.
============================================================
-/

lemma right_difference_quotient
    {x : ℝ}
    (hx : 0 < x) :
    (F x - F 0) / (x - 0) = -1 := by

  simp [F, abs_of_pos hx, ne_of_gt hx]


/-!
============================================================
Difference quotient on the left

For x < 0,

       (F(x)-F(0))/x = 1.
============================================================
-/

lemma left_difference_quotient
    {x : ℝ}
    (hx : x < 0) :
    (F x - F 0) / (x - 0) = 1 := by

  simp [F, abs_of_neg hx, ne_of_lt hx]


/-!
============================================================
F is not differentiable at zero
============================================================
-/

theorem F_not_differentiable_at_zero :
    ¬ DifferentiableAtTao F 0 := by

  intro hdiff

  obtain ⟨L, hL⟩ := hdiff

  obtain ⟨δ, hδ, hmain⟩ :=
    hL (1 / 2 : ℝ) (by norm_num)

  /-
  Positive test point δ/2.
  -/

  let xp : ℝ := δ / 2

  have hxpPos :
      0 < xp := by
    dsimp [xp]
    linarith

  have hxpNe :
      xp ≠ 0 := by
    exact ne_of_gt hxpPos

  have hxpBound :
      abs (xp - 0) ≤ δ := by

    have hxpAbs :
        abs xp = xp := by
      exact abs_of_pos hxpPos

    rw [sub_zero, hxpAbs]

    dsimp [xp]

    linarith

  have hp :=
    hmain xp hxpNe hxpBound

  have hqp :
      (F xp - F 0) / (xp - 0) = -1 := by
    exact right_difference_quotient hxpPos

  rw [hqp] at hp

  /-
  Negative test point -δ/2.
  -/

  let xm : ℝ := -(δ / 2)

  have hxmNeg :
      xm < 0 := by
    dsimp [xm]
    linarith

  have hxmNe :
      xm ≠ 0 := by
    exact ne_of_lt hxmNeg

  have hxmBound :
      abs (xm - 0) ≤ δ := by

    rw [sub_zero]

    have hxmAbs :
        abs xm = -xm := by
      exact abs_of_neg hxmNeg

    rw [hxmAbs]

    dsimp [xm]

    linarith

  have hm :=
    hmain xm hxmNe hxmBound

  have hqm :
      (F xm - F 0) / (xm - 0) = 1 := by
    exact left_difference_quotient hxmNeg

  rw [hqm] at hm

  /-
  We now have

      |-1 - L| ≤ 1/2
      | 1 - L| ≤ 1/2,

  which is impossible.
  -/

  have hpBounds :
      -(1 / 2 : ℝ) ≤ (-1 : ℝ) - L ∧
        (-1 : ℝ) - L ≤ (1 / 2 : ℝ) := by

    exact abs_le.mp hp

  have hmBounds :
      -(1 / 2 : ℝ) ≤ (1 : ℝ) - L ∧
        (1 : ℝ) - L ≤ (1 / 2 : ℝ) := by

    exact abs_le.mp hm

  rcases hpBounds with ⟨hpLow, hpHigh⟩
  rcases hmBounds with ⟨hmLow, hmHigh⟩

  linarith


/-!
============================================================
Exercise 10.2.2
============================================================
-/

theorem exercise_10_2_2 :
    Continuous f
      ∧
    (∀ x : Set.Ioo (-1 : ℝ) 1,
      f x ≤ f zeroPoint)
      ∧
    ¬ DifferentiableAtTao F 0 := by

  refine ⟨f_continuous, f_global_maximum_at_zero, ?_⟩

  exact F_not_differentiable_at_zero

end TaoExercise10_2_2
