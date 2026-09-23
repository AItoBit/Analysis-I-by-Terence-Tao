import Mathlib

namespace TaoExercise8_2_4

open Function
open scoped BigOperators

/-!
============================================================
Positive and negative parts
============================================================
-/

noncomputable def positivePart (a : ℕ → ℝ) : ℕ → ℝ :=
  fun n =>
    if 0 ≤ a n then
      a n
    else
      0


noncomputable def negativePart (a : ℕ → ℝ) : ℕ → ℝ :=
  fun n =>
    if a n < 0 then
      a n
    else
      0


/-!
============================================================
Pointwise decomposition
============================================================
-/

theorem positive_add_negative
    (a : ℕ → ℝ)
    (n : ℕ) :
    positivePart a n + negativePart a n = a n := by

  by_cases h : 0 ≤ a n

  · have hnotneg :
        ¬ a n < 0 := by
      exact not_lt.mpr h

    simp [positivePart, negativePart, h, hnotneg]

  · have hneg :
        a n < 0 := by
      exact lt_of_not_ge h

    simp [positivePart, negativePart, h, hneg]


theorem sub_positive_eq_negative
    (a : ℕ → ℝ)
    (n : ℕ) :
    a n - positivePart a n =
      negativePart a n := by

  have h :=
    positive_add_negative a n

  linarith


theorem sub_negative_eq_positive
    (a : ℕ → ℝ)
    (n : ℕ) :
    a n - negativePart a n =
      positivePart a n := by

  have h :=
    positive_add_negative a n

  linarith


/-!
============================================================
Absolute value decomposition
============================================================
-/

theorem abs_eq_positive_sub_negative
    (a : ℕ → ℝ)
    (n : ℕ) :
    |a n| =
      positivePart a n - negativePart a n := by

  by_cases h : 0 ≤ a n

  · have hnotneg :
        ¬ a n < 0 := by
      exact not_lt.mpr h

    simp [positivePart, negativePart, h, hnotneg, abs_of_nonneg h]

  · have hneg :
        a n < 0 := by
      exact lt_of_not_ge h

    simp [positivePart, negativePart, h, hneg, abs_of_neg hneg]


/-!
============================================================
Conditional convergence
============================================================
-/

def ConditionallyConvergent
    (a : ℕ → ℝ) : Prop :=
  Summable a ∧
    ¬ Summable (fun n : ℕ => |a n|)


/-!
============================================================
If positive part is summable, negative part is summable
============================================================
-/

theorem negativePart_summable_of_positivePart_summable
    (a : ℕ → ℝ)
    (ha : Summable a)
    (hpos : Summable (positivePart a)) :
    Summable (negativePart a) := by

  have h :
      Summable
        (fun n : ℕ =>
          a n - positivePart a n) := by
    exact ha.sub hpos

  have hEq :
      (fun n : ℕ =>
        a n - positivePart a n)
        =
      negativePart a := by

    funext n

    exact sub_positive_eq_negative a n

  rw [hEq] at h

  exact h


/-!
============================================================
If negative part is summable, positive part is summable
============================================================
-/

theorem positivePart_summable_of_negativePart_summable
    (a : ℕ → ℝ)
    (ha : Summable a)
    (hneg : Summable (negativePart a)) :
    Summable (positivePart a) := by

  have h :
      Summable
        (fun n : ℕ =>
          a n - negativePart a n) := by
    exact ha.sub hneg

  have hEq :
      (fun n : ℕ =>
        a n - negativePart a n)
        =
      positivePart a := by

    funext n

    exact sub_negative_eq_positive a n

  rw [hEq] at h

  exact h


/-!
============================================================
If both parts are summable, then |aₙ| is summable
============================================================
-/

theorem abs_summable_of_parts_summable
    (a : ℕ → ℝ)
    (hpos : Summable (positivePart a))
    (hneg : Summable (negativePart a)) :
    Summable (fun n : ℕ => |a n|) := by

  have h :
      Summable
        (fun n : ℕ =>
          positivePart a n -
            negativePart a n) := by
    exact hpos.sub hneg

  have hEq :
      (fun n : ℕ =>
        positivePart a n -
          negativePart a n)
        =
      (fun n : ℕ => |a n|) := by

    funext n

    exact
      (abs_eq_positive_sub_negative a n).symm

  rw [hEq] at h

  exact h


/-!
============================================================
Positive part cannot be summable
============================================================
-/

theorem positivePart_not_summable
    (a : ℕ → ℝ)
    (ha : ConditionallyConvergent a) :
    ¬ Summable (positivePart a) := by

  intro hpos

  have hneg :
      Summable (negativePart a) := by

    exact
      negativePart_summable_of_positivePart_summable
        a
        ha.1
        hpos

  have habs :
      Summable (fun n : ℕ => |a n|) := by

    exact
      abs_summable_of_parts_summable
        a
        hpos
        hneg

  exact ha.2 habs


/-!
============================================================
Negative part cannot be summable
============================================================
-/

theorem negativePart_not_summable
    (a : ℕ → ℝ)
    (ha : ConditionallyConvergent a) :
    ¬ Summable (negativePart a) := by

  intro hneg

  have hpos :
      Summable (positivePart a) := by

    exact
      positivePart_summable_of_negativePart_summable
        a
        ha.1
        hneg

  have habs :
      Summable (fun n : ℕ => |a n|) := by

    exact
      abs_summable_of_parts_summable
        a
        hpos
        hneg

  exact ha.2 habs


/-!
============================================================
Lemma 8.2.7
============================================================
-/

theorem lemma_8_2_7
    (a : ℕ → ℝ)
    (ha : ConditionallyConvergent a) :
    ¬ Summable (positivePart a)
      ∧
    ¬ Summable (negativePart a) := by

  constructor

  · exact positivePart_not_summable
      a
      ha

  · exact negativePart_not_summable
      a
      ha


/-!
============================================================
Exercise 8.2.4
============================================================
-/

theorem exercise_8_2_4
    (a : ℕ → ℝ)
    (haSummable : Summable a)
    (haNotAbsolutelySummable :
      ¬ Summable (fun n : ℕ => |a n|)) :
    ¬ Summable (positivePart a)
      ∧
    ¬ Summable (negativePart a) := by

  exact lemma_8_2_7
    a
    ⟨haSummable, haNotAbsolutelySummable⟩

end TaoExercise8_2_4
