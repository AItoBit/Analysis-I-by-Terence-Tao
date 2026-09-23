import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace TaoExercise11_10_3

open Set
open MeasureTheory
open intervalIntegral

/-!
============================================================
Exercise 11.10.3

If f is integrable on [a,b] and

  g(x) = f(-x),

then g is integrable on [-b,-a] and

  ∫_{-b}^{-a} g = ∫_a^b f.
============================================================
-/

def reflected
    (f : ℝ → ℝ) :
    ℝ → ℝ :=
  fun x => f (-x)


/-!
============================================================
Integrability under reflection
============================================================
-/

theorem reflected_intervalIntegrable
    {a b : ℝ}
    (f : ℝ → ℝ)
    (hf :
      IntervalIntegrable
        f
        volume
        a
        b) :
    IntervalIntegrable
      (reflected f)
      volume
      (-b)
      (-a) := by

  have hneg :
      IntervalIntegrable
        (fun x : ℝ => f (-x))
        volume
        (-a)
        (-b) := by

    exact
      (IntervalIntegrable.iff_comp_neg).mp hf

  exact hneg.symm


/-!
============================================================
Integral under reflection
============================================================
-/

theorem reflected_integral
    {a b : ℝ}
    (f : ℝ → ℝ) :
    (∫ x in (-b)..(-a), reflected f x)
      =
    ∫ x in a..b, f x := by

  unfold reflected

  have h :
      (∫ x in (-b)..(-a), f (-x))
        =
      ∫ x in -(-a)..-(-b), f x := by

    exact intervalIntegral.integral_comp_neg f

  simpa using h


/-!
============================================================
Main proposition
============================================================
-/

theorem exercise_11_10_3
    {a b : ℝ}
    (hab : a < b)
    (f : ℝ → ℝ)
    (hf :
      IntervalIntegrable
        f
        volume
        a
        b) :
    IntervalIntegrable
        (reflected f)
        volume
        (-b)
        (-a)
      ∧
    (∫ x in (-b)..(-a), reflected f x)
        =
      ∫ x in a..b, f x := by

  constructor

  · exact reflected_intervalIntegrable
      f
      hf

  · exact reflected_integral f


/-!
============================================================
Version written directly with f(-x)
============================================================
-/

theorem exercise_11_10_3_direct
    {a b : ℝ}
    (hab : a < b)
    (f : ℝ → ℝ)
    (hf :
      IntervalIntegrable
        f
        volume
        a
        b) :
    IntervalIntegrable
        (fun x : ℝ => f (-x))
        volume
        (-b)
        (-a)
      ∧
    (∫ x in (-b)..(-a), f (-x))
        =
      ∫ x in a..b, f x := by

  constructor

  · have hneg :
        IntervalIntegrable
          (fun x : ℝ => f (-x))
          volume
          (-a)
          (-b) := by

      exact
        (IntervalIntegrable.iff_comp_neg).mp hf

    exact hneg.symm

  · have h :
        (∫ x in (-b)..(-a), f (-x))
          =
        ∫ x in -(-a)..-(-b), f x := by

      exact intervalIntegral.integral_comp_neg f

    simpa using h

end TaoExercise11_10_3
