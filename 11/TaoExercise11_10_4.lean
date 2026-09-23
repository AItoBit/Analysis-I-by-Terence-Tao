import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

namespace TaoExercise11_10_4

open Set
open MeasureTheory
open intervalIntegral

/-!
============================================================
Exercise 11.10.4

Decreasing change of variables.

If φ is differentiable and decreasing on [a,b], then

  ∫_a^b (f ∘ φ)(x) * φ'(x) dx
    =
  - ∫_{φ(b)}^{φ(a)} f(u) du.
============================================================
-/

theorem exercise_11_10_4
    {a b : ℝ}
    {φ φ' f : ℝ → ℝ}
    (hab : a < b)
    (hφcont :
      ContinuousOn φ (Icc a b))
    (hφderiv :
      ∀ x ∈ Ioo a b,
        HasDerivAt φ (φ' x) x)
    (hφnonpos :
      ∀ x ∈ Ioo a b,
        φ' x ≤ 0)
    (hf :
      IntervalIntegrable
        f
        volume
        (φ b)
        (φ a)) :
    IntervalIntegrable
        (fun x =>
          (f ∘ φ) x * φ' x)
        volume
        a
        b
      ∧
    (∫ x in a..b,
        (f ∘ φ) x * φ' x)
      =
    - ∫ u in (φ b)..(φ a), f u := by

  have hmin :
      min a b = a := by
    exact min_eq_left (le_of_lt hab)

  have hmax :
      max a b = b := by
    exact max_eq_right (le_of_lt hab)

  have hderiv :
      ∀ x ∈ Ioo (min a b) (max a b),
        HasDerivAt φ (φ' x) x := by

    intro x hx

    rw [hmin, hmax] at hx

    exact hφderiv x hx

  have hnonpos :
      ∀ x ∈ Ioo (min a b) (max a b),
        φ' x ≤ 0 := by

    intro x hx

    rw [hmin, hmax] at hx

    exact hφnonpos x hx

  have hcont :
      ContinuousOn φ (uIcc a b) := by

    simpa [uIcc_of_le (le_of_lt hab)] using hφcont

  have hint :
      IntervalIntegrable
        (fun x =>
          (f ∘ φ) x * φ' x)
        volume
        a
        b := by

    have hiff :=
      intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonpos
        (f := φ)
        (f' := φ')
        (g := f)
        hcont
        hderiv
        hnonpos

    have hf' :
        IntervalIntegrable
          f
          volume
          (φ a)
          (φ b) := by

      exact hf.symm

    exact hiff.mpr hf'

  constructor

  · exact hint

  · have hchange :
        (∫ x in a..b,
            (f ∘ φ) x * φ' x)
          =
        ∫ u in (φ a)..(φ b), f u := by

      exact
        intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
          (f := φ)
          (f' := φ')
          (g := f)
          hcont
          hderiv
          hnonpos

    rw [hchange]

    exact intervalIntegral.integral_symm
      (φ a)
      (φ b)
      f

end TaoExercise11_10_4
