import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

namespace TaoExercise11_10_1

open Set
open MeasureTheory
open intervalIntegral

/-!
============================================================
Proposition 11.10.1
Integration by parts
============================================================
-/

theorem proposition_11_10_1
    {a b : ℝ}
    {F G F' G' : ℝ → ℝ}
    (hF :
      ∀ x ∈ uIcc a b,
        HasDerivAt F (F' x) x)
    (hG :
      ∀ x ∈ uIcc a b,
        HasDerivAt G (G' x) x)
    (hFint :
      IntervalIntegrable F' volume a b)
    (hGint :
      IntervalIntegrable G' volume a b) :
    (∫ x in a..b, F x * G' x)
      =
    F b * G b
      - F a * G a
      - ∫ x in a..b, F' x * G x := by

  exact
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
      hF
      hG
      hFint
      hGint


/-!
============================================================
Expanded product-rule form

This corresponds to the intermediate identity in Tao:

  ∫ (F'G + FG')
    =
  F(b)G(b) - F(a)G(a)
============================================================
-/

theorem integral_product_derivative
    {a b : ℝ}
    {F G F' G' : ℝ → ℝ}
    (hF :
      ∀ x ∈ uIcc a b,
        HasDerivAt F (F' x) x)
    (hG :
      ∀ x ∈ uIcc a b,
        HasDerivAt G (G' x) x)
    (hFint :
      IntervalIntegrable F' volume a b)
    (hGint :
      IntervalIntegrable G' volume a b) :
    (∫ x in a..b,
        F' x * G x + F x * G' x)
      =
    F b * G b - F a * G a := by

  exact
    intervalIntegral.integral_deriv_mul_eq_sub
      hF
      hG
      hFint
      hGint


/-!
============================================================
Product derivative itself
============================================================
-/

lemma hasDerivAt_product
    {F G F' G' : ℝ → ℝ}
    {x : ℝ}
    (hF :
      HasDerivAt F (F' x) x)
    (hG :
      HasDerivAt G (G' x) x) :
    HasDerivAt
      (fun y => F y * G y)
      (F' x * G x + F x * G' x)
      x := by

  exact hF.mul hG


/-!
============================================================
Exercise 11.10.1
============================================================
-/

theorem exercise_11_10_1
    {a b : ℝ}
    {F G F' G' : ℝ → ℝ}
    (hF :
      ∀ x ∈ uIcc a b,
        HasDerivAt F (F' x) x)
    (hG :
      ∀ x ∈ uIcc a b,
        HasDerivAt G (G' x) x)
    (hFint :
      IntervalIntegrable F' volume a b)
    (hGint :
      IntervalIntegrable G' volume a b) :
    (∫ x in a..b, F x * G' x)
      =
    F b * G b
      - F a * G a
      - ∫ x in a..b, F' x * G x := by

  exact proposition_11_10_1
    hF
    hG
    hFint
    hGint

end TaoExercise11_10_1
