import Mathlib

namespace TaoExercise11_6_1

open Set
open MeasureTheory
open intervalIntegral

/-!
============================================================
Corollary 11.6.3

A monotone real-valued function on a bounded interval
is interval integrable.
============================================================
-/

theorem corollary_11_6_3_monotone
    {a b : ℝ}
    (f : ℝ → ℝ)
    (hf : MonotoneOn f (uIcc a b)) :
    IntervalIntegrable f volume a b := by

  exact hf.intervalIntegrable


/-!
The decreasing case.
-/

theorem corollary_11_6_3_antitone
    {a b : ℝ}
    (f : ℝ → ℝ)
    (hf : AntitoneOn f (uIcc a b)) :
    IntervalIntegrable f volume a b := by

  exact hf.intervalIntegrable


/-!
============================================================
Closed interval version
============================================================
-/

theorem corollary_11_6_3_Icc
    {a b : ℝ}
    (hab : a ≤ b)
    (f : ℝ → ℝ)
    (hf : MonotoneOn f (Icc a b)) :
    IntervalIntegrable f volume a b := by

  have hu :
      MonotoneOn f (uIcc a b) := by
    simpa [uIcc_of_le hab] using hf

  exact hu.intervalIntegrable


/-!
============================================================
Auxiliary epsilon lemma

If

    lower ≤ upper

and

    upper - lower ≤ C * ε

for every ε > 0, with C ≥ 0, then upper = lower.
============================================================
-/

lemma eq_of_gap_le_all_pos
    {lower upper C : ℝ}
    (hlu : lower ≤ upper)
    (hC : 0 ≤ C)
    (hgap :
      ∀ ε : ℝ,
        0 < ε →
        upper - lower ≤ C * ε) :
    upper = lower := by

  by_contra hne

  have hlt :
      lower < upper := by

    exact lt_of_le_of_ne
      hlu
      (Ne.symm hne)

  have hdiff :
      0 < upper - lower := by

    exact sub_pos.mpr hlt

  have hC1 :
      0 < C + 1 := by

    linarith

  have hden :
      0 < 2 * (C + 1) := by

    positivity

  let ε : ℝ :=
    (upper - lower) /
      (2 * (C + 1))

  have heps :
      0 < ε := by

    dsimp [ε]

    exact div_pos
      hdiff
      hden

  have hbound :
      upper - lower ≤ C * ε := by

    exact hgap
      ε
      heps

  have hstrict :
      C * ε < upper - lower := by

    dsimp [ε]

    have hden_ne :
        2 * (C + 1) ≠ 0 := by

      exact ne_of_gt hden

    field_simp [hden_ne]

    nlinarith

  exact (not_lt_of_ge hbound) hstrict


/-!
============================================================
Tao's final gap estimate

If

  upper - lower ≤ (2 + 4M) ε

for every ε > 0, then upper = lower.
============================================================
-/

theorem riemann_integrable_of_tao_gap
    {lower upper M : ℝ}
    (hlu : lower ≤ upper)
    (hM : 0 ≤ M)
    (hgap :
      ∀ ε : ℝ,
        0 < ε →
        upper - lower ≤
          (2 + 4 * M) * ε) :
    upper = lower := by

  have hC :
      0 ≤ 2 + 4 * M := by

    nlinarith

  exact eq_of_gap_le_all_pos
    hlu
    hC
    hgap


/-!
============================================================
A version with the upper and lower Riemann integrals
abstracted explicitly.
============================================================
-/

def RiemannIntegrableTao
    (upperIntegral lowerIntegral :
      (ℝ → ℝ) → ℝ)
    (f : ℝ → ℝ) : Prop :=
  upperIntegral f = lowerIntegral f


theorem riemannIntegrable_of_gap
    (upperIntegral lowerIntegral :
      (ℝ → ℝ) → ℝ)
    (f : ℝ → ℝ)
    (M : ℝ)
    (hLowerUpper :
      lowerIntegral f ≤
        upperIntegral f)
    (hM :
      0 ≤ M)
    (hgap :
      ∀ ε : ℝ,
        0 < ε →
        upperIntegral f -
            lowerIntegral f
          ≤
        (2 + 4 * M) * ε) :
    RiemannIntegrableTao
      upperIntegral
      lowerIntegral
      f := by

  unfold RiemannIntegrableTao

  exact riemann_integrable_of_tao_gap
    hLowerUpper
    hM
    hgap


/-!
============================================================
Exercise 11.6.1

Mathlib already provides the main analytic result:
a monotone function on uIcc a b is interval integrable.
============================================================
-/

theorem exercise_11_6_1
    {a b : ℝ}
    (f : ℝ → ℝ)
    (hf : MonotoneOn f (uIcc a b)) :
    IntervalIntegrable f volume a b := by

  exact hf.intervalIntegrable


/-!
============================================================
Strict-order version a < b
============================================================
-/

theorem exercise_11_6_1_of_lt
    {a b : ℝ}
    (hab : a < b)
    (f : ℝ → ℝ)
    (hf : MonotoneOn f (Icc a b)) :
    IntervalIntegrable f volume a b := by

  have habLe :
      a ≤ b := by

    exact le_of_lt hab

  exact corollary_11_6_3_Icc
    habLe
    f
    hf

end TaoExercise11_6_1
