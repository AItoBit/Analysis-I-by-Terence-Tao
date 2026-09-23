import Mathlib.Analysis.SumIntegralComparisons

namespace TaoExercise11_6_3

open Set
open MeasureTheory
open intervalIntegral

/-!
============================================================
Finite comparison inequalities

For a decreasing function f on [0,∞):

  ∫₀ᴺ f ≤ Σ_{n < N} f(n)

and

  Σ_{n < N} f(n+1) ≤ ∫₀ᴺ f.
============================================================
-/

theorem integral_le_partial_sum
    (f : ℝ → ℝ)
    (N : ℕ)
    (hanti : AntitoneOn f (Ici 0)) :
    (∫ x in (0 : ℝ)..(N : ℝ), f x)
      ≤
    (Finset.range N).sum
      (fun n => f (n : ℝ)) := by

  have hmono :
      AntitoneOn f
        (Icc (0 : ℝ) ((0 : ℝ) + (N : ℝ))) := by

    intro x hx y hy hxy

    apply hanti

    · exact hx.1

    · exact hy.1

    · exact hxy

  simpa using
    (AntitoneOn.integral_le_sum
      (x₀ := (0 : ℝ))
      (a := N)
      hmono)


theorem shifted_partial_sum_le_integral
    (f : ℝ → ℝ)
    (N : ℕ)
    (hanti : AntitoneOn f (Ici 0)) :
    (Finset.range N).sum
        (fun n =>
          f ((n + 1 : ℕ) : ℝ))
      ≤
    (∫ x in (0 : ℝ)..(N : ℝ), f x) := by

  have hmono :
      AntitoneOn f
        (Icc (0 : ℝ) ((0 : ℝ) + (N : ℝ))) := by

    intro x hx y hy hxy

    apply hanti

    · exact hx.1

    · exact hy.1

    · exact hxy

  simpa using
    (AntitoneOn.sum_le_integral
      (x₀ := (0 : ℝ))
      (a := N)
      hmono)


/-!
============================================================
Series convergent -> improper integral finite
============================================================
-/

theorem integrable_of_summable
    (f : ℝ → ℝ)
    (hanti : AntitoneOn f (Ici 0))
    (hnonneg :
      ∀ x ∈ Ici (0 : ℝ),
        0 ≤ f x)
    (hsum :
      Summable
        (fun n : ℕ =>
          f (n : ℝ))) :
    IntegrableOn
      f
      (Ioi (0 : ℝ))
      volume := by

  exact
    hanti.integrableOn_Ioi_zero_of_summable
      hsum
      (by
        intro x hx

        apply hnonneg x

        show (0 : ℝ) ≤ x

        exact le_of_lt hx)


/-!
============================================================
Improper integral finite -> series convergent
============================================================
-/

theorem summable_of_integrable
    (f : ℝ → ℝ)
    (hanti : AntitoneOn f (Ici 0))
    (hnonneg :
      ∀ x ∈ Ici (0 : ℝ),
        0 ≤ f x)
    (hint :
      IntegrableOn
        f
        (Ioi (0 : ℝ))
        volume) :
    Summable
      (fun n : ℕ =>
        f (n : ℝ)) := by

  exact
    hanti.summable_of_integrableOn_Ioi_zero
      hint
      (by
        intro x hx

        apply hnonneg x

        show (0 : ℝ) ≤ x

        exact le_of_lt hx)


/-!
============================================================
Proposition 11.6.4

For a nonnegative decreasing function on [0,∞),
the series Σ f(n) converges iff the improper integral
over (0,∞) is finite.
============================================================
-/

theorem proposition_11_6_4
    (f : ℝ → ℝ)
    (hanti :
      AntitoneOn f (Ici 0))
    (hnonneg :
      ∀ x ∈ Ici (0 : ℝ),
        0 ≤ f x) :
    Summable
        (fun n : ℕ =>
          f (n : ℝ))
      ↔
    IntegrableOn
      f
      (Ioi (0 : ℝ))
      volume := by

  constructor

  · intro hsum

    exact integrable_of_summable
      f
      hanti
      hnonneg
      hsum

  · intro hint

    exact summable_of_integrable
      f
      hanti
      hnonneg
      hint


/-!
============================================================
Positive version, matching Tao's statement
============================================================
-/

theorem exercise_11_6_3
    (f : ℝ → ℝ)
    (hanti :
      AntitoneOn f (Ici 0))
    (hpositive :
      ∀ x ∈ Ici (0 : ℝ),
        0 < f x) :
    Summable
        (fun n : ℕ =>
          f (n : ℝ))
      ↔
    IntegrableOn
      f
      (Ioi (0 : ℝ))
      volume := by

  apply proposition_11_6_4
    f
    hanti

  intro x hx

  exact le_of_lt
    (hpositive x hx)

end TaoExercise11_6_3
