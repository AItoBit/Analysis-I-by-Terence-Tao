import Mathlib

namespace TaoExercise10_1_2

def HasDerivativeAtTao
    (X : Set ℝ)
    (f : X → ℝ)
    (x₀ : X)
    (L : ℝ) : Prop :=
  ∀ ε : ℝ,
    0 < ε →
    ∃ δ : ℝ,
      0 < δ ∧
      ∀ x : X,
        x ≠ x₀ →
        abs ((x : ℝ) - (x₀ : ℝ)) ≤ δ →
        abs
            ((f x - f x₀) /
                ((x : ℝ) - (x₀ : ℝ)) -
              L) ≤ ε


def HasLinearApproximation
    (X : Set ℝ)
    (f : X → ℝ)
    (x₀ : X)
    (L : ℝ) : Prop :=
  ∀ ε : ℝ,
    0 < ε →
    ∃ δ : ℝ,
      0 < δ ∧
      ∀ x : X,
        abs ((x : ℝ) - (x₀ : ℝ)) ≤ δ →
        abs
            (f x -
              (f x₀ +
                L * ((x : ℝ) - (x₀ : ℝ)))) ≤
          ε * abs ((x : ℝ) - (x₀ : ℝ))


lemma linear_error_factorization
    (A L h : ℝ)
    (hh : h ≠ 0) :
    A - L * h =
      h * (A / h - L) := by
  field_simp [hh]


lemma quotient_error_factorization
    (A L h : ℝ)
    (hh : h ≠ 0) :
    A / h - L =
      (A - L * h) / h := by
  field_simp [hh]


theorem derivative_implies_linear_approximation
    (X : Set ℝ)
    (f : X → ℝ)
    (x₀ : X)
    (L : ℝ)
    (hf : HasDerivativeAtTao X f x₀ L) :
    HasLinearApproximation X f x₀ L := by

  intro ε hε

  obtain ⟨δ, hδ, hmain⟩ :=
    hf ε hε

  refine ⟨δ, hδ, ?_⟩

  intro x hxδ

  by_cases hxx₀ : x = x₀

  · subst x
    norm_num

  · have hsubne :
        (x : ℝ) - (x₀ : ℝ) ≠ 0 := by
      intro hzero
      have hEq :
          (x : ℝ) = (x₀ : ℝ) := by
        linarith
      apply hxx₀
      exact Subtype.ext hEq

    have hquot :
        abs
            ((f x - f x₀) /
                ((x : ℝ) - (x₀ : ℝ)) -
              L) ≤ ε := by
      exact hmain x hxx₀ hxδ

    have hfactor :
        f x - f x₀ -
            L * ((x : ℝ) - (x₀ : ℝ))
          =
        ((x : ℝ) - (x₀ : ℝ)) *
          ((f x - f x₀) /
              ((x : ℝ) - (x₀ : ℝ)) -
            L) := by
      exact linear_error_factorization
        (f x - f x₀)
        L
        ((x : ℝ) - (x₀ : ℝ))
        hsubne

    have habs :
        abs
            (f x - f x₀ -
              L * ((x : ℝ) - (x₀ : ℝ)))
          =
        abs ((x : ℝ) - (x₀ : ℝ)) *
          abs
            ((f x - f x₀) /
                ((x : ℝ) - (x₀ : ℝ)) -
              L) := by
      rw [hfactor, abs_mul]

    have hnonneg :
        0 ≤ abs ((x : ℝ) - (x₀ : ℝ)) := by
      exact abs_nonneg _

    have hmul :
        abs ((x : ℝ) - (x₀ : ℝ)) *
            abs
              ((f x - f x₀) /
                  ((x : ℝ) - (x₀ : ℝ)) -
                L)
          ≤
        abs ((x : ℝ) - (x₀ : ℝ)) * ε := by
      exact mul_le_mul_of_nonneg_left
        hquot
        hnonneg

    change
      abs
          (f x -
            (f x₀ +
              L * ((x : ℝ) - (x₀ : ℝ)))) ≤
        ε * abs ((x : ℝ) - (x₀ : ℝ))

    have hrewrite :
        f x -
            (f x₀ +
              L * ((x : ℝ) - (x₀ : ℝ)))
          =
        f x - f x₀ -
          L * ((x : ℝ) - (x₀ : ℝ)) := by
      ring

    rw [hrewrite, habs]

    nlinarith


theorem linear_approximation_implies_derivative
    (X : Set ℝ)
    (f : X → ℝ)
    (x₀ : X)
    (L : ℝ)
    (hf : HasLinearApproximation X f x₀ L) :
    HasDerivativeAtTao X f x₀ L := by

  intro ε hε

  obtain ⟨δ, hδ, hmain⟩ :=
    hf ε hε

  refine ⟨δ, hδ, ?_⟩

  intro x hxx₀ hxδ

  have hsubne :
      (x : ℝ) - (x₀ : ℝ) ≠ 0 := by
    intro hzero
    have hEq :
        (x : ℝ) = (x₀ : ℝ) := by
      linarith
    apply hxx₀
    exact Subtype.ext hEq

  have habspos :
      0 < abs ((x : ℝ) - (x₀ : ℝ)) := by
    exact abs_pos.mpr hsubne

  have hlinear :
      abs
          (f x -
            (f x₀ +
              L * ((x : ℝ) - (x₀ : ℝ)))) ≤
        ε * abs ((x : ℝ) - (x₀ : ℝ)) := by
    exact hmain x hxδ

  have hlinear' :
      abs
          (f x - f x₀ -
            L * ((x : ℝ) - (x₀ : ℝ))) ≤
        ε * abs ((x : ℝ) - (x₀ : ℝ)) := by

    have hrewrite :
        f x -
            (f x₀ +
              L * ((x : ℝ) - (x₀ : ℝ)))
          =
        f x - f x₀ -
          L * ((x : ℝ) - (x₀ : ℝ)) := by
      ring

    rw [← hrewrite]

    exact hlinear

  have hfactor :
      (f x - f x₀) /
            ((x : ℝ) - (x₀ : ℝ)) -
          L
        =
      (f x - f x₀ -
          L * ((x : ℝ) - (x₀ : ℝ))) /
        ((x : ℝ) - (x₀ : ℝ)) := by
    exact quotient_error_factorization
      (f x - f x₀)
      L
      ((x : ℝ) - (x₀ : ℝ))
      hsubne

  rw [hfactor, abs_div]

  apply (div_le_iff₀ habspos).2

  nlinarith


theorem proposition_10_1_7
    (X : Set ℝ)
    (f : X → ℝ)
    (x₀ : X)
    (L : ℝ) :
    HasDerivativeAtTao X f x₀ L
      ↔
    HasLinearApproximation X f x₀ L := by

  constructor

  · intro hf
    exact derivative_implies_linear_approximation
      X f x₀ L hf

  · intro hf
    exact linear_approximation_implies_derivative
      X f x₀ L hf


theorem exercise_10_1_2
    (X : Set ℝ)
    (f : X → ℝ)
    (x₀ : X)
    (L : ℝ) :
    HasDerivativeAtTao X f x₀ L
      ↔
    HasLinearApproximation X f x₀ L := by

  exact proposition_10_1_7 X f x₀ L

end TaoExercise10_1_2
