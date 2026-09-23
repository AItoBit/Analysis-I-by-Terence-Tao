import Mathlib

namespace TaoExercise10_1_3

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


def ContinuousAtTao
    (X : Set ℝ)
    (f : X → ℝ)
    (x₀ : X) : Prop :=
  ∀ ε : ℝ,
    0 < ε →
    ∃ δ : ℝ,
      0 < δ ∧
      ∀ x : X,
        abs ((x : ℝ) - (x₀ : ℝ)) < δ →
        abs (f x - f x₀) < ε


lemma quotient_mul_eq
    (A h : ℝ)
    (hh : h ≠ 0) :
    A = (A / h) * h := by
  field_simp [hh]


theorem proposition_10_1_10
    (X : Set ℝ)
    (f : X → ℝ)
    (x₀ : X)
    (L : ℝ)
    (hf : HasDerivativeAtTao X f x₀ L) :
    ContinuousAtTao X f x₀ := by

  intro ε hε

  obtain ⟨α, hα, hdiff⟩ :=
    hf 1 (by norm_num)

  have hCpos :
      0 < abs L + 1 := by
    have hL : 0 ≤ abs L := abs_nonneg L
    linarith

  have hfrac :
      0 < ε / (abs L + 1) := by
    exact div_pos hε hCpos

  let δ : ℝ :=
    min α (ε / (abs L + 1))

  have hδ :
      0 < δ := by
    dsimp [δ]
    exact lt_min hα hfrac

  refine ⟨δ, hδ, ?_⟩

  intro x hxδ

  by_cases hxx₀ : x = x₀

  · subst x
    simpa using hε

  · have hsubne :
        (x : ℝ) - (x₀ : ℝ) ≠ 0 := by
      intro hzero

      have hval :
          (x : ℝ) = (x₀ : ℝ) := by
        exact sub_eq_zero.mp hzero

      apply hxx₀

      exact Subtype.ext hval

    have hxα :
        abs ((x : ℝ) - (x₀ : ℝ)) ≤ α := by

      have hδα :
          δ ≤ α := by
        dsimp [δ]
        exact min_le_left _ _

      exact le_trans
        (le_of_lt hxδ)
        hδα

    have hquotErr :
        abs
            ((f x - f x₀) /
                ((x : ℝ) - (x₀ : ℝ)) -
              L) ≤ 1 := by

      exact hdiff
        x
        hxx₀
        hxα

    let q : ℝ :=
      (f x - f x₀) /
        ((x : ℝ) - (x₀ : ℝ))

    have hqErr :
        abs (q - L) ≤ 1 := by
      exact hquotErr

    have htriangle :
        abs q ≤ abs (q - L) + abs L := by
      calc
        abs q =
            abs ((q - L) + L) := by
              congr 1
              ring
        _ ≤ abs (q - L) + abs L := by
              exact abs_add_le _ _

    have hquot :
        abs q ≤ abs L + 1 := by

      have hLnonneg :
          0 ≤ abs L := by
        exact abs_nonneg L

      calc
        abs q
            ≤ abs (q - L) + abs L := htriangle
        _ ≤ abs L + 1 := by
            linarith

    have hfactor :
        f x - f x₀ =
          q * ((x : ℝ) - (x₀ : ℝ)) := by

      dsimp [q]

      exact quotient_mul_eq
        (f x - f x₀)
        ((x : ℝ) - (x₀ : ℝ))
        hsubne

    have hbound :
        abs (f x - f x₀) ≤
          (abs L + 1) *
            abs ((x : ℝ) - (x₀ : ℝ)) := by

      rw [hfactor, abs_mul]

      exact mul_le_mul_of_nonneg_right
        hquot
        (abs_nonneg _)

    have hxfrac :
        abs ((x : ℝ) - (x₀ : ℝ)) <
          ε / (abs L + 1) := by

      have hδfrac :
          δ ≤ ε / (abs L + 1) := by
        dsimp [δ]
        exact min_le_right _ _

      exact lt_of_lt_of_le
        hxδ
        hδfrac

    have hsmall' :
        abs ((x : ℝ) - (x₀ : ℝ)) *
            (abs L + 1)
          < ε := by

      exact
        (lt_div_iff₀ hCpos).mp
          hxfrac

    have hsmall :
        (abs L + 1) *
            abs ((x : ℝ) - (x₀ : ℝ))
          < ε := by

      simpa [mul_comm] using hsmall'

    exact lt_of_le_of_lt
      hbound
      hsmall


def DifferentiableAtTao
    (X : Set ℝ)
    (f : X → ℝ)
    (x₀ : X) : Prop :=
  ∃ L : ℝ,
    HasDerivativeAtTao X f x₀ L


theorem exercise_10_1_3
    (X : Set ℝ)
    (f : X → ℝ)
    (x₀ : X)
    (hf : DifferentiableAtTao X f x₀) :
    ContinuousAtTao X f x₀ := by

  obtain ⟨L, hL⟩ := hf

  exact proposition_10_1_10
    X
    f
    x₀
    L
    hL

end TaoExercise10_1_3
