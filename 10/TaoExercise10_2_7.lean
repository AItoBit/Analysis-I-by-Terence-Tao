import Mathlib

namespace TaoExercise10_2_7

open Set

/-!
============================================================
Bounded derivative
============================================================
-/

def DerivativeBounded
    (f : ℝ → ℝ) : Prop :=
  ∃ M : ℝ,
    0 < M ∧
    ∀ x : ℝ,
      abs (deriv f x) ≤ M


/-!
============================================================
Uniform continuity, Tao epsilon-delta style
============================================================
-/

def UniformContinuousTao
    (f : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ,
    0 < ε →
    ∃ δ : ℝ,
      0 < δ ∧
      ∀ x y : ℝ,
        abs (x - y) ≤ δ →
        abs (f x - f y) ≤ ε


/-!
============================================================
Mean-value bound on an arbitrary interval [x,y]
============================================================
-/

lemma bound_of_derivative_bound
    (f : ℝ → ℝ)
    (M : ℝ)
    (hM : 0 < M)
    (hf_diff : Differentiable ℝ f)
    (hderiv :
      ∀ z : ℝ,
        abs (deriv f z) ≤ M) :
    ∀ x y : ℝ,
      abs (f x - f y) ≤ M * abs (x - y) := by

  intro x y

  rcases lt_trichotomy x y with hxy | hxy | hyx

  · have hcont_xy :
        ContinuousOn f (Set.Icc x y) := by
      exact hf_diff.continuous.continuousOn

    have hdiff_xy :
        DifferentiableOn ℝ f (Set.Ioo x y) := by
      exact hf_diff.differentiableOn

    obtain ⟨c, hc, hcderiv⟩ :=
      exists_deriv_eq_slope
        f
        hxy
        hcont_xy
        hdiff_xy

    have hcBound :
        abs (deriv f c) ≤ M := by
      exact hderiv c

    have hquot :
        abs ((f y - f x) / (y - x)) ≤ M := by
      rw [← hcderiv]
      exact hcBound

    have hyxpos :
        0 < y - x := by
      linarith

    rw [abs_div, abs_of_pos hyxpos] at hquot

    have hmain :
        abs (f y - f x) ≤ M * (y - x) := by
      exact (div_le_iff₀ hyxpos).mp hquot

    have hfun :
        abs (f x - f y) =
          abs (f y - f x) := by
      have h :
          f x - f y = -(f y - f x) := by
        ring
      rw [h, abs_neg]

    have harg :
        abs (x - y) = y - x := by
      have hneg :
          x - y < 0 := by
        linarith
      rw [abs_of_neg hneg]
      ring

    rw [hfun, harg]

    exact hmain

  · subst y
    norm_num

  · have h :
        abs (f y - f x) ≤
          M * abs (y - x) := by

      have hcont_yx :
          ContinuousOn f (Set.Icc y x) := by
        exact hf_diff.continuous.continuousOn

      have hdiff_yx :
          DifferentiableOn ℝ f (Set.Ioo y x) := by
        exact hf_diff.differentiableOn

      obtain ⟨c, hc, hcderiv⟩ :=
        exists_deriv_eq_slope
          f
          hyx
          hcont_yx
          hdiff_yx

      have hcBound :
          abs (deriv f c) ≤ M := by
        exact hderiv c

      have hquot :
          abs ((f x - f y) / (x - y)) ≤ M := by
        rw [← hcderiv]
        exact hcBound

      have hxypos :
          0 < x - y := by
        linarith

      rw [abs_div, abs_of_pos hxypos] at hquot

      have hmain :
          abs (f x - f y) ≤ M * (x - y) := by
        exact (div_le_iff₀ hxypos).mp hquot

      have hfun :
          abs (f y - f x) =
            abs (f x - f y) := by
        have heq :
            f y - f x = -(f x - f y) := by
          ring
        rw [heq, abs_neg]

      have harg :
          abs (y - x) = x - y := by
        have hneg :
            y - x < 0 := by
          linarith
        rw [abs_of_neg hneg]
        ring

      rw [hfun, harg]

      exact hmain

    have hfun :
        abs (f x - f y) =
          abs (f y - f x) := by
      have heq :
          f x - f y = -(f y - f x) := by
        ring
      rw [heq, abs_neg]

    have harg :
        abs (x - y) =
          abs (y - x) := by
      have heq :
          x - y = -(y - x) := by
        ring
      rw [heq, abs_neg]

    rw [hfun, harg]

    exact h


/-!
============================================================
Exercise 10.2.7
============================================================
-/

theorem exercise_10_2_7
    (f : ℝ → ℝ)
    (hf_diff : Differentiable ℝ f)
    (hf_bounded : DerivativeBounded f) :
    UniformContinuousTao f := by

  obtain ⟨M, hM, hderiv⟩ := hf_bounded

  have hLip :
      ∀ x y : ℝ,
        abs (f x - f y) ≤
          M * abs (x - y) := by

    exact bound_of_derivative_bound
      f
      M
      hM
      hf_diff
      hderiv

  intro ε hε

  let δ : ℝ := ε / M

  have hδ :
      0 < δ := by
    dsimp [δ]
    exact div_pos hε hM

  refine ⟨δ, hδ, ?_⟩

  intro x y hxy

  have h₁ :
      abs (f x - f y) ≤
        M * abs (x - y) := by
    exact hLip x y

  have h₂ :
      M * abs (x - y) ≤ ε := by

    have hδdef :
        abs (x - y) ≤ ε / M := by
      exact hxy

    exact (le_div_iff₀ hM).mp hδdef

  exact le_trans h₁ h₂

end TaoExercise10_2_7
