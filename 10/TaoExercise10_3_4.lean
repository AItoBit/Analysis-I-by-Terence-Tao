import Mathlib

namespace TaoExercise10_3_4

open Set

/-!
============================================================
Positive derivative -> strictly increasing
============================================================
-/

theorem strictMonoOn_of_deriv_pos
    (f : ℝ → ℝ)
    (a b : ℝ)
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hf_diff : DifferentiableOn ℝ f (Set.Ioo a b))
    (hderiv :
      ∀ x ∈ Set.Ioo a b,
        0 < deriv f x) :
    StrictMonoOn f (Set.Icc a b) := by

  intro x hx y hy hxy

  have hcont_xy :
      ContinuousOn f (Set.Icc x y) := by
    apply hf_cont.mono
    intro z hz
    exact
      ⟨le_trans hx.1 hz.1,
       le_trans hz.2 hy.2⟩

  have hdiff_xy :
      DifferentiableOn ℝ f (Set.Ioo x y) := by
    apply hf_diff.mono
    intro z hz
    exact
      ⟨lt_of_le_of_lt hx.1 hz.1,
       lt_of_lt_of_le hz.2 hy.2⟩

  obtain ⟨c, hc, hcderiv⟩ :=
    exists_deriv_eq_slope
      f
      hxy
      hcont_xy
      hdiff_xy

  have hcab :
      c ∈ Set.Ioo a b := by
    exact
      ⟨lt_of_le_of_lt hx.1 hc.1,
       lt_of_lt_of_le hc.2 hy.2⟩

  have hcpos :
      0 < deriv f c := by
    exact hderiv c hcab

  have hslope :
      0 <
        (f y - f x) / (y - x) := by
    rw [← hcderiv]
    exact hcpos

  have hyxpos :
      0 < y - x := by
    linarith

  have hprod :
      0 <
        ((f y - f x) / (y - x)) *
          (y - x) := by
    exact mul_pos hslope hyxpos

  have hyxne :
      y - x ≠ 0 := ne_of_gt hyxpos

  have hcancel :
      ((f y - f x) / (y - x)) *
          (y - x)
        =
      f y - f x := by
    field_simp [hyxne]

  rw [hcancel] at hprod

  linarith


/-!
============================================================
Negative derivative -> strictly decreasing
============================================================
-/

theorem strictAntiOn_of_deriv_neg
    (f : ℝ → ℝ)
    (a b : ℝ)
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hf_diff : DifferentiableOn ℝ f (Set.Ioo a b))
    (hderiv :
      ∀ x ∈ Set.Ioo a b,
        deriv f x < 0) :
    StrictAntiOn f (Set.Icc a b) := by

  intro x hx y hy hxy

  have hcont_xy :
      ContinuousOn f (Set.Icc x y) := by
    apply hf_cont.mono
    intro z hz
    exact
      ⟨le_trans hx.1 hz.1,
       le_trans hz.2 hy.2⟩

  have hdiff_xy :
      DifferentiableOn ℝ f (Set.Ioo x y) := by
    apply hf_diff.mono
    intro z hz
    exact
      ⟨lt_of_le_of_lt hx.1 hz.1,
       lt_of_lt_of_le hz.2 hy.2⟩

  obtain ⟨c, hc, hcderiv⟩ :=
    exists_deriv_eq_slope
      f
      hxy
      hcont_xy
      hdiff_xy

  have hcab :
      c ∈ Set.Ioo a b := by
    exact
      ⟨lt_of_le_of_lt hx.1 hc.1,
       lt_of_lt_of_le hc.2 hy.2⟩

  have hcneg :
      deriv f c < 0 := by
    exact hderiv c hcab

  have hslope :
      (f y - f x) / (y - x) < 0 := by
    rw [← hcderiv]
    exact hcneg

  have hyxpos :
      0 < y - x := by
    linarith

  have hprod :
      ((f y - f x) / (y - x)) *
          (y - x)
        < 0 := by
    exact mul_neg_of_neg_of_pos
      hslope
      hyxpos

  have hyxne :
      y - x ≠ 0 := ne_of_gt hyxpos

  have hcancel :
      ((f y - f x) / (y - x)) *
          (y - x)
        =
      f y - f x := by
    field_simp [hyxne]

  rw [hcancel] at hprod

  linarith


/-!
============================================================
Zero derivative -> constant
============================================================
-/

theorem eqOn_of_deriv_zero
    (f : ℝ → ℝ)
    (a b : ℝ)
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hf_diff : DifferentiableOn ℝ f (Set.Ioo a b))
    (hderiv :
      ∀ x ∈ Set.Ioo a b,
        deriv f x = 0) :
    ∀ x ∈ Set.Icc a b,
      ∀ y ∈ Set.Icc a b,
        f x = f y := by

  intro x hx y hy

  rcases lt_trichotomy x y with hxy | hxy | hyx

  · have hcont_xy :
        ContinuousOn f (Set.Icc x y) := by
      apply hf_cont.mono
      intro z hz
      exact
        ⟨le_trans hx.1 hz.1,
         le_trans hz.2 hy.2⟩

    have hdiff_xy :
        DifferentiableOn ℝ f (Set.Ioo x y) := by
      apply hf_diff.mono
      intro z hz
      exact
        ⟨lt_of_le_of_lt hx.1 hz.1,
         lt_of_lt_of_le hz.2 hy.2⟩

    obtain ⟨c, hc, hcderiv⟩ :=
      exists_deriv_eq_slope
        f
        hxy
        hcont_xy
        hdiff_xy

    have hcab :
        c ∈ Set.Ioo a b := by
      exact
        ⟨lt_of_le_of_lt hx.1 hc.1,
         lt_of_lt_of_le hc.2 hy.2⟩

    have hcZero :
        deriv f c = 0 := by
      exact hderiv c hcab

    have hslope :
        (f y - f x) / (y - x) = 0 := by
      rw [← hcderiv]
      exact hcZero

    have hyxne :
        y - x ≠ 0 := by
      linarith

    have hnum :
        f y - f x = 0 := by
      apply (div_eq_zero_iff).mp at hslope
      rcases hslope with h | h
      · exact h
      · exact (hyxne h).elim

    linarith

  · subst y
    rfl

  · have hcont_yx :
        ContinuousOn f (Set.Icc y x) := by
      apply hf_cont.mono
      intro z hz
      exact
        ⟨le_trans hy.1 hz.1,
         le_trans hz.2 hx.2⟩

    have hdiff_yx :
        DifferentiableOn ℝ f (Set.Ioo y x) := by
      apply hf_diff.mono
      intro z hz
      exact
        ⟨lt_of_le_of_lt hy.1 hz.1,
         lt_of_lt_of_le hz.2 hx.2⟩

    obtain ⟨c, hc, hcderiv⟩ :=
      exists_deriv_eq_slope
        f
        hyx
        hcont_yx
        hdiff_yx

    have hcab :
        c ∈ Set.Ioo a b := by
      exact
        ⟨lt_of_le_of_lt hy.1 hc.1,
         lt_of_lt_of_le hc.2 hx.2⟩

    have hcZero :
        deriv f c = 0 := by
      exact hderiv c hcab

    have hslope :
        (f x - f y) / (x - y) = 0 := by
      rw [← hcderiv]
      exact hcZero

    have hxyne :
        x - y ≠ 0 := by
      linarith

    have hnum :
        f x - f y = 0 := by
      apply (div_eq_zero_iff).mp at hslope
      rcases hslope with h | h
      · exact h
      · exact (hxyne h).elim

    linarith


/-!
============================================================
Proposition 10.3.3
============================================================
-/

theorem proposition_10_3_3
    (f : ℝ → ℝ)
    (a b : ℝ)
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hf_diff : DifferentiableOn ℝ f (Set.Ioo a b)) :
    ((∀ x ∈ Set.Ioo a b,
        0 < deriv f x) →
      StrictMonoOn f (Set.Icc a b))
      ∧
    ((∀ x ∈ Set.Ioo a b,
        deriv f x < 0) →
      StrictAntiOn f (Set.Icc a b))
      ∧
    ((∀ x ∈ Set.Ioo a b,
        deriv f x = 0) →
      ∀ x ∈ Set.Icc a b,
        ∀ y ∈ Set.Icc a b,
          f x = f y) := by

  constructor

  · intro hpos
    exact strictMonoOn_of_deriv_pos
      f a b hf_cont hf_diff hpos

  · constructor

    · intro hneg
      exact strictAntiOn_of_deriv_neg
        f a b hf_cont hf_diff hneg

    · intro hzero
      exact eqOn_of_deriv_zero
        f a b hf_cont hf_diff hzero


/-!
============================================================
Exercise 10.3.4
============================================================
-/

theorem exercise_10_3_4
    (f : ℝ → ℝ)
    (a b : ℝ)
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hf_diff : DifferentiableOn ℝ f (Set.Ioo a b))
    (hpos :
      ∀ x ∈ Set.Ioo a b,
        0 < deriv f x) :
    StrictMonoOn f (Set.Icc a b) := by

  exact strictMonoOn_of_deriv_pos
    f
    a
    b
    hf_cont
    hf_diff
    hpos

end TaoExercise10_3_4
