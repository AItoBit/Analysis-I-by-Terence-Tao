import Mathlib

namespace TaoExercise10_2_6

open Set

/-!
============================================================
Ordered case: x < y
============================================================
-/

lemma bound_of_lt
    (f : ℝ → ℝ)
    (a b M x y : ℝ)
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hf_diff : DifferentiableOn ℝ f (Set.Ioo a b))
    (hderiv :
      ∀ z ∈ Set.Ioo a b,
        abs (deriv f z) ≤ M)
    (hx : x ∈ Set.Icc a b)
    (hy : y ∈ Set.Icc a b)
    (hxy : x < y) :
    abs (f x - f y) ≤ M * abs (x - y) := by

  /-
  f is continuous on [x,y].
  -/

  have hcont_xy :
      ContinuousOn f (Set.Icc x y) := by

    apply hf_cont.mono

    intro z hz

    constructor

    · exact le_trans hx.1 hz.1

    · exact le_trans hz.2 hy.2

  /-
  f is differentiable on (x,y).
  -/

  have hdiff_xy :
      DifferentiableOn ℝ f (Set.Ioo x y) := by

    apply hf_diff.mono

    intro z hz

    constructor

    · exact lt_of_le_of_lt hx.1 hz.1

    · exact lt_of_lt_of_le hz.2 hy.2

  /-
  Apply the Mean Value Theorem.
  -/

  obtain ⟨c, hc, hcderiv⟩ :=
    exists_deriv_eq_slope
      f
      hxy
      hcont_xy
      hdiff_xy

  /-
  c is also in (a,b).
  -/

  have hcab :
      c ∈ Set.Ioo a b := by

    constructor

    · exact lt_of_le_of_lt
        hx.1
        hc.1

    · exact lt_of_lt_of_le
        hc.2
        hy.2

  /-
  The derivative is bounded at c.
  -/

  have hcBound :
      abs (deriv f c) ≤ M := by

    exact hderiv c hcab

  /-
  By MVT,

      f'(c) = (f(y)-f(x))/(y-x).
  -/

  have hquot :
      abs ((f y - f x) / (y - x)) ≤ M := by

    rw [← hcderiv]

    exact hcBound

  have hyxpos :
      0 < y - x := by
    linarith

  /-
  Remove the absolute value from y-x.
  -/

  rw [abs_div] at hquot

  have habsyx :
      abs (y - x) = y - x := by
    exact abs_of_pos hyxpos

  rw [habsyx] at hquot

  /-
  Multiply by y-x > 0.
  -/

  have hmain :
      abs (f y - f x) ≤
        M * (y - x) := by

    exact (div_le_iff₀ hyxpos).mp hquot

  /-
  Convert to Tao's orientation:

      |f(x)-f(y)| ≤ M |x-y|.
  -/

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


/-!
============================================================
Exercise 10.2.6
============================================================
-/

theorem exercise_10_2_6
    (f : ℝ → ℝ)
    (a b M : ℝ)
    (hM : 0 < M)
    (hf_cont : ContinuousOn f (Set.Icc a b))
    (hf_diff : DifferentiableOn ℝ f (Set.Ioo a b))
    (hderiv :
      ∀ z ∈ Set.Ioo a b,
        abs (deriv f z) ≤ M) :
    ∀ x ∈ Set.Icc a b,
      ∀ y ∈ Set.Icc a b,
        abs (f x - f y) ≤
          M * abs (x - y) := by

  intro x hx y hy

  rcases lt_trichotomy x y with hxy | hxy | hyx

  /-
  Case 1: x < y
  -/

  · exact bound_of_lt
      f
      a
      b
      M
      x
      y
      hf_cont
      hf_diff
      hderiv
      hx
      hy
      hxy

  /-
  Case 2: x = y
  -/

  · subst y

    norm_num

  /-
  Case 3: y < x

  Apply the already proved ordered case to y,x
  and use symmetry of absolute value.
  -/

  · have h :
        abs (f y - f x) ≤
          M * abs (y - x) := by

      exact bound_of_lt
        f
        a
        b
        M
        y
        x
        hf_cont
        hf_diff
        hderiv
        hy
        hx
        hyx

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

end TaoExercise10_2_6
