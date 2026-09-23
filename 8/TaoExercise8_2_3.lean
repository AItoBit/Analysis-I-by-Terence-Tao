import Mathlib

namespace TaoExercise8_2_3

open Function
open scoped BigOperators

universe u

def AbsolutelyConvergent
    {X : Type u}
    (f : X → ℝ) : Prop :=
  Summable (fun x : X => |f x|)

theorem summable_of_absolutelyConvergent
    {X : Type u}
    {f : X → ℝ}
    (hf : AbsolutelyConvergent f) :
    Summable f := by

  unfold AbsolutelyConvergent at hf

  have hnorm :
      Summable (fun x : X => ‖f x‖) := by
    simpa [Real.norm_eq_abs] using hf

  exact summable_norm_iff.mp hnorm


theorem absolutelyConvergent_mul
    {X : Type u}
    (f : X → ℝ)
    (c : ℝ)
    (hf : AbsolutelyConvergent f) :
    AbsolutelyConvergent
      (fun x : X => c * f x) := by

  unfold AbsolutelyConvergent at *

  have h :
      Summable
        (fun x : X => |c| * |f x|) := by
    exact hf.mul_left |c|

  simpa [abs_mul] using h


theorem tsum_mul_left
    {X : Type u}
    (f : X → ℝ)
    (c : ℝ)
    (hf : AbsolutelyConvergent f) :
    (∑' x : X, c * f x)
      =
    c * (∑' x : X, f x) := by

  have hSummable :
      Summable f := by
    exact summable_of_absolutelyConvergent hf

  exact hSummable.tsum_mul_left c


theorem proposition_8_2_6_b
    {X : Type u}
    (f : X → ℝ)
    (c : ℝ)
    (hf : AbsolutelyConvergent f) :
    AbsolutelyConvergent
        (fun x : X => c * f x)
      ∧
    (∑' x : X, c * f x)
        =
    c * (∑' x : X, f x) := by

  constructor

  · exact absolutelyConvergent_mul
      f
      c
      hf

  · exact tsum_mul_left
      f
      c
      hf


theorem proposition_8_2_6_b_smul
    {X : Type u}
    (f : X → ℝ)
    (c : ℝ)
    (hf : AbsolutelyConvergent f) :
    AbsolutelyConvergent
        (fun x : X => c • f x)
      ∧
    (∑' x : X, c • f x)
        =
    c • (∑' x : X, f x) := by

  constructor

  · simpa [smul_eq_mul] using
      absolutelyConvergent_mul
        f
        c
        hf

  · simpa [smul_eq_mul] using
      tsum_mul_left
        f
        c
        hf


theorem exercise_8_2_3
    {X : Type u}
    (f : X → ℝ)
    (c : ℝ)
    (hf : AbsolutelyConvergent f) :
    AbsolutelyConvergent
        (fun x : X => c * f x)
      ∧
    (∑' x : X, c * f x)
        =
    c * (∑' x : X, f x) := by

  exact proposition_8_2_6_b
    f
    c
    hf

end TaoExercise8_2_3
