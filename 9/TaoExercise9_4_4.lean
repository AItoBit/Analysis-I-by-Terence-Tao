import Mathlib

namespace TaoExercise9_4_4

open Set
open Filter
open Topology

theorem rpow_continuousAt_of_pos
    (p x : ℝ)
    (hx : 0 < x) :
    ContinuousAt
      (fun y : ℝ => y ^ p)
      x := by

  have hxne :
      x ≠ 0 := by
    exact ne_of_gt hx

  exact Real.continuousAt_rpow_const
    x
    p
    (Or.inl hxne)


theorem proposition_9_4_11
    (p : ℝ) :
    ContinuousOn
      (fun x : ℝ => x ^ p)
      (Set.Ioi (0 : ℝ)) := by

  intro x hx

  have hxpos :
      0 < x := by
    exact hx

  have hcont :
      ContinuousAt
        (fun y : ℝ => y ^ p)
        x := by
    exact rpow_continuousAt_of_pos
      p
      x
      hxpos

  exact hcont.continuousWithinAt


theorem rpow_limit_at_positive
    (p a : ℝ)
    (ha : 0 < a) :
    Tendsto
      (fun x : ℝ => x ^ p)
      (𝓝 a)
      (𝓝 (a ^ p)) := by

  exact
    (rpow_continuousAt_of_pos
      p
      a
      ha).tendsto


theorem rpow_limit_one
    (p : ℝ) :
    Tendsto
      (fun x : ℝ => x ^ p)
      (𝓝 (1 : ℝ))
      (𝓝 (1 : ℝ)) := by

  have h :
      Tendsto
        (fun x : ℝ => x ^ p)
        (𝓝 (1 : ℝ))
        (𝓝 ((1 : ℝ) ^ p)) := by

    exact
      rpow_limit_at_positive
        p
        1
        (by norm_num)

  simpa using h


theorem rpow_sequence_at_positive
    (p a : ℝ)
    (ha : 0 < a)
    (u : ℕ → ℝ)
    (hu :
      Tendsto u atTop (𝓝 a)) :
    Tendsto
      (fun n : ℕ => (u n) ^ p)
      atTop
      (𝓝 (a ^ p)) := by

  have hp :
      Tendsto
        (fun x : ℝ => x ^ p)
        (𝓝 a)
        (𝓝 (a ^ p)) := by

    exact rpow_limit_at_positive
      p
      a
      ha

  exact hp.comp hu


theorem rpow_continuous_positive_subtype
    (p : ℝ) :
    Continuous
      (fun x : Set.Ioi (0 : ℝ) =>
        ((x : ℝ) ^ p)) := by

  rw [continuous_iff_continuousAt]

  intro x

  have hx :
      0 < (x : ℝ) := by
    exact x.property

  have hambient :
      ContinuousAt
        (fun y : ℝ => y ^ p)
        (x : ℝ) := by

    exact rpow_continuousAt_of_pos
      p
      (x : ℝ)
      hx

  exact hambient.comp continuousAt_subtype_val


theorem exercise_9_4_4
    (p : ℝ) :
    ContinuousOn
      (fun x : ℝ => x ^ p)
      (Set.Ioi (0 : ℝ)) := by

  exact proposition_9_4_11 p

end TaoExercise9_4_4
