import Mathlib

namespace TaoExercise9_4_3

open Filter
open Topology

/-!
============================================================
Proposition 9.4.10
============================================================
-/

theorem proposition_9_4_10
    (a : ℝ)
    (ha : 0 < a) :
    Continuous (fun x : ℝ => a ^ x) := by

  have hane :
      a ≠ 0 := by
    exact ne_of_gt ha

  exact Real.continuous_const_rpow hane


/-!
============================================================
Pointwise continuity
============================================================
-/

theorem proposition_9_4_10_at
    (a x₀ : ℝ)
    (ha : 0 < a) :
    ContinuousAt
      (fun x : ℝ => a ^ x)
      x₀ := by

  exact
    (proposition_9_4_10 a ha).continuousAt


/-!
============================================================
Limit formulation
============================================================
-/

theorem proposition_9_4_10_limit
    (a x₀ : ℝ)
    (ha : 0 < a) :
    Tendsto
      (fun x : ℝ => a ^ x)
      (𝓝 x₀)
      (𝓝 (a ^ x₀)) := by

  exact
    (proposition_9_4_10_at
      a
      x₀
      ha).tendsto


/-!
============================================================
Sequential formulation
============================================================
-/

theorem proposition_9_4_10_sequence
    (a x₀ : ℝ)
    (ha : 0 < a)
    (r : ℕ → ℝ)
    (hr :
      Tendsto
        r
        atTop
        (𝓝 x₀)) :
    Tendsto
      (fun n : ℕ => a ^ (r n))
      atTop
      (𝓝 (a ^ x₀)) := by

  have hpow :
      Tendsto
        (fun x : ℝ => a ^ x)
        (𝓝 x₀)
        (𝓝 (a ^ x₀)) := by

    exact
      proposition_9_4_10_limit
        a
        x₀
        ha

  exact hpow.comp hr


/-!
============================================================
Exercise 9.4.3
============================================================
-/

theorem exercise_9_4_3
    (a : ℝ)
    (ha : 0 < a) :
    Continuous (fun x : ℝ => a ^ x) := by

  exact proposition_9_4_10 a ha

end TaoExercise9_4_3
