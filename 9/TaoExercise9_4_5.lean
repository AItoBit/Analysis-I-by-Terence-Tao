import Mathlib

namespace TaoExercise9_4_5

open Filter
open Topology

/-!
============================================================
Proposition 9.4.13

Composition of continuous functions is continuous.
============================================================
-/

theorem proposition_9_4_13
    {X Y Z : Type*}
    [TopologicalSpace X]
    [TopologicalSpace Y]
    [TopologicalSpace Z]
    (f : X → Y)
    (g : Y → Z)
    (x₀ : X)
    (hf : ContinuousAt f x₀)
    (hg : ContinuousAt g (f x₀)) :
    ContinuousAt (g ∘ f) x₀ := by

  exact hg.comp hf


/-!
============================================================
Sequential formulation
============================================================
-/

theorem proposition_9_4_13_sequence
    {X Y Z : Type*}
    [TopologicalSpace X]
    [TopologicalSpace Y]
    [TopologicalSpace Z]
    (f : X → Y)
    (g : Y → Z)
    (x₀ : X)
    (hf : ContinuousAt f x₀)
    (hg : ContinuousAt g (f x₀))
    (a : ℕ → X)
    (ha :
      Tendsto a atTop (𝓝 x₀)) :
    Tendsto
      (fun n : ℕ => g (f (a n)))
      atTop
      (𝓝 (g (f x₀))) := by

  have hfa :
      Tendsto
        (fun n : ℕ => f (a n))
        atTop
        (𝓝 (f x₀)) := by

    exact hf.tendsto.comp ha

  have hgfa :
      Tendsto
        (fun n : ℕ => g (f (a n)))
        atTop
        (𝓝 (g (f x₀))) := by

    exact hg.tendsto.comp hfa

  exact hgfa


/-!
============================================================
Version specialized to ℝ
============================================================
-/

theorem proposition_9_4_13_real
    (f g : ℝ → ℝ)
    (x₀ : ℝ)
    (hf : ContinuousAt f x₀)
    (hg : ContinuousAt g (f x₀)) :
    ContinuousAt (g ∘ f) x₀ := by

  exact hg.comp hf


/-!
============================================================
Exercise 9.4.5
============================================================
-/

theorem exercise_9_4_5
    (f g : ℝ → ℝ)
    (x₀ : ℝ)
    (hf : ContinuousAt f x₀)
    (hg : ContinuousAt g (f x₀)) :
    ContinuousAt (g ∘ f) x₀ := by

  exact proposition_9_4_13_real
    f
    g
    x₀
    hf
    hg

end TaoExercise9_4_5
