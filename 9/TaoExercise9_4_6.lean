import Mathlib

namespace TaoExercise9_4_6

/-!
============================================================
Continuity for a function defined on a subset X ⊆ ℝ
============================================================
-/

def ContinuousOnTao
    (X : Set ℝ)
    (f : X → ℝ) : Prop :=
  ∀ x₀ : X,
    ∀ ε : ℝ,
      0 < ε →
      ∃ δ : ℝ,
        0 < δ ∧
        ∀ x : X,
          abs ((x : ℝ) - (x₀ : ℝ)) < δ →
          abs (f x - f x₀) < ε


/-!
============================================================
Restriction f|Y
============================================================
-/

def restrict
    (X Y : Set ℝ)
    (hYX : Y ⊆ X)
    (f : X → ℝ) :
    Y → ℝ :=
  fun y =>
    f ⟨(y : ℝ), hYX y.property⟩


/-!
============================================================
Exercise 9.4.6

If f : X → ℝ is continuous and Y ⊆ X,
then f restricted to Y is continuous.
============================================================
-/

theorem exercise_9_4_6
    (X Y : Set ℝ)
    (hYX : Y ⊆ X)
    (f : X → ℝ)
    (hf : ContinuousOnTao X f) :
    ContinuousOnTao Y (restrict X Y hYX f) := by

  intro y₀ ε hε

  let x₀ : X :=
    ⟨(y₀ : ℝ), hYX y₀.property⟩

  obtain ⟨δ, hδpos, hδ⟩ :=
    hf x₀ ε hε

  refine ⟨δ, hδpos, ?_⟩

  intro y hy

  let x : X :=
    ⟨(y : ℝ), hYX y.property⟩

  have hx :
      abs ((x : ℝ) - (x₀ : ℝ)) < δ := by
    exact hy

  have hfx :
      abs (f x - f x₀) < ε := by
    exact hδ x hx

  exact hfx

end TaoExercise9_4_6
