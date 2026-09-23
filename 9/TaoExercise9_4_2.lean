import Mathlib

namespace TaoExercise9_4_2

/-!
============================================================
Continuity on a subset X ⊆ ℝ
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
Constant function
============================================================
-/

theorem constant_continuous
    (X : Set ℝ)
    (c : ℝ) :
    ContinuousOnTao
      X
      (fun _ : X => c) := by

  intro x₀ ε hε

  refine ⟨1, by norm_num, ?_⟩

  intro x hx

  change abs (c - c) < ε

  rw [sub_self, abs_zero]

  exact hε


/-!
============================================================
Identity function
============================================================
-/

theorem identity_continuous
    (X : Set ℝ) :
    ContinuousOnTao
      X
      (fun x : X => (x : ℝ)) := by

  intro x₀ ε hε

  refine ⟨ε, hε, ?_⟩

  intro x hx

  exact hx


/-!
============================================================
Exercise 9.4.2
============================================================
-/

theorem exercise_9_4_2
    (X : Set ℝ)
    (c : ℝ) :
    ContinuousOnTao
        X
        (fun _ : X => c)
      ∧
    ContinuousOnTao
        X
        (fun x : X => (x : ℝ)) := by

  constructor

  · exact constant_continuous X c

  · exact identity_continuous X

end TaoExercise9_4_2
