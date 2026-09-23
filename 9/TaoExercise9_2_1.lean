import Mathlib

namespace TaoExercise9_2_1

open Function

/-!
============================================================
Statement 1

(f + g) ∘ h = (f ∘ h) + (g ∘ h)
============================================================
-/

theorem statement_1
    (f g h : ℝ → ℝ) :
    (f + g) ∘ h = (f ∘ h) + (g ∘ h) := by
  funext x
  rfl


/-!
============================================================
Statement 2 is false in general
============================================================

Counterexample:

    f(x) = x^2
    g(x) = x
    h(x) = -x
-/

def f₂ : ℝ → ℝ :=
  fun x => x ^ 2

def g₂ : ℝ → ℝ :=
  fun x => x

def h₂ : ℝ → ℝ :=
  fun x => -x


theorem statement_2_counterexample :
    f₂ ∘ (g₂ + h₂) ≠
      (f₂ ∘ g₂) + (f₂ ∘ h₂) := by

  intro hEq

  have hAtOne :
      (f₂ ∘ (g₂ + h₂)) 1 =
        ((f₂ ∘ g₂) + (f₂ ∘ h₂)) 1 := by
    exact congrFun hEq 1

  norm_num [f₂, g₂, h₂, Function.comp_def] at hAtOne


/-!
============================================================
Statement 3

(f + g) * h = f * h + g * h
============================================================
-/

theorem statement_3
    (f g h : ℝ → ℝ) :
    (f + g) * h = f * h + g * h := by
  funext x
  dsimp
  ring


/-!
============================================================
Statement 4

f * (g + h) = f * g + f * h
============================================================
-/

theorem statement_4
    (f g h : ℝ → ℝ) :
    f * (g + h) = f * g + f * h := by
  funext x
  dsimp
  ring


/-!
============================================================
Exercise 9.2.1
============================================================
-/

theorem exercise_9_2_1
    (f g h : ℝ → ℝ) :
    ((f + g) ∘ h = (f ∘ h) + (g ∘ h))
      ∧
    (f₂ ∘ (g₂ + h₂) ≠
      (f₂ ∘ g₂) + (f₂ ∘ h₂))
      ∧
    ((f + g) * h = f * h + g * h)
      ∧
    (f * (g + h) = f * g + f * h) := by
  constructor
  · exact statement_1 f g h

  constructor
  · exact statement_2_counterexample

  constructor
  · exact statement_3 f g h

  · exact statement_4 f g h

end TaoExercise9_2_1
