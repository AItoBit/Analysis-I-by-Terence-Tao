import Mathlib

namespace TaoExercise3_3_1

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}

/--
Reflexivity of function equality.
-/
theorem function_eq_refl (f : X → Y) :
    f = f := by
  rfl


/--
Symmetry of function equality.
-/
theorem function_eq_symm
    (f g : X → Y)
    (h : f = g) :
    g = f := by
  exact h.symm


/--
Transitivity of function equality.
-/
theorem function_eq_trans
    (f g h : X → Y)
    (hfg : f = g)
    (hgh : g = h) :
    f = h := by
  exact hfg.trans hgh


/--
Function extensionality:
if f(x) = g(x) for every x, then f = g.
This corresponds closely to Tao's Definition 3.3.7.
-/
theorem function_extensionality
    (f g : X → Y)
    (h : ∀ x : X, f x = g x) :
    f = g := by
  funext x
  exact h x


/--
Substitution property for composition.

If f₁ = f₂ and g₁ = g₂, then

    g₁ ∘ f₁ = g₂ ∘ f₂.
-/
theorem composition_substitution
    (f₁ f₂ : X → Y)
    (g₁ g₂ : Y → Z)
    (hf : f₁ = f₂)
    (hg : g₁ = g₂) :
    g₁ ∘ f₁ = g₂ ∘ f₂ := by
  funext x

  calc
    (g₁ ∘ f₁) x
        = g₁ (f₁ x) := rfl
    _ = g₂ (f₁ x) := by
          rw [hg]
    _ = g₂ (f₂ x) := by
          rw [hf]
    _ = (g₂ ∘ f₂) x := rfl


/--
Exercise 3.3.1 packaged together.
-/
theorem exercise_3_3_1
    (f₁ f₂ : X → Y)
    (g₁ g₂ : Y → Z)
    (hf : f₁ = f₂)
    (hg : g₁ = g₂) :
    g₁ ∘ f₁ = g₂ ∘ f₂ := by
  exact composition_substitution f₁ f₂ g₁ g₂ hf hg

end TaoExercise3_3_1
