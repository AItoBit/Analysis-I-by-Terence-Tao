import Mathlib

namespace TaoExercise3_4_2

open Set

universe u v

variable {X : Type u} {Y : Type v}

/--
For any function f : X → Y and any set S ⊆ X,

    S ⊆ f⁻¹(f(S)).
-/
theorem subset_preimage_image
    (f : X → Y)
    (S : Set X) :
    S ⊆ f ⁻¹' (f '' S) := by
  intro x hxS

  change f x ∈ f '' S

  exact ⟨x, hxS, rfl⟩


/--
For any function f : X → Y and any set U ⊆ Y,

    f(f⁻¹(U)) ⊆ U.
-/
theorem image_preimage_subset
    (f : X → Y)
    (U : Set Y) :
    f '' (f ⁻¹' U) ⊆ U := by
  intro y hy

  rcases hy with ⟨x, hx, rfl⟩

  exact hx


/--
Exercise 3.4.2.

The general inclusions are

    S ⊆ f⁻¹(f(S))

and

    f(f⁻¹(U)) ⊆ U.
-/
theorem exercise_3_4_2
    (f : X → Y)
    (S : Set X)
    (U : Set Y) :
    S ⊆ f ⁻¹' (f '' S)
    ∧
    f '' (f ⁻¹' U) ⊆ U := by
  constructor
  · exact subset_preimage_image f S
  · exact image_preimage_subset f U

end TaoExercise3_4_2
