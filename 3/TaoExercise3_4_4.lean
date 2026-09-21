import Mathlib

namespace TaoExercise3_4_4

open Set

universe u v

variable {X : Type u} {Y : Type v}

/--
Preimages preserve unions:

    f⁻¹(A ∪ B) = f⁻¹(A) ∪ f⁻¹(B)
-/
theorem preimage_union
    (f : X → Y)
    (A B : Set Y) :
    f ⁻¹' (A ∪ B) = (f ⁻¹' A) ∪ (f ⁻¹' B) := by
  ext x
  constructor

  · intro hx
    rcases hx with hxA | hxB
    · exact Or.inl hxA
    · exact Or.inr hxB

  · intro hx
    rcases hx with hxA | hxB
    · exact Or.inl hxA
    · exact Or.inr hxB


/--
Preimages preserve intersections:

    f⁻¹(A ∩ B) = f⁻¹(A) ∩ f⁻¹(B)
-/
theorem preimage_inter
    (f : X → Y)
    (A B : Set Y) :
    f ⁻¹' (A ∩ B) = (f ⁻¹' A) ∩ (f ⁻¹' B) := by
  ext x
  constructor

  · intro hx
    exact ⟨hx.1, hx.2⟩

  · intro hx
    exact ⟨hx.1, hx.2⟩


/--
Preimages preserve set difference:

    f⁻¹(A \ B) = f⁻¹(A) \ f⁻¹(B)
-/
theorem preimage_diff
    (f : X → Y)
    (A B : Set Y) :
    f ⁻¹' (A \ B) = (f ⁻¹' A) \ (f ⁻¹' B) := by
  ext x
  constructor

  · intro hx
    exact ⟨hx.1, hx.2⟩

  · intro hx
    exact ⟨hx.1, hx.2⟩


/--
Exercise 3.4.4.
-/
theorem exercise_3_4_4
    (f : X → Y)
    (A B : Set Y) :
    f ⁻¹' (A ∪ B) = (f ⁻¹' A) ∪ (f ⁻¹' B)
    ∧
    f ⁻¹' (A ∩ B) = (f ⁻¹' A) ∩ (f ⁻¹' B)
    ∧
    f ⁻¹' (A \ B) = (f ⁻¹' A) \ (f ⁻¹' B) := by
  constructor
  · exact preimage_union f A B
  · constructor
    · exact preimage_inter f A B
    · exact preimage_diff f A B

end TaoExercise3_4_4
