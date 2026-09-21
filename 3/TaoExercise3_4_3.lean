import Mathlib

namespace TaoExercise3_4_3

open Set

universe u v

variable {X : Type u} {Y : Type v}

/--
1. The image of an intersection is contained in
the intersection of the images:

    f(A ∩ B) ⊆ f(A) ∩ f(B)
-/
theorem image_inter_subset
    (f : X → Y)
    (A B : Set X) :
    f '' (A ∩ B) ⊆ (f '' A) ∩ (f '' B) := by
  intro y hy

  rcases hy with ⟨x, hxAB, rfl⟩

  have hxA : x ∈ A := hxAB.1
  have hxB : x ∈ B := hxAB.2

  constructor

  · exact ⟨x, hxA, rfl⟩

  · exact ⟨x, hxB, rfl⟩


/--
2. The difference of the images is contained
in the image of the difference:

    f(A) \ f(B) ⊆ f(A \ B)
-/
theorem image_diff_subset
    (f : X → Y)
    (A B : Set X) :
    (f '' A) \ (f '' B) ⊆ f '' (A \ B) := by
  intro y hy

  have hyA : y ∈ f '' A := hy.1
  have hyNotB : y ∉ f '' B := hy.2

  rcases hyA with ⟨x, hxA, hfx⟩

  have hxNotB : x ∉ B := by
    intro hxB

    apply hyNotB

    exact ⟨x, hxB, hfx⟩

  refine ⟨x, ?_, hfx⟩

  exact ⟨hxA, hxNotB⟩


/--
3. Images preserve unions exactly:

    f(A ∪ B) = f(A) ∪ f(B)
-/
theorem image_union
    (f : X → Y)
    (A B : Set X) :
    f '' (A ∪ B) = (f '' A) ∪ (f '' B) := by
  ext y
  constructor

  /-
  f(A ∪ B) ⊆ f(A) ∪ f(B)
  -/
  · intro hy

    rcases hy with ⟨x, hx, rfl⟩

    rcases hx with hxA | hxB

    · left
      exact ⟨x, hxA, rfl⟩

    · right
      exact ⟨x, hxB, rfl⟩

  /-
  f(A) ∪ f(B) ⊆ f(A ∪ B)
  -/
  · intro hy

    rcases hy with hyA | hyB

    · rcases hyA with ⟨x, hxA, rfl⟩

      refine ⟨x, ?_, rfl⟩

      exact Or.inl hxA

    · rcases hyB with ⟨x, hxB, rfl⟩

      refine ⟨x, ?_, rfl⟩

      exact Or.inr hxB


/--
Exercise 3.4.3 — the three general results.
-/
theorem exercise_3_4_3
    (f : X → Y)
    (A B : Set X) :
    f '' (A ∩ B) ⊆ (f '' A) ∩ (f '' B)
    ∧
    (f '' A) \ (f '' B) ⊆ f '' (A \ B)
    ∧
    f '' (A ∪ B) = (f '' A) ∪ (f '' B) := by
  constructor

  · exact image_inter_subset f A B

  · constructor
    · exact image_diff_subset f A B
    · exact image_union f A B

end TaoExercise3_4_3
