import Mathlib

namespace TaoExercise3_1_9

open Set

variable {α : Type*}

/--
Exercise 3.1.9.

If

    A ∪ B = X
    A ∩ B = ∅

then

    A = X \ B
    B = X \ A.
-/
theorem exercise_3_1_9
    (A B X : Set α)
    (hUnion : A ∪ B = X)
    (hInter : A ∩ B = ∅) :
    A = X \ B ∧ B = X \ A := by

  constructor

  /-
  First prove A = X \ B.
  -/
  · ext x
    constructor

    /-
    If x ∈ A, then x ∈ X and x ∉ B.
    -/
    · intro hxA

      have hxX : x ∈ X := by
        rw [← hUnion]
        exact Or.inl hxA

      have hxNotB : x ∉ B := by
        intro hxB

        have hxInter : x ∈ A ∩ B := by
          exact ⟨hxA, hxB⟩

        rw [hInter] at hxInter
        exact hxInter

      exact ⟨hxX, hxNotB⟩

    /-
    If x ∈ X \ B, then x ∈ A.
    -/
    · intro hx

      have hxX : x ∈ X := hx.1
      have hxNotB : x ∉ B := hx.2

      have hxUnion : x ∈ A ∪ B := by
        rw [hUnion]
        exact hxX

      rcases hxUnion with hxA | hxB
      · exact hxA
      · exact False.elim (hxNotB hxB)

  /-
  Now prove B = X \ A.
  The argument is symmetric.
  -/
  · ext x
    constructor

    /-
    If x ∈ B, then x ∈ X and x ∉ A.
    -/
    · intro hxB

      have hxX : x ∈ X := by
        rw [← hUnion]
        exact Or.inr hxB

      have hxNotA : x ∉ A := by
        intro hxA

        have hxInter : x ∈ A ∩ B := by
          exact ⟨hxA, hxB⟩

        rw [hInter] at hxInter
        exact hxInter

      exact ⟨hxX, hxNotA⟩

    /-
    If x ∈ X \ A, then x ∈ B.
    -/
    · intro hx

      have hxX : x ∈ X := hx.1
      have hxNotA : x ∉ A := hx.2

      have hxUnion : x ∈ A ∪ B := by
        rw [hUnion]
        exact hxX

      rcases hxUnion with hxA | hxB
      · exact False.elim (hxNotA hxA)
      · exact hxB

end TaoExercise3_1_9
