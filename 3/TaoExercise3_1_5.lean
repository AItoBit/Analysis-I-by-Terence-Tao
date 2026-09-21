import Mathlib

namespace TaoExercise3_1_5

open Set

variable {α : Type*}

/--
Exercise 3.1.5

For sets A and B, the following are equivalent:

1. A ⊆ B
2. A ∪ B = B
3. A ∩ B = A
-/
theorem exercise_3_1_5 (A B : Set α) :
    A ⊆ B ↔ A ∪ B = B ∧ A ∩ B = A := by
  constructor

  /-
  A ⊆ B → both equalities.
  -/
  · intro hAB

    constructor

    /-
    A ∪ B = B.
    -/
    · ext x
      constructor
      · intro hx
        rcases hx with hxA | hxB
        · exact hAB hxA
        · exact hxB
      · intro hxB
        exact Or.inr hxB

    /-
    A ∩ B = A.
    -/
    · ext x
      constructor
      · intro hx
        exact hx.1
      · intro hxA
        exact ⟨hxA, hAB hxA⟩

  /-
  From the equalities, recover A ⊆ B.
  -/
  · rintro ⟨hUnion, hInter⟩

    intro x hxA

    have hxInter : x ∈ A ∩ B := by
      rw [hInter]
      exact hxA

    exact hxInter.2

end TaoExercise3_1_5
