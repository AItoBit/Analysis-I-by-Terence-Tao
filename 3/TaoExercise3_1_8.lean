import Mathlib

namespace TaoExercise3_1_8

open Set

variable {α : Type*}

/--
First absorption law:

A ∩ (A ∪ B) = A
-/
theorem absorption_inter_union (A B : Set α) :
    A ∩ (A ∪ B) = A := by
  ext x
  constructor

  /-
  If x ∈ A ∩ (A ∪ B), then x ∈ A.
  -/
  · intro hx
    exact hx.1

  /-
  If x ∈ A, then x ∈ A ∩ (A ∪ B).
  -/
  · intro hxA
    constructor
    · exact hxA
    · exact Or.inl hxA


/--
Second absorption law:

A ∪ (A ∩ B) = A
-/
theorem absorption_union_inter (A B : Set α) :
    A ∪ (A ∩ B) = A := by
  ext x
  constructor

  /-
  If x ∈ A ∪ (A ∩ B), then x ∈ A.
  -/
  · intro hx
    rcases hx with hxA | hxInter
    · exact hxA
    · exact hxInter.1

  /-
  If x ∈ A, then x ∈ A ∪ (A ∩ B).
  -/
  · intro hxA
    exact Or.inl hxA


/--
Exercise 3.1.8:
the two absorption laws.
-/
theorem exercise_3_1_8 (A B : Set α) :
    A ∩ (A ∪ B) = A
    ∧ A ∪ (A ∩ B) = A := by
  constructor
  · exact absorption_inter_union A B
  · exact absorption_union_inter A B

end TaoExercise3_1_8
