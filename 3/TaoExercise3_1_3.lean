import Mathlib

namespace TaoExercise3_1_3

open Set

variable {α : Type*}

/-- (a) {a,b} = {a} ∪ {b} -/
theorem pair_eq_union_singletons (a b : α) :
    ({a, b} : Set α) = ({a} : Set α) ∪ ({b} : Set α) := by
  ext x
  simp [or_comm]


/-- (b) A ∪ B = B ∪ A -/
theorem union_commutative (A B : Set α) :
    A ∪ B = B ∪ A := by
  ext x
  constructor
  · intro hx
    rcases hx with hxA | hxB
    · exact Or.inr hxA
    · exact Or.inl hxB
  · intro hx
    rcases hx with hxB | hxA
    · exact Or.inr hxB
    · exact Or.inl hxA


/-- (c1) A ∪ ∅ = A -/
theorem union_empty_right (A : Set α) :
    A ∪ ∅ = A := by
  ext x
  constructor
  · intro hx
    rcases hx with hxA | hxEmpty
    · exact hxA
    · exact False.elim hxEmpty
  · intro hx
    exact Or.inl hx


/-- (c2) ∅ ∪ A = A -/
theorem union_empty_left (A : Set α) :
    ∅ ∪ A = A := by
  calc
    ∅ ∪ A = A ∪ ∅ := by
      exact union_commutative ∅ A
    _ = A := by
      exact union_empty_right A


/-- Exercise 3.1.3 -/
theorem exercise_3_1_3
    (a b : α)
    (A B : Set α) :
    (({a, b} : Set α) = ({a} : Set α) ∪ ({b} : Set α))
    ∧ (A ∪ B = B ∪ A)
    ∧ (A ∪ ∅ = A)
    ∧ (∅ ∪ A = A) := by
  exact
    ⟨pair_eq_union_singletons a b,
     union_commutative A B,
     union_empty_right A,
     union_empty_left A⟩

end TaoExercise3_1_3
