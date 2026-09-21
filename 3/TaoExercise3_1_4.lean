import Mathlib

namespace TaoExercise3_1_4

open Set

variable {α : Type*}

/--
(a) If A ⊆ B and B ⊆ A, then B = A.
-/
theorem subsets_antisymmetric
    (A B : Set α)
    (hAB : A ⊆ B)
    (hBA : B ⊆ A) :
    B = A := by
  ext x
  constructor
  · intro hx
    exact hBA hx
  · intro hx
    exact hAB hx


/--
(b) If A ⊂ B and B ⊂ C, then A ⊂ C.
-/
theorem strictSubset_trans
    (A B C : Set α)
    (hAB : A ⊂ B)
    (hBC : B ⊂ C) :
    A ⊂ C := by

  constructor

  /-
  First prove A ⊆ C.
  -/
  · intro x hxA

    have hxB : x ∈ B := by
      exact hAB.1 hxA

    have hxC : x ∈ C := by
      exact hBC.1 hxB

    exact hxC

  /-
  Now prove ¬ C ⊆ A.

  Suppose C ⊆ A. Since B ⊆ C,
  this would imply B ⊆ A, contradicting
  the strictness of A ⊂ B.
  -/
  · intro hCA

    have hBA : B ⊆ A := by
      intro x hxB

      have hxC : x ∈ C := by
        exact hBC.1 hxB

      exact hCA hxC

    exact hAB.2 hBA

end TaoExercise3_1_4
