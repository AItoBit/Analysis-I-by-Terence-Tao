import Mathlib

namespace TaoExercise9_1_2

open Set

theorem subset_closure_self
    (X : Set ℝ) :
    X ⊆ closure X := by
  exact subset_closure


theorem closure_inter_subset
    (X Y : Set ℝ) :
    closure (X ∩ Y) ⊆
      closure X ∩ closure Y := by

  intro z hz

  constructor

  · have hsub :
        X ∩ Y ⊆ X := by
      intro x hx
      exact hx.1

    exact closure_mono hsub hz

  · have hsub :
        X ∩ Y ⊆ Y := by
      intro x hx
      exact hx.2

    exact closure_mono hsub hz


theorem closure_union_eq
    (X Y : Set ℝ) :
    closure (X ∪ Y) =
      closure X ∪ closure Y := by

  exact closure_union


theorem closure_mono_of_subset
    (X Y : Set ℝ)
    (hXY : X ⊆ Y) :
    closure X ⊆ closure Y := by

  exact closure_mono hXY


theorem lemma_9_1_11
    (X Y : Set ℝ) :
    (X ⊆ closure X)
      ∧
    (closure (X ∩ Y) ⊆ closure X ∩ closure Y)
      ∧
    (closure (X ∪ Y) = closure X ∪ closure Y)
      ∧
    (∀ Z : Set ℝ,
      X ⊆ Z →
      closure X ⊆ closure Z) := by

  constructor

  · exact subset_closure

  constructor

  · exact closure_inter_subset X Y

  constructor

  · exact closure_union

  · intro Z hXZ

    exact closure_mono hXZ

end TaoExercise9_1_2
