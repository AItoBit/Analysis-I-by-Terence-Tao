import Mathlib

namespace TaoExercise9_1_14

open Set
open scoped BigOperators

/-!
============================================================
Tao-style boundedness
============================================================
-/

def IsBoundedSet (X : Set ℝ) : Prop :=
  ∃ M : ℝ,
    0 < M ∧
    ∀ x : ℝ, x ∈ X →
      -M ≤ x ∧ x ≤ M


/-!
============================================================
Finite subsets of ℝ are closed
============================================================
-/

theorem finite_set_closed
    (X : Set ℝ)
    (hX : X.Finite) :
    IsClosed X := by

  exact hX.isClosed


/-!
============================================================
Finite subsets of ℝ are bounded
============================================================
-/

theorem finite_set_bounded
    (X : Set ℝ)
    (hX : X.Finite) :
    IsBoundedSet X := by
  classical

  letI : Finite X := hX
  letI : Fintype X := Fintype.ofFinite X

  let S : ℝ :=
    ∑ y : X, |(y.1 : ℝ)|

  let M : ℝ :=
    S + 1

  have hSnonneg :
      0 ≤ S := by
    dsimp [S]

    exact Finset.sum_nonneg
      (fun y _ => abs_nonneg (y.1 : ℝ))

  have hMpos :
      0 < M := by
    dsimp [M]
    linarith

  refine ⟨M, hMpos, ?_⟩

  intro x hx

  let x' : X :=
    ⟨x, hx⟩

  have hxleS :
      |x| ≤ S := by
    dsimp [S]

    have hnonneg :
        ∀ y ∈ (Finset.univ : Finset X),
          0 ≤ |(y.1 : ℝ)| := by
      intro y hy
      exact abs_nonneg (y.1 : ℝ)

    have hxmem :
        x' ∈ (Finset.univ : Finset X) := by
      exact Finset.mem_univ x'

    exact Finset.single_le_sum
      hnonneg
      hxmem

  have hxleM :
      |x| ≤ M := by
    dsimp [M]
    linarith

  have hxBounds :
      -M ≤ x ∧ x ≤ M := by
    exact abs_le.mp hxleM

  exact hxBounds


/-!
============================================================
Exercise 9.1.14
============================================================
-/

theorem exercise_9_1_14
    (X : Set ℝ)
    (hX : X.Finite) :
    IsClosed X ∧ IsBoundedSet X := by

  constructor

  · exact finite_set_closed
      X
      hX

  · exact finite_set_bounded
      X
      hX

end TaoExercise9_1_14
