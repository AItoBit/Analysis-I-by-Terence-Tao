import Mathlib

namespace TaoExercise9_1_4

open Set

def X : Set ℝ :=
  Set.Ioo (1 : ℝ) (2 : ℝ)

def Y : Set ℝ :=
  Set.Ioo (2 : ℝ) (3 : ℝ)


theorem closure_X :
    closure X = Set.Icc (1 : ℝ) (2 : ℝ) := by
  unfold X
  exact
    closure_Ioo
      (α := ℝ)
      (a := (1 : ℝ))
      (b := (2 : ℝ))
      (by norm_num)


theorem closure_Y :
    closure Y = Set.Icc (2 : ℝ) (3 : ℝ) := by
  unfold Y
  exact
    closure_Ioo
      (α := ℝ)
      (a := (2 : ℝ))
      (b := (3 : ℝ))
      (by norm_num)


theorem inter_XY_empty :
    X ∩ Y = ∅ := by
  ext x

  constructor

  · intro hx

    have hxlt :
        x < (2 : ℝ) := by
      exact hx.1.2

    have hxgt :
        (2 : ℝ) < x := by
      exact hx.2.1

    linarith

  · intro hx

    simpa using hx


theorem closure_inter_XY :
    closure (X ∩ Y) = ∅ := by
  rw [inter_XY_empty]
  exact closure_empty


theorem two_mem_closure_X :
    (2 : ℝ) ∈ closure X := by
  rw [closure_X]

  constructor

  · norm_num

  · norm_num


theorem two_mem_closure_Y :
    (2 : ℝ) ∈ closure Y := by
  rw [closure_Y]

  constructor

  · norm_num

  · norm_num


theorem two_mem_inter_closures :
    (2 : ℝ) ∈ closure X ∩ closure Y := by
  constructor

  · exact two_mem_closure_X

  · exact two_mem_closure_Y


theorem two_not_mem_closure_inter :
    (2 : ℝ) ∉ closure (X ∩ Y) := by
  rw [closure_inter_XY]
  simp


theorem exercise_9_1_4 :
    closure (X ∩ Y) ≠ closure X ∩ closure Y := by

  intro hEq

  have h2 :
      (2 : ℝ) ∈ closure (X ∩ Y) := by
    rw [hEq]
    exact two_mem_inter_closures

  exact two_not_mem_closure_inter h2

end TaoExercise9_1_4
