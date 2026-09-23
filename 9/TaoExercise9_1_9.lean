import Mathlib

namespace TaoExercise9_1_9

open Set

/-!
============================================================
Definitions
============================================================
-/

/-- `x` is a limit point of `X` iff it is adherent to
    `X \ {x}`. -/
def IsLimitPoint
    (X : Set ℝ)
    (x : ℝ) : Prop :=
  x ∈ closure (X \ {x})


/-- `x` is an isolated point of `X` iff it belongs to `X`
    but is not a limit point of `X`. -/
def IsIsolatedPoint
    (X : Set ℝ)
    (x : ℝ) : Prop :=
  x ∈ X ∧
  x ∉ closure (X \ {x})


/-!
============================================================
Every limit point is adherent
============================================================
-/

theorem limitPoint_mem_closure
    (X : Set ℝ)
    (x : ℝ)
    (hx : IsLimitPoint X x) :
    x ∈ closure X := by

  unfold IsLimitPoint at hx

  have hsub :
      X \ {x} ⊆ X := by
    intro y hy
    exact hy.1

  exact closure_mono hsub hx


/-!
============================================================
Every isolated point is adherent
============================================================
-/

theorem isolatedPoint_mem_closure
    (X : Set ℝ)
    (x : ℝ)
    (hx : IsIsolatedPoint X x) :
    x ∈ closure X := by

  unfold IsIsolatedPoint at hx

  exact subset_closure hx.1


/-!
============================================================
If x is adherent but not a limit point, then x ∈ X
============================================================
-/

theorem mem_of_mem_closure_not_limitPoint
    (X : Set ℝ)
    (x : ℝ)
    (hxClosure : x ∈ closure X)
    (hxNotLimit : ¬ IsLimitPoint X x) :
    x ∈ X := by

  by_contra hxNotX

  have hEq :
      X \ {x} = X := by

    ext y

    constructor

    · intro hy
      exact hy.1

    · intro hy

      constructor

      · exact hy

      · intro hySingleton

        have hyx :
            y = x := by
          simpa using hySingleton

        subst y

        exact hxNotX hy

  apply hxNotLimit

  unfold IsLimitPoint

  rw [hEq]

  exact hxClosure


/-!
============================================================
Every adherent point is either limit or isolated
============================================================
-/

theorem adherent_limit_or_isolated
    (X : Set ℝ)
    (x : ℝ)
    (hx : x ∈ closure X) :
    IsLimitPoint X x ∨ IsIsolatedPoint X x := by

  by_cases hlim :
      IsLimitPoint X x

  · left
    exact hlim

  · right

    unfold IsIsolatedPoint

    constructor

    · exact
        mem_of_mem_closure_not_limitPoint
          X
          x
          hx
          hlim

    · exact hlim


/-!
============================================================
A point cannot be both limit and isolated
============================================================
-/

theorem not_limit_and_isolated
    (X : Set ℝ)
    (x : ℝ) :
    ¬ (IsLimitPoint X x ∧ IsIsolatedPoint X x) := by

  intro h

  rcases h with ⟨hlim, hiso⟩

  exact hiso.2 hlim


/-!
============================================================
Equivalent exclusive-or formulation
============================================================
-/

theorem adherent_exactly_one
    (X : Set ℝ)
    (x : ℝ)
    (hx : x ∈ closure X) :
    (IsLimitPoint X x ∨ IsIsolatedPoint X x)
      ∧
    ¬ (IsLimitPoint X x ∧ IsIsolatedPoint X x) := by

  constructor

  · exact adherent_limit_or_isolated X x hx

  · exact not_limit_and_isolated X x


/-!
============================================================
Conversely, both kinds of points are adherent
============================================================
-/

theorem limit_or_isolated_mem_closure
    (X : Set ℝ)
    (x : ℝ)
    (hx :
      IsLimitPoint X x ∨
      IsIsolatedPoint X x) :
    x ∈ closure X := by

  rcases hx with hlim | hiso

  · exact limitPoint_mem_closure X x hlim

  · exact isolatedPoint_mem_closure X x hiso


/-!
============================================================
Lemma / Exercise 9.1.9
============================================================
-/

theorem exercise_9_1_9
    (X : Set ℝ)
    (x : ℝ) :
    (x ∈ closure X
      ↔
      IsLimitPoint X x ∨ IsIsolatedPoint X x)
    ∧
    ¬ (IsLimitPoint X x ∧ IsIsolatedPoint X x) := by

  constructor

  · constructor

    · intro hx
      exact adherent_limit_or_isolated X x hx

    · intro hx
      exact limit_or_isolated_mem_closure X x hx

  · exact not_limit_and_isolated X x

end TaoExercise9_1_9
