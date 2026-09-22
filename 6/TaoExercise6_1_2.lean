import Mathlib

namespace TaoExercise6_1_2

/--
A sequence `a` converges to `L` starting from index `m`
if for every ε > 0 there exists `N ≥ m` such that
for all `n ≥ N`, we have

    |a n - L| ≤ ε.
-/
def ConvergesFrom
    (a : ℕ → ℝ)
    (m : ℕ)
    (L : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ,
      m ≤ N ∧
      ∀ n : ℕ,
        N ≤ n →
        |a n - L| ≤ ε


/--
Exercise 6.1.2.

`a_n` converges to `L` from index `m` iff
for every ε > 0 there is an `N ≥ m` such that
all later terms satisfy `|a_n - L| ≤ ε`.
-/
theorem exercise_6_1_2
    (a : ℕ → ℝ)
    (m : ℕ)
    (L : ℝ) :
    ConvergesFrom a m L ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ,
          m ≤ N ∧
          ∀ n : ℕ,
            N ≤ n →
            |a n - L| ≤ ε := by

  constructor

  /-
  Forward direction.
  -/
  · intro hconv
    exact hconv

  /-
  Reverse direction.
  -/
  · intro h
    exact h

end TaoExercise6_1_2
