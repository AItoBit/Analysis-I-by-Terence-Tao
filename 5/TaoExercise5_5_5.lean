import Mathlib

namespace TaoExercise5_5_5

/--
A real number is irrational if it is not the cast
of any rational number.
-/
def IsIrrational (x : ℝ) : Prop :=
  ¬ ∃ q : ℚ, (q : ℝ) = x


/--
sqrt(2) is irrational.
-/
theorem sqrt_two_irrational :
    IsIrrational (Real.sqrt 2) := by
  unfold IsIrrational
  exact irrational_sqrt_two


/--
Exercise 5.5.5.

Between any two real numbers `x < y`,
there exists an irrational real number.
-/
theorem exercise_5_5_5
    (x y : ℝ)
    (hxy : x < y) :
    ∃ s : ℝ,
      x < s ∧
      s < y ∧
      IsIrrational s := by

  /-
  Shift the interval by sqrt(2).
  -/
  have hshift :
      x + Real.sqrt 2
        <
      y + Real.sqrt 2 := by
    linarith

  /-
  By density of Q in R, choose a rational q such that

      x + sqrt(2) < q < y + sqrt(2).
  -/
  obtain ⟨q, hqleft, hqright⟩ :=
    exists_rat_btwn hshift

  /-
  Define

      s = q - sqrt(2).
  -/
  let s : ℝ :=
    (q : ℝ) - Real.sqrt 2

  refine ⟨s, ?_, ?_, ?_⟩

  /-
  x < s.
  -/
  · dsimp [s]
    linarith

  /-
  s < y.
  -/
  · dsimp [s]
    linarith

  /-
  s is irrational.
  -/
  · unfold IsIrrational

    intro hs

    obtain ⟨q', hq'⟩ := hs

    /-
    hq' says

        q' = q - sqrt(2).

    Therefore

        sqrt(2) = q - q',

    which would make sqrt(2) rational.
    -/
    dsimp [s] at hq'

    have hsqrt :
        ((q - q' : ℚ) : ℝ)
          =
        Real.sqrt 2 := by

      push_cast

      linarith

    /-
    Contradict irrationality of sqrt(2).
    -/
    have hirr :
        IsIrrational (Real.sqrt 2) :=
      sqrt_two_irrational

    apply hirr

    exact ⟨q - q', hsqrt⟩

end TaoExercise5_5_5
