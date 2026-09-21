import Mathlib

namespace TaoExercise5_5_1

/--
The negation of a set `E`:

    -E = { -x | x ∈ E }.
-/
def NegSet (E : Set ℝ) : Set ℝ :=
  {z : ℝ | ∃ x : ℝ, x ∈ E ∧ z = -x}


/--
If `M` is the least upper bound of `E`,
then `-M` is the greatest lower bound of `-E`.
-/
theorem neg_lub_is_glb
    (E : Set ℝ)
    (M : ℝ)
    (hM : IsLUB E M) :
    IsGLB (NegSet E) (-M) := by

  /-
  hM.1:
      M is an upper bound for E.

  hM.2:
      M is less than or equal to every upper bound of E.
  -/

  constructor

  /-
  First prove that -M is a lower bound of -E.
  -/
  · intro z hz

    obtain ⟨x, hxE, rfl⟩ := hz

    have hxM :
        x ≤ M := by
      exact hM.1 hxE

    linarith

  /-
  Now prove that -M is the greatest lower bound.

  Let A be any lower bound of -E.
  We must prove

      A ≤ -M.
  -/
  · intro A hA

    /-
    We show that -A is an upper bound of E.
    -/
    have hNegAUpper :
        -A ∈ upperBounds E := by

      intro x hxE

      /-
      Since x ∈ E, we have -x ∈ -E.
      -/
      have hnegx :
          -x ∈ NegSet E := by
        exact ⟨x, hxE, rfl⟩

      /-
      Since A is a lower bound of -E,

          A ≤ -x.
      -/
      have hAle :
          A ≤ -x := by
        exact hA hnegx

      /-
      Therefore

          x ≤ -A.
      -/
      linarith

    /-
    Since M is the least upper bound of E
    and -A is an upper bound,

        M ≤ -A.
    -/
    have hMle :
        M ≤ -A := by
      exact hM.2 hNegAUpper

    /-
    Hence

        A ≤ -M.
    -/
    linarith


/--
Exercise 5.5.1.
-/
theorem exercise_5_5_1
    (E : Set ℝ)
    (M : ℝ)
    (hM : IsLUB E M) :
    IsGLB (NegSet E) (-M) := by

  exact neg_lub_is_glb E M hM

end TaoExercise5_5_1
