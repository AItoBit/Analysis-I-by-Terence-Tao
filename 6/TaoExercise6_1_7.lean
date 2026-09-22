import Mathlib

namespace TaoExercise6_1_7

/--
Definition 5.1.12-style boundedness:
there exists a nonnegative rational bound.
-/
def IsBoundedByRational
    (a : ℕ → ℝ)
    (m : ℕ) : Prop :=
  ∃ M : ℚ,
    0 ≤ M ∧
    ∀ n : ℕ,
      m ≤ n →
      |a n| ≤ (M : ℝ)

/--
Definition 6.1.16-style boundedness:
there exists a positive real bound.
-/
def IsBoundedByReal
    (a : ℕ → ℝ)
    (m : ℕ) : Prop :=
  ∃ M : ℝ,
    0 < M ∧
    ∀ n : ℕ,
      m ≤ n →
      |a n| ≤ M


/--
Exercise 6.1.7.

The two notions of boundedness are equivalent.
-/
theorem exercise_6_1_7
    (a : ℕ → ℝ)
    (m : ℕ) :
    IsBoundedByRational a m ↔
    IsBoundedByReal a m := by

  constructor

  /-
  Rational bound -> real bound.
  -/
  · intro h

    obtain ⟨M, hMnonneg, hM⟩ := h

    /-
    Take M' = M + 1.
    -/
    refine ⟨(M : ℝ) + 1, ?_, ?_⟩

    · have hMnonnegR :
          (0 : ℝ) ≤ (M : ℝ) := by
        exact_mod_cast hMnonneg

      linarith

    · intro n hn

      have hbound :
          |a n| ≤ (M : ℝ) := by
        exact hM n hn

      linarith


  /-
  Real bound -> rational bound.
  -/
  · intro h

    obtain ⟨M, hMpos, hM⟩ := h

    /-
    By the Archimedean property, choose a natural number N
    strictly larger than M.
    -/
    obtain ⟨N : ℕ, hN⟩ := exists_nat_gt M

    /-
    Use the rational number N as the required rational bound.
    -/
    refine ⟨(N : ℚ), ?_, ?_⟩

    · positivity

    · intro n hn

      have hanM :
          |a n| ≤ M := by
        exact hM n hn

      have hMN :
          M ≤ (N : ℝ) := by
        exact le_of_lt hN

      have hanN :
          |a n| ≤ (N : ℝ) := by
        exact le_trans hanM hMN

      simpa using hanN

end TaoExercise6_1_7
