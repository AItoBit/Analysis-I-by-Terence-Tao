import Mathlib

namespace TaoExercise2_3_3

/--
Exercise 2.3.3

Multiplication of natural numbers is associative:

    (a * b) * c = a * (b * c)

The proof proceeds by induction on `c`.
-/
theorem multiplication_associative (a b c : ℕ) :
    (a * b) * c = a * (b * c) := by

  induction c with

  /-
  Base case: c = 0.

  (a * b) * 0 = 0
  a * (b * 0) = a * 0 = 0
  -/
  | zero =>
      simp

  /-
  Inductive step.

  Assume:
      (a * b) * c = a * (b * c)

  Prove:
      (a * b) * succ c = a * (b * succ c)
  -/
  | succ c ih =>
      calc
        (a * b) * Nat.succ c
            = (a * b) * c + (a * b) := by
                rw [Nat.mul_succ]

        _ = a * (b * c) + a * b := by
              rw [ih]

        _ = a * (b * c + b) := by
              rw [Nat.mul_add]

        _ = a * (b * Nat.succ c) := by
              rw [Nat.mul_succ]

end TaoExercise2_3_3
