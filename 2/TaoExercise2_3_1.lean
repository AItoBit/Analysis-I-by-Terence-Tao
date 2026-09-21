import Mathlib

namespace TaoExercise2_3_1

/--
Lemma 1:
For every natural number n, n * 0 = 0.
-/
lemma mul_zero_tao (n : ℕ) :
    n * 0 = 0 := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [Nat.succ_mul, ih]


/--
Lemma 2:
For all natural numbers m and n,

m * succ n = m * n + m.
-/
lemma mul_succ_tao (m n : ℕ) :
    m * Nat.succ n = m * n + m := by
  induction m with
  | zero =>
      simp

  | succ m ih =>
      calc
        Nat.succ m * Nat.succ n
            = m * Nat.succ n + Nat.succ n := by
                rw [Nat.succ_mul]
        _ = (m * n + m) + Nat.succ n := by
              rw [ih]
        _ = (m * n + n) + Nat.succ m := by
              omega
        _ = Nat.succ m * n + Nat.succ m := by
              rw [Nat.succ_mul]


/--
Exercise 2.3.1:
Multiplication on natural numbers is commutative.
-/
theorem multiplication_commutative (n m : ℕ) :
    n * m = m * n := by
  induction n with

  /-
  Base case:
  0 * m = m * 0 = 0.
  -/
  | zero =>
      calc
        0 * m = 0 := by simp
        _ = m * 0 := by
              symm
              exact mul_zero_tao m

  /-
  Inductive step:
  Assume n * m = m * n.
  Show succ n * m = m * succ n.
  -/
  | succ n ih =>
      calc
        Nat.succ n * m
            = n * m + m := by
                rw [Nat.succ_mul]
        _ = m * n + m := by
              rw [ih]
        _ = m * Nat.succ n := by
              symm
              exact mul_succ_tao m n

end TaoExercise2_3_1
