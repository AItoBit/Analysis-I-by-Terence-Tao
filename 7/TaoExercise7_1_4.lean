import Mathlib

namespace TaoExercise7_1_4

/-!
============================================================
Factorial
============================================================
-/

/--
Tao's recursive definition of factorial:

    0! = 1
    (n + 1)! = n! * (n + 1)
-/
def taoFactorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => taoFactorial n * (n + 1)


@[simp]
theorem taoFactorial_zero :
    taoFactorial 0 = 1 := by
  rfl


@[simp]
theorem taoFactorial_succ
    (n : ℕ) :
    taoFactorial (n + 1)
      =
    taoFactorial n * (n + 1) := by
  rfl


/-!
============================================================
Our factorial agrees with Mathlib's factorial
============================================================
-/

theorem taoFactorial_eq_natFactorial
    (n : ℕ) :
    taoFactorial n = Nat.factorial n := by

  induction n with

  | zero =>
      rfl

  | succ n ih =>

      rw [taoFactorial_succ]
      rw [ih]

      rw [Nat.factorial_succ]

      simp [Nat.succ_eq_add_one, mul_comm]


/-!
============================================================
Binomial coefficient written using factorials
============================================================
-/

/--
The real-valued coefficient

           n!
    ----------------
    j! (n - j)!
-/
noncomputable def factorialBinom
    (n j : ℕ) : ℝ :=
  (taoFactorial n : ℝ)
    /
  ((taoFactorial j : ℝ)
    *
   (taoFactorial (n - j) : ℝ))


/-!
For j ≤ n, the factorial expression is exactly
the usual binomial coefficient.
-/

theorem factorialBinom_eq_choose
    (n j : ℕ)
    (hj : j ≤ n) :
    factorialBinom n j
      =
    (n.choose j : ℝ) := by

  unfold factorialBinom

  rw [
    taoFactorial_eq_natFactorial n,
    taoFactorial_eq_natFactorial j,
    taoFactorial_eq_natFactorial (n - j)
  ]

  exact (Nat.cast_choose ℝ hj).symm


/-!
============================================================
Binomial theorem in choose notation

Mathlib's binomial theorem is

 (x+y)^n =
 Σ_{j=0}^n x^j y^(n-j) * choose(n,j).
============================================================
-/

theorem binomial_choose
    (x y : ℝ)
    (n : ℕ) :
    (x + y) ^ n
      =
    (Finset.range (n + 1)).sum
      (fun j : ℕ =>
        x ^ j
          * y ^ (n - j)
          * (n.choose j : ℝ)) := by

  exact add_pow x y n


/-!
============================================================
Binomial theorem using Tao's factorial notation
============================================================
-/

theorem binomial_formula
    (x y : ℝ)
    (n : ℕ) :
    (x + y) ^ n
      =
    (Finset.range (n + 1)).sum
      (fun j : ℕ =>
        factorialBinom n j
          * x ^ j
          * y ^ (n - j)) := by

  calc
    (x + y) ^ n
        =
      (Finset.range (n + 1)).sum
        (fun j : ℕ =>
          x ^ j
            * y ^ (n - j)
            * (n.choose j : ℝ)) := by

          exact binomial_choose x y n

    _ =
      (Finset.range (n + 1)).sum
        (fun j : ℕ =>
          factorialBinom n j
            * x ^ j
            * y ^ (n - j)) := by

          apply Finset.sum_congr rfl

          intro j hj

          have hjlt :
              j < n + 1 := by
            exact Finset.mem_range.mp hj

          have hjle :
              j ≤ n := by
            omega

          rw [factorialBinom_eq_choose n j hjle]

          ring


/-!
============================================================
Exercise 7.1.4

This is the statement written explicitly as

            n!
    ------------------- x^j y^(n-j).
    j! (n-j)!
============================================================
-/

theorem exercise_7_1_4
    (x y : ℝ)
    (n : ℕ) :
    (x + y) ^ n
      =
    (Finset.range (n + 1)).sum
      (fun j : ℕ =>
        (
          (taoFactorial n : ℝ)
            /
          (
            (taoFactorial j : ℝ)
              *
            (taoFactorial (n - j) : ℝ)
          )
        )
        * x ^ j
        * y ^ (n - j)) := by

  exact binomial_formula x y n

end TaoExercise7_1_4
