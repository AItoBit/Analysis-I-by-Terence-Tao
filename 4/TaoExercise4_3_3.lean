import Mathlib

namespace TaoExercise4_3_3

/-!
(a)

x^n * x^m = x^(n+m)
-/
theorem pow_add_rule
    (x : ℚ)
    (n m : ℕ) :
    x ^ n * x ^ m = x ^ (n + m) := by
  exact (pow_add x n m).symm


/-!
(b)

(xy)^n = x^n y^n
-/
theorem mul_pow_rule
    (x y : ℚ)
    (n : ℕ) :
    (x * y) ^ n = x ^ n * y ^ n := by
  exact mul_pow x y n


/-!
(c)

(x^n)^m = x^(nm)
-/
theorem pow_pow_rule
    (x : ℚ)
    (n m : ℕ) :
    (x ^ n) ^ m = x ^ (n * m) := by
  exact (pow_mul x n m).symm


/-!
Auxiliary zero-product lemma.
-/
theorem rat_mul_eq_zero
    (x y : ℚ)
    (h : x * y = 0) :
    x = 0 ∨ y = 0 := by
  exact mul_eq_zero.mp h


/-!
(d)

If n > 0, then

    x^n = 0 ↔ x = 0.
-/

theorem pow_eq_zero_iff_raw
    (x : ℚ)
    (n : ℕ)
    (hn : 0 < n) :
    x ^ n = 0 ↔ x = 0 := by

  induction n with

  /-
  Impossible base case because hn : 0 < 0.
  -/
  | zero =>
      omega

  | succ n ih =>
      constructor

      /-
      If x^(n+1) = 0, then x = 0.
      -/
      · intro h

        rw [pow_succ] at h

        rcases mul_eq_zero.mp h with hpow | hx

        · by_cases hn0 : n = 0

          /-
          n = 0, so x^0 = 1, impossible.
          -/
          · subst hn0
            simp at hpow

          /-
          n > 0, so use the induction hypothesis.
          -/
          · have hnpos : 0 < n :=
              Nat.pos_of_ne_zero hn0

            exact (ih hnpos).mp hpow

        · exact hx

      /-
      If x = 0, then x^(n+1) = 0.
      -/
      · intro hx
        subst hx
        simp


/-!
Equivalent version using n ≠ 0.
-/

theorem pow_eq_zero_iff_ne_zero
    (x : ℚ)
    (n : ℕ)
    (hn : n ≠ 0) :
    x ^ n = 0 ↔ x = 0 := by

  have hnpos : 0 < n :=
    Nat.pos_of_ne_zero hn

  exact pow_eq_zero_iff_raw x n hnpos


/-!
(e)

If

    x ≥ y ≥ 0,

then

    x^n ≥ y^n ≥ 0.
-/

theorem pow_monotone_nonnegative
    (x y : ℚ)
    (n : ℕ)
    (hxy : y ≤ x)
    (hy : 0 ≤ y) :
    y ^ n ≤ x ^ n ∧ 0 ≤ y ^ n := by

  constructor

  · exact pow_le_pow_left₀ hy hxy n

  · exact pow_nonneg hy n


/--
Same result in Tao's order:

    x^n ≥ y^n ≥ 0.
-/
theorem pow_order_chain
    (x y : ℚ)
    (n : ℕ)
    (hxy : x ≥ y)
    (hy : y ≥ 0) :
    x ^ n ≥ y ^ n ∧ y ^ n ≥ 0 := by

  constructor

  · exact pow_le_pow_left₀ hy hxy n

  · exact pow_nonneg hy n


/-!
(f)

|x^n| = |x|^n.
-/

/-
Important: do not call this theorem `abs_pow`,
because Mathlib already has a theorem with that name.
-/
theorem abs_pow_rule
    (x : ℚ)
    (n : ℕ) :
    |x ^ n| = |x| ^ n := by
  exact abs_pow x n


/-!
Proposition 4.3.10 packaged together.
-/

theorem proposition_4_3_10
    (x y : ℚ)
    (n m : ℕ)
    (hn : 0 < n)
    (hxy : y ≤ x)
    (hy : 0 ≤ y) :
    (x ^ n * x ^ m = x ^ (n + m))
    ∧
    ((x * y) ^ n = x ^ n * y ^ n)
    ∧
    ((x ^ n) ^ m = x ^ (n * m))
    ∧
    (x ^ n = 0 ↔ x = 0)
    ∧
    (y ^ n ≤ x ^ n ∧ 0 ≤ y ^ n)
    ∧
    (|x ^ n| = |x| ^ n) := by

  constructor

  · exact pow_add_rule x n m

  constructor

  · exact mul_pow_rule x y n

  constructor

  · exact pow_pow_rule x n m

  constructor

  · exact pow_eq_zero_iff_raw x n hn

  constructor

  · exact pow_monotone_nonnegative x y n hxy hy

  · exact abs_pow_rule x n

end TaoExercise4_3_3
