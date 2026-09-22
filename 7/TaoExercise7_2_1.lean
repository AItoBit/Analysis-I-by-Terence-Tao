import Mathlib

namespace TaoExercise7_2_1

/-!
============================================================
Convergence
============================================================
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


/-!
============================================================
Partial sums of Σ (-1)^n
============================================================

We define

    S_0 = 0
    S_(N+1) = S_N + (-1)^(N+1).

Thus

    S_N = Σ_{n=1}^N (-1)^n.
-/

def partialSum : ℕ → ℝ
  | 0 => 0
  | N + 1 =>
      partialSum N + (-1 : ℝ) ^ (N + 1)


@[simp]
theorem partialSum_zero :
    partialSum 0 = 0 := by
  rfl


@[simp]
theorem partialSum_succ
    (N : ℕ) :
    partialSum (N + 1)
      =
    partialSum N + (-1 : ℝ) ^ (N + 1) := by
  rfl


/-!
============================================================
Closed formula for the partial sums
============================================================
-/

theorem partialSum_formula
    (N : ℕ) :
    partialSum N
      =
    (((-1 : ℝ) ^ N) - 1) / 2 := by

  induction N with

  | zero =>
      norm_num [partialSum]

  | succ N ih =>

      rw [partialSum_succ, ih]

      rw [pow_succ]

      ring


/-!
============================================================
Powers of -1
============================================================
-/

theorem neg_one_pow_even
    (k : ℕ) :
    (-1 : ℝ) ^ (2 * k) = 1 := by

  rw [pow_mul]

  norm_num


theorem neg_one_pow_odd
    (k : ℕ) :
    (-1 : ℝ) ^ (2 * k + 1) = -1 := by

  rw [pow_add]

  rw [neg_one_pow_even]

  norm_num


/-!
============================================================
Even and odd partial sums
============================================================
-/

theorem partialSum_even
    (k : ℕ) :
    partialSum (2 * k) = 0 := by

  rw [partialSum_formula]

  rw [neg_one_pow_even]

  norm_num


theorem partialSum_odd
    (k : ℕ) :
    partialSum (2 * k + 1) = -1 := by

  rw [partialSum_formula]

  rw [neg_one_pow_odd]

  norm_num


/-!
============================================================
The partial-sum sequence cannot converge
============================================================
-/

theorem partialSum_diverges :
    ¬ ∃ L : ℝ,
      ConvergesFrom partialSum 1 L := by

  rintro ⟨L, hconv⟩

  /-
  Use ε = 1/4.
  -/
  have hquarter :
      (0 : ℝ) < 1 / 4 := by
    norm_num

  obtain ⟨N, h1N, hN⟩ :=
    hconv (1 / 4) hquarter

  /-
  Choose one sufficiently large even index
  and the following odd index.
  -/
  let k : ℕ := N + 1

  let E : ℕ := 2 * k

  let O : ℕ := 2 * k + 1

  have hNE :
      N ≤ E := by
    dsimp [E, k]
    omega

  have hNO :
      N ≤ O := by
    dsimp [O, k]
    omega

  have hEvenClose :
      |partialSum E - L| ≤ (1 : ℝ) / 4 := by
    exact hN E hNE

  have hOddClose :
      |partialSum O - L| ≤ (1 : ℝ) / 4 := by
    exact hN O hNO

  have hEzero :
      partialSum E = 0 := by
    dsimp [E]
    exact partialSum_even k

  have hOminus :
      partialSum O = -1 := by
    dsimp [O]
    exact partialSum_odd k

  rw [hEzero] at hEvenClose
  rw [hOminus] at hOddClose

  have hEvenBounds :=
    abs_le.mp hEvenClose

  have hOddBounds :=
    abs_le.mp hOddClose

  linarith [
    hEvenBounds.1,
    hEvenBounds.2,
    hOddBounds.1,
    hOddBounds.2
  ]


/-!
============================================================
Definition of convergence of this infinite series
============================================================
-/

def AlternatingSeriesConverges : Prop :=
  ∃ L : ℝ,
    ConvergesFrom partialSum 1 L


/-!
============================================================
Exercise 7.2.1
============================================================
-/

theorem exercise_7_2_1 :
    ¬ AlternatingSeriesConverges := by

  unfold AlternatingSeriesConverges

  exact partialSum_diverges

end TaoExercise7_2_1
