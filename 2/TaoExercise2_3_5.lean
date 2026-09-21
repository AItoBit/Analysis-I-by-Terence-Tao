import Mathlib

namespace TaoExercise2_3_5

/--
Exercise 2.3.5 — Euclidean algorithm.

Let `n` be a natural number and let `q` be positive.
Then there exist natural numbers `m, r` such that

    0 ≤ r < q

and

    n = m * q + r.
-/
theorem euclidean_algorithm
    (n q : ℕ)
    (hq : 0 < q) :
    ∃ m r : ℕ,
      0 ≤ r ∧
      r < q ∧
      n = m * q + r := by

  induction n with

  /-
  Base case: n = 0.

  Choose
      m = 0
      r = 0.
  -/
  | zero =>
      refine ⟨0, 0, Nat.zero_le 0, hq, ?_⟩
      simp

  /-
  Inductive step.

  Suppose

      n = m*q + r
      0 ≤ r < q.

  We must construct a quotient and remainder for succ n.
  -/
  | succ n ih =>

      obtain ⟨m, r, hr_nonneg, hr_lt, hn⟩ := ih

      /-
      Since r < q, we have r + 1 ≤ q.
      -/
      have hr_succ_le : r + 1 ≤ q := by
        omega

      /-
      There are two possibilities:

      1. r + 1 < q
      2. r + 1 = q
      -/
      by_cases hlt : r + 1 < q

      /-
      Case 1:

          r + 1 < q.

      Keep the quotient m and use remainder r + 1.
      -/
      · refine ⟨m, r + 1, Nat.zero_le _, hlt, ?_⟩

        calc
          Nat.succ n
              = Nat.succ (m * q + r) := by
                  rw [hn]

          _ = m * q + (r + 1) := by
                omega

      /-
      Case 2:

          r + 1 = q.

      Increase the quotient by 1 and reset
      the remainder to 0.
      -/
      · have heq : r + 1 = q := by
          omega

        refine ⟨m + 1, 0, Nat.zero_le 0, hq, ?_⟩

        calc
          Nat.succ n
              = Nat.succ (m * q + r) := by
                  rw [hn]

          _ = m * q + (r + 1) := by
                omega

          _ = m * q + q := by
                rw [heq]

          _ = (m + 1) * q + 0 := by
                simp [Nat.add_mul]

end TaoExercise2_3_5
