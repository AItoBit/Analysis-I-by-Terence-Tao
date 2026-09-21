import Mathlib

namespace TaoExercise2_3_2

/--
If n and m are both positive natural numbers,
then their product is positive.
-/
theorem mul_pos_of_pos
    (n m : ℕ)
    (hn : 0 < n)
    (hm : 0 < m) :
    0 < n * m := by

  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)

  simp [Nat.succ_mul]


/--
Exercise 2.3.2:
Natural numbers have no zero divisors.

n * m = 0 iff n = 0 or m = 0.
-/
theorem no_zero_divisors (n m : ℕ) :
    n * m = 0 ↔ n = 0 ∨ m = 0 := by
  constructor

  /-
  Left-to-right:
  if n * m = 0, then one of n or m must be zero.
  -/
  · intro hnm

    by_cases hn : n = 0

    · exact Or.inl hn

    · right

      by_contra hm

      have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hmpos : 0 < m := Nat.pos_of_ne_zero hm

      have hpos : 0 < n * m :=
        mul_pos_of_pos n m hnpos hmpos

      rw [hnm] at hpos
      exact Nat.lt_irrefl 0 hpos

  /-
  Right-to-left:
  if n = 0 or m = 0, then n * m = 0.
  -/
  · intro h

    rcases h with hn | hm

    · subst n
      simp

    · subst m
      simp

end TaoExercise2_3_2
