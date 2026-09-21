import Mathlib

namespace TaoExercise2_2_6

/--
Exercise 2.2.6 — Backwards induction.

Let `P` be a property of natural numbers such that
`P (m + 1) → P m` for every `m`.

If `P n` holds, then `P m` holds for every `m ≤ n`.
-/
theorem backwards_induction
    (P : ℕ → Prop)
    (hstep : ∀ m : ℕ, P (Nat.succ m) → P m) :
    ∀ n : ℕ, P n → ∀ m : ℕ, m ≤ n → P m := by

  intro n

  induction n with

  /-
  Base case: n = 0.

  If m ≤ 0, then necessarily m = 0.
  -/
  | zero =>
      intro hP0
      intro m hm

      have hm0 : m = 0 := by
        exact Nat.eq_zero_of_le_zero hm

      subst m
      exact hP0

  /-
  Inductive step:
  Assume the result for n and prove it for succ n.
  -/
  | succ n ih =>
      intro hPsucc
      intro m hm

      /-
      From P(succ n), backwards induction step gives P(n).
      -/
      have hPn : P n := by
        exact hstep n hPsucc

      /-
      If m ≤ succ n, then either
        m = succ n
      or
        m ≤ n.
      -/
      rcases Nat.eq_or_lt_of_le hm with hEq | hLt

      /-
      Case m = succ n:
      use the given hypothesis directly.
      -/
      · subst m
        exact hPsucc

      /-
      Case m < succ n:
      equivalently m ≤ n.
      Then use the induction hypothesis.
      -/
      · have hmn : m ≤ n := by
          exact Nat.le_of_lt_succ hLt

        exact ih hPn m hmn

end TaoExercise2_2_6
