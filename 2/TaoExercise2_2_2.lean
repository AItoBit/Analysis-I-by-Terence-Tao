import Mathlib

namespace TaoExercise2_2_2

/--
Exercise 2.2.2.

Let `a` be a positive natural number.
Then there exists exactly one natural number `b`
such that `b++ = a`.

Here `b++` is represented by `Nat.succ b`.
-/
theorem exercise_2_2_2 (a : ℕ) (ha : 0 < a) :
    ∃! b : ℕ, Nat.succ b = a := by
  cases a with
  | zero =>
      simp at ha
  | succ n =>
      refine ⟨n, rfl, ?_⟩
      intro b hb
      exact Nat.succ.inj hb

end TaoExercise2_2_2
