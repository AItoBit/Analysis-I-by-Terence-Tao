import Mathlib

namespace TaoExercise4_1_8

/--
The property used as a counterexample to induction on integers:

    P(n) :⇔ 0 ≤ n.

This means that `n` is a nonnegative integer.
-/
def P (n : ℤ) : Prop :=
  0 ≤ n


/--
P(0) is true.
-/
theorem P_zero :
    P 0 := by
  unfold P
  exact le_refl 0


/--
If P(n) is true, then P(n+1) is true.
-/
theorem P_succ
    (n : ℤ)
    (h : P n) :
    P (n + 1) := by
  unfold P at h ⊢
  omega


/--
But P(-1) is false.
-/
theorem not_P_neg_one :
    ¬ P (-1) := by
  unfold P
  omega


/--
Exercise 4.1.8.

There exists a property on the integers such that

* P(0) holds,
* P(n) implies P(n+1) for every integer n,
* but P(n) does not hold for every integer n.
-/
theorem exercise_4_1_8 :
    ∃ Q : ℤ → Prop,
      Q 0
      ∧ (∀ n : ℤ, Q n → Q (n + 1))
      ∧ ¬ (∀ n : ℤ, Q n) := by

  refine ⟨P, ?_, ?_, ?_⟩

  · exact P_zero

  · intro n hn
    exact P_succ n hn

  · intro hAll
    have hNegOne : P (-1) := hAll (-1)
    exact not_P_neg_one hNegOne

end TaoExercise4_1_8
