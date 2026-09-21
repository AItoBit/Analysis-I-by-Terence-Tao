import Mathlib

namespace TaoExercise5_3_3

/--
Two rational sequences are equivalent if, for every positive ε,
they are eventually ε-close.
-/
def SeqEquivalent
    (u v : ℕ → ℚ) : Prop :=
  ∀ ε : ℚ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ,
      N ≤ n →
      |u n - v n| ≤ ε


/--
The constant sequence with value `a`.
-/
def constSeq (a : ℚ) : ℕ → ℚ :=
  fun _ => a


/--
If `a = b`, then the constant sequences `a,a,a,...`
and `b,b,b,...` are equivalent.
-/
theorem constSeq_equiv_of_eq
    {a b : ℚ}
    (h : a = b) :
    SeqEquivalent (constSeq a) (constSeq b) := by

  subst b

  intro ε hε

  refine ⟨0, ?_⟩

  intro n hn

  unfold constSeq

  simp

  exact le_of_lt hε


/--
If the two constant rational sequences are equivalent,
then their constant values are equal.
-/
theorem eq_of_constSeq_equiv
    {a b : ℚ}
    (h : SeqEquivalent (constSeq a) (constSeq b)) :
    a = b := by

  by_contra hab

  have habAbs :
      0 < |a - b| := by
    exact abs_pos.mpr (sub_ne_zero.mpr hab)

  have heps :
      0 < |a - b| / 2 := by
    linarith

  obtain ⟨N, hN⟩ :=
    h (|a - b| / 2) heps

  have hclose :
      |a - b| ≤ |a - b| / 2 := by
    simpa [constSeq] using hN N (le_refl N)

  linarith


/--
Exercise 5.3.3.

For rational numbers `a` and `b`,

    a = b

if and only if their constant Cauchy sequences are equivalent.
-/
theorem exercise_5_3_3
    (a b : ℚ) :
    a = b ↔
      SeqEquivalent (constSeq a) (constSeq b) := by

  constructor

  · intro hab
    exact constSeq_equiv_of_eq hab

  · intro hEq
    exact eq_of_constSeq_equiv hEq

end TaoExercise5_3_3
