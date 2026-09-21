import Mathlib

namespace TaoExercise4_1_1

/--
A raw integer representation.

The pair `(a,b)` represents the formal difference `a - b`.
-/
structure RawInt where
  pos : ℕ
  neg : ℕ

/--
Tao's equality relation on integer representatives:

    (a,b) ~ (c,d)  iff  a + d = c + b.
-/
def IntEq (x y : RawInt) : Prop :=
  x.pos + y.neg = y.pos + x.neg

infix:50 " ≈ " => IntEq


/--
Reflexivity of Tao's integer equality.
-/
theorem intEq_refl (x : RawInt) :
    x ≈ x := by
  unfold IntEq
  rfl


/--
Symmetry of Tao's integer equality.
-/
theorem intEq_symm
    {x y : RawInt}
    (h : x ≈ y) :
    y ≈ x := by
  unfold IntEq at h ⊢
  exact h.symm


/--
Exercise 4.1.1 packaged together.
-/
theorem exercise_4_1_1 :
    (∀ x : RawInt, x ≈ x)
    ∧
    (∀ x y : RawInt, x ≈ y → y ≈ x) := by
  constructor

  · intro x
    exact intEq_refl x

  · intro x y h
    exact intEq_symm h

end TaoExercise4_1_1
