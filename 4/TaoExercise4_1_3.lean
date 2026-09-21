import Mathlib

namespace TaoExercise4_1_3

/--
A raw integer representation.

The pair `(a,b)` represents the formal difference `a - b`.
-/
structure RawInt where
  pos : ℕ
  neg : ℕ

/--
Tao's equality relation on integer representatives:

    (a,b) ≈ (c,d)  iff  a + d = c + b.
-/
def IntEq (x y : RawInt) : Prop :=
  x.pos + y.neg = y.pos + x.neg

infix:50 " ≈ " => IntEq


/--
Negation:

    -(a - b) = b - a.
-/
def rawNeg (x : RawInt) : RawInt :=
  ⟨x.neg, x.pos⟩

prefix:75 "－" => rawNeg


/--
Multiplication of integer representatives:

    (a - b)(c - d)
      = (ac + bd) - (ad + bc).
-/
def rawMul (x y : RawInt) : RawInt :=
  ⟨x.pos * y.pos + x.neg * y.neg,
   x.pos * y.neg + x.neg * y.pos⟩

infixl:70 " ⊗ " => rawMul


/--
The integer `-1`, represented as `0 - 1`.
-/
def minusOne : RawInt :=
  ⟨0, 1⟩


/--
Exercise 4.1.3.

For every integer representative `a`,

    (-1) * a = -a

with equality interpreted using Tao's integer equality relation.
-/
theorem minus_one_mul (a : RawInt) :
    minusOne ⊗ a ≈ －a := by
  unfold minusOne rawMul rawNeg IntEq
  simp


/--
The same calculation written more explicitly for
an integer represented as `m - n`.
-/
theorem minus_one_mul_explicit (m n : ℕ) :
    rawMul minusOne ⟨m, n⟩ ≈ rawNeg ⟨m, n⟩ := by
  unfold minusOne rawMul rawNeg IntEq
  simp

end TaoExercise4_1_3
