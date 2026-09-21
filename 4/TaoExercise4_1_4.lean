import Mathlib

namespace TaoExercise4_1_4

/-
The pair (a,b) represents the formal integer a - b.
-/
structure RawInt where
  pos : ℕ
  neg : ℕ


/--
Equality of integer representatives:

    (a,b) ~ (c,d) iff a + d = c + b.
-/
def IntEq (x y : RawInt) : Prop :=
  x.pos + y.neg = y.pos + x.neg


/--
Addition:

    (a-b) + (c-d) = (a+c) - (b+d).
-/
def rawAdd (x y : RawInt) : RawInt :=
  ⟨x.pos + y.pos, x.neg + y.neg⟩


/--
Negation:

    -(a-b) = b-a.
-/
def rawNeg (x : RawInt) : RawInt :=
  ⟨x.neg, x.pos⟩


/--
Multiplication:

    (a-b)(c-d)
      = (ac + bd) - (ad + bc).
-/
def rawMul (x y : RawInt) : RawInt :=
  ⟨x.pos * y.pos + x.neg * y.neg,
   x.pos * y.neg + x.neg * y.pos⟩


/--
Zero integer: 0 - 0.
-/
def zeroInt : RawInt :=
  ⟨0, 0⟩


/--
One integer: 1 - 0.
-/
def oneInt : RawInt :=
  ⟨1, 0⟩


/-!
1. Addition is commutative.
-/
theorem add_comm_raw
    (x y : RawInt) :
    IntEq (rawAdd x y) (rawAdd y x) := by
  simp only [IntEq, rawAdd]
  ac_rfl


/-!
2. Addition is associative.
-/
theorem add_assoc_raw
    (x y z : RawInt) :
    IntEq
      (rawAdd (rawAdd x y) z)
      (rawAdd x (rawAdd y z)) := by
  simp only [IntEq, rawAdd]
  ac_rfl


/-!
3. Zero is the additive identity.
-/
theorem add_zero_raw
    (x : RawInt) :
    IntEq (rawAdd x zeroInt) x := by
  simp [IntEq, rawAdd, zeroInt]


theorem zero_add_raw
    (x : RawInt) :
    IntEq (rawAdd zeroInt x) x := by
  simp [IntEq, rawAdd, zeroInt]


/-!
4. Additive inverse.
-/
theorem add_neg_raw
    (x : RawInt) :
    IntEq (rawAdd x (rawNeg x)) zeroInt := by
  simp only [IntEq, rawAdd, rawNeg, zeroInt]
  ac_rfl


theorem neg_add_raw
    (x : RawInt) :
    IntEq (rawAdd (rawNeg x) x) zeroInt := by
  simp only [IntEq, rawAdd, rawNeg, zeroInt]
  ac_rfl


/-!
5. Multiplication is commutative.
-/
theorem mul_comm_raw
    (x y : RawInt) :
    IntEq (rawMul x y) (rawMul y x) := by
  simp only [IntEq, rawMul]
  ring


/-!
6. Multiplication is associative.
-/
theorem mul_assoc_raw
    (x y z : RawInt) :
    IntEq
      (rawMul (rawMul x y) z)
      (rawMul x (rawMul y z)) := by
  simp only [IntEq, rawMul]
  ring


/-!
7. One is the multiplicative identity.
-/
theorem mul_one_raw
    (x : RawInt) :
    IntEq (rawMul x oneInt) x := by
  simp [IntEq, rawMul, oneInt]


theorem one_mul_raw
    (x : RawInt) :
    IntEq (rawMul oneInt x) x := by
  simp [IntEq, rawMul, oneInt]


/-!
8. Left distributivity:

    x * (y + z) = x*y + x*z.
-/
theorem left_distrib_raw
    (x y z : RawInt) :
    IntEq
      (rawMul x (rawAdd y z))
      (rawAdd (rawMul x y) (rawMul x z)) := by
  simp only [IntEq, rawAdd, rawMul]
  ring


/-!
9. Right distributivity:

    (y + z) * x = y*x + z*x.
-/
theorem right_distrib_raw
    (x y z : RawInt) :
    IntEq
      (rawMul (rawAdd y z) x)
      (rawAdd (rawMul y x) (rawMul z x)) := by
  simp only [IntEq, rawAdd, rawMul]
  ring


/--
Exercise 4.1.4 packaged together.
-/
theorem exercise_4_1_4
    (x y z : RawInt) :
    IntEq (rawAdd x y) (rawAdd y x)
    ∧ IntEq
        (rawAdd (rawAdd x y) z)
        (rawAdd x (rawAdd y z))
    ∧ IntEq (rawAdd x zeroInt) x
    ∧ IntEq (rawAdd zeroInt x) x
    ∧ IntEq (rawAdd x (rawNeg x)) zeroInt
    ∧ IntEq (rawAdd (rawNeg x) x) zeroInt
    ∧ IntEq (rawMul x y) (rawMul y x)
    ∧ IntEq
        (rawMul (rawMul x y) z)
        (rawMul x (rawMul y z))
    ∧ IntEq (rawMul x oneInt) x
    ∧ IntEq (rawMul oneInt x) x
    ∧ IntEq
        (rawMul x (rawAdd y z))
        (rawAdd (rawMul x y) (rawMul x z))
    ∧ IntEq
        (rawMul (rawAdd y z) x)
        (rawAdd (rawMul y x) (rawMul z x)) := by
  constructor
  · exact add_comm_raw x y
  constructor
  · exact add_assoc_raw x y z
  constructor
  · exact add_zero_raw x
  constructor
  · exact zero_add_raw x
  constructor
  · exact add_neg_raw x
  constructor
  · exact neg_add_raw x
  constructor
  · exact mul_comm_raw x y
  constructor
  · exact mul_assoc_raw x y z
  constructor
  · exact mul_one_raw x
  constructor
  · exact one_mul_raw x
  constructor
  · exact left_distrib_raw x y z
  · exact right_distrib_raw x y z

end TaoExercise4_1_4
