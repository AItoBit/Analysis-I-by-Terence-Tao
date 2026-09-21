import Mathlib

namespace TaoExercise4_2_3

/-
A raw rational number.

The triple stores a numerator, a nonzero denominator,
and the proof that the denominator is nonzero.
-/
structure RawRat where
  num : ℤ
  den : ℤ
  den_ne_zero : den ≠ 0


/--
Equality of rational representatives:

    a / b = c / d  iff  a*d = c*b.
-/
def RatEq (x y : RawRat) : Prop :=
  x.num * y.den = y.num * x.den


/--
Addition:

    a/b + c/d = (ad + bc)/(bd).
-/
def rawAdd (x y : RawRat) : RawRat :=
  ⟨x.num * y.den + x.den * y.num,
   x.den * y.den,
   mul_ne_zero x.den_ne_zero y.den_ne_zero⟩


/--
Negation:

    -(a/b) = (-a)/b.
-/
def rawNeg (x : RawRat) : RawRat :=
  ⟨-x.num, x.den, x.den_ne_zero⟩


/--
Multiplication:

    (a/b)(c/d) = (ac)/(bd).
-/
def rawMul (x y : RawRat) : RawRat :=
  ⟨x.num * y.num,
   x.den * y.den,
   mul_ne_zero x.den_ne_zero y.den_ne_zero⟩


/--
Zero rational:

    0 = 0/1.
-/
def zeroRat : RawRat :=
  ⟨0, 1, by norm_num⟩


/--
One rational:

    1 = 1/1.
-/
def oneRat : RawRat :=
  ⟨1, 1, by norm_num⟩


/-!
Before defining the inverse, we prove that a rational
which is not equal to zero has nonzero numerator.
-/

theorem num_ne_zero_of_not_ratEq_zero
    (x : RawRat)
    (hx : ¬ RatEq x zeroRat) :
    x.num ≠ 0 := by
  intro hnum
  apply hx
  unfold RatEq zeroRat
  simp [hnum]


/--
Inverse of a nonzero rational:

    (a/b)⁻¹ = b/a.
-/
def rawInv
    (x : RawRat)
    (hx : ¬ RatEq x zeroRat) :
    RawRat :=
  ⟨x.den,
   x.num,
   num_ne_zero_of_not_ratEq_zero x hx⟩


/-!
1. Addition is commutative.

    x + y = y + x
-/

theorem add_comm_raw
    (x y : RawRat) :
    RatEq (rawAdd x y) (rawAdd y x) := by
  simp only [RatEq, rawAdd]
  ring


/-!
2. Addition is associative.

    (x + y) + z = x + (y + z)
-/

theorem add_assoc_raw
    (x y z : RawRat) :
    RatEq
      (rawAdd (rawAdd x y) z)
      (rawAdd x (rawAdd y z)) := by
  simp only [RatEq, rawAdd]
  ring


/-!
3. Zero is the additive identity.

    x + 0 = x
    0 + x = x
-/

theorem add_zero_raw
    (x : RawRat) :
    RatEq (rawAdd x zeroRat) x := by
  simp [RatEq, rawAdd, zeroRat]


theorem zero_add_raw
    (x : RawRat) :
    RatEq (rawAdd zeroRat x) x := by
  simp [RatEq, rawAdd, zeroRat]


/-!
4. Additive inverses.

    x + (-x) = 0
    (-x) + x = 0
-/

theorem add_neg_raw
    (x : RawRat) :
    RatEq
      (rawAdd x (rawNeg x))
      zeroRat := by
  simp only [RatEq, rawAdd, rawNeg, zeroRat]
  ring


theorem neg_add_raw
    (x : RawRat) :
    RatEq
      (rawAdd (rawNeg x) x)
      zeroRat := by
  simp only [RatEq, rawAdd, rawNeg, zeroRat]
  ring


/-!
5. Multiplication is commutative.

    xy = yx
-/

theorem mul_comm_raw
    (x y : RawRat) :
    RatEq (rawMul x y) (rawMul y x) := by
  simp only [RatEq, rawMul]
  ring


/-!
6. Multiplication is associative.

    (xy)z = x(yz)
-/

theorem mul_assoc_raw
    (x y z : RawRat) :
    RatEq
      (rawMul (rawMul x y) z)
      (rawMul x (rawMul y z)) := by
  simp only [RatEq, rawMul]
  ring


/-!
7. One is the multiplicative identity.

    x * 1 = x
    1 * x = x
-/

theorem mul_one_raw
    (x : RawRat) :
    RatEq (rawMul x oneRat) x := by
  simp [RatEq, rawMul, oneRat]


theorem one_mul_raw
    (x : RawRat) :
    RatEq (rawMul oneRat x) x := by
  simp [RatEq, rawMul, oneRat]


/-!
8. Left distributivity.

    x(y + z) = xy + xz
-/

theorem left_distrib_raw
    (x y z : RawRat) :
    RatEq
      (rawMul x (rawAdd y z))
      (rawAdd
        (rawMul x y)
        (rawMul x z)) := by
  simp only [RatEq, rawAdd, rawMul]
  ring


/-!
9. Right distributivity.

    (y + z)x = yx + zx
-/

theorem right_distrib_raw
    (x y z : RawRat) :
    RatEq
      (rawMul (rawAdd y z) x)
      (rawAdd
        (rawMul y x)
        (rawMul z x)) := by
  simp only [RatEq, rawAdd, rawMul]
  ring


/-!
10. Multiplicative inverse.

If x ≠ 0, then

    x * x⁻¹ = 1.
-/

theorem mul_inv_raw
    (x : RawRat)
    (hx : ¬ RatEq x zeroRat) :
    RatEq
      (rawMul x (rawInv x hx))
      oneRat := by
  simp only [RatEq, rawMul, rawInv, oneRat]
  ring


/--
Also

    x⁻¹ * x = 1.
-/
theorem inv_mul_raw
    (x : RawRat)
    (hx : ¬ RatEq x zeroRat) :
    RatEq
      (rawMul (rawInv x hx) x)
      oneRat := by
  simp only [RatEq, rawMul, rawInv, oneRat]
  ring


/-!
A useful statement packaging the two inverse laws.
-/

theorem inverse_laws
    (x : RawRat)
    (hx : ¬ RatEq x zeroRat) :
    RatEq
        (rawMul x (rawInv x hx))
        oneRat
    ∧
    RatEq
        (rawMul (rawInv x hx) x)
        oneRat := by
  constructor
  · exact mul_inv_raw x hx
  · exact inv_mul_raw x hx


/-!
The algebraic part of Proposition 4.2.4 packaged together.
-/

theorem proposition_4_2_4_main
    (x y z : RawRat) :
    RatEq
        (rawAdd x y)
        (rawAdd y x)
    ∧
    RatEq
        (rawAdd (rawAdd x y) z)
        (rawAdd x (rawAdd y z))
    ∧
    RatEq
        (rawAdd x zeroRat)
        x
    ∧
    RatEq
        (rawAdd zeroRat x)
        x
    ∧
    RatEq
        (rawAdd x (rawNeg x))
        zeroRat
    ∧
    RatEq
        (rawAdd (rawNeg x) x)
        zeroRat
    ∧
    RatEq
        (rawMul x y)
        (rawMul y x)
    ∧
    RatEq
        (rawMul (rawMul x y) z)
        (rawMul x (rawMul y z))
    ∧
    RatEq
        (rawMul x oneRat)
        x
    ∧
    RatEq
        (rawMul oneRat x)
        x
    ∧
    RatEq
        (rawMul x (rawAdd y z))
        (rawAdd (rawMul x y) (rawMul x z))
    ∧
    RatEq
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


/--
Exercise 4.2.3, including the inverse clause.

The inverse part is conditional on x being nonzero.
-/
theorem exercise_4_2_3
    (x y z : RawRat)
    (hx : ¬ RatEq x zeroRat) :
    RatEq
        (rawAdd x y)
        (rawAdd y x)
    ∧
    RatEq
        (rawAdd (rawAdd x y) z)
        (rawAdd x (rawAdd y z))
    ∧
    RatEq
        (rawAdd x zeroRat)
        x
    ∧
    RatEq
        (rawAdd x (rawNeg x))
        zeroRat
    ∧
    RatEq
        (rawMul x y)
        (rawMul y x)
    ∧
    RatEq
        (rawMul (rawMul x y) z)
        (rawMul x (rawMul y z))
    ∧
    RatEq
        (rawMul x oneRat)
        x
    ∧
    RatEq
        (rawMul x (rawAdd y z))
        (rawAdd (rawMul x y) (rawMul x z))
    ∧
    RatEq
        (rawMul (rawAdd y z) x)
        (rawAdd (rawMul y x) (rawMul z x))
    ∧
    RatEq
        (rawMul x (rawInv x hx))
        oneRat
    ∧
    RatEq
        (rawMul (rawInv x hx) x)
        oneRat := by

  constructor
  · exact add_comm_raw x y

  constructor
  · exact add_assoc_raw x y z

  constructor
  · exact add_zero_raw x

  constructor
  · exact add_neg_raw x

  constructor
  · exact mul_comm_raw x y

  constructor
  · exact mul_assoc_raw x y z

  constructor
  · exact mul_one_raw x

  constructor
  · exact left_distrib_raw x y z

  constructor
  · exact right_distrib_raw x y z

  constructor
  · exact mul_inv_raw x hx

  · exact inv_mul_raw x hx

end TaoExercise4_2_3
