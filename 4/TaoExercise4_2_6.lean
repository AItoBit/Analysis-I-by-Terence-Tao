import Mathlib

namespace TaoExercise4_2_6

/-
A raw rational number.

The pair (a,b), with b ≠ 0, represents a / b.
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
Multiplication:

    (a/b)(c/d) = (ac)/(bd).
-/
def rawMul (x y : RawRat) : RawRat :=
  ⟨x.num * y.num,
   x.den * y.den,
   mul_ne_zero x.den_ne_zero y.den_ne_zero⟩


/--
Interpret a raw rational as an ordinary Mathlib rational.
-/
def value (x : RawRat) : ℚ :=
  (x.num : ℚ) / (x.den : ℚ)


/--
Strict order:

    x < y.
-/
def RatLt (x y : RawRat) : Prop :=
  value x < value y


/--
Strict greater-than:

    x > y.
-/
def RatGt (x y : RawRat) : Prop :=
  value y < value x


/--
A rational is negative iff its value is less than zero.
-/
def RatNeg (x : RawRat) : Prop :=
  value x < 0


/--
The denominator remains nonzero after casting to ℚ.
-/
theorem den_cast_ne_zero
    (x : RawRat) :
    (x.den : ℚ) ≠ 0 := by
  exact_mod_cast x.den_ne_zero


/--
Raw multiplication corresponds to ordinary rational multiplication.
-/
theorem value_rawMul
    (x y : RawRat) :
    value (rawMul x y) =
      value x * value y := by

  have hx : (x.den : ℚ) ≠ 0 :=
    den_cast_ne_zero x

  have hy : (y.den : ℚ) ≠ 0 :=
    den_cast_ne_zero y

  unfold value rawMul
  push_cast
  field_simp [hx, hy]


/--
Exercise 4.2.6.

If x < y and z is negative, then xz > yz.
-/
theorem exercise_4_2_6
    (x y z : RawRat)
    (hxy : RatLt x y)
    (hz : RatNeg z) :
    RatGt
      (rawMul x z)
      (rawMul y z) := by

  unfold RatLt at hxy
  unfold RatNeg at hz
  unfold RatGt

  rw [value_rawMul, value_rawMul]

  exact mul_lt_mul_of_neg_right hxy hz

end TaoExercise4_2_6
