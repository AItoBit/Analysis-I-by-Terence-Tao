import Mathlib

namespace TaoExercise4_2_4

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
Zero rational:

    0 = 0/1.
-/
def zeroRat : RawRat :=
  ⟨0, 1, by norm_num⟩


/--
A rational a/b is positive exactly when
the numerator and denominator have the same sign.

Equivalently:

    a*b > 0.
-/
def RatPos (x : RawRat) : Prop :=
  0 < x.num * x.den


/--
A rational a/b is negative exactly when
the numerator and denominator have opposite signs.

Equivalently:

    a*b < 0.
-/
def RatNeg (x : RawRat) : Prop :=
  x.num * x.den < 0


/-!
A rational is equal to zero iff its numerator is zero.
-/
theorem ratEq_zero_iff_num_zero
    (x : RawRat) :
    RatEq x zeroRat ↔ x.num = 0 := by
  unfold RatEq zeroRat
  simp


/-!
If numerator * denominator = 0, then the numerator
must be zero because the denominator is nonzero.
-/
theorem num_eq_zero_of_mul_den_eq_zero
    (x : RawRat)
    (h : x.num * x.den = 0) :
    x.num = 0 := by

  rcases mul_eq_zero.mp h with hnum | hden

  · exact hnum

  · exact False.elim (x.den_ne_zero hden)


/-!
At least one of the three alternatives holds:

    x = 0
    or x > 0
    or x < 0.
-/
theorem trichotomy_at_least_one
    (x : RawRat) :
    RatEq x zeroRat ∨ RatPos x ∨ RatNeg x := by

  rcases lt_trichotomy (x.num * x.den) 0 with hneg | hzero | hpos

  /-
  Case x.num * x.den < 0.
  -/
  · right
    right

    unfold RatNeg
    exact hneg

  /-
  Case x.num * x.den = 0.
  -/
  · left

    apply (ratEq_zero_iff_num_zero x).mpr

    exact num_eq_zero_of_mul_den_eq_zero x hzero

  /-
  Case 0 < x.num * x.den.
  -/
  · right
    left

    unfold RatPos
    exact hpos


/-!
Zero cannot be positive.
-/
theorem zero_not_positive
    (x : RawRat)
    (hx : RatEq x zeroRat) :
    ¬ RatPos x := by

  have hnum :
      x.num = 0 :=
    (ratEq_zero_iff_num_zero x).mp hx

  unfold RatPos

  rw [hnum]

  norm_num


/-!
Zero cannot be negative.
-/
theorem zero_not_negative
    (x : RawRat)
    (hx : RatEq x zeroRat) :
    ¬ RatNeg x := by

  have hnum :
      x.num = 0 :=
    (ratEq_zero_iff_num_zero x).mp hx

  unfold RatNeg

  rw [hnum]

  norm_num


/-!
A positive rational cannot be zero.
-/
theorem positive_not_zero
    (x : RawRat)
    (hx : RatPos x) :
    ¬ RatEq x zeroRat := by

  intro hzero

  exact zero_not_positive x hzero hx


/-!
A negative rational cannot be zero.
-/
theorem negative_not_zero
    (x : RawRat)
    (hx : RatNeg x) :
    ¬ RatEq x zeroRat := by

  intro hzero

  exact zero_not_negative x hzero hx


/-!
A rational cannot be both positive and negative.
-/
theorem not_positive_and_negative
    (x : RawRat) :
    ¬ (RatPos x ∧ RatNeg x) := by

  rintro ⟨hpos, hneg⟩

  unfold RatPos at hpos
  unfold RatNeg at hneg

  exact (lt_asymm hneg hpos)


/-!
If x is positive, then x is not negative.
-/
theorem positive_not_negative
    (x : RawRat)
    (hpos : RatPos x) :
    ¬ RatNeg x := by

  intro hneg

  exact not_positive_and_negative x ⟨hpos, hneg⟩


/-!
If x is negative, then x is not positive.
-/
theorem negative_not_positive
    (x : RawRat)
    (hneg : RatNeg x) :
    ¬ RatPos x := by

  intro hpos

  exact not_positive_and_negative x ⟨hpos, hneg⟩


/-!
Full trichotomy.

Exactly one of the following holds:

1. x = 0
2. x is positive
3. x is negative
-/
theorem rational_trichotomy_exact
    (x : RawRat) :
    (RatEq x zeroRat
      ∧ ¬ RatPos x
      ∧ ¬ RatNeg x)
    ∨
    (RatPos x
      ∧ ¬ RatEq x zeroRat
      ∧ ¬ RatNeg x)
    ∨
    (RatNeg x
      ∧ ¬ RatEq x zeroRat
      ∧ ¬ RatPos x) := by

  rcases lt_trichotomy (x.num * x.den) 0 with hneg | hzero | hpos

  /-
  Negative case.
  -/
  · right
    right

    have hxneg : RatNeg x := by
      unfold RatNeg
      exact hneg

    constructor

    · exact hxneg

    constructor

    · exact negative_not_zero x hxneg

    · exact negative_not_positive x hxneg


  /-
  Zero case.
  -/
  · left

    have hnum :
        x.num = 0 :=
      num_eq_zero_of_mul_den_eq_zero x hzero

    have hxzero :
        RatEq x zeroRat :=
      (ratEq_zero_iff_num_zero x).mpr hnum

    constructor

    · exact hxzero

    constructor

    · exact zero_not_positive x hxzero

    · exact zero_not_negative x hxzero


  /-
  Positive case.
  -/
  · right
    left

    have hxpos : RatPos x := by
      unfold RatPos
      exact hpos

    constructor

    · exact hxpos

    constructor

    · exact positive_not_zero x hxpos

    · exact positive_not_negative x hxpos


/--
Exercise 4.2.4 / Lemma 4.2.7.

Every rational is exactly one of:

* zero,
* positive,
* negative.
-/
theorem exercise_4_2_4
    (x : RawRat) :
    (RatEq x zeroRat
      ∧ ¬ RatPos x
      ∧ ¬ RatNeg x)
    ∨
    (RatPos x
      ∧ ¬ RatEq x zeroRat
      ∧ ¬ RatNeg x)
    ∨
    (RatNeg x
      ∧ ¬ RatEq x zeroRat
      ∧ ¬ RatPos x) := by

  exact rational_trichotomy_exact x

end TaoExercise4_2_4
