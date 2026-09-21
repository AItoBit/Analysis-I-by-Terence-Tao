import Mathlib

namespace TaoExercise4_3_1

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
Interpret a raw rational as an ordinary Mathlib rational.
-/
def value (x : RawRat) : ℚ :=
  (x.num : ℚ) / (x.den : ℚ)


/--
Absolute value of a raw rational.
-/
def ratAbs (x : RawRat) : ℚ :=
  |value x|


/--
Distance between two rational numbers:

    d(x,y) = |x-y|.
-/
def distRat (x y : RawRat) : ℚ :=
  |value x - value y|


/-!
Basic compatibility between RawRat equality
and ordinary equality in ℚ.
-/

/--
The denominator remains nonzero after casting to ℚ.
-/
theorem den_cast_ne_zero
    (x : RawRat) :
    (x.den : ℚ) ≠ 0 := by
  exact_mod_cast x.den_ne_zero


/--
Tao's equality relation agrees with equality
of the represented rational values.
-/
theorem ratEq_iff_value_eq
    (x y : RawRat) :
    RatEq x y ↔ value x = value y := by

  have hx : (x.den : ℚ) ≠ 0 :=
    den_cast_ne_zero x

  have hy : (y.den : ℚ) ≠ 0 :=
    den_cast_ne_zero y

  unfold RatEq value

  constructor

  · intro h
    apply (div_eq_div_iff hx hy).2
    exact_mod_cast h

  · intro h
    have hcross :
        (x.num : ℚ) * (y.den : ℚ)
          =
        (y.num : ℚ) * (x.den : ℚ) :=
      (div_eq_div_iff hx hy).1 h

    exact_mod_cast hcross


/-!
(a)

|x| ≥ 0

and

|x| = 0 iff x = 0.
-/

theorem abs_nonnegative
    (x : RawRat) :
    0 ≤ ratAbs x := by
  unfold ratAbs
  exact abs_nonneg (value x)


theorem abs_eq_zero_iff
    (x : RawRat) :
    ratAbs x = 0 ↔ value x = 0 := by
  unfold ratAbs
  exact abs_eq_zero


/-!
(b)

Triangle inequality:

    |x+y| ≤ |x| + |y|.
-/

theorem abs_add_le_raw
    (x y : RawRat) :
    |value x + value y|
      ≤
    ratAbs x + ratAbs y := by
  unfold ratAbs
  exact abs_add_le (value x) (value y)


/-!
(c)

-y ≤ x ≤ y iff |x| ≤ y.
-/

theorem abs_le_iff_raw
    (x : RawRat)
    (y : ℚ) :
    (-y ≤ value x ∧ value x ≤ y)
      ↔
    ratAbs x ≤ y := by

  unfold ratAbs

  constructor

  · rintro ⟨hleft, hright⟩

    by_cases hx : 0 ≤ value x

    · rw [abs_of_nonneg hx]
      exact hright

    · have hxneg : value x < 0 := by
        exact lt_of_not_ge hx

      rw [abs_of_neg hxneg]
      linarith

  · intro h

    by_cases hx : 0 ≤ value x

    · have habs :
          |value x| = value x := by
        exact abs_of_nonneg hx

      rw [habs] at h

      constructor

      · linarith

      · exact h

    · have hxneg :
          value x < 0 := by
        exact lt_of_not_ge hx

      have habs :
          |value x| = -value x := by
        exact abs_of_neg hxneg

      rw [habs] at h

      constructor

      · linarith

      · linarith


/--
In particular:

    -|x| ≤ x ≤ |x|.
-/
theorem neg_abs_le_and_le_abs
    (x : RawRat) :
    -ratAbs x ≤ value x
      ∧
    value x ≤ ratAbs x := by

  unfold ratAbs

  constructor

  · exact neg_abs_le (value x)

  · exact le_abs_self (value x)


/-!
(d)

|xy| = |x||y|.
-/

theorem abs_mul_eq
    (x y : RawRat) :
    |value x * value y|
      =
    ratAbs x * ratAbs y := by

  unfold ratAbs

  exact abs_mul (value x) (value y)


/--
In particular:

    |-x| = |x|.
-/
theorem abs_neg_eq
    (x : RawRat) :
    |-value x| = ratAbs x := by

  unfold ratAbs

  exact abs_neg (value x)


/-!
(e)

Distance is nonnegative:

    d(x,y) ≥ 0

and

    d(x,y) = 0 iff x = y.
-/

theorem dist_nonnegative
    (x y : RawRat) :
    0 ≤ distRat x y := by

  unfold distRat

  exact abs_nonneg (value x - value y)


theorem dist_eq_zero_iff
    (x y : RawRat) :
    distRat x y = 0 ↔ RatEq x y := by

  unfold distRat

  constructor

  · intro h

    have hsub :
        value x - value y = 0 := by
      exact abs_eq_zero.mp h

    have hxy :
        value x = value y := by
      exact sub_eq_zero.mp hsub

    exact (ratEq_iff_value_eq x y).mpr hxy

  · intro h

    have hxy :
        value x = value y :=
      (ratEq_iff_value_eq x y).mp h

    have hsub :
        value x - value y = 0 := by
      exact sub_eq_zero.mpr hxy

    rw [hsub]
    norm_num


/-!
(f)

Distance is symmetric:

    d(x,y) = d(y,x).
-/

theorem dist_symm_raw
    (x y : RawRat) :
    distRat x y = distRat y x := by

  unfold distRat

  have h :
      value y - value x
        =
      -(value x - value y) := by
    ring

  rw [h]

  exact (abs_neg (value x - value y)).symm


/-!
(g)

Triangle inequality:

    d(x,z) ≤ d(x,y) + d(y,z).
-/

theorem dist_triangle
    (x y z : RawRat) :
    distRat x z
      ≤
    distRat x y + distRat y z := by

  unfold distRat

  have h :
      value x - value z
        =
      (value x - value y)
        +
      (value y - value z) := by
    ring

  rw [h]

  exact abs_add_le
    (value x - value y)
    (value y - value z)


/-!
Proposition 4.3.3 packaged together.
-/

theorem proposition_4_3_3
    (x y z : RawRat)
    (r : ℚ) :
    (0 ≤ ratAbs x)
    ∧
    (ratAbs x = 0 ↔ value x = 0)
    ∧
    (|value x + value y|
        ≤ ratAbs x + ratAbs y)
    ∧
    ((-r ≤ value x ∧ value x ≤ r)
        ↔ ratAbs x ≤ r)
    ∧
    (|value x * value y|
        = ratAbs x * ratAbs y)
    ∧
    (0 ≤ distRat x y)
    ∧
    (distRat x y = 0 ↔ RatEq x y)
    ∧
    (distRat x y = distRat y x)
    ∧
    (distRat x z
        ≤ distRat x y + distRat y z) := by

  constructor

  · exact abs_nonnegative x

  constructor

  · exact abs_eq_zero_iff x

  constructor

  · exact abs_add_le_raw x y

  constructor

  · exact abs_le_iff_raw x r

  constructor

  · exact abs_mul_eq x y

  constructor

  · exact dist_nonnegative x y

  constructor

  · exact dist_eq_zero_iff x y

  constructor

  · exact dist_symm_raw x y

  · exact dist_triangle x y z

end TaoExercise4_3_1
