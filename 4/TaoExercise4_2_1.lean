import Mathlib

namespace TaoExercise4_2_1

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


/-!
Exercise 4.2.1

We prove that `RatEq` is:

1. reflexive,
2. symmetric,
3. transitive.
-/


/-!
Reflexivity.
-/

theorem ratEq_refl
    (x : RawRat) :
    RatEq x x := by
  unfold RatEq
  rfl


/-!
Symmetry.
-/

theorem ratEq_symm
    {x y : RawRat}
    (h : RatEq x y) :
    RatEq y x := by
  unfold RatEq at h ⊢
  exact h.symm


/-!
Transitivity.

Suppose

    a*d = c*b

and

    c*f = e*d.

We multiply appropriately to obtain

    d * (a*f) = d * (e*b).

Since d ≠ 0, cancellation gives

    a*f = e*b.
-/

theorem ratEq_trans
    {x y z : RawRat}
    (hxy : RatEq x y)
    (hyz : RatEq y z) :
    RatEq x z := by

  unfold RatEq at hxy hyz ⊢

  /-
  From

      x.num * y.den = y.num * x.den

  and

      y.num * z.den = z.num * y.den

  derive

      y.den * (x.num * z.den)
        =
      y.den * (z.num * x.den).
  -/
  have hcancel :
      y.den * (x.num * z.den)
        =
      y.den * (z.num * x.den) := by

    calc
      y.den * (x.num * z.den)
          = (x.num * y.den) * z.den := by
              ring

      _ = (y.num * x.den) * z.den := by
            rw [hxy]

      _ = x.den * (y.num * z.den) := by
            ring

      _ = x.den * (z.num * y.den) := by
            rw [hyz]

      _ = y.den * (z.num * x.den) := by
            ring

  /-
  Instead of relying on a cancellation theorem with a
  version-dependent name, turn the equality into

      y.den * (x.num*z.den - z.num*x.den) = 0

  and use the fact that integers have no zero divisors.
  -/
  have hzero :
      y.den *
          (x.num * z.den - z.num * x.den) = 0 := by

    rw [mul_sub]

    exact sub_eq_zero.mpr hcancel

  rcases mul_eq_zero.mp hzero with hden | hdiff

  /-
  First case is impossible because denominators are nonzero.
  -/
  · exact False.elim (y.den_ne_zero hden)

  /-
  Therefore

      x.num*z.den - z.num*x.den = 0,

  hence

      x.num*z.den = z.num*x.den.
  -/
  · exact sub_eq_zero.mp hdiff


/--
The three properties packaged together.
-/
theorem exercise_4_2_1 :
    (∀ x : RawRat, RatEq x x)
    ∧
    (∀ x y : RawRat,
      RatEq x y → RatEq y x)
    ∧
    (∀ x y z : RawRat,
      RatEq x y →
      RatEq y z →
      RatEq x z) := by

  constructor

  · intro x
    exact ratEq_refl x

  constructor

  · intro x y h
    exact ratEq_symm h

  · intro x y z hxy hyz
    exact ratEq_trans hxy hyz

end TaoExercise4_2_1
