import Mathlib

namespace TaoExercise4_2_2

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


/-!
First part:

If

    a/b = a'/b',

then

    -(a'/b') = -(a/b).
-/

theorem neg_well_defined_reverse
    {x x' : RawRat}
    (h : RatEq x x') :
    RatEq (rawNeg x') (rawNeg x) := by

  unfold RatEq at h
  unfold RatEq
  simp only [rawNeg]

  calc
    (-x'.num) * x.den
        = -(x'.num * x.den) := by
            ring

    _ = -(x.num * x'.den) := by
          rw [← h]

    _ = (-x.num) * x'.den := by
          ring


/--
The same result in the conventional orientation:

    x = x' -> -x = -x'.
-/
theorem neg_well_defined
    {x x' : RawRat}
    (h : RatEq x x') :
    RatEq (rawNeg x) (rawNeg x') := by

  unfold RatEq at h
  unfold RatEq
  simp only [rawNeg]

  calc
    (-x.num) * x'.den
        = -(x.num * x'.den) := by
            ring

    _ = -(x'.num * x.den) := by
          rw [h]

    _ = (-x'.num) * x.den := by
          ring


/-!
Second part:

If

    a/b = a'/b',

then

    (a/b)(c/d) = (a'/b')(c/d).
-/

theorem mul_well_defined_left
    {x x' y : RawRat}
    (h : RatEq x x') :
    RatEq (rawMul x y) (rawMul x' y) := by

  unfold RatEq at h
  unfold RatEq
  simp only [rawMul]

  calc
    (x.num * y.num) * (x'.den * y.den)
        = (x.num * x'.den) * (y.num * y.den) := by
            ring

    _ = (x'.num * x.den) * (y.num * y.den) := by
          rw [h]

    _ = (x'.num * y.num) * (x.den * y.den) := by
          ring


/-!
Third part:

If

    c/d = c'/d',

then

    (a/b)(c/d) = (a/b)(c'/d').
-/

theorem mul_well_defined_right
    {x y y' : RawRat}
    (h : RatEq y y') :
    RatEq (rawMul x y) (rawMul x y') := by

  unfold RatEq at h
  unfold RatEq
  simp only [rawMul]

  calc
    (x.num * y.num) * (x.den * y'.den)
        = (x.num * x.den) * (y.num * y'.den) := by
            ring

    _ = (x.num * x.den) * (y'.num * y.den) := by
          rw [h]

    _ = (x.num * y'.num) * (x.den * y.den) := by
          ring


/--
Combined well-definedness of multiplication:

if x = x' and y = y', then

    x*y = x'*y'.
-/
theorem mul_well_defined
    {x x' y y' : RawRat}
    (hx : RatEq x x')
    (hy : RatEq y y') :
    RatEq (rawMul x y) (rawMul x' y') := by

  unfold RatEq at hx
  unfold RatEq at hy
  unfold RatEq
  simp only [rawMul]

  calc
    (x.num * y.num) * (x'.den * y'.den)
        =
      (x.num * x'.den) *
        (y.num * y'.den) := by
          ring

    _ =
      (x'.num * x.den) *
        (y'.num * y.den) := by
          rw [hx, hy]

    _ =
      (x'.num * y'.num) *
        (x.den * y.den) := by
          ring


/--
Exercise 4.2.2 packaged together.
-/
theorem exercise_4_2_2
    {x x' y y' : RawRat}
    (hx : RatEq x x')
    (hy : RatEq y y') :
    RatEq (rawNeg x') (rawNeg x)
    ∧
    RatEq (rawMul x y) (rawMul x' y)
    ∧
    RatEq (rawMul x y) (rawMul x y') := by

  constructor

  · exact neg_well_defined_reverse hx

  constructor

  · exact mul_well_defined_left hx

  · exact mul_well_defined_right hy

end TaoExercise4_2_2
