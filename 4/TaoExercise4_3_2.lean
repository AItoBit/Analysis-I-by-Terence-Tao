import Mathlib

namespace TaoExercise4_3_2

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

    a / b = c / d iff a*d = c*b.
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
Negation.
-/
def rawNeg (x : RawRat) : RawRat :=
  ⟨-x.num, x.den, x.den_ne_zero⟩


/--
Subtraction.
-/
def rawSub (x y : RawRat) : RawRat :=
  rawAdd x (rawNeg y)


/--
Multiplication:

    (a/b)(c/d) = (ac)/(bd).
-/
def rawMul (x y : RawRat) : RawRat :=
  ⟨x.num * y.num,
   x.den * y.den,
   mul_ne_zero x.den_ne_zero y.den_ne_zero⟩


/--
Interpret a raw rational as a Mathlib rational.
-/
def value (x : RawRat) : ℚ :=
  (x.num : ℚ) / (x.den : ℚ)


/--
Absolute value.
-/
def ratAbs (x : RawRat) : ℚ :=
  |value x|


/--
Distance:

    d(x,y) = |x-y|.
-/
def distRat (x y : RawRat) : ℚ :=
  |value x - value y|


/--
x and y are epsilon-close iff

    d(x,y) ≤ epsilon.
-/
def Close (x y : RawRat) (epsilon : ℚ) : Prop :=
  distRat x y ≤ epsilon


/--
Positive rational.
-/
def RatPos (x : RawRat) : Prop :=
  0 < value x


/-!
Basic compatibility lemmas.
-/

theorem den_cast_ne_zero
    (x : RawRat) :
    (x.den : ℚ) ≠ 0 := by
  exact_mod_cast x.den_ne_zero


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


theorem value_rawAdd
    (x y : RawRat) :
    value (rawAdd x y)
      =
    value x + value y := by

  have hx : (x.den : ℚ) ≠ 0 :=
    den_cast_ne_zero x

  have hy : (y.den : ℚ) ≠ 0 :=
    den_cast_ne_zero y

  unfold value rawAdd
  push_cast
  field_simp [hx, hy]


theorem value_rawNeg
    (x : RawRat) :
    value (rawNeg x) = -value x := by

  unfold value rawNeg
  push_cast
  ring


theorem value_rawSub
    (x y : RawRat) :
    value (rawSub x y)
      =
    value x - value y := by

  unfold rawSub

  rw [value_rawAdd, value_rawNeg]

  ring


theorem value_rawMul
    (x y : RawRat) :
    value (rawMul x y)
      =
    value x * value y := by

  have hx : (x.den : ℚ) ≠ 0 :=
    den_cast_ne_zero x

  have hy : (y.den : ℚ) ≠ 0 :=
    den_cast_ne_zero y

  unfold value rawMul
  push_cast
  field_simp [hx, hy]


/-!
Properties of distance.
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

    rw [hxy]

    simp


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
(a)

x = y iff x and y are epsilon-close
for every positive epsilon.
-/

theorem eq_iff_close_for_all_positive
    (x y : RawRat) :
    RatEq x y
      ↔
    ∀ epsilon : ℚ,
      0 < epsilon →
      Close x y epsilon := by

  constructor

  /-
  x = y -> d(x,y) ≤ epsilon
  for every positive epsilon.
  -/
  · intro hxy epsilon hepsilon

    unfold Close

    have hdist :
        distRat x y = 0 :=
      (dist_eq_zero_iff x y).mpr hxy

    rw [hdist]

    exact le_of_lt hepsilon


  /-
  Conversely, suppose x and y are
  epsilon-close for every epsilon > 0.
  -/
  · intro hclose

    have hdistNonneg :
        0 ≤ distRat x y :=
      dist_nonnegative x y

    have hdistZero :
        distRat x y = 0 := by

      by_contra hne

      have hdistPos :
          0 < distRat x y := by
        exact lt_of_le_of_ne
          hdistNonneg
          (Ne.symm hne)

      let epsilon : ℚ :=
        distRat x y / 2

      have hepsilon :
          0 < epsilon := by
        dsimp [epsilon]
        linarith

      have hsmall :
          distRat x y ≤ epsilon :=
        hclose epsilon hepsilon

      dsimp [epsilon] at hsmall

      linarith

    exact (dist_eq_zero_iff x y).mp hdistZero


/-!
(b)

Closeness is symmetric.
-/

theorem close_symm
    (x y : RawRat)
    (epsilon : ℚ)
    (h : Close x y epsilon) :
    Close y x epsilon := by

  unfold Close at h ⊢

  rw [dist_symm_raw y x]

  exact h


/-!
(c)

If

    d(x,y) ≤ epsilon
    d(y,z) ≤ delta

then

    d(x,z) ≤ epsilon + delta.
-/

theorem close_trans
    (x y z : RawRat)
    (epsilon delta : ℚ)
    (hxy : Close x y epsilon)
    (hyz : Close y z delta) :
    Close x z (epsilon + delta) := by

  unfold Close at hxy hyz ⊢

  have htriangle :
      distRat x z
        ≤
      distRat x y + distRat y z :=
    dist_triangle x y z

  calc
    distRat x z
        ≤ distRat x y + distRat y z :=
      htriangle

    _ ≤ epsilon + delta :=
      add_le_add hxy hyz


/-!
(d1)

Addition preserves closeness:

if

    d(x,y) ≤ epsilon
    d(z,w) ≤ delta

then

    d(x+z, y+w) ≤ epsilon + delta.
-/

theorem close_add
    (x y z w : RawRat)
    (epsilon delta : ℚ)
    (hxy : Close x y epsilon)
    (hzw : Close z w delta) :
    Close
      (rawAdd x z)
      (rawAdd y w)
      (epsilon + delta) := by

  unfold Close at hxy hzw ⊢
  unfold distRat at hxy hzw ⊢

  rw [value_rawAdd, value_rawAdd]

  have hdecomp :
      (value x + value z) -
          (value y + value w)
        =
      (value x - value y)
        +
      (value z - value w) := by
    ring

  rw [hdecomp]

  calc
    |(value x - value y) +
        (value z - value w)|
        ≤
      |value x - value y|
        +
      |value z - value w| := by
        exact abs_add_le
          (value x - value y)
          (value z - value w)

    _ ≤ epsilon + delta :=
      add_le_add hxy hzw


/-!
(d2)

Subtraction preserves closeness:

if

    d(x,y) ≤ epsilon
    d(z,w) ≤ delta

then

    d(x-z, y-w) ≤ epsilon + delta.
-/

theorem close_sub
    (x y z w : RawRat)
    (epsilon delta : ℚ)
    (hxy : Close x y epsilon)
    (hzw : Close z w delta) :
    Close
      (rawSub x z)
      (rawSub y w)
      (epsilon + delta) := by

  unfold Close at hxy hzw ⊢
  unfold distRat at hxy hzw ⊢

  rw [value_rawSub, value_rawSub]

  have hdecomp :
      (value x - value z) -
          (value y - value w)
        =
      (value x - value y)
        +
      (value w - value z) := by
    ring

  rw [hdecomp]

  have hsymm :
      |value w - value z|
        =
      |value z - value w| := by

    have h :
        value w - value z
          =
        -(value z - value w) := by
      ring

    rw [h]

    exact abs_neg (value z - value w)

  calc
    |(value x - value y) +
        (value w - value z)|
        ≤
      |value x - value y|
        +
      |value w - value z| := by
        exact abs_add_le
          (value x - value y)
          (value w - value z)

    _ =
      |value x - value y|
        +
      |value z - value w| := by
        rw [hsymm]

    _ ≤ epsilon + delta :=
      add_le_add hxy hzw


/--
Part (d) packaged together.
-/
theorem close_add_and_sub
    (x y z w : RawRat)
    (epsilon delta : ℚ)
    (hxy : Close x y epsilon)
    (hzw : Close z w delta) :
    Close
        (rawAdd x z)
        (rawAdd y w)
        (epsilon + delta)
    ∧
    Close
        (rawSub x z)
        (rawSub y w)
        (epsilon + delta) := by

  constructor

  · exact close_add
      x y z w epsilon delta hxy hzw

  · exact close_sub
      x y z w epsilon delta hxy hzw


/-!
(e)

If x and y are epsilon-close and

    epsilon < epsilon',

then they are also epsilon'-close.
-/

theorem close_mono
    (x y : RawRat)
    (epsilon epsilon' : ℚ)
    (hxy : Close x y epsilon)
    (heps : epsilon < epsilon') :
    Close x y epsilon' := by

  unfold Close at hxy ⊢

  exact le_trans hxy (le_of_lt heps)


/-!
(f)

Suppose y and z are both epsilon-close to x.

If

    y ≤ w ≤ z,

then w is also epsilon-close to x.
-/

theorem close_of_between_ordered
    (x y z w : RawRat)
    (epsilon : ℚ)
    (hxy : Close x y epsilon)
    (hxz : Close x z epsilon)
    (hyw : value y ≤ value w)
    (hwz : value w ≤ value z) :
    Close x w epsilon := by

  unfold Close at hxy hxz ⊢
  unfold distRat at hxy hxz ⊢

  /-
  From |x-y| ≤ epsilon we obtain

      x-y ≤ epsilon.
  -/
  have hxyUpper :
      value x - value y ≤ epsilon := by

    have h :
        value x - value y
          ≤
        |value x - value y| :=
      le_abs_self (value x - value y)

    exact le_trans h hxy


  /-
  From |x-z| ≤ epsilon we obtain

      -epsilon ≤ x-z.
  -/
  have hxzLower :
      -epsilon ≤ value x - value z := by

    have h :
        -|value x - value z|
          ≤
        value x - value z :=
      neg_abs_le (value x - value z)

    linarith


  /-
  Since y ≤ w ≤ z,

      x-z ≤ x-w ≤ x-y.
  -/
  have hLower :
      -epsilon ≤ value x - value w := by
    linarith

  have hUpper :
      value x - value w ≤ epsilon := by
    linarith


  /-
  Hence |x-w| ≤ epsilon.
  -/
  by_cases hsign :
      0 ≤ value x - value w

  · rw [abs_of_nonneg hsign]
    exact hUpper

  · have hneg :
        value x - value w < 0 :=
      lt_of_not_ge hsign

    rw [abs_of_neg hneg]

    linarith


/-!
Full version of (f), allowing w to lie between
y and z in either order.
-/

theorem close_of_between
    (x y z w : RawRat)
    (epsilon : ℚ)
    (hxy : Close x y epsilon)
    (hxz : Close x z epsilon)
    (hbetween :
      (value y ≤ value w ∧ value w ≤ value z)
      ∨
      (value z ≤ value w ∧ value w ≤ value y)) :
    Close x w epsilon := by

  rcases hbetween with h | h

  · exact close_of_between_ordered
      x y z w epsilon
      hxy hxz
      h.1 h.2

  · exact close_of_between_ordered
      x z y w epsilon
      hxz hxy
      h.1 h.2


/-!
(g)

If x and y are epsilon-close and z is positive,
then xz and yz are epsilon*|z|-close.
-/

theorem close_mul_positive
    (x y z : RawRat)
    (epsilon : ℚ)
    (hxy : Close x y epsilon)
    (hz : RatPos z) :
    Close
      (rawMul x z)
      (rawMul y z)
      (epsilon * ratAbs z) := by

  unfold Close at hxy ⊢
  unfold distRat at hxy ⊢
  unfold RatPos at hz
  unfold ratAbs

  rw [value_rawMul, value_rawMul]

  have hfactor :
      value x * value z -
          value y * value z
        =
      (value x - value y) * value z := by
    ring

  rw [hfactor]
  rw [abs_mul]

  have hzNonneg :
      0 ≤ value z :=
    le_of_lt hz

  rw [abs_of_nonneg hzNonneg]

  exact mul_le_mul_of_nonneg_right
    hxy
    hzNonneg


/-!
Proposition 4.3.7.

The principal claims of the exercise are packaged below.
-/

theorem proposition_4_3_7
    (x y z w : RawRat)
    (epsilon delta epsilon' : ℚ)
    (hepsilon : 0 < epsilon)
    (hxy : Close x y epsilon)
    (hyz : Close y z delta)
    (hzw : Close z w delta)
    (heps : epsilon < epsilon')
    (hzPos : RatPos z) :
    (RatEq x y
      ↔
      ∀ e : ℚ, 0 < e → Close x y e)
    ∧
    Close y x epsilon
    ∧
    Close x z (epsilon + delta)
    ∧
    Close
        (rawAdd x z)
        (rawAdd y w)
        (epsilon + delta)
    ∧
    Close
        (rawSub x z)
        (rawSub y w)
        (epsilon + delta)
    ∧
    Close x y epsilon'
    ∧
    Close
        (rawMul x z)
        (rawMul y z)
        (epsilon * ratAbs z) := by

  constructor

  · exact eq_iff_close_for_all_positive x y

  constructor

  · exact close_symm x y epsilon hxy

  constructor

  · exact close_trans
      x y z
      epsilon delta
      hxy hyz

  constructor

  · exact close_add
      x y z w
      epsilon delta
      hxy hzw

  constructor

  · exact close_sub
      x y z w
      epsilon delta
      hxy hzw

  constructor

  · exact close_mono
      x y
      epsilon epsilon'
      hxy heps

  · exact close_mul_positive
      x y z
      epsilon
      hxy hzPos

end TaoExercise4_3_2
