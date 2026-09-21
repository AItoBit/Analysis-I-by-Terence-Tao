import Mathlib

namespace TaoExercise4_2_5

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
Addition:

    a/b + c/d = (ad + bc)/(bd).
-/
def rawAdd (x y : RawRat) : RawRat :=
  ⟨x.num * y.den + x.den * y.num,
   x.den * y.den,
   mul_ne_zero x.den_ne_zero y.den_ne_zero⟩


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
A rational is positive iff its value is greater than zero.
-/
def RatPos (x : RawRat) : Prop :=
  0 < value x


/-!
Basic compatibility lemmas.
-/

/--
The denominator remains nonzero after casting to ℚ.
-/
theorem den_cast_ne_zero
    (x : RawRat) :
    (x.den : ℚ) ≠ 0 := by
  exact_mod_cast x.den_ne_zero


/--
Tao's equality relation is equivalent to equality
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


/--
Raw addition corresponds to ordinary rational addition.
-/
theorem value_rawAdd
    (x y : RawRat) :
    value (rawAdd x y) =
      value x + value y := by

  have hx : (x.den : ℚ) ≠ 0 :=
    den_cast_ne_zero x

  have hy : (y.den : ℚ) ≠ 0 :=
    den_cast_ne_zero y

  unfold value rawAdd
  push_cast
  field_simp [hx, hy]


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


/-!
1. Order trichotomy.

Exactly one of

    x = y,
    x < y,
    x > y

holds.
-/

theorem order_trichotomy_exact
    (x y : RawRat) :
    (RatEq x y
      ∧ ¬ RatLt x y
      ∧ ¬ RatGt x y)
    ∨
    (RatLt x y
      ∧ ¬ RatEq x y
      ∧ ¬ RatGt x y)
    ∨
    (RatGt x y
      ∧ ¬ RatEq x y
      ∧ ¬ RatLt x y) := by

  rcases lt_trichotomy (value x) (value y) with hxy | heq | hyx

  /-
  Case x < y.
  -/
  · right
    left

    constructor

    · unfold RatLt
      exact hxy

    constructor

    · intro hEq

      have hv :
          value x = value y :=
        (ratEq_iff_value_eq x y).mp hEq

      exact (ne_of_lt hxy) hv

    · unfold RatGt
      exact not_lt_of_ge (le_of_lt hxy)


  /-
  Case x = y.
  -/
  · left

    constructor

    · exact (ratEq_iff_value_eq x y).mpr heq

    constructor

    · unfold RatLt
      rw [heq]
      exact lt_irrefl (value y)

    · unfold RatGt
      rw [heq]
      exact lt_irrefl (value y)


  /-
  Case y < x.
  -/
  · right
    right

    constructor

    · unfold RatGt
      exact hyx

    constructor

    · intro hEq

      have hv :
          value x = value y :=
        (ratEq_iff_value_eq x y).mp hEq

      exact (ne_of_gt hyx) hv

    · unfold RatLt
      exact not_lt_of_ge (le_of_lt hyx)


/-!
2.

    x < y iff y > x.
-/

theorem lt_iff_gt
    (x y : RawRat) :
    RatLt x y ↔ RatGt y x := by
  rfl


/-!
3. Transitivity:

    x < y,
    y < z
    ------
    x < z.
-/

theorem lt_trans_raw
    (x y z : RawRat)
    (hxy : RatLt x y)
    (hyz : RatLt y z) :
    RatLt x z := by

  unfold RatLt at hxy hyz ⊢

  exact lt_trans hxy hyz


/-!
4. Addition preserves strict order:

    x < y -> x + z < y + z.
-/

theorem add_preserves_lt
    (x y z : RawRat)
    (hxy : RatLt x y) :
    RatLt
      (rawAdd x z)
      (rawAdd y z) := by

  unfold RatLt at hxy ⊢

  rw [value_rawAdd, value_rawAdd]

  simpa [add_comm] using
    add_lt_add_right hxy (value z)


/-!
5. Multiplication by a positive rational preserves strict order:

    x < y
    z > 0
    -----
    xz < yz.
-/

theorem positive_mul_preserves_lt
    (x y z : RawRat)
    (hxy : RatLt x y)
    (hz : RatPos z) :
    RatLt
      (rawMul x z)
      (rawMul y z) := by

  unfold RatLt at hxy ⊢
  unfold RatPos at hz

  rw [value_rawMul, value_rawMul]

  exact mul_lt_mul_of_pos_right hxy hz


/--
Proposition 4.2.9 packaged together.
-/
theorem proposition_4_2_9
    (x y z : RawRat) :
    (
      (RatEq x y
        ∧ ¬ RatLt x y
        ∧ ¬ RatGt x y)
      ∨
      (RatLt x y
        ∧ ¬ RatEq x y
        ∧ ¬ RatGt x y)
      ∨
      (RatGt x y
        ∧ ¬ RatEq x y
        ∧ ¬ RatLt x y)
    )
    ∧
    (RatLt x y ↔ RatGt y x)
    ∧
    (RatLt x y →
      RatLt y z →
      RatLt x z)
    ∧
    (RatLt x y →
      RatLt
        (rawAdd x z)
        (rawAdd y z))
    ∧
    (RatLt x y →
      RatPos z →
      RatLt
        (rawMul x z)
        (rawMul y z)) := by

  constructor

  · exact order_trichotomy_exact x y

  constructor

  · exact lt_iff_gt x y

  constructor

  · intro hxy hyz
    exact lt_trans_raw x y z hxy hyz

  constructor

  · intro hxy
    exact add_preserves_lt x y z hxy

  · intro hxy hz
    exact positive_mul_preserves_lt x y z hxy hz

end TaoExercise4_2_5
