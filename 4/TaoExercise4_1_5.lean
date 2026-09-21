import Mathlib

namespace TaoExercise4_1_5

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
Interpret a raw integer representative `(a,b)`
as the Mathlib integer `a - b`.
-/
def value (x : RawInt) : ℤ :=
  (x.pos : ℤ) - (x.neg : ℤ)


/--
Tao's equality relation is exactly equality
of the corresponding integer values.
-/
theorem intEq_iff_value_eq
    (x y : RawInt) :
    IntEq x y ↔ value x = value y := by
  unfold IntEq value
  constructor
  · intro h
    omega
  · intro h
    omega


/--
The raw zero represents the integer zero.
-/
theorem value_zeroInt :
    value zeroInt = 0 := by
  simp [value, zeroInt]


/--
Raw multiplication represents ordinary integer multiplication.
-/
theorem value_rawMul
    (x y : RawInt) :
    value (rawMul x y) = value x * value y := by
  unfold value rawMul
  push_cast
  ring


/--
Proposition 4.1.8 / Exercise 4.1.5.

If xy = 0, then x = 0 or y = 0,
where equality is Tao's equality relation on raw integers.
-/
theorem zero_product
    (x y : RawInt)
    (h : IntEq (rawMul x y) zeroInt) :
    IntEq x zeroInt ∨ IntEq y zeroInt := by

  /-
  Convert xy = 0 from the RawInt representation
  to ordinary integer equality.
  -/
  have hvalue :
      value (rawMul x y) = value zeroInt :=
    (intEq_iff_value_eq (rawMul x y) zeroInt).mp h

  /-
  Hence value(x) * value(y) = 0.
  -/
  have hprod :
      value x * value y = 0 := by
    calc
      value x * value y
          = value (rawMul x y) := by
              symm
              exact value_rawMul x y
      _ = value zeroInt := hvalue
      _ = 0 := value_zeroInt

  /-
  Integers have no zero divisors.
  -/
  rcases mul_eq_zero.mp hprod with hx | hy

  /-
  Case value(x) = 0.
  -/
  · left

    apply (intEq_iff_value_eq x zeroInt).mpr

    calc
      value x = 0 := hx
      _ = value zeroInt := value_zeroInt.symm

  /-
  Case value(y) = 0.
  -/
  · right

    apply (intEq_iff_value_eq y zeroInt).mpr

    calc
      value y = 0 := hy
      _ = value zeroInt := value_zeroInt.symm


/--
Exercise packaged as an implication.
-/
theorem exercise_4_1_5
    (x y : RawInt) :
    IntEq (rawMul x y) zeroInt →
      IntEq x zeroInt ∨ IntEq y zeroInt := by
  intro h
  exact zero_product x y h

end TaoExercise4_1_5
