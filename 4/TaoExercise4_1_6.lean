import Mathlib

namespace TaoExercise4_1_6

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
Tao's equality relation agrees with equality
of the represented integers.
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
The raw zero represents 0.
-/
theorem value_zeroInt :
    value zeroInt = 0 := by
  simp [value, zeroInt]


/--
Raw multiplication agrees with integer multiplication.
-/
theorem value_rawMul
    (x y : RawInt) :
    value (rawMul x y) = value x * value y := by
  unfold value rawMul
  push_cast
  ring


/--
Corollary 4.1.9 / Exercise 4.1.6.

If ac = bc and c ≠ 0, then a = b.
-/
theorem cancellation
    (a b c : RawInt)
    (hacbc : IntEq (rawMul a c) (rawMul b c))
    (hc : ¬ IntEq c zeroInt) :
    IntEq a b := by

  /-
  Convert ac = bc into ordinary integer equality.
  -/
  have hmulRaw :
      value (rawMul a c) = value (rawMul b c) :=
    (intEq_iff_value_eq
      (rawMul a c)
      (rawMul b c)).mp hacbc

  /-
  Therefore

      value a * value c = value b * value c.
  -/
  have hmul :
      value a * value c = value b * value c := by
    calc
      value a * value c
          = value (rawMul a c) := by
              symm
              exact value_rawMul a c
      _ = value (rawMul b c) := hmulRaw
      _ = value b * value c := by
              exact value_rawMul b c

  /-
  c ≠ 0 as a raw integer implies value c ≠ 0.
  -/
  have hcValue :
      value c ≠ 0 := by
    intro hc0

    apply hc

    apply (intEq_iff_value_eq c zeroInt).mpr

    calc
      value c = 0 := hc0
      _ = value zeroInt := value_zeroInt.symm

  /-
  From ac = bc,

      (a - b)c = 0.
  -/
  have hzero :
      (value a - value b) * value c = 0 := by
    calc
      (value a - value b) * value c
          = value a * value c -
              value b * value c := by
              ring
      _ = 0 := by
            rw [hmul]
            simp

  /-
  Since integers have no zero divisors,
  either a-b = 0 or c = 0.
  -/
  rcases mul_eq_zero.mp hzero with hab | hc0

  · have habValue :
        value a = value b := by
      exact sub_eq_zero.mp hab

    exact (intEq_iff_value_eq a b).mpr habValue

  · exact False.elim (hcValue hc0)


/--
Exercise packaged as an implication.
-/
theorem exercise_4_1_6
    (a b c : RawInt) :
    IntEq (rawMul a c) (rawMul b c) →
    ¬ IntEq c zeroInt →
    IntEq a b := by
  intro hacbc hc
  exact cancellation a b c hacbc hc

end TaoExercise4_1_6
