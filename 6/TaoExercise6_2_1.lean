import Mathlib

namespace TaoExercise6_2_1

/-!
Exercise 6.2.1 — Proposition 6.2.5

We use `EReal`, Mathlib's extended real numbers.

    ⊥ = -∞
    ⊤ = +∞
-/

/-!
============================================================
(a)

x ≤ x
============================================================
-/

theorem proposition_6_2_5_a
    (x : EReal) :
    x ≤ x := by

  exact le_refl x


/-!
============================================================
(b)

Trichotomy:

    x < y ∨ x = y ∨ x > y.
============================================================
-/

theorem proposition_6_2_5_b
    (x y : EReal) :
    x < y ∨ x = y ∨ x > y := by

  exact lt_trichotomy x y


/--
A version explicitly saying that the three alternatives
are mutually exclusive.
-/
theorem proposition_6_2_5_b_exactly_one
    (x y : EReal) :
    (x < y ∨ x = y ∨ x > y)
    ∧ ¬ (x < y ∧ x = y)
    ∧ ¬ (x < y ∧ x > y)
    ∧ ¬ (x = y ∧ x > y) := by

  constructor

  /-
  At least one alternative holds.
  -/
  · exact lt_trichotomy x y

  constructor

  /-
  x < y and x = y are incompatible.
  -/
  · rintro ⟨hxy, hEq⟩

    subst y

    exact (lt_irrefl x) hxy

  constructor

  /-
  x < y and x > y are incompatible.
  -/
  · rintro ⟨hxy, hyx⟩

    exact lt_asymm hxy hyx

  /-
  x = y and x > y are incompatible.
  -/
  · rintro ⟨hEq, hyx⟩

    subst y

    exact (lt_irrefl x) hyx


/-!
============================================================
(c)

Transitivity:

    x ≤ y → y ≤ z → x ≤ z.
============================================================
-/

theorem proposition_6_2_5_c
    (x y z : EReal)
    (hxy : x ≤ y)
    (hyz : y ≤ z) :
    x ≤ z := by

  exact le_trans hxy hyz


/-!
============================================================
(d)

Negation reverses the order:

    x ≤ y → -y ≤ -x.
============================================================
-/

theorem proposition_6_2_5_d
    (x y : EReal)
    (hxy : x ≤ y) :
    -y ≤ -x := by

  exact EReal.neg_le_neg_iff.mpr hxy


/-!
============================================================
Explicit infinity facts corresponding to Tao's case analysis.
============================================================
-/

/--
Every extended real is at most +∞.
-/
theorem le_pos_infinity
    (x : EReal) :
    x ≤ ⊤ := by

  exact le_top


/--
-∞ is at most every extended real.
-/
theorem neg_infinity_le
    (x : EReal) :
    ⊥ ≤ x := by

  exact bot_le


/--
Every finite real is strictly less than +∞.
-/
theorem real_lt_pos_infinity
    (x : ℝ) :
    (x : EReal) < ⊤ := by

  simp


/--
-∞ is strictly less than every finite real.
-/
theorem neg_infinity_lt_real
    (x : ℝ) :
    (⊥ : EReal) < (x : EReal) := by

  simp


/--
-∞ < +∞.
-/
theorem neg_infinity_lt_pos_infinity :
    (⊥ : EReal) < ⊤ := by

  exact bot_lt_top


/-!
============================================================
Negation of infinities.
============================================================
-/

theorem neg_pos_infinity :
    -(⊤ : EReal) = ⊥ := by

  simp


theorem neg_neg_infinity :
    -(⊥ : EReal) = ⊤ := by

  simp


/-!
============================================================
A useful explicit order-reversal equivalence.

For EReal, Mathlib provides:

    -a ≤ -b ↔ b ≤ a.
============================================================
-/

theorem neg_order_reversal
    (x y : EReal) :
    -y ≤ -x ↔ x ≤ y := by

  exact EReal.neg_le_neg_iff


/-!
============================================================
Complete packaged Proposition 6.2.5.
============================================================
-/

theorem proposition_6_2_5
    (x y z : EReal) :
    (x ≤ x)
    ∧
    (x < y ∨ x = y ∨ x > y)
    ∧
    (x ≤ y → y ≤ z → x ≤ z)
    ∧
    (x ≤ y → -y ≤ -x) := by

  constructor

  /-
  (a)
  -/
  · exact le_refl x

  constructor

  /-
  (b)
  -/
  · exact lt_trichotomy x y

  constructor

  /-
  (c)
  -/
  · intro hxy hyz

    exact le_trans hxy hyz

  /-
  (d)
  -/
  · intro hxy

    exact EReal.neg_le_neg_iff.mpr hxy

end TaoExercise6_2_1
