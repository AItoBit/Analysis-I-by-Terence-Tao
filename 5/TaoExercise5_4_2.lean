import Mathlib

namespace TaoExercise5_4_2

/-!
Exercise 5.4.2
Proposition 5.4.7: remaining order properties of the real numbers.
-/


/-!
============================================================
(a) Order trichotomy
============================================================

Exactly one of

    x = y
    x < y
    x > y

holds.
-/

theorem order_trichotomy
    (x y : ℝ) :
    (x = y ∨ x < y ∨ x > y)
    ∧ ¬ (x = y ∧ x < y)
    ∧ ¬ (x = y ∧ x > y)
    ∧ ¬ (x < y ∧ x > y) := by

  constructor

  /-
  At least one of the three alternatives holds.
  -/
  · rcases lt_trichotomy x y with hxy | hxy | hxy

    · exact Or.inr (Or.inl hxy)

    · exact Or.inl hxy

    · exact Or.inr (Or.inr hxy)

  constructor

  /-
  x = y and x < y are incompatible.
  -/
  · rintro ⟨hEq, hLt⟩
    subst y
    exact (lt_irrefl x) hLt

  constructor

  /-
  x = y and x > y are incompatible.
  -/
  · rintro ⟨hEq, hGt⟩
    subst y
    exact (lt_irrefl x) hGt

  /-
  x < y and x > y are incompatible.
  -/
  · rintro ⟨hLt, hGt⟩

    have hxy :
        x ≤ y := by
      exact le_of_lt hLt

    exact (not_lt_of_ge hxy) hGt


/--
A shorter version containing only the exhaustive
part of trichotomy.
-/
theorem order_trichotomy_short
    (x y : ℝ) :
    x = y ∨ x < y ∨ x > y := by

  rcases lt_trichotomy x y with hxy | hxy | hxy

  · exact Or.inr (Or.inl hxy)

  · exact Or.inl hxy

  · exact Or.inr (Or.inr hxy)


/-!
============================================================
(b) Order is anti-symmetric in Tao's terminology
============================================================

    x < y ↔ y > x

Since `y > x` is notation for `x < y`,
this is definitionally true.
-/

theorem lt_iff_gt
    (x y : ℝ) :
    x < y ↔ y > x := by

  rfl


/-!
============================================================
(c) Order is transitive
============================================================

    x < y
    y < z
    --------
    x < z
-/

theorem order_transitive
    {x y z : ℝ}
    (hxy : x < y)
    (hyz : y < z) :
    x < z := by

  exact lt_trans hxy hyz


/--
Implication-style version.
-/
theorem order_transitive_imp
    (x y z : ℝ) :
    x < y →
    y < z →
    x < z := by

  intro hxy hyz

  exact lt_trans hxy hyz


/-!
============================================================
(d) Addition preserves order
============================================================

If

    x < y,

then

    x + z < y + z.
-/

theorem addition_preserves_order
    {x y z : ℝ}
    (hxy : x < y) :
    x + z < y + z := by

  simpa [add_comm] using add_lt_add_right hxy z


/--
Implication-style version.
-/
theorem addition_preserves_order_imp
    (x y z : ℝ) :
    x < y →
    x + z < y + z := by

  intro hxy

  simpa [add_comm] using add_lt_add_right hxy z


/-!
============================================================
Difference characterizations
============================================================
These correspond closely to Tao's definitions of order.
-/

/--
x < y iff x - y is negative.
-/
theorem lt_iff_sub_negative
    (x y : ℝ) :
    x < y ↔ x - y < 0 := by

  constructor

  · intro hxy
    linarith

  · intro h
    linarith


/--
x > y iff x - y is positive.
-/
theorem gt_iff_sub_positive
    (x y : ℝ) :
    x > y ↔ 0 < x - y := by

  constructor

  · intro hxy
    linarith

  · intro h
    linarith


/--
x = y iff x - y = 0.
-/
theorem eq_iff_sub_zero
    (x y : ℝ) :
    x = y ↔ x - y = 0 := by

  constructor

  · intro hxy
    subst y
    ring

  · intro h
    linarith


/-!
============================================================
(a) Trichotomy via x - y
============================================================
This version mirrors Tao's proof more closely.
-/

theorem order_trichotomy_via_subtraction
    (x y : ℝ) :
    x = y ∨ x < y ∨ x > y := by

  rcases lt_trichotomy (x - y) 0 with hneg | hzero | hpos

  /-
  x - y < 0, hence x < y.
  -/
  · exact Or.inr
      (Or.inl
        ((lt_iff_sub_negative x y).mpr hneg))

  /-
  x - y = 0, hence x = y.
  -/
  · exact Or.inl
      ((eq_iff_sub_zero x y).mpr hzero)

  /-
  0 < x - y, hence x > y.
  -/
  · exact Or.inr
      (Or.inr
        ((gt_iff_sub_positive x y).mpr hpos))


/-!
============================================================
(b) Anti-symmetry via subtraction
============================================================
-/

theorem lt_iff_gt_via_subtraction
    (x y : ℝ) :
    x < y ↔ y > x := by

  constructor

  · intro hxy

    have hneg :
        x - y < 0 := by
      exact (lt_iff_sub_negative x y).mp hxy

    have hpos :
        0 < y - x := by
      linarith

    exact (gt_iff_sub_positive y x).mpr hpos

  · intro hyx

    have hpos :
        0 < y - x := by
      exact (gt_iff_sub_positive y x).mp hyx

    have hneg :
        x - y < 0 := by
      linarith

    exact (lt_iff_sub_negative x y).mpr hneg


/-!
============================================================
(c) Transitivity via subtraction
============================================================
-/

theorem order_transitive_via_subtraction
    {x y z : ℝ}
    (hxy : x < y)
    (hyz : y < z) :
    x < z := by

  have hxyNeg :
      x - y < 0 := by
    exact (lt_iff_sub_negative x y).mp hxy

  have hyzNeg :
      y - z < 0 := by
    exact (lt_iff_sub_negative y z).mp hyz

  have hxzIdentity :
      x - z =
        (x - y) + (y - z) := by
    ring

  have hxzNeg :
      x - z < 0 := by
    rw [hxzIdentity]
    linarith

  exact (lt_iff_sub_negative x z).mpr hxzNeg


/-!
============================================================
(d) Addition preserves order via subtraction
============================================================
-/

theorem addition_preserves_order_via_subtraction
    {x y z : ℝ}
    (hxy : x < y) :
    x + z < y + z := by

  have hneg :
      x - y < 0 := by
    exact (lt_iff_sub_negative x y).mp hxy

  have hidentity :
      (x + z) - (y + z) =
        x - y := by
    ring

  apply
    (lt_iff_sub_negative
      (x + z)
      (y + z)).mpr

  rw [hidentity]

  exact hneg


/-!
============================================================
Exercise 5.4.2 / Proposition 5.4.7 (a)-(d)
============================================================
-/

theorem exercise_5_4_2
    (x y z : ℝ) :
    (
      (x = y ∨ x < y ∨ x > y)
      ∧ ¬ (x = y ∧ x < y)
      ∧ ¬ (x = y ∧ x > y)
      ∧ ¬ (x < y ∧ x > y)
    )
    ∧
    (x < y ↔ y > x)
    ∧
    (x < y → y < z → x < z)
    ∧
    (x < y → x + z < y + z) := by

  constructor

  /-
  (a) Order trichotomy.
  -/
  · exact order_trichotomy x y

  constructor

  /-
  (b) x < y iff y > x.
  -/
  · exact lt_iff_gt x y

  constructor

  /-
  (c) Transitivity.
  -/
  · intro hxy hyz

    exact order_transitive hxy hyz

  /-
  (d) Addition preserves order.
  -/
  · intro hxy

    exact addition_preserves_order hxy

end TaoExercise5_4_2
