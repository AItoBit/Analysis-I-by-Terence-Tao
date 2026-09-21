import Mathlib

namespace TaoExercise5_4_6

/--
Exercise 5.4.6, strict version:

    |x - y| < ε ↔ y - ε < x ∧ x < y + ε
-/
theorem abs_sub_lt_iff
    (x y ε : ℝ) :
    |x - y| < ε ↔
      y - ε < x ∧ x < y + ε := by

  constructor

  /-
  Forward direction.
  -/
  · intro h

    have hbounds :
        -ε < x - y ∧ x - y < ε := by
      exact abs_lt.mp h

    constructor

    · linarith [hbounds.1]

    · linarith [hbounds.2]


  /-
  Reverse direction.
  -/
  · rintro ⟨hlower, hupper⟩

    apply abs_lt.mpr

    constructor

    · linarith

    · linarith


/--
Exercise 5.4.6, non-strict version:

    |x - y| ≤ ε ↔ y - ε ≤ x ∧ x ≤ y + ε
-/
theorem abs_sub_le_iff
    (x y ε : ℝ) :
    |x - y| ≤ ε ↔
      y - ε ≤ x ∧ x ≤ y + ε := by

  constructor

  /-
  Forward direction.
  -/
  · intro h

    have hbounds :
        -ε ≤ x - y ∧ x - y ≤ ε := by
      exact abs_le.mp h

    constructor

    · linarith [hbounds.1]

    · linarith [hbounds.2]


  /-
  Reverse direction.
  -/
  · rintro ⟨hlower, hupper⟩

    apply abs_le.mpr

    constructor

    · linarith

    · linarith


/--
Packaged version of Exercise 5.4.6.
-/
theorem exercise_5_4_6
    (x y ε : ℝ)
    (hε : 0 < ε) :
    (|x - y| < ε ↔
      y - ε < x ∧ x < y + ε)
    ∧
    (|x - y| ≤ ε ↔
      y - ε ≤ x ∧ x ≤ y + ε) := by

  constructor

  · exact abs_sub_lt_iff x y ε

  · exact abs_sub_le_iff x y ε

end TaoExercise5_4_6
