import Mathlib

namespace TaoExercise5_4_7

/-!
Exercise 5.4.7
-/


/-!
============================================================
First statement
============================================================

x ≤ y + ε for every ε > 0
iff
x ≤ y.
-/

theorem le_add_eps_iff
    (x y : ℝ) :
    (∀ ε : ℝ, 0 < ε → x ≤ y + ε) ↔
    x ≤ y := by

  constructor

  /-
  Forward direction.
  -/
  · intro h

    by_contra hxy

    have hyx :
        y < x := by
      exact lt_of_not_ge hxy

    let δ : ℝ :=
      (x - y) / 2

    have hδpos :
        0 < δ := by
      dsimp [δ]
      linarith

    have hbound :
        x ≤ y + δ :=
      h δ hδpos

    dsimp [δ] at hbound

    linarith


  /-
  Reverse direction.
  -/
  · intro hxy

    intro ε hε

    linarith


/-!
============================================================
Second statement
============================================================

|x-y| ≤ ε for every ε > 0
iff
x = y.
-/

theorem abs_sub_le_eps_iff
    (x y : ℝ) :
    (∀ ε : ℝ, 0 < ε → |x - y| ≤ ε) ↔
    x = y := by

  constructor

  /-
  Forward direction.
  -/
  · intro h

    by_contra hxy

    have habspos :
        0 < |x - y| := by
      exact abs_pos.mpr (sub_ne_zero.mpr hxy)

    let δ : ℝ :=
      |x - y| / 2

    have hδpos :
        0 < δ := by
      dsimp [δ]
      linarith

    have hbound :
        |x - y| ≤ δ :=
      h δ hδpos

    dsimp [δ] at hbound

    linarith


  /-
  Reverse direction.
  -/
  · intro hxy

    subst y

    intro ε hε

    simp

    exact le_of_lt hε


/-!
============================================================
Exercise 5.4.7 packaged together
============================================================
-/

theorem exercise_5_4_7
    (x y : ℝ) :
    ((∀ ε : ℝ, 0 < ε → x ≤ y + ε) ↔ x ≤ y)
    ∧
    ((∀ ε : ℝ, 0 < ε → |x - y| ≤ ε) ↔ x = y) := by

  constructor

  · exact le_add_eps_iff x y

  · exact abs_sub_le_eps_iff x y

end TaoExercise5_4_7
