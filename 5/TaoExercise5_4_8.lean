import Mathlib

namespace TaoExercise5_4_8

/-!
============================================================
Convergence of a rational sequence to a real number
============================================================
-/

/--
A rational sequence `a` converges to a real number `L`
if for every ε > 0, eventually

    |a n - L| < ε.
-/
def ConvergesTo
    (a : ℕ → ℚ)
    (L : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ,
      N ≤ n →
      |(a n : ℝ) - L| < ε


/-!
============================================================
Upper bound passes to the limit
============================================================
-/

/--
If `aₙ → L` and every term satisfies `aₙ ≤ x`,
then

    L ≤ x.
-/
theorem limit_le_of_all_le
    (a : ℕ → ℚ)
    (L x : ℝ)
    (hlim : ConvergesTo a L)
    (hbound :
      ∀ n : ℕ,
        (a n : ℝ) ≤ x) :
    L ≤ x := by

  /-
  Suppose instead that x < L.
  -/
  by_contra h

  have hxL :
      x < L := by
    exact lt_of_not_ge h

  /-
  Choose

      ε = (L - x)/2 > 0.
  -/
  let ε : ℝ :=
    (L - x) / 2

  have hε :
      0 < ε := by
    dsimp [ε]
    linarith

  /-
  Since aₙ → L, eventually

      |aₙ - L| < ε.
  -/
  obtain ⟨N, hN⟩ :=
    hlim ε hε

  have hclose :
      |(a N : ℝ) - L| < ε := by
    exact hN N (le_refl N)

  /-
  From |a_N - L| < ε we get

      -ε < a_N - L.
  -/
  have hlower :
      -ε < (a N : ℝ) - L := by
    exact (abs_lt.mp hclose).1

  /-
  With ε = (L-x)/2 this implies

      x < a_N.
  -/
  have ha_gt_x :
      x < (a N : ℝ) := by
    dsimp [ε] at hlower
    linarith

  /-
  But every term was assumed ≤ x.
  -/
  have ha_le_x :
      (a N : ℝ) ≤ x :=
    hbound N

  linarith


/-!
============================================================
Lower bound passes to the limit
============================================================
-/

/--
If `aₙ → L` and every term satisfies `x ≤ aₙ`,
then

    x ≤ L.
-/
theorem le_limit_of_all_le
    (a : ℕ → ℚ)
    (L x : ℝ)
    (hlim : ConvergesTo a L)
    (hbound :
      ∀ n : ℕ,
        x ≤ (a n : ℝ)) :
    x ≤ L := by

  /-
  Suppose instead that L < x.
  -/
  by_contra h

  have hLx :
      L < x := by
    exact lt_of_not_ge h

  /-
  Choose

      ε = (x-L)/2 > 0.
  -/
  let ε : ℝ :=
    (x - L) / 2

  have hε :
      0 < ε := by
    dsimp [ε]
    linarith

  obtain ⟨N, hN⟩ :=
    hlim ε hε

  have hclose :
      |(a N : ℝ) - L| < ε := by
    exact hN N (le_refl N)

  /-
  From |a_N-L| < ε we obtain

      a_N - L < ε.
  -/
  have hupper :
      (a N : ℝ) - L < ε := by
    exact (abs_lt.mp hclose).2

  /-
  Hence a_N < x.
  -/
  have ha_lt_x :
      (a N : ℝ) < x := by
    dsimp [ε] at hupper
    linarith

  /-
  Contradiction with x ≤ a_N.
  -/
  have hx_le_a :
      x ≤ (a N : ℝ) :=
    hbound N

  linarith


/-!
============================================================
Exercise 5.4.8
============================================================
-/

/--
Exercise 5.4.8.

If all terms of a convergent rational sequence lie below `x`,
then its real limit lies below `x`.

If all terms lie above `x`, then its real limit lies above `x`.
-/
theorem exercise_5_4_8
    (a : ℕ → ℚ)
    (L x : ℝ)
    (hlim : ConvergesTo a L) :
    ((∀ n : ℕ,
        (a n : ℝ) ≤ x) →
      L ≤ x)
    ∧
    ((∀ n : ℕ,
        x ≤ (a n : ℝ)) →
      x ≤ L) := by

  constructor

  · intro hbound

    exact limit_le_of_all_le
      a L x
      hlim
      hbound

  · intro hbound

    exact le_limit_of_all_le
      a L x
      hlim
      hbound

end TaoExercise5_4_8
