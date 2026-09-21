import Mathlib

namespace TaoExercise4_4_1

/-!
Exercise 4.4.1 / Proposition 4.4.1.
-/


/--
For every rational number x, there exists an integer n such that

    n ≤ x < n + 1.
-/
theorem exists_integer_part
    (x : ℚ) :
    ∃ n : ℤ,
      (n : ℚ) ≤ x
        ∧
      x < ((n + 1 : ℤ) : ℚ) := by

  refine ⟨x.floor, ?_, ?_⟩

  · exact Rat.floor_le x

  · exact Rat.lt_floor_add_one x


/--
Uniqueness of the integer part.

If both n and m satisfy

    n ≤ x < n+1
    m ≤ x < m+1,

then n = m.
-/
theorem integer_part_unique
    (x : ℚ)
    (n m : ℤ)
    (hn_lower : (n : ℚ) ≤ x)
    (hn_upper : x < ((n + 1 : ℤ) : ℚ))
    (hm_lower : (m : ℚ) ≤ x)
    (hm_upper : x < ((m + 1 : ℤ) : ℚ)) :
    n = m := by

  /-
  From

      n ≤ x < m+1

  we get

      n < m+1.
  -/
  have hnmQ :
      (n : ℚ) < ((m + 1 : ℤ) : ℚ) := by
    exact lt_of_le_of_lt hn_lower hm_upper

  have hnmZ :
      n < m + 1 := by
    exact_mod_cast hnmQ

  have hnm :
      n ≤ m := by
    omega


  /-
  Similarly,

      m < n+1,

  so m ≤ n.
  -/
  have hmnQ :
      (m : ℚ) < ((n + 1 : ℤ) : ℚ) := by
    exact lt_of_le_of_lt hm_lower hn_upper

  have hmnZ :
      m < n + 1 := by
    exact_mod_cast hmnQ

  have hmn :
      m ≤ n := by
    omega

  exact le_antisymm hnm hmn


/--
The unique integer satisfying

    n ≤ x < n+1

is floor(x).
-/
theorem integer_part_eq_floor
    (x : ℚ)
    (n : ℤ)
    (hn_lower : (n : ℚ) ≤ x)
    (hn_upper : x < ((n + 1 : ℤ) : ℚ)) :
    n = x.floor := by

  apply integer_part_unique x n x.floor

  · exact hn_lower

  · exact hn_upper

  · exact Rat.floor_le x

  · exact Rat.lt_floor_add_one x


/--
Existence and uniqueness of the integer part.
-/
theorem exists_unique_integer_part
    (x : ℚ) :
    ∃! n : ℤ,
      (n : ℚ) ≤ x
        ∧
      x < ((n + 1 : ℤ) : ℚ) := by

  refine ⟨x.floor, ?_, ?_⟩

  /-
  floor(x) satisfies the required inequalities.
  -/
  · constructor

    · exact Rat.floor_le x

    · exact Rat.lt_floor_add_one x

  /-
  Any other such integer equals floor(x).
  -/
  · intro n hn

    exact integer_part_eq_floor
      x n hn.1 hn.2


/-!
Final claim:

For every rational x, there exists a natural number N
such that x < N.
-/

theorem exists_nat_gt
    (x : ℚ) :
    ∃ N : ℕ, x < (N : ℚ) := by

  by_cases hxneg : x < 0

  /-
  If x < 0, choose N = 0.
  -/
  · refine ⟨0, ?_⟩
    simpa using hxneg


  /-
  Otherwise x ≥ 0.

  We choose

      N = toNat(floor(x) + 1).
  -/
  · have hxnonneg :
        0 ≤ x := by
      exact le_of_not_gt hxneg

    have hfloor_nonneg :
        0 ≤ x.floor := by
      exact Int.floor_nonneg.mpr hxnonneg

    have hfloor1_nonneg :
        0 ≤ x.floor + 1 := by
      omega

    let N : ℕ :=
      (x.floor + 1).toNat

    refine ⟨N, ?_⟩

    have htoNat :
        ((x.floor + 1).toNat : ℤ)
          =
        x.floor + 1 := by
      exact Int.toNat_of_nonneg hfloor1_nonneg

    have hcast :
        ((N : ℕ) : ℚ)
          =
        ((x.floor + 1 : ℤ) : ℚ) := by
      dsimp [N]
      exact_mod_cast htoNat

    rw [hcast]

    exact Rat.lt_floor_add_one x


/--
Proposition 4.4.1:

1. there exists a unique integer n such that
      n ≤ x < n+1;

2. there exists a natural number N such that
      x < N.
-/
theorem proposition_4_4_1
    (x : ℚ) :
    (∃! n : ℤ,
      (n : ℚ) ≤ x
        ∧
      x < ((n + 1 : ℤ) : ℚ))
    ∧
    (∃ N : ℕ, x < (N : ℚ)) := by

  constructor

  · exact exists_unique_integer_part x

  · exact exists_nat_gt x

end TaoExercise4_4_1
