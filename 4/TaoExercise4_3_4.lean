import Mathlib

namespace TaoExercise4_3_4

theorem nat_pow_order
    (x y : ℚ)
    (k : ℕ)
    (hxy : y ≤ x)
    (hy : 0 ≤ y) :
    y ^ k ≤ x ^ k := by
  exact pow_le_pow_left₀ hy hxy k


theorem negative_integer_exponent_order
    (x y : ℚ)
    (n : ℤ)
    (hxy : y ≤ x)
    (hy : 0 < y)
    (hn : n < 0) :
    0 < x ^ n ∧ x ^ n ≤ y ^ n := by

  have hx : 0 < x := by
    exact lt_of_lt_of_le hy hxy

  let k : ℕ := Int.natAbs n

  have hkpos : 0 < k := by
    dsimp [k]
    exact Int.natAbs_pos.mpr (ne_of_lt hn)

  have hnonpos : n ≤ 0 := by
    exact le_of_lt hn

  have hn_eq :
      n = -(k : ℤ) := by
    dsimp [k]
    simp [Int.ofNat_natAbs_of_nonpos hnonpos]

  constructor

  · exact zpow_pos hx n

  · rw [hn_eq]

    simp only [zpow_neg, zpow_natCast]

    have hpow :
        y ^ k ≤ x ^ k := by
      exact nat_pow_order
        x y k
        hxy
        (le_of_lt hy)

    have hyPowPos :
        0 < y ^ k := by
      exact pow_pos hy k

    have hxPowPos :
        0 < x ^ k := by
      exact pow_pos hx k

    exact (inv_le_inv₀ hxPowPos hyPowPos).2 hpow

end TaoExercise4_3_4
