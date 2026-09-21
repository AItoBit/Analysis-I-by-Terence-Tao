import Mathlib

namespace TaoExercise5_5_2

/-!
Exercise 5.5.2.

Let E be nonempty, n ≥ 1, and L < K.

Assume K/n is an upper bound for E but L/n is not.
Then there exists L < m ≤ K such that m/n is an upper
bound but (m-1)/n is not.
-/

/--
`UpperByQuot E m n` means that `m / n` is an upper bound for `E`.
The division is carried out in `ℝ`.
-/
def UpperByQuot
    (E : Set ℝ)
    (m n : ℤ) : Prop :=
  ∀ x : ℝ, x ∈ E →
    x ≤ (m : ℝ) / (n : ℝ)


theorem exercise_5_5_2
    (E : Set ℝ)
    (n L K : ℤ)
    (hE : E.Nonempty)
    (hn : 1 ≤ n)
    (hLK : L < K)
    (hK : UpperByQuot E K n)
    (hL : ¬ UpperByQuot E L n) :
    ∃ m : ℤ,
      L < m
        ∧ m ≤ K
        ∧ UpperByQuot E m n
        ∧ ¬ UpperByQuot E (m - 1) n := by

  /-
  Let

      d = K - L.

  Since L < K, d is a positive natural number.
  -/
  let d : ℕ := (K - L).toNat

  have hKLpos :
      0 < K - L := by
    omega

  have hdpos :
      0 < d := by
    dsimp [d]
    exact Int.toNat_pos.mpr hKLpos

  have hdcast :
      (d : ℤ) = K - L := by
    dsimp [d]
    exact Int.toNat_of_nonneg (le_of_lt hKLpos)

  /-
  P t means

      (L+t)/n

  is an upper bound of E.
  -/
  let P : ℕ → Prop :=
    fun t =>
      UpperByQuot E (L + (t : ℤ)) n

  /-
  P d holds because

      L + d = K

  and K/n is an upper bound.
  -/
  have hLd :
      L + (d : ℤ) = K := by
    rw [hdcast]
    omega

  have hPd :
      P d := by
    dsimp [P]
    rw [hLd]
    exact hK

  /-
  Thus there is at least one t satisfying P.
  -/
  have hex :
      ∃ t : ℕ, P t := by
    exact ⟨d, hPd⟩

  /-
  Choose the smallest such t.
  -/
  let t : ℕ := Nat.find hex

  have hPt :
      P t := by
    dsimp [t]
    exact Nat.find_spec hex

  /-
  Since d satisfies P, minimality gives t ≤ d.
  -/
  have ht_le_d :
      t ≤ d := by
    dsimp [t]
    exact Nat.find_min' hex hPd

  /-
  P 0 is false, because P 0 says precisely that L/n
  is an upper bound.
  -/
  have hPzero :
      ¬ P 0 := by
    intro h

    apply hL

    simpa [P] using h

  /-
  Therefore the minimal t cannot be zero.
  -/
  have htpos :
      0 < t := by
    by_contra ht

    have htzero :
        t = 0 := by
      omega

    apply hPzero

    simpa [htzero] using hPt

  /-
  By minimality, P (t-1) is false.
  -/
  have hpred_lt :
      t - 1 < t := by
    omega

  have hPpred :
      ¬ P (t - 1) := by
    exact Nat.find_min hex hpred_lt

  /-
  Define

      m = L + t.
  -/
  let m : ℤ :=
    L + (t : ℤ)

  refine ⟨m, ?_, ?_, ?_, ?_⟩

  /-
  L < m because t > 0.
  -/
  · dsimp [m]

    have htposZ :
        (0 : ℤ) < (t : ℤ) := by
      exact_mod_cast htpos

    omega

  /-
  m ≤ K because t ≤ d = K-L.
  -/
  · dsimp [m]

    have ht_le_dZ :
        (t : ℤ) ≤ (d : ℤ) := by
      exact_mod_cast ht_le_d

    rw [hdcast] at ht_le_dZ

    omega

  /-
  m/n is an upper bound because P t holds.
  -/
  · simpa [P, m] using hPt

  /-
  Finally, (m-1)/n is not an upper bound.

  Since t > 0,

      L + (t-1) = (L+t)-1 = m-1.

  Thus this follows from ¬P(t-1).
  -/
  · have htone :
        1 ≤ t := by
      omega

    have hcast_pred :
        ((t - 1 : ℕ) : ℤ) =
          (t : ℤ) - 1 := by
      rw [Nat.cast_sub htone]
      norm_num

    have hpred_eq :
        L + ((t - 1 : ℕ) : ℤ) =
          m - 1 := by
      dsimp [m]
      rw [hcast_pred]
      ring

    intro hUpper

    apply hPpred

    dsimp [P]

    rw [hpred_eq]

    exact hUpper

end TaoExercise5_5_2
