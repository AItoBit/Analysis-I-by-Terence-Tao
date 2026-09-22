import Mathlib

namespace TaoExercise6_1_4

/--
A sequence `a` converges to `L` starting from index `m`
if for every ε > 0 there exists `N ≥ m` such that
for all `n ≥ N`,

    |a n - L| ≤ ε.
-/
def ConvergesFrom
    (a : ℕ → ℝ)
    (m : ℕ)
    (L : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ,
      m ≤ N ∧
      ∀ n : ℕ,
        N ≤ n →
        |a n - L| ≤ ε


/--
Exercise 6.1.4.

For every natural number `k`,

    a_n → c

from index `m` iff

    a_{n+k} → c

from index `m`.
-/
theorem exercise_6_1_4
    (a : ℕ → ℝ)
    (m k : ℕ)
    (c : ℝ) :
    ConvergesFrom a m c ↔
    ConvergesFrom (fun n => a (n + k)) m c := by

  constructor

  /-
  Forward direction.

  If a_n converges to c, then a_{n+k} also converges to c.
  -/
  · intro hconv

    intro ε hε

    obtain ⟨N, hmN, hN⟩ :=
      hconv ε hε

    refine ⟨N, hmN, ?_⟩

    intro n hn

    have hnNk :
        N ≤ n + k := by
      exact le_trans hn (Nat.le_add_right n k)

    exact hN (n + k) hnNk


  /-
  Reverse direction.

  If a_{n+k} converges to c, then a_n converges to c.
  -/
  · intro hconv

    intro ε hε

    obtain ⟨M, hmM, hM⟩ :=
      hconv ε hε

    /-
    Take N = M + k.
    -/
    refine ⟨M + k, ?_, ?_⟩

    /-
    Since m ≤ M ≤ M+k, we have m ≤ M+k.
    -/
    · exact le_trans hmM (Nat.le_add_right M k)

    /-
    For n ≥ M+k, we have n-k ≥ M.
    Then

        (n-k)+k = n.
    -/
    · intro n hn

      have hk_le_n :
          k ≤ n := by
        have hk_le_Mk :
            k ≤ M + k := by
          exact Nat.le_add_left k M

        exact le_trans hk_le_Mk hn

      have hMle :
          M ≤ n - k := by
        omega

      have hshift :
          |a ((n - k) + k) - c| ≤ ε := by
        exact hM (n - k) hMle

      have hsubadd :
          (n - k) + k = n := by
        exact Nat.sub_add_cancel hk_le_n

      rw [hsubadd] at hshift

      exact hshift

end TaoExercise6_1_4
