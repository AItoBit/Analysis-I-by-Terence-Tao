import Mathlib

namespace TaoExercise6_1_3

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
Exercise 6.1.3.

If `m ≤ m'`, then the sequence starting at `m`
converges to `c` iff the sequence starting at `m'`
converges to `c`.
-/
theorem exercise_6_1_3
    (a : ℕ → ℝ)
    (m m' : ℕ)
    (c : ℝ)
    (hmm' : m ≤ m') :
    ConvergesFrom a m c ↔
    ConvergesFrom a m' c := by

  constructor

  /-
  If the sequence converges starting from m,
  then it also converges starting from m'.
  -/
  · intro hconv

    intro ε hε

    obtain ⟨N, hmN, hN⟩ :=
      hconv ε hε

    /-
    Take N' = max N m'.
    -/
    let N' : ℕ := max N m'

    refine ⟨N', ?_, ?_⟩

    · exact le_max_right N m'

    · intro n hn

      have hNle :
          N ≤ N' := by
        exact le_max_left N m'

      have hNn :
          N ≤ n := by
        exact le_trans hNle hn

      exact hN n hNn


  /-
  Conversely, if the sequence converges starting from m',
  then it converges starting from m.
  -/
  · intro hconv

    intro ε hε

    obtain ⟨N, hm'N, hN⟩ :=
      hconv ε hε

    refine ⟨N, ?_, ?_⟩

    /-
    Since m ≤ m' ≤ N, we have m ≤ N.
    -/
    · exact le_trans hmm' hm'N

    · intro n hn

      exact hN n hn

end TaoExercise6_1_3
