import Mathlib

namespace TaoExercise6_1_5

/--
A real sequence `a` converges to `L`, starting from index `m`.
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
A real sequence is Cauchy starting from index `m`.
-/
def IsCauchyFrom
    (a : ℕ → ℝ)
    (m : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ,
      m ≤ N ∧
      ∀ j k : ℕ,
        N ≤ j →
        N ≤ k →
        |a j - a k| ≤ ε


/--
Proposition 6.1.12.

Every convergent sequence of real numbers is Cauchy.
-/
theorem proposition_6_1_12
    (a : ℕ → ℝ)
    (m : ℕ)
    (c : ℝ)
    (hconv : ConvergesFrom a m c) :
    IsCauchyFrom a m := by

  intro ε hε

  /-
  Since ε > 0, we also have ε/2 > 0.
  -/
  have hε2 :
      0 < ε / 2 := by
    linarith

  /-
  Since a_n → c, eventually

      |a_n - c| ≤ ε/2.
  -/
  obtain ⟨N, hmN, hN⟩ :=
    hconv (ε / 2) hε2

  refine ⟨N, hmN, ?_⟩

  intro j k hj hk

  have hjclose :
      |a j - c| ≤ ε / 2 := by
    exact hN j hj

  have hkclose :
      |a k - c| ≤ ε / 2 := by
    exact hN k hk

  /-
  Decompose

      a_j - a_k
        =
      (a_j - c) + (c - a_k).
  -/
  have hdecomp :
      a j - a k =
        (a j - c) + (c - a k) := by
    ring

  rw [hdecomp]

  calc
    |(a j - c) + (c - a k)|
        ≤ |a j - c| + |c - a k| := by
          exact abs_add_le
            (a j - c)
            (c - a k)

    _ = |a j - c| + |a k - c| := by
          have h :
              |c - a k| = |a k - c| := by
            have hneg :
                c - a k = -(a k - c) := by
              ring
            rw [hneg]
            exact abs_neg (a k - c)

          rw [h]

    _ ≤ ε / 2 + ε / 2 := by
          exact add_le_add hjclose hkclose

    _ = ε := by
          ring


/--
Implication-style formulation of Exercise 6.1.5.
-/
theorem exercise_6_1_5
    (a : ℕ → ℝ)
    (m : ℕ)
    (c : ℝ) :
    ConvergesFrom a m c →
    IsCauchyFrom a m := by

  intro hconv

  exact proposition_6_1_12
    a m c hconv

end TaoExercise6_1_5
