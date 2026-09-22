import Mathlib

namespace TaoExercise6_1_6

/--
A rational sequence converges to a real number `L`,
starting from index `m`.
-/
def ConvergesFromRat
    (a : ℕ → ℚ)
    (m : ℕ)
    (L : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ,
      m ≤ N ∧
      ∀ n : ℕ,
        N ≤ n →
        |(a n : ℝ) - L| ≤ ε


/--
Tao's formal limit.

A Cauchy sequence of rational numbers defines a real number.
In Mathlib this is exactly `Real.mk`.
-/
def formalLimit
    (a : CauSeq ℚ abs) : ℝ :=
  Real.mk a


/--
Proposition 6.1.15 / Exercise 6.1.6.

Formal limits are genuine limits.

If `a` is a Cauchy sequence of rational numbers, then the
sequence of corresponding real numbers converges to the real
number represented by that Cauchy sequence.
-/
theorem proposition_6_1_15
    (a : CauSeq ℚ abs)
    (m : ℕ) :
    ConvergesFromRat
      (fun n => a n)
      m
      (formalLimit a) := by

  intro ε hε

  /-
  The rational Cauchy sequence, after coercion to ℝ,
  is still a Cauchy sequence.
  -/
  have hCauchyReal :
      IsCauSeq abs (fun n : ℕ => (a n : ℝ)) := by
    exact
      Real.isCauSeq_iff_lift.mp
        (CauSeq.isCauSeq a)

  /-
  Therefore there exists N₀ such that for j,k ≥ N₀,

      |a_j - a_k| < ε.
  -/
  obtain ⟨N₀, hN₀⟩ :=
    hCauchyReal.cauchy₂ hε

  /-
  We also need the chosen index to be ≥ m.
  -/
  let N : ℕ := max m N₀

  refine ⟨N, ?_, ?_⟩

  · exact le_max_left m N₀

  · intro n hn

    have hN₀N :
        N₀ ≤ N := by
      exact le_max_right m N₀

    have hN₀n :
        N₀ ≤ n := by
      exact le_trans hN₀N hn

    /-
    Fix n ≥ N.

    Since the sequence is Cauchy, every sufficiently late
    term a_j lies within ε of a_n.
    -/
    have hNearN :
        ∃ i : ℕ,
          ∀ j : ℕ,
            i ≤ j →
            |(a j : ℝ) - (a n : ℝ)| ≤ ε := by

      refine ⟨N₀, ?_⟩

      intro j hj

      have hdist :
          |(a j : ℝ) - (a n : ℝ)| < ε := by
        exact hN₀ j hj n hN₀n

      exact le_of_lt hdist

    /-
    `Real.mk_near_of_forall_near` says that if all sufficiently
    late terms of the Cauchy sequence lie within ε of x,
    then its formal limit lies within ε of x.
    -/
    have hFormal :
        |Real.mk a - (a n : ℝ)| ≤ ε := by
      exact
        Real.mk_near_of_forall_near
          hNearN

    /-
    Reverse the subtraction inside the absolute value.
    -/
    change
      |(a n : ℝ) - Real.mk a| ≤ ε

    simpa [abs_sub_comm] using hFormal


/--
Same result written explicitly with `formalLimit`.
-/
theorem exercise_6_1_6
    (a : CauSeq ℚ abs)
    (m : ℕ) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ,
        m ≤ N ∧
        ∀ n : ℕ,
          N ≤ n →
          |(a n : ℝ) - formalLimit a| ≤ ε := by

  exact proposition_6_1_15 a m

end TaoExercise6_1_6
