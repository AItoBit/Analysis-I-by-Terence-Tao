import Mathlib

namespace TaoExercise5_5_3

/--
`UpperByQuot E m n` means that `m / n`
is an upper bound for `E`.
-/
def UpperByQuot
    (E : Set ℝ)
    (m n : ℤ) : Prop :=
  ∀ x : ℝ, x ∈ E →
    x ≤ (m : ℝ) / (n : ℝ)


/--
Exercise 5.5.3.

Let `n ≥ 1`. Suppose both `m / n` and `m' / n`
are upper bounds for `E`, while

    (m - 1) / n
    (m' - 1) / n

are not upper bounds.

Then `m = m'`.
-/
theorem exercise_5_5_3
    (E : Set ℝ)
    (n m m' : ℤ)
    (hE : E.Nonempty)
    (hn : 1 ≤ n)
    (hm : UpperByQuot E m n)
    (hm' : UpperByQuot E m' n)
    (hmPred : ¬ UpperByQuot E (m - 1) n)
    (hm'Pred : ¬ UpperByQuot E (m' - 1) n) :
    m = m' := by

  /-
  Since n ≥ 1, n is positive.
  -/
  have hnPosZ :
      0 < n := by
    omega

  have hnPosR :
      (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hnPosZ

  have hnNeR :
      (n : ℝ) ≠ 0 :=
    ne_of_gt hnPosR


  /-
  ------------------------------------------------------------
  First prove m ≤ m'.
  ------------------------------------------------------------

  Since (m-1)/n is not an upper bound,
  choose x₀ ∈ E with

      (m-1)/n < x₀.
  -/
  have hmPred' := hmPred

  unfold UpperByQuot at hmPred'

  push Not at hmPred'

  obtain ⟨x₀, hx₀E, hx₀⟩ := hmPred'

  /-
  Since m'/n is an upper bound,

      x₀ ≤ m'/n.
  -/
  have hx₀Upper :
      x₀ ≤ (m' : ℝ) / (n : ℝ) := by
    exact hm' x₀ hx₀E

  /-
  Therefore

      (m-1)/n < m'/n.
  -/
  have hdiv₁ :
      ((m - 1 : ℤ) : ℝ) / (n : ℝ)
        <
      (m' : ℝ) / (n : ℝ) := by
    exact lt_of_lt_of_le hx₀ hx₀Upper

  /-
  Multiply by the positive denominator n.
  -/
  have hmul₁ :=
    mul_lt_mul_of_pos_right hdiv₁ hnPosR

  have hnum₁ :
      ((m - 1 : ℤ) : ℝ) < (m' : ℝ) := by
    field_simp [hnNeR] at hmul₁
    exact hmul₁

  have hInt₁ :
      m - 1 < m' := by
    exact_mod_cast hnum₁

  have hmm' :
      m ≤ m' := by
    omega


  /-
  ------------------------------------------------------------
  Now prove m' ≤ m.
  ------------------------------------------------------------

  Since (m'-1)/n is not an upper bound,
  choose x₁ ∈ E with

      (m'-1)/n < x₁.
  -/
  have hm'Pred' := hm'Pred

  unfold UpperByQuot at hm'Pred'

  push Not at hm'Pred'

  obtain ⟨x₁, hx₁E, hx₁⟩ := hm'Pred'

  /-
  Since m/n is an upper bound,

      x₁ ≤ m/n.
  -/
  have hx₁Upper :
      x₁ ≤ (m : ℝ) / (n : ℝ) := by
    exact hm x₁ hx₁E

  /-
  Hence

      (m'-1)/n < m/n.
  -/
  have hdiv₂ :
      ((m' - 1 : ℤ) : ℝ) / (n : ℝ)
        <
      (m : ℝ) / (n : ℝ) := by
    exact lt_of_lt_of_le hx₁ hx₁Upper

  /-
  Multiply by positive n.
  -/
  have hmul₂ :=
    mul_lt_mul_of_pos_right hdiv₂ hnPosR

  have hnum₂ :
      ((m' - 1 : ℤ) : ℝ) < (m : ℝ) := by
    field_simp [hnNeR] at hmul₂
    exact hmul₂

  have hInt₂ :
      m' - 1 < m := by
    exact_mod_cast hnum₂

  have hm'm :
      m' ≤ m := by
    omega


  /-
  Both inequalities imply equality.
  -/
  exact le_antisymm hmm' hm'm

end TaoExercise5_5_3
