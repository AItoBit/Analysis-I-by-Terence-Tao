import Mathlib

namespace TaoExercise6_4_6

/--
The sequence aₙ = -1/n.
-/
noncomputable def a (n : ℕ) : ℝ :=
  -(1 / (n : ℝ))

/--
The constant-zero sequence.
-/
def b (n : ℕ) : ℝ :=
  0

/--
Values of a sequence from index 1 onward.
-/
def seqSet
    (u : ℕ → ℝ) : Set ℝ :=
  {x | ∃ n : ℕ, 1 ≤ n ∧ x = u n}

/--
Supremum of a sequence from index 1 onward.
-/
noncomputable def seqSup
    (u : ℕ → ℝ) : ℝ :=
  sSup (seqSet u)

/-!
============================================================
Pointwise strict inequality
============================================================
-/

theorem a_lt_b
    (n : ℕ)
    (hn : 1 ≤ n) :
    a n < b n := by

  unfold a b

  have hnpos :
      0 < n := by
    omega

  have hnposR :
      (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hnpos

  have hdiv :
      0 < 1 / (n : ℝ) := by
    positivity

  linarith


/-!
============================================================
Boundedness
============================================================
-/

theorem a_bounded :
    ∃ M : ℝ,
      ∀ n : ℕ,
        1 ≤ n →
        |a n| ≤ M := by

  refine ⟨1, ?_⟩

  intro n hn

  unfold a

  have hnR :
      (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn

  have hnposR :
      (0 : ℝ) < (n : ℝ) := by
    linarith

  have hdiv :
      1 / (n : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hnposR).2
    simpa using hnR

  rw [abs_neg]

  have hnonneg :
      0 ≤ 1 / (n : ℝ) := by
    positivity

  rw [abs_of_nonneg hnonneg]

  exact hdiv


theorem b_bounded :
    ∃ M : ℝ,
      ∀ n : ℕ,
        1 ≤ n →
        |b n| ≤ M := by

  refine ⟨0, ?_⟩

  intro n hn

  simp [b]


/-!
============================================================
The supremum of b is 0
============================================================
-/

theorem zero_mem_b :
    (0 : ℝ) ∈ seqSet b := by

  refine ⟨1, le_rfl, ?_⟩

  simp [b]


theorem b_le_zero
    {x : ℝ}
    (hx : x ∈ seqSet b) :
    x ≤ 0 := by

  rcases hx with ⟨n, hn, rfl⟩

  simp [b]


theorem b_set_bddAbove :
    BddAbove (seqSet b) := by

  refine ⟨0, ?_⟩

  intro x hx

  exact b_le_zero hx


theorem sup_b_eq_zero :
    seqSup b = 0 := by

  unfold seqSup

  apply le_antisymm

  · exact csSup_le
      ⟨0, zero_mem_b⟩
      (by
        intro x hx
        exact b_le_zero hx)

  · exact le_csSup
      b_set_bddAbove
      zero_mem_b


/-!
============================================================
The supremum of a is also 0
============================================================
-/

theorem a_le_zero
    {x : ℝ}
    (hx : x ∈ seqSet a) :
    x ≤ 0 := by

  rcases hx with ⟨n, hn, rfl⟩

  unfold a

  have hnpos :
      0 < n := by
    omega

  have hnposR :
      (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hnpos

  have h :
      0 ≤ 1 / (n : ℝ) := by
    positivity

  linarith


theorem a_set_bddAbove :
    BddAbove (seqSet a) := by

  refine ⟨0, ?_⟩

  intro x hx

  exact a_le_zero hx


/--
Every negative real number fails to be an upper bound
for the sequence `a`.
-/
theorem exists_a_gt_of_neg
    (y : ℝ)
    (hy : y < 0) :
    ∃ n : ℕ,
      1 ≤ n ∧
      y < a n := by

  have hpos :
      0 < -y := by
    linarith

  obtain ⟨n : ℕ, hn⟩ :=
    exists_nat_gt (1 / (-y))

  have hInvPos :
      0 < 1 / (-y) := by
    positivity

  have hnPosR :
      (0 : ℝ) < (n : ℝ) := by
    exact lt_trans hInvPos hn

  have hnPos :
      0 < n := by
    exact_mod_cast hnPosR

  have hnOne :
      1 ≤ n := by
    omega

  have hmul :
      1 < (n : ℝ) * (-y) := by
    exact (div_lt_iff₀ hpos).mp hn

  have hdiv :
      1 / (n : ℝ) < -y := by
    apply (div_lt_iff₀ hnPosR).2
    simpa [mul_comm] using hmul

  refine ⟨n, hnOne, ?_⟩

  unfold a

  linarith


theorem sup_a_eq_zero :
    seqSup a = 0 := by

  unfold seqSup

  apply le_antisymm

  /-
  sup a ≤ 0.
  -/
  · exact csSup_le
      (by
        refine ⟨a 1, ?_⟩
        exact ⟨1, le_rfl, rfl⟩)
      (by
        intro x hx
        exact a_le_zero hx)

  /-
  0 ≤ sup a.
  -/
  · by_contra h

    have hsupNeg :
        sSup (seqSet a) < 0 := by
      exact lt_of_not_ge h

    obtain ⟨n, hn, hgt⟩ :=
      exists_a_gt_of_neg
        (sSup (seqSet a))
        hsupNeg

    have hmem :
        a n ∈ seqSet a := by
      exact ⟨n, hn, rfl⟩

    have hle :
        a n ≤ sSup (seqSet a) := by
      exact le_csSup a_set_bddAbove hmem

    linarith


/-!
============================================================
Exercise 6.4.6
============================================================
-/

theorem exercise_6_4_6 :
    (∃ M : ℝ,
      ∀ n : ℕ,
        1 ≤ n →
        |a n| ≤ M)
    ∧
    (∃ M : ℝ,
      ∀ n : ℕ,
        1 ≤ n →
        |b n| ≤ M)
    ∧
    (∀ n : ℕ,
      1 ≤ n →
      a n < b n)
    ∧
    seqSup a = 0
    ∧
    seqSup b = 0
    ∧
    ¬ seqSup a < seqSup b := by

  constructor

  · exact a_bounded

  constructor

  · exact b_bounded

  constructor

  · intro n hn
    exact a_lt_b n hn

  constructor

  · exact sup_a_eq_zero

  constructor

  · exact sup_b_eq_zero

  · rw [sup_a_eq_zero, sup_b_eq_zero]
    exact lt_irrefl 0

end TaoExercise6_4_6
