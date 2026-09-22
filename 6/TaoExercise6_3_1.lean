import Mathlib

namespace TaoExercise6_3_1

/--
The sequence aₙ = 1/n.
-/
noncomputable def a (n : ℕ) : ℝ :=
  1 / (n : ℝ)

/--
Values of the sequence beginning at index 1.
-/
noncomputable def seqSet : Set ℝ :=
  {x | ∃ n : ℕ, 1 ≤ n ∧ x = a n}


/-!
============================================================
Basic facts
============================================================
-/

/--
1 is a term of the sequence.
-/
theorem one_mem_seqSet :
    (1 : ℝ) ∈ seqSet := by

  refine ⟨1, le_rfl, ?_⟩

  unfold a

  norm_num


/--
The set is nonempty.
-/
theorem seqSet_nonempty :
    seqSet.Nonempty := by

  exact ⟨1, one_mem_seqSet⟩


/--
Every term is positive.
-/
theorem seq_pos
    {x : ℝ}
    (hx : x ∈ seqSet) :
    0 < x := by

  rcases hx with ⟨n, hn, rfl⟩

  unfold a

  have hnpos :
      0 < n := by
    omega

  have hnposR :
      (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hnpos

  positivity


/--
Every term is nonnegative.
-/
theorem seq_nonneg
    {x : ℝ}
    (hx : x ∈ seqSet) :
    0 ≤ x := by

  exact le_of_lt (seq_pos hx)


/--
Every term is at most 1.
-/
theorem seq_le_one
    {x : ℝ}
    (hx : x ∈ seqSet) :
    x ≤ 1 := by

  rcases hx with ⟨n, hn, rfl⟩

  unfold a

  have hnR :
      (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn

  have hnPos :
      (0 : ℝ) < (n : ℝ) := by
    linarith

  apply (div_le_iff₀ hnPos).2

  simpa using hnR


/-!
============================================================
Boundedness
============================================================
-/

/--
The sequence values are bounded above by 1.
-/
theorem seqSet_bddAbove :
    BddAbove seqSet := by

  refine ⟨1, ?_⟩

  intro x hx

  exact seq_le_one hx


/--
The sequence values are bounded below by 0.
-/
theorem seqSet_bddBelow :
    BddBelow seqSet := by

  refine ⟨0, ?_⟩

  intro x hx

  exact seq_nonneg hx


/-!
============================================================
Supremum
============================================================
-/

/--
The supremum is 1.
-/
theorem sup_seq_eq_one :
    sSup seqSet = 1 := by

  apply le_antisymm

  /-
  sSup ≤ 1, since 1 is an upper bound.
  -/
  · exact csSup_le
      seqSet_nonempty
      (by
        intro x hx
        exact seq_le_one hx)

  /-
  1 ≤ sSup because 1 belongs to the set.
  -/
  · exact le_csSup
      seqSet_bddAbove
      one_mem_seqSet


/-!
============================================================
Infimum
============================================================
-/

/--
0 is below the infimum because it is a lower bound.
-/
theorem zero_le_inf :
    (0 : ℝ) ≤ sInf seqSet := by

  exact le_csInf
    seqSet_nonempty
    (by
      intro x hx
      exact seq_nonneg hx)


/--
The infimum cannot be positive.
-/
theorem inf_le_zero :
    sInf seqSet ≤ (0 : ℝ) := by

  by_contra h

  have hinfPos :
      0 < sInf seqSet := by
    exact lt_of_not_ge h

  /-
  Choose N with

      1 / sInf(seqSet) < N.
  -/
  obtain ⟨N : ℕ, hN⟩ :=
    exists_nat_gt (1 / sInf seqSet)

  have hInvPos :
      0 < 1 / sInf seqSet := by
    positivity

  have hNPosR :
      (0 : ℝ) < (N : ℝ) := by
    exact lt_trans hInvPos hN

  have hNPos :
      0 < N := by
    exact_mod_cast hNPosR

  have hNge1 :
      1 ≤ N := by
    omega

  /-
  Therefore a_N belongs to the sequence set.
  -/
  have hterm :
      a N ∈ seqSet := by

    refine ⟨N, hNge1, rfl⟩

  /-
  Since sInf is a lower bound,

      sInf seqSet ≤ a N.
  -/
  have hinf_le_term :
      sInf seqSet ≤ a N := by

    exact csInf_le
      seqSet_bddBelow
      hterm

  /-
  But from 1 / sInf < N we obtain

      1/N < sInf.
  -/
  have hterm_lt :
      a N < sInf seqSet := by

    unfold a

    have hmul :
        1 < (N : ℝ) * sInf seqSet := by

      exact
        (div_lt_iff₀ hinfPos).mp hN

    have hmul' :
        1 < sInf seqSet * (N : ℝ) := by

      simpa [mul_comm] using hmul

    exact
      (div_lt_iff₀ hNPosR).2 hmul'

  exact (not_lt_of_ge hinf_le_term) hterm_lt


/--
The infimum is 0.
-/
theorem inf_seq_eq_zero :
    sInf seqSet = 0 := by

  apply le_antisymm

  · exact inf_le_zero

  · exact zero_le_inf


/-!
============================================================
Exercise 6.3.1
============================================================
-/

theorem exercise_6_3_1 :
    sSup seqSet = 1 ∧
    sInf seqSet = 0 := by

  constructor

  · exact sup_seq_eq_one

  · exact inf_seq_eq_zero

end TaoExercise6_3_1
