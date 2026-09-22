import Mathlib

namespace TaoExercise6_6_3

/-!
============================================================
Basic definitions
============================================================
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


def IsBounded
    (a : ℕ → ℝ) : Prop :=
  ∃ M : ℝ,
    ∀ n : ℕ,
      |a n| ≤ M


def IsSubsequence
    (a b : ℕ → ℝ) : Prop :=
  ∃ φ : ℕ → ℕ,
    StrictMono φ ∧
    ∀ n : ℕ,
      b n = a (φ n)


/-!
============================================================
An unbounded sequence has arbitrarily large terms
============================================================
-/

theorem exists_abs_gt
    (a : ℕ → ℝ)
    (hUnbounded : ¬ IsBounded a)
    (M : ℝ) :
    ∃ n : ℕ,
      M < |a n| := by

  by_contra h

  apply hUnbounded

  refine ⟨M, ?_⟩

  intro n

  by_contra hn

  have hgt :
      M < |a n| := by
    exact lt_of_not_ge hn

  exact h ⟨n, hgt⟩


/-!
============================================================
There is a sufficiently large term after any fixed index
============================================================
-/

theorem exists_large_after
    (a : ℕ → ℝ)
    (hUnbounded : ¬ IsBounded a)
    (j K : ℕ) :
    ∃ n : ℕ,
      K < n ∧
      (j : ℝ) ≤ |a n| := by

  /-
  This bounds the finitely many terms
      |a 0|, ..., |a K|.
  -/
  let S : ℝ :=
    ∑ i ∈ Finset.range (K + 1), |a i|

  let R : ℝ :=
    max (j : ℝ) S

  obtain ⟨n, hnLarge⟩ :=
    exists_abs_gt a hUnbounded R

  have hjR :
      (j : ℝ) ≤ R := by
    dsimp [R]
    exact le_max_left (j : ℝ) S

  have hSR :
      S ≤ R := by
    dsimp [R]
    exact le_max_right (j : ℝ) S

  have hjLarge :
      (j : ℝ) < |a n| := by
    exact lt_of_le_of_lt hjR hnLarge

  have hSLarge :
      S < |a n| := by
    exact lt_of_le_of_lt hSR hnLarge

  /-
  n cannot be ≤ K, since then |a n| would occur
  among the summands defining S.
  -/
  have hKn :
      K < n := by

    by_contra hNot

    have hnK :
        n ≤ K := by
      exact Nat.le_of_not_gt hNot

    have hnMem :
        n ∈ Finset.range (K + 1) := by
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le hnK)

    have hterm :
        |a n| ≤ S := by

      dsimp [S]

      exact Finset.single_le_sum
        (fun i hi => abs_nonneg (a i))
        hnMem

    exact (not_lt_of_ge hterm) hSLarge

  exact ⟨n, hKn, le_of_lt hjLarge⟩


/-!
============================================================
Recursive sequence of selected indices
============================================================
-/

noncomputable def indexSeq
    (a : ℕ → ℝ)
    (hUnbounded : ¬ IsBounded a) :
    ℕ → ℕ
  | 0 => 0
  | j + 1 =>
      Nat.find
        (exists_large_after
          a
          hUnbounded
          (j + 1)
          (indexSeq a hUnbounded j))


/-!
============================================================
One recursive step
============================================================
-/

theorem indexSeq_step_spec
    (a : ℕ → ℝ)
    (hUnbounded : ¬ IsBounded a)
    (j : ℕ) :
    indexSeq a hUnbounded j
        < indexSeq a hUnbounded (j + 1)
    ∧
    ((j + 1 : ℕ) : ℝ)
        ≤ |a (indexSeq a hUnbounded (j + 1))| := by

  rw [indexSeq]

  exact Nat.find_spec
    (exists_large_after
      a
      hUnbounded
      (j + 1)
      (indexSeq a hUnbounded j))


/-!
============================================================
The selected indices are strictly increasing

We prove this manually instead of using
`strictMono_nat_of_lt_succ`, avoiding the AddRightMono
typeclass inference problem.
============================================================
-/

theorem indexSeq_strictMono
    (a : ℕ → ℝ)
    (hUnbounded : ¬ IsBounded a) :
    StrictMono (indexSeq a hUnbounded) := by

  intro i j hij

  induction j with

  | zero =>
      omega

  | succ j ih =>

      by_cases hijEq : i = j

      /-
      i = j, so this is exactly one recursive step.
      -/
      · subst i

        exact
          (indexSeq_step_spec
            a
            hUnbounded
            j).1

      /-
      Otherwise i < j.
      -/
      · have hij' :
            i < j := by
          omega

        have hPrev :
            indexSeq a hUnbounded i
              < indexSeq a hUnbounded j := by
          exact ih hij'

        have hStep :
            indexSeq a hUnbounded j
              < indexSeq a hUnbounded (j + 1) := by
          exact
            (indexSeq_step_spec
              a
              hUnbounded
              j).1

        exact lt_trans hPrev hStep


/-!
============================================================
The selected terms become arbitrarily large
============================================================
-/

theorem indexSeq_large
    (a : ℕ → ℝ)
    (hUnbounded : ¬ IsBounded a)
    (j : ℕ) :
    (j : ℝ) ≤
      |a (indexSeq a hUnbounded j)| := by

  cases j with

  | zero =>
      exact abs_nonneg _

  | succ j =>
      exact
        (indexSeq_step_spec
          a
          hUnbounded
          j).2


/-!
============================================================
Define the subsequence b_j = a_(indexSeq j)
============================================================
-/

noncomputable def b
    (a : ℕ → ℝ)
    (hUnbounded : ¬ IsBounded a)
    (j : ℕ) : ℝ :=
  a (indexSeq a hUnbounded j)


theorem b_is_subsequence
    (a : ℕ → ℝ)
    (hUnbounded : ¬ IsBounded a) :
    IsSubsequence
      a
      (b a hUnbounded) := by

  refine ⟨indexSeq a hUnbounded, ?_, ?_⟩

  · exact indexSeq_strictMono
      a
      hUnbounded

  · intro n
    rfl


theorem b_large
    (a : ℕ → ℝ)
    (hUnbounded : ¬ IsBounded a)
    (j : ℕ) :
    (j : ℝ) ≤
      |b a hUnbounded j| := by

  unfold b

  exact indexSeq_large
    a
    hUnbounded
    j


/-!
============================================================
The reciprocals converge to zero
============================================================
-/

theorem reciprocal_b_converges_zero
    (a : ℕ → ℝ)
    (hUnbounded : ¬ IsBounded a) :
    ConvergesFrom
      (fun j : ℕ =>
        1 / b a hUnbounded j)
      0
      0 := by

  intro ε hε

  /-
  Choose J > 1/ε.
  -/
  obtain ⟨J : ℕ, hJ⟩ :=
    exists_nat_gt (1 / ε)

  have hInvPos :
      (0 : ℝ) < 1 / ε := by
    exact one_div_pos.mpr hε

  have hJposR :
      (0 : ℝ) < (J : ℝ) := by
    exact lt_trans hInvPos hJ

  refine ⟨J, Nat.zero_le J, ?_⟩

  intro k hk

  /-
  J ≤ k, now viewed in ℝ.
  -/
  have hJkR :
      (J : ℝ) ≤ (k : ℝ) := by
    exact Nat.cast_le.mpr hk

  /-
  By construction,

      k ≤ |b_k|.
  -/
  have hkLarge :
      (k : ℝ) ≤
        |b a hUnbounded k| := by
    exact b_large
      a
      hUnbounded
      k

  have hJLarge :
      (J : ℝ) ≤
        |b a hUnbounded k| := by
    exact le_trans hJkR hkLarge

  have habsPos :
      0 < |b a hUnbounded k| := by
    exact lt_of_lt_of_le
      hJposR
      hJLarge

  /-
  From

      1/ε < J

  obtain

      1 < εJ.
  -/
  have hOneJ :
      (1 : ℝ) < (J : ℝ) * ε := by
    exact
      (div_lt_iff₀ hε).mp hJ

  have hOneJ' :
      (1 : ℝ) < ε * (J : ℝ) := by
    simpa [mul_comm] using hOneJ

  /-
  Since J ≤ |b_k| and ε > 0,

      εJ ≤ ε|b_k|.
  -/
  have hMul :
      ε * (J : ℝ)
        ≤ ε * |b a hUnbounded k| := by

    exact mul_le_mul_of_nonneg_left
      hJLarge
      (le_of_lt hε)

  have hOneAbs :
      (1 : ℝ)
        < ε * |b a hUnbounded k| := by

    exact lt_of_lt_of_le
      hOneJ'
      hMul

  /-
  This is exactly the orientation required by
  `div_lt_iff₀` in this Mathlib version:

      1 / |b_k| < ε
        ↔
      1 < ε * |b_k|.
  -/
  have hRec :
      (1 : ℝ) / |b a hUnbounded k| < ε := by

    exact
      (div_lt_iff₀ habsPos).2
        hOneAbs

  have hRecLe :
      (1 : ℝ) / |b a hUnbounded k| ≤ ε := by

    exact le_of_lt hRec

  /-
      |1 / b_k| = 1 / |b_k|.
  -/
  have hAbs :
      |1 / b a hUnbounded k|
        =
      (1 : ℝ) / |b a hUnbounded k| := by

    rw [abs_div]

    norm_num

  have hFinal :
      |1 / b a hUnbounded k| ≤ ε := by

    rw [hAbs]

    exact hRecLe

  /-
  The target is

      |1 / b_k - 0| ≤ ε.
  -/
  simpa using hFinal


/-!
============================================================
Exercise 6.6.3
============================================================
-/

theorem exercise_6_6_3
    (a : ℕ → ℝ)
    (hUnbounded : ¬ IsBounded a) :
    ∃ bseq : ℕ → ℝ,
      IsSubsequence a bseq
      ∧
      ConvergesFrom
        (fun n : ℕ =>
          1 / bseq n)
        0
        0 := by

  refine
    ⟨b a hUnbounded, ?_, ?_⟩

  · exact b_is_subsequence
      a
      hUnbounded

  · exact reciprocal_b_converges_zero
      a
      hUnbounded

end TaoExercise6_6_3
