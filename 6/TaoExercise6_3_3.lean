import Mathlib

namespace TaoExercise6_3_3

/--
A real sequence converges to `L` starting from index `m`.
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
A sequence is bounded from index `m` onward.
-/
def IsBoundedFrom
    (a : ℕ → ℝ)
    (m : ℕ) : Prop :=
  ∃ B : ℝ,
    ∀ n : ℕ,
      m ≤ n →
      |a n| ≤ B


/--
The set of values of the sequence from index `m` onward.
-/
def seqSet
    (a : ℕ → ℝ)
    (m : ℕ) : Set ℝ :=
  {x | ∃ n : ℕ, m ≤ n ∧ x = a n}


/--
The supremum of the sequence from index `m` onward.
-/
noncomputable def seqSup
    (a : ℕ → ℝ)
    (m : ℕ) : ℝ :=
  sSup (seqSet a m)


/-!
============================================================
Basic properties of the set of sequence values
============================================================
-/

/--
The sequence-value set is nonempty.
-/
theorem seqSet_nonempty
    (a : ℕ → ℝ)
    (m : ℕ) :
    (seqSet a m).Nonempty := by

  refine ⟨a m, ?_⟩

  exact ⟨m, le_rfl, rfl⟩


/--
A bounded sequence gives a set bounded above.
-/
theorem seqSet_bddAbove
    (a : ℕ → ℝ)
    (m : ℕ)
    (hbounded : IsBoundedFrom a m) :
    BddAbove (seqSet a m) := by

  obtain ⟨B, hB⟩ := hbounded

  refine ⟨B, ?_⟩

  intro x hx

  rcases hx with ⟨n, hn, rfl⟩

  have habs :
      |a n| ≤ B := by
    exact hB n hn

  exact le_trans (le_abs_self (a n)) habs


/-!
============================================================
Every term is below the supremum
============================================================
-/

theorem term_le_seqSup
    (a : ℕ → ℝ)
    (m n : ℕ)
    (hbounded : IsBoundedFrom a m)
    (hn : m ≤ n) :
    a n ≤ seqSup a m := by

  unfold seqSup

  apply le_csSup

  · exact seqSet_bddAbove a m hbounded

  · exact ⟨n, hn, rfl⟩


/-!
============================================================
Stepwise monotonicity implies monotonicity for arbitrary indices
============================================================
-/

theorem increasing_of_steps
    (a : ℕ → ℝ)
    (m : ℕ)
    (hstep :
      ∀ n : ℕ,
        m ≤ n →
        a n ≤ a (n + 1))
    {i j : ℕ}
    (hmi : m ≤ i)
    (hij : i ≤ j) :
    a i ≤ a j := by

  induction j with

  | zero =>
      have hi0 :
          i = 0 := by
        omega

      subst i

      exact le_rfl

  | succ j ih =>

      by_cases hijEq :
          i = j + 1

      /-
      If i = j+1, the conclusion is reflexivity.
      -/
      · subst i
        exact le_rfl

      /-
      Otherwise i ≤ j.
      -/
      · have hij' :
            i ≤ j := by
          omega

        have hmi_j :
            m ≤ j := by
          exact le_trans hmi hij'

        have hbefore :
            a i ≤ a j := by
          exact ih hij'

        have hnext :
            a j ≤ a (j + 1) := by
          exact hstep j hmi_j

        exact le_trans hbefore hnext


/-!
============================================================
A number below the supremum is exceeded by some sequence term
============================================================
-/

theorem exists_term_gt_of_lt_seqSup
    (a : ℕ → ℝ)
    (m : ℕ)
    (hbounded : IsBoundedFrom a m)
    (y : ℝ)
    (hy : y < seqSup a m) :
    ∃ n : ℕ,
      m ≤ n ∧
      y < a n := by

  by_contra h

  /-
  If there is no term above y, then y is an upper bound
  of the set of sequence values.
  -/
  have hUpper :
      ∀ z : ℝ,
        z ∈ seqSet a m →
        z ≤ y := by

    intro z hz

    rcases hz with ⟨n, hn, rfl⟩

    by_contra hny

    have hyn :
        y < a n := by
      exact lt_of_not_ge hny

    exact h ⟨n, hn, hyn⟩

  have hSupLe :
      seqSup a m ≤ y := by

    unfold seqSup

    exact csSup_le
      (seqSet_nonempty a m)
      hUpper

  exact (not_le_of_gt hy) hSupLe


/-!
============================================================
Proposition 6.3.8

An increasing bounded real sequence converges.
============================================================
-/

theorem proposition_6_3_8
    (a : ℕ → ℝ)
    (m : ℕ)
    (hstep :
      ∀ n : ℕ,
        m ≤ n →
        a n ≤ a (n + 1))
    (hbounded : IsBoundedFrom a m) :
    ConvergesFrom
      a
      m
      (seqSup a m) := by

  intro ε hε

  let ℓ : ℝ := seqSup a m

  /-
  Since ε > 0,

      ℓ - ε < ℓ.
  -/
  have hbelow :
      ℓ - ε < ℓ := by
    linarith

  /-
  Since ℓ is the supremum, some term a n₀ lies above ℓ - ε.
  -/
  obtain ⟨n₀, hmn₀, hn₀Lower⟩ :=
    exists_term_gt_of_lt_seqSup
      a
      m
      hbounded
      (ℓ - ε)
      (by
        dsimp [ℓ]
        exact hbelow)

  refine ⟨n₀, hmn₀, ?_⟩

  intro n hn

  /-
  Since the sequence is increasing,

      a n₀ ≤ a n.
  -/
  have hn₀n :
      a n₀ ≤ a n := by

    exact increasing_of_steps
      a
      m
      hstep
      hmn₀
      hn

  /-
  Every term is at most ℓ.
  -/
  have hnUpper :
      a n ≤ ℓ := by

    dsimp [ℓ]

    exact term_le_seqSup
      a
      m
      n
      hbounded
      (le_trans hmn₀ hn)

  /-
  Combining

      ℓ - ε < a n₀ ≤ a n ≤ ℓ

  gives

      -ε ≤ a n - ℓ ≤ ε.
  -/
  have hnLower :
      ℓ - ε ≤ a n := by
    exact le_trans
      (le_of_lt hn₀Lower)
      hn₀n

  apply abs_le.mpr

  constructor

  · linarith

  · linarith


/-!
============================================================
Exercise wrapper
============================================================
-/

theorem exercise_6_3_3
    (a : ℕ → ℝ)
    (m : ℕ)
    (hstep :
      ∀ n : ℕ,
        m ≤ n →
        a n ≤ a (n + 1))
    (hbounded :
      ∃ B : ℝ,
        ∀ n : ℕ,
          m ≤ n →
          |a n| ≤ B) :
    ConvergesFrom
      a
      m
      (seqSup a m) := by

  exact proposition_6_3_8
    a
    m
    hstep
    hbounded

end TaoExercise6_3_3
