import Mathlib

namespace TaoExercise6_3_2

/--
The set of values attained by the sequence `a`
from index `m` onward.
-/
def seqSet
    (a : ℕ → EReal)
    (m : ℕ) : Set EReal :=
  {x | ∃ n : ℕ, m ≤ n ∧ x = a n}


/--
The supremum of the sequence starting from index `m`.
-/
noncomputable def seqSup
    (a : ℕ → EReal)
    (m : ℕ) : EReal :=
  sSup (seqSet a m)


/-!
============================================================
Part 1

For every n ≥ m,

    a n ≤ sup(a_n).
============================================================
-/

theorem term_le_seqSup
    (a : ℕ → EReal)
    (m n : ℕ)
    (hn : m ≤ n) :
    a n ≤ seqSup a m := by

  unfold seqSup

  apply le_sSup

  exact ⟨n, hn, rfl⟩


/-!
============================================================
Part 2

If M is an upper bound of the sequence, then

    seqSup a m ≤ M.
============================================================
-/

theorem seqSup_le_upper_bound
    (a : ℕ → EReal)
    (m : ℕ)
    (M : EReal)
    (hM :
      ∀ n : ℕ,
        m ≤ n →
        a n ≤ M) :
    seqSup a m ≤ M := by

  unfold seqSup

  apply sSup_le

  intro x hx

  rcases hx with ⟨n, hn, rfl⟩

  exact hM n hn


/-!
============================================================
Part 3

If y < sup(a_n), then there exists n ≥ m such that

    y < a n ≤ sup(a_n).
============================================================
-/

theorem exists_term_gt_of_lt_seqSup
    (a : ℕ → EReal)
    (m : ℕ)
    (y : EReal)
    (hy : y < seqSup a m) :
    ∃ n : ℕ,
      m ≤ n ∧
      y < a n ∧
      a n ≤ seqSup a m := by

  by_contra h

  push Not at h

  /-
  We show that y is an upper bound for the sequence.
  -/
  have hUpper :
      ∀ n : ℕ,
        m ≤ n →
        a n ≤ y := by

    intro n hn

    by_contra hny

    have hyn :
        y < a n := by
      exact lt_of_not_ge hny

    have hanSup :
        a n ≤ seqSup a m := by
      exact term_le_seqSup a m n hn

    /-
    After `push Not at h`, the hypothesis gives

        h n hn hyn : seqSup a m < a n.

    This contradicts `hanSup`.
    -/
    exact (not_lt_of_ge hanSup) (h n hn hyn)

  /-
  Since y is an upper bound, the supremum is ≤ y.
  -/
  have hSupLe :
      seqSup a m ≤ y := by

    exact seqSup_le_upper_bound
      a
      m
      y
      hUpper

  /-
  But we assumed y < sup.
  -/
  exact (not_le_of_gt hy) hSupLe


/-!
============================================================
Simpler existence version

If y < sup(a_n), then some term satisfies

    y < a n.
============================================================
-/

theorem exists_term_gt_of_lt_seqSup'
    (a : ℕ → EReal)
    (m : ℕ)
    (y : EReal)
    (hy : y < seqSup a m) :
    ∃ n : ℕ,
      m ≤ n ∧
      y < a n := by

  obtain ⟨n, hn, hyn, hanSup⟩ :=
    exists_term_gt_of_lt_seqSup
      a
      m
      y
      hy

  exact ⟨n, hn, hyn⟩


/-!
============================================================
Proposition 6.3.6 packaged
============================================================
-/

theorem proposition_6_3_6
    (a : ℕ → EReal)
    (m : ℕ) :
    (∀ n : ℕ,
      m ≤ n →
      a n ≤ seqSup a m)
    ∧
    (∀ M : EReal,
      (∀ n : ℕ,
        m ≤ n →
        a n ≤ M) →
      seqSup a m ≤ M)
    ∧
    (∀ y : EReal,
      y < seqSup a m →
      ∃ n : ℕ,
        m ≤ n ∧
        y < a n ∧
        a n ≤ seqSup a m) := by

  constructor

  /-
  First statement:
  every term lies below the supremum.
  -/
  · intro n hn

    exact term_le_seqSup
      a
      m
      n
      hn

  constructor

  /-
  Second statement:
  the supremum lies below every upper bound.
  -/
  · intro M hM

    exact seqSup_le_upper_bound
      a
      m
      M
      hM

  /-
  Third statement:
  every y below the supremum is exceeded by some term.
  -/
  · intro y hy

    exact exists_term_gt_of_lt_seqSup
      a
      m
      y
      hy

end TaoExercise6_3_2
