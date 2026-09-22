import Mathlib

namespace TaoExercises6_1_9_6_1_10

/-
We reuse the same convergence notion as in the previous exercises.
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


/-!
============================================================
Exercise 6.1.9
============================================================

The quotient law cannot be stated with limit denominator 0
because the candidate limit x / 0 is not the intended quotient
limit law.

Nevertheless, the quotient sequence may still converge.
We formalize Tao's example:

    a_n = b_n = 1/(n+1).

Then both sequences converge to 0, while

    a_n / b_n = 1

for every n, so the quotient converges to 1.
-/

def invNatSeq (n : ℕ) : ℝ :=
  1 / (n + 1 : ℝ)


theorem invNatSeq_ne_zero
    (n : ℕ) :
    invNatSeq n ≠ 0 := by

  unfold invNatSeq

  have h :
      (n + 1 : ℝ) ≠ 0 := by
    positivity

  exact one_div_ne_zero h


theorem invNatSeq_div_self
    (n : ℕ) :
    invNatSeq n / invNatSeq n = 1 := by

  exact div_self (invNatSeq_ne_zero n)


theorem quotient_example_converges_to_one
    (m : ℕ) :
    ConvergesFrom
      (fun n => invNatSeq n / invNatSeq n)
      m
      1 := by

  intro ε hε

  refine ⟨m, le_rfl, ?_⟩

  intro n hn

  rw [invNatSeq_div_self]

  simp [le_of_lt hε]


/--
The denominator sequence in Tao's example converges to zero.
-/
theorem invNatSeq_converges_to_zero :
    ConvergesFrom invNatSeq 0 0 := by

  intro ε hε

  obtain ⟨N : ℕ, hN⟩ :=
    exists_nat_gt (1 / ε)

  refine ⟨N, Nat.zero_le N, ?_⟩

  intro n hn

  unfold invNatSeq

  have hεinv :
      0 < 1 / ε := by
    positivity

  have hNposR :
      0 < (N + 1 : ℝ) := by
    positivity

  have hnposR :
      0 < (n + 1 : ℝ) := by
    positivity

  have hNlt :
      1 / ε < (N : ℝ) := by
    exact hN

  have hNlt' :
      1 / ε < (N + 1 : ℝ) := by
    norm_num at *
    linarith

  have hNn :
      (N + 1 : ℝ) ≤ (n + 1 : ℝ) := by
    exact_mod_cast Nat.add_le_add_right hn 1

  have hinv :
      1 / (n + 1 : ℝ) ≤ ε := by

    have hposε :
        0 < ε := hε

    apply (div_le_iff₀ hnposR).2

    have hmul :
        1 ≤ ε * (n + 1 : ℝ) := by

      have hfirst :
          1 < ε * (N + 1 : ℝ) := by
        have :=
          (div_lt_iff₀ hposε).mp hNlt'
        simpa [mul_comm] using this

      have hsecond :
          ε * (N + 1 : ℝ) ≤ ε * (n + 1 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hNn (le_of_lt hε)

      exact le_trans (le_of_lt hfirst) hsecond

    exact hmul

  have hnonneg :
      0 ≤ 1 / (n + 1 : ℝ) := by
    positivity

  rw [sub_zero, abs_of_nonneg hnonneg]

  exact hinv


/--
Tao's counterexample:
both numerator and denominator converge to 0,
but their quotient converges to 1.
-/
theorem exercise_6_1_9_example :
    ConvergesFrom invNatSeq 0 0
    ∧
    ConvergesFrom invNatSeq 0 0
    ∧
    ConvergesFrom
      (fun n => invNatSeq n / invNatSeq n)
      0
      1 := by

  constructor

  · exact invNatSeq_converges_to_zero

  constructor

  · exact invNatSeq_converges_to_zero

  · exact quotient_example_converges_to_one 0


/-!
============================================================
Exercise 6.1.10
============================================================

Eventually ε-close using positive rational ε.
-/

def EventuallyCloseRat
    (a b : ℕ → ℝ) : Prop :=
  ∀ ε : ℚ, 0 < ε →
    ∃ N : ℕ,
      ∀ n : ℕ,
        N ≤ n →
        |a n - b n| ≤ (ε : ℝ)


/--
Eventually ε-close using positive real ε.
-/
def EventuallyCloseReal
    (a b : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ,
      ∀ n : ℕ,
        N ≤ n →
        |a n - b n| ≤ ε


/--
Exercise 6.1.10.

The definition does not change if ε is required to be
positive real instead of positive rational.
-/
theorem exercise_6_1_10
    (a b : ℕ → ℝ) :
    EventuallyCloseRat a b ↔
    EventuallyCloseReal a b := by

  constructor

  /-
  Rational ε -> real ε.

  Given ε > 0 real, choose a positive rational q < ε.
  -/
  · intro hRat

    intro ε hε

    obtain ⟨q : ℚ, hq0, hqε⟩ :=
      exists_pos_rat_lt hε

    obtain ⟨N, hN⟩ :=
      hRat q hq0

    refine ⟨N, ?_⟩

    intro n hn

    have hqclose :
        |a n - b n| ≤ (q : ℝ) := by
      exact hN n hn

    exact le_trans hqclose (le_of_lt hqε)


  /-
  Real ε -> rational ε.

  A positive rational ε is also a positive real ε.
  -/
  · intro hReal

    intro ε hε

    have hεR :
        (0 : ℝ) < (ε : ℝ) := by
      exact_mod_cast hε

    obtain ⟨N, hN⟩ :=
      hReal (ε : ℝ) hεR

    refine ⟨N, ?_⟩

    intro n hn

    exact hN n hn

end TaoExercises6_1_9_6_1_10
