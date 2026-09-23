import Mathlib

namespace TaoExercise9_9_1

/-!
============================================================
Sequences starting from n = 1
============================================================

Two sequences are "equivalent" when their difference
eventually becomes arbitrarily small.
-/

def EquivalentFromOne
    (a b : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ,
    0 < ε →
    ∃ N : ℕ,
      1 ≤ N ∧
      ∀ n : ℕ,
        N ≤ n →
        abs (a n - b n) ≤ ε


/-!
============================================================
Convergence from n = 1
============================================================
-/

def ConvergesFromOne
    (a : ℕ → ℝ)
    (L : ℝ) : Prop :=
  ∀ ε : ℝ,
    0 < ε →
    ∃ N : ℕ,
      1 ≤ N ∧
      ∀ n : ℕ,
        N ≤ n →
        abs (a n - L) ≤ ε


/-!
============================================================
Equivalent sequences imply aₙ - bₙ → 0
============================================================
-/

theorem equivalent_implies_difference_tends_zero
    (a b : ℕ → ℝ)
    (h : EquivalentFromOne a b) :
    ConvergesFromOne
      (fun n : ℕ => a n - b n)
      0 := by

  unfold EquivalentFromOne at h
  unfold ConvergesFromOne

  intro ε hε

  obtain ⟨N, hN1, hN⟩ :=
    h ε hε

  refine ⟨N, hN1, ?_⟩

  intro n hn

  have hab :
      abs (a n - b n) ≤ ε := by
    exact hN n hn

  simpa using hab


/-!
============================================================
aₙ - bₙ → 0 implies the sequences are equivalent
============================================================
-/

theorem difference_tends_zero_implies_equivalent
    (a b : ℕ → ℝ)
    (h :
      ConvergesFromOne
        (fun n : ℕ => a n - b n)
        0) :
    EquivalentFromOne a b := by

  unfold ConvergesFromOne at h
  unfold EquivalentFromOne

  intro ε hε

  obtain ⟨N, hN1, hN⟩ :=
    h ε hε

  refine ⟨N, hN1, ?_⟩

  intro n hn

  have hab :
      abs ((a n - b n) - 0) ≤ ε := by
    exact hN n hn

  simpa using hab


/-!
============================================================
Lemma 9.9.7
============================================================

Two sequences aₙ and bₙ are equivalent iff

        aₙ - bₙ → 0.
-/

theorem lemma_9_9_7
    (a b : ℕ → ℝ) :
    EquivalentFromOne a b
      ↔
    ConvergesFromOne
      (fun n : ℕ => a n - b n)
      0 := by

  constructor

  · intro h

    exact equivalent_implies_difference_tends_zero
      a
      b
      h

  · intro h

    exact difference_tends_zero_implies_equivalent
      a
      b
      h


/-!
============================================================
Exercise 9.9.1
============================================================
-/

theorem exercise_9_9_1
    (a b : ℕ → ℝ) :
    EquivalentFromOne a b
      ↔
    ConvergesFromOne
      (fun n : ℕ => a n - b n)
      0 := by

  exact lemma_9_9_7 a b

end TaoExercise9_9_1
