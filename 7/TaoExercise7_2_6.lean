import Mathlib

namespace TaoExercise7_2_6

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


def telescopingPartialSum
    (a : ℕ → ℝ)
    (N : ℕ) : ℝ :=
  (Finset.range (N + 1)).sum
    (fun n => a n - a (n + 1))


theorem sum_range_telescoping
    (a : ℕ → ℝ)
    (N : ℕ) :
    (Finset.range N).sum
        (fun n => a n - a (n + 1))
      =
    a 0 - a N := by

  induction N with

  | zero =>
      simp

  | succ N ih =>

      rw [Finset.sum_range_succ]

      rw [ih]

      ring


theorem telescopingPartialSum_formula
    (a : ℕ → ℝ)
    (N : ℕ) :
    telescopingPartialSum a N
      =
    a 0 - a (N + 1) := by

  unfold telescopingPartialSum

  exact sum_range_telescoping
    a
    (N + 1)


theorem telescopingPartialSum_converges
    (a : ℕ → ℝ)
    (ha : ConvergesFrom a 0 0) :
    ConvergesFrom
      (telescopingPartialSum a)
      0
      (a 0) := by

  intro ε hε

  obtain ⟨M, h0M, hM⟩ :=
    ha ε hε

  refine ⟨M, h0M, ?_⟩

  intro N hMN

  have hMsucc :
      M ≤ N + 1 := by
    omega

  have hclose :
      |a (N + 1) - 0| ≤ ε := by

    exact hM
      (N + 1)
      hMsucc

  have hclose' :
      |a (N + 1)| ≤ ε := by

    simpa using hclose

  rw [telescopingPartialSum_formula]

  have hdiff :
      (a 0 - a (N + 1)) - a 0
        =
      -a (N + 1) := by

    ring

  rw [hdiff, abs_neg]

  exact hclose'


def TelescopingSeriesHasSum
    (a : ℕ → ℝ)
    (L : ℝ) : Prop :=
  ConvergesFrom
    (fun N =>
      (Finset.range (N + 1)).sum
        (fun n => a n - a (n + 1)))
    0
    L


theorem lemma_7_2_15
    (a : ℕ → ℝ)
    (ha : ConvergesFrom a 0 0) :
    TelescopingSeriesHasSum
      a
      (a 0) := by

  unfold TelescopingSeriesHasSum

  change
    ConvergesFrom
      (telescopingPartialSum a)
      0
      (a 0)

  exact telescopingPartialSum_converges
    a
    ha


theorem exercise_7_2_6
    (a : ℕ → ℝ)
    (ha : ConvergesFrom a 0 0) :
    TelescopingSeriesHasSum
      a
      (a 0) := by

  exact lemma_7_2_15
    a
    ha

end TaoExercise7_2_6
