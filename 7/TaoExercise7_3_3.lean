import Mathlib

namespace TaoExercise7_3_3

def partialSum
    (a : ℕ → ℝ)
    (N : ℕ) : ℝ :=
  (Finset.range (N + 1)).sum a

def SeriesHasSum
    (a : ℕ → ℝ)
    (L : ℝ) : Prop :=
  Filter.Tendsto
    (partialSum a)
    Filter.atTop
    (nhds L)

def AbsolutelyConverges
    (a : ℕ → ℝ) : Prop :=
  ∃ L : ℝ,
    SeriesHasSum
      (fun n => abs (a n))
      L

theorem abs_term_le_partialSum_abs
    (a : ℕ → ℝ)
    (m N : ℕ)
    (hmN : m ≤ N) :
    abs (a m)
      ≤
    partialSum
      (fun n => abs (a n))
      N := by

  unfold partialSum

  have hmMem :
      m ∈ Finset.range (N + 1) := by

    rw [Finset.mem_range]

    omega

  have hnonneg :
      ∀ i ∈ Finset.range (N + 1),
        0 ≤ abs (a i) := by

    intro i hi

    exact abs_nonneg (a i)

  exact Finset.single_le_sum
    hnonneg
    hmMem


theorem lemma_7_3_3
    (a : ℕ → ℝ)
    (habs : AbsolutelyConverges a)
    (hsum :
      SeriesHasSum
        (fun n => abs (a n))
        0) :
    ∀ n : ℕ, a n = 0 := by

  intro m

  by_contra ham

  have habsPos :
      0 < abs (a m) := by

    exact abs_pos.mpr ham

  have hmetric :=
    Metric.tendsto_atTop.mp hsum

  obtain ⟨N₀, hN₀⟩ :=
    hmetric
      (abs (a m) / 2)
      (by
        linarith)

  let N : ℕ :=
    max m N₀

  have hmN :
      m ≤ N := by

    exact le_max_left m N₀

  have hN₀N :
      N₀ ≤ N := by

    exact le_max_right m N₀

  have hclose :
      dist
        (partialSum
          (fun n => abs (a n))
          N)
        0
        <
      abs (a m) / 2 := by

    exact hN₀
      N
      hN₀N

  have hnonneg :
      0 ≤
        partialSum
          (fun n => abs (a n))
          N := by

    unfold partialSum

    apply Finset.sum_nonneg

    intro i hi

    exact abs_nonneg (a i)

  have hsmall :
      partialSum
          (fun n => abs (a n))
          N
        <
      abs (a m) / 2 := by

    rw [Real.dist_eq] at hclose

    have habsEq :
        abs
          (
            partialSum
                (fun n => abs (a n))
                N
              -
            0
          )
          =
        partialSum
          (fun n => abs (a n))
          N := by

      rw [sub_zero]

      exact abs_of_nonneg hnonneg

    rw [habsEq] at hclose

    exact hclose

  have hlower :
      abs (a m)
        ≤
      partialSum
        (fun n => abs (a n))
        N := by

    exact abs_term_le_partialSum_abs
      a
      m
      N
      hmN

  linarith


theorem exercise_7_3_3
    (a : ℕ → ℝ)
    (habs : AbsolutelyConverges a)
    (hsum :
      SeriesHasSum
        (fun n => abs (a n))
        0) :
    ∀ n : ℕ, a n = 0 := by

  exact lemma_7_3_3
    a
    habs
    hsum

end TaoExercise7_3_3
