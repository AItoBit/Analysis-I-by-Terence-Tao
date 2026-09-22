import Mathlib

namespace TaoExercise6_5_3

/-!
============================================================
Definition of convergence used in the previous exercises
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


/-!
============================================================
The nth-root sequence

For n ≥ 1,

    nthRootSeq x n = x^(1/n).

Here `^` is `Real.rpow`, because the exponent is real.
============================================================
-/

noncomputable def nthRootSeq
    (x : ℝ)
    (n : ℕ) : ℝ :=
  x ^ ((n : ℝ)⁻¹)


/-!
============================================================
Conversion from Mathlib's filter convergence
to our ε-N definition.
============================================================
-/

theorem convergesFrom_of_tendsto
    (a : ℕ → ℝ)
    (m : ℕ)
    (L : ℝ)
    (h :
      Filter.Tendsto
        a
        Filter.atTop
        (nhds L)) :
    ConvergesFrom a m L := by

  intro ε hε

  obtain ⟨N, hN⟩ :=
    (Metric.tendsto_atTop.mp h) ε hε

  let M : ℕ := max m N

  refine ⟨M, ?_, ?_⟩

  · exact le_max_left m N

  · intro n hn

    have hNM :
        N ≤ M := by
      exact le_max_right m N

    have hNn :
        N ≤ n := by
      exact le_trans hNM hn

    have hd :
        dist (a n) L < ε := by
      exact hN n hNn

    have hdle :
        dist (a n) L ≤ ε := by
      exact le_of_lt hd

    simpa [Real.dist_eq] using hdle


/-!
============================================================
1/n tends to 0.
============================================================
-/

theorem invNat_tendsto_zero :
    Filter.Tendsto
      (fun n : ℕ => ((n : ℝ)⁻¹))
      Filter.atTop
      (nhds 0) := by

  exact tendsto_inv_atTop_nhds_zero_nat


/-!
============================================================
For a fixed positive x, y ↦ x^y is continuous at 0.
============================================================
-/

theorem const_rpow_tendsto_at_zero
    (x : ℝ)
    (hx : 0 < x) :
    Filter.Tendsto
      (fun y : ℝ => x ^ y)
      (nhds 0)
      (nhds 1) := by

  have hx0 :
      x ≠ 0 := by
    exact ne_of_gt hx

  have hcont :
      ContinuousAt
        (fun y : ℝ => x ^ y)
        0 := by
    exact Real.continuousAt_const_rpow hx0

  have ht :
      Filter.Tendsto
        (fun y : ℝ => x ^ y)
        (nhds 0)
        (nhds (x ^ (0 : ℝ))) := by
    exact hcont

  simpa using ht


/-!
============================================================
Main filter result:

    x^(1/n) -> 1

for x > 0.
============================================================
-/

theorem nthRoot_tendsto_one
    (x : ℝ)
    (hx : 0 < x) :
    Filter.Tendsto
      (fun n : ℕ => x ^ ((n : ℝ)⁻¹))
      Filter.atTop
      (nhds 1) := by

  have hpow :
      Filter.Tendsto
        (fun y : ℝ => x ^ y)
        (nhds 0)
        (nhds 1) :=
    const_rpow_tendsto_at_zero x hx

  have hinv :
      Filter.Tendsto
        (fun n : ℕ => ((n : ℝ)⁻¹))
        Filter.atTop
        (nhds 0) :=
    invNat_tendsto_zero

  exact hpow.comp hinv


/-!
============================================================
Lemma 6.5.3

For every positive real x,

        lim x^(1/n) = 1.
============================================================
-/

theorem lemma_6_5_3
    (x : ℝ)
    (hx : 0 < x) :
    ConvergesFrom
      (nthRootSeq x)
      1
      1 := by

  have ht :
      Filter.Tendsto
        (nthRootSeq x)
        Filter.atTop
        (nhds 1) := by

    unfold nthRootSeq

    exact nthRoot_tendsto_one x hx

  exact convergesFrom_of_tendsto
    (nthRootSeq x)
    1
    1
    ht


/-!
============================================================
Exercise 6.5.3, written without the auxiliary definition
============================================================
-/

theorem exercise_6_5_3
    (x : ℝ)
    (hx : 0 < x) :
    ConvergesFrom
      (fun n : ℕ =>
        x ^ ((n : ℝ)⁻¹))
      1
      1 := by

  have h :=
    lemma_6_5_3 x hx

  simpa [nthRootSeq] using h

end TaoExercise6_5_3
