import Mathlib

namespace TaoExercise11_6_4

open Set
open MeasureTheory
open Filter
open Topology
open intervalIntegral

/-!
============================================================
The set of natural numbers inside ℝ
============================================================
-/

def natPoints : Set ℝ :=
  Set.range (fun n : ℕ => (n : ℝ))


lemma natPoints_countable :
    natPoints.Countable := by
  exact Set.countable_range (fun n : ℕ => (n : ℝ))


/-!
============================================================
First counterexample

f₁(x) = 0 at natural numbers,
f₁(x) = 1 otherwise.

Then Σ f₁(n) converges, but the interval integrals
are unbounded.
============================================================
-/

noncomputable def f₁ (x : ℝ) : ℝ := by
  classical
  exact if x ∈ natPoints then 0 else 1


lemma f₁_nat
    (n : ℕ) :
    f₁ (n : ℝ) = 0 := by

  unfold f₁

  have hn :
      (n : ℝ) ∈ natPoints := by
    exact ⟨n, rfl⟩

  simp [hn]


lemma f₁_ae_one :
    f₁ =ᵐ[volume] (fun _ : ℝ => 1) := by

  have hnot :
      ∀ᵐ x : ℝ ∂volume,
        x ∉ natPoints := by
    exact natPoints_countable.ae_notMem volume

  filter_upwards [hnot] with x hx

  unfold f₁

  simp [hx]


theorem f₁_series_summable :
    Summable
      (fun n : ℕ =>
        f₁ (n : ℝ)) := by

  have hfun :
      (fun n : ℕ =>
        f₁ (n : ℝ))
      =
      (fun _ : ℕ => (0 : ℝ)) := by

    funext n

    exact f₁_nat n

  rw [hfun]

  exact summable_zero


theorem integral_f₁
    (N : ℕ) :
    (∫ x in (0 : ℝ)..(N : ℝ), f₁ x)
      =
    (N : ℝ) := by

  calc
    (∫ x in (0 : ℝ)..(N : ℝ), f₁ x)
        =
      ∫ x in (0 : ℝ)..(N : ℝ), (1 : ℝ) := by

        apply intervalIntegral.integral_congr_ae

        filter_upwards [f₁_ae_one] with x hx

        intro _hxInterval

        exact hx

    _ =
      (N : ℝ) := by

      simp


theorem f₁_integrals_not_bddAbove :
    ¬ BddAbove
      (Set.range
        (fun N : ℕ =>
          ∫ x in (0 : ℝ)..(N : ℝ), f₁ x)) := by

  intro hbdd

  obtain ⟨B, hB⟩ := hbdd

  obtain ⟨N, hN⟩ :=
    exists_nat_gt B

  have hle :
      (∫ x in (0 : ℝ)..(N : ℝ), f₁ x)
        ≤
      B := by

    exact hB
      (Set.mem_range_self N)

  rw [integral_f₁ N] at hle

  exact (not_le_of_gt hN) hle


/-!
============================================================
Second counterexample

f₂(x) = 1 at natural numbers,
f₂(x) = 0 otherwise.

Then every interval integral is zero,
but Σ f₂(n) diverges.
============================================================
-/

noncomputable def f₂ (x : ℝ) : ℝ := by
  classical
  exact if x ∈ natPoints then 1 else 0


lemma f₂_nat
    (n : ℕ) :
    f₂ (n : ℝ) = 1 := by

  unfold f₂

  have hn :
      (n : ℝ) ∈ natPoints := by
    exact ⟨n, rfl⟩

  simp [hn]


lemma f₂_ae_zero :
    f₂ =ᵐ[volume] (fun _ : ℝ => 0) := by

  have hnot :
      ∀ᵐ x : ℝ ∂volume,
        x ∉ natPoints := by
    exact natPoints_countable.ae_notMem volume

  filter_upwards [hnot] with x hx

  unfold f₂

  simp [hx]


theorem integral_f₂
    (N : ℕ) :
    (∫ x in (0 : ℝ)..(N : ℝ), f₂ x)
      =
    0 := by

  calc
    (∫ x in (0 : ℝ)..(N : ℝ), f₂ x)
        =
      ∫ x in (0 : ℝ)..(N : ℝ), (0 : ℝ) := by

        apply intervalIntegral.integral_congr_ae

        filter_upwards [f₂_ae_zero] with x hx

        intro _hxInterval

        exact hx

    _ = 0 := by

      exact intervalIntegral.integral_zero


theorem f₂_integrals_bddAbove :
    BddAbove
      (Set.range
        (fun N : ℕ =>
          ∫ x in (0 : ℝ)..(N : ℝ), f₂ x)) := by

  refine ⟨0, ?_⟩

  intro y hy

  obtain ⟨N, rfl⟩ := hy

  change
    (∫ x in (0 : ℝ)..(N : ℝ), f₂ x)
      ≤ 0

  rw [integral_f₂ N]


theorem f₂_series_not_summable :
    ¬ Summable
      (fun n : ℕ =>
        f₂ (n : ℝ)) := by

  intro hsum

  have hzero :
      Tendsto
        (fun n : ℕ =>
          f₂ (n : ℝ))
        atTop
        (𝓝 0) := by

    exact hsum.tendsto_atTop_zero

  have hone :
      Tendsto
        (fun n : ℕ =>
          f₂ (n : ℝ))
        atTop
        (𝓝 1) := by

    have hconst :
        Tendsto
          (fun _ : ℕ => (1 : ℝ))
          atTop
          (𝓝 1) := by

      exact tendsto_const_nhds

    simpa only [f₂_nat] using hconst

  have h01 :
      (0 : ℝ) = 1 := by

    exact tendsto_nhds_unique
      hzero
      hone

  norm_num at h01


/-!
============================================================
Exercise 11.6.4
============================================================
-/

theorem exercise_11_6_4 :
    (Summable
        (fun n : ℕ =>
          f₁ (n : ℝ))
      ∧
      ¬ BddAbove
        (Set.range
          (fun N : ℕ =>
            ∫ x in (0 : ℝ)..(N : ℝ), f₁ x)))
      ∧
    (¬ Summable
        (fun n : ℕ =>
          f₂ (n : ℝ))
      ∧
      BddAbove
        (Set.range
          (fun N : ℕ =>
            ∫ x in (0 : ℝ)..(N : ℝ), f₂ x))) := by

  constructor

  · exact ⟨
      f₁_series_summable,
      f₁_integrals_not_bddAbove
    ⟩

  · exact ⟨
      f₂_series_not_summable,
      f₂_integrals_bddAbove
    ⟩

end TaoExercise11_6_4
