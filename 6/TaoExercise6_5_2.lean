import Mathlib

namespace TaoExercise6_5_2

/-!
============================================================
Definitions
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


def DivergesFrom
    (a : ℕ → ℝ)
    (m : ℕ) : Prop :=
  ¬ ∃ L : ℝ, ConvergesFrom a m L


/-!
============================================================
Convert Mathlib's filter convergence into our ε-N definition
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
Uniqueness of limits
============================================================
-/

theorem limit_unique
    (a : ℕ → ℝ)
    (m : ℕ)
    (L K : ℝ)
    (hL : ConvergesFrom a m L)
    (hK : ConvergesFrom a m K) :
    L = K := by

  by_contra hLK

  have hd :
      0 < |L - K| := by
    exact abs_pos.mpr (sub_ne_zero.mpr hLK)

  have hε :
      0 < |L - K| / 3 := by
    positivity

  obtain ⟨N₁, hmN₁, hClose₁⟩ :=
    hL (|L - K| / 3) hε

  obtain ⟨N₂, hmN₂, hClose₂⟩ :=
    hK (|L - K| / 3) hε

  let N : ℕ := max N₁ N₂

  have hN₁N :
      N₁ ≤ N := by
    exact le_max_left N₁ N₂

  have hN₂N :
      N₂ ≤ N := by
    exact le_max_right N₁ N₂

  have hclose₁ :
      |a N - L| ≤ |L - K| / 3 := by
    exact hClose₁ N hN₁N

  have hclose₂ :
      |a N - K| ≤ |L - K| / 3 := by
    exact hClose₂ N hN₂N

  have hclose₁' :
      |L - a N| ≤ |L - K| / 3 := by
    simpa [abs_sub_comm] using hclose₁

  have hdecomp :
      L - K =
        (L - a N) + (a N - K) := by
    ring

  have htriangle :
      |L - K| ≤
        |L - a N| + |a N - K| := by
    rw [hdecomp]
    exact abs_add_le _ _

  have hupper :
      |L - K| ≤
        |L - K| / 3 + |L - K| / 3 := by
    exact le_trans
      htriangle
      (add_le_add hclose₁' hclose₂)

  linarith


/-!
============================================================
Finite shift preserves a limit
============================================================
-/

theorem converges_shift_one
    (a : ℕ → ℝ)
    (m : ℕ)
    (L : ℝ)
    (hconv : ConvergesFrom a m L) :
    ConvergesFrom
      (fun n => a (n + 1))
      m
      L := by

  intro ε hε

  obtain ⟨N, hmN, hN⟩ :=
    hconv ε hε

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

    have hNsucc :
        N ≤ n + 1 := by
      omega

    exact hN (n + 1) hNsucc


/-!
============================================================
Multiplication by a constant preserves convergence
============================================================
-/

theorem converges_const_mul
    (a : ℕ → ℝ)
    (m : ℕ)
    (L c : ℝ)
    (hconv : ConvergesFrom a m L) :
    ConvergesFrom
      (fun n => c * a n)
      m
      (c * L) := by

  by_cases hc : c = 0

  · subst c

    intro ε hε

    refine ⟨m, le_rfl, ?_⟩

    intro n hn

    simp [le_of_lt hε]

  · have habsc :
        0 < |c| := by
      exact abs_pos.mpr hc

    intro ε hε

    have hδ :
        0 < ε / |c| := by
      exact div_pos hε habsc

    obtain ⟨N, hmN, hN⟩ :=
      hconv (ε / |c|) hδ

    refine ⟨N, hmN, ?_⟩

    intro n hn

    have hclose :
        |a n - L| ≤ ε / |c| := by
      exact hN n hn

    have halgebra :
        c * a n - c * L =
          c * (a n - L) := by
      ring

    rw [halgebra, abs_mul]

    calc
      |c| * |a n - L|
          ≤ |c| * (ε / |c|) := by
            exact mul_le_mul_of_nonneg_left
              hclose
              (abs_nonneg c)

      _ = ε := by
            field_simp [ne_of_gt habsc]


/-!
============================================================
If 1 ≤ |x|, then every |x^n| is at least 1
============================================================
-/

theorem one_le_abs_pow
    (x : ℝ)
    (hx : 1 ≤ |x|) :
    ∀ n : ℕ,
      1 ≤ |x ^ n| := by

  intro n

  induction n with

  | zero =>
      norm_num

  | succ n ih =>

      rw [pow_succ, abs_mul]

      have hnonneg :
          0 ≤ |x ^ n| := by
        exact abs_nonneg _

      calc
        (1 : ℝ)
            = 1 * 1 := by
              ring

        _ ≤ |x ^ n| * |x| := by
              exact mul_le_mul
                ih
                hx
                (by norm_num)
                hnonneg


/-!
============================================================
If |x| < 1, then x^n -> 0
============================================================
-/

theorem pow_converges_zero_of_abs_lt_one
    (x : ℝ)
    (hx : |x| < 1) :
    ConvergesFrom
      (fun n : ℕ => x ^ n)
      1
      0 := by

  have ht :
      Filter.Tendsto
        (fun n : ℕ => x ^ n)
        Filter.atTop
        (nhds 0) := by
    exact tendsto_pow_atTop_nhds_zero_of_abs_lt_one hx

  exact convergesFrom_of_tendsto
    (fun n : ℕ => x ^ n)
    1
    0
    ht


/-!
============================================================
If x = 1, then x^n -> 1
============================================================
-/

theorem pow_converges_one_of_eq_one
    (x : ℝ)
    (hx : x = 1) :
    ConvergesFrom
      (fun n : ℕ => x ^ n)
      1
      1 := by

  subst x

  intro ε hε

  refine ⟨1, le_rfl, ?_⟩

  intro n hn

  simp [le_of_lt hε]


/-!
============================================================
Main divergence lemma

If

    1 ≤ |x|

and

    x ≠ 1,

then x^n cannot converge to a real number.

This simultaneously handles:
* x = -1
* x > 1
* x < -1.
============================================================
-/

theorem pow_diverges_of_one_le_abs
    (x : ℝ)
    (hxabs : 1 ≤ |x|)
    (hx1 : x ≠ 1) :
    DivergesFrom
      (fun n : ℕ => x ^ n)
      1 := by

  unfold DivergesFrom

  rintro ⟨L, hconv⟩

  /-
  x^(n+1) -> L, since shifting does not change the limit.
  -/
  have hshift :
      ConvergesFrom
        (fun n : ℕ => x ^ (n + 1))
        1
        L := by

    exact converges_shift_one
      (fun n : ℕ => x ^ n)
      1
      L
      hconv

  /-
  x * x^n -> xL.
  -/
  have hscaled :
      ConvergesFrom
        (fun n : ℕ => x * x ^ n)
        1
        (x * L) := by

    exact converges_const_mul
      (fun n : ℕ => x ^ n)
      1
      L
      x
      hconv

  /-
  But x * x^n = x^(n+1).
  -/
  have hshiftScaled :
      ConvergesFrom
        (fun n : ℕ => x ^ (n + 1))
        1
        (x * L) := by

    simpa [pow_succ, mul_comm] using hscaled

  /-
  Hence uniqueness gives

      L = xL.
  -/
  have hL :
      L = x * L := by

    exact limit_unique
      (fun n : ℕ => x ^ (n + 1))
      1
      L
      (x * L)
      hshift
      hshiftScaled

  /-
  Since x ≠ 1, this forces L = 0.
  -/
  have hxminus :
      x - 1 ≠ 0 := by
    exact sub_ne_zero.mpr hx1

  have hfactor :
      (x - 1) * L = 0 := by
    nlinarith [hL]

  have hLzero :
      L = 0 := by

    rcases mul_eq_zero.mp hfactor with hxzero | hLzero

    · exact False.elim (hxminus hxzero)

    · exact hLzero

  /-
  But |x^n| ≥ 1 for every n.
  Convergence to 0 would eventually force |x^n| ≤ 1/2.
  -/
  have hpowers :
      ∀ n : ℕ,
        1 ≤ |x ^ n| := by
    exact one_le_abs_pow x hxabs

  have hhalf :
      (0 : ℝ) < 1 / 2 := by
    norm_num

  obtain ⟨N, h1N, hN⟩ :=
    hconv (1 / 2) hhalf

  have hclose :
      |x ^ N - L| ≤ (1 : ℝ) / 2 := by
    exact hN N le_rfl

  rw [hLzero, sub_zero] at hclose

  have hlower :
      (1 : ℝ) ≤ |x ^ N| := by
    exact hpowers N

  linarith


/-!
============================================================
x = -1 diverges
============================================================
-/

theorem pow_neg_one_diverges :
    DivergesFrom
      (fun n : ℕ => (-1 : ℝ) ^ n)
      1 := by

  apply pow_diverges_of_one_le_abs (-1)

  · norm_num

  · norm_num


/-!
============================================================
If |x| > 1, then x^n diverges
============================================================
-/

theorem pow_diverges_of_abs_gt_one
    (x : ℝ)
    (hx : 1 < |x|) :
    DivergesFrom
      (fun n : ℕ => x ^ n)
      1 := by

  have hxabs :
      1 ≤ |x| := by
    exact le_of_lt hx

  have hx1 :
      x ≠ 1 := by
    intro h

    subst x

    norm_num at hx

  exact pow_diverges_of_one_le_abs
    x
    hxabs
    hx1


/-!
============================================================
Special cases x > 1 and x < -1
============================================================
-/

theorem pow_diverges_of_one_lt
    (x : ℝ)
    (hx : 1 < x) :
    DivergesFrom
      (fun n : ℕ => x ^ n)
      1 := by

  apply pow_diverges_of_abs_gt_one x

  have hxpos :
      0 < x := by
    linarith

  rw [abs_of_pos hxpos]

  exact hx


theorem pow_diverges_of_lt_neg_one
    (x : ℝ)
    (hx : x < -1) :
    DivergesFrom
      (fun n : ℕ => x ^ n)
      1 := by

  apply pow_diverges_of_abs_gt_one x

  have hxneg :
      x < 0 := by
    linarith

  rw [abs_of_neg hxneg]

  linarith


/-!
============================================================
Lemma 6.5.2
============================================================

This packages exactly the cases in Tao:

* |x| < 1  -> x^n -> 0
* x = 1    -> x^n -> 1
* x = -1   -> divergence
* |x| > 1  -> divergence
-/

theorem lemma_6_5_2
    (x : ℝ) :
    (|x| < 1 →
      ConvergesFrom
        (fun n : ℕ => x ^ n)
        1
        0)
    ∧
    (x = 1 →
      ConvergesFrom
        (fun n : ℕ => x ^ n)
        1
        1)
    ∧
    (x = -1 →
      DivergesFrom
        (fun n : ℕ => x ^ n)
        1)
    ∧
    (1 < |x| →
      DivergesFrom
        (fun n : ℕ => x ^ n)
        1) := by

  constructor

  · intro hx
    exact pow_converges_zero_of_abs_lt_one x hx

  constructor

  · intro hx
    exact pow_converges_one_of_eq_one x hx

  constructor

  · intro hx

    subst x

    exact pow_neg_one_diverges

  · intro hx

    exact pow_diverges_of_abs_gt_one
      x
      hx


/-!
============================================================
Exercise 6.5.2
============================================================
-/

theorem exercise_6_5_2
    (x : ℝ) :
    (|x| < 1 →
      ConvergesFrom
        (fun n : ℕ => x ^ n)
        1
        0)
    ∧
    (x = 1 →
      ConvergesFrom
        (fun n : ℕ => x ^ n)
        1
        1)
    ∧
    (x = -1 →
      DivergesFrom
        (fun n : ℕ => x ^ n)
        1)
    ∧
    (1 < |x| →
      DivergesFrom
        (fun n : ℕ => x ^ n)
        1) := by

  exact lemma_6_5_2 x

end TaoExercise6_5_2
