import Mathlib

namespace TaoExercise6_3_4

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
A sequence diverges if it has no finite real limit.
-/
def DivergesFrom
    (a : ℕ → ℝ)
    (m : ℕ) : Prop :=
  ¬ ∃ L : ℝ, ConvergesFrom a m L


/--
The geometric sequence `x^n`.
-/
def powSeq
    (x : ℝ)
    (n : ℕ) : ℝ :=
  x ^ n


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

  have hcloseL :
      |a N - L| ≤ |L - K| / 3 := by
    exact hClose₁ N hN₁N

  have hcloseK :
      |a N - K| ≤ |L - K| / 3 := by
    exact hClose₂ N hN₂N

  have hcloseL' :
      |L - a N| ≤ |L - K| / 3 := by
    simpa [abs_sub_comm] using hcloseL

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
    exact le_trans htriangle
      (add_le_add hcloseL' hcloseK)

  linarith


/-!
============================================================
Shifting a convergent sequence preserves its limit
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
Constant multiplication preserves limits
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

  /-
  Case c = 0.
  -/
  · subst c

    intro ε hε

    refine ⟨m, le_rfl, ?_⟩

    intro n hn

    simp [le_of_lt hε]

  /-
  Case c ≠ 0.
  -/
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
If 1 ≤ x, then 1 ≤ x^n
============================================================
-/

theorem one_le_pow_of_one_le
    (x : ℝ)
    (hx : 1 ≤ x) :
    ∀ n : ℕ, 1 ≤ x ^ n := by

  intro n

  induction n with

  | zero =>
      norm_num

  | succ n ih =>

      have hxNonneg :
          0 ≤ x := by
        linarith

      have hpowNonneg :
          0 ≤ x ^ n := by
        positivity

      calc
        (1 : ℝ)
            = 1 * 1 := by
              ring

        _ ≤ x ^ n * x := by
              exact mul_le_mul
                ih
                hx
                (by norm_num)
                hpowNonneg

        _ = x ^ (n + 1) := by
              rw [pow_succ]


/-!
============================================================
Main theorem

If x > 1, then x^n does not converge to a finite real limit.
============================================================
-/

theorem pow_sequence_diverges
    (x : ℝ)
    (hx : 1 < x) :
    DivergesFrom (powSeq x) 1 := by

  unfold DivergesFrom

  rintro ⟨L, hconv⟩

  /-
  The shifted sequence x^(n+1) converges to L.
  -/
  have hshift :
      ConvergesFrom
        (fun n => powSeq x (n + 1))
        1
        L := by

    exact converges_shift_one
      (powSeq x)
      1
      L
      hconv

  /-
  Since x^n → L, multiplying by x gives

      x * x^n → xL.
  -/
  have hscaled :
      ConvergesFrom
        (fun n => x * powSeq x n)
        1
        (x * L) := by

    exact converges_const_mul
      (powSeq x)
      1
      L
      x
      hconv

  /-
  But x * x^n = x^(n+1).
  Hence the shifted sequence also converges to xL.
  -/
  have hshiftScaled :
      ConvergesFrom
        (fun n => powSeq x (n + 1))
        1
        (x * L) := by

    simpa [powSeq, pow_succ, mul_comm] using hscaled

  /-
  By uniqueness of limits,

      L = xL.
  -/
  have hL :
      L = x * L := by

    exact limit_unique
      (fun n => powSeq x (n + 1))
      1
      L
      (x * L)
      hshift
      hshiftScaled

  /-
  Since x > 1, this forces L = 0.
  -/
  have hxne :
      x - 1 ≠ 0 := by
    have hxpos :
        0 < x - 1 := by
      linarith

    exact ne_of_gt hxpos

  have hfactor :
      (x - 1) * L = 0 := by
    nlinarith [hL]

  have hLzero :
      L = 0 := by

    rcases mul_eq_zero.mp hfactor with hxzero | hLzero

    · exact False.elim (hxne hxzero)

    · exact hLzero

  /-
  But every x^n ≥ 1.
  -/
  have hxOne :
      1 ≤ x := by
    exact le_of_lt hx

  have hpow :
      ∀ n : ℕ,
        1 ≤ powSeq x n := by

    intro n

    unfold powSeq

    exact one_le_pow_of_one_le x hxOne n

  /-
  If x^n → 0, eventually |x^n| ≤ 1/2.
  This contradicts x^n ≥ 1.
  -/
  have hhalf :
      (0 : ℝ) < 1 / 2 := by
    norm_num

  obtain ⟨N, hmN, hN⟩ :=
    hconv (1 / 2) hhalf

  have hclose :
      |powSeq x N - L| ≤ (1 : ℝ) / 2 := by
    exact hN N le_rfl

  rw [hLzero, sub_zero] at hclose

  have hpowN :
      1 ≤ powSeq x N := by
    exact hpow N

  have hpowNNonneg :
      0 ≤ powSeq x N := by
    linarith

  rw [abs_of_nonneg hpowNNonneg] at hclose

  linarith


/-!
============================================================
Exercise 6.3.4
============================================================
-/

theorem exercise_6_3_4
    (x : ℝ)
    (hx : 1 < x) :
    ¬ ∃ L : ℝ,
      ConvergesFrom
        (fun n => x ^ n)
        1
        L := by

  intro hExists

  obtain ⟨L, hL⟩ := hExists

  have hPowSeq :
      ConvergesFrom
        (powSeq x)
        1
        L := by

    change
      ConvergesFrom
        (fun n => x ^ n)
        1
        L

    exact hL

  have hdiv :
      DivergesFrom (powSeq x) 1 :=
    pow_sequence_diverges x hx

  unfold DivergesFrom at hdiv

  exact hdiv ⟨L, hPowSeq⟩

end TaoExercise6_3_4
