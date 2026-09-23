import Mathlib

namespace TaoExercise11_8_4

open Set

/-!
============================================================
Riemann-Stieltjes integrability

For the purposes of this chapter, integrability means that
the upper and lower Riemann-Stieltjes integrals coincide.
============================================================
-/

def RSIntegrable
    (upperIntegral lowerIntegral : ℝ) : Prop :=
  upperIntegral = lowerIntegral


/-!
============================================================
Abstract oscillation of f on a piece

In Tao's proof this is

  sup_{x ∈ J} f(x) - inf_{x ∈ J} f(x).
============================================================
-/

def OscillationBound
    (osc : Set ℝ → ℝ)
    (P : Finset (Set ℝ))
    (ε : ℝ) : Prop :=
  ∀ J ∈ P,
    osc J ≤ ε


/-!
============================================================
One partition estimate

If

  upper - lower
    ≤ Σ_J osc(J) α[J]

and

  osc(J) ≤ ε
  α[J] ≥ 0,

then

  upper - lower
    ≤ Σ_J ε α[J].
============================================================
-/

lemma gap_le_epsilon_sum
    (upper lower ε : ℝ)
    (alphaContent osc : Set ℝ → ℝ)
    (P : Finset (Set ℝ))
    (hGap :
      upper - lower ≤
        P.sum
          (fun J =>
            osc J * alphaContent J))
    (hOsc :
      ∀ J ∈ P,
        osc J ≤ ε)
    (hAlphaNonneg :
      ∀ J ∈ P,
        0 ≤ alphaContent J) :
    upper - lower ≤
      P.sum
        (fun J =>
          ε * alphaContent J) := by

  refine le_trans hGap ?_

  exact Finset.sum_le_sum
    (fun J hJ => by

      exact mul_le_mul_of_nonneg_right
        (hOsc J hJ)
        (hAlphaNonneg J hJ))


/-!
============================================================
Use Lemma 11.8.4

  Σ_{J∈P} α[J] = α[I]

to simplify the previous estimate.
============================================================
-/

lemma gap_le_epsilon_alphaContent
    (I : Set ℝ)
    (upper lower ε : ℝ)
    (alphaContent osc : Set ℝ → ℝ)
    (P : Finset (Set ℝ))
    (hGap :
      upper - lower ≤
        P.sum
          (fun J =>
            osc J * alphaContent J))
    (hOsc :
      ∀ J ∈ P,
        osc J ≤ ε)
    (hAlphaNonneg :
      ∀ J ∈ P,
        0 ≤ alphaContent J)
    (hAlphaTotal :
      P.sum alphaContent =
        alphaContent I) :
    upper - lower ≤
      ε * alphaContent I := by

  have h1 :
      upper - lower ≤
        P.sum
          (fun J =>
            ε * alphaContent J) := by

    exact gap_le_epsilon_sum
      upper
      lower
      ε
      alphaContent
      osc
      P
      hGap
      hOsc
      hAlphaNonneg

  calc
    upper - lower
        ≤
      P.sum
        (fun J =>
          ε * alphaContent J) := h1

    _ =
      ε * P.sum alphaContent := by

      rw [Finset.mul_sum]

    _ =
      ε * alphaContent I := by

      rw [hAlphaTotal]


/-!
============================================================
Epsilon argument

If

  lower ≤ upper
  0 ≤ A

and

  upper - lower ≤ ε A

for every ε > 0, then upper = lower.
============================================================
-/

lemma eq_of_gap_le_epsilon_mul
    {lower upper A : ℝ}
    (hLowerUpper :
      lower ≤ upper)
    (hA :
      0 ≤ A)
    (hGap :
      ∀ ε : ℝ,
        0 < ε →
        upper - lower ≤ ε * A) :
    upper = lower := by

  by_contra hne

  have hlt :
      lower < upper := by

    exact lt_of_le_of_ne
      hLowerUpper
      (Ne.symm hne)

  have hdiff :
      0 < upper - lower := by

    exact sub_pos.mpr hlt

  have hA1 :
      0 < A + 1 := by

    linarith

  have hden :
      0 < 2 * (A + 1) := by

    positivity

  let ε : ℝ :=
    (upper - lower) /
      (2 * (A + 1))

  have hε :
      0 < ε := by

    dsimp [ε]

    exact div_pos
      hdiff
      hden

  have hbound :
      upper - lower ≤
        ε * A := by

    exact hGap ε hε

  have hstrict :
      ε * A <
        upper - lower := by

    dsimp [ε]

    have hden_ne :
        2 * (A + 1) ≠ 0 := by

      exact ne_of_gt hden

    field_simp [hden_ne]

    nlinarith

  exact
    (not_lt_of_ge hbound)
      hstrict


/-!
============================================================
Abstract Riemann-Stieltjes theorem

This is the exact final part of Tao's proof.

For every ε > 0 we assume that there exists a partition P
such that

  1. α[J] ≥ 0;
  2. Σ α[J] = α[I]      (Lemma 11.8.4);
  3. osc(f,J) ≤ ε;
  4. upper - lower ≤ Σ osc(f,J) α[J].

Then the upper and lower RS integrals coincide.
============================================================
-/

theorem riemannStieltjes_integrable_of_fine_partitions
    (I : Set ℝ)
    (alphaContent osc : Set ℝ → ℝ)
    (upperIntegral lowerIntegral : ℝ)
    (hLowerUpper :
      lowerIntegral ≤ upperIntegral)
    (hAlphaI :
      0 ≤ alphaContent I)
    (hFinePartition :
      ∀ ε : ℝ,
        0 < ε →
        ∃ P : Finset (Set ℝ),
          (∀ J ∈ P,
            0 ≤ alphaContent J)
          ∧
          P.sum alphaContent =
            alphaContent I
          ∧
          (∀ J ∈ P,
            osc J ≤ ε)
          ∧
          upperIntegral - lowerIntegral
            ≤
          P.sum
            (fun J =>
              osc J * alphaContent J)) :
    RSIntegrable
      upperIntegral
      lowerIntegral := by

  unfold RSIntegrable

  apply eq_of_gap_le_epsilon_mul
    hLowerUpper
    hAlphaI

  intro ε hε

  obtain
    ⟨P,
      hAlphaNonneg,
      hAlphaTotal,
      hOsc,
      hPartitionGap⟩ :=
    hFinePartition ε hε

  exact gap_le_epsilon_alphaContent
    I
    upperIntegral
    lowerIntegral
    ε
    alphaContent
    osc
    P
    hPartitionGap
    hOsc
    hAlphaNonneg
    hAlphaTotal


/-!
============================================================
Uniform continuity interface

This packages precisely the one geometric/analytic step in
Theorem 11.5.1:

uniform continuity + bounded interval
        ↓
for every ε > 0 there is a finite partition whose pieces
have oscillation at most ε.

The remainder is completely algebraic and is proved above.
============================================================
-/

theorem theorem_11_8_4
    (I : Set ℝ)
    (f : ℝ → ℝ)
    (alphaContent osc : Set ℝ → ℝ)
    (upperIntegral lowerIntegral : ℝ)

    (hUniform :
      UniformContinuousOn f I)

    (hLowerUpper :
      lowerIntegral ≤ upperIntegral)

    (hAlphaI :
      0 ≤ alphaContent I)

    /-
    This is the partition obtained from uniform continuity
    and the Archimedean principle.
    -/
    (hFinePartition :
      UniformContinuousOn f I →
      ∀ ε : ℝ,
        0 < ε →
        ∃ P : Finset (Set ℝ),
          (∀ J ∈ P,
            0 ≤ alphaContent J)
          ∧
          P.sum alphaContent =
            alphaContent I
          ∧
          (∀ J ∈ P,
            osc J ≤ ε)
          ∧
          upperIntegral - lowerIntegral
            ≤
          P.sum
            (fun J =>
              osc J * alphaContent J)) :
    RSIntegrable
      upperIntegral
      lowerIntegral := by

  exact
    riemannStieltjes_integrable_of_fine_partitions
      I
      alphaContent
      osc
      upperIntegral
      lowerIntegral
      hLowerUpper
      hAlphaI
      (hFinePartition hUniform)


/-!
============================================================
Explicit form of Tao's final estimate

If for every ε > 0,

  upper - lower ≤ ε α[I],

then f is Riemann-Stieltjes integrable.
============================================================
-/

theorem rsIntegrable_of_final_estimate
    (I : Set ℝ)
    (alphaContent : Set ℝ → ℝ)
    (upperIntegral lowerIntegral : ℝ)
    (hLowerUpper :
      lowerIntegral ≤ upperIntegral)
    (hAlphaI :
      0 ≤ alphaContent I)
    (hε :
      ∀ ε : ℝ,
        0 < ε →
        upperIntegral - lowerIntegral
          ≤
        ε * alphaContent I) :
    RSIntegrable
      upperIntegral
      lowerIntegral := by

  unfold RSIntegrable

  exact eq_of_gap_le_epsilon_mul
    hLowerUpper
    hAlphaI
    hε


/-!
============================================================
Exercise 11.8.4
============================================================
-/

theorem exercise_11_8_4
    (I : Set ℝ)
    (f : ℝ → ℝ)
    (alphaContent osc : Set ℝ → ℝ)
    (upperIntegral lowerIntegral : ℝ)
    (hUniform :
      UniformContinuousOn f I)
    (hLowerUpper :
      lowerIntegral ≤ upperIntegral)
    (hAlphaI :
      0 ≤ alphaContent I)
    (hFinePartition :
      UniformContinuousOn f I →
      ∀ ε : ℝ,
        0 < ε →
        ∃ P : Finset (Set ℝ),
          (∀ J ∈ P,
            0 ≤ alphaContent J)
          ∧
          P.sum alphaContent =
            alphaContent I
          ∧
          (∀ J ∈ P,
            osc J ≤ ε)
          ∧
          upperIntegral - lowerIntegral
            ≤
          P.sum
            (fun J =>
              osc J * alphaContent J)) :
    RSIntegrable
      upperIntegral
      lowerIntegral := by

  exact theorem_11_8_4
    I
    f
    alphaContent
    osc
    upperIntegral
    lowerIntegral
    hUniform
    hLowerUpper
    hAlphaI
    hFinePartition

end TaoExercise11_8_4
