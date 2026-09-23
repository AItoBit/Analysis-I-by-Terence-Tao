import Mathlib

namespace TaoExercise9_9_4

open Filter
open Topology

/-!
============================================================
Sequence convergence
============================================================
-/

def SeqConverges
    (a : ℕ → ℝ)
    (L : ℝ) : Prop :=
  ∀ ε : ℝ,
    0 < ε →
    ∃ N : ℕ,
      ∀ n : ℕ,
        N ≤ n →
        abs (a n - L) < ε


/-!
============================================================
Cauchy sequences
============================================================
-/

def IsCauchySeq
    (a : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ,
    0 < ε →
    ∃ N : ℕ,
      ∀ j k : ℕ,
        N ≤ j →
        N ≤ k →
        abs (a j - a k) < ε


/-!
============================================================
Equivalent sequences
============================================================
-/

def EquivalentSeq
    (a b : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ,
    0 < ε →
    ∃ N : ℕ,
      ∀ n : ℕ,
        N ≤ n →
        abs (a n - b n) < ε


/-!
============================================================
Uniform continuity
============================================================
-/

def UniformContinuousOnTao
    (X : Set ℝ)
    (f : X → ℝ) : Prop :=
  ∀ ε : ℝ,
    0 < ε →
    ∃ δ : ℝ,
      0 < δ ∧
      ∀ x y : X,
        abs ((x : ℝ) - (y : ℝ)) < δ →
        abs (f x - f y) < ε


/-!
============================================================
Sequential formulation of "x₀ is adherent to X"

By Lemma 9.1.14 this is equivalent to

    x₀ ∈ closure X.
============================================================
-/

def IsAdherentPoint
    (X : Set ℝ)
    (x₀ : ℝ) : Prop :=
  ∃ a : ℕ → X,
    SeqConverges
      (fun n : ℕ => (a n : ℝ))
      x₀


/-!
============================================================
Sequential formulation of existence of the limit

This is the condition from Proposition 9.3.9.
============================================================
-/

def HasSequentialLimitAt
    (X : Set ℝ)
    (f : X → ℝ)
    (x₀ : ℝ) : Prop :=
  ∃ L : ℝ,
    ∀ a : ℕ → X,
      SeqConverges
          (fun n : ℕ => (a n : ℝ))
          x₀ →
      SeqConverges
          (fun n : ℕ => f (a n))
          L


/-!
============================================================
A convergent sequence is Cauchy
============================================================
-/

theorem seqConverges_isCauchy
    (a : ℕ → ℝ)
    (L : ℝ)
    (ha : SeqConverges a L) :
    IsCauchySeq a := by

  intro ε hε

  have hhalf :
      0 < ε / 2 := by
    linarith

  obtain ⟨N, hN⟩ :=
    ha (ε / 2) hhalf

  refine ⟨N, ?_⟩

  intro j k hj hk

  have hjL :
      abs (a j - L) < ε / 2 := by
    exact hN j hj

  have hkL :
      abs (a k - L) < ε / 2 := by
    exact hN k hk

  have hLk :
      abs (L - a k) < ε / 2 := by
    have h :
        L - a k = -(a k - L) := by
      ring
    rw [h, abs_neg]
    exact hkL

  have htriangle :
      abs (a j - a k)
        ≤ abs (a j - L) + abs (L - a k) := by

    have h :
        a j - a k =
          (a j - L) + (L - a k) := by
      ring

    rw [h]

    exact abs_add_le _ _

  linarith


/-!
============================================================
A real Cauchy sequence converges
============================================================
-/

theorem cauchySeq_converges_real
    (a : ℕ → ℝ)
    (ha : IsCauchySeq a) :
    ∃ L : ℝ, SeqConverges a L := by

  have hCauchy :
      CauchySeq a := by

    rw [Metric.cauchySeq_iff]

    intro ε hε

    obtain ⟨N, hN⟩ :=
      ha ε hε

    refine ⟨N, ?_⟩

    intro m hm n hn

    have h :
        abs (a m - a n) < ε := by
      exact hN m n hm hn

    simpa [Real.dist_eq] using h

  obtain ⟨L, hL⟩ :=
    cauchySeq_tendsto_of_complete hCauchy

  refine ⟨L, ?_⟩

  intro ε hε

  have hMetric :=
    Metric.tendsto_atTop.mp hL

  obtain ⟨N, hN⟩ :=
    hMetric ε hε

  refine ⟨N, ?_⟩

  intro n hn

  have h :
      dist (a n) L < ε := by
    exact hN n hn

  simpa [Real.dist_eq] using h


/-!
============================================================
Proposition 9.9.12
============================================================
-/

theorem proposition_9_9_12
    (X : Set ℝ)
    (f : X → ℝ)
    (x : ℕ → X)
    (hf : UniformContinuousOnTao X f)
    (hx :
      IsCauchySeq
        (fun n : ℕ => (x n : ℝ))) :
    IsCauchySeq
      (fun n : ℕ => f (x n)) := by

  intro ε hε

  obtain ⟨δ, hδ, hfδ⟩ :=
    hf ε hε

  obtain ⟨N, hN⟩ :=
    hx δ hδ

  refine ⟨N, ?_⟩

  intro j k hj hk

  have hxjk :
      abs ((x j : ℝ) - (x k : ℝ)) < δ := by
    exact hN j k hj hk

  exact hfδ
    (x j)
    (x k)
    hxjk


/-!
============================================================
Two sequences with the same limit are equivalent
============================================================
-/

theorem equivalent_of_same_limit
    (a b : ℕ → ℝ)
    (L : ℝ)
    (ha : SeqConverges a L)
    (hb : SeqConverges b L) :
    EquivalentSeq a b := by

  intro ε hε

  have hhalf :
      0 < ε / 2 := by
    linarith

  obtain ⟨N₁, hN₁⟩ :=
    ha (ε / 2) hhalf

  obtain ⟨N₂, hN₂⟩ :=
    hb (ε / 2) hhalf

  refine ⟨max N₁ N₂, ?_⟩

  intro n hn

  have hn₁ :
      N₁ ≤ n := by
    exact le_trans (le_max_left _ _) hn

  have hn₂ :
      N₂ ≤ n := by
    exact le_trans (le_max_right _ _) hn

  have haL :
      abs (a n - L) < ε / 2 := by
    exact hN₁ n hn₁

  have hbL :
      abs (b n - L) < ε / 2 := by
    exact hN₂ n hn₂

  have hLb :
      abs (L - b n) < ε / 2 := by
    have h :
        L - b n = -(b n - L) := by
      ring
    rw [h, abs_neg]
    exact hbL

  have htriangle :
      abs (a n - b n)
        ≤ abs (a n - L) + abs (L - b n) := by

    have h :
        a n - b n =
          (a n - L) + (L - b n) := by
      ring

    rw [h]

    exact abs_add_le _ _

  linarith


/-!
============================================================
Uniform continuity preserves equivalent sequences
============================================================
-/

theorem uniformContinuous_preserves_equivalent
    (X : Set ℝ)
    (f : X → ℝ)
    (x y : ℕ → X)
    (hf : UniformContinuousOnTao X f)
    (hxy :
      EquivalentSeq
        (fun n : ℕ => (x n : ℝ))
        (fun n : ℕ => (y n : ℝ))) :
    EquivalentSeq
      (fun n : ℕ => f (x n))
      (fun n : ℕ => f (y n)) := by

  intro ε hε

  obtain ⟨δ, hδ, hfδ⟩ :=
    hf ε hε

  obtain ⟨N, hN⟩ :=
    hxy δ hδ

  refine ⟨N, ?_⟩

  intro n hn

  exact hfδ
    (x n)
    (y n)
    (hN n hn)


/-!
============================================================
Equivalent sequences preserve a known limit
============================================================
-/

theorem converges_of_equivalent
    (a b : ℕ → ℝ)
    (L : ℝ)
    (ha : SeqConverges a L)
    (hab : EquivalentSeq a b) :
    SeqConverges b L := by

  intro ε hε

  have hhalf :
      0 < ε / 2 := by
    linarith

  obtain ⟨N₁, hN₁⟩ :=
    ha (ε / 2) hhalf

  obtain ⟨N₂, hN₂⟩ :=
    hab (ε / 2) hhalf

  refine ⟨max N₁ N₂, ?_⟩

  intro n hn

  have hn₁ :
      N₁ ≤ n := by
    exact le_trans (le_max_left _ _) hn

  have hn₂ :
      N₂ ≤ n := by
    exact le_trans (le_max_right _ _) hn

  have haL :
      abs (a n - L) < ε / 2 := by
    exact hN₁ n hn₁

  have habClose :
      abs (a n - b n) < ε / 2 := by
    exact hN₂ n hn₂

  have hbaClose :
      abs (b n - a n) < ε / 2 := by
    have h :
        b n - a n = -(a n - b n) := by
      ring
    rw [h, abs_neg]
    exact habClose

  have htriangle :
      abs (b n - L)
        ≤ abs (b n - a n) + abs (a n - L) := by

    have h :
        b n - L =
          (b n - a n) + (a n - L) := by
      ring

    rw [h]

    exact abs_add_le _ _

  linarith


/-!
============================================================
Corollary 9.9.14
============================================================

A uniformly continuous function has a limit at every
adherent point of its domain.
============================================================
-/

theorem corollary_9_9_14
    (X : Set ℝ)
    (f : X → ℝ)
    (x₀ : ℝ)
    (hf : UniformContinuousOnTao X f)
    (hx₀ : IsAdherentPoint X x₀) :
    HasSequentialLimitAt X f x₀ := by

  rcases hx₀ with ⟨a, haLim⟩

  have haCauchy :
      IsCauchySeq
        (fun n : ℕ => (a n : ℝ)) := by
    exact seqConverges_isCauchy
      (fun n : ℕ => (a n : ℝ))
      x₀
      haLim

  have hfaCauchy :
      IsCauchySeq
        (fun n : ℕ => f (a n)) := by
    exact proposition_9_9_12
      X
      f
      a
      hf
      haCauchy

  obtain ⟨L, hfaLim⟩ :=
    cauchySeq_converges_real
      (fun n : ℕ => f (a n))
      hfaCauchy

  refine ⟨L, ?_⟩

  intro b hbLim

  have hab :
      EquivalentSeq
        (fun n : ℕ => (a n : ℝ))
        (fun n : ℕ => (b n : ℝ)) := by

    exact equivalent_of_same_limit
      (fun n : ℕ => (a n : ℝ))
      (fun n : ℕ => (b n : ℝ))
      x₀
      haLim
      hbLim

  have hfab :
      EquivalentSeq
        (fun n : ℕ => f (a n))
        (fun n : ℕ => f (b n)) := by

    exact uniformContinuous_preserves_equivalent
      X
      f
      a
      b
      hf
      hab

  exact converges_of_equivalent
    (fun n : ℕ => f (a n))
    (fun n : ℕ => f (b n))
    L
    hfaLim
    hfab


/-!
============================================================
Exercise 9.9.4
============================================================
-/

theorem exercise_9_9_4
    (X : Set ℝ)
    (f : X → ℝ)
    (x₀ : ℝ)
    (hf : UniformContinuousOnTao X f)
    (hx₀ : IsAdherentPoint X x₀) :
    HasSequentialLimitAt X f x₀ := by

  exact corollary_9_9_14
    X
    f
    x₀
    hf
    hx₀

end TaoExercise9_9_4
