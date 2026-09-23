import Mathlib

namespace TaoExercise9_3_2

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
        |a n - L| < ε


/-!
============================================================
Function convergence at x₀ within E
============================================================
-/

def ConvergesAtWithin
    (f : ℝ → ℝ)
    (E : Set ℝ)
    (x₀ L : ℝ) : Prop :=
  ∀ ε : ℝ,
    0 < ε →
    ∃ δ : ℝ,
      0 < δ ∧
      ∀ x : ℝ,
        x ∈ E →
        |x - x₀| < δ →
        |f x - L| < ε


/-!
============================================================
SeqConverges ↔ Tendsto
============================================================
-/

theorem seqConverges_iff_tendsto
    (a : ℕ → ℝ)
    (L : ℝ) :
    SeqConverges a L
      ↔
    Tendsto a atTop (𝓝 L) := by

  constructor

  · intro ha

    apply Metric.tendsto_atTop.mpr

    intro ε hε

    obtain ⟨N, hN⟩ :=
      ha ε hε

    refine ⟨N, ?_⟩

    intro n hn

    have h :
        |a n - L| < ε := by
      exact hN n hn

    simpa [Real.dist_eq] using h

  · intro ha

    unfold SeqConverges

    intro ε hε

    have hmetric :=
      Metric.tendsto_atTop.mp ha

    obtain ⟨N, hN⟩ :=
      hmetric ε hε

    refine ⟨N, ?_⟩

    intro n hn

    have h :
        dist (a n) L < ε := by
      exact hN n hn

    simpa [Real.dist_eq] using h


/-!
============================================================
Product law for convergent sequences
============================================================
-/

theorem seqConverges_mul
    {a b : ℕ → ℝ}
    {L M : ℝ}
    (ha : SeqConverges a L)
    (hb : SeqConverges b M) :
    SeqConverges
      (fun n : ℕ => a n * b n)
      (L * M) := by

  have haT :
      Tendsto a atTop (𝓝 L) := by
    exact
      (seqConverges_iff_tendsto a L).1 ha

  have hbT :
      Tendsto b atTop (𝓝 M) := by
    exact
      (seqConverges_iff_tendsto b M).1 hb

  have hmul :
      Tendsto
        (fun n : ℕ => a n * b n)
        atTop
        (𝓝 (L * M)) := by
    exact haT.mul hbT

  exact
    (seqConverges_iff_tendsto
      (fun n : ℕ => a n * b n)
      (L * M)).2 hmul


/-!
============================================================
Proposition 9.3.9

Sequential characterization of convergence.
============================================================
-/

theorem bad_points_of_not_converges
    (E : Set ℝ)
    (f : ℝ → ℝ)
    (x₀ L ε : ℝ)
    (hε : 0 < ε)
    (hfail :
      ¬ ∃ δ : ℝ,
          0 < δ ∧
          ∀ x : ℝ,
            x ∈ E →
            |x - x₀| < δ →
            |f x - L| < ε) :
    ∀ δ : ℝ,
      0 < δ →
      ∃ x : ℝ,
        x ∈ E ∧
        |x - x₀| < δ ∧
        ε ≤ |f x - L| := by

  intro δ hδ

  by_contra h

  apply hfail

  refine ⟨δ, hδ, ?_⟩

  intro x hxE hxδ

  by_contra hfx

  apply h

  refine ⟨x, hxE, hxδ, ?_⟩

  exact le_of_not_gt hfx


theorem inv_nat_succ_small :
    ∀ ε : ℝ,
      0 < ε →
      ∃ N : ℕ,
        ∀ n : ℕ,
          N ≤ n →
          1 / (((n + 1 : ℕ) : ℝ)) < ε := by

  intro ε hε

  obtain ⟨N : ℕ, hN⟩ :=
    exists_nat_gt (1 / ε)

  refine ⟨N, ?_⟩

  intro n hn

  have hNn :
      (N : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn

  have hlarge :
      1 / ε <
        ((n + 1 : ℕ) : ℝ) := by
    have hsucc :
        (n : ℝ) <
          ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.lt_succ_self n

    linarith

  have hden :
      0 < ((n + 1 : ℕ) : ℝ) := by
    positivity

  have hprod :
      1 <
        ε * ((n + 1 : ℕ) : ℝ) := by

    have h :=
      (div_lt_iff₀ hε).mp hlarge

    simpa [mul_comm] using h

  apply (div_lt_iff₀ hden).mpr

  simpa [mul_comm] using hprod


theorem seqConverges_of_inv_bound
    (a : ℕ → ℝ)
    (x₀ : ℝ)
    (ha :
      ∀ n : ℕ,
        |a n - x₀| <
          1 / (((n + 1 : ℕ) : ℝ))) :
    SeqConverges a x₀ := by

  unfold SeqConverges

  intro ε hε

  obtain ⟨N, hN⟩ :=
    inv_nat_succ_small ε hε

  refine ⟨N, ?_⟩

  intro n hn

  exact lt_trans
    (ha n)
    (hN n hn)


theorem proposition_9_3_9
    (E : Set ℝ)
    (f : ℝ → ℝ)
    (x₀ L : ℝ) :
    ConvergesAtWithin f E x₀ L
      ↔
    ∀ a : ℕ → ℝ,
      (∀ n : ℕ, a n ∈ E) →
      SeqConverges a x₀ →
      SeqConverges
        (fun n : ℕ => f (a n))
        L := by

  constructor

  · intro hf
    intro a haE ha

    unfold SeqConverges at ha ⊢

    intro ε hε

    obtain ⟨δ, hδ, hfδ⟩ :=
      hf ε hε

    obtain ⟨N, hN⟩ :=
      ha δ hδ

    refine ⟨N, ?_⟩

    intro n hn

    exact hfδ
      (a n)
      (haE n)
      (hN n hn)

  · intro hseq

    unfold ConvergesAtWithin

    intro ε hε

    by_contra hNoDelta

    have hbad :
        ∀ δ : ℝ,
          0 < δ →
          ∃ x : ℝ,
            x ∈ E ∧
            |x - x₀| < δ ∧
            ε ≤ |f x - L| := by

      exact bad_points_of_not_converges
        E f x₀ L ε hε hNoDelta

    have hExists :
        ∀ n : ℕ,
          ∃ x : ℝ,
            x ∈ E ∧
            |x - x₀| <
              1 / (((n + 1 : ℕ) : ℝ)) ∧
            ε ≤ |f x - L| := by

      intro n

      have hpos :
          0 <
            1 / (((n + 1 : ℕ) : ℝ)) := by
        positivity

      exact hbad
        (1 / (((n + 1 : ℕ) : ℝ)))
        hpos

    choose a ha using hExists

    have haE :
        ∀ n : ℕ, a n ∈ E := by
      intro n
      exact (ha n).1

    have haClose :
        ∀ n : ℕ,
          |a n - x₀| <
            1 / (((n + 1 : ℕ) : ℝ)) := by
      intro n
      exact (ha n).2.1

    have haFar :
        ∀ n : ℕ,
          ε ≤ |f (a n) - L| := by
      intro n
      exact (ha n).2.2

    have haLim :
        SeqConverges a x₀ := by
      exact seqConverges_of_inv_bound
        a x₀ haClose

    have hfaLim :
        SeqConverges
          (fun n : ℕ => f (a n))
          L := by
      exact hseq a haE haLim

    obtain ⟨N, hN⟩ :=
      hfaLim ε hε

    have hnear :
        |f (a N) - L| < ε := by
      exact hN N le_rfl

    have hfar :
        ε ≤ |f (a N) - L| := by
      exact haFar N

    linarith


/-!
============================================================
Proposition 9.3.14 — product law
============================================================
-/

theorem convergesAtWithin_mul
    (E : Set ℝ)
    (f g : ℝ → ℝ)
    (x₀ L M : ℝ)
    (hf : ConvergesAtWithin f E x₀ L)
    (hg : ConvergesAtWithin g E x₀ M) :
    ConvergesAtWithin
      (fun x : ℝ => f x * g x)
      E
      x₀
      (L * M) := by

  apply
    (proposition_9_3_9
      E
      (fun x : ℝ => f x * g x)
      x₀
      (L * M)).2

  intro a haE haLim

  have hfa :
      SeqConverges
        (fun n : ℕ => f (a n))
        L := by

    exact
      (proposition_9_3_9
        E f x₀ L).1
        hf
        a
        haE
        haLim

  have hga :
      SeqConverges
        (fun n : ℕ => g (a n))
        M := by

    exact
      (proposition_9_3_9
        E g x₀ M).1
        hg
        a
        haE
        haLim

  exact seqConverges_mul
    hfa
    hga


/-!
============================================================
Exercise 9.3.2
============================================================
-/

theorem exercise_9_3_2
    (E : Set ℝ)
    (f g : ℝ → ℝ)
    (x₀ L M : ℝ)
    (hf : ConvergesAtWithin f E x₀ L)
    (hg : ConvergesAtWithin g E x₀ M) :
    ConvergesAtWithin
      (fun x : ℝ => f x * g x)
      E
      x₀
      (L * M) := by

  exact convergesAtWithin_mul
    E
    f
    g
    x₀
    L
    M
    hf
    hg

end TaoExercise9_3_2
