import Mathlib

namespace TaoExercise9_4_1

/-!
============================================================
Convergence of a sequence
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
(a) Continuity at x₀
============================================================
-/

def ContinuousAtTao
    (f : ℝ → ℝ)
    (x₀ : ℝ) : Prop :=
  ∀ ε : ℝ,
    0 < ε →
    ∃ δ : ℝ,
      0 < δ ∧
      ∀ x : ℝ,
        abs (x - x₀) < δ →
        abs (f x - f x₀) < ε


/-!
============================================================
(b) Sequential continuity
============================================================
-/

def SequentiallyContinuousAt
    (f : ℝ → ℝ)
    (x₀ : ℝ) : Prop :=
  ∀ a : ℕ → ℝ,
    SeqConverges a x₀ →
    SeqConverges (fun n : ℕ => f (a n)) (f x₀)


/-!
============================================================
(c) Strict ε-δ formulation
============================================================
-/

def ConditionC
    (f : ℝ → ℝ)
    (x₀ : ℝ) : Prop :=
  ∀ ε : ℝ,
    0 < ε →
    ∃ δ : ℝ,
      0 < δ ∧
      ∀ x : ℝ,
        abs (x - x₀) < δ →
        abs (f x - f x₀) < ε


/-!
============================================================
(d) Non-strict formulation
============================================================
-/

def ConditionD
    (f : ℝ → ℝ)
    (x₀ : ℝ) : Prop :=
  ∀ ε : ℝ,
    0 < ε →
    ∃ δ : ℝ,
      0 < δ ∧
      ∀ x : ℝ,
        abs (x - x₀) ≤ δ →
        abs (f x - f x₀) ≤ ε


/-!
============================================================
(a) -> (c)
============================================================
-/

theorem continuous_implies_conditionC
    (f : ℝ → ℝ)
    (x₀ : ℝ)
    (hf : ContinuousAtTao f x₀) :
    ConditionC f x₀ := by
  exact hf


/-!
============================================================
(c) -> (d)
============================================================
-/

theorem conditionC_implies_conditionD
    (f : ℝ → ℝ)
    (x₀ : ℝ)
    (hc : ConditionC f x₀) :
    ConditionD f x₀ := by

  intro ε hε

  have hhalf :
      0 < ε / 2 := by
    linarith

  obtain ⟨α, hα, hmain⟩ :=
    hc (ε / 2) hhalf

  let δ : ℝ := α / 2

  have hδ :
      0 < δ := by
    dsimp [δ]
    linarith

  refine ⟨δ, hδ, ?_⟩

  intro x hx

  have hxα :
      abs (x - x₀) < α := by
    dsimp [δ] at hx
    linarith

  have hout :
      abs (f x - f x₀) < ε / 2 := by
    exact hmain x hxα

  linarith


/-!
============================================================
(d) -> (b)
============================================================
-/

theorem conditionD_implies_sequential
    (f : ℝ → ℝ)
    (x₀ : ℝ)
    (hd : ConditionD f x₀) :
    SequentiallyContinuousAt f x₀ := by

  intro a ha

  unfold SeqConverges at ha ⊢

  intro ε hε

  have hhalf :
      0 < ε / 2 := by
    linarith

  obtain ⟨δ, hδ, hfδ⟩ :=
    hd (ε / 2) hhalf

  obtain ⟨N, hN⟩ :=
    ha δ hδ

  refine ⟨N, ?_⟩

  intro n hn

  have haClose :
      abs (a n - x₀) < δ := by
    exact hN n hn

  have hfClose :
      abs (f (a n) - f x₀) ≤ ε / 2 := by
    exact hfδ (a n) (le_of_lt haClose)

  linarith


/-!
============================================================
Auxiliary fact: 1/(n+1) -> 0
============================================================
-/

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

  have hnSucc :
      (n : ℝ) < ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_succ_self n

  have hlarge :
      1 / ε < ((n + 1 : ℕ) : ℝ) := by
    linarith

  have hden :
      0 < ((n + 1 : ℕ) : ℝ) := by
    positivity

  have hprod :
      1 < ε * ((n + 1 : ℕ) : ℝ) := by
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
        abs (a n - x₀) <
          1 / (((n + 1 : ℕ) : ℝ))) :
    SeqConverges a x₀ := by

  intro ε hε

  obtain ⟨N, hN⟩ :=
    inv_nat_succ_small ε hε

  refine ⟨N, ?_⟩

  intro n hn

  exact lt_trans
    (ha n)
    (hN n hn)


/-!
============================================================
(b) -> (a)

This is the sequential criterion of Proposition 9.3.9.
============================================================
-/

theorem sequential_implies_continuous
    (f : ℝ → ℝ)
    (x₀ : ℝ)
    (hseq : SequentiallyContinuousAt f x₀) :
    ContinuousAtTao f x₀ := by

  intro ε hε

  by_contra hNoDelta

  have hbad :
      ∀ δ : ℝ,
        0 < δ →
        ∃ x : ℝ,
          abs (x - x₀) < δ ∧
          ε ≤ abs (f x - f x₀) := by

    intro δ hδ

    by_contra hNoPoint

    apply hNoDelta

    refine ⟨δ, hδ, ?_⟩

    intro x hx

    by_contra hfx

    apply hNoPoint

    refine ⟨x, hx, ?_⟩

    exact le_of_not_gt hfx

  have hExists :
      ∀ n : ℕ,
        ∃ x : ℝ,
          abs (x - x₀) <
            1 / (((n + 1 : ℕ) : ℝ)) ∧
          ε ≤ abs (f x - f x₀) := by

    intro n

    have hpos :
        0 <
          1 / (((n + 1 : ℕ) : ℝ)) := by
      positivity

    exact hbad
      (1 / (((n + 1 : ℕ) : ℝ)))
      hpos

  choose a ha using hExists

  have haClose :
      ∀ n : ℕ,
        abs (a n - x₀) <
          1 / (((n + 1 : ℕ) : ℝ)) := by
    intro n
    exact (ha n).1

  have haFar :
      ∀ n : ℕ,
        ε ≤ abs (f (a n) - f x₀) := by
    intro n
    exact (ha n).2

  have haLim :
      SeqConverges a x₀ := by
    exact seqConverges_of_inv_bound
      a
      x₀
      haClose

  have hfaLim :
      SeqConverges
        (fun n : ℕ => f (a n))
        (f x₀) := by
    exact hseq a haLim

  obtain ⟨N, hN⟩ :=
    hfaLim ε hε

  have hnear :
      abs (f (a N) - f x₀) < ε := by
    exact hN N le_rfl

  have hfar :
      ε ≤ abs (f (a N) - f x₀) := by
    exact haFar N

  linarith


/-!
============================================================
Individual equivalences
============================================================
-/

theorem continuous_iff_sequential
    (f : ℝ → ℝ)
    (x₀ : ℝ) :
    ContinuousAtTao f x₀
      ↔
    SequentiallyContinuousAt f x₀ := by

  constructor

  · intro hf

    have hc :
        ConditionC f x₀ := by
      exact continuous_implies_conditionC f x₀ hf

    have hd :
        ConditionD f x₀ := by
      exact conditionC_implies_conditionD f x₀ hc

    exact conditionD_implies_sequential
      f
      x₀
      hd

  · intro hseq

    exact sequential_implies_continuous
      f
      x₀
      hseq


theorem continuous_iff_conditionC
    (f : ℝ → ℝ)
    (x₀ : ℝ) :
    ContinuousAtTao f x₀
      ↔
    ConditionC f x₀ := by
  constructor
  · intro h
    exact h
  · intro h
    exact h


theorem continuous_iff_conditionD
    (f : ℝ → ℝ)
    (x₀ : ℝ) :
    ContinuousAtTao f x₀
      ↔
    ConditionD f x₀ := by

  constructor

  · intro hf

    exact conditionC_implies_conditionD
      f
      x₀
      hf

  · intro hd

    have hseq :
        SequentiallyContinuousAt f x₀ := by
      exact conditionD_implies_sequential
        f
        x₀
        hd

    exact sequential_implies_continuous
      f
      x₀
      hseq


/-!
============================================================
Proposition 9.4.7
============================================================
-/

theorem proposition_9_4_7
    (f : ℝ → ℝ)
    (x₀ : ℝ) :
    (ContinuousAtTao f x₀
      ↔ SequentiallyContinuousAt f x₀)
    ∧
    (ContinuousAtTao f x₀
      ↔ ConditionC f x₀)
    ∧
    (ContinuousAtTao f x₀
      ↔ ConditionD f x₀) := by

  constructor

  · exact continuous_iff_sequential f x₀

  constructor

  · exact continuous_iff_conditionC f x₀

  · exact continuous_iff_conditionD f x₀


/-!
============================================================
Exercise 9.4.1
============================================================
-/

theorem exercise_9_4_1
    (f : ℝ → ℝ)
    (x₀ : ℝ) :
    (ContinuousAtTao f x₀
      ↔ SequentiallyContinuousAt f x₀)
    ∧
    (ContinuousAtTao f x₀
      ↔ ConditionC f x₀)
    ∧
    (ContinuousAtTao f x₀
      ↔ ConditionD f x₀) := by

  exact proposition_9_4_7 f x₀

end TaoExercise9_4_1
