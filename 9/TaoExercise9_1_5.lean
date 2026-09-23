import Mathlib

namespace TaoExercise9_1_5

open Set
open Filter
open Topology

/-!
============================================================
Lemma 9.1.14
============================================================

For X ⊆ ℝ and ℓ ∈ ℝ,

there exists a sequence in X converging to ℓ

iff

ℓ ∈ closure X.
-/

theorem lemma_9_1_14
    (X : Set ℝ)
    (ℓ : ℝ) :
    (∃ a : ℕ → ℝ,
        (∀ n : ℕ, a n ∈ X) ∧
        Tendsto a atTop (𝓝 ℓ))
      ↔
    ℓ ∈ closure X := by
  constructor

  /- ---------------------------------------------------------
     (a) → (b)
     --------------------------------------------------------- -/

  · rintro ⟨a, haX, haLim⟩

    apply mem_closure_of_tendsto haLim

    filter_upwards with n

    exact haX n

  /- ---------------------------------------------------------
     (b) → (a)
     --------------------------------------------------------- -/

  · intro hℓ

    classical

    have hclose :
        ∀ ε : ℝ,
          0 < ε →
          ∃ x : ℝ,
            x ∈ X ∧
            dist x ℓ < ε := by

      intro ε hε

      have h :=
        (Metric.mem_closure_iff.mp hℓ)
          ε
          hε

      rcases h with ⟨x, hxX, hx⟩

      refine ⟨x, hxX, ?_⟩

      simpa [dist_comm] using hx


    /- For each n choose a point of X at distance
       < 1 / (n+1) from ℓ. -/

    have hExists :
        ∀ n : ℕ,
          ∃ x : ℝ,
            x ∈ X ∧
            dist x ℓ <
              1 / ((n + 1 : ℕ) : ℝ) := by

      intro n

      have hpos :
          0 <
            1 / ((n + 1 : ℕ) : ℝ) := by
        positivity

      exact
        hclose
          (1 / ((n + 1 : ℕ) : ℝ))
          hpos


    choose a haX haDist using hExists

    refine ⟨a, haX, ?_⟩


    /- -------------------------------------------------------
       Prove aₙ → ℓ
       ------------------------------------------------------- -/

    apply Metric.tendsto_atTop.mpr

    intro ε hε

    obtain ⟨N : ℕ, hN⟩ :=
      exists_nat_gt (1 / ε)

    refine ⟨N, ?_⟩

    intro n hn

    have hNn :
        (N : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn

    have hInvN :
        1 < (N : ℝ) * ε := by

      have h :=
        (div_lt_iff₀ hε).mp hN

      simpa [mul_comm] using h

    have hnPos :
        0 < ((n + 1 : ℕ) : ℝ) := by
      positivity

    have hBig :
        1 <
          ((n + 1 : ℕ) : ℝ) * ε := by

      have hNle :
          (N : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
        have hnlt :
            (n : ℝ) < ((n + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.lt_succ_self n

        linarith

      nlinarith [hInvN, hε]

    have hRadius :
        1 / ((n + 1 : ℕ) : ℝ) < ε := by

      apply (div_lt_iff₀ hnPos).mpr

      simpa [mul_comm] using hBig

    exact lt_trans
      (haDist n)
      hRadius


/-!
============================================================
Exercise 9.1.5
============================================================
-/

theorem exercise_9_1_5
    (X : Set ℝ)
    (ℓ : ℝ) :
    (∃ a : ℕ → ℝ,
        (∀ n : ℕ, a n ∈ X) ∧
        Tendsto a atTop (𝓝 ℓ))
      ↔
    ℓ ∈ closure X := by

  exact lemma_9_1_14 X ℓ

end TaoExercise9_1_5
