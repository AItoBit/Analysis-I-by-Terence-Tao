import Mathlib

namespace TaoExercise9_9_3

/-!
============================================================
Uniform continuity on X
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
Cauchy sequence in ℝ
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
Proposition 9.9.12

Uniformly continuous functions map Cauchy sequences
to Cauchy sequences.
============================================================
-/

theorem proposition_9_9_12
    (X : Set ℝ)
    (f : X → ℝ)
    (x : ℕ → X)
    (hf : UniformContinuousOnTao X f)
    (hx : IsCauchySeq (fun n => (x n : ℝ))) :
    IsCauchySeq (fun n => f (x n)) := by

  unfold IsCauchySeq at hx ⊢

  intro ε hε

  obtain ⟨δ, hδpos, hδ⟩ :=
    hf ε hε

  obtain ⟨N, hN⟩ :=
    hx δ hδpos

  refine ⟨N, ?_⟩

  intro j k hj hk

  have hClose :
      abs ((x j : ℝ) - (x k : ℝ)) < δ := by
    exact hN j k hj hk

  exact hδ
    (x j)
    (x k)
    hClose


/-!
============================================================
Exercise 9.9.3
============================================================
-/

theorem exercise_9_9_3
    (X : Set ℝ)
    (f : X → ℝ)
    (x : ℕ → X)
    (hf : UniformContinuousOnTao X f)
    (hx : IsCauchySeq (fun n => (x n : ℝ))) :
    IsCauchySeq (fun n => f (x n)) := by

  exact proposition_9_9_12
    X
    f
    x
    hf
    hx

end TaoExercise9_9_3
