import Mathlib

namespace TaoExercise9_9_2

/-!
============================================================
Equivalent real sequences, starting from n = 1
============================================================
-/

def EquivalentFromOne
    (a b : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ,
    0 < ε →
    ∃ N : ℕ,
      1 ≤ N ∧
      ∀ n : ℕ,
        N ≤ n →
        abs (a n - b n) ≤ ε


/-!
============================================================
Uniform continuity on X
============================================================

f : X → ℝ is uniformly continuous if

  ∀ ε > 0, ∃ δ > 0,
    |x-y| ≤ δ → |f(x)-f(y)| ≤ ε

for all x,y ∈ X.
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
        abs ((x : ℝ) - (y : ℝ)) ≤ δ →
        abs (f x - f y) ≤ ε


/-!
============================================================
1/(n+1) eventually becomes arbitrarily small
============================================================
-/

theorem inv_nat_succ_small
    (ε : ℝ)
    (hε : 0 < ε) :
    ∃ N : ℕ,
      1 ≤ N ∧
      ∀ n : ℕ,
        N ≤ n →
        1 / (((n + 1 : ℕ) : ℝ)) ≤ ε := by

  obtain ⟨K : ℕ, hK⟩ :=
    exists_nat_gt (1 / ε)

  let N : ℕ := max 1 K

  have h1N :
      1 ≤ N := by
    exact le_max_left 1 K

  refine ⟨N, h1N, ?_⟩

  intro n hn

  have hKN :
      K ≤ N := by
    exact le_max_right 1 K

  have hKn :
      K ≤ n := by
    exact le_trans hKN hn

  have hKnReal :
      (K : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hKn

  have hnSucc :
      (n : ℝ) < ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_succ_self n

  have hLarge :
      1 / ε < ((n + 1 : ℕ) : ℝ) := by
    linarith

  have hDenPos :
      0 < ((n + 1 : ℕ) : ℝ) := by
    positivity

  have hProd :
      1 < ε * ((n + 1 : ℕ) : ℝ) := by
    have h :=
      (div_lt_iff₀ hε).mp hLarge
    simpa [mul_comm] using h

  have hInv :
      1 / ((n + 1 : ℕ) : ℝ) < ε := by
    apply (div_lt_iff₀ hDenPos).mpr
    simpa [mul_comm] using hProd

  exact le_of_lt hInv


/-!
============================================================
(a) -> (b)

Uniform continuity preserves equivalent sequences.
============================================================
-/

theorem uniformContinuous_implies_preserves_equivalent
    (X : Set ℝ)
    (f : X → ℝ)
    (hf : UniformContinuousOnTao X f) :
    ∀ x y : ℕ → X,
      EquivalentFromOne
          (fun n => (x n : ℝ))
          (fun n => (y n : ℝ)) →
      EquivalentFromOne
          (fun n => f (x n))
          (fun n => f (y n)) := by

  intro x y hxy

  unfold EquivalentFromOne at hxy ⊢

  intro ε hε

  obtain ⟨δ, hδ, hfδ⟩ :=
    hf ε hε

  obtain ⟨N, hN1, hN⟩ :=
    hxy δ hδ

  refine ⟨N, hN1, ?_⟩

  intro n hn

  have hClose :
      abs ((x n : ℝ) - (y n : ℝ)) ≤ δ := by
    exact hN n hn

  exact hfδ
    (x n)
    (y n)
    hClose


/-!
============================================================
Failure of uniform continuity gives bad pairs
============================================================
-/

theorem bad_pairs_of_not_uniform
    (X : Set ℝ)
    (f : X → ℝ)
    (ε : ℝ)
    (hε : 0 < ε)
    (hfail :
      ¬ ∃ δ : ℝ,
          0 < δ ∧
          ∀ x y : X,
            abs ((x : ℝ) - (y : ℝ)) ≤ δ →
            abs (f x - f y) ≤ ε) :
    ∀ δ : ℝ,
      0 < δ →
      ∃ x y : X,
        abs ((x : ℝ) - (y : ℝ)) ≤ δ ∧
        ε < abs (f x - f y) := by

  intro δ hδ

  by_contra hNoPair

  apply hfail

  refine ⟨δ, hδ, ?_⟩

  intro x y hxy

  by_contra hfar

  apply hNoPair

  refine ⟨x, y, hxy, ?_⟩

  exact lt_of_not_ge hfar


/-!
============================================================
If two sequences are pointwise within 1/(n+1),
then they are equivalent.
============================================================
-/

theorem equivalent_of_inv_bound
    (X : Set ℝ)
    (x y : ℕ → X)
    (hxy :
      ∀ n : ℕ,
        abs ((x n : ℝ) - (y n : ℝ))
          ≤ 1 / (((n + 1 : ℕ) : ℝ))) :
    EquivalentFromOne
      (fun n => (x n : ℝ))
      (fun n => (y n : ℝ)) := by

  unfold EquivalentFromOne

  intro ε hε

  obtain ⟨N, hN1, hN⟩ :=
    inv_nat_succ_small ε hε

  refine ⟨N, hN1, ?_⟩

  intro n hn

  exact le_trans
    (hxy n)
    (hN n hn)


/-!
============================================================
(b) -> (a)

If equivalent sequences always have equivalent images,
then f is uniformly continuous.
============================================================
-/

theorem preserves_equivalent_implies_uniformContinuous
    (X : Set ℝ)
    (f : X → ℝ)
    (hseq :
      ∀ x y : ℕ → X,
        EquivalentFromOne
            (fun n => (x n : ℝ))
            (fun n => (y n : ℝ)) →
        EquivalentFromOne
            (fun n => f (x n))
            (fun n => f (y n))) :
    UniformContinuousOnTao X f := by

  unfold UniformContinuousOnTao

  intro ε hε

  by_contra hNoDelta

  have hbad :
      ∀ δ : ℝ,
        0 < δ →
        ∃ x y : X,
          abs ((x : ℝ) - (y : ℝ)) ≤ δ ∧
          ε < abs (f x - f y) := by
    exact bad_pairs_of_not_uniform
      X
      f
      ε
      hε
      hNoDelta

  have hExists :
      ∀ n : ℕ,
        ∃ x y : X,
          abs ((x : ℝ) - (y : ℝ))
            ≤ 1 / (((n + 1 : ℕ) : ℝ)) ∧
          ε < abs (f x - f y) := by

    intro n

    have hRadius :
        0 <
          1 / (((n + 1 : ℕ) : ℝ)) := by
      positivity

    exact hbad
      (1 / (((n + 1 : ℕ) : ℝ)))
      hRadius

  choose x y hclose hfar using hExists

  have hxyEquivalent :
      EquivalentFromOne
        (fun n => (x n : ℝ))
        (fun n => (y n : ℝ)) := by

    exact equivalent_of_inv_bound
      X
      x
      y
      hclose

  have hfEquivalent :
      EquivalentFromOne
        (fun n => f (x n))
        (fun n => f (y n)) := by

    exact hseq
      x
      y
      hxyEquivalent

  obtain ⟨N, hN1, hN⟩ :=
    hfEquivalent ε hε

  have hNear :
      abs (f (x N) - f (y N)) ≤ ε := by
    exact hN N le_rfl

  have hFar :
      ε < abs (f (x N) - f (y N)) := by
    exact hfar N

  linarith


/-!
============================================================
Proposition 9.9.8
============================================================

(a) f is uniformly continuous on X

iff

(b) equivalent sequences in X have equivalent images.
============================================================
-/

theorem proposition_9_9_8
    (X : Set ℝ)
    (f : X → ℝ) :
    UniformContinuousOnTao X f
      ↔
    ∀ x y : ℕ → X,
      EquivalentFromOne
          (fun n => (x n : ℝ))
          (fun n => (y n : ℝ)) →
      EquivalentFromOne
          (fun n => f (x n))
          (fun n => f (y n)) := by

  constructor

  · intro hf

    exact uniformContinuous_implies_preserves_equivalent
      X
      f
      hf

  · intro hseq

    exact preserves_equivalent_implies_uniformContinuous
      X
      f
      hseq


/-!
============================================================
Exercise 9.9.2
============================================================
-/

theorem exercise_9_9_2
    (X : Set ℝ)
    (f : X → ℝ) :
    UniformContinuousOnTao X f
      ↔
    ∀ x y : ℕ → X,
      EquivalentFromOne
          (fun n => (x n : ℝ))
          (fun n => (y n : ℝ)) →
      EquivalentFromOne
          (fun n => f (x n))
          (fun n => f (y n)) := by

  exact proposition_9_9_8 X f

end TaoExercise9_9_2
