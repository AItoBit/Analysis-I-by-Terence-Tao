import Mathlib

namespace TaoExercise7_1_5

/-!
============================================================
Convergence from an index m
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


/-!
============================================================
Finite-set sum
============================================================
-/

noncomputable def finiteSetSum
    {α : Type*}
    (X : Finset α)
    (f : α → ℝ) : ℝ :=
  X.sum f


/-!
============================================================
The constant zero sequence converges to zero
============================================================
-/

theorem converges_zero
    (m : ℕ) :
    ConvergesFrom
      (fun _ : ℕ => (0 : ℝ))
      m
      0 := by

  intro ε hε

  refine ⟨m, le_rfl, ?_⟩

  intro n hn

  simpa using (le_of_lt hε)


/-!
============================================================
Sum of two convergent sequences
============================================================
-/

theorem converges_add
    (a b : ℕ → ℝ)
    (m : ℕ)
    (A B : ℝ)
    (ha : ConvergesFrom a m A)
    (hb : ConvergesFrom b m B) :
    ConvergesFrom
      (fun n => a n + b n)
      m
      (A + B) := by

  intro ε hε

  have hhalf :
      0 < ε / 2 := by
    linarith

  obtain ⟨N₁, hmN₁, hN₁⟩ :=
    ha (ε / 2) hhalf

  obtain ⟨N₂, hmN₂, hN₂⟩ :=
    hb (ε / 2) hhalf

  let N : ℕ := max N₁ N₂

  refine ⟨N, ?_, ?_⟩

  · exact le_trans hmN₁ (le_max_left N₁ N₂)

  · intro n hn

    have hN₁N :
        N₁ ≤ N := by
      exact le_max_left N₁ N₂

    have hN₂N :
        N₂ ≤ N := by
      exact le_max_right N₁ N₂

    have hN₁n :
        N₁ ≤ n := by
      exact le_trans hN₁N hn

    have hN₂n :
        N₂ ≤ n := by
      exact le_trans hN₂N hn

    have haClose :
        |a n - A| ≤ ε / 2 := by
      exact hN₁ n hN₁n

    have hbClose :
        |b n - B| ≤ ε / 2 := by
      exact hN₂ n hN₂n

    have hrewrite :
        (a n + b n) - (A + B)
          =
        (a n - A) + (b n - B) := by
      ring

    rw [hrewrite]

    calc
      |(a n - A) + (b n - B)|
          ≤ |a n - A| + |b n - B| := by
            exact abs_add_le _ _

      _ ≤ ε / 2 + ε / 2 := by
            exact add_le_add haClose hbClose

      _ = ε := by
            ring


/-!
============================================================
Finite sum of convergent sequences
============================================================

If every sequence x ↦ a_n(x) converges to L(x),
then their finite sum converges to the sum of the limits.
-/

theorem finite_sum_converges
    {α : Type*}
    [DecidableEq α]
    (X : Finset α)
    (a : ℕ → α → ℝ)
    (L : α → ℝ)
    (m : ℕ)
    (hconv :
      ∀ x : α,
        x ∈ X →
        ConvergesFrom
          (fun n => a n x)
          m
          (L x)) :
    ConvergesFrom
      (fun n =>
        finiteSetSum X (fun x => a n x))
      m
      (finiteSetSum X L) := by

  revert hconv

  induction X using Finset.induction_on with

  /-
  Empty set.
  -/
  | empty =>

      intro hconv

      have hzero :
          ConvergesFrom
            (fun _ : ℕ => (0 : ℝ))
            m
            0 := by
        exact converges_zero m

      simpa [finiteSetSum] using hzero

  /-
  Insert one new element x.
  -/
  | @insert x X hx ih =>

      intro hconv

      have hxConv :
          ConvergesFrom
            (fun n => a n x)
            m
            (L x) := by

        exact hconv x (by simp)

      have hX :
          ∀ y : α,
            y ∈ X →
            ConvergesFrom
              (fun n => a n y)
              m
              (L y) := by

        intro y hy

        exact hconv y (by
          simp [hy])

      have hXConv :
          ConvergesFrom
            (fun n =>
              finiteSetSum X
                (fun y => a n y))
            m
            (finiteSetSum X L) := by

        exact ih hX

      have hAdd :
          ConvergesFrom
            (fun n =>
              a n x
                +
              finiteSetSum X
                (fun y => a n y))
            m
            (L x + finiteSetSum X L) := by

        exact converges_add
          (fun n => a n x)
          (fun n =>
            finiteSetSum X
              (fun y => a n y))
          m
          (L x)
          (finiteSetSum X L)
          hxConv
          hXConv

      simpa [finiteSetSum, hx] using hAdd


/-!
============================================================
Exercise 7.1.5
============================================================
-/

theorem exercise_7_1_5
    {α : Type*}
    [DecidableEq α]
    (X : Finset α)
    (a : ℕ → α → ℝ)
    (L : α → ℝ)
    (m : ℕ)
    (hconv :
      ∀ x : α,
        x ∈ X →
        ConvergesFrom
          (fun n => a n x)
          m
          (L x)) :
    ConvergesFrom
      (fun n =>
        finiteSetSum X
          (fun x => a n x))
      m
      (finiteSetSum X L) := by

  exact finite_sum_converges
    X
    a
    L
    m
    hconv

end TaoExercise7_1_5
