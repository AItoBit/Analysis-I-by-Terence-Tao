import Mathlib

namespace TaoExercise6_5_1

/--
A real sequence `a` converges to `L` starting from index `m`.
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
The sequence n^(-q).

For positive n this is exactly 1 / n^q.
-/
noncomputable def invRpowSeq
    (q : ℚ)
    (n : ℕ) : ℝ :=
  (n : ℝ) ^ (-(q : ℝ))


/-!
============================================================
For n ≥ 1,

    n^(-q) = 1 / n^q.
============================================================
-/

theorem invRpowSeq_eq
    (q : ℚ)
    (n : ℕ)
    (hn : 1 ≤ n) :
    invRpowSeq q n =
      1 / ((n : ℝ) ^ (q : ℝ)) := by

  unfold invRpowSeq

  have hn0 :
      (0 : ℝ) ≤ (n : ℝ) := by
    positivity

  rw [Real.rpow_neg hn0]

  simp [one_div]


/-!
============================================================
The natural-number coercion tends to +∞.
============================================================
-/

theorem natCast_tendsto_atTop :
    Filter.Tendsto
      (fun n : ℕ => (n : ℝ))
      Filter.atTop
      Filter.atTop := by

  rw [Filter.tendsto_atTop_atTop]

  intro b

  obtain ⟨N : ℕ, hN⟩ :=
    exists_nat_gt b

  refine ⟨N, ?_⟩

  intro n hn

  have hNn :
      (N : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn

  exact le_trans (le_of_lt hN) hNn


/-!
============================================================
n^(-q) tends to 0 whenever q > 0.
============================================================
-/

theorem invRpowSeq_converges_zero
    (q : ℚ)
    (hq : 0 < q) :
    ConvergesFrom
      (invRpowSeq q)
      1
      0 := by

  have hqR :
      (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast hq

  /-
  x^(-q) -> 0 as x -> +∞.
  -/
  have hrpow :
      Filter.Tendsto
        (fun x : ℝ => x ^ (-(q : ℝ)))
        Filter.atTop
        (nhds 0) := by

    exact tendsto_rpow_neg_atTop hqR

  /-
  Compose with n ↦ (n : ℝ).
  -/
  have hseq :
      Filter.Tendsto
        (fun n : ℕ =>
          (n : ℝ) ^ (-(q : ℝ)))
        Filter.atTop
        (nhds 0) := by

    exact hrpow.comp natCast_tendsto_atTop

  /-
  Convert Mathlib's filter definition of convergence
  into our ε-N definition.
  -/
  have hmetric :
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ,
          ∀ n : ℕ,
            N ≤ n →
            dist ((n : ℝ) ^ (-(q : ℝ))) 0 < ε := by

    exact (Metric.tendsto_atTop.mp hseq)

  intro ε hε

  obtain ⟨N, hN⟩ :=
    hmetric ε hε

  let M : ℕ := max 1 N

  refine ⟨M, ?_, ?_⟩

  · exact le_max_left 1 N

  · intro n hn

    have hNM :
        N ≤ M := by
      exact le_max_right 1 N

    have hNn :
        N ≤ n := by
      exact le_trans hNM hn

    have hd :
        dist ((n : ℝ) ^ (-(q : ℝ))) 0 < ε := by
      exact hN n hNn

    have hdle :
        dist ((n : ℝ) ^ (-(q : ℝ))) 0 ≤ ε := by
      exact le_of_lt hd

    unfold invRpowSeq

    simpa [Real.dist_eq] using hdle


/-!
============================================================
Exercise 6.5.1

For every rational q > 0,

       1
    -------  -> 0.
      n^q
============================================================
-/

theorem exercise_6_5_1
    (q : ℚ)
    (hq : 0 < q) :
    ConvergesFrom
      (fun n : ℕ =>
        1 / ((n : ℝ) ^ (q : ℝ)))
      1
      0 := by

  have hconv :
      ConvergesFrom
        (invRpowSeq q)
        1
        0 := by

    exact invRpowSeq_converges_zero q hq

  intro ε hε

  obtain ⟨N, h1N, hN⟩ :=
    hconv ε hε

  refine ⟨N, h1N, ?_⟩

  intro n hn

  have h1n :
      1 ≤ n := by
    exact le_trans h1N hn

  have hclose :
      |invRpowSeq q n - 0| ≤ ε := by
    exact hN n hn

  rw [invRpowSeq_eq q n h1n] at hclose

  exact hclose

end TaoExercise6_5_1
