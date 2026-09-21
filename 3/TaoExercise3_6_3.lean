import Mathlib

namespace TaoExercise3_6_3

open Finset

/--
Exercise 3.6.3.

Let `f` be a function defined on the natural numbers
`i` with `1 ≤ i ≤ n`. Then there exists a natural number `M`
such that `f i ≤ M` for every such `i`.
-/
theorem finite_nat_subset_bounded
    (n : ℕ)
    (f : {i : ℕ // i ∈ Finset.Icc 1 n} → ℕ) :
    ∃ M : ℕ, ∀ i : {i : ℕ // i ∈ Finset.Icc 1 n}, f i ≤ M := by
  classical

  let S : Finset ℕ := (Finset.Icc 1 n).attach.image f

  refine ⟨S.sum, ?_⟩

  intro i

  have hmem : f i ∈ S := by
    simp [S]

  exact Finset.single_le_sum
    (fun x hx => Nat.zero_le x)
    hmem
