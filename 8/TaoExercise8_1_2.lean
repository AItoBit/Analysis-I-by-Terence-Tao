import Mathlib

namespace TaoExercise8_1_2

open Set

/-!
============================================================
Proposition 8.1.4
Well-ordering principle for ℕ
============================================================

Every nonempty subset of ℕ has a least element.
-/

theorem proposition_8_1_4
    (X : Set ℕ)
    (hX : X.Nonempty) :
    ∃ n : ℕ,
      n ∈ X ∧
      ∀ m : ℕ,
        m ∈ X →
        n ≤ m := by
  classical

  rcases hX with ⟨k, hk⟩

  have hex :
      ∃ n : ℕ, n ∈ X := by
    exact ⟨k, hk⟩

  let n : ℕ :=
    Nat.find hex

  have hnX :
      n ∈ X := by
    dsimp [n]
    exact Nat.find_spec hex

  refine ⟨n, hnX, ?_⟩

  intro m hm

  dsimp [n]

  exact Nat.find_min' hex hm


/-!
Equivalent formulation using `IsLeast`.
-/

theorem proposition_8_1_4_isLeast
    (X : Set ℕ)
    (hX : X.Nonempty) :
    ∃ n : ℕ, IsLeast X n := by
  obtain ⟨n, hnX, hnmin⟩ :=
    proposition_8_1_4 X hX

  exact ⟨n, hnX, hnmin⟩


/-!
============================================================
The well-ordering principle fails for ℤ
============================================================

Take

    A = {z : ℤ | z ≤ 0}.

It is nonempty, but it has no least element.
Indeed, if z ∈ A, then z - 1 ∈ A and z - 1 < z.
-/

def integerCounterexample : Set ℤ :=
  {z : ℤ | z ≤ 0}


theorem integerCounterexample_nonempty :
    integerCounterexample.Nonempty := by
  refine ⟨0, ?_⟩

  change (0 : ℤ) ≤ 0

  exact le_rfl


theorem integerCounterexample_has_smaller
    (z : ℤ)
    (hz : z ∈ integerCounterexample) :
    ∃ w : ℤ,
      w ∈ integerCounterexample ∧
      w < z := by

  refine ⟨z - 1, ?_, ?_⟩

  · change z - 1 ≤ 0

    change z ≤ 0 at hz

    omega

  · omega


theorem integerCounterexample_no_least :
    ¬ ∃ z : ℤ,
        IsLeast integerCounterexample z := by

  rintro ⟨z, hzA, hzLeast⟩

  obtain ⟨w, hwA, hwz⟩ :=
    integerCounterexample_has_smaller z hzA

  have hzw :
      z ≤ w := by
    exact hzLeast hwA

  exact (not_lt_of_ge hzw) hwz


theorem integers_not_well_ordered :
    ∃ A : Set ℤ,
      A.Nonempty ∧
      ¬ ∃ z : ℤ, IsLeast A z := by

  exact
    ⟨integerCounterexample,
      integerCounterexample_nonempty,
      integerCounterexample_no_least⟩


/-!
============================================================
The well-ordering principle fails for positive ℚ
============================================================

Instead of using {1/n : n > 0}, we can use the even
simpler set of all positive rationals:

    Q₊ = {q : ℚ | 0 < q}.

For any q > 0, q/2 is still positive and is strictly
smaller than q.
-/

def positiveRationals : Set ℚ :=
  {q : ℚ | 0 < q}


theorem positiveRationals_nonempty :
    positiveRationals.Nonempty := by

  refine ⟨1, ?_⟩

  change (0 : ℚ) < 1

  norm_num


theorem positiveRationals_has_smaller
    (q : ℚ)
    (hq : q ∈ positiveRationals) :
    ∃ r : ℚ,
      r ∈ positiveRationals ∧
      r < q := by

  refine ⟨q / 2, ?_, ?_⟩

  · change 0 < q / 2

    change 0 < q at hq

    positivity

  · change q / 2 < q

    change 0 < q at hq

    linarith


theorem positiveRationals_no_least :
    ¬ ∃ q : ℚ,
        IsLeast positiveRationals q := by

  rintro ⟨q, hqPos, hqLeast⟩

  obtain ⟨r, hrPos, hrq⟩ :=
    positiveRationals_has_smaller
      q
      hqPos

  have hqr :
      q ≤ r := by
    exact hqLeast hrPos

  exact (not_lt_of_ge hqr) hrq


theorem positive_rationals_not_well_ordered :
    ∃ Q : Set ℚ,
      Q.Nonempty ∧
      ¬ ∃ q : ℚ, IsLeast Q q := by

  exact
    ⟨positiveRationals,
      positiveRationals_nonempty,
      positiveRationals_no_least⟩


/-!
============================================================
Exercise 8.1.2 packaged together
============================================================
-/

theorem exercise_8_1_2
    (X : Set ℕ)
    (hX : X.Nonempty) :
    (∃ n : ℕ, IsLeast X n)
    ∧
    (∃ A : Set ℤ,
      A.Nonempty ∧
      ¬ ∃ z : ℤ, IsLeast A z)
    ∧
    (∃ Q : Set ℚ,
      Q.Nonempty ∧
      ¬ ∃ q : ℚ, IsLeast Q q) := by

  constructor

  · exact proposition_8_1_4_isLeast
      X
      hX

  constructor

  · exact integers_not_well_ordered

  · exact positive_rationals_not_well_ordered

end TaoExercise8_1_2
