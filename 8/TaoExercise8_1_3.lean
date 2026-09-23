import Mathlib

namespace TaoExercise8_1_3

open Set

/-!
============================================================
Remaining elements
============================================================

`remaining X a n` is the set

  {x ∈ X | x ≠ a m for every m < n}.
-/

def remaining
    (X : Set ℕ)
    (a : ℕ → ℕ)
    (n : ℕ) : Set ℕ :=
  {x : ℕ |
    x ∈ X ∧
    ∀ m : ℕ, m < n → x ≠ a m}


/-!
The set of values already selected before stage `n`.
-/

def used
    (a : ℕ → ℕ)
    (n : ℕ) : Set ℕ :=
  ↑((Finset.range n).image a)


/-!
============================================================
Membership in remaining
============================================================
-/

theorem mem_remaining_iff
    (X : Set ℕ)
    (a : ℕ → ℕ)
    (n x : ℕ) :
    x ∈ remaining X a n ↔
      x ∈ X ∧
      ∀ m : ℕ, m < n → x ≠ a m := by
  rfl


/-!
============================================================
An earlier value belongs to `used`
============================================================
-/

theorem mem_used_of_eq
    (a : ℕ → ℕ)
    {n m x : ℕ}
    (hm : m < n)
    (hx : x = a m) :
    x ∈ used a n := by

  unfold used

  rw [Finset.mem_coe]

  apply Finset.mem_image.mpr

  refine ⟨m, ?_, ?_⟩

  · exact Finset.mem_range.mpr hm

  · exact hx.symm


/-!
============================================================
Every element of X is either already used
or is still remaining.
============================================================
-/

theorem subset_used_union_remaining
    (X : Set ℕ)
    (a : ℕ → ℕ)
    (n : ℕ) :
    X ⊆ used a n ∪ remaining X a n := by

  intro x hxX

  by_cases hused :
      ∃ m : ℕ, m < n ∧ x = a m

  · rcases hused with ⟨m, hm, hxm⟩

    left

    exact mem_used_of_eq
      a
      hm
      hxm

  · right

    constructor

    · exact hxX

    · intro m hm hxm

      apply hused

      exact ⟨m, hm, hxm⟩


/-!
============================================================
The used set is finite
============================================================
-/

theorem used_finite
    (a : ℕ → ℕ)
    (n : ℕ) :
    (used a n).Finite := by

  unfold used

  exact
    ((Finset.range n).image a).finite_toSet


/-!
============================================================
Gap 1

The remaining set is infinite.
============================================================
-/

theorem remaining_infinite
    (X : Set ℕ)
    (a : ℕ → ℕ)
    (hX : ¬ X.Finite)
    (n : ℕ) :
    ¬ (remaining X a n).Finite := by

  intro hRemaining

  have hUsed :
      (used a n).Finite := by
    exact used_finite a n

  have hUnion :
      (used a n ∪ remaining X a n).Finite := by
    exact hUsed.union hRemaining

  have hXFinite :
      X.Finite := by

    exact hUnion.subset
      (subset_used_union_remaining X a n)

  exact hX hXFinite


/-!
============================================================
The recursive construction

`hLeast` says:

  a n = min {x ∈ X | x has not occurred before n}.
============================================================
-/

def IsRecursiveMinimum
    (X : Set ℕ)
    (a : ℕ → ℕ) : Prop :=
  ∀ n : ℕ,
    IsLeast
      (remaining X a n)
      (a n)


/-!
============================================================
a n belongs to the remaining set
============================================================
-/

theorem selected_mem_remaining
    (X : Set ℕ)
    (a : ℕ → ℕ)
    (hLeast : IsRecursiveMinimum X a)
    (n : ℕ) :
    a n ∈ remaining X a n := by

  exact (hLeast n).1


/-!
============================================================
Gap 4

a n ∈ X
============================================================
-/

theorem selected_mem_X
    (X : Set ℕ)
    (a : ℕ → ℕ)
    (hLeast : IsRecursiveMinimum X a)
    (n : ℕ) :
    a n ∈ X := by

  have hn :
      a n ∈ remaining X a n := by

    exact selected_mem_remaining
      X
      a
      hLeast
      n

  exact hn.1


/-!
============================================================
A_{n+1} ⊆ A_n
============================================================
-/

theorem remaining_succ_subset
    (X : Set ℕ)
    (a : ℕ → ℕ)
    (n : ℕ) :
    remaining X a (n + 1)
      ⊆
    remaining X a n := by

  intro x hx

  rcases hx with ⟨hxX, hxFresh⟩

  constructor

  · exact hxX

  · intro m hm

    exact hxFresh m (by omega)


/-!
============================================================
a n ≤ a (n+1)
============================================================
-/

theorem selected_le_succ
    (X : Set ℕ)
    (a : ℕ → ℕ)
    (hLeast : IsRecursiveMinimum X a)
    (n : ℕ) :
    a n ≤ a (n + 1) := by

  have hSuccMem :
      a (n + 1) ∈
        remaining X a (n + 1) := by

    exact
      selected_mem_remaining
        X
        a
        hLeast
        (n + 1)

  have hSuccOld :
      a (n + 1) ∈
        remaining X a n := by

    exact
      remaining_succ_subset
        X
        a
        n
        hSuccMem

  exact
    (hLeast n).2
      hSuccOld


/-!
============================================================
a (n+1) ≠ a n
============================================================
-/

theorem selected_succ_ne
    (X : Set ℕ)
    (a : ℕ → ℕ)
    (hLeast : IsRecursiveMinimum X a)
    (n : ℕ) :
    a (n + 1) ≠ a n := by

  have hSuccMem :
      a (n + 1) ∈
        remaining X a (n + 1) := by

    exact
      selected_mem_remaining
        X
        a
        hLeast
        (n + 1)

  have hFresh :
      ∀ m : ℕ,
        m < n + 1 →
        a (n + 1) ≠ a m := by

    exact hSuccMem.2

  exact hFresh n (by omega)


/-!
============================================================
a n < a (n+1)
============================================================
-/

theorem selected_lt_succ
    (X : Set ℕ)
    (a : ℕ → ℕ)
    (hLeast : IsRecursiveMinimum X a)
    (n : ℕ) :
    a n < a (n + 1) := by

  have hle :
      a n ≤ a (n + 1) := by

    exact selected_le_succ
      X
      a
      hLeast
      n

  have hne :
      a (n + 1) ≠ a n := by

    exact selected_succ_ne
      X
      a
      hLeast
      n

  omega


/-!
============================================================
Gap 2

The sequence is strictly increasing.
============================================================
-/

theorem selected_strictMono
    (X : Set ℕ)
    (a : ℕ → ℕ)
    (hLeast : IsRecursiveMinimum X a) :
    StrictMono a := by

  intro m n hmn

  induction n with

  | zero =>
      omega

  | succ n ih =>

      by_cases hmn' : m = n

      · subst m

        exact selected_lt_succ
          X
          a
          hLeast
          n

      · have hm_lt_n :
            m < n := by
          omega

        have hmnValues :
            a m < a n := by

          exact ih hm_lt_n

        have hnSucc :
            a n < a (n + 1) := by

          exact selected_lt_succ
            X
            a
            hLeast
            n

        exact lt_trans
          hmnValues
          hnSucc


/-!
============================================================
Gap 3

Distinct indices give distinct values.
============================================================
-/

theorem selected_ne_of_ne
    (X : Set ℕ)
    (a : ℕ → ℕ)
    (hLeast : IsRecursiveMinimum X a)
    {n m : ℕ}
    (hnm : n ≠ m) :
    a n ≠ a m := by

  have hInjective :
      Function.Injective a := by

    exact
      (selected_strictMono
        X
        a
        hLeast).injective

  intro hEq

  apply hnm

  exact hInjective hEq


theorem selected_injective
    (X : Set ℕ)
    (a : ℕ → ℕ)
    (hLeast : IsRecursiveMinimum X a) :
    Function.Injective a := by

  exact
    (selected_strictMono
      X
      a
      hLeast).injective


/-!
============================================================
Exercise 8.1.3

All four gaps packaged together.
============================================================
-/

theorem exercise_8_1_3
    (X : Set ℕ)
    (a : ℕ → ℕ)
    (hX : ¬ X.Finite)
    (hLeast : IsRecursiveMinimum X a) :
    (∀ n : ℕ,
      ¬ (remaining X a n).Finite)
    ∧
    StrictMono a
    ∧
    (∀ n m : ℕ,
      n ≠ m →
      a n ≠ a m)
    ∧
    (∀ n : ℕ,
      a n ∈ X) := by

  constructor

  · intro n

    exact remaining_infinite
      X
      a
      hX
      n

  constructor

  · exact selected_strictMono
      X
      a
      hLeast

  constructor

  · intro n m hnm

    exact selected_ne_of_ne
      X
      a
      hLeast
      hnm

  · intro n

    exact selected_mem_X
      X
      a
      hLeast
      n

end TaoExercise8_1_3
