import Mathlib

namespace TaoExercise8_3_1

open Finset

universe u

/-!
============================================================
Exercise 8.3.1

If X is a finite set with n elements, then its
power set has 2^n elements.
============================================================
-/

theorem exercise_8_3_1
    {α : Type u}
    [DecidableEq α]
    (X : Finset α)
    (n : ℕ)
    (hcard : X.card = n) :
    X.powerset.card = 2 ^ n := by

  rw [Finset.card_powerset]

  rw [hcard]


/-!
============================================================
Equivalent formulation without introducing n separately
============================================================
-/

theorem powerset_card
    {α : Type u}
    [DecidableEq α]
    (X : Finset α) :
    X.powerset.card = 2 ^ X.card := by

  exact Finset.card_powerset X


/-!
============================================================
Base case from Tao's inductive proof
============================================================
-/

theorem powerset_empty
    {α : Type u}
    [DecidableEq α] :
    (∅ : Finset α).powerset.card = 1 := by

  rw [Finset.card_powerset]

  norm_num


/-!
============================================================
Inductive step in cardinal form
============================================================

If X has n+1 elements, then its powerset has 2^(n+1)
elements.
-/

theorem powerset_card_succ
    {α : Type u}
    [DecidableEq α]
    (X : Finset α)
    (n : ℕ)
    (hcard : X.card = n + 1) :
    X.powerset.card = 2 ^ (n + 1) := by

  rw [Finset.card_powerset]

  exact congrArg (fun k : ℕ => 2 ^ k) hcard


/-!
============================================================
Same result written as 2^n + 2^n
============================================================
-/

theorem powerset_card_succ_split
    {α : Type u}
    [DecidableEq α]
    (X : Finset α)
    (n : ℕ)
    (hcard : X.card = n + 1) :
    X.powerset.card = 2 ^ n + 2 ^ n := by

  rw [Finset.card_powerset]
  rw [hcard, pow_succ]

  ring

end TaoExercise8_3_1
