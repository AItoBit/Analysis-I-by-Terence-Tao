import Mathlib

namespace TaoExercise8_1_6

open Function

universe u

/-!
============================================================
At most countable
============================================================

A type is at most countable when it admits an
injective map into ℕ.
-/

def AtMostCountable
    (A : Type u) : Prop :=
  ∃ f : A → ℕ,
    Function.Injective f


/-!
============================================================
Forward direction

If A is at most countable, there exists an
injection A → ℕ.
============================================================
-/

theorem injection_of_atMostCountable
    (A : Type u)
    (hA : AtMostCountable A) :
    ∃ f : A → ℕ,
      Function.Injective f := by

  exact hA


/-!
============================================================
Backward direction

If there is an injection A → ℕ, then A is
at most countable.
============================================================
-/

theorem atMostCountable_of_injection
    (A : Type u)
    (h :
      ∃ f : A → ℕ,
        Function.Injective f) :
    AtMostCountable A := by

  exact h


/-!
============================================================
Exercise 8.1.6
============================================================

A is at most countable iff there exists an
injective map A → ℕ.
-/

theorem exercise_8_1_6
    (A : Type u) :
    AtMostCountable A
      ↔
    ∃ f : A → ℕ,
      Function.Injective f := by

  constructor

  · intro hA

    exact injection_of_atMostCountable
      A
      hA

  · intro h

    exact atMostCountable_of_injection
      A
      h


/-!
Because `AtMostCountable` was defined by the
right-hand side, Lean can also prove the theorem
by reflexivity.
-/

theorem exercise_8_1_6_short
    (A : Type u) :
    AtMostCountable A
      ↔
    ∃ f : A → ℕ,
      Function.Injective f := by

  rfl

end TaoExercise8_1_6
