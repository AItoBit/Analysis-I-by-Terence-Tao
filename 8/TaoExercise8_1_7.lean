import Mathlib

namespace TaoExercise8_1_7

open Set
open Function

universe u

/-!
============================================================
Tao's notion of countably infinite
============================================================

A set `X` is countably infinite when its subtype
is equivalent to ℕ.
-/

def CountablyInfinite
    {α : Type u}
    (X : Set α) : Prop :=
  Nonempty (ℕ ≃ X)


/-!
============================================================
A countably infinite set is countable
============================================================
-/

theorem countable_of_countablyInfinite
    {α : Type u}
    {X : Set α}
    (hX : CountablyInfinite X) :
    X.Countable := by

  rcases hX with ⟨e⟩

  rw [Set.countable_iff_exists_injective]

  refine ⟨e.symm, ?_⟩

  exact e.symm.injective


/-!
============================================================
A countably infinite set is infinite
============================================================
-/

theorem infinite_of_countablyInfinite
    {α : Type u}
    {X : Set α}
    (hX : CountablyInfinite X) :
    X.Infinite := by

  rcases hX with ⟨e⟩

  rw [← Set.infinite_coe_iff]

  exact
    (e.infinite_iff).mp
      (inferInstance : Infinite ℕ)


/-!
============================================================
The union of two countable sets is countable
============================================================
-/

theorem union_countable
    {α : Type u}
    {X Y : Set α}
    (hX : X.Countable)
    (hY : Y.Countable) :
    (X ∪ Y).Countable := by

  exact hX.union hY


/-!
============================================================
If X is infinite and X ⊆ X ∪ Y, then X ∪ Y is infinite
============================================================
-/

theorem union_infinite_of_left
    {α : Type u}
    {X Y : Set α}
    (hX : X.Infinite) :
    (X ∪ Y).Infinite := by

  exact hX.mono Set.subset_union_left


/-!
============================================================
Proposition 8.1.10

If X and Y are countably infinite, then X ∪ Y
is countably infinite.
============================================================
-/

theorem proposition_8_1_10
    {α : Type u}
    (X Y : Set α)
    (hX : CountablyInfinite X)
    (hY : CountablyInfinite Y) :
    CountablyInfinite (X ∪ Y) := by

  have hXCountable :
      X.Countable := by
    exact countable_of_countablyInfinite hX

  have hYCountable :
      Y.Countable := by
    exact countable_of_countablyInfinite hY

  have hUnionCountable :
      (X ∪ Y).Countable := by
    exact union_countable
      hXCountable
      hYCountable

  have hXInfinite :
      X.Infinite := by
    exact infinite_of_countablyInfinite hX

  have hUnionInfinite :
      (X ∪ Y).Infinite := by
    exact union_infinite_of_left hXInfinite

  letI : Countable ↑(X ∪ Y) :=
    hUnionCountable.to_subtype

  letI : Infinite ↑(X ∪ Y) :=
    hUnionInfinite.to_subtype

  have hEquiv :
      Nonempty (↑(X ∪ Y) ≃ ℕ) := by

    exact
      nonempty_equiv_of_countable

  rcases hEquiv with ⟨e⟩

  exact ⟨e.symm⟩


/-!
============================================================
Exercise 8.1.7
============================================================
-/

theorem exercise_8_1_7
    {α : Type u}
    (X Y : Set α)
    (hX : CountablyInfinite X)
    (hY : CountablyInfinite Y) :
    CountablyInfinite (X ∪ Y) := by

  exact proposition_8_1_10
    X
    Y
    hX
    hY

end TaoExercise8_1_7
