import Mathlib

namespace TaoExercise3_6_2

open Set

universe u

variable {α : Type u}

/--
A set `X` has cardinality zero iff there exists a bijection
from `X` to `Fin 0`.

`Fin 0` is the Lean analogue of the empty finite set
corresponding to `{i ∈ ℕ | 1 ≤ i ≤ 0}`.
-/
def HasCardinalityZero (X : Set α) : Prop :=
  ∃ f : X → Fin 0, Function.Bijective f


/--
The empty set has cardinality zero.
-/
theorem empty_has_cardinality_zero :
    HasCardinalityZero (∅ : Set α) := by

  let f : (∅ : Set α) → Fin 0 :=
    fun x => False.elim x.property

  refine ⟨f, ?_, ?_⟩

  /-
  Injectivity is vacuous because the domain is empty.
  -/
  · intro x x' h
    exact False.elim x.property

  /-
  Surjectivity is also vacuous because `Fin 0` is empty.
  -/
  · intro y
    exact Fin.elim0 y


/--
If a set has cardinality zero, then it is empty.
-/
theorem eq_empty_of_cardinality_zero
    (X : Set α)
    (hX : HasCardinalityZero X) :
    X = ∅ := by

  obtain ⟨f, hf⟩ := hX

  ext x
  constructor

  /-
  Suppose x ∈ X.

  Then `⟨x,hx⟩ : X`, so `f ⟨x,hx⟩ : Fin 0`.
  But `Fin 0` has no elements: contradiction.
  -/
  · intro hx

    have y : Fin 0 :=
      f ⟨x, hx⟩

    exact Fin.elim0 y

  /-
  Nothing belongs to the empty set.
  -/
  · intro hx
    exact False.elim hx


/--
Exercise 3.6.2.

A set has cardinality zero iff it is the empty set.
-/
theorem exercise_3_6_2
    (X : Set α) :
    HasCardinalityZero X ↔ X = ∅ := by
  constructor

  · intro hX
    exact eq_empty_of_cardinality_zero X hX

  · intro hX
    subst X
    exact empty_has_cardinality_zero

end TaoExercise3_6_2
