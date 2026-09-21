import Mathlib

namespace TaoExercise3_4_7

open Set

universe u v

variable {X : Type u} {Y : Type v}

/--
A partial function from X to Y consists of

* a subset `dom ⊆ X`,
* a subset `cod ⊆ Y`,
* a function `dom → cod`.

Here `dom` and `cod` are used as subtype types.
-/
structure PartialFunction (X : Type u) (Y : Type v) where
  dom   : Set X
  cod   : Set Y
  toFun : dom → cod


/--
The collection of all partial functions from X to Y.

In Lean, once `PartialFunction X Y` is a type,
the collection of all such objects is simply `Set.univ`.
-/
def allPartialFunctions (X : Type u) (Y : Type v) :
    Set (PartialFunction X Y) :=
  Set.univ


/--
Every partial function belongs to the collection
of all partial functions.
-/
theorem mem_allPartialFunctions
    (f : PartialFunction X Y) :
    f ∈ allPartialFunctions X Y := by
  simp [allPartialFunctions]


/--
Exercise 3.4.7.

There exists a set whose elements are precisely
all partial functions from X to Y.
-/
theorem exercise_3_4_7 :
    ∃ P : Set (PartialFunction X Y),
      ∀ f : PartialFunction X Y, f ∈ P := by

  refine ⟨allPartialFunctions X Y, ?_⟩

  intro f

  exact mem_allPartialFunctions f


end TaoExercise3_4_7
