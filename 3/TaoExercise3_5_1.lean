import Mathlib

namespace TaoExercise3_5_1

open Set

universe u

variable {α : Type u}

/--
Kuratowski ordered pair:

    (x,y) := {{x}, {x,y}}
-/
def orderedPair (x y : α) : Set (Set α) :=
  {{x}, {x, y}}


/--
If both coordinates are equal, then the corresponding
ordered pairs are equal.
-/
lemma orderedPair_eq_of_coordinates_eq
    {x y x' y' : α}
    (hx : x = x')
    (hy : y = y') :
    orderedPair x y = orderedPair x' y' := by
  subst x'
  subst y'
  rfl


/--
Property (3.5):

    (x,y) = (x',y') ↔ x = x' ∧ y = y'.

Thus the Kuratowski definition really behaves as an ordered pair.
-/
theorem orderedPair_eq_iff
    (x y x' y' : α) :
    orderedPair x y = orderedPair x' y'
      ↔
    x = x' ∧ y = y' := by
  constructor

  /-
  Difficult direction.
  -/
  · intro h

    unfold orderedPair at h

    /-
    Equality of the two outer pair-sets gives two possibilities:

    1. {x} = {x'} and {x,y} = {x',y'}
    2. {x} = {x',y'} and {x,y} = {x'}
    -/
    rcases Set.pair_eq_pair_iff.mp h with hsame | hswap

    /-
    Case 1:
      {x} = {x'}
      {x,y} = {x',y'}
    -/
    · rcases hsame with ⟨hsingle, hpairs⟩

      have hx : x = x' := by
        exact Set.singleton_injective hsingle

      subst x'

      have hy : y = y' := by
        rcases Set.pair_eq_pair_iff.mp hpairs with hdirect | hreverse

        · exact hdirect.2

        · calc
            y = x := hreverse.2
            _ = y' := hreverse.1

      exact ⟨rfl, hy⟩

    /-
    Case 2:
      {x} = {x',y'}
      {x,y} = {x'}

    The first equality forces both x' and y' to equal x.
    The second forces y = x'.
    -/
    · rcases hswap with ⟨h1, h2⟩

      have hx' : x' = x := by
        have hm : x' ∈ ({x} : Set α) := by
          rw [h1]
          simp
        simpa using hm

      have hy' : y' = x := by
        have hm : y' ∈ ({x} : Set α) := by
          rw [h1]
          simp
        simpa using hm

      have hy : y = x' := by
        have hm : y ∈ ({x'} : Set α) := by
          rw [← h2]
          simp
        simpa using hm

      constructor

      · exact hx'.symm

      · calc
          y = x' := hy
          _ = x := hx'
          _ = y' := hy'.symm

  /-
  Easy direction:
  if x = x' and y = y', substitute.
  -/
  · rintro ⟨rfl, rfl⟩
    rfl


/--
In particular, equality of ordered pairs determines
the first coordinate.
-/
theorem orderedPair_first_coordinate
    {x y x' y' : α}
    (h : orderedPair x y = orderedPair x' y') :
    x = x' := by
  exact (orderedPair_eq_iff x y x' y').mp h |>.1


/--
And equality of ordered pairs determines
the second coordinate.
-/
theorem orderedPair_second_coordinate
    {x y x' y' : α}
    (h : orderedPair x y = orderedPair x' y') :
    y = y' := by
  exact (orderedPair_eq_iff x y x' y').mp h |>.2


/--
Cartesian product using Kuratowski ordered pairs.

Its elements are exactly the objects

    {{x}, {x,y}}

with x ∈ X and y ∈ Y.
-/
def cartesianProduct
    (X Y : Set α) :
    Set (Set (Set α)) :=
  {p | ∃ x : α, x ∈ X ∧
       ∃ y : α, y ∈ Y ∧
       p = orderedPair x y}


/--
Membership characterization of the Cartesian product.
-/
theorem mem_cartesianProduct_iff
    (X Y : Set α)
    (p : Set (Set α)) :
    p ∈ cartesianProduct X Y
      ↔
    ∃ x : α, x ∈ X ∧
      ∃ y : α, y ∈ Y ∧
        p = orderedPair x y := by
  rfl


/--
The Cartesian product exists as a set.

This is the Lean analogue of the final existence argument
using power sets and specification.
-/
theorem cartesian_product_is_set
    (X Y : Set α) :
    ∃ P : Set (Set (Set α)),
      ∀ p : Set (Set α),
        p ∈ P ↔
          ∃ x : α, x ∈ X ∧
            ∃ y : α, y ∈ Y ∧
              p = orderedPair x y := by
  refine ⟨cartesianProduct X Y, ?_⟩
  intro p
  rfl


/--
Exercise 3.5.1, packaged together:

1. Kuratowski pairs satisfy property (3.5).
2. The Cartesian product of two sets exists as a set.
-/
theorem exercise_3_5_1
    (X Y : Set α) :
    (∀ x y x' y' : α,
      orderedPair x y = orderedPair x' y'
        ↔
      x = x' ∧ y = y')
    ∧
    (∃ P : Set (Set (Set α)),
      ∀ p : Set (Set α),
        p ∈ P ↔
          ∃ x : α, x ∈ X ∧
            ∃ y : α, y ∈ Y ∧
              p = orderedPair x y) := by
  constructor

  · intro x y x' y'
    exact orderedPair_eq_iff x y x' y'

  · exact cartesian_product_is_set X Y

end TaoExercise3_5_1
