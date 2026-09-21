import Mathlib

namespace TaoExercise3_4_6

open Set

universe u

variable {X : Type u}

/--
The characteristic function of a subset A ⊆ X.

It takes the value `true` exactly on the elements of A.
-/
noncomputable def characteristic
    (A : Set X) :
    X → Bool := by
  classical
  exact fun x =>
    if x ∈ A then true else false


/--
The inverse image of `{true}` under the characteristic
function of A is exactly A.

This is the key observation in Tao's proof.
-/
theorem characteristic_preimage_true
    (A : Set X) :
    characteristic A ⁻¹' ({true} : Set Bool) = A := by
  classical

  ext x

  simp [characteristic]


/--
The collection obtained by "replacement":

take every function

    f : X → Bool

and replace it by

    f⁻¹({true}).

In Lean this replacement construction is represented by `Set.range`.
-/
def representedSubsets :
    Set (Set X) :=
  Set.range
    (fun f : X → Bool =>
      f ⁻¹' ({true} : Set Bool))


/--
Every subset of X occurs as the inverse image of `{true}`
under some function X → Bool.

The required function is its characteristic function.
-/
theorem every_subset_is_represented
    (A : Set X) :
    A ∈ representedSubsets (X := X) := by

  refine ⟨characteristic A, ?_⟩

  exact characteristic_preimage_true A


/--
Conversely, anything produced by the replacement construction
is, by construction, a subset of X.

In Lean, an element of `Set X` is already a subset of X.
-/
theorem represented_is_subset
    (A : Set X)
    (hA : A ∈ representedSubsets (X := X)) :
    A ⊆ (Set.univ : Set X) := by
  intro x hx
  exact Set.mem_univ x


/--
The collection obtained from all characteristic functions
contains every subset of X.
-/
theorem representedSubsets_eq_univ :
    representedSubsets (X := X) = Set.univ := by
  ext A

  constructor

  · intro h
    exact Set.mem_univ A

  · intro h
    exact every_subset_is_represented A


/--
Lemma 3.4.9.

There exists a set whose elements are precisely all subsets of X.
-/
theorem lemma_3_4_9 :
    ∃ P : Set (Set X),
      ∀ A : Set X,
        A ∈ P ↔ A ⊆ (Set.univ : Set X) := by

  refine ⟨representedSubsets (X := X), ?_⟩

  intro A

  constructor

  /-
  If A belongs to our constructed collection,
  then A is a subset of X.
  -/
  · intro hA
    exact represented_is_subset A hA

  /-
  If A is a subset of X, use its characteristic function.
  -/
  · intro hA
    exact every_subset_is_represented A


/--
A cleaner formulation of the conclusion:

the range of

    f ↦ f⁻¹({true})

over all functions X → Bool is exactly the collection
of all subsets of X.
-/
theorem power_set_via_characteristic_functions :
    Set.range
        (fun f : X → Bool =>
          f ⁻¹' ({true} : Set Bool))
      =
    (Set.univ : Set (Set X)) := by

  exact representedSubsets_eq_univ

end TaoExercise3_4_6
