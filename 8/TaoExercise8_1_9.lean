import Mathlib

namespace TaoExercise8_1_9

open Set

universe u v

/-!
============================================================
The union indexed by a set I
============================================================

For

    I : Set ι
    A : ι → Set α

the expression

    ⋃ i, ⋃ (_ : i ∈ I), A i

means

    ⋃_{i ∈ I} Aᵢ.
-/

def indexedUnion
    {ι : Type u}
    {α : Type v}
    (I : Set ι)
    (A : ι → Set α) : Set α :=
  ⋃ i, ⋃ (_ : i ∈ I), A i


/-!
============================================================
Membership characterization
============================================================
-/

theorem mem_indexedUnion_iff
    {ι : Type u}
    {α : Type v}
    (I : Set ι)
    (A : ι → Set α)
    (x : α) :
    x ∈ indexedUnion I A ↔
      ∃ i : ι, i ∈ I ∧ x ∈ A i := by

  constructor

  · intro hx

    unfold indexedUnion at hx

    simp only [Set.mem_iUnion] at hx

    rcases hx with ⟨i, hi⟩
    rcases hi with ⟨hI, hxA⟩

    exact ⟨i, hI, hxA⟩

  · rintro ⟨i, hi, hxA⟩

    unfold indexedUnion

    simp only [Set.mem_iUnion]

    exact ⟨i, ⟨hi, hxA⟩⟩


/-!
============================================================
Exercise 8.1.9
============================================================

If I is at most countable and every Aᵢ,
for i ∈ I, is at most countable, then

    ⋃_{i ∈ I} Aᵢ

is at most countable.
-/

theorem exercise_8_1_9
    {ι : Type u}
    {α : Type v}
    (I : Set ι)
    (A : ι → Set α)
    (hI : I.Countable)
    (hA : ∀ i : ι, i ∈ I → (A i).Countable) :
    (indexedUnion I A).Countable := by

  unfold indexedUnion

  exact hI.biUnion hA


/-!
============================================================
Same result without the helper definition
============================================================
-/

theorem exercise_8_1_9_direct
    {ι : Type u}
    {α : Type v}
    (I : Set ι)
    (A : ι → Set α)
    (hI : I.Countable)
    (hA : ∀ i : ι, i ∈ I → (A i).Countable) :
    (⋃ i, ⋃ (_ : i ∈ I), A i).Countable := by

  exact hI.biUnion hA


/-!
============================================================
In particular: a sequence of countable sets
has countable union.
============================================================
-/

theorem countable_iUnion_nat
    {α : Type v}
    (A : ℕ → Set α)
    (hA : ∀ n : ℕ, (A n).Countable) :
    (⋃ n : ℕ, A n).Countable := by

  exact Set.countable_iUnion hA


/-!
============================================================
More general version

Any countable index type gives a countable union.
============================================================
-/

theorem countable_iUnion
    {ι : Type u}
    {α : Type v}
    [Countable ι]
    (A : ι → Set α)
    (hA : ∀ i : ι, (A i).Countable) :
    (⋃ i : ι, A i).Countable := by

  exact Set.countable_iUnion hA


/-!
============================================================
The union over a countable set I is literally the
set of elements belonging to at least one Aᵢ.
============================================================
-/

theorem indexedUnion_eq_setOf
    {ι : Type u}
    {α : Type v}
    (I : Set ι)
    (A : ι → Set α) :
    indexedUnion I A =
      {x : α | ∃ i : ι, i ∈ I ∧ x ∈ A i} := by

  ext x

  exact mem_indexedUnion_iff I A x

end TaoExercise8_1_9
