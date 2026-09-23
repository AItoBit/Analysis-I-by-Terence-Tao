import Mathlib

namespace TaoExercise8_1_4

open Set
open Function

/-!
============================================================
At most countable
============================================================
-/

def AtMostCountable (α : Type*) : Prop :=
  ∃ g : α → ℕ, Function.Injective g


/-!
============================================================
First occurrence
============================================================
-/

def FirstOccurrence
    {Y : Type*}
    (f : ℕ → Y)
    (n : ℕ) : Prop :=
  ∀ m : ℕ,
    m < n →
    f m ≠ f n


def FirstOccurrenceSet
    {Y : Type*}
    (f : ℕ → Y) : Set ℕ :=
  {n : ℕ | FirstOccurrence f n}


/-!
============================================================
First index of a value in the range
============================================================
-/

noncomputable def firstIndex
    {Y : Type*}
    (f : ℕ → Y)
    (y : {y : Y // y ∈ Set.range f}) : ℕ := by
  classical
  exact Nat.find y.property


theorem firstIndex_spec
    {Y : Type*}
    (f : ℕ → Y)
    (y : {y : Y // y ∈ Set.range f}) :
    f (firstIndex f y) = y.1 := by
  classical

  unfold firstIndex

  exact Nat.find_spec y.property


/-!
============================================================
The chosen index is a first occurrence
============================================================
-/

theorem firstIndex_isFirstOccurrence
    {Y : Type*}
    (f : ℕ → Y)
    (y : {y : Y // y ∈ Set.range f}) :
    FirstOccurrence f (firstIndex f y) := by
  classical

  intro m hm hEq

  have hnotEq :
      f m ≠ y.1 := by
    exact Nat.find_min y.property hm

  apply hnotEq

  calc
    f m = f (firstIndex f y) := hEq
    _ = y.1 := firstIndex_spec f y


/-!
============================================================
The first-index map is injective
============================================================
-/

theorem firstIndex_injective
    {Y : Type*}
    (f : ℕ → Y) :
    Function.Injective
      (firstIndex f :
        {y : Y // y ∈ Set.range f} → ℕ) := by
  classical

  intro y₁ y₂ hIndex

  apply Subtype.ext

  have hy₁ :
      f (firstIndex f y₁) = y₁.1 := by
    exact firstIndex_spec f y₁

  have hy₂ :
      f (firstIndex f y₂) = y₂.1 := by
    exact firstIndex_spec f y₂

  calc
    y₁.1
        =
      f (firstIndex f y₁) := hy₁.symm

    _ =
      f (firstIndex f y₂) := by
        rw [hIndex]

    _ =
      y₂.1 := hy₂


/-!
============================================================
Proposition 8.1.8
============================================================
-/

theorem proposition_8_1_8
    {Y : Type*}
    (f : ℕ → Y) :
    AtMostCountable
      {y : Y // y ∈ Set.range f} := by
  classical

  refine ⟨firstIndex f, ?_⟩

  exact firstIndex_injective f


/-!
============================================================
Tao's set A of first occurrences
============================================================
-/

def firstOccurrenceMap
    {Y : Type*}
    (f : ℕ → Y) :
    {n : ℕ // FirstOccurrence f n} →
      {y : Y // y ∈ Set.range f} :=
  fun n =>
    ⟨f n.1, ⟨n.1, rfl⟩⟩


/-!
============================================================
Injectivity of the restriction
============================================================
-/

theorem firstOccurrenceMap_injective
    {Y : Type*}
    (f : ℕ → Y) :
    Function.Injective
      (firstOccurrenceMap f) := by

  intro a b hab

  have hfab :
      f a.1 = f b.1 := by

    exact congrArg
      (fun z : {y : Y // y ∈ Set.range f} => z.1)
      hab

  apply Subtype.ext

  by_cases hablt : a.1 < b.1

  · have hne :
        f a.1 ≠ f b.1 := by

      exact b.2 a.1 hablt

    exact False.elim (hne hfab)

  · by_cases hbalt : b.1 < a.1

    · have hne :
          f b.1 ≠ f a.1 := by

        exact a.2 b.1 hbalt

      exact False.elim (hne hfab.symm)

    · omega


/-!
============================================================
Surjectivity of the restriction
============================================================
-/

theorem firstOccurrenceMap_surjective
    {Y : Type*}
    (f : ℕ → Y) :
    Function.Surjective
      (firstOccurrenceMap f) := by
  classical

  intro y

  let n : ℕ :=
    firstIndex f y

  have hn :
      FirstOccurrence f n := by

    dsimp [n]

    exact firstIndex_isFirstOccurrence
      f
      y

  let a :
      {n : ℕ // FirstOccurrence f n} :=
    ⟨n, hn⟩

  refine ⟨a, ?_⟩

  apply Subtype.ext

  change f n = y.1

  dsimp [n]

  exact firstIndex_spec
    f
    y


/-!
============================================================
Bijection between first occurrences and range
============================================================
-/

noncomputable def firstOccurrenceEquiv
    {Y : Type*}
    (f : ℕ → Y) :
    {n : ℕ // FirstOccurrence f n}
      ≃
    {y : Y // y ∈ Set.range f} := by
  classical

  exact
    Equiv.ofBijective
      (firstOccurrenceMap f)
      ⟨
        firstOccurrenceMap_injective f,
        firstOccurrenceMap_surjective f
      ⟩


/-!
============================================================
The set of first occurrences is at most countable
============================================================
-/

theorem firstOccurrenceSet_atMostCountable
    {Y : Type*}
    (f : ℕ → Y) :
    AtMostCountable
      {n : ℕ // FirstOccurrence f n} := by

  refine ⟨Subtype.val, ?_⟩

  intro a b hab

  exact Subtype.ext hab


/-!
============================================================
Exercise 8.1.4
============================================================
-/

theorem exercise_8_1_4
    {Y : Type*}
    (f : ℕ → Y) :
    AtMostCountable
      {y : Y // y ∈ Set.range f} := by

  exact proposition_8_1_8 f

end TaoExercise8_1_4
