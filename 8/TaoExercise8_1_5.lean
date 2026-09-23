import Mathlib

namespace TaoExercise8_1_5

open Set
open Function

universe u v

/-!
============================================================
At most countable
============================================================
-/

def AtMostCountable (α : Type u) : Prop :=
  ∃ encode : α → ℕ,
    Function.Injective encode


/-!
============================================================
Countable
============================================================

Tao's convention here:

    X is countable  ↔  ℕ ≃ X.
-/

def CountableType (X : Type u) : Prop :=
  Nonempty (ℕ ≃ X)


/-!
============================================================
Proposition 8.1.8

The range of a function ℕ → Y is at most countable.
============================================================
-/

noncomputable def firstIndex
    {Y : Type v}
    (f : ℕ → Y)
    (y : {y : Y // y ∈ Set.range f}) : ℕ := by
  classical
  exact Nat.find y.property


theorem firstIndex_spec
    {Y : Type v}
    (f : ℕ → Y)
    (y : {y : Y // y ∈ Set.range f}) :
    f (firstIndex f y) = y.1 := by
  classical

  unfold firstIndex

  exact Nat.find_spec y.property


theorem firstIndex_injective
    {Y : Type v}
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


theorem proposition_8_1_8
    {Y : Type v}
    (f : ℕ → Y) :
    AtMostCountable
      {y : Y // y ∈ Set.range f} := by
  classical

  refine ⟨firstIndex f, ?_⟩

  exact firstIndex_injective f


/-!
============================================================
The map h = f ∘ g
============================================================
-/

def composedMap
    {X : Type u}
    {Y : Type v}
    (f : X → Y)
    (g : ℕ ≃ X) :
    ℕ → Y :=
  fun n => f (g n)


/-!
============================================================
Every element of range f belongs to range (f ∘ g)
============================================================

Since g : ℕ ≃ X is surjective, if

    y = f x

then

    y = f (g (g.symm x)).
-/

theorem mem_range_composed_of_mem_range
    {X : Type u}
    {Y : Type v}
    (f : X → Y)
    (g : ℕ ≃ X)
    {y : Y}
    (hy : y ∈ Set.range f) :
    y ∈ Set.range (composedMap f g) := by

  rcases hy with ⟨x, hx⟩

  refine ⟨g.symm x, ?_⟩

  unfold composedMap

  calc
    f (g (g.symm x))
        =
      f x := by
        rw [g.apply_symm_apply]

    _ = y := hx


/-!
============================================================
Embedding range f into range (f ∘ g)
============================================================

The underlying element of Y is unchanged.
-/

def toComposedRange
    {X : Type u}
    {Y : Type v}
    (f : X → Y)
    (g : ℕ ≃ X) :
    {y : Y // y ∈ Set.range f} →
      {y : Y // y ∈ Set.range (composedMap f g)} :=
  fun y =>
    ⟨
      y.1,
      mem_range_composed_of_mem_range
        f
        g
        y.2
    ⟩


theorem toComposedRange_injective
    {X : Type u}
    {Y : Type v}
    (f : X → Y)
    (g : ℕ ≃ X) :
    Function.Injective
      (toComposedRange f g) := by

  intro y₁ y₂ h

  apply Subtype.ext

  have hval :
      (toComposedRange f g y₁).1
        =
      (toComposedRange f g y₂).1 := by

    exact congrArg
      (fun z :
        {y : Y //
          y ∈ Set.range (composedMap f g)} =>
        z.1)
      h

  exact hval


/-!
============================================================
At-most-countability transfers along an injection
============================================================
-/

theorem atMostCountable_of_injective
    {A : Type u}
    {B : Type v}
    (ι : A → B)
    (hι : Function.Injective ι)
    (hB : AtMostCountable B) :
    AtMostCountable A := by

  rcases hB with ⟨encode, hEncode⟩

  refine ⟨fun a => encode (ι a), ?_⟩

  intro a₁ a₂ h

  apply hι

  apply hEncode

  exact h


/-!
============================================================
Corollary 8.1.9

If X is countable and f : X → Y, then f(X)
is at most countable.
============================================================
-/

theorem corollary_8_1_9
    {X : Type u}
    {Y : Type v}
    (f : X → Y)
    (hX : CountableType X) :
    AtMostCountable
      {y : Y // y ∈ Set.range f} := by

  rcases hX with ⟨g⟩

  let h : ℕ → Y :=
    composedMap f g

  have hRangeCountable :
      AtMostCountable
        {y : Y // y ∈ Set.range h} := by

    exact proposition_8_1_8 h

  have hInjection :
      Function.Injective
        (toComposedRange f g) := by

    exact toComposedRange_injective
      f
      g

  have hSame :
      ∀ y :
        {y : Y // y ∈ Set.range f},
        (toComposedRange f g y).1 = y.1 := by

    intro y

    rfl

  have hRangeCountable' :
      AtMostCountable
        {y : Y //
          y ∈ Set.range (composedMap f g)} := by

    simpa [h] using hRangeCountable

  exact atMostCountable_of_injective
    (toComposedRange f g)
    hInjection
    hRangeCountable'


/-!
============================================================
A stronger fact: the two ranges are actually equal
============================================================
-/

theorem range_composed_eq_range
    {X : Type u}
    {Y : Type v}
    (f : X → Y)
    (g : ℕ ≃ X) :
    Set.range (composedMap f g)
      =
    Set.range f := by

  ext y

  constructor

  · intro hy

    rcases hy with ⟨n, hn⟩

    refine ⟨g n, ?_⟩

    exact hn

  · intro hy

    exact mem_range_composed_of_mem_range
      f
      g
      hy


/-!
============================================================
Exercise 8.1.5
============================================================
-/

theorem exercise_8_1_5
    {X : Type u}
    {Y : Type v}
    (f : X → Y)
    (hX : CountableType X) :
    AtMostCountable
      {y : Y // y ∈ Set.range f} := by

  exact corollary_8_1_9
    f
    hX

end TaoExercise8_1_5
