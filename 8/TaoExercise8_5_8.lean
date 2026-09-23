import Mathlib

namespace TaoExercise8_5_8

universe u

/-!
============================================================
Minimum / maximum of a subset
============================================================
-/

def IsMinimum
    {X : Type u}
    [LinearOrder X]
    (Y : Set X)
    (m : X) : Prop :=
  m ∈ Y ∧
  ∀ y : X, y ∈ Y → m ≤ y


def IsMaximum
    {X : Type u}
    [LinearOrder X]
    (Y : Set X)
    (M : X) : Prop :=
  M ∈ Y ∧
  ∀ y : X, y ∈ Y → y ≤ M


/-!
============================================================
Finite nonempty subset has a minimum
============================================================
-/

theorem finite_nonempty_has_minimum
    {X : Type u}
    [LinearOrder X]
    {Y : Set X}
    (hfin : Y.Finite)
    (hne : Y.Nonempty) :
    ∃ m : X, IsMinimum Y m := by
  classical

  letI : Finite Y := hfin
  letI : Fintype Y := Fintype.ofFinite Y

  rcases hne with ⟨y₀, hy₀⟩

  let y₀' : Y := ⟨y₀, hy₀⟩

  have huniv :
      (Finset.univ : Finset Y).Nonempty := by
    exact ⟨y₀', Finset.mem_univ y₀'⟩

  let m' : Y :=
    (Finset.univ : Finset Y).min' huniv

  refine ⟨m'.1, ?_⟩

  constructor

  · exact m'.2

  · intro y hy

    let y' : Y := ⟨y, hy⟩

    have hle :
        m' ≤ y' := by
      dsimp [m']
      exact
        Finset.min'_le
          (Finset.univ : Finset Y)
          y'
          (Finset.mem_univ y')

    exact hle


/-!
============================================================
Finite nonempty subset has a maximum
============================================================
-/

theorem finite_nonempty_has_maximum
    {X : Type u}
    [LinearOrder X]
    {Y : Set X}
    (hfin : Y.Finite)
    (hne : Y.Nonempty) :
    ∃ M : X, IsMaximum Y M := by
  classical

  letI : Finite Y := hfin
  letI : Fintype Y := Fintype.ofFinite Y

  rcases hne with ⟨y₀, hy₀⟩

  let y₀' : Y := ⟨y₀, hy₀⟩

  have huniv :
      (Finset.univ : Finset Y).Nonempty := by
    exact ⟨y₀', Finset.mem_univ y₀'⟩

  let M' : Y :=
    (Finset.univ : Finset Y).max' huniv

  refine ⟨M'.1, ?_⟩

  constructor

  · exact M'.2

  · intro y hy

    let y' : Y := ⟨y, hy⟩

    have hle :
        y' ≤ M' := by
      dsimp [M']
      exact
        Finset.le_max'
          (Finset.univ : Finset Y)
          y'
          (Finset.mem_univ y')

    exact hle


/-!
============================================================
Both minimum and maximum
============================================================
-/

theorem finite_nonempty_has_min_and_max
    {X : Type u}
    [LinearOrder X]
    {Y : Set X}
    (hfin : Y.Finite)
    (hne : Y.Nonempty) :
    (∃ m : X, IsMinimum Y m)
      ∧
    (∃ M : X, IsMaximum Y M) := by

  constructor

  · exact finite_nonempty_has_minimum
      hfin
      hne

  · exact finite_nonempty_has_maximum
      hfin
      hne


/-!
============================================================
Exercise 8.5.8
============================================================
-/

theorem exercise_8_5_8
    {X : Type u}
    [LinearOrder X]
    {Y : Set X}
    (hfin : Y.Finite)
    (hne : Y.Nonempty) :
    (∃ m : X, IsMinimum Y m)
      ∧
    (∃ M : X, IsMaximum Y M) := by

  exact finite_nonempty_has_min_and_max
    hfin
    hne


/-!
============================================================
Every subset of a finite type is finite
============================================================
-/

theorem subset_finite_of_finite_type
    {X : Type u}
    [Finite X]
    (Y : Set X) :
    Y.Finite := by

  exact
    Finite.of_injective
      (fun y : Y => y.1)
      Subtype.val_injective


/-!
============================================================
Finite total orders are well ordered
============================================================

Every nonempty subset has a minimum.
-/

theorem finite_linear_order_well_ordered
    {X : Type u}
    [LinearOrder X]
    [Finite X] :
    ∀ Y : Set X,
      Y.Nonempty →
      ∃ m : X, IsMinimum Y m := by

  intro Y hne

  have hfin :
      Y.Finite := by
    exact subset_finite_of_finite_type Y

  exact finite_nonempty_has_minimum
    hfin
    hne


/-!
============================================================
Expanded well-ordering statement
============================================================
-/

theorem finite_linear_order_every_nonempty_subset_has_least
    {X : Type u}
    [LinearOrder X]
    [Finite X]
    (Y : Set X)
    (hne : Y.Nonempty) :
    ∃ m : X,
      m ∈ Y ∧
      ∀ y : X, y ∈ Y → m ≤ y := by

  exact finite_linear_order_well_ordered
    Y
    hne

end TaoExercise8_5_8
