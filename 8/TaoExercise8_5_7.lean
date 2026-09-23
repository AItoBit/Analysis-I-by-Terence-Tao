import Mathlib

namespace TaoExercise8_5_7

universe u

/-!
============================================================
Minimal and maximal elements of a subset
============================================================
-/

def IsMinimum
    {X : Type u}
    [PartialOrder X]
    (Y : Set X)
    (m : X) : Prop :=
  m ∈ Y ∧
  ∀ y : X, y ∈ Y → m ≤ y


def IsMaximum
    {X : Type u}
    [PartialOrder X]
    (Y : Set X)
    (M : X) : Prop :=
  M ∈ Y ∧
  ∀ y : X, y ∈ Y → y ≤ M


/-!
============================================================
At most one minimum
============================================================
-/

theorem at_most_one_minimum
    {X : Type u}
    [PartialOrder X]
    (Y : Set X)
    (hYtotal :
      ∀ a : X, a ∈ Y →
      ∀ b : X, b ∈ Y →
      a ≤ b ∨ b ≤ a) :
    ∀ {m m' : X},
      IsMinimum Y m →
      IsMinimum Y m' →
      m = m' := by

  intro m m' hm hm'

  rcases hm with ⟨hmY, hmLeast⟩
  rcases hm' with ⟨hmY', hmLeast'⟩

  have hmm' :
      m ≤ m' := by
    exact hmLeast m' hmY'

  have hm'm :
      m' ≤ m := by
    exact hmLeast' m hmY

  exact le_antisymm hmm' hm'm


/-!
============================================================
At most one maximum
============================================================
-/

theorem at_most_one_maximum
    {X : Type u}
    [PartialOrder X]
    (Y : Set X)
    (hYtotal :
      ∀ a : X, a ∈ Y →
      ∀ b : X, b ∈ Y →
      a ≤ b ∨ b ≤ a) :
    ∀ {M M' : X},
      IsMaximum Y M →
      IsMaximum Y M' →
      M = M' := by

  intro M M' hM hM'

  rcases hM with ⟨hMY, hMGreatest⟩
  rcases hM' with ⟨hMY', hMGreatest'⟩

  have hMM' :
      M ≤ M' := by
    exact hMGreatest' M hMY

  have hM'M :
      M' ≤ M := by
    exact hMGreatest M' hMY'

  exact le_antisymm hMM' hM'M


/-!
============================================================
Exercise 8.5.7
============================================================
-/

theorem exercise_8_5_7
    {X : Type u}
    [PartialOrder X]
    (Y : Set X)
    (hYtotal :
      ∀ a : X, a ∈ Y →
      ∀ b : X, b ∈ Y →
      a ≤ b ∨ b ≤ a) :
    (∀ {m m' : X},
      IsMinimum Y m →
      IsMinimum Y m' →
      m = m')
    ∧
    (∀ {M M' : X},
      IsMaximum Y M →
      IsMaximum Y M' →
      M = M') := by

  constructor

  · exact at_most_one_minimum
      Y
      hYtotal

  · exact at_most_one_maximum
      Y
      hYtotal

end TaoExercise8_5_7
