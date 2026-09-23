import Mathlib

namespace TaoExercise8_5_9

universe u

def IsMinimum
    {X : Type u}
    [LinearOrder X]
    (A : Set X)
    (m : X) : Prop :=
  m ∈ A ∧
  ∀ x : X, x ∈ A → m ≤ x


def IsMaximum
    {X : Type u}
    [LinearOrder X]
    (A : Set X)
    (M : X) : Prop :=
  M ∈ A ∧
  ∀ x : X, x ∈ A → x ≤ M


/-!
Every nonempty subset having a minimum implies
well-foundedness of `<`.
-/

theorem wellFoundedLT_of_every_nonempty_has_minimum
    {X : Type u}
    [LinearOrder X]
    (hmin :
      ∀ A : Set X,
        A.Nonempty →
        ∃ m : X, IsMinimum A m) :
    WellFounded (fun x y : X => x < y) := by

  rw [WellFounded.wellFounded_iff_has_min]

  intro A hA

  rcases hmin A hA with ⟨m, hmA, hmLeast⟩

  refine ⟨m, hmA, ?_⟩

  intro x hx hxm

  have hmx :
      m ≤ x := by
    exact hmLeast x hx

  exact (not_lt_of_ge hmx) hxm


/-!
Every nonempty subset having a maximum implies
well-foundedness of the reverse strict order.
-/

theorem wellFoundedGT_of_every_nonempty_has_maximum
    {X : Type u}
    [LinearOrder X]
    (hmax :
      ∀ A : Set X,
        A.Nonempty →
        ∃ M : X, IsMaximum A M) :
    WellFounded (fun x y : X => y < x) := by

  rw [WellFounded.wellFounded_iff_has_min]

  intro A hA

  rcases hmax A hA with ⟨M, hMA, hMGreatest⟩

  refine ⟨M, hMA, ?_⟩

  intro x hx hMx

  have hxM :
      x ≤ M := by
    exact hMGreatest x hx

  exact (not_lt_of_ge hxM) hMx


/-!
Main lemma.
-/

theorem lemma_8_5_9
    {X : Type u}
    [LinearOrder X]
    (hmin :
      ∀ A : Set X,
        A.Nonempty →
        ∃ m : X, IsMinimum A m)
    (hmax :
      ∀ A : Set X,
        A.Nonempty →
        ∃ M : X, IsMaximum A M) :
    Finite X := by

  have hlt :
      WellFounded (fun x y : X => x < y) := by
    exact
      wellFoundedLT_of_every_nonempty_has_minimum
        hmin

  have hgt :
      WellFounded (fun x y : X => y < x) := by
    exact
      wellFoundedGT_of_every_nonempty_has_maximum
        hmax

  let wfl : WellFoundedLT X :=
    ⟨hlt.apply⟩

  let wfg : WellFoundedGT X :=
    ⟨hgt.apply⟩

  exact
    @Finite.of_wellFoundedLT_of_wellFoundedGT
      X
      inferInstance
      wfl
      wfg


/-!
Exercise 8.5.9.
-/

theorem exercise_8_5_9
    {X : Type u}
    [LinearOrder X]
    (h :
      ∀ A : Set X,
        A.Nonempty →
        (∃ m : X, IsMinimum A m) ∧
        (∃ M : X, IsMaximum A M)) :
    Finite X := by

  have hmin :
      ∀ A : Set X,
        A.Nonempty →
        ∃ m : X, IsMinimum A m := by

    intro A hA

    exact (h A hA).1

  have hmax :
      ∀ A : Set X,
        A.Nonempty →
        ∃ M : X, IsMaximum A M := by

    intro A hA

    exact (h A hA).2

  exact lemma_8_5_9
    hmin
    hmax

end TaoExercise8_5_9
