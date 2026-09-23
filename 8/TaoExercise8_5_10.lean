import Mathlib

namespace TaoExercise8_5_10

universe u

def IsMinimum
    {X : Type u}
    [LinearOrder X]
    (A : Set X)
    (m : X) : Prop :=
  m ∈ A ∧
  ∀ x : X, x ∈ A → m ≤ x


def IsWellOrdered
    (X : Type u)
    [LinearOrder X] : Prop :=
  ∀ A : Set X,
    A.Nonempty →
    ∃ m : X, IsMinimum A m


theorem wellFoundedLT_of_wellOrdered
    {X : Type u}
    [LinearOrder X]
    (hX : IsWellOrdered X) :
    WellFounded (fun x y : X => x < y) := by

  rw [WellFounded.wellFounded_iff_has_min]

  intro A hA

  rcases hX A hA with ⟨m, hmA, hmLeast⟩

  refine ⟨m, hmA, ?_⟩

  intro x hx hxm

  have hmx :
      m ≤ x := by
    exact hmLeast x hx

  exact (not_lt_of_ge hmx) hxm


theorem proposition_8_5_10
    {X : Type u}
    [LinearOrder X]
    (hX : IsWellOrdered X)
    (P : X → Prop)
    (hstep :
      ∀ n : X,
        (∀ m : X, m < n → P m) →
        P n) :
    ∀ n : X, P n := by

  have hlt :
      WellFounded (fun x y : X => x < y) := by
    exact wellFoundedLT_of_wellOrdered hX

  intro n

  exact hlt.induction n
    (fun n ih =>
      hstep n ih)


theorem proposition_8_5_10_expanded
    {X : Type u}
    [LinearOrder X]
    (hX :
      ∀ A : Set X,
        A.Nonempty →
        ∃ m : X,
          m ∈ A ∧
          ∀ x : X, x ∈ A → m ≤ x)
    (P : X → Prop)
    (hstep :
      ∀ n : X,
        (∀ m : X, m < n → P m) →
        P n) :
    ∀ n : X, P n := by

  have hWell :
      IsWellOrdered X := by
    intro A hA
    exact hX A hA

  exact proposition_8_5_10
    hWell
    P
    hstep


theorem exists_least_counterexample
    {X : Type u}
    [LinearOrder X]
    (hX : IsWellOrdered X)
    (P : X → Prop)
    (hfail : ∃ x : X, ¬ P x) :
    ∃ m : X,
      ¬ P m ∧
      ∀ x : X, ¬ P x → m ≤ x := by

  let A : Set X :=
    {x : X | ¬ P x}

  have hA :
      A.Nonempty := by
    rcases hfail with ⟨x, hx⟩
    exact ⟨x, hx⟩

  rcases hX A hA with ⟨m, hmA, hmLeast⟩

  refine ⟨m, ?_, ?_⟩

  · exact hmA

  · intro x hx

    exact hmLeast x hx


theorem proposition_8_5_10_by_contradiction
    {X : Type u}
    [LinearOrder X]
    (hX : IsWellOrdered X)
    (P : X → Prop)
    (hstep :
      ∀ n : X,
        (∀ m : X, m < n → P m) →
        P n) :
    ∀ n : X, P n := by

  intro n

  by_contra hn

  have hfail :
      ∃ x : X, ¬ P x := by
    exact ⟨n, hn⟩

  obtain ⟨M, hMP, hMleast⟩ :=
    exists_least_counterexample
      hX
      P
      hfail

  have hPrevious :
      ∀ m : X, m < M → P m := by

    intro m hm

    by_contra hmP

    have hMm :
        M ≤ m := by
      exact hMleast m hmP

    exact (not_lt_of_ge hMm) hm

  have hPM :
      P M := by
    exact hstep M hPrevious

  exact hMP hPM


theorem exercise_8_5_10
    {X : Type u}
    [LinearOrder X]
    (hX : IsWellOrdered X)
    (P : X → Prop)
    (hstep :
      ∀ n : X,
        (∀ m : X, m < n → P m) →
        P n) :
    ∀ n : X, P n := by

  exact proposition_8_5_10
    hX
    P
    hstep

end TaoExercise8_5_10
