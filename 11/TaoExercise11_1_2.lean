import Mathlib

namespace TaoExercise11_1_2

open Set

/-!
============================================================
Definitions from Exercise 11.1.1
============================================================
-/

def IsBoundedSetTao
    (X : Set ℝ) : Prop :=
  ∃ M : ℝ,
    0 < M ∧
    ∀ x : ℝ,
      x ∈ X →
      abs x ≤ M


def ConnectedTao
    (X : Set ℝ) : Prop :=
  ∀ x : ℝ,
    x ∈ X →
    ∀ y : ℝ,
      y ∈ X →
      x < y →
      ∀ z : ℝ,
        x < z →
        z < y →
        z ∈ X


def IsBoundedIntervalTao
    (X : Set ℝ) : Prop :=
  IsBoundedSetTao X ∧ ConnectedTao X


/-!
============================================================
The intersection of two bounded sets is bounded.

In fact, we only need the bound for I, since I ∩ J ⊆ I.
============================================================
-/

lemma bounded_inter
    (I J : Set ℝ)
    (hI : IsBoundedSetTao I) :
    IsBoundedSetTao (I ∩ J) := by

  obtain ⟨M, hM, hIM⟩ := hI

  refine ⟨M, hM, ?_⟩

  intro x hx

  exact hIM x hx.1


/-!
============================================================
The intersection of two connected subsets of ℝ is connected.
============================================================
-/

lemma connected_inter
    (I J : Set ℝ)
    (hI : ConnectedTao I)
    (hJ : ConnectedTao J) :
    ConnectedTao (I ∩ J) := by

  intro x hx y hy hxy z hxz hzy

  have hxI :
      x ∈ I := hx.1

  have hyI :
      y ∈ I := hy.1

  have hxJ :
      x ∈ J := hx.2

  have hyJ :
      y ∈ J := hy.2

  have hzI :
      z ∈ I := by
    exact hI
      x
      hxI
      y
      hyI
      hxy
      z
      hxz
      hzy

  have hzJ :
      z ∈ J := by
    exact hJ
      x
      hxJ
      y
      hyJ
      hxy
      z
      hxz
      hzy

  exact ⟨hzI, hzJ⟩


/-!
============================================================
Corollary 11.1.6

The intersection of two bounded intervals is a bounded interval.
============================================================
-/

theorem corollary_11_1_6
    (I J : Set ℝ)
    (hI : IsBoundedIntervalTao I)
    (hJ : IsBoundedIntervalTao J) :
    IsBoundedIntervalTao (I ∩ J) := by

  rcases hI with ⟨hIbounded, hIconnected⟩
  rcases hJ with ⟨hJbounded, hJconnected⟩

  constructor

  · exact bounded_inter I J hIbounded

  · exact connected_inter
      I
      J
      hIconnected
      hJconnected


/-!
============================================================
Exercise 11.1.2
============================================================
-/

theorem exercise_11_1_2
    (I J : Set ℝ)
    (hI : IsBoundedIntervalTao I)
    (hJ : IsBoundedIntervalTao J) :
    IsBoundedIntervalTao (I ∩ J) := by

  exact corollary_11_1_6 I J hI hJ

end TaoExercise11_1_2
