import Mathlib

namespace TaoExercise11_1_1

open Set

/-!
============================================================
Bounded set, in the epsilon-free Tao style
============================================================
-/

def IsBoundedSetTao
    (X : Set ℝ) : Prop :=
  ∃ M : ℝ,
    0 < M ∧
    ∀ x : ℝ,
      x ∈ X →
      abs x ≤ M


/-!
============================================================
Connected subset of ℝ

For subsets of ℝ, Tao's notion here is:

if x,y ∈ X and x < z < y, then z ∈ X.
============================================================
-/

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


/-!
============================================================
Tao-connected = Mathlib OrdConnected
============================================================
-/

theorem connectedTao_iff_ordConnected
    (X : Set ℝ) :
    ConnectedTao X ↔ X.OrdConnected := by

  constructor

  · intro h

    apply Set.ordConnected_of_Ioo

    intro x hx y hy hxy z hz

    exact h
      x
      hx
      y
      hy
      hxy
      z
      hz.1
      hz.2

  · intro h

    intro x hx y hy hxy z hxz hzy

    have hzIcc :
        z ∈ Set.Icc x y := by
      exact ⟨le_of_lt hxz, le_of_lt hzy⟩

    exact h.out hx hy hzIcc


/-!
============================================================
A bounded interval
============================================================

An interval is an order-connected subset of ℝ.
A bounded interval is therefore a bounded order-connected set.
-/

def IsBoundedIntervalTao
    (X : Set ℝ) : Prop :=
  IsBoundedSetTao X ∧ X.OrdConnected


/-!
============================================================
Lemma 11.1.4
============================================================
-/

theorem lemma_11_1_4
    (X : Set ℝ) :
    IsBoundedIntervalTao X ↔
      IsBoundedSetTao X ∧ ConnectedTao X := by

  constructor

  · intro h

    rcases h with ⟨hbounded, hinterval⟩

    refine ⟨hbounded, ?_⟩

    exact
      (connectedTao_iff_ordConnected X).2
        hinterval

  · intro h

    rcases h with ⟨hbounded, hconnected⟩

    refine ⟨hbounded, ?_⟩

    exact
      (connectedTao_iff_ordConnected X).1
        hconnected


/-!
============================================================
Exercise 11.1.1
============================================================
-/

theorem exercise_11_1_1
    (X : Set ℝ) :
    IsBoundedIntervalTao X ↔
      IsBoundedSetTao X ∧ ConnectedTao X := by

  exact lemma_11_1_4 X

end TaoExercise11_1_1
