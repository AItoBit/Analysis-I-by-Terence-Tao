import Mathlib

namespace TaoExercise9_1_10

open Set

/-!
============================================================
Bounded subset of ℝ
============================================================

This follows Tao's definition:

    X is bounded iff there exists M > 0 such that
    X ⊆ [-M, M].
-/

def IsBoundedSet (X : Set ℝ) : Prop :=
  ∃ M : ℝ,
    0 < M ∧
    ∀ x : ℝ, x ∈ X →
      -M ≤ x ∧ x ≤ M


/-!
============================================================
"inf X is finite"
============================================================

We express this as the existence of a real greatest
lower bound.
-/

def HasFiniteInf (X : Set ℝ) : Prop :=
  ∃ a : ℝ, IsGLB X a


/-!
============================================================
"sup X is finite"
============================================================

We express this as the existence of a real least
upper bound.
-/

def HasFiniteSup (X : Set ℝ) : Prop :=
  ∃ b : ℝ, IsLUB X b


/-!
============================================================
A bounded nonempty set has a finite infimum
============================================================
-/

theorem finite_inf_of_bounded
    (X : Set ℝ)
    (hne : X.Nonempty)
    (hbounded : IsBoundedSet X) :
    HasFiniteInf X := by

  rcases hbounded with ⟨M, hMpos, hM⟩

  have hBelow :
      BddBelow X := by
    refine ⟨-M, ?_⟩
    intro x hx
    exact (hM x hx).1

  refine ⟨sInf X, ?_⟩

  constructor

  · intro x hx
    exact csInf_le hBelow hx

  · intro b hb
    exact le_csInf hne hb


/-!
============================================================
A bounded nonempty set has a finite supremum
============================================================
-/

theorem finite_sup_of_bounded
    (X : Set ℝ)
    (hne : X.Nonempty)
    (hbounded : IsBoundedSet X) :
    HasFiniteSup X := by

  rcases hbounded with ⟨M, hMpos, hM⟩

  have hAbove :
      BddAbove X := by
    refine ⟨M, ?_⟩
    intro x hx
    exact (hM x hx).2

  refine ⟨sSup X, ?_⟩

  constructor

  · intro x hx
    exact le_csSup hAbove hx

  · intro b hb
    exact csSup_le hne hb


/-!
============================================================
Finite infimum and supremum imply boundedness
============================================================
-/

theorem bounded_of_finite_inf_sup
    (X : Set ℝ)
    (hinf : HasFiniteInf X)
    (hsup : HasFiniteSup X) :
    IsBoundedSet X := by

  rcases hinf with ⟨a, ha⟩
  rcases hsup with ⟨b, hb⟩

  let M : ℝ :=
    max |a| |b| + 1

  have haMax :
      |a| ≤ max |a| |b| := by
    exact le_max_left _ _

  have hbMax :
      |b| ≤ max |a| |b| := by
    exact le_max_right _ _

  have hMaxNonneg :
      0 ≤ max |a| |b| := by
    exact le_trans (abs_nonneg a) haMax

  have hMpos :
      0 < M := by
    dsimp [M]
    linarith

  refine ⟨M, hMpos, ?_⟩

  intro x hx

  have hax :
      a ≤ x := by
    exact ha.1 hx

  have hxb :
      x ≤ b := by
    exact hb.1 hx

  have hNegAbsA :
      -|a| ≤ a := by
    exact neg_abs_le a

  have hbAbs :
      b ≤ |b| := by
    exact le_abs_self b

  constructor

  · dsimp [M]
    linarith

  · dsimp [M]
    linarith


/-!
============================================================
Lemma 9.1.10
============================================================

For a nonempty subset X ⊆ ℝ:

    X is bounded
      ↔
    inf X and sup X are finite.
-/

theorem lemma_9_1_10
    (X : Set ℝ)
    (hne : X.Nonempty) :
    IsBoundedSet X
      ↔
    HasFiniteInf X ∧ HasFiniteSup X := by

  constructor

  · intro hbounded

    constructor

    · exact finite_inf_of_bounded
        X
        hne
        hbounded

    · exact finite_sup_of_bounded
        X
        hne
        hbounded

  · rintro ⟨hinf, hsup⟩

    exact bounded_of_finite_inf_sup
      X
      hinf
      hsup


/-!
============================================================
Exercise 9.1.10
============================================================
-/

theorem exercise_9_1_10
    (X : Set ℝ)
    (hne : X.Nonempty) :
    IsBoundedSet X
      ↔
    HasFiniteInf X ∧ HasFiniteSup X := by

  exact lemma_9_1_10
    X
    hne

end TaoExercise9_1_10
