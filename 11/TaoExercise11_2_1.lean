import Mathlib

namespace TaoExercise11_2_1

open Set

variable {α β : Type*}

/-!
============================================================
Refinement

Q is finer than P if every piece of Q is contained
in some piece of P.
============================================================
-/

def FinerThan
    (Q P : Set (Set α)) : Prop :=
  ∀ J' ∈ Q,
    ∃ J ∈ P,
      J' ⊆ J


/-!
============================================================
Piecewise constant with respect to a partition/family P

For every J ∈ P, the restriction of f to J is constant.
============================================================
-/

def PiecewiseConstantOn
    (f : α → β)
    (P : Set (Set α)) : Prop :=
  ∀ J ∈ P,
    ∃ c : β,
      ∀ x ∈ J,
        f x = c


/-!
============================================================
Lemma 11.2.7

If f is piecewise constant with respect to P,
and P' is finer than P,
then f is piecewise constant with respect to P'.
============================================================
-/

theorem lemma_11_2_7
    (f : α → β)
    (P P' : Set (Set α))
    (hf : PiecewiseConstantOn f P)
    (hrefine : FinerThan P' P) :
    PiecewiseConstantOn f P' := by

  intro J' hJ'

  obtain ⟨J, hJ, hsub⟩ :=
    hrefine J' hJ'

  obtain ⟨c, hc⟩ :=
    hf J hJ

  refine ⟨c, ?_⟩

  intro x hx

  exact hc x (hsub hx)


/-!
============================================================
Exercise 11.2.1
============================================================
-/

theorem exercise_11_2_1
    (f : ℝ → ℝ)
    (P P' : Set (Set ℝ))
    (hf : PiecewiseConstantOn f P)
    (hrefine : FinerThan P' P) :
    PiecewiseConstantOn f P' := by

  exact lemma_11_2_7
    f
    P
    P'
    hf
    hrefine

end TaoExercise11_2_1
