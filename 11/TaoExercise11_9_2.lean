import Mathlib

namespace TaoExercise11_9_2

open Set

/-!
============================================================
Antiderivative on a set
============================================================
-/

def IsAntiderivativeOn
    (f F : ℝ → ℝ)
    (I : Set ℝ) : Prop :=
  ∀ x ∈ I,
    HasDerivWithinAt F (f x) I x


/-!
============================================================
Difference of two antiderivatives has derivative zero
============================================================
-/

lemma hasDerivWithinAt_sub_zero
    {f F G : ℝ → ℝ}
    {I : Set ℝ}
    (hF : IsAntiderivativeOn f F I)
    (hG : IsAntiderivativeOn f G I)
    {x : ℝ}
    (hx : x ∈ I) :
    HasDerivWithinAt
      (fun y => F y - G y)
      0
      I
      x := by

  have hFx :
      HasDerivWithinAt F (f x) I x := by
    exact hF x hx

  have hGx :
      HasDerivWithinAt G (f x) I x := by
    exact hG x hx

  have hsub :
      HasDerivWithinAt
        (fun y => F y - G y)
        (f x - f x)
        I
        x := by
    exact hFx.sub hGx

  simpa using hsub


/-!
============================================================
Differentiability of F - G
============================================================
-/

lemma differentiableOn_sub
    {f F G : ℝ → ℝ}
    {I : Set ℝ}
    (hF : IsAntiderivativeOn f F I)
    (hG : IsAntiderivativeOn f G I) :
    DifferentiableOn ℝ
      (fun x => F x - G x)
      I := by

  intro x hx

  exact
    (hasDerivWithinAt_sub_zero
      hF
      hG
      hx).differentiableWithinAt


/-!
============================================================
Closed interval version of Lemma 11.9.5
============================================================
-/

theorem lemma_11_9_5_Icc
    {a b : ℝ}
    (hab : a < b)
    (f F G : ℝ → ℝ)
    (hF :
      IsAntiderivativeOn
        f
        F
        (Icc a b))
    (hG :
      IsAntiderivativeOn
        f
        G
        (Icc a b)) :
    ∃ C : ℝ,
      ∀ x ∈ Icc a b,
        F x = G x + C := by

  let H : ℝ → ℝ :=
    fun x => F x - G x

  have hHdiff :
      DifferentiableOn ℝ H (Icc a b) := by

    intro x hx

    change
      DifferentiableWithinAt ℝ
        (fun y => F y - G y)
        (Icc a b)
        x

    exact
      (hasDerivWithinAt_sub_zero
        hF
        hG
        hx).differentiableWithinAt

  have hHderiv :
      ∀ x ∈ Ico a b,
        derivWithin H (Icc a b) x = 0 := by

    intro x hx

    have hxIcc :
        x ∈ Icc a b := by
      exact ⟨hx.1, le_of_lt hx.2⟩

    have hzero :
        HasDerivWithinAt H 0 (Icc a b) x := by

      change
        HasDerivWithinAt
          (fun y => F y - G y)
          0
          (Icc a b)
          x

      exact
        hasDerivWithinAt_sub_zero
          hF
          hG
          hxIcc

    have hud :
        UniqueDiffWithinAt ℝ
          (Icc a b)
          x := by

      exact
        (uniqueDiffOn_Icc hab)
          x
          hxIcc

    exact hzero.derivWithin hud

  have hconst :
      ∀ x ∈ Icc a b,
        H x = H a := by

    exact
      constant_of_derivWithin_zero
        hHdiff
        hHderiv

  refine ⟨F a - G a, ?_⟩

  intro x hx

  have hxconst :
      H x = H a := by
    exact hconst x hx

  dsimp [H] at hxconst

  linarith


/-!
============================================================
Version with a ≤ b

This also handles the singleton case a = b.
============================================================
-/

theorem lemma_11_9_5_Icc_le
    {a b : ℝ}
    (hab : a ≤ b)
    (f F G : ℝ → ℝ)
    (hF :
      IsAntiderivativeOn
        f
        F
        (Icc a b))
    (hG :
      IsAntiderivativeOn
        f
        G
        (Icc a b)) :
    ∃ C : ℝ,
      ∀ x ∈ Icc a b,
        F x = G x + C := by

  by_cases heq : a = b

  · subst b

    refine ⟨F a - G a, ?_⟩

    intro x hx

    have hxEq :
        x = a := by
      exact le_antisymm hx.2 hx.1

    subst x

    ring

  · have hablt :
        a < b := by
      exact lt_of_le_of_ne hab heq

    exact lemma_11_9_5_Icc
      hablt
      f
      F
      G
      hF
      hG


/-!
============================================================
Empty interval version
============================================================
-/

theorem lemma_11_9_5_empty
    (f F G : ℝ → ℝ) :
    ∃ C : ℝ,
      ∀ x ∈ (∅ : Set ℝ),
        F x = G x + C := by

  refine ⟨0, ?_⟩

  intro x hx

  exact False.elim hx


/-!
============================================================
Exercise 11.9.2
============================================================
-/

theorem exercise_11_9_2
    {a b : ℝ}
    (hab : a ≤ b)
    (f F G : ℝ → ℝ)
    (hF :
      IsAntiderivativeOn
        f
        F
        (Icc a b))
    (hG :
      IsAntiderivativeOn
        f
        G
        (Icc a b)) :
    ∃ C : ℝ,
      ∀ x ∈ Icc a b,
        F x = G x + C := by

  exact lemma_11_9_5_Icc_le
    hab
    f
    F
    G
    hF
    hG

end TaoExercise11_9_2
