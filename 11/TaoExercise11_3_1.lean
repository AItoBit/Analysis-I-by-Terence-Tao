import Mathlib

namespace TaoExercise11_3_1

open Set

/-!
============================================================
Majorization on a set I
============================================================
-/

def Majorizes
    (I : Set ℝ)
    (f g : ℝ → ℝ) : Prop :=
  ∀ x ∈ I,
    g x ≤ f x


/-!
============================================================
Transitivity
============================================================
-/

theorem majorizes_trans
    (I : Set ℝ)
    (f g h : ℝ → ℝ)
    (hfg : Majorizes I f g)
    (hgh : Majorizes I g h) :
    Majorizes I f h := by

  intro x hx

  exact le_trans
    (hgh x hx)
    (hfg x hx)


/-!
============================================================
Antisymmetry
============================================================
-/

theorem majorizes_antisymm
    (I : Set ℝ)
    (f g : ℝ → ℝ)
    (hfg : Majorizes I f g)
    (hgf : Majorizes I g f) :
    ∀ x ∈ I,
      f x = g x := by

  intro x hx

  apply le_antisymm

  · exact hgf x hx

  · exact hfg x hx


/-!
============================================================
Equality of the restrictions to I
============================================================
-/

theorem majorizes_each_other_eqOn
    (I : Set ℝ)
    (f g : ℝ → ℝ)
    (hfg : Majorizes I f g)
    (hgf : Majorizes I g f) :
    Set.EqOn f g I := by

  intro x hx

  exact majorizes_antisymm
    I
    f
    g
    hfg
    hgf
    x
    hx


/-!
============================================================
If the functions are genuinely functions I → ℝ,
then they are equal by function extensionality.
============================================================
-/

def MajorizesSubtype
    (I : Set ℝ)
    (f g : I → ℝ) : Prop :=
  ∀ x : I,
    g x ≤ f x


theorem majorizesSubtype_trans
    (I : Set ℝ)
    (f g h : I → ℝ)
    (hfg : MajorizesSubtype I f g)
    (hgh : MajorizesSubtype I g h) :
    MajorizesSubtype I f h := by

  intro x

  exact le_trans
    (hgh x)
    (hfg x)


theorem majorizesSubtype_antisymm
    (I : Set ℝ)
    (f g : I → ℝ)
    (hfg : MajorizesSubtype I f g)
    (hgf : MajorizesSubtype I g f) :
    f = g := by

  funext x

  apply le_antisymm

  · exact hgf x

  · exact hfg x


/-!
============================================================
Exercise 11.3.1
============================================================
-/

theorem exercise_11_3_1
    (I : Set ℝ)
    (f g h : I → ℝ)
    (hfg : MajorizesSubtype I f g)
    (hgh : MajorizesSubtype I g h) :
    MajorizesSubtype I f h := by

  exact majorizesSubtype_trans
    I
    f
    g
    h
    hfg
    hgh


theorem exercise_11_3_1_antisymm
    (I : Set ℝ)
    (f g : I → ℝ)
    (hfg : MajorizesSubtype I f g)
    (hgf : MajorizesSubtype I g f) :
    f = g := by

  exact majorizesSubtype_antisymm
    I
    f
    g
    hfg
    hgf

end TaoExercise11_3_1
