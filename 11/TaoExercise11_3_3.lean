import Mathlib

namespace TaoExercise11_3_3

open Set

/-!
============================================================
Majorization and minorization on I
============================================================
-/

def Majorizes
    (I : Set ℝ)
    (f g : ℝ → ℝ) : Prop :=
  ∀ x ∈ I,
    g x ≤ f x


def Minorizes
    (I : Set ℝ)
    (f g : ℝ → ℝ) : Prop :=
  ∀ x ∈ I,
    f x ≤ g x


/-!
Every function majorizes and minorizes itself.
-/

lemma majorizes_refl
    (I : Set ℝ)
    (f : ℝ → ℝ) :
    Majorizes I f f := by

  intro x hx

  exact le_rfl


lemma minorizes_refl
    (I : Set ℝ)
    (f : ℝ → ℝ) :
    Minorizes I f f := by

  intro x hx

  exact le_rfl


/-!
============================================================
Piecewise constant functions

We leave the actual partition structure abstract here,
because Lemma 11.3.7 only uses the fact that f itself is
an admissible piecewise-constant majorant/minorant.
============================================================
-/

def PiecewiseConstantTao
    (I : Set ℝ)
    (f : ℝ → ℝ) : Prop :=
  ∃ P : Set (Set ℝ),
    ∀ J ∈ P,
      ∃ c : ℝ,
        ∀ x ∈ J,
          f x = c


/-!
============================================================
Riemann integrability in Tao's formulation

upperIntegral f = lowerIntegral f
============================================================
-/

def RiemannIntegrableTao
    (upperIntegral lowerIntegral : (ℝ → ℝ) → ℝ)
    (f : ℝ → ℝ) : Prop :=
  upperIntegral f = lowerIntegral f


/-!
============================================================
Lemma 11.3.7

The assumptions hUpperBound and hLowerBound encode
Definition 11.3.2:

* every piecewise-constant majorant g gives
      upperIntegral f ≤ pcIntegral g

* every piecewise-constant minorant g gives
      pcIntegral g ≤ lowerIntegral f

The assumption hLowerLeUpper is Lemma 11.3.3.
============================================================
-/

theorem lemma_11_3_7
    (I : Set ℝ)
    (f : ℝ → ℝ)
    (pcIntegral : (ℝ → ℝ) → ℝ)
    (upperIntegral lowerIntegral : (ℝ → ℝ) → ℝ)
    (hf_pc : PiecewiseConstantTao I f)
    (hUpperBound :
      ∀ g : ℝ → ℝ,
        PiecewiseConstantTao I g →
        Majorizes I g f →
        upperIntegral f ≤ pcIntegral g)
    (hLowerBound :
      ∀ g : ℝ → ℝ,
        PiecewiseConstantTao I g →
        Minorizes I g f →
        pcIntegral g ≤ lowerIntegral f)
    (hLowerLeUpper :
      lowerIntegral f ≤ upperIntegral f) :
    RiemannIntegrableTao
        upperIntegral
        lowerIntegral
        f
      ∧
    upperIntegral f = pcIntegral f
      ∧
    lowerIntegral f = pcIntegral f := by

  /-
  Since f majorizes itself,
      upperIntegral f ≤ pcIntegral f.
  -/

  have hUpperLePc :
      upperIntegral f ≤ pcIntegral f := by

    exact hUpperBound
      f
      hf_pc
      (majorizes_refl I f)

  /-
  Since f minorizes itself,
      pcIntegral f ≤ lowerIntegral f.
  -/

  have hPcLeLower :
      pcIntegral f ≤ lowerIntegral f := by

    exact hLowerBound
      f
      hf_pc
      (minorizes_refl I f)

  /-
  Hence

      upper ≤ pc ≤ lower ≤ upper.

  Therefore all three quantities are equal.
  -/

  have hUpperEqPc :
      upperIntegral f = pcIntegral f := by

    apply le_antisymm

    · exact hUpperLePc

    · exact le_trans
        hPcLeLower
        hLowerLeUpper

  have hPcEqLower :
      pcIntegral f = lowerIntegral f := by

    apply le_antisymm

    · exact hPcLeLower

    · exact le_trans
        hLowerLeUpper
        hUpperLePc

  have hUpperEqLower :
      upperIntegral f = lowerIntegral f := by

    exact hUpperEqPc.trans hPcEqLower

  constructor

  · exact hUpperEqLower

  · constructor

    · exact hUpperEqPc

    · exact hPcEqLower.symm


/-!
============================================================
Exercise 11.3.3

A slightly cleaner conclusion:

f is Riemann integrable and its integral equals
its piecewise-constant integral.
============================================================
-/

theorem exercise_11_3_3
    (I : Set ℝ)
    (f : ℝ → ℝ)
    (pcIntegral : (ℝ → ℝ) → ℝ)
    (upperIntegral lowerIntegral : (ℝ → ℝ) → ℝ)
    (hf_pc : PiecewiseConstantTao I f)
    (hUpperBound :
      ∀ g : ℝ → ℝ,
        PiecewiseConstantTao I g →
        Majorizes I g f →
        upperIntegral f ≤ pcIntegral g)
    (hLowerBound :
      ∀ g : ℝ → ℝ,
        PiecewiseConstantTao I g →
        Minorizes I g f →
        pcIntegral g ≤ lowerIntegral f)
    (hLowerLeUpper :
      lowerIntegral f ≤ upperIntegral f) :
    RiemannIntegrableTao
        upperIntegral
        lowerIntegral
        f
      ∧
    upperIntegral f = pcIntegral f := by

  obtain ⟨hInt, hUpper, hLower⟩ :=
    lemma_11_3_7
      I
      f
      pcIntegral
      upperIntegral
      lowerIntegral
      hf_pc
      hUpperBound
      hLowerBound
      hLowerLeUpper

  exact ⟨hInt, hUpper⟩

end TaoExercise11_3_3
