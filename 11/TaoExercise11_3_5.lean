import Mathlib

namespace TaoExercise11_3_5

open Set

/-!
============================================================
Majorization
============================================================
-/

def Majorizes
    (I : Set ℝ)
    (g f : ℝ → ℝ) : Prop :=
  ∀ x ∈ I,
    f x ≤ g x


/-!
============================================================
The possible values of p.c. integrals of majorants
============================================================
-/

def MajorantIntegralValues
    {Part : Type}
    (I : Set ℝ)
    (f : ℝ → ℝ)
    (IsPartition : Part → Prop)
    (PiecewiseConstantOn :
      (ℝ → ℝ) → Part → Prop)
    (pcIntegral :
      (ℝ → ℝ) → ℝ) :
    Set ℝ :=
  {r : ℝ |
    ∃ g : ℝ → ℝ,
    ∃ P : Part,
      IsPartition P ∧
      PiecewiseConstantOn g P ∧
      Majorizes I g f ∧
      r = pcIntegral g}


/-!
============================================================
The possible upper sums U(f,P)
============================================================
-/

def UpperSumValues
    {Part : Type}
    (f : ℝ → ℝ)
    (IsPartition : Part → Prop)
    (upperSum :
      (ℝ → ℝ) → Part → ℝ) :
    Set ℝ :=
  {r : ℝ |
    ∃ P : Part,
      IsPartition P ∧
      r = upperSum f P}


/-!
============================================================
Tao's upper Riemann integral
============================================================
-/

noncomputable def upperRiemannIntegral
    {Part : Type}
    (I : Set ℝ)
    (f : ℝ → ℝ)
    (IsPartition : Part → Prop)
    (PiecewiseConstantOn :
      (ℝ → ℝ) → Part → Prop)
    (pcIntegral :
      (ℝ → ℝ) → ℝ) :
    ℝ :=
  sInf
    (MajorantIntegralValues
      I
      f
      IsPartition
      PiecewiseConstantOn
      pcIntegral)


/-!
============================================================
inf { U(f,P) : P is a partition }
============================================================
-/

noncomputable def infUpperSums
    {Part : Type}
    (f : ℝ → ℝ)
    (IsPartition : Part → Prop)
    (upperSum :
      (ℝ → ℝ) → Part → ℝ) :
    ℝ :=
  sInf
    (UpperSumValues
      f
      IsPartition
      upperSum)


/-!
============================================================
First direction

inf_P U(f,P) ≤ upper integral.

This corresponds to the first bullet in Tao's proof.
============================================================
-/

lemma infUpperSums_le_upperRiemannIntegral
    {Part : Type}
    (I : Set ℝ)
    (f : ℝ → ℝ)
    (IsPartition : Part → Prop)
    (PiecewiseConstantOn :
      (ℝ → ℝ) → Part → Prop)
    (pcIntegral :
      (ℝ → ℝ) → ℝ)
    (upperSum :
      (ℝ → ℝ) → Part → ℝ)
    (hMajorantsNonempty :
      (MajorantIntegralValues
        I
        f
        IsPartition
        PiecewiseConstantOn
        pcIntegral).Nonempty)
    (hUpperSumsBddBelow :
      BddBelow
        (UpperSumValues
          f
          IsPartition
          upperSum))
    (hLemma11311 :
      ∀ g : ℝ → ℝ,
      ∀ P : Part,
        IsPartition P →
        PiecewiseConstantOn g P →
        Majorizes I g f →
        upperSum f P ≤ pcIntegral g) :
    infUpperSums
        f
        IsPartition
        upperSum
      ≤
    upperRiemannIntegral
        I
        f
        IsPartition
        PiecewiseConstantOn
        pcIntegral := by

  unfold infUpperSums upperRiemannIntegral

  apply le_csInf hMajorantsNonempty

  intro r hr

  obtain ⟨g, P, hP, hgPc, hgf, hr⟩ := hr

  have hUpperMem :
      upperSum f P ∈
        UpperSumValues
          f
          IsPartition
          upperSum := by

    exact ⟨P, hP, rfl⟩

  have hInfLeUpper :
      sInf
          (UpperSumValues
            f
            IsPartition
            upperSum)
        ≤
      upperSum f P := by

    exact csInf_le
      hUpperSumsBddBelow
      hUpperMem

  have hUpperLePc :
      upperSum f P ≤
        pcIntegral g := by

    exact hLemma11311
      g
      P
      hP
      hgPc
      hgf

  rw [hr]

  exact le_trans
    hInfLeUpper
    hUpperLePc


/-!
============================================================
Second direction

upper integral ≤ inf_P U(f,P).

For every partition P we construct the upper step function S:
on every J ∈ P it has value sup_{x∈J} f(x).

The hypothesis hUpperStep packages precisely that construction.
============================================================
-/

lemma upperRiemannIntegral_le_infUpperSums
    {Part : Type}
    (I : Set ℝ)
    (f : ℝ → ℝ)
    (IsPartition : Part → Prop)
    (PiecewiseConstantOn :
      (ℝ → ℝ) → Part → Prop)
    (pcIntegral :
      (ℝ → ℝ) → ℝ)
    (upperSum :
      (ℝ → ℝ) → Part → ℝ)
    (hPartitionsNonempty :
      ∃ P : Part,
        IsPartition P)
    (hMajorantsBddBelow :
      BddBelow
        (MajorantIntegralValues
          I
          f
          IsPartition
          PiecewiseConstantOn
          pcIntegral))
    (hUpperStep :
      ∀ P : Part,
        IsPartition P →
        ∃ S : ℝ → ℝ,
          PiecewiseConstantOn S P ∧
          Majorizes I S f ∧
          pcIntegral S = upperSum f P) :
    upperRiemannIntegral
        I
        f
        IsPartition
        PiecewiseConstantOn
        pcIntegral
      ≤
    infUpperSums
        f
        IsPartition
        upperSum := by

  unfold upperRiemannIntegral infUpperSums

  have hUpperSumsNonempty :
      (UpperSumValues
        f
        IsPartition
        upperSum).Nonempty := by

    obtain ⟨P, hP⟩ := hPartitionsNonempty

    exact ⟨upperSum f P, P, hP, rfl⟩

  apply le_csInf hUpperSumsNonempty

  intro r hr

  obtain ⟨P, hP, hr⟩ := hr

  obtain ⟨S, hSPc, hSmaj, hSint⟩ :=
    hUpperStep P hP

  have hMajorantMem :
      pcIntegral S ∈
        MajorantIntegralValues
          I
          f
          IsPartition
          PiecewiseConstantOn
          pcIntegral := by

    exact
      ⟨S, P, hP, hSPc, hSmaj, rfl⟩

  have hInfLe :
      sInf
          (MajorantIntegralValues
            I
            f
            IsPartition
            PiecewiseConstantOn
            pcIntegral)
        ≤
      pcIntegral S := by

    exact csInf_le
      hMajorantsBddBelow
      hMajorantMem

  rw [hr]

  rw [hSint] at hInfLe

  exact hInfLe


/-!
============================================================
Proposition 11.3.12 — upper integral
============================================================
-/

theorem proposition_11_3_12_upper
    {Part : Type}
    (I : Set ℝ)
    (f : ℝ → ℝ)
    (IsPartition : Part → Prop)
    (PiecewiseConstantOn :
      (ℝ → ℝ) → Part → Prop)
    (pcIntegral :
      (ℝ → ℝ) → ℝ)
    (upperSum :
      (ℝ → ℝ) → Part → ℝ)
    (hPartitionsNonempty :
      ∃ P : Part,
        IsPartition P)
    (hMajorantsNonempty :
      (MajorantIntegralValues
        I
        f
        IsPartition
        PiecewiseConstantOn
        pcIntegral).Nonempty)
    (hMajorantsBddBelow :
      BddBelow
        (MajorantIntegralValues
          I
          f
          IsPartition
          PiecewiseConstantOn
          pcIntegral))
    (hUpperSumsBddBelow :
      BddBelow
        (UpperSumValues
          f
          IsPartition
          upperSum))
    (hLemma11311 :
      ∀ g : ℝ → ℝ,
      ∀ P : Part,
        IsPartition P →
        PiecewiseConstantOn g P →
        Majorizes I g f →
        upperSum f P ≤ pcIntegral g)
    (hUpperStep :
      ∀ P : Part,
        IsPartition P →
        ∃ S : ℝ → ℝ,
          PiecewiseConstantOn S P ∧
          Majorizes I S f ∧
          pcIntegral S = upperSum f P) :
    upperRiemannIntegral
        I
        f
        IsPartition
        PiecewiseConstantOn
        pcIntegral
      =
    infUpperSums
        f
        IsPartition
        upperSum := by

  apply le_antisymm

  · exact
      upperRiemannIntegral_le_infUpperSums
        I
        f
        IsPartition
        PiecewiseConstantOn
        pcIntegral
        upperSum
        hPartitionsNonempty
        hMajorantsBddBelow
        hUpperStep

  · exact
      infUpperSums_le_upperRiemannIntegral
        I
        f
        IsPartition
        PiecewiseConstantOn
        pcIntegral
        upperSum
        hMajorantsNonempty
        hUpperSumsBddBelow
        hLemma11311


/-!
============================================================
Exercise 11.3.5
============================================================
-/

theorem exercise_11_3_5
    {Part : Type}
    (I : Set ℝ)
    (f : ℝ → ℝ)
    (IsPartition : Part → Prop)
    (PiecewiseConstantOn :
      (ℝ → ℝ) → Part → Prop)
    (pcIntegral :
      (ℝ → ℝ) → ℝ)
    (upperSum :
      (ℝ → ℝ) → Part → ℝ)
    (hPartitionsNonempty :
      ∃ P : Part,
        IsPartition P)
    (hMajorantsNonempty :
      (MajorantIntegralValues
        I
        f
        IsPartition
        PiecewiseConstantOn
        pcIntegral).Nonempty)
    (hMajorantsBddBelow :
      BddBelow
        (MajorantIntegralValues
          I
          f
          IsPartition
          PiecewiseConstantOn
          pcIntegral))
    (hUpperSumsBddBelow :
      BddBelow
        (UpperSumValues
          f
          IsPartition
          upperSum))
    (hLemma11311 :
      ∀ g : ℝ → ℝ,
      ∀ P : Part,
        IsPartition P →
        PiecewiseConstantOn g P →
        Majorizes I g f →
        upperSum f P ≤ pcIntegral g)
    (hUpperStep :
      ∀ P : Part,
        IsPartition P →
        ∃ S : ℝ → ℝ,
          PiecewiseConstantOn S P ∧
          Majorizes I S f ∧
          pcIntegral S = upperSum f P) :
    upperRiemannIntegral
        I
        f
        IsPartition
        PiecewiseConstantOn
        pcIntegral
      =
    infUpperSums
        f
        IsPartition
        upperSum := by

  exact proposition_11_3_12_upper
    I
    f
    IsPartition
    PiecewiseConstantOn
    pcIntegral
    upperSum
    hPartitionsNonempty
    hMajorantsNonempty
    hMajorantsBddBelow
    hUpperSumsBddBelow
    hLemma11311
    hUpperStep

end TaoExercise11_3_5
