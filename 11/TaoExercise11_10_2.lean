import Mathlib

namespace TaoExercise11_10_2

open Set

/-!
============================================================
Tao-style connected subsets of ℝ
============================================================
-/

def ConnectedTao (S : Set ℝ) : Prop :=
  ∀ ⦃x y z : ℝ⦄,
    x ∈ S →
    y ∈ S →
    x ≤ z →
    z ≤ y →
    z ∈ S


/-!
============================================================
Finite partitions
============================================================
-/

def IsPartition
    (I : Set ℝ)
    (P : Finset (Set ℝ)) : Prop :=
  (∀ J ∈ P, J ⊆ I) ∧
  (∀ x ∈ I,
    ∃! J : Set ℝ,
      J ∈ P ∧ x ∈ J)


/-!
============================================================
Piecewise constant functions
============================================================
-/

def PiecewiseConstantOn
    (f : ℝ → ℝ)
    (P : Finset (Set ℝ)) : Prop :=
  ∀ J ∈ P,
    ∃ c : ℝ,
      ∀ x ∈ J,
        f x = c


/-!
============================================================
Restricted preimage
============================================================

We work with

  I ∩ φ⁻¹(J)

because φ is only relevant on the original interval I.
-/

def restrictedPreimage
    (I : Set ℝ)
    (φ : ℝ → ℝ)
    (J : Set ℝ) :
    Set ℝ :=
  I ∩ φ ⁻¹' J


/-!
============================================================
1. The preimage of a connected interval is connected
============================================================
-/

lemma restrictedPreimage_connected
    (I J : Set ℝ)
    (φ : ℝ → ℝ)
    (hI : ConnectedTao I)
    (hJ : ConnectedTao J)
    (hmono : MonotoneOn φ I) :
    ConnectedTao (restrictedPreimage I φ J) := by

  intro x y z hx hy hxz hzy

  have hxI :
      x ∈ I := by
    exact hx.1

  have hyI :
      y ∈ I := by
    exact hy.1

  have hzI :
      z ∈ I := by

    exact hI
      hxI
      hyI
      hxz
      hzy

  have hxJ :
      φ x ∈ J := by
    exact hx.2

  have hyJ :
      φ y ∈ J := by
    exact hy.2

  have hφxz :
      φ x ≤ φ z := by

    exact hmono
      hxI
      hzI
      hxz

  have hφzy :
      φ z ≤ φ y := by

    exact hmono
      hzI
      hyI
      hzy

  constructor

  · exact hzI

  · exact hJ
      hxJ
      hyJ
      hφxz
      hφzy


/-!
============================================================
2. The constant value passes through composition
============================================================
-/

lemma constantOn_comp_restrictedPreimage
    (I J : Set ℝ)
    (φ f : ℝ → ℝ)
    (c : ℝ)
    (hf :
      ∀ y ∈ J,
        f y = c) :
    ∀ x ∈ restrictedPreimage I φ J,
      f (φ x) = c := by

  intro x hx

  exact hf
    (φ x)
    hx.2


/-!
============================================================
Pullback partition
============================================================
-/

noncomputable def pullbackPartition
    (I : Set ℝ)
    (φ : ℝ → ℝ)
    (P : Finset (Set ℝ)) :
    Finset (Set ℝ) := by

  classical

  exact P.image
    (fun J =>
      restrictedPreimage I φ J)


/-!
Every pullback piece is contained in I.
-/

lemma pullbackPiece_subset
    (I : Set ℝ)
    (φ : ℝ → ℝ)
    (P : Finset (Set ℝ))
    (K : Set ℝ)
    (hK :
      K ∈ pullbackPartition I φ P) :
    K ⊆ I := by

  classical

  unfold pullbackPartition at hK

  obtain ⟨J, _hJ, rfl⟩ :=
    Finset.mem_image.mp hK

  intro x hx

  exact hx.1


/-!
============================================================
3. Pullback of a partition is a partition
============================================================
-/

theorem pullbackPartition_isPartition
    (I R : Set ℝ)
    (φ : ℝ → ℝ)
    (P : Finset (Set ℝ))
    (hP :
      IsPartition R P)
    (hmap :
      MapsTo φ I R) :
    IsPartition I
      (pullbackPartition I φ P) := by

  classical

  constructor

  · intro K hK

    exact pullbackPiece_subset
      I
      φ
      P
      K
      hK

  · intro x hxI

    have hφxR :
        φ x ∈ R := by

      exact hmap hxI

    obtain ⟨J, ⟨hJP, hφxJ⟩, huniqJ⟩ :=
      hP.2 (φ x) hφxR

    let K : Set ℝ :=
      restrictedPreimage I φ J

    have hKQ :
        K ∈ pullbackPartition I φ P := by

      unfold pullbackPartition

      apply Finset.mem_image.mpr

      exact ⟨J, hJP, rfl⟩

    have hxK :
        x ∈ K := by

      exact ⟨hxI, hφxJ⟩

    refine ⟨K, ⟨hKQ, hxK⟩, ?_⟩

    intro K' hK'x

    obtain ⟨hK'Q, hxK'⟩ := hK'x

    unfold pullbackPartition at hK'Q

    obtain ⟨J', hJ'P, hJ'eq⟩ :=
      Finset.mem_image.mp hK'Q

    have hxPreJ' :
        x ∈ restrictedPreimage I φ J' := by

      rw [hJ'eq]

      exact hxK'

    have hφxJ' :
        φ x ∈ J' := by

      exact hxPreJ'.2

    have hJJ' :
        J' = J := by

      exact huniqJ
        J'
        ⟨hJ'P, hφxJ'⟩

    subst J'

    exact hJ'eq.symm


/-!
============================================================
4. f ∘ φ is piecewise constant on the pullback partition
============================================================
-/

theorem piecewiseConstant_comp_pullback
    (I : Set ℝ)
    (φ f : ℝ → ℝ)
    (P : Finset (Set ℝ))
    (hf :
      PiecewiseConstantOn f P) :
    PiecewiseConstantOn
      (fun x => f (φ x))
      (pullbackPartition I φ P) := by

  classical

  intro K hK

  unfold pullbackPartition at hK

  obtain ⟨J, hJP, rfl⟩ :=
    Finset.mem_image.mp hK

  obtain ⟨c, hc⟩ :=
    hf J hJP

  refine ⟨c, ?_⟩

  intro x hx

  exact constantOn_comp_restrictedPreimage
    I
    J
    φ
    f
    c
    hc
    x
    hx


/-!
============================================================
5. Image of the restricted preimage
============================================================

If J ⊆ φ '' I, then

  φ '' (I ∩ φ⁻¹(J)) = J.
-/

lemma image_restrictedPreimage
    (I J : Set ℝ)
    (φ : ℝ → ℝ)
    (hJ :
      J ⊆ φ '' I) :
    φ '' (restrictedPreimage I φ J) = J := by

  ext y

  constructor

  · intro hy

    obtain ⟨x, hx, rfl⟩ := hy

    exact hx.2

  · intro hyJ

    have hyImage :
        y ∈ φ '' I := by

      exact hJ hyJ

    obtain ⟨x, hxI, hxy⟩ :=
      hyImage

    refine ⟨x, ?_, hxy⟩

    constructor

    · exact hxI

    · change φ x ∈ J

      rw [hxy]

      exact hyJ


/-!
For a whole partition P of R, surjectivity of φ from I onto R
gives the image equality for every partition piece.
-/

lemma image_pullback_piece_eq
    (I R : Set ℝ)
    (φ : ℝ → ℝ)
    (P : Finset (Set ℝ))
    (hP :
      IsPartition R P)
    (hsurj :
      R ⊆ φ '' I)
    (J : Set ℝ)
    (hJ :
      J ∈ P) :
    φ '' (restrictedPreimage I φ J) = J := by

  apply image_restrictedPreimage
    I
    J
    φ

  intro y hyJ

  apply hsurj

  exact hP.1
    J
    hJ
    hyJ


/-!
============================================================
Length/content consequence
============================================================
-/

lemma pullback_image_length_eq
    (I R : Set ℝ)
    (φ : ℝ → ℝ)
    (P : Finset (Set ℝ))
    (len : Set ℝ → ℝ)
    (hP :
      IsPartition R P)
    (hsurj :
      R ⊆ φ '' I)
    (J : Set ℝ)
    (hJ :
      J ∈ P) :
    len (φ '' (restrictedPreimage I φ J))
      =
    len J := by

  rw [
    image_pullback_piece_eq
      I
      R
      φ
      P
      hP
      hsurj
      J
      hJ
  ]


/-!
============================================================
Constant value statement for a specific piece
============================================================
-/

lemma piece_constant_after_pullback
    (I : Set ℝ)
    (φ f : ℝ → ℝ)
    (P : Finset (Set ℝ))
    (J : Set ℝ)
    (hJ :
      J ∈ P)
    (hf :
      PiecewiseConstantOn f P) :
    ∃ c : ℝ,
      ∀ x ∈ restrictedPreimage I φ J,
        f (φ x) = c := by

  obtain ⟨c, hc⟩ :=
    hf J hJ

  refine ⟨c, ?_⟩

  exact constantOn_comp_restrictedPreimage
    I
    J
    φ
    f
    c
    hc


/-!
============================================================
Exercise 11.10.2
============================================================

This packages the main structural statements used in
Lemma 11.10.5.
-/

theorem exercise_11_10_2
    (I R : Set ℝ)
    (φ f : ℝ → ℝ)
    (P : Finset (Set ℝ))
    (hI :
      ConnectedTao I)
    (hPiecesConnected :
      ∀ J ∈ P,
        ConnectedTao J)
    (hmono :
      MonotoneOn φ I)
    (hmap :
      MapsTo φ I R)
    (hsurj :
      R ⊆ φ '' I)
    (hP :
      IsPartition R P)
    (hf :
      PiecewiseConstantOn f P) :
    IsPartition I
        (pullbackPartition I φ P)
      ∧
    PiecewiseConstantOn
        (fun x => f (φ x))
        (pullbackPartition I φ P)
      ∧
    (∀ J ∈ P,
      ConnectedTao
        (restrictedPreimage I φ J))
      ∧
    (∀ J ∈ P,
      φ '' (restrictedPreimage I φ J) = J) := by

  refine ⟨?_, ?_, ?_, ?_⟩

  · exact pullbackPartition_isPartition
      I
      R
      φ
      P
      hP
      hmap

  · exact piecewiseConstant_comp_pullback
      I
      φ
      f
      P
      hf

  · intro J hJ

    exact restrictedPreimage_connected
      I
      J
      φ
      hI
      (hPiecesConnected J hJ)
      hmono

  · intro J hJ

    exact image_pullback_piece_eq
      I
      R
      φ
      P
      hP
      hsurj
      J
      hJ

end TaoExercise11_10_2
