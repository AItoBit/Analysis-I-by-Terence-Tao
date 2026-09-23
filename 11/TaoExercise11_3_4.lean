import Mathlib

namespace TaoExercise11_3_4

open Set

/-!
============================================================
Majorization / minorization
============================================================
-/

def Majorizes
    (I : Set ℝ)
    (g f : ℝ → ℝ) : Prop :=
  ∀ x ∈ I,
    f x ≤ g x


def Minorizes
    (I : Set ℝ)
    (g f : ℝ → ℝ) : Prop :=
  ∀ x ∈ I,
    g x ≤ f x


/-!
============================================================
Piecewise constant functions on a finite partition
============================================================
-/

def PiecewiseConstantOn
    (g : ℝ → ℝ)
    (P : Finset (Set ℝ)) : Prop :=
  ∀ J ∈ P,
    ∃ c : ℝ,
      ∀ x ∈ J,
        g x = c


noncomputable def pieceValue
    (g : ℝ → ℝ)
    (J : Set ℝ) : ℝ :=
  g (Classical.epsilon (fun x : ℝ => x ∈ J))


lemma epsilon_mem
    (J : Set ℝ)
    (hJ : J.Nonempty) :
    Classical.epsilon (fun x : ℝ => x ∈ J) ∈ J := by

  exact Classical.epsilon_spec hJ


lemma eq_pieceValue_of_piecewise
    (g : ℝ → ℝ)
    (P : Finset (Set ℝ))
    (hg : PiecewiseConstantOn g P)
    (J : Set ℝ)
    (hJ : J ∈ P)
    (hJne : J.Nonempty)
    (x : ℝ)
    (hx : x ∈ J) :
    g x = pieceValue g J := by

  obtain ⟨c, hc⟩ := hg J hJ

  have hxVal :
      g x = c := by
    exact hc x hx

  have hepsVal :
      g (Classical.epsilon (fun y : ℝ => y ∈ J)) = c := by
    exact hc
      (Classical.epsilon (fun y : ℝ => y ∈ J))
      (epsilon_mem J hJne)

  unfold pieceValue

  exact hxVal.trans hepsVal.symm


/-!
============================================================
Nonempty pieces

Tao writes

  ∑_{J ∈ P, J ≠ ∅}

when defining the upper and lower sums.

We encode precisely those pieces by filtering P.
============================================================
-/

noncomputable def nonemptyPieces
    (P : Finset (Set ℝ)) :
    Finset (Set ℝ) := by

  classical

  exact P.filter (fun J => J.Nonempty)


lemma mem_nonemptyPieces
    (P : Finset (Set ℝ))
    (J : Set ℝ) :
    J ∈ nonemptyPieces P ↔
      J ∈ P ∧ J.Nonempty := by

  classical

  unfold nonemptyPieces

  simp


/-!
============================================================
Piecewise-constant integral

Since zero-length empty pieces contribute nothing, we sum
over the nonempty pieces, matching the reduced sum used
in Tao's proof of Lemma 11.3.11.
============================================================
-/

noncomputable def pcIntegral
    (len : Set ℝ → ℝ)
    (g : ℝ → ℝ)
    (P : Finset (Set ℝ)) : ℝ :=

  (nonemptyPieces P).sum
    (fun J =>
      pieceValue g J * len J)


/-!
============================================================
Upper and lower Riemann sums
============================================================
-/

noncomputable def upperSum
    (len : Set ℝ → ℝ)
    (f : ℝ → ℝ)
    (P : Finset (Set ℝ)) : ℝ :=

  (nonemptyPieces P).sum
    (fun J =>
      sSup (f '' J) * len J)


noncomputable def lowerSum
    (len : Set ℝ → ℝ)
    (f : ℝ → ℝ)
    (P : Finset (Set ℝ)) : ℝ :=

  (nonemptyPieces P).sum
    (fun J =>
      sInf (f '' J) * len J)


/-!
============================================================
A majorizing constant on J is above sup f(J)
============================================================
-/

lemma sSup_le_pieceValue
    (I : Set ℝ)
    (f g : ℝ → ℝ)
    (P : Finset (Set ℝ))
    (hg_pc : PiecewiseConstantOn g P)
    (hgf : Majorizes I g f)
    (hsub :
      ∀ J ∈ P,
        J ⊆ I)
    (J : Set ℝ)
    (hJ : J ∈ P)
    (hJne : J.Nonempty) :
    sSup (f '' J) ≤ pieceValue g J := by

  apply csSup_le

  · exact hJne.image f

  · intro y hy

    obtain ⟨x, hxJ, rfl⟩ := hy

    have hxI :
        x ∈ I := by
      exact hsub J hJ hxJ

    have hfxg :
        f x ≤ g x := by
      exact hgf x hxI

    have hgValue :
        g x = pieceValue g J := by
      exact eq_pieceValue_of_piecewise
        g
        P
        hg_pc
        J
        hJ
        hJne
        x
        hxJ

    rw [hgValue] at hfxg

    exact hfxg


/-!
============================================================
First half of Lemma 11.3.11

If g is piecewise constant and majorizes f, then

    U(f,P) ≤ pcIntegral(g,P).
============================================================
-/

theorem pcIntegral_ge_upperSum
    (I : Set ℝ)
    (len : Set ℝ → ℝ)
    (f g : ℝ → ℝ)
    (P : Finset (Set ℝ))
    (hg_pc : PiecewiseConstantOn g P)
    (hgf : Majorizes I g f)
    (hsub :
      ∀ J ∈ P,
        J ⊆ I)
    (hlen :
      ∀ J ∈ P,
        0 ≤ len J) :
    upperSum len f P ≤
      pcIntegral len g P := by

  classical

  unfold upperSum pcIntegral

  apply Finset.sum_le_sum

  intro J hJnePieces

  have hmem :
      J ∈ P ∧ J.Nonempty := by
    exact (mem_nonemptyPieces P J).mp hJnePieces

  have hsup :
      sSup (f '' J) ≤ pieceValue g J := by
    exact sSup_le_pieceValue
      I
      f
      g
      P
      hg_pc
      hgf
      hsub
      J
      hmem.1
      hmem.2

  exact mul_le_mul_of_nonneg_right
    hsup
    (hlen J hmem.1)


/-!
============================================================
A minorizing constant on J is below inf f(J)
============================================================
-/

lemma pieceValue_le_sInf
    (I : Set ℝ)
    (f g : ℝ → ℝ)
    (P : Finset (Set ℝ))
    (hg_pc : PiecewiseConstantOn g P)
    (hgf : Minorizes I g f)
    (hsub :
      ∀ J ∈ P,
        J ⊆ I)
    (J : Set ℝ)
    (hJ : J ∈ P)
    (hJne : J.Nonempty) :
    pieceValue g J ≤ sInf (f '' J) := by

  apply le_csInf

  · exact hJne.image f

  · intro y hy

    obtain ⟨x, hxJ, rfl⟩ := hy

    have hxI :
        x ∈ I := by
      exact hsub J hJ hxJ

    have hgxf :
        g x ≤ f x := by
      exact hgf x hxI

    have hgValue :
        g x = pieceValue g J := by
      exact eq_pieceValue_of_piecewise
        g
        P
        hg_pc
        J
        hJ
        hJne
        x
        hxJ

    rw [hgValue] at hgxf

    exact hgxf


/-!
============================================================
Second half of Lemma 11.3.11

If g is piecewise constant and minorizes f, then

    pcIntegral(g,P) ≤ L(f,P).
============================================================
-/

theorem pcIntegral_le_lowerSum
    (I : Set ℝ)
    (len : Set ℝ → ℝ)
    (f g : ℝ → ℝ)
    (P : Finset (Set ℝ))
    (hg_pc : PiecewiseConstantOn g P)
    (hgf : Minorizes I g f)
    (hsub :
      ∀ J ∈ P,
        J ⊆ I)
    (hlen :
      ∀ J ∈ P,
        0 ≤ len J) :
    pcIntegral len g P ≤
      lowerSum len f P := by

  classical

  unfold pcIntegral lowerSum

  apply Finset.sum_le_sum

  intro J hJnePieces

  have hmem :
      J ∈ P ∧ J.Nonempty := by
    exact (mem_nonemptyPieces P J).mp hJnePieces

  have hinf :
      pieceValue g J ≤ sInf (f '' J) := by
    exact pieceValue_le_sInf
      I
      f
      g
      P
      hg_pc
      hgf
      hsub
      J
      hmem.1
      hmem.2

  exact mul_le_mul_of_nonneg_right
    hinf
    (hlen J hmem.1)


/-!
============================================================
Lemma 11.3.11
============================================================
-/

theorem lemma_11_3_11
    (I : Set ℝ)
    (len : Set ℝ → ℝ)
    (f g : ℝ → ℝ)
    (P : Finset (Set ℝ))
    (hg_pc : PiecewiseConstantOn g P)
    (hsub :
      ∀ J ∈ P,
        J ⊆ I)
    (hlen :
      ∀ J ∈ P,
        0 ≤ len J) :
    (Majorizes I g f →
      upperSum len f P ≤
        pcIntegral len g P)
      ∧
    (Minorizes I g f →
      pcIntegral len g P ≤
        lowerSum len f P) := by

  constructor

  · intro hgf

    exact pcIntegral_ge_upperSum
      I
      len
      f
      g
      P
      hg_pc
      hgf
      hsub
      hlen

  · intro hgf

    exact pcIntegral_le_lowerSum
      I
      len
      f
      g
      P
      hg_pc
      hgf
      hsub
      hlen


/-!
============================================================
Exercise 11.3.4
============================================================
-/

theorem exercise_11_3_4_majorant
    (I : Set ℝ)
    (len : Set ℝ → ℝ)
    (f g : ℝ → ℝ)
    (P : Finset (Set ℝ))
    (hg_pc : PiecewiseConstantOn g P)
    (hgf : Majorizes I g f)
    (hsub :
      ∀ J ∈ P,
        J ⊆ I)
    (hlen :
      ∀ J ∈ P,
        0 ≤ len J) :
    upperSum len f P ≤
      pcIntegral len g P := by

  exact pcIntegral_ge_upperSum
    I
    len
    f
    g
    P
    hg_pc
    hgf
    hsub
    hlen


theorem exercise_11_3_4_minorant
    (I : Set ℝ)
    (len : Set ℝ → ℝ)
    (f g : ℝ → ℝ)
    (P : Finset (Set ℝ))
    (hg_pc : PiecewiseConstantOn g P)
    (hgf : Minorizes I g f)
    (hsub :
      ∀ J ∈ P,
        J ⊆ I)
    (hlen :
      ∀ J ∈ P,
        0 ≤ len J) :
    pcIntegral len g P ≤
      lowerSum len f P := by

  exact pcIntegral_le_lowerSum
    I
    len
    f
    g
    P
    hg_pc
    hgf
    hsub
    hlen

end TaoExercise11_3_4
