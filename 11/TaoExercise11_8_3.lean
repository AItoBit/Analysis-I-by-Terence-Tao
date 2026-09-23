import Mathlib

namespace TaoExercise11_8_3

open Set

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
Chosen value of a piecewise constant function
============================================================
-/

noncomputable def pieceValue
    (f : ℝ → ℝ)
    (J : Set ℝ) : ℝ :=
  f (Classical.epsilon (fun x : ℝ => x ∈ J))


lemma epsilon_mem
    (J : Set ℝ)
    (hJ : J.Nonempty) :
    Classical.epsilon (fun x : ℝ => x ∈ J) ∈ J := by

  exact Classical.epsilon_spec hJ


lemma pieceValue_eq_of_constant
    (f : ℝ → ℝ)
    (J : Set ℝ)
    (hJ : J.Nonempty)
    (c : ℝ)
    (hc :
      ∀ x ∈ J,
        f x = c) :
    pieceValue f J = c := by

  unfold pieceValue

  exact hc
    (Classical.epsilon (fun x : ℝ => x ∈ J))
    (epsilon_mem J hJ)


lemma eq_pieceValue_of_piecewise
    (f : ℝ → ℝ)
    (P : Finset (Set ℝ))
    (hf : PiecewiseConstantOn f P)
    (J : Set ℝ)
    (hJ : J ∈ P)
    (hJne : J.Nonempty)
    (x : ℝ)
    (hx : x ∈ J) :
    f x = pieceValue f J := by

  obtain ⟨c, hc⟩ := hf J hJ

  have hxVal :
      f x = c := by
    exact hc x hx

  have hpiece :
      pieceValue f J = c := by
    exact pieceValue_eq_of_constant
      f
      J
      hJne
      c
      hc

  exact hxVal.trans hpiece.symm


/-!
============================================================
Algebra of pieceValue
============================================================
-/

lemma pieceValue_add
    (f g : ℝ → ℝ)
    (J : Set ℝ) :
    pieceValue (fun x => f x + g x) J =
      pieceValue f J + pieceValue g J := by

  rfl


lemma pieceValue_sub
    (f g : ℝ → ℝ)
    (J : Set ℝ) :
    pieceValue (fun x => f x - g x) J =
      pieceValue f J - pieceValue g J := by

  rfl


lemma pieceValue_const_mul
    (c : ℝ)
    (f : ℝ → ℝ)
    (J : Set ℝ) :
    pieceValue (fun x => c * f x) J =
      c * pieceValue f J := by

  rfl


/-!
============================================================
Piecewise constancy is preserved by algebra
============================================================
-/

lemma piecewiseConstantOn_add
    (f g : ℝ → ℝ)
    (P : Finset (Set ℝ))
    (hf : PiecewiseConstantOn f P)
    (hg : PiecewiseConstantOn g P) :
    PiecewiseConstantOn
      (fun x => f x + g x)
      P := by

  intro J hJ

  obtain ⟨c, hc⟩ := hf J hJ
  obtain ⟨d, hd⟩ := hg J hJ

  refine ⟨c + d, ?_⟩

  intro x hx

  change f x + g x = c + d

  rw [hc x hx, hd x hx]


lemma piecewiseConstantOn_const_mul
    (c : ℝ)
    (f : ℝ → ℝ)
    (P : Finset (Set ℝ))
    (hf : PiecewiseConstantOn f P) :
    PiecewiseConstantOn
      (fun x => c * f x)
      P := by

  intro J hJ

  obtain ⟨d, hd⟩ := hf J hJ

  refine ⟨c * d, ?_⟩

  intro x hx

  change c * f x = c * d

  rw [hd x hx]


lemma piecewiseConstantOn_sub
    (f g : ℝ → ℝ)
    (P : Finset (Set ℝ))
    (hf : PiecewiseConstantOn f P)
    (hg : PiecewiseConstantOn g P) :
    PiecewiseConstantOn
      (fun x => f x - g x)
      P := by

  intro J hJ

  obtain ⟨c, hc⟩ := hf J hJ
  obtain ⟨d, hd⟩ := hg J hJ

  refine ⟨c - d, ?_⟩

  intro x hx

  change f x - g x = c - d

  rw [hc x hx, hd x hx]


/-!
============================================================
Piecewise constant Riemann-Stieltjes integral
============================================================
-/

noncomputable def pcRSIntegral
    (alphaContent : Set ℝ → ℝ)
    (f : ℝ → ℝ)
    (P : Finset (Set ℝ)) : ℝ :=
  P.sum
    (fun J =>
      pieceValue f J * alphaContent J)


/-!
============================================================
(a) Additivity
============================================================
-/

theorem pcRSIntegral_add
    (alphaContent : Set ℝ → ℝ)
    (f g : ℝ → ℝ)
    (P : Finset (Set ℝ)) :
    pcRSIntegral alphaContent
        (fun x => f x + g x)
        P
      =
    pcRSIntegral alphaContent f P +
      pcRSIntegral alphaContent g P := by

  classical

  unfold pcRSIntegral

  calc
    P.sum
        (fun J =>
          pieceValue (fun x => f x + g x) J *
            alphaContent J)
        =
      P.sum
        (fun J =>
          pieceValue f J * alphaContent J +
            pieceValue g J * alphaContent J) := by

      apply Finset.sum_congr rfl

      intro J _hJ

      rw [pieceValue_add]

      ring

    _ =
      P.sum
          (fun J =>
            pieceValue f J * alphaContent J)
        +
      P.sum
          (fun J =>
            pieceValue g J * alphaContent J) := by

      exact Finset.sum_add_distrib


/-!
============================================================
(b) Scalar multiplication

This actually holds for every real c, not merely c > 0.
============================================================
-/

theorem pcRSIntegral_const_mul
    (alphaContent : Set ℝ → ℝ)
    (c : ℝ)
    (f : ℝ → ℝ)
    (P : Finset (Set ℝ)) :
    pcRSIntegral alphaContent
        (fun x => c * f x)
        P
      =
    c * pcRSIntegral alphaContent f P := by

  classical

  unfold pcRSIntegral

  calc
    P.sum
        (fun J =>
          pieceValue (fun x => c * f x) J *
            alphaContent J)
        =
      P.sum
        (fun J =>
          c *
            (pieceValue f J * alphaContent J)) := by

      apply Finset.sum_congr rfl

      intro J _hJ

      rw [pieceValue_const_mul]

      ring

    _ =
      c *
        P.sum
          (fun J =>
            pieceValue f J * alphaContent J) := by

      rw [Finset.mul_sum]


/-!
============================================================
(c) Subtraction

We derive this from (a) and (b), exactly as Tao does.
============================================================
-/

theorem pcRSIntegral_sub
    (alphaContent : Set ℝ → ℝ)
    (f g : ℝ → ℝ)
    (P : Finset (Set ℝ)) :
    pcRSIntegral alphaContent
        (fun x => f x - g x)
        P
      =
    pcRSIntegral alphaContent f P -
      pcRSIntegral alphaContent g P := by

  have hfun :
      (fun x : ℝ => f x - g x)
        =
      (fun x : ℝ => f x + (-1 : ℝ) * g x) := by

    funext x

    ring

  rw [hfun]

  rw [pcRSIntegral_add]

  rw [pcRSIntegral_const_mul]

  ring


/-!
============================================================
(d) Non-negativity

For increasing α we have α[J] ≥ 0.
============================================================
-/

theorem pcRSIntegral_nonneg
    (I : Set ℝ)
    (alphaContent : Set ℝ → ℝ)
    (f : ℝ → ℝ)
    (P : Finset (Set ℝ))
    (hsub :
      ∀ J ∈ P,
        J ⊆ I)
    (hne :
      ∀ J ∈ P,
        J.Nonempty)
    (halpha :
      ∀ J ∈ P,
        0 ≤ alphaContent J)
    (hf :
      ∀ x ∈ I,
        0 ≤ f x) :
    0 ≤ pcRSIntegral alphaContent f P := by

  classical

  unfold pcRSIntegral

  exact Finset.sum_nonneg
    (fun J hJ => by

      have hJne :
          J.Nonempty := by

        exact hne J hJ

      have hxJ :
          Classical.epsilon
              (fun x : ℝ => x ∈ J) ∈ J := by

        exact epsilon_mem J hJne

      have hxI :
          Classical.epsilon
              (fun x : ℝ => x ∈ J) ∈ I := by

        exact hsub J hJ hxJ

      have hvalue :
          0 ≤ pieceValue f J := by

        unfold pieceValue

        exact hf
          (Classical.epsilon
            (fun x : ℝ => x ∈ J))
          hxI

      exact mul_nonneg
        hvalue
        (halpha J hJ))


/-!
============================================================
(e) Monotonicity
============================================================
-/

theorem pcRSIntegral_mono
    (I : Set ℝ)
    (alphaContent : Set ℝ → ℝ)
    (f g : ℝ → ℝ)
    (P : Finset (Set ℝ))
    (hsub :
      ∀ J ∈ P,
        J ⊆ I)
    (hne :
      ∀ J ∈ P,
        J.Nonempty)
    (halpha :
      ∀ J ∈ P,
        0 ≤ alphaContent J)
    (hfg :
      ∀ x ∈ I,
        g x ≤ f x) :
    pcRSIntegral alphaContent g P ≤
      pcRSIntegral alphaContent f P := by

  classical

  unfold pcRSIntegral

  exact Finset.sum_le_sum
    (fun J hJ => by

      have hJne :
          J.Nonempty := by

        exact hne J hJ

      have hxJ :
          Classical.epsilon
              (fun x : ℝ => x ∈ J) ∈ J := by

        exact epsilon_mem J hJne

      have hxI :
          Classical.epsilon
              (fun x : ℝ => x ∈ J) ∈ I := by

        exact hsub J hJ hxJ

      have hvalues :
          pieceValue g J ≤ pieceValue f J := by

        unfold pieceValue

        exact hfg
          (Classical.epsilon
            (fun x : ℝ => x ∈ J))
          hxI

      exact mul_le_mul_of_nonneg_right
        hvalues
        (halpha J hJ))


/-!
============================================================
(f) Constant functions

Lemma 11.8.4 provides:

    P.sum alphaContent = alphaContent I
============================================================
-/

theorem pcRSIntegral_const
    (I : Set ℝ)
    (alphaContent : Set ℝ → ℝ)
    (P : Finset (Set ℝ))
    (hne :
      ∀ J ∈ P,
        J.Nonempty)
    (halphaTotal :
      P.sum alphaContent =
        alphaContent I)
    (c : ℝ) :
    pcRSIntegral alphaContent
        (fun _ : ℝ => c)
        P
      =
    c * alphaContent I := by

  classical

  unfold pcRSIntegral

  have hpiece :
      ∀ J ∈ P,
        pieceValue (fun _ : ℝ => c) J = c := by

    intro J hJ

    exact pieceValue_eq_of_constant
      (fun _ : ℝ => c)
      J
      (hne J hJ)
      c
      (by
        intro _x _hx
        rfl)

  calc
    P.sum
        (fun J =>
          pieceValue (fun _ : ℝ => c) J *
            alphaContent J)
        =
      P.sum
        (fun J =>
          c * alphaContent J) := by

      apply Finset.sum_congr rfl

      intro J hJ

      rw [hpiece J hJ]

    _ =
      c * P.sum alphaContent := by

      rw [Finset.mul_sum]

    _ =
      c * alphaContent I := by

      rw [halphaTotal]


/-!
============================================================
Zero extension
============================================================
-/

noncomputable def zeroExtension
    (I : Set ℝ)
    (f : ℝ → ℝ) :
    ℝ → ℝ := by

  classical

  exact fun x =>
    if x ∈ I then f x else 0


lemma pieceValue_zeroExtension_inside
    (I : Set ℝ)
    (f : ℝ → ℝ)
    (J : Set ℝ)
    (hJne : J.Nonempty)
    (hsub : J ⊆ I) :
    pieceValue (zeroExtension I f) J =
      pieceValue f J := by

  have hxJ :
      Classical.epsilon
          (fun x : ℝ => x ∈ J) ∈ J := by

    exact epsilon_mem J hJne

  have hxI :
      Classical.epsilon
          (fun x : ℝ => x ∈ J) ∈ I := by

    exact hsub hxJ

  unfold pieceValue zeroExtension

  simp [hxI]


lemma pieceValue_zeroExtension_outside
    (I : Set ℝ)
    (f : ℝ → ℝ)
    (J : Set ℝ)
    (hJne : J.Nonempty)
    (hout :
      ∀ x ∈ J,
        x ∉ I) :
    pieceValue (zeroExtension I f) J = 0 := by

  have hxJ :
      Classical.epsilon
          (fun x : ℝ => x ∈ J) ∈ J := by

    exact epsilon_mem J hJne

  have hxNotI :
      Classical.epsilon
          (fun x : ℝ => x ∈ J) ∉ I := by

    exact hout
      (Classical.epsilon
        (fun x : ℝ => x ∈ J))
      hxJ

  unfold pieceValue zeroExtension

  simp [hxNotI]


/-!
============================================================
(g) Extension by zero

P consists of the pieces inside I.
Q consists of the new pieces in J \ I.
============================================================
-/

theorem pcRSIntegral_zeroExtension
    (I : Set ℝ)
    (alphaContent : Set ℝ → ℝ)
    (f : ℝ → ℝ)
    (P Q : Finset (Set ℝ))
    (hdisj :
      Disjoint P Q)
    (hPne :
      ∀ K ∈ P,
        K.Nonempty)
    (hQne :
      ∀ K ∈ Q,
        K.Nonempty)
    (hPsub :
      ∀ K ∈ P,
        K ⊆ I)
    (hQout :
      ∀ K ∈ Q,
        ∀ x ∈ K,
          x ∉ I) :
    pcRSIntegral
        alphaContent
        (zeroExtension I f)
        (P ∪ Q)
      =
    pcRSIntegral
        alphaContent
        f
        P := by

  classical

  unfold pcRSIntegral

  rw [Finset.sum_union hdisj]

  have hP :
      P.sum
          (fun K =>
            pieceValue (zeroExtension I f) K *
              alphaContent K)
        =
      P.sum
          (fun K =>
            pieceValue f K *
              alphaContent K) := by

    apply Finset.sum_congr rfl

    intro K hK

    rw [pieceValue_zeroExtension_inside
      I
      f
      K
      (hPne K hK)
      (hPsub K hK)]

  have hQ :
      Q.sum
          (fun K =>
            pieceValue (zeroExtension I f) K *
              alphaContent K)
        =
      0 := by

    exact Finset.sum_eq_zero
      (fun K hK => by

        rw [pieceValue_zeroExtension_outside
          I
          f
          K
          (hQne K hK)
          (hQout K hK)]

        ring)

  rw [hP, hQ]

  ring


/-!
============================================================
(h) Splitting a partition into two disjoint collections
============================================================
-/

theorem pcRSIntegral_union
    (alphaContent : Set ℝ → ℝ)
    (f : ℝ → ℝ)
    (P Q : Finset (Set ℝ))
    (hdisj :
      Disjoint P Q) :
    pcRSIntegral alphaContent f (P ∪ Q)
      =
    pcRSIntegral alphaContent f P +
      pcRSIntegral alphaContent f Q := by

  classical

  unfold pcRSIntegral

  exact Finset.sum_union hdisj


/-!
============================================================
Theorem 11.8.3 — parts (a)-(f)
============================================================
-/

theorem theorem_11_8_3
    (I : Set ℝ)
    (alphaContent : Set ℝ → ℝ)
    (f g : ℝ → ℝ)
    (P : Finset (Set ℝ))
    (hsub :
      ∀ J ∈ P,
        J ⊆ I)
    (hne :
      ∀ J ∈ P,
        J.Nonempty)
    (halpha :
      ∀ J ∈ P,
        0 ≤ alphaContent J)
    (halphaTotal :
      P.sum alphaContent =
        alphaContent I) :
    (pcRSIntegral alphaContent
        (fun x => f x + g x)
        P
      =
      pcRSIntegral alphaContent f P +
        pcRSIntegral alphaContent g P)
      ∧
    (∀ c : ℝ,
      pcRSIntegral alphaContent
          (fun x => c * f x)
          P
        =
      c * pcRSIntegral alphaContent f P)
      ∧
    (pcRSIntegral alphaContent
        (fun x => f x - g x)
        P
      =
      pcRSIntegral alphaContent f P -
        pcRSIntegral alphaContent g P)
      ∧
    ((∀ x ∈ I, 0 ≤ f x) →
      0 ≤ pcRSIntegral alphaContent f P)
      ∧
    ((∀ x ∈ I, g x ≤ f x) →
      pcRSIntegral alphaContent g P ≤
        pcRSIntegral alphaContent f P)
      ∧
    (∀ c : ℝ,
      pcRSIntegral alphaContent
          (fun _ : ℝ => c)
          P
        =
      c * alphaContent I) := by

  refine ⟨pcRSIntegral_add alphaContent f g P, ?_⟩

  refine ⟨?_, ?_⟩

  · intro c

    exact pcRSIntegral_const_mul
      alphaContent
      c
      f
      P

  · refine
      ⟨pcRSIntegral_sub
        alphaContent
        f
        g
        P, ?_⟩

    refine ⟨?_, ?_⟩

    · intro hfNonneg

      exact pcRSIntegral_nonneg
        I
        alphaContent
        f
        P
        hsub
        hne
        halpha
        hfNonneg

    · refine ⟨?_, ?_⟩

      · intro hfg

        exact pcRSIntegral_mono
          I
          alphaContent
          f
          g
          P
          hsub
          hne
          halpha
          hfg

      · intro c

        exact pcRSIntegral_const
          I
          alphaContent
          P
          hne
          halphaTotal
          c


/-!
============================================================
Piecewise constancy statements for (a)-(c)
============================================================
-/

theorem theorem_11_8_3_piecewise
    (f g : ℝ → ℝ)
    (P : Finset (Set ℝ))
    (hf : PiecewiseConstantOn f P)
    (hg : PiecewiseConstantOn g P) :
    PiecewiseConstantOn
        (fun x => f x + g x)
        P
      ∧
    (∀ c : ℝ,
      PiecewiseConstantOn
        (fun x => c * f x)
        P)
      ∧
    PiecewiseConstantOn
        (fun x => f x - g x)
        P := by

  refine
    ⟨piecewiseConstantOn_add
      f
      g
      P
      hf
      hg, ?_⟩

  refine ⟨?_, ?_⟩

  · intro c

    exact piecewiseConstantOn_const_mul
      c
      f
      P
      hf

  · exact piecewiseConstantOn_sub
      f
      g
      P
      hf
      hg


/-!
============================================================
Exercise 11.8.3
============================================================
-/

theorem exercise_11_8_3
    (I : Set ℝ)
    (alphaContent : Set ℝ → ℝ)
    (f g : ℝ → ℝ)
    (P : Finset (Set ℝ))
    (hsub :
      ∀ J ∈ P,
        J ⊆ I)
    (hne :
      ∀ J ∈ P,
        J.Nonempty)
    (halpha :
      ∀ J ∈ P,
        0 ≤ alphaContent J)
    (halphaTotal :
      P.sum alphaContent =
        alphaContent I) :
    (pcRSIntegral alphaContent
        (fun x => f x + g x)
        P
      =
      pcRSIntegral alphaContent f P +
        pcRSIntegral alphaContent g P)
      ∧
    (∀ c : ℝ,
      pcRSIntegral alphaContent
          (fun x => c * f x)
          P
        =
      c * pcRSIntegral alphaContent f P)
      ∧
    (pcRSIntegral alphaContent
        (fun x => f x - g x)
        P
      =
      pcRSIntegral alphaContent f P -
        pcRSIntegral alphaContent g P)
      ∧
    ((∀ x ∈ I, 0 ≤ f x) →
      0 ≤ pcRSIntegral alphaContent f P)
      ∧
    ((∀ x ∈ I, g x ≤ f x) →
      pcRSIntegral alphaContent g P ≤
        pcRSIntegral alphaContent f P)
      ∧
    (∀ c : ℝ,
      pcRSIntegral alphaContent
          (fun _ : ℝ => c)
          P
        =
      c * alphaContent I) := by

  exact theorem_11_8_3
    I
    alphaContent
    f
    g
    P
    hsub
    hne
    halpha
    halphaTotal

end TaoExercise11_8_3
