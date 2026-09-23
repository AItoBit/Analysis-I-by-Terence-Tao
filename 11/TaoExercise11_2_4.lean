import Mathlib

namespace TaoExercise11_2_4

open Set

/-!
============================================================
Basic definitions
============================================================
-/

def PiecewiseConstantOn
    (f : ℝ → ℝ)
    (P : Finset (Set ℝ)) : Prop :=
  ∀ J ∈ P,
    ∃ c : ℝ,
      ∀ x ∈ J,
        f x = c


noncomputable def pieceValue
    (f : ℝ → ℝ)
    (J : Set ℝ) : ℝ :=
  f (Classical.epsilon (fun x : ℝ => x ∈ J))


noncomputable def pcIntegral
    (len : Set ℝ → ℝ)
    (f : ℝ → ℝ)
    (P : Finset (Set ℝ)) : ℝ :=
  P.sum (fun J =>
    pieceValue f J * len J)


/-!
============================================================
Chosen point of a nonempty set
============================================================
-/

lemma epsilon_mem
    (J : Set ℝ)
    (hJ : J.Nonempty) :
    Classical.epsilon (fun x : ℝ => x ∈ J) ∈ J := by

  exact Classical.epsilon_spec hJ


/-!
============================================================
pieceValue of a constant function
============================================================
-/

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
Piecewise constancy: addition
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


/-!
============================================================
Piecewise constancy: scalar multiplication
============================================================
-/

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


/-!
============================================================
Piecewise constancy: subtraction
============================================================
-/

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
(a) Additivity
============================================================
-/

theorem pcIntegral_add
    (len : Set ℝ → ℝ)
    (f g : ℝ → ℝ)
    (P : Finset (Set ℝ)) :
    pcIntegral len (fun x => f x + g x) P =
      pcIntegral len f P +
      pcIntegral len g P := by

  classical

  unfold pcIntegral

  calc
    P.sum
        (fun J =>
          pieceValue (fun x => f x + g x) J *
            len J)
        =
      P.sum
        (fun J =>
          pieceValue f J * len J +
            pieceValue g J * len J) := by

      apply Finset.sum_congr rfl

      intro J _hJ

      rw [pieceValue_add]

      ring

    _ =
      P.sum
          (fun J =>
            pieceValue f J * len J)
        +
      P.sum
          (fun J =>
            pieceValue g J * len J) := by

      exact Finset.sum_add_distrib


/-!
============================================================
(b) Scalar multiplication
============================================================
-/

theorem pcIntegral_const_mul
    (len : Set ℝ → ℝ)
    (c : ℝ)
    (f : ℝ → ℝ)
    (P : Finset (Set ℝ)) :
    pcIntegral len (fun x => c * f x) P =
      c * pcIntegral len f P := by

  classical

  unfold pcIntegral

  calc
    P.sum
        (fun J =>
          pieceValue (fun x => c * f x) J *
            len J)
        =
      P.sum
        (fun J =>
          c * (pieceValue f J * len J)) := by

      apply Finset.sum_congr rfl

      intro J _hJ

      rw [pieceValue_const_mul]

      ring

    _ =
      c *
        P.sum
          (fun J =>
            pieceValue f J * len J) := by

      rw [Finset.mul_sum]


/-!
============================================================
(c) Subtraction
============================================================
-/

theorem pcIntegral_sub
    (len : Set ℝ → ℝ)
    (f g : ℝ → ℝ)
    (P : Finset (Set ℝ)) :
    pcIntegral len (fun x => f x - g x) P =
      pcIntegral len f P -
      pcIntegral len g P := by

  classical

  unfold pcIntegral

  calc
    P.sum
        (fun J : Set ℝ =>
          pieceValue (fun x => f x - g x) J *
            len J)
        =
      P.sum
        (fun J : Set ℝ =>
          pieceValue f J * len J -
            pieceValue g J * len J) := by

      apply Finset.sum_congr rfl

      intro J _hJ

      rw [pieceValue_sub]

      ring

    _ =
      P.sum
          (fun J : Set ℝ =>
            pieceValue f J * len J)
        -
      P.sum
          (fun J : Set ℝ =>
            pieceValue g J * len J) := by

      simpa only using
        (Finset.sum_sub_distrib :
          P.sum
              (fun J : Set ℝ =>
                pieceValue f J * len J -
                  pieceValue g J * len J)
            =
          P.sum
              (fun J : Set ℝ =>
                pieceValue f J * len J)
            -
          P.sum
              (fun J : Set ℝ =>
                pieceValue g J * len J))


/-!
============================================================
(d) Nonnegative function -> nonnegative integral
============================================================
-/

theorem pcIntegral_nonneg
    (I : Set ℝ)
    (len : Set ℝ → ℝ)
    (f : ℝ → ℝ)
    (P : Finset (Set ℝ))
    (hsub :
      ∀ J ∈ P,
        J ⊆ I)
    (hne :
      ∀ J ∈ P,
        J.Nonempty)
    (hlen :
      ∀ J ∈ P,
        0 ≤ len J)
    (hf :
      ∀ x ∈ I,
        0 ≤ f x) :
    0 ≤ pcIntegral len f P := by

  classical

  unfold pcIntegral

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

      have hval :
          0 ≤ pieceValue f J := by

        unfold pieceValue

        exact hf
          (Classical.epsilon
            (fun x : ℝ => x ∈ J))
          hxI

      exact mul_nonneg
        hval
        (hlen J hJ))


/-!
============================================================
(e) Monotonicity
============================================================
-/

theorem pcIntegral_mono
    (I : Set ℝ)
    (len : Set ℝ → ℝ)
    (f g : ℝ → ℝ)
    (P : Finset (Set ℝ))
    (hsub :
      ∀ J ∈ P,
        J ⊆ I)
    (hne :
      ∀ J ∈ P,
        J.Nonempty)
    (hlen :
      ∀ J ∈ P,
        0 ≤ len J)
    (hfg :
      ∀ x ∈ I,
        g x ≤ f x) :
    pcIntegral len g P ≤
      pcIntegral len f P := by

  classical

  unfold pcIntegral

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
          pieceValue g J ≤
            pieceValue f J := by

        unfold pieceValue

        exact hfg
          (Classical.epsilon
            (fun x : ℝ => x ∈ J))
          hxI

      exact mul_le_mul_of_nonneg_right
        hvalues
        (hlen J hJ))


/-!
============================================================
(f) Constant function
============================================================
-/

theorem pcIntegral_const
    (len : Set ℝ → ℝ)
    (I : Set ℝ)
    (P : Finset (Set ℝ))
    (hne :
      ∀ J ∈ P,
        J.Nonempty)
    (hlen_total :
      P.sum len = len I)
    (c : ℝ) :
    pcIntegral len (fun _ : ℝ => c) P =
      c * len I := by

  classical

  unfold pcIntegral

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
            len J)
        =
      P.sum
        (fun J =>
          c * len J) := by

      apply Finset.sum_congr rfl

      intro J hJ

      rw [hpiece J hJ]

    _ =
      c * P.sum len := by

      rw [Finset.mul_sum]

    _ =
      c * len I := by

      rw [hlen_total]


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
    if x ∈ I then
      f x
    else
      0


/-!
============================================================
Inside I, zeroExtension equals f
============================================================
-/

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


/-!
============================================================
Outside I, zeroExtension equals 0
============================================================
-/

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
(g) Zero extension preserves the integral
============================================================
-/

theorem pcIntegral_zeroExtension
    (I : Set ℝ)
    (len : Set ℝ → ℝ)
    (f : ℝ → ℝ)
    (P Q : Finset (Set ℝ))
    (hdisj :
      Disjoint P Q)
    (hPne :
      ∀ J ∈ P,
        J.Nonempty)
    (hQne :
      ∀ J ∈ Q,
        J.Nonempty)
    (hPsub :
      ∀ J ∈ P,
        J ⊆ I)
    (hQout :
      ∀ J ∈ Q,
        ∀ x ∈ J,
          x ∉ I) :
    pcIntegral len
        (zeroExtension I f)
        (P ∪ Q)
      =
    pcIntegral len f P := by

  classical

  unfold pcIntegral

  rw [Finset.sum_union hdisj]

  have hP :
      P.sum
          (fun J =>
            pieceValue (zeroExtension I f) J *
              len J)
        =
      P.sum
          (fun J =>
            pieceValue f J *
              len J) := by

    apply Finset.sum_congr rfl

    intro J hJ

    rw [pieceValue_zeroExtension_inside
      I
      f
      J
      (hPne J hJ)
      (hPsub J hJ)]

  have hQ :
      Q.sum
          (fun J =>
            pieceValue (zeroExtension I f) J *
              len J)
        = 0 := by

    exact Finset.sum_eq_zero
      (fun J hJ => by

        rw [pieceValue_zeroExtension_outside
          I
          f
          J
          (hQne J hJ)
          (hQout J hJ)]

        ring)

  rw [hP, hQ]

  ring


/-!
============================================================
(h) Splitting the partition
============================================================
-/

theorem pcIntegral_union
    (len : Set ℝ → ℝ)
    (f : ℝ → ℝ)
    (P Q : Finset (Set ℝ))
    (hdisj :
      Disjoint P Q) :
    pcIntegral len f (P ∪ Q) =
      pcIntegral len f P +
      pcIntegral len f Q := by

  classical

  unfold pcIntegral

  exact Finset.sum_union hdisj


/-!
============================================================
Theorem 11.2.16, parts (a)-(f)
============================================================
-/

theorem theorem_11_2_16
    (I : Set ℝ)
    (len : Set ℝ → ℝ)
    (f g : ℝ → ℝ)
    (P : Finset (Set ℝ))
    (hsub :
      ∀ J ∈ P,
        J ⊆ I)
    (hne :
      ∀ J ∈ P,
        J.Nonempty)
    (hlen_nonneg :
      ∀ J ∈ P,
        0 ≤ len J)
    (hlen_total :
      P.sum len = len I) :
    (pcIntegral len
        (fun x => f x + g x) P =
      pcIntegral len f P +
        pcIntegral len g P)
      ∧
    (∀ c : ℝ,
      pcIntegral len
          (fun x => c * f x) P =
        c * pcIntegral len f P)
      ∧
    (pcIntegral len
        (fun x => f x - g x) P =
      pcIntegral len f P -
        pcIntegral len g P)
      ∧
    ((∀ x ∈ I, 0 ≤ f x) →
      0 ≤ pcIntegral len f P)
      ∧
    ((∀ x ∈ I, g x ≤ f x) →
      pcIntegral len g P ≤
        pcIntegral len f P)
      ∧
    (∀ c : ℝ,
      pcIntegral len
          (fun _ : ℝ => c) P =
        c * len I) := by

  refine ⟨pcIntegral_add len f g P, ?_⟩

  refine ⟨?_, ?_⟩

  · intro c

    exact pcIntegral_const_mul
      len
      c
      f
      P

  · refine
      ⟨pcIntegral_sub len f g P, ?_⟩

    refine ⟨?_, ?_⟩

    · intro hfNonneg

      exact pcIntegral_nonneg
        I
        len
        f
        P
        hsub
        hne
        hlen_nonneg
        hfNonneg

    · refine ⟨?_, ?_⟩

      · intro hfg

        exact pcIntegral_mono
          I
          len
          f
          g
          P
          hsub
          hne
          hlen_nonneg
          hfg

      · intro c

        exact pcIntegral_const
          len
          I
          P
          hne
          hlen_total
          c


/-!
============================================================
Piecewise-constancy statements
============================================================
-/

theorem theorem_11_2_16_piecewise
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
      f g P hf hg, ?_⟩

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
Exercise 11.2.4
============================================================
-/

theorem exercise_11_2_4
    (I : Set ℝ)
    (len : Set ℝ → ℝ)
    (f g : ℝ → ℝ)
    (P : Finset (Set ℝ))
    (hsub :
      ∀ J ∈ P,
        J ⊆ I)
    (hne :
      ∀ J ∈ P,
        J.Nonempty)
    (hlen_nonneg :
      ∀ J ∈ P,
        0 ≤ len J)
    (hlen_total :
      P.sum len = len I) :
    (pcIntegral len
        (fun x => f x + g x) P =
      pcIntegral len f P +
        pcIntegral len g P)
      ∧
    (∀ c : ℝ,
      pcIntegral len
          (fun x => c * f x) P =
        c * pcIntegral len f P)
      ∧
    (pcIntegral len
        (fun x => f x - g x) P =
      pcIntegral len f P -
        pcIntegral len g P)
      ∧
    ((∀ x ∈ I, 0 ≤ f x) →
      0 ≤ pcIntegral len f P)
      ∧
    ((∀ x ∈ I, g x ≤ f x) →
      pcIntegral len g P ≤
        pcIntegral len f P)
      ∧
    (∀ c : ℝ,
      pcIntegral len
          (fun _ : ℝ => c) P =
        c * len I) := by

  exact theorem_11_2_16
    I
    len
    f
    g
    P
    hsub
    hne
    hlen_nonneg
    hlen_total

end TaoExercise11_2_4
