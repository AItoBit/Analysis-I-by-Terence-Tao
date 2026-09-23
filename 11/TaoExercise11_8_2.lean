import Mathlib

namespace TaoExercise11_8_2

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
Chosen constant value on a piece
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


lemma eq_pieceValue_of_piecewise
    (f : ℝ → ℝ)
    (P : Finset (Set ℝ))
    (hf : PiecewiseConstantOn f P)
    (J : Set ℝ)
    (hJ : J ∈ P)
    (x : ℝ)
    (hx : x ∈ J) :
    f x = pieceValue f J := by

  obtain ⟨c, hc⟩ := hf J hJ

  have hJne :
      J.Nonempty := by
    exact ⟨x, hx⟩

  have hchosen :
      Classical.epsilon
          (fun y : ℝ => y ∈ J) ∈ J := by

    exact epsilon_mem J hJne

  have hxVal :
      f x = c := by

    exact hc x hx

  have hchosenVal :
      f (Classical.epsilon
          (fun y : ℝ => y ∈ J)) = c := by

    exact hc
      (Classical.epsilon
        (fun y : ℝ => y ∈ J))
      hchosen

  unfold pieceValue

  exact hxVal.trans hchosenVal.symm


/-!
============================================================
Piece values agree on nonempty intersections
============================================================
-/

lemma pieceValue_eq_on_inter
    (f : ℝ → ℝ)
    (P P' : Finset (Set ℝ))
    (hfP : PiecewiseConstantOn f P)
    (hfP' : PiecewiseConstantOn f P')
    (K L : Set ℝ)
    (hK : K ∈ P)
    (hL : L ∈ P')
    (hKL : (K ∩ L).Nonempty) :
    pieceValue f K =
      pieceValue f L := by

  obtain ⟨x, hxK, hxL⟩ := hKL

  have hKval :
      f x = pieceValue f K := by

    exact eq_pieceValue_of_piecewise
      f
      P
      hfP
      K
      hK
      x
      hxK

  have hLval :
      f x = pieceValue f L := by

    exact eq_pieceValue_of_piecewise
      f
      P'
      hfP'
      L
      hL
      x
      hxL

  exact hKval.symm.trans hLval


/-!
============================================================
Riemann-Stieltjes piecewise-constant integral

alphaContent J represents Tao's α[J].
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
Empty intersections contribute zero
============================================================
-/

lemma inter_eq_empty_of_not_nonempty
    (K L : Set ℝ)
    (hKL : ¬ (K ∩ L).Nonempty) :
    K ∩ L = ∅ := by

  ext x

  simp only [
    Set.mem_inter_iff,
    Set.mem_empty_iff_false,
    iff_false
  ]

  intro hx

  exact hKL ⟨x, hx⟩


lemma alphaContent_inter_eq_zero
    (alphaContent : Set ℝ → ℝ)
    (hEmpty : alphaContent ∅ = 0)
    (K L : Set ℝ)
    (hKL : ¬ (K ∩ L).Nonempty) :
    alphaContent (K ∩ L) = 0 := by

  have hempty :
      K ∩ L = ∅ := by

    exact inter_eq_empty_of_not_nonempty
      K
      L
      hKL

  rw [hempty]

  exact hEmpty


/-!
============================================================
One intersection term can use either piece value
============================================================
-/

lemma intersection_term_eq
    (alphaContent : Set ℝ → ℝ)
    (hEmpty : alphaContent ∅ = 0)
    (f : ℝ → ℝ)
    (P P' : Finset (Set ℝ))
    (hfP : PiecewiseConstantOn f P)
    (hfP' : PiecewiseConstantOn f P')
    (K L : Set ℝ)
    (hK : K ∈ P)
    (hL : L ∈ P') :
    pieceValue f K * alphaContent (K ∩ L)
      =
    pieceValue f L * alphaContent (K ∩ L) := by

  classical

  by_cases hKL :
      (K ∩ L).Nonempty

  · have hvalues :
        pieceValue f K =
          pieceValue f L := by

      exact pieceValue_eq_on_inter
        f
        P
        P'
        hfP
        hfP'
        K
        L
        hK
        hL
        hKL

    rw [hvalues]

  · have hzero :
        alphaContent (K ∩ L) = 0 := by

      exact alphaContent_inter_eq_zero
        alphaContent
        hEmpty
        K
        L
        hKL

    rw [hzero]

    ring


/-!
============================================================
Expand the integral over P into the common refinement
============================================================
-/

lemma pcRSIntegral_eq_double_sum_left
    (alphaContent : Set ℝ → ℝ)
    (f : ℝ → ℝ)
    (P P' : Finset (Set ℝ))
    (hAlphaLeft :
      ∀ K ∈ P,
        P'.sum
            (fun L =>
              alphaContent (K ∩ L))
          =
        alphaContent K) :
    pcRSIntegral alphaContent f P
      =
    P.sum
      (fun K =>
        P'.sum
          (fun L =>
            pieceValue f K *
              alphaContent (K ∩ L))) := by

  classical

  unfold pcRSIntegral

  apply Finset.sum_congr rfl

  intro K hK

  have hdecomp :
      P'.sum
          (fun L =>
            alphaContent (K ∩ L))
        =
      alphaContent K := by

    exact hAlphaLeft K hK

  calc
    pieceValue f K * alphaContent K
        =
      pieceValue f K *
        P'.sum
          (fun L =>
            alphaContent (K ∩ L)) := by

      rw [hdecomp]

    _ =
      P'.sum
        (fun L =>
          pieceValue f K *
            alphaContent (K ∩ L)) := by

      rw [Finset.mul_sum]


/-!
============================================================
Expand the integral over P'
============================================================
-/

lemma pcRSIntegral_eq_double_sum_right
    (alphaContent : Set ℝ → ℝ)
    (f : ℝ → ℝ)
    (P P' : Finset (Set ℝ))
    (hAlphaRight :
      ∀ L ∈ P',
        P.sum
            (fun K =>
              alphaContent (K ∩ L))
          =
        alphaContent L) :
    pcRSIntegral alphaContent f P'
      =
    P'.sum
      (fun L =>
        P.sum
          (fun K =>
            pieceValue f L *
              alphaContent (K ∩ L))) := by

  classical

  unfold pcRSIntegral

  apply Finset.sum_congr rfl

  intro L hL

  have hdecomp :
      P.sum
          (fun K =>
            alphaContent (K ∩ L))
        =
      alphaContent L := by

    exact hAlphaRight L hL

  calc
    pieceValue f L * alphaContent L
        =
      pieceValue f L *
        P.sum
          (fun K =>
            alphaContent (K ∩ L)) := by

      rw [hdecomp]

    _ =
      P.sum
        (fun K =>
          pieceValue f L *
            alphaContent (K ∩ L)) := by

      rw [Finset.mul_sum]


/-!
============================================================
Replace c_K by c_L on every nonempty common-refinement piece
============================================================
-/

lemma double_sum_pieceValue_eq
    (alphaContent : Set ℝ → ℝ)
    (hEmpty : alphaContent ∅ = 0)
    (f : ℝ → ℝ)
    (P P' : Finset (Set ℝ))
    (hfP : PiecewiseConstantOn f P)
    (hfP' : PiecewiseConstantOn f P') :
    P.sum
        (fun K =>
          P'.sum
            (fun L =>
              pieceValue f K *
                alphaContent (K ∩ L)))
      =
    P.sum
        (fun K =>
          P'.sum
            (fun L =>
              pieceValue f L *
                alphaContent (K ∩ L))) := by

  classical

  apply Finset.sum_congr rfl

  intro K hK

  apply Finset.sum_congr rfl

  intro L hL

  exact intersection_term_eq
    alphaContent
    hEmpty
    f
    P
    P'
    hfP
    hfP'
    K
    L
    hK
    hL


/-!
============================================================
Swap the two finite sums
============================================================
-/

lemma double_sum_commute
    (alphaContent : Set ℝ → ℝ)
    (f : ℝ → ℝ)
    (P P' : Finset (Set ℝ)) :
    P.sum
        (fun K =>
          P'.sum
            (fun L =>
              pieceValue f L *
                alphaContent (K ∩ L)))
      =
    P'.sum
        (fun L =>
          P.sum
            (fun K =>
              pieceValue f L *
                alphaContent (K ∩ L))) := by

  classical

  rw [Finset.sum_comm]


/-!
============================================================
Riemann-Stieltjes version of Proposition 11.2.13
============================================================

The two decomposition assumptions are exactly the applications
of Lemma 11.8.4 to the partitions

  { K ∩ L | L ∈ P' }

of K, and

  { K ∩ L | K ∈ P }

of L.
-/

theorem proposition_11_8_2
    (alphaContent : Set ℝ → ℝ)
    (hEmpty :
      alphaContent ∅ = 0)
    (f : ℝ → ℝ)
    (P P' : Finset (Set ℝ))
    (hfP :
      PiecewiseConstantOn f P)
    (hfP' :
      PiecewiseConstantOn f P')
    (hAlphaLeft :
      ∀ K ∈ P,
        P'.sum
            (fun L =>
              alphaContent (K ∩ L))
          =
        alphaContent K)
    (hAlphaRight :
      ∀ L ∈ P',
        P.sum
            (fun K =>
              alphaContent (K ∩ L))
          =
        alphaContent L) :
    pcRSIntegral alphaContent f P =
      pcRSIntegral alphaContent f P' := by

  calc
    pcRSIntegral alphaContent f P
        =
      P.sum
        (fun K =>
          P'.sum
            (fun L =>
              pieceValue f K *
                alphaContent (K ∩ L))) := by

      exact pcRSIntegral_eq_double_sum_left
        alphaContent
        f
        P
        P'
        hAlphaLeft

    _ =
      P.sum
        (fun K =>
          P'.sum
            (fun L =>
              pieceValue f L *
                alphaContent (K ∩ L))) := by

      exact double_sum_pieceValue_eq
        alphaContent
        hEmpty
        f
        P
        P'
        hfP
        hfP'

    _ =
      P'.sum
        (fun L =>
          P.sum
            (fun K =>
              pieceValue f L *
                alphaContent (K ∩ L))) := by

      exact double_sum_commute
        alphaContent
        f
        P
        P'

    _ =
      pcRSIntegral alphaContent f P' := by

      symm

      exact pcRSIntegral_eq_double_sum_right
        alphaContent
        f
        P
        P'
        hAlphaRight


/-!
============================================================
Exercise 11.8.2
============================================================
-/

theorem exercise_11_8_2
    (alphaContent : Set ℝ → ℝ)
    (hEmpty :
      alphaContent ∅ = 0)
    (f : ℝ → ℝ)
    (P P' : Finset (Set ℝ))
    (hfP :
      PiecewiseConstantOn f P)
    (hfP' :
      PiecewiseConstantOn f P')
    (hAlphaLeft :
      ∀ K ∈ P,
        P'.sum
            (fun L =>
              alphaContent (K ∩ L))
          =
        alphaContent K)
    (hAlphaRight :
      ∀ L ∈ P',
        P.sum
            (fun K =>
              alphaContent (K ∩ L))
          =
        alphaContent L) :
    pcRSIntegral alphaContent f P =
      pcRSIntegral alphaContent f P' := by

  exact proposition_11_8_2
    alphaContent
    hEmpty
    f
    P
    P'
    hfP
    hfP'
    hAlphaLeft
    hAlphaRight

end TaoExercise11_8_2
