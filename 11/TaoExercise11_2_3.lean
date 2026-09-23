import Mathlib

namespace TaoExercise11_2_3

open Set

/-!
============================================================
Piecewise constant on a finite partition
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
Canonical value attached to a piece
============================================================
-/

noncomputable def pieceValue
    (f : ℝ → ℝ)
    (J : Set ℝ) : ℝ :=
  f (Classical.epsilon (fun x : ℝ => x ∈ J))


/-!
============================================================
If f is constant on J, then every value of f on J
equals pieceValue f J
============================================================
-/

lemma eq_pieceValue_of_piecewise
    (f : ℝ → ℝ)
    (P : Finset (Set ℝ))
    (hf : PiecewiseConstantOn f P)
    (J : Set ℝ)
    (hJ : J ∈ P)
    (x : ℝ)
    (hx : x ∈ J) :
    f x = pieceValue f J := by

  obtain ⟨c, hc⟩ :=
    hf J hJ

  have hne :
      J.Nonempty := by
    exact ⟨x, hx⟩

  have hchosen :
      Classical.epsilon (fun y : ℝ => y ∈ J) ∈ J := by
    exact Classical.epsilon_spec hne

  have hxVal :
      f x = c := by
    exact hc x hx

  have hchosenVal :
      f (Classical.epsilon (fun y : ℝ => y ∈ J)) = c := by
    exact hc
      (Classical.epsilon (fun y : ℝ => y ∈ J))
      hchosen

  unfold pieceValue

  exact hxVal.trans hchosenVal.symm


/-!
============================================================
Piecewise-constant integral associated with a finite partition
============================================================
-/

noncomputable def pcIntegral
    (len : Set ℝ → ℝ)
    (f : ℝ → ℝ)
    (P : Finset (Set ℝ)) : ℝ :=
  ∑ J ∈ P,
    pieceValue f J * len J


/-!
============================================================
If J ∩ K is nonempty, the two constants agree
============================================================
-/

lemma pieceValue_eq_on_nonempty_inter
    (f : ℝ → ℝ)
    (P P' : Finset (Set ℝ))
    (hfP : PiecewiseConstantOn f P)
    (hfP' : PiecewiseConstantOn f P')
    (J K : Set ℝ)
    (hJ : J ∈ P)
    (hK : K ∈ P')
    (hJK : (J ∩ K).Nonempty) :
    pieceValue f J = pieceValue f K := by

  obtain ⟨x, hx⟩ := hJK

  have hxJ :
      x ∈ J := by
    exact hx.1

  have hxK :
      x ∈ K := by
    exact hx.2

  have hJval :
      f x = pieceValue f J := by
    exact eq_pieceValue_of_piecewise
      f
      P
      hfP
      J
      hJ
      x
      hxJ

  have hKval :
      f x = pieceValue f K := by
    exact eq_pieceValue_of_piecewise
      f
      P'
      hfP'
      K
      hK
      x
      hxK

  exact hJval.symm.trans hKval


/-!
============================================================
If J ∩ K is not nonempty, it is empty
============================================================
-/

lemma inter_eq_empty_of_not_nonempty
    (J K : Set ℝ)
    (hJK : ¬(J ∩ K).Nonempty) :
    J ∩ K = ∅ := by

  ext x

  constructor

  · intro hx

    exfalso

    exact hJK ⟨x, hx⟩

  · intro hx

    exact hx.elim


/-!
============================================================
If J ∩ K is empty, its length is zero
============================================================
-/

lemma length_inter_eq_zero_of_not_nonempty
    (len : Set ℝ → ℝ)
    (hlen_empty : len ∅ = 0)
    (J K : Set ℝ)
    (hJK : ¬(J ∩ K).Nonempty) :
    len (J ∩ K) = 0 := by

  have hEmpty :
      J ∩ K = ∅ := by

    exact inter_eq_empty_of_not_nonempty
      J
      K
      hJK

  rw [hEmpty]

  exact hlen_empty


/-!
============================================================
Contribution on J ∩ K can be computed from J or K
============================================================
-/

lemma intersection_contribution_eq
    (len : Set ℝ → ℝ)
    (hlen_empty : len ∅ = 0)
    (f : ℝ → ℝ)
    (P P' : Finset (Set ℝ))
    (hfP : PiecewiseConstantOn f P)
    (hfP' : PiecewiseConstantOn f P')
    (J K : Set ℝ)
    (hJ : J ∈ P)
    (hK : K ∈ P') :
    pieceValue f J * len (J ∩ K) =
      pieceValue f K * len (J ∩ K) := by

  classical

  by_cases hJK :
      (J ∩ K).Nonempty

  · have hvalues :
        pieceValue f J = pieceValue f K := by

      exact pieceValue_eq_on_nonempty_inter
        f
        P
        P'
        hfP
        hfP'
        J
        K
        hJ
        hK
        hJK

    rw [hvalues]

  · have hlen :
        len (J ∩ K) = 0 := by

      exact length_inter_eq_zero_of_not_nonempty
        len
        hlen_empty
        J
        K
        hJK

    rw [hlen]

    simp


/-!
============================================================
Expand pcIntegral over P using intersections with P'
============================================================
-/

lemma pcIntegral_eq_double_sum_left
    (len : Set ℝ → ℝ)
    (f : ℝ → ℝ)
    (P P' : Finset (Set ℝ))
    (hlen_left :
      ∀ J ∈ P,
        (∑ K ∈ P', len (J ∩ K)) = len J) :
    pcIntegral len f P =
      ∑ J ∈ P,
        ∑ K ∈ P',
          pieceValue f J * len (J ∩ K) := by

  classical

  unfold pcIntegral

  apply Finset.sum_congr rfl

  intro J hJ

  have hlen :
      (∑ K ∈ P', len (J ∩ K)) = len J := by
    exact hlen_left J hJ

  calc
    pieceValue f J * len J =
        pieceValue f J *
          (∑ K ∈ P', len (J ∩ K)) := by
            rw [hlen]

    _ =
        ∑ K ∈ P',
          pieceValue f J * len (J ∩ K) := by
            rw [Finset.mul_sum]


/-!
============================================================
Expand pcIntegral over P' using intersections with P
============================================================
-/

lemma pcIntegral_eq_double_sum_right
    (len : Set ℝ → ℝ)
    (f : ℝ → ℝ)
    (P P' : Finset (Set ℝ))
    (hlen_right :
      ∀ K ∈ P',
        (∑ J ∈ P, len (J ∩ K)) = len K) :
    pcIntegral len f P' =
      ∑ K ∈ P',
        ∑ J ∈ P,
          pieceValue f K * len (J ∩ K) := by

  classical

  unfold pcIntegral

  apply Finset.sum_congr rfl

  intro K hK

  have hlen :
      (∑ J ∈ P, len (J ∩ K)) = len K := by
    exact hlen_right K hK

  calc
    pieceValue f K * len K =
        pieceValue f K *
          (∑ J ∈ P, len (J ∩ K)) := by
            rw [hlen]

    _ =
        ∑ J ∈ P,
          pieceValue f K * len (J ∩ K) := by
            rw [Finset.mul_sum]


/-!
============================================================
Replace pieceValue f J by pieceValue f K
inside each intersection
============================================================
-/

lemma double_sum_pieceValue_eq
    (len : Set ℝ → ℝ)
    (hlen_empty : len ∅ = 0)
    (f : ℝ → ℝ)
    (P P' : Finset (Set ℝ))
    (hfP : PiecewiseConstantOn f P)
    (hfP' : PiecewiseConstantOn f P') :
    (∑ J ∈ P,
        ∑ K ∈ P',
          pieceValue f J * len (J ∩ K))
      =
    ∑ J ∈ P,
      ∑ K ∈ P',
        pieceValue f K * len (J ∩ K) := by

  classical

  apply Finset.sum_congr rfl

  intro J hJ

  apply Finset.sum_congr rfl

  intro K hK

  exact intersection_contribution_eq
    len
    hlen_empty
    f
    P
    P'
    hfP
    hfP'
    J
    K
    hJ
    hK


/-!
============================================================
Finite Fubini
============================================================
-/

lemma double_sum_commute
    (len : Set ℝ → ℝ)
    (f : ℝ → ℝ)
    (P P' : Finset (Set ℝ)) :
    (∑ J ∈ P,
        ∑ K ∈ P',
          pieceValue f K * len (J ∩ K))
      =
    ∑ K ∈ P',
      ∑ J ∈ P,
        pieceValue f K * len (J ∩ K) := by

  classical

  rw [Finset.sum_comm]


/-!
============================================================
Proposition 11.2.13
============================================================
-/

theorem proposition_11_2_13
    (len : Set ℝ → ℝ)
    (hlen_empty : len ∅ = 0)
    (f : ℝ → ℝ)
    (P P' : Finset (Set ℝ))
    (hfP : PiecewiseConstantOn f P)
    (hfP' : PiecewiseConstantOn f P')
    (hlen_left :
      ∀ J ∈ P,
        (∑ K ∈ P', len (J ∩ K)) = len J)
    (hlen_right :
      ∀ K ∈ P',
        (∑ J ∈ P, len (J ∩ K)) = len K) :
    pcIntegral len f P =
      pcIntegral len f P' := by

  calc
    pcIntegral len f P
        =
      ∑ J ∈ P,
        ∑ K ∈ P',
          pieceValue f J * len (J ∩ K) := by

      exact pcIntegral_eq_double_sum_left
        len
        f
        P
        P'
        hlen_left

    _ =
      ∑ J ∈ P,
        ∑ K ∈ P',
          pieceValue f K * len (J ∩ K) := by

      exact double_sum_pieceValue_eq
        len
        hlen_empty
        f
        P
        P'
        hfP
        hfP'

    _ =
      ∑ K ∈ P',
        ∑ J ∈ P,
          pieceValue f K * len (J ∩ K) := by

      exact double_sum_commute
        len
        f
        P
        P'

    _ =
      pcIntegral len f P' := by

      symm

      exact pcIntegral_eq_double_sum_right
        len
        f
        P
        P'
        hlen_right


/-!
============================================================
Exercise 11.2.3
============================================================
-/

theorem exercise_11_2_3
    (len : Set ℝ → ℝ)
    (hlen_empty : len ∅ = 0)
    (f : ℝ → ℝ)
    (P P' : Finset (Set ℝ))
    (hfP : PiecewiseConstantOn f P)
    (hfP' : PiecewiseConstantOn f P')
    (hlen_left :
      ∀ J ∈ P,
        (∑ K ∈ P', len (J ∩ K)) = len J)
    (hlen_right :
      ∀ K ∈ P',
        (∑ J ∈ P, len (J ∩ K)) = len K) :
    pcIntegral len f P =
      pcIntegral len f P' := by

  exact proposition_11_2_13
    len
    hlen_empty
    f
    P
    P'
    hfP
    hfP'
    hlen_left
    hlen_right

end TaoExercise11_2_3
