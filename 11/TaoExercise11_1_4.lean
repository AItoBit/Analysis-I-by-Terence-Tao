import Mathlib

namespace TaoExercise11_1_4

open Set

variable {α : Type*}

/-!
============================================================
A partition of I

Every member of P is contained in I, and every x ∈ I
belongs to exactly one member of P.
============================================================
-/

def IsPartitionTao
    (I : Set α)
    (P : Set (Set α)) : Prop :=
  (∀ J ∈ P, J ⊆ I) ∧
  (∀ x ∈ I,
    ∃! J : Set α,
      J ∈ P ∧ x ∈ J)


/-!
============================================================
Common refinement

P # P' = { J ∩ K | J ∈ P, K ∈ P' }
============================================================
-/

def CommonRefinement
    (P P' : Set (Set α)) :
    Set (Set α) :=
  {S : Set α |
    ∃ J ∈ P,
      ∃ K ∈ P',
        S = J ∩ K}


/-!
============================================================
Q is finer than P

Every member of Q is contained in some member of P.
============================================================
-/

def FinerThan
    (Q P : Set (Set α)) : Prop :=
  ∀ S ∈ Q,
    ∃ J ∈ P,
      S ⊆ J


/-!
============================================================
The common refinement is a partition
============================================================
-/

theorem commonRefinement_isPartition
    (I : Set α)
    (P P' : Set (Set α))
    (hP : IsPartitionTao I P)
    (hP' : IsPartitionTao I P') :
    IsPartitionTao I (CommonRefinement P P') := by

  rcases hP with ⟨hPsub, hPuniq⟩
  rcases hP' with ⟨hP'sub, hP'uniq⟩

  constructor

  /-
  Every J ∩ K is contained in I.
  -/
  · intro S hS

    rcases hS with ⟨J, hJP, K, hKP', rfl⟩

    intro x hx

    exact hPsub J hJP hx.1

  /-
  Every x ∈ I belongs to exactly one intersection J ∩ K.
  -/
  · intro x hxI

    obtain ⟨J, hJ, hJuniq⟩ :=
      hPuniq x hxI

    obtain ⟨K, hK, hKuniq⟩ :=
      hP'uniq x hxI

    refine ⟨J ∩ K, ?_, ?_⟩

    /-
    Existence.
    -/
    · constructor

      · exact ⟨J, hJ.1, K, hK.1, rfl⟩

      · exact ⟨hJ.2, hK.2⟩

    /-
    Uniqueness.
    -/
    · intro S hS

      rcases hS.1 with
        ⟨J', hJ'P, K', hK'P', hSeq⟩

      have hxS :
          x ∈ S := hS.2

      have hxInter :
          x ∈ J' ∩ K' := by
        rw [← hSeq]
        exact hxS

      have hxJ' :
          x ∈ J' := hxInter.1

      have hxK' :
          x ∈ K' := hxInter.2

      have hJJ' :
          J' = J := by
        exact hJuniq J' ⟨hJ'P, hxJ'⟩

      have hKK' :
          K' = K := by
        exact hKuniq K' ⟨hK'P', hxK'⟩

      rw [hSeq, hJJ', hKK']


/-!
============================================================
The common refinement is finer than P
============================================================
-/

theorem commonRefinement_finer_left
    (P P' : Set (Set α)) :
    FinerThan (CommonRefinement P P') P := by

  intro S hS

  rcases hS with ⟨J, hJP, K, hKP', rfl⟩

  refine ⟨J, hJP, ?_⟩

  intro x hx

  exact hx.1


/-!
============================================================
The common refinement is finer than P'
============================================================
-/

theorem commonRefinement_finer_right
    (P P' : Set (Set α)) :
    FinerThan (CommonRefinement P P') P' := by

  intro S hS

  rcases hS with ⟨J, hJP, K, hKP', rfl⟩

  refine ⟨K, hKP', ?_⟩

  intro x hx

  exact hx.2


/-!
============================================================
Lemma 11.1.18
============================================================
-/

theorem lemma_11_1_18
    (I : Set α)
    (P P' : Set (Set α))
    (hP : IsPartitionTao I P)
    (hP' : IsPartitionTao I P') :
    IsPartitionTao I (CommonRefinement P P')
      ∧
    FinerThan (CommonRefinement P P') P
      ∧
    FinerThan (CommonRefinement P P') P' := by

  exact
    ⟨commonRefinement_isPartition I P P' hP hP',
     commonRefinement_finer_left P P',
     commonRefinement_finer_right P P'⟩


/-!
============================================================
Exercise 11.1.4
============================================================
-/

theorem exercise_11_1_4
    (I : Set ℝ)
    (P P' : Set (Set ℝ))
    (hP : IsPartitionTao I P)
    (hP' : IsPartitionTao I P') :
    IsPartitionTao I (CommonRefinement P P')
      ∧
    FinerThan (CommonRefinement P P') P
      ∧
    FinerThan (CommonRefinement P P') P' := by

  exact lemma_11_1_18 I P P' hP hP'

end TaoExercise11_1_4
