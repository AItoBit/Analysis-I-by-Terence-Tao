import Mathlib

namespace TaoExercise11_6_2

open Set

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
Piecewise monotone functions
============================================================

f is piecewise monotone on I if there exists a finite
partition P of I such that f is monotone on every piece.
-/

def PiecewiseMonotoneOn
    (I : Set ℝ)
    (f : ℝ → ℝ) : Prop :=
  ∃ P : Finset (Set ℝ),
    IsPartition I P ∧
    ∀ J ∈ P,
      MonotoneOn f J


/-!
============================================================
Boundedness on I
============================================================
-/

def BoundedOnTao
    (I : Set ℝ)
    (f : ℝ → ℝ) : Prop :=
  ∃ M : ℝ,
    0 ≤ M ∧
    ∀ x ∈ I,
      |f x| ≤ M


lemma boundedOn_subset
    (I J : Set ℝ)
    (f : ℝ → ℝ)
    (hJI : J ⊆ I)
    (hf : BoundedOnTao I f) :
    BoundedOnTao J f := by

  obtain ⟨M, hM, hbound⟩ := hf

  refine ⟨M, hM, ?_⟩

  intro x hx

  exact hbound x (hJI hx)


/-!
============================================================
Zero extension of one partition piece
============================================================
-/

noncomputable def pieceExtension
    (J : Set ℝ)
    (f : ℝ → ℝ) :
    ℝ → ℝ := by
  classical
  exact fun x =>
    if x ∈ J then f x else 0


lemma pieceExtension_eq_of_mem
    (J : Set ℝ)
    (f : ℝ → ℝ)
    (x : ℝ)
    (hx : x ∈ J) :
    pieceExtension J f x = f x := by

  unfold pieceExtension

  simp [hx]


lemma pieceExtension_eq_zero_of_not_mem
    (J : Set ℝ)
    (f : ℝ → ℝ)
    (x : ℝ)
    (hx : x ∉ J) :
    pieceExtension J f x = 0 := by

  unfold pieceExtension

  simp [hx]


/-!
============================================================
The sum of the piece extensions is f on I
============================================================
-/

lemma sum_pieceExtensions_eq
    (I : Set ℝ)
    (f : ℝ → ℝ)
    (P : Finset (Set ℝ))
    (hP : IsPartition I P) :
    ∀ x ∈ I,
      P.sum
          (fun J =>
            pieceExtension J f x)
        =
      f x := by

  classical

  intro x hxI

  obtain ⟨J, ⟨hJmem, hxJ⟩, huniq⟩ :=
    hP.2 x hxI

  have hzero :
      ∀ K ∈ P,
        K ≠ J →
        pieceExtension K f x = 0 := by

    intro K hK hKne

    have hxNotK :
        x ∉ K := by

      intro hxK

      have hKJ :
          K = J := by

        exact huniq
          K
          ⟨hK, hxK⟩

      exact hKne hKJ

    exact pieceExtension_eq_zero_of_not_mem
      K
      f
      x
      hxNotK

  calc
    P.sum
        (fun K =>
          pieceExtension K f x)
        =
      pieceExtension J f x := by

      rw [Finset.sum_eq_single J]

      · intro K hK hKne

        exact hzero
          K
          hK
          hKne

      · intro hJnot

        exact False.elim
          (hJnot hJmem)

    _ =
      f x := by

      exact pieceExtension_eq_of_mem
        J
        f
        x
        hxJ


/-!
============================================================
Finite sums of integrable functions

This formalizes repeated applications of
Theorem 11.4.1(a).
============================================================
-/

theorem integrable_finset_sum
    (I : Set ℝ)
    (IntegrableOn :
      Set ℝ → (ℝ → ℝ) → Prop)
    (P : Finset (Set ℝ))
    (G : Set ℝ → ℝ → ℝ)
    (hzero :
      IntegrableOn I
        (fun _ => 0))
    (hadd :
      ∀ u v : ℝ → ℝ,
        IntegrableOn I u →
        IntegrableOn I v →
        IntegrableOn I
          (fun x => u x + v x))
    (hG :
      ∀ J ∈ P,
        IntegrableOn I (G J)) :
    IntegrableOn I
      (fun x =>
        P.sum
          (fun J =>
            G J x)) := by

  classical

  induction P using Finset.induction_on with

  | empty =>

      simpa using hzero

  | @insert J Q hJ ih =>

      have hJint :
          IntegrableOn I (G J) := by

        exact hG
          J
          (Finset.mem_insert_self J Q)

      have hQ :
          ∀ K ∈ Q,
            IntegrableOn I (G K) := by

        intro K hK

        exact hG
          K
          (Finset.mem_insert_of_mem hK)

      have hQint :
          IntegrableOn I
            (fun x =>
              Q.sum
                (fun K =>
                  G K x)) := by

        exact ih hQ

      have haddInt :
          IntegrableOn I
            (fun x =>
              G J x +
              Q.sum
                (fun K =>
                  G K x)) := by

        exact hadd
          (G J)
          (fun x =>
            Q.sum
              (fun K =>
                G K x))
          hJint
          hQint

      simpa [Finset.sum_insert, hJ] using haddInt


/-!
============================================================
Piecewise monotone relative to a fixed partition
============================================================
-/

def PiecewiseMonotoneOnPartition
    (f : ℝ → ℝ)
    (P : Finset (Set ℝ)) : Prop :=
  ∀ J ∈ P,
    MonotoneOn f J


/-!
============================================================
Main theorem relative to a chosen partition
============================================================

hMonotoneIntegrable corresponds to Corollary 11.6.3.

hExtend corresponds to Theorem 11.4.1(g).

hadd corresponds to Theorem 11.4.1(a).
-/

theorem bounded_piecewiseMonotone_integrable_on_partition
    (I : Set ℝ)
    (f : ℝ → ℝ)
    (P : Finset (Set ℝ))
    (IntegrableOn :
      Set ℝ → (ℝ → ℝ) → Prop)

    (hPartition :
      IsPartition I P)

    (hPiecewise :
      PiecewiseMonotoneOnPartition f P)

    (hBounded :
      BoundedOnTao I f)

    /-
    Corollary 11.6.3:
    bounded + monotone on J -> integrable on J.
    -/
    (hMonotoneIntegrable :
      ∀ J : Set ℝ,
        BoundedOnTao J f →
        MonotoneOn f J →
        IntegrableOn J f)

    /-
    Theorem 11.4.1(g):
    integrability survives extension by zero.
    -/
    (hExtend :
      ∀ J : Set ℝ,
        J ⊆ I →
        IntegrableOn J f →
        IntegrableOn I
          (pieceExtension J f))

    /-
    The zero function is integrable.
    -/
    (hzero :
      IntegrableOn I
        (fun _ => 0))

    /-
    Theorem 11.4.1(a).
    -/
    (hadd :
      ∀ u v : ℝ → ℝ,
        IntegrableOn I u →
        IntegrableOn I v →
        IntegrableOn I
          (fun x => u x + v x))

    /-
    Integrability is invariant under equality on I.
    -/
    (hcongr :
      ∀ u v : ℝ → ℝ,
        (∀ x ∈ I,
          u x = v x) →
        IntegrableOn I u →
        IntegrableOn I v) :
    IntegrableOn I f := by

  /-
  Every individual piece is integrable after extension by zero.
  -/

  have hPieceExt :
      ∀ J ∈ P,
        IntegrableOn I
          (pieceExtension J f) := by

    intro J hJ

    have hJI :
        J ⊆ I := by

      exact hPartition.1 J hJ

    have hBoundJ :
        BoundedOnTao J f := by

      exact boundedOn_subset
        I
        J
        f
        hJI
        hBounded

    have hMonoJ :
        MonotoneOn f J := by

      exact hPiecewise
        J
        hJ

    have hIntJ :
        IntegrableOn J f := by

      exact hMonotoneIntegrable
        J
        hBoundJ
        hMonoJ

    exact hExtend
      J
      hJI
      hIntJ

  /-
  Their finite sum is integrable on I.
  -/

  have hsumInt :
      IntegrableOn I
        (fun x =>
          P.sum
            (fun J =>
              pieceExtension J f x)) := by

    exact integrable_finset_sum
      I
      IntegrableOn
      P
      (fun J =>
        pieceExtension J f)
      hzero
      hadd
      hPieceExt

  /-
  Since P is a partition, that sum agrees with f on I.
  -/

  have hsumEq :
      ∀ x ∈ I,
        P.sum
            (fun J =>
              pieceExtension J f x)
          =
        f x := by

    exact sum_pieceExtensions_eq
      I
      f
      P
      hPartition

  /-
  Therefore f itself is integrable.
  -/

  exact hcongr
    (fun x =>
      P.sum
        (fun J =>
          pieceExtension J f x))
    f
    hsumEq
    hsumInt


/-!
============================================================
Exercise 11.6.2

Now use the existential definition of PiecewiseMonotoneOn.
============================================================
-/

theorem exercise_11_6_2
    (I : Set ℝ)
    (f : ℝ → ℝ)
    (IntegrableOn :
      Set ℝ → (ℝ → ℝ) → Prop)

    (hPiecewise :
      PiecewiseMonotoneOn I f)

    (hBounded :
      BoundedOnTao I f)

    (hMonotoneIntegrable :
      ∀ J : Set ℝ,
        BoundedOnTao J f →
        MonotoneOn f J →
        IntegrableOn J f)

    (hExtend :
      ∀ J : Set ℝ,
        J ⊆ I →
        IntegrableOn J f →
        IntegrableOn I
          (pieceExtension J f))

    (hzero :
      IntegrableOn I
        (fun _ => 0))

    (hadd :
      ∀ u v : ℝ → ℝ,
        IntegrableOn I u →
        IntegrableOn I v →
        IntegrableOn I
          (fun x => u x + v x))

    (hcongr :
      ∀ u v : ℝ → ℝ,
        (∀ x ∈ I,
          u x = v x) →
        IntegrableOn I u →
        IntegrableOn I v) :
    IntegrableOn I f := by

  obtain ⟨P, hPartition, hMono⟩ :=
    hPiecewise

  exact bounded_piecewiseMonotone_integrable_on_partition
    I
    f
    P
    IntegrableOn
    hPartition
    hMono
    hBounded
    hMonotoneIntegrable
    hExtend
    hzero
    hadd
    hcongr

end TaoExercise11_6_2
