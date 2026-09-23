import Mathlib

namespace TaoExercise11_5_2

open Set

/-!
============================================================
Piecewise continuity on a finite partition
============================================================
-/

def PiecewiseContinuousOn
    (I : Set ℝ)
    (f : ℝ → ℝ)
    (P : Finset (Set ℝ)) : Prop :=
  (∀ J ∈ P, J ⊆ I) ∧
  (∀ J ∈ P, ContinuousOn f J)


/-!
============================================================
Zero extension of f restricted to J
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
Finite partition

Each x ∈ I belongs to exactly one piece J ∈ P.
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
The sum of the zero extensions equals f on I
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

      have hK_eq_J :
          K = J := by

        exact huniq K ⟨hK, hxK⟩

      exact hKne hK_eq_J

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
Finite sums of integrable functions are integrable

This is the finite iteration of Theorem 11.4.1(a).
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
Proposition 11.5.6

Each piece is continuous, hence integrable on its piece.
Theorem 11.4.1(g) gives integrability after extension by 0.
Theorem 11.4.1(a) gives integrability of their finite sum.
============================================================
-/

theorem proposition_11_5_6
    (I : Set ℝ)
    (f : ℝ → ℝ)
    (P : Finset (Set ℝ))
    (IntegrableOn :
      Set ℝ → (ℝ → ℝ) → Prop)
    (hPartition :
      IsPartition I P)

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
    Integrability depends only on the values on I.
    -/
    (hcongr :
      ∀ u v : ℝ → ℝ,
        (∀ x ∈ I,
          u x = v x) →
        IntegrableOn I u →
        IntegrableOn I v)

    /-
    Proposition 11.5.3 + Theorem 11.4.1(g):
    the extension by zero of every continuous piece is
    integrable on I.
    -/
    (hPieceIntegrable :
      ∀ J ∈ P,
        IntegrableOn I
          (pieceExtension J f)) :
    IntegrableOn I f := by

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
      hPieceIntegrable

  have hEq :
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

  exact hcongr
    (fun x =>
      P.sum
        (fun J =>
          pieceExtension J f x))
    f
    hEq
    hsumInt


/-!
============================================================
Exercise 11.5.2
============================================================
-/

theorem exercise_11_5_2
    (I : Set ℝ)
    (f : ℝ → ℝ)
    (P : Finset (Set ℝ))
    (IntegrableOn :
      Set ℝ → (ℝ → ℝ) → Prop)
    (hPartition :
      IsPartition I P)
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
        IntegrableOn I v)
    (hPieceIntegrable :
      ∀ J ∈ P,
        IntegrableOn I
          (pieceExtension J f)) :
    IntegrableOn I f := by

  exact proposition_11_5_6
    I
    f
    P
    IntegrableOn
    hPartition
    hzero
    hadd
    hcongr
    hPieceIntegrable

end TaoExercise11_5_2
