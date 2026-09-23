import Mathlib

namespace TaoExercise11_4_2

open Set

/-!
============================================================
Union of all pieces of a finite partition
============================================================
-/

def unionPieces
    (P : Finset (Set ℝ)) :
    Set ℝ :=
  {x : ℝ |
    ∃ J : Set ℝ,
      J ∈ P ∧ x ∈ J}


lemma unionPieces_empty :
    unionPieces (∅ : Finset (Set ℝ)) = ∅ := by
  ext x
  simp [unionPieces]


lemma unionPieces_insert
    (J : Set ℝ)
    (P : Finset (Set ℝ)) :
    unionPieces (insert J P) =
      J ∪ unionPieces P := by

  classical

  ext x

  simp [unionPieces]


/-!
============================================================
A finite family covers I
============================================================
-/

def Covers
    (I : Set ℝ)
    (P : Finset (Set ℝ)) : Prop :=
  unionPieces P = I


/-!
============================================================
Finite additivity over all pieces
============================================================
-/

theorem integral_unionPieces_eq_sum
    (IntOn :
      Set ℝ → (ℝ → ℝ) → ℝ)
    (f : ℝ → ℝ)
    (P : Finset (Set ℝ))
    (hEmpty :
      IntOn ∅ f = 0)
    (hStep :
      ∀ J : Set ℝ,
      ∀ Q : Finset (Set ℝ),
        J ∉ Q →
        IntOn (unionPieces (insert J Q)) f =
          IntOn (unionPieces Q) f +
          IntOn J f) :
    IntOn (unionPieces P) f =
      P.sum (fun J =>
        IntOn J f) := by

  classical

  induction P using Finset.induction_on with

  | empty =>

      rw [unionPieces_empty]

      rw [hEmpty]

      simp

  | @insert J Q hJ ih =>

      rw [hStep J Q hJ]

      rw [ih]

      rw [Finset.sum_insert hJ]

      exact add_comm
        (Q.sum (fun K => IntOn K f))
        (IntOn J f)


/-!
============================================================
Exercise 11.4.2

If P covers I, then

    ∫_I f = Σ_{J ∈ P} ∫_J f
============================================================
-/

theorem exercise_11_4_2
    (I : Set ℝ)
    (f : ℝ → ℝ)
    (P : Finset (Set ℝ))
    (IntOn :
      Set ℝ → (ℝ → ℝ) → ℝ)
    (hCover :
      Covers I P)
    (hEmpty :
      IntOn ∅ f = 0)
    (hStep :
      ∀ J : Set ℝ,
      ∀ Q : Finset (Set ℝ),
        J ∉ Q →
        IntOn (unionPieces (insert J Q)) f =
          IntOn (unionPieces Q) f +
          IntOn J f) :
    IntOn I f =
      P.sum (fun J =>
        IntOn J f) := by

  have hUnion :
      unionPieces P = I := by
    exact hCover

  rw [← hUnion]

  exact integral_unionPieces_eq_sum
    IntOn
    f
    P
    hEmpty
    hStep


/-!
============================================================
Same result with the covering equality given directly
============================================================
-/

theorem exercise_11_4_2_induction
    (I : Set ℝ)
    (f : ℝ → ℝ)
    (P : Finset (Set ℝ))
    (IntOn :
      Set ℝ → (ℝ → ℝ) → ℝ)
    (hCover :
      unionPieces P = I)
    (hEmpty :
      IntOn ∅ f = 0)
    (hAddPiece :
      ∀ J : Set ℝ,
      ∀ Q : Finset (Set ℝ),
        J ∉ Q →
        IntOn (unionPieces (insert J Q)) f =
          IntOn (unionPieces Q) f +
          IntOn J f) :
    IntOn I f =
      P.sum (fun J =>
        IntOn J f) := by

  rw [← hCover]

  exact integral_unionPieces_eq_sum
    IntOn
    f
    P
    hEmpty
    hAddPiece

end TaoExercise11_4_2
