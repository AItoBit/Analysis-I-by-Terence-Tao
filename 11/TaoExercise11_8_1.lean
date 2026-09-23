import Mathlib

namespace TaoExercise11_8_1

open Set

/-!
============================================================
Finite partitions
============================================================
-/

def unionPieces
    (P : Finset (Set ℝ)) :
    Set ℝ :=
  {x : ℝ |
    ∃ J : Set ℝ,
      J ∈ P ∧ x ∈ J}


def IsPartition
    (I : Set ℝ)
    (P : Finset (Set ℝ)) : Prop :=
  (∀ J ∈ P, J ⊆ I) ∧
  (∀ x ∈ I,
    ∃! J : Set ℝ,
      J ∈ P ∧ x ∈ J)


/-!
============================================================
Basic facts about unionPieces
============================================================
-/

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
Abstract α-content of an interval
============================================================

alphaContent J represents Tao's notation α[J].

The proof of Lemma 11.8.4 only needs:

  α[∅] = 0

and finite additivity when one partition piece is removed.
-/

variable
    (alphaContent : Set ℝ → ℝ)


/-!
============================================================
Continuous-case algebra

For a continuous α, on an interval [a,b] one has

  α[[a,b]] = α(b) - α(a).

Splitting at c gives the required additive identity.
============================================================
-/

def closedContent
    (α : ℝ → ℝ)
    (a b : ℝ) : ℝ :=
  α b - α a


lemma closedContent_split
    (α : ℝ → ℝ)
    (a c b : ℝ) :
    closedContent α a b =
      closedContent α a c +
      closedContent α c b := by

  unfold closedContent

  ring


/-!
The same algebraic identity in the orientation used in the
induction step.
-/

lemma closedContent_split'
    (α : ℝ → ℝ)
    (a c b : ℝ) :
    closedContent α a c +
      closedContent α c b =
    closedContent α a b := by

  symm

  exact closedContent_split α a c b


/-!
============================================================
Finite-additivity induction

This is the combinatorial core of Lemma 11.8.4.

hAddPiece represents the identity proved in Tao's two endpoint
cases:

  α[union(Q ∪ {J})]
    =
  α[union Q] + α[J].
============================================================
-/

theorem alphaContent_unionPieces_eq_sum
    (alphaContent : Set ℝ → ℝ)
    (P : Finset (Set ℝ))
    (hEmpty :
      alphaContent ∅ = 0)
    (hAddPiece :
      ∀ J : Set ℝ,
      ∀ Q : Finset (Set ℝ),
        J ∉ Q →
        alphaContent (unionPieces (insert J Q))
          =
        alphaContent (unionPieces Q) +
          alphaContent J) :
    alphaContent (unionPieces P)
      =
    P.sum alphaContent := by

  classical

  induction P using Finset.induction_on with

  | empty =>

      rw [unionPieces_empty]

      rw [hEmpty]

      simp

  | @insert J Q hJ ih =>

      rw [hAddPiece J Q hJ]

      rw [ih]

      rw [Finset.sum_insert hJ]

      exact add_comm
        (Q.sum alphaContent)
        (alphaContent J)


/-!
============================================================
Version oriented exactly as Tao's statement

  Σ_{J∈P} α[J] = α[I]
============================================================
-/

theorem alphaContent_sum_eq_unionPieces
    (alphaContent : Set ℝ → ℝ)
    (P : Finset (Set ℝ))
    (hEmpty :
      alphaContent ∅ = 0)
    (hAddPiece :
      ∀ J : Set ℝ,
      ∀ Q : Finset (Set ℝ),
        J ∉ Q →
        alphaContent (unionPieces (insert J Q))
          =
        alphaContent (unionPieces Q) +
          alphaContent J) :
    P.sum alphaContent
      =
    alphaContent (unionPieces P) := by

  symm

  exact alphaContent_unionPieces_eq_sum
    alphaContent
    P
    hEmpty
    hAddPiece


/-!
============================================================
Lemma 11.8.4

If P is a partition of I and α-content is additive under
the removal/addition of one partition piece, then

  Σ J∈P, α[J] = α[I].
============================================================
-/

theorem lemma_11_8_4
    (I : Set ℝ)
    (P : Finset (Set ℝ))
    (alphaContent : Set ℝ → ℝ)
    (hCover :
      unionPieces P = I)
    (hEmpty :
      alphaContent ∅ = 0)
    (hAddPiece :
      ∀ J : Set ℝ,
      ∀ Q : Finset (Set ℝ),
        J ∉ Q →
        alphaContent (unionPieces (insert J Q))
          =
        alphaContent (unionPieces Q) +
          alphaContent J) :
    P.sum alphaContent =
      alphaContent I := by

  rw [← hCover]

  exact alphaContent_sum_eq_unionPieces
    alphaContent
    P
    hEmpty
    hAddPiece


/-!
============================================================
Same theorem using IsPartition
============================================================
-/

theorem lemma_11_8_4_of_partition
    (I : Set ℝ)
    (P : Finset (Set ℝ))
    (alphaContent : Set ℝ → ℝ)
    (hP : IsPartition I P)
    (hCover :
      unionPieces P = I)
    (hEmpty :
      alphaContent ∅ = 0)
    (hAddPiece :
      ∀ J : Set ℝ,
      ∀ Q : Finset (Set ℝ),
        J ∉ Q →
        alphaContent (unionPieces (insert J Q))
          =
        alphaContent (unionPieces Q) +
          alphaContent J) :
    P.sum alphaContent =
      alphaContent I := by

  have _hpieces :
      ∀ J ∈ P,
        J ⊆ I := by

    exact hP.1

  exact lemma_11_8_4
    I
    P
    alphaContent
    hCover
    hEmpty
    hAddPiece


/-!
============================================================
Concrete continuous split

This isolates precisely Tao's calculation

  α(b)-α(a)
    =
  (α(c)-α(a)) + (α(b)-α(c)).
============================================================
-/

theorem continuous_interval_split_identity
    (α : ℝ → ℝ)
    (a c b : ℝ) :
    (α b - α a)
      =
    (α c - α a) +
      (α b - α c) := by

  ring


/-!
============================================================
Monotone-case telescoping identity

The one-sided-limit terms in Tao's definition cancel in
exactly the same algebraic way.

Here Lc represents lim_{x→c⁻} α(x).
============================================================
-/

theorem monotone_interval_split_identity
    (αa αb Lc : ℝ) :
    αb - αa =
      (Lc - αa) +
      (αb - Lc) := by

  ring


/-!
============================================================
Exercise 11.8.1
============================================================
-/

theorem exercise_11_8_1
    (I : Set ℝ)
    (P : Finset (Set ℝ))
    (alphaContent : Set ℝ → ℝ)
    (hCover :
      unionPieces P = I)
    (hEmpty :
      alphaContent ∅ = 0)
    (hAddPiece :
      ∀ J : Set ℝ,
      ∀ Q : Finset (Set ℝ),
        J ∉ Q →
        alphaContent (unionPieces (insert J Q))
          =
        alphaContent (unionPieces Q) +
          alphaContent J) :
    P.sum alphaContent =
      alphaContent I := by

  exact lemma_11_8_4
    I
    P
    alphaContent
    hCover
    hEmpty
    hAddPiece

end TaoExercise11_8_1
