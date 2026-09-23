import Mathlib

namespace TaoExercise9_1_13

open Set
open Filter
open Topology

def IsBoundedSet (X : Set ℝ) : Prop :=
  ∃ M : ℝ,
    0 < M ∧
    ∀ x : ℝ, x ∈ X →
      -M ≤ x ∧ x ≤ M


theorem bornology_bounded_of_tao_bounded
    (X : Set ℝ)
    (hX : IsBoundedSet X) :
    Bornology.IsBounded X := by

  rcases hX with ⟨M, hMpos, hM⟩

  have hsub :
      X ⊆ Set.Icc (-M) M := by
    intro x hx
    exact hM x hx

  exact
    (Metric.isBounded_Icc (-M) M).subset hsub


theorem tao_bounded_of_bornology_bounded
    (X : Set ℝ)
    (hX : Bornology.IsBounded X) :
    IsBoundedSet X := by

  obtain ⟨R, hsub⟩ :=
    (Metric.isBounded_iff_subset_closedBall
      (s := X)
      (c := (0 : ℝ))).1 hX

  let M : ℝ := |R| + 1

  have hMpos :
      0 < M := by
    dsimp [M]
    have hR :
        0 ≤ |R| := abs_nonneg R
    linarith

  refine ⟨M, hMpos, ?_⟩

  intro x hx

  have hxBall :
      x ∈ Metric.closedBall (0 : ℝ) R := by
    exact hsub hx

  have hdist :
      dist x (0 : ℝ) ≤ R := by
    exact hxBall

  have habs :
      |x| ≤ R := by
    simpa [Real.dist_eq] using hdist

  have hRabs :
      R ≤ |R| := by
    exact le_abs_self R

  have hxabs :
      |x| ≤ |R| := by
    exact le_trans habs hRabs

  have hxBounds :
      -|R| ≤ x ∧ x ≤ |R| := by
    exact abs_le.mp hxabs

  constructor

  · dsimp [M]
    linarith [hxBounds.1]

  · dsimp [M]
    linarith [hxBounds.2]


def TaoSeqCompact (X : Set ℝ) : Prop :=
  ∀ a : ℕ → ℝ,
    (∀ n : ℕ, a n ∈ X) →
    ∃ L : ℝ,
      L ∈ X ∧
      ∃ φ : ℕ → ℕ,
        StrictMono φ ∧
        Tendsto (a ∘ φ) atTop (𝓝 L)


theorem seqCompact_iff_tao_property
    (X : Set ℝ) :
    IsSeqCompact X ↔ TaoSeqCompact X := by
  rfl


theorem closed_bounded_implies_seqCompact
    (X : Set ℝ)
    (hClosed : IsClosed X)
    (hBounded : IsBoundedSet X) :
    IsSeqCompact X := by

  have hBorn :
      Bornology.IsBounded X := by
    exact
      bornology_bounded_of_tao_bounded
        X
        hBounded

  have hCompact :
      IsCompact X := by
    exact
      (Metric.isCompact_iff_isClosed_bounded).2
        ⟨hClosed, hBorn⟩

  exact
    (isCompact_iff_isSeqCompact).1 hCompact


theorem seqCompact_implies_closed_bounded
    (X : Set ℝ)
    (hSeq : IsSeqCompact X) :
    IsClosed X ∧ IsBoundedSet X := by

  have hCompact :
      IsCompact X := by
    exact
      (isCompact_iff_isSeqCompact).2 hSeq

  have hCB :
      IsClosed X ∧ Bornology.IsBounded X := by
    exact
      (Metric.isCompact_iff_isClosed_bounded).1
        hCompact

  constructor

  · exact hCB.1

  · exact
      tao_bounded_of_bornology_bounded
        X
        hCB.2


theorem theorem_9_1_24
    (X : Set ℝ) :
    (IsClosed X ∧ IsBoundedSet X)
      ↔
    IsSeqCompact X := by

  constructor

  · rintro ⟨hClosed, hBounded⟩

    exact
      closed_bounded_implies_seqCompact
        X
        hClosed
        hBounded

  · intro hSeq

    exact
      seqCompact_implies_closed_bounded
        X
        hSeq


theorem theorem_9_1_24_expanded
    (X : Set ℝ) :
    (IsClosed X ∧ IsBoundedSet X)
      ↔
    TaoSeqCompact X := by

  rw [← seqCompact_iff_tao_property X]

  exact theorem_9_1_24 X


theorem exercise_9_1_13
    (X : Set ℝ) :
    (IsClosed X ∧ IsBoundedSet X)
      ↔
    ∀ a : ℕ → ℝ,
      (∀ n : ℕ, a n ∈ X) →
      ∃ L : ℝ,
        L ∈ X ∧
        ∃ φ : ℕ → ℕ,
          StrictMono φ ∧
          Tendsto (a ∘ φ) atTop (𝓝 L) := by

  exact theorem_9_1_24_expanded X

end TaoExercise9_1_13
