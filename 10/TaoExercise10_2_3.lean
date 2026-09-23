import Mathlib

namespace TaoExercise10_2_3

open Set

def F (x : ℝ) : ℝ :=
  x ^ 3


def f :
    Set.Ioo (-1 : ℝ) 1 → ℝ :=
  fun x => F (x : ℝ)


theorem F_hasDerivAt
    (x : ℝ) :
    HasDerivAt F (3 * x ^ 2) x := by

  unfold F

  change
    HasDerivAt
      (id ^ (3 : ℕ))
      (3 * x ^ 2)
      x

  simpa using (hasDerivAt_id x).pow 3


theorem F_differentiable :
    Differentiable ℝ F := by

  intro x

  exact (F_hasDerivAt x).differentiableAt


theorem F_differentiableOn :
    DifferentiableOn ℝ F (Set.Ioo (-1 : ℝ) 1) := by

  intro x hx

  exact
    (F_hasDerivAt x).differentiableAt.differentiableWithinAt


theorem F_deriv_zero :
    deriv F 0 = 0 := by

  have h :=
    (F_hasDerivAt 0).deriv

  norm_num at h ⊢

  exact h


def HasLocalMaximumAtZero : Prop :=
  ∃ δ : ℝ,
    0 < δ ∧
    ∀ x : ℝ,
      x ∈ Set.Ioo (-1 : ℝ) 1 →
      abs x < δ →
      F x ≤ F 0


def HasLocalMinimumAtZero : Prop :=
  ∃ δ : ℝ,
    0 < δ ∧
    ∀ x : ℝ,
      x ∈ Set.Ioo (-1 : ℝ) 1 →
      abs x < δ →
      F 0 ≤ F x


lemma exists_small_positive
    {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ t : ℝ,
      0 < t ∧
      t < δ ∧
      t < 1 := by

  let t : ℝ :=
    min (δ / 2) (1 / 2 : ℝ)

  have hδhalf :
      0 < δ / 2 := by
    linarith

  have hhalf :
      0 < (1 / 2 : ℝ) := by
    norm_num

  have htPos :
      0 < t := by
    dsimp [t]
    exact lt_min hδhalf hhalf

  have htδhalf :
      t ≤ δ / 2 := by
    dsimp [t]
    exact min_le_left _ _

  have htHalf :
      t ≤ (1 / 2 : ℝ) := by
    dsimp [t]
    exact min_le_right _ _

  have htδ :
      t < δ := by
    linarith

  have htOne :
      t < 1 := by
    linarith

  exact ⟨t, htPos, htδ, htOne⟩


theorem zero_not_localMaximum :
    ¬ HasLocalMaximumAtZero := by

  intro hmax

  obtain ⟨δ, hδ, hmaxδ⟩ := hmax

  obtain ⟨t, htPos, htδ, htOne⟩ :=
    exists_small_positive hδ

  have htMem :
      t ∈ Set.Ioo (-1 : ℝ) 1 := by

    constructor

    · linarith

    · exact htOne

  have htAbs :
      abs t < δ := by

    rw [abs_of_pos htPos]

    exact htδ

  have hle :
      F t ≤ F 0 := by

    exact hmaxδ
      t
      htMem
      htAbs

  unfold F at hle

  have htSquarePos :
      0 < t * t := by
    exact mul_pos htPos htPos

  have htCube :
      0 < t ^ 3 := by

    calc
      0 < (t * t) * t := by
        exact mul_pos htSquarePos htPos
      _ = t ^ 3 := by
        ring

  norm_num at hle

  linarith


theorem zero_not_localMinimum :
    ¬ HasLocalMinimumAtZero := by

  intro hmin

  obtain ⟨δ, hδ, hminδ⟩ := hmin

  obtain ⟨t, htPos, htδ, htOne⟩ :=
    exists_small_positive hδ

  let y : ℝ := -t

  have hyMem :
      y ∈ Set.Ioo (-1 : ℝ) 1 := by

    dsimp [y]

    constructor

    · linarith

    · linarith

  have hyNeg :
      y < 0 := by

    dsimp [y]

    linarith

  have hyAbs :
      abs y < δ := by

    have habs :
        abs y = t := by

      dsimp [y]

      rw [abs_neg, abs_of_pos htPos]

    rw [habs]

    exact htδ

  have hle :
      F 0 ≤ F y := by

    exact hminδ
      y
      hyMem
      hyAbs

  unfold F at hle

  have hySquarePos :
      0 < y * y := by

    exact mul_pos_of_neg_of_neg
      hyNeg
      hyNeg

  have hyCube :
      y ^ 3 < 0 := by

    calc
      y ^ 3 = (y * y) * y := by
        ring

      _ < 0 := by
        exact mul_neg_of_pos_of_neg
          hySquarePos
          hyNeg

  norm_num at hle

  linarith


theorem zero_not_local_extremum :
    ¬ HasLocalMaximumAtZero ∧
    ¬ HasLocalMinimumAtZero := by

  exact
    ⟨zero_not_localMaximum,
     zero_not_localMinimum⟩


theorem exercise_10_2_3 :
    DifferentiableOn ℝ F (Set.Ioo (-1 : ℝ) 1)
      ∧
    deriv F 0 = 0
      ∧
    ¬ HasLocalMaximumAtZero
      ∧
    ¬ HasLocalMinimumAtZero := by

  exact
    ⟨F_differentiableOn,
     F_deriv_zero,
     zero_not_localMaximum,
     zero_not_localMinimum⟩

end TaoExercise10_2_3
