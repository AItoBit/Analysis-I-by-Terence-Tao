import Mathlib

namespace TaoExercise9_5_1

/-!
============================================================
Limits equal to +∞ and -∞ within a subset E
============================================================
-/

/-- `f(x) → +∞` as `x → x₀`, with `x ∈ E`. -/
def TendsToPosInfWithin
    (E : Set ℝ)
    (f : E → ℝ)
    (x₀ : ℝ) : Prop :=
  ∀ A : ℝ,
    0 < A →
    ∃ δ : ℝ,
      0 < δ ∧
      ∀ x : E,
        abs ((x : ℝ) - x₀) < δ →
        A < f x


/-- `f(x) → -∞` as `x → x₀`, with `x ∈ E`. -/
def TendsToNegInfWithin
    (E : Set ℝ)
    (f : E → ℝ)
    (x₀ : ℝ) : Prop :=
  ∀ A : ℝ,
    0 < A →
    ∃ δ : ℝ,
      0 < δ ∧
      ∀ x : E,
        abs ((x : ℝ) - x₀) < δ →
        f x < -A


/-!
============================================================
One-sided infinite limits
============================================================
-/

/-- `f(x) → +∞` as `x → x₀⁺`. -/
def TendsToPosInfRight
    (E : Set ℝ)
    (f : E → ℝ)
    (x₀ : ℝ) : Prop :=
  ∀ A : ℝ,
    0 < A →
    ∃ δ : ℝ,
      0 < δ ∧
      ∀ x : E,
        x₀ < (x : ℝ) →
        (x : ℝ) < x₀ + δ →
        A < f x


/-- `f(x) → +∞` as `x → x₀⁻`. -/
def TendsToPosInfLeft
    (E : Set ℝ)
    (f : E → ℝ)
    (x₀ : ℝ) : Prop :=
  ∀ A : ℝ,
    0 < A →
    ∃ δ : ℝ,
      0 < δ ∧
      ∀ x : E,
        x₀ - δ < (x : ℝ) →
        (x : ℝ) < x₀ →
        A < f x


/-- `f(x) → -∞` as `x → x₀⁺`. -/
def TendsToNegInfRight
    (E : Set ℝ)
    (f : E → ℝ)
    (x₀ : ℝ) : Prop :=
  ∀ A : ℝ,
    0 < A →
    ∃ δ : ℝ,
      0 < δ ∧
      ∀ x : E,
        x₀ < (x : ℝ) →
        (x : ℝ) < x₀ + δ →
        f x < -A


/-- `f(x) → -∞` as `x → x₀⁻`. -/
def TendsToNegInfLeft
    (E : Set ℝ)
    (f : E → ℝ)
    (x₀ : ℝ) : Prop :=
  ∀ A : ℝ,
    0 < A →
    ∃ δ : ℝ,
      0 < δ ∧
      ∀ x : E,
        x₀ - δ < (x : ℝ) →
        (x : ℝ) < x₀ →
        f x < -A


/-!
============================================================
The domain ℝ \ {0}
============================================================
-/

def NonzeroReals : Set ℝ :=
  {x : ℝ | x ≠ 0}


/-- The reciprocal function on ℝ \ {0}. -/
noncomputable def reciprocal : NonzeroReals → ℝ :=
  fun x => 1 / (x : ℝ)


/-!
============================================================
A useful inequality

If A > 0 and

    0 < x < 1/(A+1),

then

    A < 1/x.
============================================================
-/

lemma reciprocal_large
    (A x : ℝ)
    (hA : 0 < A)
    (hxpos : 0 < x)
    (hxsmall : x < 1 / (A + 1)) :
    A < 1 / x := by

  have hA1 :
      0 < A + 1 := by
    linarith

  have hmul :
      x * (A + 1) < 1 := by
    exact (lt_div_iff₀ hA1).mp hxsmall

  have hAx :
      A * x < 1 := by
    nlinarith

  exact (lt_div_iff₀ hxpos).2 hAx


/-!
============================================================
lim_{x → 0⁺} 1/x = +∞
============================================================
-/

theorem reciprocal_tendsTo_posInf_right :
    TendsToPosInfRight
      NonzeroReals
      reciprocal
      0 := by

  intro A hA

  let δ : ℝ :=
    1 / (A + 1)

  have hA1 :
      0 < A + 1 := by
    linarith

  have hδ :
      0 < δ := by
    dsimp [δ]
    positivity

  refine ⟨δ, hδ, ?_⟩

  intro x hxpos hxδ

  have hxpos' :
      0 < (x : ℝ) := by
    exact hxpos

  have hxsmall :
      (x : ℝ) < 1 / (A + 1) := by
    dsimp [δ] at hxδ
    simpa using hxδ

  change A < 1 / (x : ℝ)

  exact reciprocal_large
    A
    (x : ℝ)
    hA
    hxpos'
    hxsmall


/-!
============================================================
lim_{x → 0⁻} 1/x = -∞
============================================================
-/

theorem reciprocal_tendsTo_negInf_left :
    TendsToNegInfLeft
      NonzeroReals
      reciprocal
      0 := by

  intro A hA

  let δ : ℝ :=
    1 / (A + 1)

  have hA1 :
      0 < A + 1 := by
    linarith

  have hδ :
      0 < δ := by
    dsimp [δ]
    positivity

  refine ⟨δ, hδ, ?_⟩

  intro x hxLower hxNeg

  have hxNeg' :
      (x : ℝ) < 0 := by
    exact hxNeg

  have hNegXPos :
      0 < -(x : ℝ) := by
    linarith

  have hNegXSmall :
      -(x : ℝ) < 1 / (A + 1) := by
    dsimp [δ] at hxLower
    linarith

  have hLarge :
      A < 1 / (-(x : ℝ)) := by
    exact reciprocal_large
      A
      (-(x : ℝ))
      hA
      hNegXPos
      hNegXSmall

  change 1 / (x : ℝ) < -A

  have hInvNeg :
      1 / (-(x : ℝ)) = -(1 / (x : ℝ)) := by
    ring

  rw [hInvNeg] at hLarge

  linarith


/-!
============================================================
Exercise 9.5.1
============================================================
-/

theorem exercise_9_5_1 :
    TendsToPosInfRight
        NonzeroReals
        reciprocal
        0
      ∧
    TendsToNegInfLeft
        NonzeroReals
        reciprocal
        0 := by

  constructor

  · exact reciprocal_tendsTo_posInf_right

  · exact reciprocal_tendsTo_negInf_left

end TaoExercise9_5_1
