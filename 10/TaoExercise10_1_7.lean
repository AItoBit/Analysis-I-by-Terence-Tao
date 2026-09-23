import Mathlib

namespace TaoExercise10_1_7

/-!
============================================================
Derivative with prescribed value
============================================================
-/

def HasDerivativeAtTao
    (X : Set ℝ)
    (f : X → ℝ)
    (x₀ : X)
    (L : ℝ) : Prop :=
  ∀ ε : ℝ,
    0 < ε →
    ∃ δ : ℝ,
      0 < δ ∧
      ∀ x : X,
        x ≠ x₀ →
        abs ((x : ℝ) - (x₀ : ℝ)) ≤ δ →
        abs
            ((f x - f x₀) /
                ((x : ℝ) - (x₀ : ℝ)) -
              L) ≤ ε


/-!
============================================================
Newton approximation
============================================================
-/

def HasLinearApproximation
    (X : Set ℝ)
    (f : X → ℝ)
    (x₀ : X)
    (L : ℝ) : Prop :=
  ∀ ε : ℝ,
    0 < ε →
    ∃ δ : ℝ,
      0 < δ ∧
      ∀ x : X,
        abs ((x : ℝ) - (x₀ : ℝ)) ≤ δ →
        abs
            (f x - f x₀ -
              L * ((x : ℝ) - (x₀ : ℝ))) ≤
          ε * abs ((x : ℝ) - (x₀ : ℝ))


/-!
============================================================
Algebra
============================================================
-/

lemma linear_error_factorization
    (A L h : ℝ)
    (hh : h ≠ 0) :
    A - L * h =
      h * (A / h - L) := by
  field_simp [hh]


lemma quotient_error_factorization
    (A L h : ℝ)
    (hh : h ≠ 0) :
    A / h - L =
      (A - L * h) / h := by
  field_simp [hh]


/-!
============================================================
Proposition 10.1.7
Derivative -> Newton approximation
============================================================
-/

theorem derivative_implies_linear_approximation
    (X : Set ℝ)
    (f : X → ℝ)
    (x₀ : X)
    (L : ℝ)
    (hf : HasDerivativeAtTao X f x₀ L) :
    HasLinearApproximation X f x₀ L := by

  intro ε hε

  obtain ⟨δ, hδ, hmain⟩ :=
    hf ε hε

  refine ⟨δ, hδ, ?_⟩

  intro x hxδ

  by_cases hxx₀ : x = x₀

  · subst x
    norm_num

  · have hsubne :
        (x : ℝ) - (x₀ : ℝ) ≠ 0 := by
      intro hzero

      have hval :
          (x : ℝ) = (x₀ : ℝ) := by
        exact sub_eq_zero.mp hzero

      apply hxx₀
      exact Subtype.ext hval

    have hquot :
        abs
            ((f x - f x₀) /
                ((x : ℝ) - (x₀ : ℝ)) -
              L) ≤ ε := by
      exact hmain x hxx₀ hxδ

    have hfactor :
        f x - f x₀ -
            L * ((x : ℝ) - (x₀ : ℝ))
          =
        ((x : ℝ) - (x₀ : ℝ)) *
          ((f x - f x₀) /
              ((x : ℝ) - (x₀ : ℝ)) -
            L) := by

      exact linear_error_factorization
        (f x - f x₀)
        L
        ((x : ℝ) - (x₀ : ℝ))
        hsubne

    rw [hfactor, abs_mul]

    have hmul :
        abs ((x : ℝ) - (x₀ : ℝ)) *
            abs
              ((f x - f x₀) /
                  ((x : ℝ) - (x₀ : ℝ)) -
                L)
          ≤
        abs ((x : ℝ) - (x₀ : ℝ)) * ε := by

      exact mul_le_mul_of_nonneg_left
        hquot
        (abs_nonneg _)

    simpa [mul_comm] using hmul


/-!
============================================================
Proposition 10.1.7
Newton approximation -> derivative
============================================================
-/

theorem linear_approximation_implies_derivative
    (X : Set ℝ)
    (f : X → ℝ)
    (x₀ : X)
    (L : ℝ)
    (hf : HasLinearApproximation X f x₀ L) :
    HasDerivativeAtTao X f x₀ L := by

  intro ε hε

  obtain ⟨δ, hδ, hmain⟩ :=
    hf ε hε

  refine ⟨δ, hδ, ?_⟩

  intro x hxx₀ hxδ

  have hsubne :
      (x : ℝ) - (x₀ : ℝ) ≠ 0 := by
    intro hzero

    have hval :
        (x : ℝ) = (x₀ : ℝ) := by
      exact sub_eq_zero.mp hzero

    apply hxx₀
    exact Subtype.ext hval

  have habspos :
      0 < abs ((x : ℝ) - (x₀ : ℝ)) := by
    exact abs_pos.mpr hsubne

  have hlinear :
      abs
          (f x - f x₀ -
            L * ((x : ℝ) - (x₀ : ℝ))) ≤
        ε * abs ((x : ℝ) - (x₀ : ℝ)) := by
    exact hmain x hxδ

  have hfactor :
      (f x - f x₀) /
            ((x : ℝ) - (x₀ : ℝ)) -
          L
        =
      (f x - f x₀ -
          L * ((x : ℝ) - (x₀ : ℝ))) /
        ((x : ℝ) - (x₀ : ℝ)) := by

    exact quotient_error_factorization
      (f x - f x₀)
      L
      ((x : ℝ) - (x₀ : ℝ))
      hsubne

  rw [hfactor, abs_div]

  apply (div_le_iff₀ habspos).2

  simpa [mul_comm] using hlinear


/-!
============================================================
Newton approximation chain rule
============================================================
-/

theorem linear_approximation_chain
    (X Y : Set ℝ)
    (f : X → Y)
    (g : Y → ℝ)
    (x₀ : X)
    (L₁ L₂ : ℝ)
    (hf :
      HasLinearApproximation
        X
        (fun x => (f x : ℝ))
        x₀
        L₁)
    (hg :
      HasLinearApproximation
        Y
        g
        (f x₀)
        L₂) :
    HasLinearApproximation
      X
      (fun x => g (f x))
      x₀
      (L₂ * L₁) := by

  intro ε hε

  /-
  C = |L₁| + |L₂| + 1 > 0.
  -/

  let C : ℝ :=
    abs L₁ + abs L₂ + 1

  have hCpos :
      0 < C := by
    dsimp [C]

    have h₁ :
        0 ≤ abs L₁ := abs_nonneg L₁

    have h₂ :
        0 ≤ abs L₂ := abs_nonneg L₂

    linarith

  /-
  Choose η small enough so that

      η (η + |L₁| + |L₂|) ≤ ε.
  -/

  let η : ℝ :=
    min 1 (ε / (2 * C))

  have hTwoCpos :
      0 < 2 * C := by
    positivity

  have hFracPos :
      0 < ε / (2 * C) := by
    exact div_pos hε hTwoCpos

  have hη :
      0 < η := by
    dsimp [η]
    exact lt_min zero_lt_one hFracPos

  have hηone :
      η ≤ 1 := by
    dsimp [η]
    exact min_le_left _ _

  have hηfrac :
      η ≤ ε / (2 * C) := by
    dsimp [η]
    exact min_le_right _ _

  have hηTwoC :
      η * (2 * C) ≤ ε := by
    exact (le_div_iff₀ hTwoCpos).mp hηfrac

  have hCoeffLe :
      η + abs L₁ + abs L₂ ≤ C := by
    dsimp [C]
    linarith

  have hηCoeff :
      η * (η + abs L₁ + abs L₂)
        ≤ η * C := by

    exact mul_le_mul_of_nonneg_left
      hCoeffLe
      (le_of_lt hη)

  have hηC :
      η * C ≤ ε := by

    have hnonneg :
        0 ≤ η * C := by
      exact mul_nonneg
        (le_of_lt hη)
        (le_of_lt hCpos)

    nlinarith [hηTwoC]

  have hηFinal :
      η * (η + abs L₁ + abs L₂) ≤ ε := by
    exact le_trans hηCoeff hηC

  /-
  Newton approximations for f and g.
  -/

  obtain ⟨δf, hδf, hfApprox⟩ :=
    hf η hη

  obtain ⟨δg, hδg, hgApprox⟩ :=
    hg η hη

  /-
  B controls the size of f(x)-f(x₀).
  -/

  let B : ℝ :=
    abs L₁ + η + 1

  have hBpos :
      0 < B := by
    dsimp [B]

    have h₁ :
        0 ≤ abs L₁ := abs_nonneg L₁

    linarith

  have hδgDiv :
      0 < δg / B := by
    exact div_pos hδg hBpos

  let δ : ℝ :=
    min δf (δg / B)

  have hδ :
      0 < δ := by
    dsimp [δ]
    exact lt_min hδf hδgDiv

  refine ⟨δ, hδ, ?_⟩

  intro x hxδ

  have hxδf :
      abs ((x : ℝ) - (x₀ : ℝ)) ≤ δf := by

    have h :
        δ ≤ δf := by
      dsimp [δ]
      exact min_le_left _ _

    exact le_trans hxδ h

  have hxδg :
      abs ((x : ℝ) - (x₀ : ℝ)) ≤ δg / B := by

    have h :
        δ ≤ δg / B := by
      dsimp [δ]
      exact min_le_right _ _

    exact le_trans hxδ h

  /-
  Error for f.
  -/

  have hfError :
      abs
          ((f x : ℝ) - (f x₀ : ℝ) -
            L₁ * ((x : ℝ) - (x₀ : ℝ))) ≤
        η * abs ((x : ℝ) - (x₀ : ℝ)) := by

    exact hfApprox x hxδf

  /-
  Bound the actual displacement of f.
  -/

  let A : ℝ :=
    (f x : ℝ) - (f x₀ : ℝ) -
      L₁ * ((x : ℝ) - (x₀ : ℝ))

  let D : ℝ :=
    L₁ * ((x : ℝ) - (x₀ : ℝ))

  have hdecomp :
      (f x : ℝ) - (f x₀ : ℝ) =
        A + D := by
    dsimp [A, D]
    ring

  have htriangleF :
      abs ((f x : ℝ) - (f x₀ : ℝ))
        ≤ abs A + abs D := by

    rw [hdecomp]

    simpa only using (abs_add_le A D)

  have hA :
      abs A ≤
        η * abs ((x : ℝ) - (x₀ : ℝ)) := by
    exact hfError

  have hD :
      abs D =
        abs L₁ *
          abs ((x : ℝ) - (x₀ : ℝ)) := by
    dsimp [D]
    exact abs_mul _ _

  have hsum :
      abs A + abs D
        ≤
      η * abs ((x : ℝ) - (x₀ : ℝ)) +
        abs L₁ * abs ((x : ℝ) - (x₀ : ℝ)) := by

    apply add_le_add

    · exact hA

    · rw [hD]

  have hfDistance :
      abs ((f x : ℝ) - (f x₀ : ℝ))
        ≤
      (abs L₁ + η) *
        abs ((x : ℝ) - (x₀ : ℝ)) := by

    calc
      abs ((f x : ℝ) - (f x₀ : ℝ))
          ≤ abs A + abs D := htriangleF

      _ ≤
          η * abs ((x : ℝ) - (x₀ : ℝ)) +
            abs L₁ *
              abs ((x : ℝ) - (x₀ : ℝ)) := hsum

      _ =
          (abs L₁ + η) *
            abs ((x : ℝ) - (x₀ : ℝ)) := by
        ring

  /-
  Show that f(x) is within δg of f(x₀).
  -/

  have hCoeffB :
      abs L₁ + η ≤ B := by
    dsimp [B]
    linarith

  have hCoeffNonneg :
      0 ≤ abs L₁ + η := by

    have h₁ :
        0 ≤ abs L₁ := abs_nonneg L₁

    have h₂ :
        0 ≤ η := le_of_lt hη

    linarith

  have hStep1 :
      (abs L₁ + η) *
          abs ((x : ℝ) - (x₀ : ℝ))
        ≤
      (abs L₁ + η) * (δg / B) := by

    exact mul_le_mul_of_nonneg_left
      hxδg
      hCoeffNonneg

  have hDivNonneg :
      0 ≤ δg / B := by
    exact le_of_lt hδgDiv

  have hStep2 :
      (abs L₁ + η) * (δg / B)
        ≤ B * (δg / B) := by

    exact mul_le_mul_of_nonneg_right
      hCoeffB
      hDivNonneg

  have hCancel :
      B * (δg / B) = δg := by
    field_simp [ne_of_gt hBpos]

  have hfClose :
      abs ((f x : ℝ) - (f x₀ : ℝ)) ≤ δg := by

    calc
      abs ((f x : ℝ) - (f x₀ : ℝ))
          ≤
        (abs L₁ + η) *
          abs ((x : ℝ) - (x₀ : ℝ)) :=
        hfDistance

      _ ≤
        (abs L₁ + η) * (δg / B) :=
        hStep1

      _ ≤
        B * (δg / B) :=
        hStep2

      _ = δg := hCancel

  /-
  Apply Newton approximation for g.
  -/

  have hgError :
      abs
          (g (f x) - g (f x₀) -
            L₂ * ((f x : ℝ) - (f x₀ : ℝ))) ≤
        η *
          abs ((f x : ℝ) - (f x₀ : ℝ)) := by

    exact hgApprox (f x) hfClose

  /-
  Middle-man trick.
  -/

  let P : ℝ :=
    g (f x) - g (f x₀) -
      L₂ * ((f x : ℝ) - (f x₀ : ℝ))

  let Q : ℝ :=
    L₂ *
      ((f x : ℝ) - (f x₀ : ℝ) -
        L₁ * ((x : ℝ) - (x₀ : ℝ)))

  have hMiddle :
      g (f x) - g (f x₀) -
          (L₂ * L₁) *
            ((x : ℝ) - (x₀ : ℝ))
        =
      P + Q := by

    dsimp [P, Q]

    ring

  have htriangle :
      abs (P + Q) ≤ abs P + abs Q := by
    simpa only using (abs_add_le P Q)

  have hP :
      abs P ≤
        η *
          abs ((f x : ℝ) - (f x₀ : ℝ)) := by

    exact hgError

  have hQ :
      abs Q ≤
        abs L₂ *
          (η *
            abs ((x : ℝ) - (x₀ : ℝ))) := by

    dsimp [Q]

    rw [abs_mul]

    exact mul_le_mul_of_nonneg_left
      hfError
      (abs_nonneg L₂)

  have hPQ :
      abs P + abs Q
        ≤
      η *
          abs ((f x : ℝ) - (f x₀ : ℝ)) +
        abs L₂ *
          (η *
            abs ((x : ℝ) - (x₀ : ℝ))) := by

    exact add_le_add hP hQ

  have hEtaDistance :
      η *
          abs ((f x : ℝ) - (f x₀ : ℝ))
        ≤
      η *
        ((abs L₁ + η) *
          abs ((x : ℝ) - (x₀ : ℝ))) := by

    exact mul_le_mul_of_nonneg_left
      hfDistance
      (le_of_lt hη)

  have hMain :
      abs
          (g (f x) - g (f x₀) -
            (L₂ * L₁) *
              ((x : ℝ) - (x₀ : ℝ)))
        ≤
      η * (η + abs L₁ + abs L₂) *
        abs ((x : ℝ) - (x₀ : ℝ)) := by

    rw [hMiddle]

    calc
      abs (P + Q)
          ≤ abs P + abs Q :=
        htriangle

      _ ≤
          η *
              abs ((f x : ℝ) - (f x₀ : ℝ)) +
            abs L₂ *
              (η *
                abs ((x : ℝ) - (x₀ : ℝ))) :=
        hPQ

      _ ≤
          η *
              ((abs L₁ + η) *
                abs ((x : ℝ) - (x₀ : ℝ))) +
            abs L₂ *
              (η *
                abs ((x : ℝ) - (x₀ : ℝ))) := by

        apply add_le_add

        · exact hEtaDistance

        · exact le_rfl

      _ =
          η * (η + abs L₁ + abs L₂) *
            abs ((x : ℝ) - (x₀ : ℝ)) := by
        ring

  have hFinal :
      η * (η + abs L₁ + abs L₂) *
          abs ((x : ℝ) - (x₀ : ℝ))
        ≤
      ε * abs ((x : ℝ) - (x₀ : ℝ)) := by

    exact mul_le_mul_of_nonneg_right
      hηFinal
      (abs_nonneg _)

  exact le_trans hMain hFinal


/-!
============================================================
Theorem 10.1.5 — Chain rule
============================================================
-/

theorem theorem_10_1_5
    (X Y : Set ℝ)
    (f : X → Y)
    (g : Y → ℝ)
    (x₀ : X)
    (y₀ : Y)
    (L₁ L₂ : ℝ)
    (hxy : f x₀ = y₀)
    (hf :
      HasDerivativeAtTao
        X
        (fun x => (f x : ℝ))
        x₀
        L₁)
    (hg :
      HasDerivativeAtTao
        Y
        g
        y₀
        L₂) :
    HasDerivativeAtTao
      X
      (fun x => g (f x))
      x₀
      (L₂ * L₁) := by

  subst y₀

  have hfLinear :
      HasLinearApproximation
        X
        (fun x => (f x : ℝ))
        x₀
        L₁ := by

    exact derivative_implies_linear_approximation
      X
      (fun x => (f x : ℝ))
      x₀
      L₁
      hf

  have hgLinear :
      HasLinearApproximation
        Y
        g
        (f x₀)
        L₂ := by

    exact derivative_implies_linear_approximation
      Y
      g
      (f x₀)
      L₂
      hg

  have hcomp :
      HasLinearApproximation
        X
        (fun x => g (f x))
        x₀
        (L₂ * L₁) := by

    exact linear_approximation_chain
      X
      Y
      f
      g
      x₀
      L₁
      L₂
      hfLinear
      hgLinear

  exact linear_approximation_implies_derivative
    X
    (fun x => g (f x))
    x₀
    (L₂ * L₁)
    hcomp


/-!
============================================================
Exercise 10.1.7
============================================================
-/

theorem exercise_10_1_7
    (X Y : Set ℝ)
    (f : X → Y)
    (g : Y → ℝ)
    (x₀ : X)
    (y₀ : Y)
    (L₁ L₂ : ℝ)
    (hxy : f x₀ = y₀)
    (hf :
      HasDerivativeAtTao
        X
        (fun x => (f x : ℝ))
        x₀
        L₁)
    (hg :
      HasDerivativeAtTao
        Y
        g
        y₀
        L₂) :
    HasDerivativeAtTao
      X
      (fun x => g (f x))
      x₀
      (L₂ * L₁) := by

  exact theorem_10_1_5
    X
    Y
    f
    g
    x₀
    y₀
    L₁
    L₂
    hxy
    hf
    hg

end TaoExercise10_1_7
