import Mathlib

namespace TaoExercises10_3

open Set

/-!
============================================================
Derivative in the sense used in Tao
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


def DifferentiableAtTao
    (X : Set ℝ)
    (f : X → ℝ)
    (x₀ : X) : Prop :=
  ∃ L : ℝ,
    HasDerivativeAtTao X f x₀ L


/-!
A sequential/epsilon formulation sufficient for saying that x₀
is a limit point of X.
-/

def IsLimitPointTao
    (X : Set ℝ)
    (x₀ : X) : Prop :=
  ∀ δ : ℝ,
    0 < δ →
    ∃ x : X,
      x ≠ x₀ ∧
      abs ((x : ℝ) - (x₀ : ℝ)) ≤ δ


/-!
============================================================
Exercise 10.3.1 / Proposition 10.3.1

Monotone increasing -> derivative ≥ 0.
============================================================
-/

theorem monotone_derivative_nonneg
    (X : Set ℝ)
    (f : X → ℝ)
    (x₀ : X)
    (L : ℝ)
    (hlim : IsLimitPointTao X x₀)
    (hmono : Monotone f)
    (hderiv : HasDerivativeAtTao X f x₀ L) :
    0 ≤ L := by

  by_contra hL

  have hLneg :
      L < 0 := by
    exact lt_of_not_ge hL

  have hε :
      0 < -L / 2 := by
    linarith

  obtain ⟨δ, hδ, hmain⟩ :=
    hderiv (-L / 2) hε

  obtain ⟨x, hxne, hxδ⟩ :=
    hlim δ hδ

  have hrealne :
      (x : ℝ) ≠ (x₀ : ℝ) := by
    intro h
    apply hxne
    exact Subtype.ext h

  have hquotNonneg :
      0 ≤
        (f x - f x₀) /
          ((x : ℝ) - (x₀ : ℝ)) := by

    rcases lt_trichotomy
      (x : ℝ)
      (x₀ : ℝ) with hlt | heq | hgt

    · have hxx₀ :
          x ≤ x₀ := by
        exact le_of_lt hlt

      have hf_le :
          f x ≤ f x₀ := by
        exact hmono hxx₀

      have hnum :
          f x - f x₀ ≤ 0 := by
        linarith

      have hden :
          (x : ℝ) - (x₀ : ℝ) ≤ 0 := by
        linarith

      exact div_nonneg_of_nonpos_of_nonpos
        hnum
        hden

    · exact (hrealne heq).elim

    · have hx₀x :
          x₀ ≤ x := by
        exact le_of_lt hgt

      have hf_ge :
          f x₀ ≤ f x := by
        exact hmono hx₀x

      have hnum :
          0 ≤ f x - f x₀ := by
        linarith

      have hden :
          0 ≤ (x : ℝ) - (x₀ : ℝ) := by
        linarith

      exact div_nonneg hnum hden

  have hclose :
      abs
          ((f x - f x₀) /
              ((x : ℝ) - (x₀ : ℝ)) -
            L) ≤
        -L / 2 := by

    exact hmain
      x
      hxne
      hxδ

  have hupper :
      (f x - f x₀) /
            ((x : ℝ) - (x₀ : ℝ)) -
          L
        ≤ -L / 2 := by

    exact (abs_le.mp hclose).2

  linarith


/-!
============================================================
Monotone decreasing -> derivative ≤ 0.
============================================================
-/

theorem antitone_derivative_nonpos
    (X : Set ℝ)
    (f : X → ℝ)
    (x₀ : X)
    (L : ℝ)
    (hlim : IsLimitPointTao X x₀)
    (hanti : Antitone f)
    (hderiv : HasDerivativeAtTao X f x₀ L) :
    L ≤ 0 := by

  by_contra hL

  have hLpos :
      0 < L := by
    exact lt_of_not_ge hL

  have hε :
      0 < L / 2 := by
    linarith

  obtain ⟨δ, hδ, hmain⟩ :=
    hderiv (L / 2) hε

  obtain ⟨x, hxne, hxδ⟩ :=
    hlim δ hδ

  have hrealne :
      (x : ℝ) ≠ (x₀ : ℝ) := by
    intro h
    apply hxne
    exact Subtype.ext h

  have hquotNonpos :
      (f x - f x₀) /
          ((x : ℝ) - (x₀ : ℝ))
        ≤ 0 := by

    rcases lt_trichotomy
      (x : ℝ)
      (x₀ : ℝ) with hlt | heq | hgt

    · have hxx₀ :
          x ≤ x₀ := le_of_lt hlt

      have hf_ge :
          f x₀ ≤ f x := by
        exact hanti hxx₀

      have hnum :
          0 ≤ f x - f x₀ := by
        linarith

      have hden :
          (x : ℝ) - (x₀ : ℝ) ≤ 0 := by
        linarith

      exact div_nonpos_of_nonneg_of_nonpos
        hnum
        hden

    · exact (hrealne heq).elim

    · have hx₀x :
          x₀ ≤ x := le_of_lt hgt

      have hf_le :
          f x ≤ f x₀ := by
        exact hanti hx₀x

      have hnum :
          f x - f x₀ ≤ 0 := by
        linarith

      have hden :
          0 ≤ (x : ℝ) - (x₀ : ℝ) := by
        linarith

      exact div_nonpos_of_nonpos_of_nonneg
        hnum
        hden

  have hclose :
      abs
          ((f x - f x₀) /
              ((x : ℝ) - (x₀ : ℝ)) -
            L) ≤
        L / 2 := by

    exact hmain
      x
      hxne
      hxδ

  have hlower :
      -(L / 2) ≤
        (f x - f x₀) /
            ((x : ℝ) - (x₀ : ℝ)) -
          L := by

    exact (abs_le.mp hclose).1

  linarith


theorem exercise_10_3_1
    (X : Set ℝ)
    (f : X → ℝ)
    (x₀ : X)
    (L : ℝ)
    (hlim : IsLimitPointTao X x₀)
    (hderiv : HasDerivativeAtTao X f x₀ L) :
    (Monotone f → 0 ≤ L) ∧
    (Antitone f → L ≤ 0) := by

  constructor

  · intro hmono
    exact monotone_derivative_nonneg
      X f x₀ L hlim hmono hderiv

  · intro hanti
    exact antitone_derivative_nonpos
      X f x₀ L hlim hanti hderiv


/-!
============================================================
Exercise 10.3.2

The example is

       F(x) = x + max x 0.

Thus

       F(x) = x    for x ≤ 0
       F(x) = 2x   for x ≥ 0.
============================================================
-/

def F (x : ℝ) : ℝ :=
  x + max x 0


def f :
    Set.Ioo (-1 : ℝ) 1 → ℝ :=
  fun x => F (x : ℝ)


def zeroPoint :
    Set.Ioo (-1 : ℝ) 1 :=
  ⟨0, by
    constructor <;> norm_num⟩


/-!
It is exactly Tao's piecewise function.
-/

theorem F_of_nonpos
    {x : ℝ}
    (hx : x ≤ 0) :
    F x = x := by

  unfold F

  rw [max_eq_right hx]

  ring


theorem F_of_nonneg
    {x : ℝ}
    (hx : 0 ≤ x) :
    F x = 2 * x := by

  unfold F

  rw [max_eq_left hx]

  ring


/-!
============================================================
Continuity
============================================================
-/

theorem F_continuous :
    Continuous F := by

  unfold F

  fun_prop


theorem f_continuous :
    Continuous f := by

  unfold f

  fun_prop


/-!
============================================================
Monotonicity
============================================================
-/

theorem F_monotone :
    Monotone F := by

  intro x y hxy

  unfold F

  exact add_le_add
    hxy
    (max_le_max hxy le_rfl)


theorem f_monotone :
    Monotone f := by

  intro x y hxy

  exact F_monotone hxy


/-!
============================================================
Difference quotients at zero
============================================================
-/

lemma left_difference_quotient
    {x : ℝ}
    (hx : x < 0) :
    (F x - F 0) / (x - 0) = 1 := by

  have hx0 :
      x ≠ 0 := ne_of_lt hx

  have hxnonpos :
      x ≤ 0 := le_of_lt hx

  rw [F_of_nonpos hxnonpos]

  have hF0 :
      F 0 = 0 := by
    norm_num [F]

  rw [hF0]

  field_simp [hx0]


lemma right_difference_quotient
    {x : ℝ}
    (hx : 0 < x) :
    (F x - F 0) / (x - 0) = 2 := by

  have hx0 :
      x ≠ 0 := ne_of_gt hx

  have hxnonneg :
      0 ≤ x := le_of_lt hx

  rw [F_of_nonneg hxnonneg]

  have hF0 :
      F 0 = 0 := by
    norm_num [F]

  rw [hF0]

  field_simp [hx0]


/-!
A Tao-style derivative definition on ℝ.
-/

def HasDerivativeRealTao
    (F : ℝ → ℝ)
    (x₀ L : ℝ) : Prop :=
  ∀ ε : ℝ,
    0 < ε →
    ∃ δ : ℝ,
      0 < δ ∧
      ∀ x : ℝ,
        x ≠ x₀ →
        abs (x - x₀) ≤ δ →
        abs
            ((F x - F x₀) / (x - x₀) - L) ≤ ε


def DifferentiableRealTao
    (F : ℝ → ℝ)
    (x₀ : ℝ) : Prop :=
  ∃ L : ℝ,
    HasDerivativeRealTao F x₀ L


/-!
============================================================
F is not differentiable at zero.

The left quotient is 1 and the right quotient is 2.
============================================================
-/

theorem F_not_differentiable_at_zero :
    ¬ DifferentiableRealTao F 0 := by

  intro hdiff

  obtain ⟨L, hL⟩ := hdiff

  obtain ⟨δ, hδ, hmain⟩ :=
    hL (1 / 4 : ℝ) (by norm_num)

  let t : ℝ := δ / 2

  have htpos :
      0 < t := by
    dsimp [t]
    linarith

  have htne :
      t ≠ 0 := ne_of_gt htpos

  have htBound :
      abs (t - 0) ≤ δ := by

    rw [sub_zero, abs_of_pos htpos]

    dsimp [t]

    linarith

  have hright :=
    hmain t htne htBound

  have hrightQ :
      (F t - F 0) / (t - 0) = 2 := by
    exact right_difference_quotient htpos

  rw [hrightQ] at hright

  let s : ℝ := -t

  have hsneg :
      s < 0 := by
    dsimp [s]
    linarith

  have hsne :
      s ≠ 0 := ne_of_lt hsneg

  have hsBound :
      abs (s - 0) ≤ δ := by

    rw [sub_zero]

    have hsabs :
        abs s = t := by
      dsimp [s]
      rw [abs_neg, abs_of_pos htpos]

    rw [hsabs]

    dsimp [t]

    linarith

  have hleft :=
    hmain s hsne hsBound

  have hleftQ :
      (F s - F 0) / (s - 0) = 1 := by
    exact left_difference_quotient hsneg

  rw [hleftQ] at hleft

  have hrBounds :
      -(1 / 4 : ℝ) ≤ (2 : ℝ) - L ∧
        (2 : ℝ) - L ≤ (1 / 4 : ℝ) := by
    exact abs_le.mp hright

  have hlBounds :
      -(1 / 4 : ℝ) ≤ (1 : ℝ) - L ∧
        (1 : ℝ) - L ≤ (1 / 4 : ℝ) := by
    exact abs_le.mp hleft

  rcases hrBounds with ⟨hrLow, hrHigh⟩
  rcases hlBounds with ⟨hlLow, hlHigh⟩

  linarith


/-!
============================================================
Exercise 10.3.2
============================================================
-/

theorem exercise_10_3_2 :
    Continuous f
      ∧
    Monotone f
      ∧
    ¬ DifferentiableRealTao F 0 := by

  exact
    ⟨f_continuous,
     f_monotone,
     F_not_differentiable_at_zero⟩

end TaoExercises10_3
