import Mathlib

namespace TaoExercise11_3_2

open Set

/-!
============================================================
Majorization on a set I
============================================================
-/

def Majorizes
    (I : Set ℝ)
    (f g : ℝ → ℝ) : Prop :=
  ∀ x ∈ I,
    g x ≤ f x


/-!
============================================================
Addition preserves majorization
============================================================
-/

theorem majorizes_add
    (I : Set ℝ)
    (f g h : ℝ → ℝ)
    (hfg : Majorizes I f g) :
    Majorizes I
      (fun x => f x + h x)
      (fun x => g x + h x) := by

  intro x hx

  exact add_le_add
    (hfg x hx)
    le_rfl


/-!
============================================================
Multiplication by a nonnegative function preserves
majorization
============================================================
-/

theorem majorizes_mul_of_nonneg
    (I : Set ℝ)
    (f g h : ℝ → ℝ)
    (hfg : Majorizes I f g)
    (hh :
      ∀ x ∈ I,
        0 ≤ h x) :
    Majorizes I
      (fun x => f x * h x)
      (fun x => g x * h x) := by

  intro x hx

  exact mul_le_mul_of_nonneg_right
    (hfg x hx)
    (hh x hx)


/-!
============================================================
Counterexample for multiplication

Take I = {0},
f = 1,
g = 0,
h = -1.

Then f majorizes g, but f*h does not majorize g*h.
============================================================
-/

def I₀ : Set ℝ :=
  {0}


def f₀ (_x : ℝ) : ℝ :=
  1


def g₀ (_x : ℝ) : ℝ :=
  0


def h₀ (_x : ℝ) : ℝ :=
  -1


theorem f₀_majorizes_g₀ :
    Majorizes I₀ f₀ g₀ := by

  intro x hx

  norm_num [f₀, g₀]


theorem mul_counterexample :
    ¬ Majorizes I₀
        (fun x => f₀ x * h₀ x)
        (fun x => g₀ x * h₀ x) := by

  intro hmaj

  have h :=
    hmaj 0 (by
      simp [I₀])

  norm_num [f₀, g₀, h₀] at h


/-!
============================================================
Scalar multiplication by c ≥ 0 preserves majorization
============================================================
-/

theorem majorizes_const_mul_of_nonneg
    (I : Set ℝ)
    (f g : ℝ → ℝ)
    (c : ℝ)
    (hfg : Majorizes I f g)
    (hc : 0 ≤ c) :
    Majorizes I
      (fun x => c * f x)
      (fun x => c * g x) := by

  intro x hx

  exact mul_le_mul_of_nonneg_left
    (hfg x hx)
    hc


/-!
============================================================
Counterexample for negative scalar multiplication

Again take I = {0}, f = 1, g = 0 and c = -1.
============================================================
-/

theorem const_mul_counterexample :
    ¬ Majorizes I₀
        (fun x => (-1 : ℝ) * f₀ x)
        (fun x => (-1 : ℝ) * g₀ x) := by

  intro hmaj

  have h :=
    hmaj 0 (by
      simp [I₀])

  norm_num [f₀, g₀] at h


/-!
============================================================
If c ≤ 0, multiplication reverses the order
============================================================
-/

theorem const_mul_reverses_of_nonpos
    (I : Set ℝ)
    (f g : ℝ → ℝ)
    (c : ℝ)
    (hfg : Majorizes I f g)
    (hc : c ≤ 0) :
    Majorizes I
      (fun x => c * g x)
      (fun x => c * f x) := by

  intro x hx

  exact mul_le_mul_of_nonpos_left
    (hfg x hx)
    hc


/-!
============================================================
Strictly negative version
============================================================
-/

theorem const_mul_reverses_of_neg
    (I : Set ℝ)
    (f g : ℝ → ℝ)
    (c : ℝ)
    (hfg : Majorizes I f g)
    (hc : c < 0) :
    Majorizes I
      (fun x => c * g x)
      (fun x => c * f x) := by

  exact const_mul_reverses_of_nonpos
    I
    f
    g
    c
    hfg
    (le_of_lt hc)


/-!
============================================================
Exercise 11.3.2 — addition
============================================================
-/

theorem exercise_11_3_2_add
    (I : Set ℝ)
    (f g h : ℝ → ℝ)
    (hfg : Majorizes I f g) :
    Majorizes I
      (fun x => f x + h x)
      (fun x => g x + h x) := by

  exact majorizes_add
    I
    f
    g
    h
    hfg


/-!
============================================================
Exercise 11.3.2 — multiplication

It is true provided h is nonnegative.
Without this hypothesis, mul_counterexample shows that
the statement is false in general.
============================================================
-/

theorem exercise_11_3_2_mul_nonneg
    (I : Set ℝ)
    (f g h : ℝ → ℝ)
    (hfg : Majorizes I f g)
    (hh :
      ∀ x ∈ I,
        0 ≤ h x) :
    Majorizes I
      (fun x => f x * h x)
      (fun x => g x * h x) := by

  exact majorizes_mul_of_nonneg
    I
    f
    g
    h
    hfg
    hh


/-!
============================================================
Exercise 11.3.2 — scalar multiplication

It is true provided c ≥ 0.
Without this hypothesis, const_mul_counterexample shows
that the statement is false in general.
============================================================
-/

theorem exercise_11_3_2_const_nonneg
    (I : Set ℝ)
    (f g : ℝ → ℝ)
    (c : ℝ)
    (hfg : Majorizes I f g)
    (hc : 0 ≤ c) :
    Majorizes I
      (fun x => c * f x)
      (fun x => c * g x) := by

  exact majorizes_const_mul_of_nonneg
    I
    f
    g
    c
    hfg
    hc


/-!
============================================================
Combined formal statement of Exercise 11.3.2
============================================================
-/

theorem exercise_11_3_2
    (I : Set ℝ)
    (f g h : ℝ → ℝ)
    (hfg : Majorizes I f g) :
    Majorizes I
        (fun x => f x + h x)
        (fun x => g x + h x)
      ∧
    ((∀ x ∈ I, 0 ≤ h x) →
      Majorizes I
        (fun x => f x * h x)
        (fun x => g x * h x))
      ∧
    (∀ c : ℝ,
      0 ≤ c →
      Majorizes I
        (fun x => c * f x)
        (fun x => c * g x)) := by

  constructor

  · exact majorizes_add
      I
      f
      g
      h
      hfg

  · constructor

    · intro hh

      exact majorizes_mul_of_nonneg
        I
        f
        g
        h
        hfg
        hh

    · intro c hc

      exact majorizes_const_mul_of_nonneg
        I
        f
        g
        c
        hfg
        hc

end TaoExercise11_3_2
