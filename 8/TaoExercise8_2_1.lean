import Mathlib

namespace TaoExercise8_2_1

open Set
open scoped BigOperators

universe u

/-!
============================================================
Restriction of f to X
============================================================
-/

def restricted
    {α : Type u}
    (X : Set α)
    (f : α → ℝ) :
    X → ℝ :=
  fun x => f x.1


/-!
============================================================
Absolute convergence on X
============================================================

This is the Mathlib formulation of

    ∑_{x ∈ X} |f(x)| < ∞.

The index type is the subtype `X`.
-/

def AbsolutelyConvergentOn
    {α : Type u}
    (X : Set α)
    (f : α → ℝ) : Prop :=
  Summable (fun x : X => abs (f x.1))


/-!
============================================================
Finite subsums are uniformly bounded
============================================================

This formalizes

  sup {
    ∑_{x ∈ A} |f(x)| :
    A ⊆ X,
    A finite
  } < ∞.

A `Finset X` is precisely a finite collection of
elements of X.
-/

def FiniteAbsSumsBounded
    {α : Type u}
    (X : Set α)
    (f : α → ℝ) : Prop :=
  ∃ C : ℝ,
    0 ≤ C ∧
    ∀ s : Finset X,
      s.sum (fun x => abs (f x.1)) ≤ C


/-!
============================================================
The ℓ¹ formulation is equivalent to absolute convergence
============================================================
-/

theorem memLp_one_iff_absoluteConvergent
    {α : Type u}
    (X : Set α)
    (f : α → ℝ) :
    Memℓp (restricted X f) (1 : ENNReal)
      ↔
    AbsolutelyConvergentOn X f := by

  unfold AbsolutelyConvergentOn

  have h :=
    memℓp_gen_iff
      (f := restricted X f)
      (p := (1 : ENNReal))
      (by norm_num)

  simpa [restricted, Real.norm_eq_abs] using h


/-!
============================================================
The ℓ¹ formulation is equivalent to bounded finite sums
============================================================
-/

theorem memLp_one_iff_finiteAbsSumsBounded
    {α : Type u}
    (X : Set α)
    (f : α → ℝ) :
    Memℓp (restricted X f) (1 : ENNReal)
      ↔
    FiniteAbsSumsBounded X f := by

  unfold FiniteAbsSumsBounded

  have h :=
    memℓp_gen_iff''
      (f := restricted X f)
      (p := (1 : ENNReal))
      (by norm_num)

  simpa [restricted, Real.norm_eq_abs] using h


/-!
============================================================
Lemma 8.2.3
============================================================

For a countable set X,

    ∑_{x ∈ X} f(x)

is absolutely convergent iff all finite sums

    ∑_{x ∈ A} |f(x)|

are bounded above by one finite real number.
-/

theorem lemma_8_2_3
    {α : Type u}
    (X : Set α)
    (f : α → ℝ)
    (_hX : X.Countable) :
    AbsolutelyConvergentOn X f
      ↔
    FiniteAbsSumsBounded X f := by

  have h₁ :
      Memℓp (restricted X f) (1 : ENNReal)
        ↔
      AbsolutelyConvergentOn X f :=
    memLp_one_iff_absoluteConvergent X f

  have h₂ :
      Memℓp (restricted X f) (1 : ENNReal)
        ↔
      FiniteAbsSumsBounded X f :=
    memLp_one_iff_finiteAbsSumsBounded X f

  exact h₁.symm.trans h₂


/-!
============================================================
Exercise 8.2.1
============================================================
-/

theorem exercise_8_2_1
    {α : Type u}
    (X : Set α)
    (f : α → ℝ)
    (hX : X.Countable) :
    AbsolutelyConvergentOn X f
      ↔
    FiniteAbsSumsBounded X f := by

  exact lemma_8_2_3 X f hX

end TaoExercise8_2_1
