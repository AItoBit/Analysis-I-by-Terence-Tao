import Mathlib

namespace TaoExercise8_2_2

open Set
open Function

universe u

/-!
============================================================
Absolute convergence
============================================================

For a function `f : X → ℝ`, absolute convergence means

    ∑ x, |f x|

is summable.
-/

def AbsolutelyConvergent
    {X : Type u}
    (f : X → ℝ) : Prop :=
  Summable (fun x : X => |f x|)


/-!
============================================================
Support
============================================================

The support is the set

    {x | f x ≠ 0}.
-/

def nonzeroSet
    {X : Type u}
    (f : X → ℝ) : Set X :=
  {x : X | f x ≠ 0}


/-!
The support of `|f|` is exactly the support of `f`.
-/

theorem support_abs_eq_support
    {X : Type u}
    (f : X → ℝ) :
    Function.support (fun x : X => |f x|)
      =
    Function.support f := by

  ext x

  simp [Function.mem_support]


/-!
Our explicit `nonzeroSet` is the same as `Function.support`.
-/

theorem nonzeroSet_eq_support
    {X : Type u}
    (f : X → ℝ) :
    nonzeroSet f = Function.support f := by

  ext x

  rfl


/-!
============================================================
Key fact

An absolutely summable function has countable support.
============================================================
-/

theorem support_countable_of_absoluteConvergence
    {X : Type u}
    (f : X → ℝ)
    (hf : AbsolutelyConvergent f) :
    (Function.support f).Countable := by

  unfold AbsolutelyConvergent at hf

  have hCountable :
      (Function.support (fun x : X => |f x|)).Countable := by

    exact hf.countable_support

  rw [support_abs_eq_support f] at hCountable

  exact hCountable


/-!
============================================================
Lemma 8.2.5

If the sum of `f` is absolutely convergent, then

    {x | f x ≠ 0}

is at most countable.
============================================================
-/

theorem lemma_8_2_5
    {X : Type u}
    (f : X → ℝ)
    (hf : AbsolutelyConvergent f) :
    (nonzeroSet f).Countable := by

  rw [nonzeroSet_eq_support f]

  exact support_countable_of_absoluteConvergence
    f
    hf


/-!
============================================================
Version written exactly as a set comprehension
============================================================
-/

theorem lemma_8_2_5_set
    {X : Type u}
    (f : X → ℝ)
    (hf : Summable (fun x : X => |f x|)) :
    ({x : X | f x ≠ 0} : Set X).Countable := by

  have hSupport :
      (Function.support f).Countable := by

    have hAbsSupport :
        (Function.support (fun x : X => |f x|)).Countable := by

      exact hf.countable_support

    rw [support_abs_eq_support f] at hAbsSupport

    exact hAbsSupport

  exact hSupport


/-!
============================================================
Exercise 8.2.2
============================================================
-/

theorem exercise_8_2_2
    {X : Type u}
    (f : X → ℝ)
    (hf : AbsolutelyConvergent f) :
    ({x : X | f x ≠ 0} : Set X).Countable := by

  exact lemma_8_2_5
    f
    hf

end TaoExercise8_2_2
