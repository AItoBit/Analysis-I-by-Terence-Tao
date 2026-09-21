import Mathlib

namespace TaoExercise3_3_6

universe u v

variable {X : Type u} {Y : Type v}

/--
The inverse of a bijective function.
-/
noncomputable def inverseOfBijective
    (f : X → Y)
    (hf : Function.Bijective f) :
    Y → X :=
  (Equiv.ofBijective f hf).symm


/--
First cancellation law:

    f⁻¹ (f x) = x.
-/
theorem inverse_apply_apply
    (f : X → Y)
    (hf : Function.Bijective f)
    (x : X) :
    inverseOfBijective f hf (f x) = x := by
  let e : X ≃ Y := Equiv.ofBijective f hf

  change e.symm (e x) = x

  exact e.symm_apply_apply x


/--
Second cancellation law:

    f (f⁻¹ y) = y.
-/
theorem apply_inverse_apply
    (f : X → Y)
    (hf : Function.Bijective f)
    (y : Y) :
    f (inverseOfBijective f hf y) = y := by
  let e : X ≃ Y := Equiv.ofBijective f hf

  change e (e.symm y) = y

  exact e.apply_symm_apply y


/--
The inverse function is injective.
-/
theorem inverse_injective
    (f : X → Y)
    (hf : Function.Bijective f) :
    Function.Injective (inverseOfBijective f hf) := by
  intro y1 y2 h

  have h1 :
      f (inverseOfBijective f hf y1) =
      f (inverseOfBijective f hf y2) := by
    rw [h]

  rw [apply_inverse_apply f hf y1] at h1
  rw [apply_inverse_apply f hf y2] at h1

  exact h1


/--
The inverse function is surjective.
-/
theorem inverse_surjective
    (f : X → Y)
    (hf : Function.Bijective f) :
    Function.Surjective (inverseOfBijective f hf) := by
  intro x

  refine ⟨f x, ?_⟩

  exact inverse_apply_apply f hf x


/--
The inverse of a bijection is itself bijective.
-/
theorem inverse_bijective
    (f : X → Y)
    (hf : Function.Bijective f) :
    Function.Bijective (inverseOfBijective f hf) := by
  constructor
  · exact inverse_injective f hf
  · exact inverse_surjective f hf


/--
The inverse function has `f` as its inverse.

The two equations are:

    f⁻¹ (f x) = x
    f (f⁻¹ y) = y
-/
theorem f_is_inverse_of_inverse
    (f : X → Y)
    (hf : Function.Bijective f) :
    (∀ x : X, inverseOfBijective f hf (f x) = x)
    ∧
    (∀ y : Y, f (inverseOfBijective f hf y) = y) := by
  constructor
  · intro x
    exact inverse_apply_apply f hf x
  · intro y
    exact apply_inverse_apply f hf y


/--
Exercise 3.3.6.
-/
theorem exercise_3_3_6
    (f : X → Y)
    (hf : Function.Bijective f) :
    Function.Bijective (inverseOfBijective f hf)
    ∧
    (∀ x : X, inverseOfBijective f hf (f x) = x)
    ∧
    (∀ y : Y, f (inverseOfBijective f hf y) = y) := by
  constructor

  · exact inverse_bijective f hf

  · constructor
    · intro x
      exact inverse_apply_apply f hf x

    · intro y
      exact apply_inverse_apply f hf y

end TaoExercise3_3_6
