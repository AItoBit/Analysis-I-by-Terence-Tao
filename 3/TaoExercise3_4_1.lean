import Mathlib

namespace TaoExercise3_4_1

open Set

universe u v

variable {X : Type u} {Y : Type v}

/--
Inverse of a bijective function.
-/
noncomputable def inv
    (f : X → Y)
    (hf : Function.Bijective f) :
    Y → X :=
  (Equiv.ofBijective f hf).symm


/--
Cancellation law:

    f (inv f y) = y
-/
theorem apply_inv_apply
    (f : X → Y)
    (hf : Function.Bijective f)
    (y : Y) :
    f (inv f hf y) = y := by
  let e : X ≃ Y := Equiv.ofBijective f hf
  change e (e.symm y) = y
  exact e.apply_symm_apply y


/--
Cancellation law:

    inv f (f x) = x
-/
theorem inv_apply_apply
    (f : X → Y)
    (hf : Function.Bijective f)
    (x : X) :
    inv f hf (f x) = x := by
  let e : X ≃ Y := Equiv.ofBijective f hf
  change e.symm (e x) = x
  exact e.symm_apply_apply x


/--
Exercise 3.4.1.

The forward image of `V` under `f⁻¹`
is equal to the inverse image of `V` under `f`.
-/
theorem exercise_3_4_1
    (f : X → Y)
    (hf : Function.Bijective f)
    (V : Set Y) :
    inv f hf '' V = f ⁻¹' V := by

  ext x
  constructor

  /-
  Forward direction:
  if x is in the image of V under f⁻¹,
  then f x ∈ V.
  -/
  · intro hx

    rcases hx with ⟨y, hyV, hxy⟩

    /-
    hxy : inv f hf y = x
    -/
    subst x

    change f (inv f hf y) ∈ V

    rw [apply_inv_apply f hf y]

    exact hyV

  /-
  Reverse direction:
  if f x ∈ V,
  then x is the image under f⁻¹ of f x.
  -/
  · intro hx

    refine ⟨f x, hx, ?_⟩

    exact inv_apply_apply f hf x

end TaoExercise3_4_1
