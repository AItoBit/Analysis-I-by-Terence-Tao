import Mathlib

namespace TaoExercise3_3_7

universe u v w u₁ u₂

variable {X : Type u} {Y : Type v} {Z : Type w}

/--
If `f : X → Y` and `g : Y → Z` are bijective,
then `g ∘ f` is bijective.
-/
theorem comp_bijective
    (f : X → Y)
    (g : Y → Z)
    (hf : Function.Bijective f)
    (hg : Function.Bijective g) :
    Function.Bijective (g ∘ f) := by
  constructor
  · exact hg.1.comp hf.1
  · exact hg.2.comp hf.2


/--
Inverse of a bijective function.
-/
noncomputable def inv
    {A : Type u₁}
    {B : Type u₂}
    (f : A → B)
    (hf : Function.Bijective f) :
    B → A :=
  (Equiv.ofBijective f hf).symm


/--
First cancellation law:

    inv f (f x) = x
-/
theorem inv_apply_apply
    {A : Type u₁}
    {B : Type u₂}
    (f : A → B)
    (hf : Function.Bijective f)
    (x : A) :
    inv f hf (f x) = x := by
  let e : A ≃ B := Equiv.ofBijective f hf
  change e.symm (e x) = x
  exact e.symm_apply_apply x


/--
Second cancellation law:

    f (inv f y) = y
-/
theorem apply_inv_apply
    {A : Type u₁}
    {B : Type u₂}
    (f : A → B)
    (hf : Function.Bijective f)
    (y : B) :
    f (inv f hf y) = y := by
  let e : A ≃ B := Equiv.ofBijective f hf
  change e (e.symm y) = y
  exact e.apply_symm_apply y


/--
Exercise 3.3.7:

    (g ∘ f)⁻¹ = f⁻¹ ∘ g⁻¹
-/
theorem inverse_comp
    (f : X → Y)
    (g : Y → Z)
    (hf : Function.Bijective f)
    (hg : Function.Bijective g) :
    inv
        (A := X)
        (B := Z)
        (g ∘ f)
        (comp_bijective f g hf hg)
      =
    (inv (A := X) (B := Y) f hf)
      ∘
    (inv (A := Y) (B := Z) g hg) := by

  funext z

  apply (comp_bijective f g hf hg).1

  calc
    (g ∘ f)
        (inv
          (A := X)
          (B := Z)
          (g ∘ f)
          (comp_bijective f g hf hg)
          z)
        = z := by
            exact
              apply_inv_apply
                (A := X)
                (B := Z)
                (g ∘ f)
                (comp_bijective f g hf hg)
                z

    _ = g (inv (A := Y) (B := Z) g hg z) := by
          symm
          exact
            apply_inv_apply
              (A := Y)
              (B := Z)
              g
              hg
              z

    _ =
        g
          (f
            (inv
              (A := X)
              (B := Y)
              f
              hf
              (inv (A := Y) (B := Z) g hg z))) := by
          congr 1
          symm
          exact
            apply_inv_apply
              (A := X)
              (B := Y)
              f
              hf
              (inv (A := Y) (B := Z) g hg z)

    _ =
        (g ∘ f)
          (((inv (A := X) (B := Y) f hf)
              ∘
            (inv (A := Y) (B := Z) g hg)) z) := by
          rfl


/--
Full statement of Exercise 3.3.7.
-/
theorem exercise_3_3_7
    (f : X → Y)
    (g : Y → Z)
    (hf : Function.Bijective f)
    (hg : Function.Bijective g) :
    Function.Bijective (g ∘ f)
    ∧
    inv
        (A := X)
        (B := Z)
        (g ∘ f)
        (comp_bijective f g hf hg)
      =
    (inv (A := X) (B := Y) f hf)
      ∘
    (inv (A := Y) (B := Z) g hg) := by
  constructor
  · exact comp_bijective f g hf hg
  · exact inverse_comp f g hf hg

end TaoExercise3_3_7
