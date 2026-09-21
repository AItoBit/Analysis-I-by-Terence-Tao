import Mathlib

namespace TaoExercise3_4_5

open Set

universe u v

variable {X : Type u} {Y : Type v}

/--
Surjectivity is equivalent to saying that for every subset U of Y,

    f(f⁻¹(U)) = U.
-/
theorem surjective_iff_image_preimage_eq
    (f : X → Y) :
    Function.Surjective f ↔
      ∀ U : Set Y, f '' (f ⁻¹' U) = U := by
  constructor

  /-
  If f is surjective, then
      f(f⁻¹(U)) = U
  for every U ⊆ Y.
  -/
  · intro hf U

    ext y
    constructor

    /-
    f(f⁻¹(U)) ⊆ U.
    -/
    · intro hy

      rcases hy with ⟨x, hx, rfl⟩

      exact hx

    /-
    U ⊆ f(f⁻¹(U)).
    -/
    · intro hyU

      obtain ⟨x, hx⟩ := hf y

      refine ⟨x, ?_, hx⟩

      change f x ∈ U

      rw [hx]

      exact hyU

  /-
  Conversely, suppose
      f(f⁻¹(U)) = U
  for every U.

  Take U = univ.
  -/
  · intro h y

    have hy :
        y ∈ f '' (f ⁻¹' (Set.univ : Set Y)) := by
      rw [h (Set.univ : Set Y)]
      exact Set.mem_univ y

    rcases hy with ⟨x, hx, hxy⟩

    exact ⟨x, hxy⟩


/--
Injectivity is equivalent to saying that for every subset S of X,

    f⁻¹(f(S)) = S.
-/
theorem injective_iff_preimage_image_eq
    (f : X → Y) :
    Function.Injective f ↔
      ∀ S : Set X, f ⁻¹' (f '' S) = S := by
  constructor

  /-
  Suppose f is injective.
  -/
  · intro hf S

    ext x
    constructor

    /-
    f⁻¹(f(S)) ⊆ S.
    -/
    · intro hx

      change f x ∈ f '' S at hx

      rcases hx with ⟨x', hx'S, hEq⟩

      have hxx' : x' = x := by
        exact hf hEq

      rw [← hxx']

      exact hx'S

    /-
    S ⊆ f⁻¹(f(S)).
    -/
    · intro hxS

      change f x ∈ f '' S

      exact ⟨x, hxS, rfl⟩

  /-
  Conversely, suppose
      f⁻¹(f(S)) = S
  for every S.

  Take the singleton S = {x}.
  -/
  · intro h
    intro x x' hfx

    have hx' :
        x' ∈ f ⁻¹' (f '' ({x} : Set X)) := by

      change f x' ∈ f '' ({x} : Set X)

      refine ⟨x, ?_, ?_⟩

      · simp

      · exact hfx

    have hx'Singleton :
        x' ∈ ({x} : Set X) := by
      rw [← h ({x} : Set X)]
      exact hx'

    have hxx' : x' = x := by
      simpa using hx'Singleton

    exact hxx'.symm


/--
Exercise 3.4.5: both characterizations.
-/
theorem exercise_3_4_5
    (f : X → Y) :
    (Function.Surjective f ↔
      ∀ U : Set Y, f '' (f ⁻¹' U) = U)
    ∧
    (Function.Injective f ↔
      ∀ S : Set X, f ⁻¹' (f '' S) = S) := by
  constructor

  · exact surjective_iff_image_preimage_eq f

  · exact injective_iff_preimage_image_eq f

end TaoExercise3_4_5
