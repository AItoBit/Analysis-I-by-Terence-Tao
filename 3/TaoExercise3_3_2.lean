import Mathlib

namespace TaoExercise3_3_2

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}

/--
If `f : X → Y` and `g : Y → Z` are injective,
then `g ∘ f` is injective.
-/
theorem comp_injective
    (f : X → Y)
    (g : Y → Z)
    (hf : Function.Injective f)
    (hg : Function.Injective g) :
    Function.Injective (g ∘ f) := by
  intro x x' h
  apply hf
  apply hg
  exact h


/--
If `f : X → Y` and `g : Y → Z` are surjective,
then `g ∘ f` is surjective.
-/
theorem comp_surjective
    (f : X → Y)
    (g : Y → Z)
    (hf : Function.Surjective f)
    (hg : Function.Surjective g) :
    Function.Surjective (g ∘ f) := by
  intro z

  obtain ⟨y, hy⟩ := hg z
  obtain ⟨x, hx⟩ := hf y

  refine ⟨x, ?_⟩

  change g (f x) = z

  rw [hx]
  exact hy


/--
Exercise 3.3.2.
-/
theorem exercise_3_3_2
    (f : X → Y)
    (g : Y → Z)
    (hf_inj : Function.Injective f)
    (hg_inj : Function.Injective g)
    (hf_surj : Function.Surjective f)
    (hg_surj : Function.Surjective g) :
    Function.Injective (g ∘ f)
    ∧ Function.Surjective (g ∘ f) := by
  constructor
  · exact comp_injective f g hf_inj hg_inj
  · exact comp_surjective f g hf_surj hg_surj

end TaoExercise3_3_2
