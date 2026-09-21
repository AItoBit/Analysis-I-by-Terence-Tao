import Mathlib

namespace TaoExercise3_3_5

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}

/--
If `g ∘ f` is injective, then `f` is injective.
-/
theorem injective_of_comp_injective
    (f : X → Y)
    (g : Y → Z)
    (hcomp : Function.Injective (g ∘ f)) :
    Function.Injective f := by
  intro x x' hfx

  apply hcomp

  change g (f x) = g (f x')

  rw [hfx]


/--
`g` need not be injective even if `g ∘ f` is injective.
-/
theorem g_need_not_be_injective :
    ∃ (f : Bool → Option Bool) (g : Option Bool → Bool),
      Function.Injective (g ∘ f) ∧
      ¬ Function.Injective g := by

  let f : Bool → Option Bool := fun x =>
    some x

  let g : Option Bool → Bool
    | none => false
    | some false => false
    | some true => true

  refine ⟨f, g, ?_, ?_⟩

  · intro x x' h
    cases x <;> cases x' <;> simp [f, g] at h ⊢

  · intro hg
    have hEq :
        g none = g (some false) := by
      rfl

    have hBad :
        none = some false := by
      exact hg hEq

    cases hBad


/--
If `g ∘ f` is surjective, then `g` is surjective.
-/
theorem surjective_of_comp_surjective
    (f : X → Y)
    (g : Y → Z)
    (hcomp : Function.Surjective (g ∘ f)) :
    Function.Surjective g := by
  intro z

  obtain ⟨x, hx⟩ := hcomp z

  refine ⟨f x, ?_⟩

  exact hx


/--
`f` need not be surjective even if `g ∘ f` is surjective.
-/
theorem f_need_not_be_surjective :
    ∃ (f : Bool → Option Bool) (g : Option Bool → Bool),
      Function.Surjective (g ∘ f) ∧
      ¬ Function.Surjective f := by

  let f : Bool → Option Bool := fun x =>
    some x

  let g : Option Bool → Bool
    | none => false
    | some false => false
    | some true => true

  refine ⟨f, g, ?_, ?_⟩

  · intro z

    cases z with
    | false =>
        refine ⟨false, ?_⟩
        rfl
    | true =>
        refine ⟨true, ?_⟩
        rfl

  · intro hf

    obtain ⟨x, hx⟩ := hf none

    cases x <;> simp [f] at hx


/--
Exercise 3.3.5, first main statement.
-/
theorem exercise_3_3_5_part1
    (f : X → Y)
    (g : Y → Z)
    (hcomp : Function.Injective (g ∘ f)) :
    Function.Injective f := by
  exact injective_of_comp_injective f g hcomp


/--
Exercise 3.3.5, second main statement.
-/
theorem exercise_3_3_5_part2
    (f : X → Y)
    (g : Y → Z)
    (hcomp : Function.Surjective (g ∘ f)) :
    Function.Surjective g := by
  exact surjective_of_comp_surjective f g hcomp

end TaoExercise3_3_5
