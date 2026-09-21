import Mathlib

namespace TaoExercise3_3_4

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}

/--
If g ∘ f1 = g ∘ f2 and g is injective,
then f1 = f2.
-/
theorem cancel_left_of_injective
    (f1 f2 : X → Y)
    (g : Y → Z)
    (hcomp : g ∘ f1 = g ∘ f2)
    (hg : Function.Injective g) :
    f1 = f2 := by
  funext x
  apply hg
  exact congrFun hcomp x


/--
If g1 ∘ f = g2 ∘ f and f is surjective,
then g1 = g2.
-/
theorem cancel_right_of_surjective
    (f : X → Y)
    (g1 g2 : Y → Z)
    (hcomp : g1 ∘ f = g2 ∘ f)
    (hf : Function.Surjective f) :
    g1 = g2 := by
  funext y
  obtain ⟨x, hx⟩ := hf y

  have h := congrFun hcomp x

  change g1 (f x) = g2 (f x) at h

  rw [hx] at h

  exact h


/--
Counterexample:
without injectivity of g, left cancellation can fail.
-/
theorem left_cancellation_fails_without_injective :
    ∃ (f1 f2 : Bool → Bool) (g : Bool → Bool),
      g ∘ f1 = g ∘ f2 ∧ f1 ≠ f2 := by

  let f1 : Bool → Bool := fun x => x
  let f2 : Bool → Bool := fun _ => false
  let g : Bool → Bool := fun _ => false

  refine ⟨f1, f2, g, ?_, ?_⟩

  · funext x
    rfl

  · intro h
    have htrue : f1 true = f2 true :=
      congrFun h true

    simp [f1, f2] at htrue


/--
Counterexample:
without surjectivity of f, right cancellation can fail.
-/
theorem right_cancellation_fails_without_surjective :
    ∃ (f : Unit → Bool) (g1 g2 : Bool → Bool),
      g1 ∘ f = g2 ∘ f ∧ g1 ≠ g2 := by

  let f : Unit → Bool := fun _ => false
  let g1 : Bool → Bool := fun _ => false
  let g2 : Bool → Bool := fun x => x

  refine ⟨f, g1, g2, ?_, ?_⟩

  · funext x
    cases x
    rfl

  · intro h
    have htrue : g1 true = g2 true :=
      congrFun h true

    simp [g1, g2] at htrue


/--
First assertion of Exercise 3.3.4.
-/
theorem exercise_3_3_4_part1
    (f1 f2 : X → Y)
    (g : Y → Z)
    (hcomp : g ∘ f1 = g ∘ f2)
    (hg : Function.Injective g) :
    f1 = f2 := by
  exact cancel_left_of_injective f1 f2 g hcomp hg


/--
Second assertion of Exercise 3.3.4.
-/
theorem exercise_3_3_4_part2
    (f : X → Y)
    (g1 g2 : Y → Z)
    (hcomp : g1 ∘ f = g2 ∘ f)
    (hf : Function.Surjective f) :
    g1 = g2 := by
  exact cancel_right_of_surjective f g1 g2 hcomp hf

end TaoExercise3_3_4
