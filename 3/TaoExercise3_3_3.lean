import Mathlib

namespace TaoExercise3_3_3

universe u

variable {Y : Type u}

/--
The empty function from `Empty` to `Y`.
-/
def emptyFunction : Empty → Y :=
  fun x => nomatch x


/--
The empty function is always injective.
-/
theorem empty_function_injective :
    Function.Injective (emptyFunction : Empty → Y) := by
  intro x x' h
  exact nomatch x


/--
The empty function is surjective iff the codomain is empty.
We express "Y is empty" by `IsEmpty Y`.
-/
theorem empty_function_surjective_iff :
    Function.Surjective (emptyFunction : Empty → Y) ↔ IsEmpty Y := by
  constructor

  /-
  If the empty function is surjective, then Y has no elements.
  -/
  · intro hsurj

    constructor
    intro y

    obtain ⟨x, hx⟩ := hsurj y

    exact nomatch x

  /-
  If Y is empty, surjectivity is vacuously true.
  -/
  · intro hEmpty
    intro y

    exact isEmptyElim y


/--
The empty function is bijective iff the codomain is empty.
-/
theorem empty_function_bijective_iff :
    Function.Bijective (emptyFunction : Empty → Y) ↔ IsEmpty Y := by
  constructor

  · intro hbij
    exact
      (empty_function_surjective_iff (Y := Y)).1 hbij.2

  · intro hEmpty
    constructor
    · exact empty_function_injective (Y := Y)
    · exact
        (empty_function_surjective_iff (Y := Y)).2 hEmpty

end TaoExercise3_3_3
