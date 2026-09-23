import Mathlib

namespace TaoExercise9_1_8

open Set

universe u

/-!
============================================================
Arbitrary intersections of closed sets are closed
============================================================
-/

theorem arbitrary_intersection_closed
    {ι : Type u}
    (X : ι → Set ℝ)
    (hX : ∀ i : ι, IsClosed (X i)) :
    IsClosed (⋂ i : ι, X i) := by

  exact isClosed_iInter hX


/-!
============================================================
Exercise 9.1.8
============================================================
-/

theorem exercise_9_1_8
    {ι : Type u}
    (X : ι → Set ℝ)
    (hX : ∀ i : ι, IsClosed (X i)) :
    IsClosed (⋂ i : ι, X i) := by

  exact isClosed_iInter hX

end TaoExercise9_1_8
