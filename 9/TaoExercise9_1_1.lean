import Mathlib

namespace TaoExercise9_1_1

open Set

/-!
============================================================
Closure sandwich lemma
============================================================
-/

theorem exercise_9_1_1
    (X Y : Set ℝ)
    (hXY : X ⊆ Y)
    (hYclX : Y ⊆ closure X) :
    closure Y = closure X := by

  apply le_antisymm

  · exact closure_minimal hYclX isClosed_closure

  · exact closure_mono hXY

end TaoExercise9_1_1
