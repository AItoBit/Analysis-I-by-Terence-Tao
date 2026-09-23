import Mathlib

namespace TaoExercise8_5_4

open Set

/-!
============================================================
Positive real numbers
============================================================
-/

def PositiveReals : Set ℝ :=
  {x : ℝ | 0 < x}


/-!
============================================================
Every positive real has a smaller positive real
============================================================
-/

theorem exists_smaller_positive
    {m : ℝ}
    (hm : m ∈ PositiveReals) :
    ∃ x : ℝ,
      x ∈ PositiveReals ∧
      x < m := by

  have hmpos :
      0 < m := by
    exact hm

  refine ⟨m / 2, ?_, ?_⟩

  · unfold PositiveReals

    have htwo :
        (0 : ℝ) < 2 := by
      norm_num

    exact div_pos hmpos htwo

  · have hhalf :
        m / 2 < m := by
      linarith

    exact hhalf


/-!
============================================================
There is no minimal element
============================================================
-/

theorem positiveReals_no_minimal :
    ¬ ∃ m : ℝ,
        m ∈ PositiveReals ∧
        ∀ x : ℝ,
          x ∈ PositiveReals →
          m ≤ x := by

  intro hmin

  rcases hmin with ⟨m, hmPos, hmLeast⟩

  obtain ⟨x, hxPos, hxm⟩ :=
    exists_smaller_positive hmPos

  have hmx :
      m ≤ x := by
    exact hmLeast x hxPos

  linarith


/-!
============================================================
Same result using Set.IsLeast
============================================================
-/

theorem positiveReals_no_isLeast :
    ¬ ∃ m : ℝ,
        IsLeast PositiveReals m := by

  intro h

  rcases h with ⟨m, hm⟩

  have hmPos :
      m ∈ PositiveReals := by
    exact hm.1

  obtain ⟨x, hxPos, hxm⟩ :=
    exists_smaller_positive hmPos

  have hmx :
      m ≤ x := by
    exact hm.2 hxPos

  linarith


/-!
============================================================
Exercise 8.5.4
============================================================
-/

theorem exercise_8_5_4 :
    ¬ ∃ m : ℝ,
        IsLeast PositiveReals m := by

  exact positiveReals_no_isLeast

end TaoExercise8_5_4
