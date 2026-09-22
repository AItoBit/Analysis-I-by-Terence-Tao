import Mathlib

namespace TaoExercise6_4_7

/--
A real sequence `a` converges to `L` starting from index `m`.
-/
def ConvergesFrom
    (a : ℕ → ℝ)
    (m : ℕ)
    (L : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ,
      m ≤ N ∧
      ∀ n : ℕ,
        N ≤ n →
        |a n - L| ≤ ε


/-!
============================================================
Forward direction

If |a_n| -> 0, then a_n -> 0.
============================================================
-/

theorem converges_zero_of_abs_converges_zero
    (a : ℕ → ℝ)
    (m : ℕ)
    (habs :
      ConvergesFrom
        (fun n => |a n|)
        m
        0) :
    ConvergesFrom
      a
      m
      0 := by

  intro ε hε

  obtain ⟨N, hmN, hN⟩ :=
    habs ε hε

  refine ⟨N, hmN, ?_⟩

  intro n hn

  have hclose :=
    hN n hn

  simpa using hclose


/-!
============================================================
Reverse direction

If a_n -> 0, then |a_n| -> 0.
============================================================
-/

theorem abs_converges_zero_of_converges_zero
    (a : ℕ → ℝ)
    (m : ℕ)
    (ha :
      ConvergesFrom
        a
        m
        0) :
    ConvergesFrom
      (fun n => |a n|)
      m
      0 := by

  intro ε hε

  obtain ⟨N, hmN, hN⟩ :=
    ha ε hε

  refine ⟨N, hmN, ?_⟩

  intro n hn

  have hclose :=
    hN n hn

  simpa using hclose


/-!
============================================================
Corollary 6.4.17

a_n -> 0 iff |a_n| -> 0.
============================================================
-/

theorem corollary_6_4_17
    (a : ℕ → ℝ)
    (m : ℕ) :
    ConvergesFrom a m 0 ↔
    ConvergesFrom (fun n => |a n|) m 0 := by

  constructor

  · intro ha

    exact abs_converges_zero_of_converges_zero
      a
      m
      ha

  · intro habs

    exact converges_zero_of_abs_converges_zero
      a
      m
      habs


/-!
============================================================
Exercise 6.4.7
============================================================
-/

theorem exercise_6_4_7
    (a : ℕ → ℝ)
    (m : ℕ) :
    ConvergesFrom a m 0 ↔
    ConvergesFrom (fun n => |a n|) m 0 := by

  exact corollary_6_4_17 a m

end TaoExercise6_4_7
