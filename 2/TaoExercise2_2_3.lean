import Mathlib

namespace TaoExercise2_2_3

/-
Exercise 2.2.3

Let a, b, c be natural numbers.
Prove the basic properties of order.
-/

variable (a b c : ℕ)

/-- (a) Reflexivity: a ≥ a. -/
theorem part_a_reflexivity :
    a ≤ a := by
  exact le_rfl


/-- (b) Transitivity:
if a ≥ b and b ≥ c, then a ≥ c.

Written with Lean's ≤ notation:
c ≤ b → b ≤ a → c ≤ a.
-/
theorem part_b_transitivity
    (hab : b ≤ a)
    (hbc : c ≤ b) :
    c ≤ a := by
  exact le_trans hbc hab


/-- (c) Antisymmetry:
if a ≥ b and b ≥ a, then a = b.
-/
theorem part_c_antisymmetry
    (hab : b ≤ a)
    (hba : a ≤ b) :
    a = b := by
  exact Nat.le_antisymm hab hba


/-- (d) Preservation of order:
a ≥ b iff a + c ≥ b + c.
-/
theorem part_d_preservation :
    b ≤ a ↔ b + c ≤ a + c := by
  constructor
  · intro hab
    exact Nat.add_le_add_right hab c
  · intro h
    exact Nat.le_of_add_le_add_right h


/-- (e) a < b iff succ a ≤ b. -/
theorem part_e_succ_order :
    a < b ↔ Nat.succ a ≤ b := by
  exact Nat.lt_iff_add_one_le


/-- (f) a < b iff b = a + d for some positive d. -/
theorem part_f_positive_difference :
    a < b ↔ ∃ d : ℕ, 0 < d ∧ b = a + d := by
  constructor

  · intro hab

    have hab' : a ≤ b := Nat.le_of_lt hab

    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hab'

    have hdpos : 0 < d := by
      by_contra h
      have hd0 : d = 0 := Nat.eq_zero_of_not_pos h
      subst d
      simp at hd
      subst b
      exact (Nat.lt_irrefl a) hab

    exact ⟨d, hdpos, hd.symm⟩

  · rintro ⟨d, hdpos, rfl⟩

    exact Nat.lt_add_of_pos_right hdpos


end TaoExercise2_2_3
