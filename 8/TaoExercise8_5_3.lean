import Mathlib

namespace TaoExercise8_5_3

open Nat

/-!
============================================================
Positive naturals
============================================================
-/

abbrev PosNat := ℕ+


/-!
============================================================
Divisibility relation
============================================================

We use the usual divisibility relation on the
underlying natural numbers.
-/

def Divides (a b : PosNat) : Prop :=
  (a : ℕ) ∣ (b : ℕ)


/-!
============================================================
Reflexivity
============================================================
-/

theorem divides_reflexive :
    ∀ a : PosNat, Divides a a := by
  intro a

  unfold Divides

  exact dvd_refl (a : ℕ)


/-!
============================================================
Antisymmetry
============================================================

For positive natural numbers, if a ∣ b and b ∣ a,
then a = b.
-/

theorem divides_antisymmetric :
    ∀ a b : PosNat,
      Divides a b →
      Divides b a →
      a = b := by

  intro a b hab hba

  apply Subtype.ext

  unfold Divides at hab hba

  exact Nat.dvd_antisymm hab hba


/-!
============================================================
Transitivity
============================================================
-/

theorem divides_transitive :
    ∀ a b c : PosNat,
      Divides a b →
      Divides b c →
      Divides a c := by

  intro a b c hab hbc

  unfold Divides at *

  exact dvd_trans hab hbc


/-!
============================================================
Partial order
============================================================
-/

theorem divisibility_is_partial_order :
    (∀ a : PosNat, Divides a a)
    ∧
    (∀ a b : PosNat,
      Divides a b →
      Divides b a →
      a = b)
    ∧
    (∀ a b c : PosNat,
      Divides a b →
      Divides b c →
      Divides a c) := by

  exact
    ⟨divides_reflexive,
      divides_antisymmetric,
      divides_transitive⟩


/-!
============================================================
Not a total order
============================================================

2 and 3 are incomparable:
  2 ∤ 3
  3 ∤ 2
-/

theorem two_not_divides_three :
    ¬ Divides (2 : PosNat) (3 : PosNat) := by

  unfold Divides

  norm_num


theorem three_not_divides_two :
    ¬ Divides (3 : PosNat) (2 : PosNat) := by

  unfold Divides

  norm_num


theorem divisibility_not_total :
    ¬ (∀ a b : PosNat,
        Divides a b ∨ Divides b a) := by

  intro htotal

  have h :=
    htotal (2 : PosNat) (3 : PosNat)

  rcases h with h23 | h32

  · exact two_not_divides_three h23

  · exact three_not_divides_two h32


/-
============================================================
Exercise 8.5.3
============================================================
-/

theorem exercise_8_5_3 :
    ((∀ a : PosNat, Divides a a)
      ∧
     (∀ a b : PosNat,
        Divides a b →
        Divides b a →
        a = b)
      ∧
     (∀ a b c : PosNat,
        Divides a b →
        Divides b c →
        Divides a c))
    ∧
    ¬ (∀ a b : PosNat,
        Divides a b ∨ Divides b a) := by

  constructor

  · exact divisibility_is_partial_order

  · exact divisibility_not_total

end TaoExercise8_5_3
