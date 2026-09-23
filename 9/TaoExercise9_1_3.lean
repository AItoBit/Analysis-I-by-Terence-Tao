import Mathlib

namespace TaoExercise9_1_3

open Set

def NatReals : Set ℝ :=
  Set.range (fun n : ℕ => (n : ℝ))

def IntReals : Set ℝ :=
  Set.range (fun z : ℤ => (z : ℝ))

def RatReals : Set ℝ :=
  Set.range (fun q : ℚ => (q : ℝ))


/-!
(i) closure ℝ = ℝ
-/

theorem closure_real :
    closure (Set.univ : Set ℝ) = Set.univ := by
  exact closure_univ


/-!
(ii) closure ∅ = ∅
-/

theorem closure_empty_real :
    closure (∅ : Set ℝ) = ∅ := by
  exact closure_empty


/-!
(iii) closure ℕ = ℕ
-/

theorem natReals_isClosed :
    IsClosed NatReals := by
  unfold NatReals
  exact Nat.isClosedEmbedding_coe_real.isClosed_range


theorem closure_natReals :
    closure NatReals = NatReals := by
  exact natReals_isClosed.closure_eq


/-!
(iv) closure ℤ = ℤ
-/

theorem intReals_isClosed :
    IsClosed IntReals := by
  unfold IntReals
  exact Int.isClosedEmbedding_coe_real.isClosed_range


theorem closure_intReals :
    closure IntReals = IntReals := by
  exact intReals_isClosed.closure_eq


/-!
(v) closure ℚ = ℝ
-/

theorem ratReals_dense :
    Dense RatReals := by
  unfold RatReals
  exact Rat.isDenseEmbedding_coe_real.dense


theorem closure_ratReals :
    closure RatReals = Set.univ := by
  exact ratReals_dense.closure_eq


/-!
Lemma 9.1.13
-/

theorem lemma_9_1_13 :
    closure (Set.univ : Set ℝ) = Set.univ
      ∧
    closure (∅ : Set ℝ) = ∅
      ∧
    closure NatReals = NatReals
      ∧
    closure IntReals = IntReals
      ∧
    closure RatReals = Set.univ := by

  constructor

  · exact closure_real

  constructor

  · exact closure_empty_real

  constructor

  · exact closure_natReals

  constructor

  · exact closure_intReals

  · exact closure_ratReals


theorem exercise_9_1_3 :
    closure (Set.univ : Set ℝ) = Set.univ
      ∧
    closure (∅ : Set ℝ) = ∅
      ∧
    closure NatReals = NatReals
      ∧
    closure IntReals = IntReals
      ∧
    closure RatReals = Set.univ := by

  exact lemma_9_1_13

end TaoExercise9_1_3
