import Mathlib

namespace TaoExercise3_1_2

/-
Minimal universe sufficient for Exercise 3.1.2.
-/
inductive HFSet : Type
  | empty : HFSet
  | singleton : HFSet → HFSet
  | pair : HFSet → HFSet → HFSet
deriving DecidableEq

namespace HFSet

/-- Membership relation. -/
def Mem (x : HFSet) : HFSet → Prop
  | empty => False
  | singleton a => x = a
  | pair a b => x = a ∨ x = b

/-
Custom membership notation.
We avoid Lean's typeclass-based `∈`.
-/
infix:50 " ∈ₕ " => Mem

notation "∅ₕ" => HFSet.empty
notation "{" a "}ₕ" => HFSet.singleton a
notation "{" a ", " b "}ₕ" => HFSet.pair a b


/-!
Basic membership facts.
-/

lemma not_mem_empty (x : HFSet) :
    ¬ x ∈ₕ ∅ₕ := by
  intro h
  exact h


lemma mem_singleton_iff (x a : HFSet) :
    x ∈ₕ {a}ₕ ↔ x = a := by
  rfl


lemma mem_pair_iff (x a b : HFSet) :
    x ∈ₕ {a, b}ₕ ↔ x = a ∨ x = b := by
  rfl


/-!
1. ∅ ≠ {∅}
-/

lemma empty_ne_singleton_empty :
    ∅ₕ ≠ {∅ₕ}ₕ := by
  intro h

  have hm : ∅ₕ ∈ₕ {∅ₕ}ₕ := by
    rfl

  rw [← h] at hm

  exact not_mem_empty ∅ₕ hm


/-!
2. ∅ ≠ {{∅}}
-/

lemma empty_ne_singleton_singleton_empty :
    ∅ₕ ≠ {{∅ₕ}ₕ}ₕ := by
  intro h

  have hm : {∅ₕ}ₕ ∈ₕ {{∅ₕ}ₕ}ₕ := by
    rfl

  rw [← h] at hm

  exact not_mem_empty {∅ₕ}ₕ hm


/-!
3. ∅ ≠ {∅,{∅}}
-/

lemma empty_ne_pair :
    ∅ₕ ≠ {∅ₕ, {∅ₕ}ₕ}ₕ := by
  intro h

  have hm : ∅ₕ ∈ₕ {∅ₕ, {∅ₕ}ₕ}ₕ := by
    exact Or.inl rfl

  rw [← h] at hm

  exact not_mem_empty ∅ₕ hm


/-!
4. {∅} ≠ {{∅}}
-/

lemma singleton_empty_ne_singleton_singleton_empty :
    {∅ₕ}ₕ ≠ {{∅ₕ}ₕ}ₕ := by
  intro h

  have hm : ∅ₕ ∈ₕ {∅ₕ}ₕ := by
    rfl

  rw [h] at hm

  have heq : ∅ₕ = {∅ₕ}ₕ := by
    exact hm

  exact empty_ne_singleton_empty heq


/-!
5. {∅} ≠ {∅,{∅}}
-/

lemma singleton_empty_ne_pair :
    {∅ₕ}ₕ ≠ {∅ₕ, {∅ₕ}ₕ}ₕ := by
  intro h

  have hm :
      {∅ₕ}ₕ ∈ₕ {∅ₕ, {∅ₕ}ₕ}ₕ := by
    exact Or.inr rfl

  rw [← h] at hm

  have heq : {∅ₕ}ₕ = ∅ₕ := by
    exact hm

  exact empty_ne_singleton_empty heq.symm


/-!
6. {{∅}} ≠ {∅,{∅}}
-/

lemma singleton_singleton_empty_ne_pair :
    {{∅ₕ}ₕ}ₕ ≠ {∅ₕ, {∅ₕ}ₕ}ₕ := by
  intro h

  have hm :
      ∅ₕ ∈ₕ {∅ₕ, {∅ₕ}ₕ}ₕ := by
    exact Or.inl rfl

  rw [← h] at hm

  have heq : ∅ₕ = {∅ₕ}ₕ := by
    exact hm

  exact empty_ne_singleton_empty heq


/--
Exercise 3.1.2.

The four sets

    ∅
    {∅}
    {{∅}}
    {∅,{∅}}

are pairwise distinct.
-/
theorem exercise_3_1_2 :
    ∅ₕ ≠ {∅ₕ}ₕ
    ∧ ∅ₕ ≠ {{∅ₕ}ₕ}ₕ
    ∧ ∅ₕ ≠ {∅ₕ, {∅ₕ}ₕ}ₕ
    ∧ {∅ₕ}ₕ ≠ {{∅ₕ}ₕ}ₕ
    ∧ {∅ₕ}ₕ ≠ {∅ₕ, {∅ₕ}ₕ}ₕ
    ∧ {{∅ₕ}ₕ}ₕ ≠ {∅ₕ, {∅ₕ}ₕ}ₕ := by
  exact
    ⟨empty_ne_singleton_empty,
     empty_ne_singleton_singleton_empty,
     empty_ne_pair,
     singleton_empty_ne_singleton_singleton_empty,
     singleton_empty_ne_pair,
     singleton_singleton_empty_ne_pair⟩

end HFSet
end TaoExercise3_1_2
