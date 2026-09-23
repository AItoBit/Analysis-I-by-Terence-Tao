import Mathlib

namespace TaoExercise8_5_2

/-!
============================================================
Basic relation properties
============================================================
-/

def IsReflexive
    {α : Type*}
    (r : α → α → Prop) : Prop :=
  ∀ x : α, r x x


def IsAntisymmetric
    {α : Type*}
    (r : α → α → Prop) : Prop :=
  ∀ x y : α, r x y → r y x → x = y


def IsTransitive
    {α : Type*}
    (r : α → α → Prop) : Prop :=
  ∀ x y z : α, r x y → r y z → r x z


/-!
============================================================
(a)

Reflexive and antisymmetric, but not transitive.

We use

    n R₁ m  ↔  n = m ∨ n + 1 = m.

Thus each number is related to itself and to its
immediate successor.
============================================================
-/

def relA (n m : ℕ) : Prop :=
  n = m ∨ n + 1 = m


theorem relA_reflexive :
    IsReflexive relA := by
  intro n
  left
  rfl


theorem relA_antisymmetric :
    IsAntisymmetric relA := by
  intro n m hnm hmn

  rcases hnm with hnm | hnm

  · exact hnm

  · rcases hmn with hmn | hmn

    · exact hmn.symm

    · omega


theorem relA_not_transitive :
    ¬ IsTransitive relA := by
  intro htrans

  have h12 :
      relA 1 2 := by
    right
    norm_num

  have h23 :
      relA 2 3 := by
    right
    norm_num

  have h13 :
      relA 1 3 := by
    exact htrans 1 2 3 h12 h23

  unfold relA at h13

  omega


theorem example_a :
    IsReflexive relA
      ∧ IsAntisymmetric relA
      ∧ ¬ IsTransitive relA := by
  exact
    ⟨relA_reflexive,
      relA_antisymmetric,
      relA_not_transitive⟩


/-!
============================================================
(b)

Reflexive and transitive, but not antisymmetric.

On ℝ × ℝ define

    (x,y) R₂ (x',y')  ↔  x ≤ x'.

Only the first coordinate matters.
============================================================
-/

def relB
    (p q : ℝ × ℝ) : Prop :=
  p.1 ≤ q.1


theorem relB_reflexive :
    IsReflexive relB := by
  intro p

  unfold relB

  exact le_rfl


theorem relB_transitive :
    IsTransitive relB := by
  intro p q r hpq hqr

  unfold relB at *

  exact le_trans hpq hqr


theorem relB_not_antisymmetric :
    ¬ IsAntisymmetric relB := by
  intro hanti

  let p : ℝ × ℝ := (2, 3)
  let q : ℝ × ℝ := (2, 4)

  have hpq :
      relB p q := by
    unfold relB p q
    norm_num

  have hqp :
      relB q p := by
    unfold relB p q
    norm_num

  have hpqEq :
      p = q := by
    exact hanti p q hpq hqp

  have hsecond :
      p.2 = q.2 := by
    exact congrArg Prod.snd hpqEq

  norm_num [p, q] at hsecond


theorem example_b :
    IsReflexive relB
      ∧ IsTransitive relB
      ∧ ¬ IsAntisymmetric relB := by
  exact
    ⟨relB_reflexive,
      relB_transitive,
      relB_not_antisymmetric⟩


/-!
============================================================
(c)

Antisymmetric and transitive, but not reflexive.

Use ordinary strict inequality on ℝ.
============================================================
-/

def relC (x y : ℝ) : Prop :=
  x < y


theorem relC_transitive :
    IsTransitive relC := by
  intro x y z hxy hyz

  exact lt_trans hxy hyz


theorem relC_antisymmetric :
    IsAntisymmetric relC := by
  intro x y hxy hyx

  have hfalse : False := by
    exact (lt_asymm hxy hyx)

  exact False.elim hfalse


theorem relC_not_reflexive :
    ¬ IsReflexive relC := by
  intro hrefl

  have h00 :
      relC 0 0 := by
    exact hrefl 0

  unfold relC at h00

  exact (lt_irrefl (0 : ℝ)) h00


theorem example_c :
    IsAntisymmetric relC
      ∧ IsTransitive relC
      ∧ ¬ IsReflexive relC := by
  exact
    ⟨relC_antisymmetric,
      relC_transitive,
      relC_not_reflexive⟩


/-!
============================================================
Exercise 8.5.2
============================================================
-/

theorem exercise_8_5_2 :
    (IsReflexive relA
      ∧ IsAntisymmetric relA
      ∧ ¬ IsTransitive relA)
    ∧
    (IsReflexive relB
      ∧ IsTransitive relB
      ∧ ¬ IsAntisymmetric relB)
    ∧
    (IsAntisymmetric relC
      ∧ IsTransitive relC
      ∧ ¬ IsReflexive relC) := by

  exact
    ⟨example_a,
      example_b,
      example_c⟩

end TaoExercise8_5_2
