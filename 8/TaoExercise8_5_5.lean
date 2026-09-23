import Mathlib

namespace TaoExercise8_5_5

universe u v

/-!
============================================================
Basic relation properties
============================================================
-/

def IsReflexive
    {α : Type u}
    (r : α → α → Prop) : Prop :=
  ∀ x : α, r x x


def IsAntisymmetric
    {α : Type u}
    (r : α → α → Prop) : Prop :=
  ∀ x y : α,
    r x y →
    r y x →
    x = y


def IsTransitive
    {α : Type u}
    (r : α → α → Prop) : Prop :=
  ∀ x y z : α,
    r x y →
    r y z →
    r x z


def IsTotal
    {α : Type u}
    (r : α → α → Prop) : Prop :=
  ∀ x y : α,
    r x y ∨ r y x


/-!
============================================================
The relation induced by f
============================================================

    x ≤ₓ y  ↔  f x < f y ∨ x = y
-/

def PullbackOrder
    {X : Type u}
    {Y : Type v}
    [PartialOrder Y]
    (f : X → Y)
    (x y : X) : Prop :=
  f x < f y ∨ x = y


/-!
============================================================
Reflexivity
============================================================
-/

theorem pullback_reflexive
    {X : Type u}
    {Y : Type v}
    [PartialOrder Y]
    (f : X → Y) :
    IsReflexive (PullbackOrder f) := by

  intro x

  right

  rfl


/-!
============================================================
Antisymmetry
============================================================
-/

theorem pullback_antisymmetric
    {X : Type u}
    {Y : Type v}
    [PartialOrder Y]
    (f : X → Y) :
    IsAntisymmetric (PullbackOrder f) := by

  intro x y hxy hyx

  rcases hxy with hxy | hxy

  · rcases hyx with hyx | hyx

    · have hfalse : False := by
        exact lt_asymm hxy hyx

      exact False.elim hfalse

    · exact hyx.symm

  · exact hxy


/-!
============================================================
Transitivity
============================================================
-/

theorem pullback_transitive
    {X : Type u}
    {Y : Type v}
    [PartialOrder Y]
    (f : X → Y) :
    IsTransitive (PullbackOrder f) := by

  intro x y z hxy hyz

  rcases hxy with hxy | hxy

  · rcases hyz with hyz | hyz

    · left

      exact lt_trans hxy hyz

    · subst z

      left

      exact hxy

  · subst y

    exact hyz


/-!
============================================================
Therefore it is a partial order relation
============================================================
-/

theorem pullback_is_partial_order
    {X : Type u}
    {Y : Type v}
    [PartialOrder Y]
    (f : X → Y) :
    IsReflexive (PullbackOrder f)
      ∧
    IsAntisymmetric (PullbackOrder f)
      ∧
    IsTransitive (PullbackOrder f) := by

  exact
    ⟨pullback_reflexive f,
      pullback_antisymmetric f,
      pullback_transitive f⟩


/-!
============================================================
A total order on Y is NOT sufficient
============================================================

Take X = Y = ℝ and f(x) = 0.
Then 2 and 3 are incomparable.
-/

def constantZero (_x : ℝ) : ℝ :=
  0


theorem constant_example_not_total :
    ¬ IsTotal (PullbackOrder constantZero) := by

  intro htotal

  have h :=
    htotal (2 : ℝ) (3 : ℝ)

  rcases h with h23 | h32

  · unfold PullbackOrder constantZero at h23

    rcases h23 with hlt | heq

    · norm_num at hlt

    · norm_num at heq

  · unfold PullbackOrder constantZero at h32

    rcases h32 with hlt | heq

    · norm_num at hlt

    · norm_num at heq


/-!
============================================================
Why injectivity is sufficient
============================================================

If Y is totally ordered and f is injective, then for
x ≠ y we necessarily have f x ≠ f y, and therefore
either

    f x < f y

or

    f y < f x.
-/

theorem pullback_total_of_injective
    {X : Type u}
    {Y : Type v}
    [LinearOrder Y]
    (f : X → Y)
    (hf : Function.Injective f) :
    IsTotal (PullbackOrder f) := by

  intro x y

  by_cases hxy : x = y

  · left

    right

    exact hxy

  · have hfxfy :
        f x ≠ f y := by

      intro h

      apply hxy

      exact hf h

    rcases lt_or_gt_of_ne hfxfy with hlt | hgt

    · left

      left

      exact hlt

    · right

      left

      exact hgt


/-!
============================================================
Injectivity is also necessary
============================================================

If the induced relation is total, two different
points cannot have the same f-value.
-/

theorem injective_of_pullback_total
    {X : Type u}
    {Y : Type v}
    [PartialOrder Y]
    (f : X → Y)
    (htotal : IsTotal (PullbackOrder f)) :
    Function.Injective f := by

  intro x y hfxfy

  by_contra hxy

  have htotalXY :
      PullbackOrder f x y ∨
      PullbackOrder f y x := by

    exact htotal x y

  rcases htotalXY with hrel | hrel

  · rcases hrel with hlt | heq

    · rw [hfxfy] at hlt

      exact (lt_irrefl (f y)) hlt

    · exact hxy heq

  · rcases hrel with hlt | heq

    · rw [hfxfy] at hlt

      exact (lt_irrefl (f y)) hlt

    · exact hxy heq.symm


/-!
============================================================
Characterization for a totally ordered codomain
============================================================

When Y is linearly ordered:

    PullbackOrder f is total ↔ f is injective.
-/

theorem pullback_total_iff_injective
    {X : Type u}
    {Y : Type v}
    [LinearOrder Y]
    (f : X → Y) :
    IsTotal (PullbackOrder f)
      ↔
    Function.Injective f := by

  constructor

  · intro htotal

    exact injective_of_pullback_total
      f
      htotal

  · intro hf

    exact pullback_total_of_injective
      f
      hf


/-!
============================================================
Exercise 8.5.5
============================================================
-/

theorem exercise_8_5_5_partial_order
    {X : Type u}
    {Y : Type v}
    [PartialOrder Y]
    (f : X → Y) :
    IsReflexive (PullbackOrder f)
      ∧
    IsAntisymmetric (PullbackOrder f)
      ∧
    IsTransitive (PullbackOrder f) := by

  exact pullback_is_partial_order f


theorem exercise_8_5_5_total_characterization
    {X : Type u}
    {Y : Type v}
    [LinearOrder Y]
    (f : X → Y) :
    IsTotal (PullbackOrder f)
      ↔
    Function.Injective f := by

  exact pullback_total_iff_injective f

end TaoExercise8_5_5
