import Mathlib

namespace TaoExercise3_6_7

open Set
open Function

universe u v

variable {α : Type u} {β : Type v}

/--
Cardinality of a finite set.
-/
noncomputable def finiteSetCard
    (A : Set α)
    (hA : A.Finite) : ℕ :=
  @Fintype.card A hA.fintype


/--
Exercise 3.6.7.

For finite sets A and B,

there exists an injection A → B
iff
#A ≤ #B.
-/
theorem exercise_3_6_7
    (A : Set α)
    (B : Set β)
    (hA : A.Finite)
    (hB : B.Finite) :
    (∃ f : A → B, Function.Injective f)
      ↔
    finiteSetCard A hA ≤ finiteSetCard B hB := by

  classical

  letI : Fintype A := hA.fintype
  letI : Fintype B := hB.fintype

  constructor

  /-
  Forward direction:

  If there exists an injection A → B,
  then #A ≤ #B.
  -/
  · rintro ⟨f, hf⟩

    change Fintype.card A ≤ Fintype.card B

    exact Fintype.card_le_of_injective f hf


  /-
  Reverse direction:

  Suppose #A ≤ #B.
  We identify

      A ≃ Fin (#A)
      B ≃ Fin (#B)

  and use the natural inclusion

      Fin (#A) → Fin (#B).
  -/
  · intro hcard

    change Fintype.card A ≤ Fintype.card B at hcard

    let eA : A ≃ Fin (Fintype.card A) :=
      Fintype.equivFin A

    let eB : B ≃ Fin (Fintype.card B) :=
      Fintype.equivFin B

    /-
    Inclusion Fin (#A) → Fin (#B).
    -/
    let inc :
        Fin (Fintype.card A) →
        Fin (Fintype.card B) :=
      fun i =>
        ⟨i.val, lt_of_lt_of_le i.isLt hcard⟩

    /-
    Define

        A → Fin(#A) → Fin(#B) → B.
    -/
    let f : A → B :=
      fun a =>
        eB.symm (inc (eA a))

    refine ⟨f, ?_⟩

    /-
    Prove f is injective.
    -/
    intro a₁ a₂ hEq

    /-
    Since eB⁻¹ is injective:
    -/
    have hFin :
        inc (eA a₁) = inc (eA a₂) := by
      exact eB.symm.injective hEq

    /-
    `inc` preserves the underlying natural number.
    -/
    have hVal :
        (eA a₁).val = (eA a₂).val := by
      simpa [inc] using congrArg Fin.val hFin

    /-
    Hence the Fin values themselves are equal.
    -/
    have hEA :
        eA a₁ = eA a₂ := by
      apply Fin.ext
      exact hVal

    /-
    Finally, eA is injective.
    -/
    exact eA.injective hEA

end TaoExercise3_6_7
