import Mathlib

namespace TaoExercise3_4_11

open Set

universe u v

variable {X : Type u} {ι : Type v}

/--
First De Morgan law for an indexed family of sets:

    X \ (⋃ α, A α) = ⋂ α, (X \ A α)

The index type is assumed nonempty, corresponding to Tao's
assumption that I is nonempty.
-/
theorem diff_iUnion
    [Nonempty ι]
    (Xset : Set X)
    (A : ι → Set X) :
    Xset \ (⋃ α, A α) = ⋂ α, (Xset \ A α) := by

  classical
  ext x
  constructor

  /-
  x ∈ X \ ⋃ Aα
  →
  x ∈ ⋂ (X \ Aα)
  -/
  · intro hx

    have hxX : x ∈ Xset := hx.1
    have hxNotUnion : x ∉ ⋃ α, A α := hx.2

    rw [Set.mem_iInter]

    intro α

    constructor

    · exact hxX

    · intro hxA

      apply hxNotUnion

      apply Set.mem_iUnion.mpr

      exact ⟨α, hxA⟩

  /-
  x ∈ ⋂ (X \ Aα)
  →
  x ∈ X \ ⋃ Aα
  -/
  · intro hx

    let α₀ : ι :=
      Classical.choice (inferInstance : Nonempty ι)

    have hx₀ :
        x ∈ Xset \ A α₀ := by
      exact Set.mem_iInter.mp hx α₀

    constructor

    /-
    We use nonemptiness of the index set here
    to recover x ∈ X.
    -/
    · exact hx₀.1

    /-
    x cannot belong to any Aα.
    -/
    · intro hxUnion

      obtain ⟨α, hxA⟩ :=
        Set.mem_iUnion.mp hxUnion

      have hxDiff :
          x ∈ Xset \ A α := by
        exact Set.mem_iInter.mp hx α

      exact hxDiff.2 hxA


/--
Second De Morgan law for an indexed family:

    X \ (⋂ α, A α) = ⋃ α, (X \ A α)
-/
theorem diff_iInter
    [Nonempty ι]
    (Xset : Set X)
    (A : ι → Set X) :
    Xset \ (⋂ α, A α) = ⋃ α, (Xset \ A α) := by

  classical
  ext x
  constructor

  /-
  x ∈ X \ ⋂ Aα
  →
  x ∈ ⋃ (X \ Aα)
  -/
  · intro hx

    have hxX : x ∈ Xset := hx.1
    have hxNotInter : x ∉ ⋂ α, A α := hx.2

    by_contra hxNotUnion

    apply hxNotInter

    rw [Set.mem_iInter]

    intro α

    by_contra hxNotA

    apply hxNotUnion

    apply Set.mem_iUnion.mpr

    refine ⟨α, ?_⟩

    exact ⟨hxX, hxNotA⟩

  /-
  x ∈ ⋃ (X \ Aα)
  →
  x ∈ X \ ⋂ Aα
  -/
  · intro hx

    obtain ⟨α, hxDiff⟩ :=
      Set.mem_iUnion.mp hx

    constructor

    · exact hxDiff.1

    · intro hxInter

      have hxA :
          x ∈ A α := by
        exact Set.mem_iInter.mp hxInter α

      exact hxDiff.2 hxA


/--
Exercise 3.4.11: both indexed De Morgan laws.
-/
theorem exercise_3_4_11
    [Nonempty ι]
    (Xset : Set X)
    (A : ι → Set X) :
    (Xset \ (⋃ α, A α) = ⋂ α, (Xset \ A α))
    ∧
    (Xset \ (⋂ α, A α) = ⋃ α, (Xset \ A α)) := by
  constructor
  · exact diff_iUnion Xset A
  · exact diff_iInter Xset A

end TaoExercise3_4_11
