import Mathlib

namespace TaoExercise3_4_8

universe u

/-
A minimal axiomatic setup.

`Obj` is the universe of objects/sets.
`Mem x A` means x ∈ A.
-/
variable {Obj : Type u}

variable (Mem : Obj → Obj → Prop)

/-
Axiom 3.3: pair sets exist.

For any A B, there exists P such that

  x ∈ P ↔ x = A ∨ x = B.
-/
def PairAxiom : Prop :=
  ∀ A B : Obj,
    ∃ P : Obj,
      ∀ x : Obj,
        Mem x P ↔ x = A ∨ x = B

/-
Axiom 3.11: union of a set exists.

For any family-set F, there exists U such that

  x ∈ U ↔ ∃ S, S ∈ F ∧ x ∈ S.
-/
def UnionAxiom : Prop :=
  ∀ F : Obj,
    ∃ U : Obj,
      ∀ x : Obj,
        Mem x U ↔ ∃ S : Obj, Mem S F ∧ Mem x S

/-
Axiom 3.4, the binary union axiom we want to derive.

For any A B, there exists U such that

  x ∈ U ↔ x ∈ A ∨ x ∈ B.
-/
def BinaryUnionAxiom : Prop :=
  ∀ A B : Obj,
    ∃ U : Obj,
      ∀ x : Obj,
        Mem x U ↔ Mem x A ∨ Mem x B


/--
Exercise 3.4.8.

Axiom 3.4 follows from the pair-set axiom and the union axiom.

Conceptually:
  form {A,B},
  then take ⋃{A,B}.
-/
theorem axiom_3_4_from_3_3_and_3_11
    (hPair : PairAxiom Mem)
    (hUnion : UnionAxiom Mem) :
    BinaryUnionAxiom Mem := by

  intro A B

  /-
  By Axiom 3.3, form the pair set {A,B}.
  -/
  obtain ⟨P, hP⟩ := hPair A B

  /-
  By Axiom 3.11, form ⋃P.
  -/
  obtain ⟨U, hU⟩ := hUnion P

  refine ⟨U, ?_⟩

  intro x

  constructor

  /-
  If x ∈ ⋃{A,B}, then there exists S ∈ {A,B}
  such that x ∈ S.

  Since S = A or S = B, we get x ∈ A or x ∈ B.
  -/
  · intro hx

    have hx' :
        ∃ S : Obj, Mem S P ∧ Mem x S :=
      (hU x).1 hx

    obtain ⟨S, hSP, hxS⟩ := hx'

    have hS :
        S = A ∨ S = B :=
      (hP S).1 hSP

    rcases hS with hSA | hSB

    · left
      simpa [hSA] using hxS

    · right
      simpa [hSB] using hxS

  /-
  Conversely, if x ∈ A or x ∈ B,
  then choose S = A or S = B respectively.
  -/
  · intro hx

    apply (hU x).2

    rcases hx with hxA | hxB

    · refine ⟨A, ?_, hxA⟩
      exact (hP A).2 (Or.inl rfl)

    · refine ⟨B, ?_, hxB⟩
      exact (hP B).2 (Or.inr rfl)

end TaoExercise3_4_8
