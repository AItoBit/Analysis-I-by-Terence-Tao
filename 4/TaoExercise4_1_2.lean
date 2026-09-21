import Mathlib

namespace TaoExercise4_1_2

/--
A raw integer representation.
The pair `(a,b)` represents the formal difference `a - b`.
-/
structure RawInt where
  pos : ℕ
  neg : ℕ

/--
Tao's equality relation on raw integer representatives:

    (a,b) ~ (c,d)  iff  a + d = c + b.
-/
def IntEq (x y : RawInt) : Prop :=
  x.pos + y.neg = y.pos + x.neg

infix:50 " ≈ " => IntEq

/--
Negation of a raw integer representative:

    -(a - b) = b - a.
-/
def rawNeg (x : RawInt) : RawInt :=
  ⟨x.neg, x.pos⟩

prefix:75 "－" => rawNeg


/--
Exercise 4.1.2.

Negation is well-defined with respect to Tao's equality relation.
-/
theorem neg_well_defined
    {x y : RawInt}
    (h : x ≈ y) :
    －x ≈ －y := by

  unfold IntEq at h
  unfold IntEq
  unfold rawNeg

  calc
    x.neg + y.pos
        = y.pos + x.neg := by
            exact Nat.add_comm _ _

    _ = x.pos + y.neg := by
          exact h.symm

    _ = y.neg + x.pos := by
          exact Nat.add_comm _ _


/--
Same statement written directly with four natural numbers.
-/
theorem neg_well_defined_explicit
    (a b a' b' : ℕ)
    (h : a + b' = a' + b) :
    b + a' = b' + a := by

  calc
    b + a'
        = a' + b := by
            exact Nat.add_comm _ _

    _ = a + b' := by
          exact h.symm

    _ = b' + a := by
          exact Nat.add_comm _ _

end TaoExercise4_1_2
