import Mathlib

namespace TaoExercise5_3_1

/-!
============================================================
Cauchy sequences of rational numbers
============================================================
-/

/--
A rational sequence is Cauchy if for every ε > 0,
all sufficiently late terms are ε-close.
-/
def IsCauchySeq (a : ℕ → ℚ) : Prop :=
  ∀ ε : ℚ, 0 < ε →
    ∃ N : ℕ, ∀ j k : ℕ,
      N ≤ j →
      N ≤ k →
      |a j - a k| ≤ ε


/--
A Cauchy sequence together with the proof that it is Cauchy.

This represents Tao's formal limit

    LIM a_n.
-/
structure CauchySeq where
  seq : ℕ → ℚ
  isCauchy : IsCauchySeq seq


/-!
============================================================
Equivalence of Cauchy sequences
============================================================
-/

/--
Two sequences are equivalent if for every ε > 0,
they are eventually ε-close:

    ∀ ε > 0, ∃ N, ∀ n ≥ N,
      |a_n - b_n| ≤ ε.
-/
def SeqEquivalent
    (a b : ℕ → ℚ) : Prop :=
  ∀ ε : ℚ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ,
      N ≤ n →
      |a n - b n| ≤ ε


/--
Equality of formal real numbers represented by Cauchy sequences.
-/
def RealEq
    (x y : CauchySeq) : Prop :=
  SeqEquivalent x.seq y.seq


/-!
A small auxiliary lemma:

    |x-y| = |y-x|.
-/
theorem abs_sub_symm
    (x y : ℚ) :
    |x - y| = |y - x| := by

  have h :
      y - x = -(x - y) := by
    ring

  rw [h]

  exact (abs_neg (x - y)).symm


/-!
============================================================
1. Reflexivity
============================================================
-/

/--
Every Cauchy sequence is equivalent to itself.
-/
theorem seqEquivalent_refl
    (a : ℕ → ℚ) :
    SeqEquivalent a a := by

  intro ε hε

  refine ⟨0, ?_⟩

  intro n hn

  simp

  exact le_of_lt hε


/--
Reflexivity of equality of formal real numbers:

    x = x.
-/
theorem realEq_refl
    (x : CauchySeq) :
    RealEq x x := by

  unfold RealEq

  exact seqEquivalent_refl x.seq


/-!
============================================================
2. Symmetry
============================================================
-/

/--
If a and b are equivalent, then b and a are equivalent.
-/
theorem seqEquivalent_symm
    {a b : ℕ → ℚ}
    (h : SeqEquivalent a b) :
    SeqEquivalent b a := by

  intro ε hε

  obtain ⟨N, hN⟩ :=
    h ε hε

  refine ⟨N, ?_⟩

  intro n hn

  have hab :
      |a n - b n| ≤ ε :=
    hN n hn

  rw [abs_sub_symm]

  exact hab


/--
Symmetry of equality:

    x = y -> y = x.
-/
theorem realEq_symm
    {x y : CauchySeq}
    (hxy : RealEq x y) :
    RealEq y x := by

  unfold RealEq at hxy ⊢

  exact seqEquivalent_symm hxy


/-!
============================================================
3. Transitivity
============================================================
-/

/--
If

    a ~ b
and
    b ~ c,

then

    a ~ c.
-/
theorem seqEquivalent_trans
    {a b c : ℕ → ℚ}
    (hab : SeqEquivalent a b)
    (hbc : SeqEquivalent b c) :
    SeqEquivalent a c := by

  intro ε hε

  /-
  ε / 2 is positive.
  -/
  have heps2 :
      0 < ε / 2 := by
    linarith

  /-
  Since a ~ b, eventually

      |a_n - b_n| ≤ ε/2.
  -/
  obtain ⟨N₁, hN₁⟩ :=
    hab (ε / 2) heps2

  /-
  Since b ~ c, eventually

      |b_n - c_n| ≤ ε/2.
  -/
  obtain ⟨N₂, hN₂⟩ :=
    hbc (ε / 2) heps2

  /-
  Take the larger threshold.
  -/
  refine ⟨max N₁ N₂, ?_⟩

  intro n hn

  have hn₁ :
      N₁ ≤ n := by
    exact le_trans
      (le_max_left N₁ N₂)
      hn

  have hn₂ :
      N₂ ≤ n := by
    exact le_trans
      (le_max_right N₁ N₂)
      hn

  have habn :
      |a n - b n| ≤ ε / 2 :=
    hN₁ n hn₁

  have hbcn :
      |b n - c n| ≤ ε / 2 :=
    hN₂ n hn₂

  /-
  Algebraically,

      a_n - c_n
        =
      (a_n - b_n) + (b_n - c_n).
  -/
  have hdecomp :
      a n - c n =
        (a n - b n) + (b n - c n) := by
    ring

  rw [hdecomp]

  calc
    |(a n - b n) + (b n - c n)|
        ≤
      |a n - b n| + |b n - c n| := by
        exact abs_add_le
          (a n - b n)
          (b n - c n)

    _ ≤ ε / 2 + ε / 2 := by
          exact add_le_add habn hbcn

    _ = ε := by
          ring


/--
Transitivity of equality:

    x = y ->
    y = z ->
    x = z.
-/
theorem realEq_trans
    {x y z : CauchySeq}
    (hxy : RealEq x y)
    (hyz : RealEq y z) :
    RealEq x z := by

  unfold RealEq at hxy hyz ⊢

  exact seqEquivalent_trans hxy hyz


/-!
============================================================
Proposition 5.3.3
============================================================
-/

/--
The equality relation on formal limits satisfies:

1. reflexivity;
2. symmetry;
3. transitivity.
-/
theorem proposition_5_3_3 :
    (∀ x : CauchySeq,
      RealEq x x)
    ∧
    (∀ x y : CauchySeq,
      RealEq x y →
      RealEq y x)
    ∧
    (∀ x y z : CauchySeq,
      RealEq x y →
      RealEq y z →
      RealEq x z) := by

  constructor

  /-
  Reflexivity.
  -/
  · intro x
    exact realEq_refl x

  constructor

  /-
  Symmetry.
  -/
  · intro x y hxy
    exact realEq_symm hxy

  /-
  Transitivity.
  -/
  · intro x y z hxy hyz
    exact realEq_trans hxy hyz

end TaoExercise5_3_1
