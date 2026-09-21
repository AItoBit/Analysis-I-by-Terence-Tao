import Mathlib

namespace TaoExercise5_3_2

/-!
============================================================
Basic definitions
============================================================
-/

/--
A rational sequence is Cauchy if, for every ε > 0,
all sufficiently late terms are ε-close.
-/
def IsCauchySeq (a : ℕ → ℚ) : Prop :=
  ∀ ε : ℚ, 0 < ε →
    ∃ N : ℕ, ∀ j k : ℕ,
      N ≤ j →
      N ≤ k →
      |a j - a k| ≤ ε


/--
A rational sequence is bounded if there exists M such that

    |a n| ≤ M

for every n.
-/
def IsBoundedSeq (a : ℕ → ℚ) : Prop :=
  ∃ M : ℚ, ∀ n : ℕ, |a n| ≤ M


/--
A formal real number is represented by a Cauchy sequence.
-/
structure CauchySeq where
  seq : ℕ → ℚ
  isCauchy : IsCauchySeq seq


/-!
============================================================
Finite sequences are bounded
============================================================
-/

theorem finite_prefix_bounded
    (a : ℕ → ℚ) :
    ∀ N : ℕ,
      ∃ M : ℚ, ∀ n : ℕ,
        n < N → |a n| ≤ M := by

  intro N

  induction N with

  | zero =>
      refine ⟨0, ?_⟩
      intro n hn
      omega

  | succ N ih =>
      obtain ⟨M, hM⟩ := ih

      refine ⟨max M |a N|, ?_⟩

      intro n hn

      by_cases hEq : n = N

      · subst n
        exact le_max_right M |a N|

      · have hlt : n < N := by
          omega

        exact le_trans
          (hM n hlt)
          (le_max_left M |a N|)


/-!
============================================================
Every Cauchy sequence is bounded
============================================================
-/

theorem cauchy_seq_bounded
    (a : ℕ → ℚ)
    (ha : IsCauchySeq a) :
    IsBoundedSeq a := by

  /-
  Apply the Cauchy property with ε = 1.
  -/
  obtain ⟨N, hN⟩ :=
    ha 1 (by norm_num : (0 : ℚ) < 1)

  /-
  Bound the finite prefix.
  -/
  obtain ⟨M, hM⟩ :=
    finite_prefix_bounded a N

  /-
  A bound for the whole sequence.
  -/
  let B : ℚ :=
    max M (1 + |a N|)

  refine ⟨B, ?_⟩

  intro n

  by_cases hn : n < N

  /-
  Finite prefix.
  -/
  · have hprefix :
        |a n| ≤ M :=
      hM n hn

    exact le_trans
      hprefix
      (le_max_left M (1 + |a N|))

  /-
  Tail.
  -/
  · have hnN :
        N ≤ n := by
      omega

    have hclose :
        |a n - a N| ≤ 1 := by
      exact hN n N hnN (le_refl N)

    have hrewrite :
        a n = (a n - a N) + a N := by
      ring

    rw [hrewrite]

    calc
      |(a n - a N) + a N|
          ≤ |a n - a N| + |a N| := by
              exact abs_add_le
                (a n - a N)
                (a N)

      _ ≤ 1 + |a N| := by
            linarith

      _ ≤ B := by
            exact le_max_right
              M
              (1 + |a N|)


/-!
============================================================
Pointwise product
============================================================
-/

/--
The pointwise product of two sequences.
-/
def seqMul
    (a b : ℕ → ℚ) :
    ℕ → ℚ :=
  fun n => a n * b n


/-!
============================================================
Proposition 5.3.10

The product of two Cauchy sequences is Cauchy.
============================================================
-/

theorem mul_cauchy
    (a b : ℕ → ℚ)
    (ha : IsCauchySeq a)
    (hb : IsCauchySeq b) :
    IsCauchySeq (seqMul a b) := by

  /-
  Both Cauchy sequences are bounded.
  -/
  obtain ⟨Ma, hMa⟩ :=
    cauchy_seq_bounded a ha

  obtain ⟨Mb, hMb⟩ :=
    cauchy_seq_bounded b hb

  /-
  Replace the bounds by strictly positive bounds.

      A = max Ma 1
      B = max Mb 1.
  -/
  let A : ℚ := max Ma 1
  let B : ℚ := max Mb 1

  have hApos :
      0 < A := by
    dsimp [A]
    exact lt_of_lt_of_le
      (by norm_num : (0 : ℚ) < 1)
      (le_max_right Ma 1)

  have hBpos :
      0 < B := by
    dsimp [B]
    exact lt_of_lt_of_le
      (by norm_num : (0 : ℚ) < 1)
      (le_max_right Mb 1)

  have hAbound :
      ∀ n : ℕ, |a n| ≤ A := by
    intro n

    exact le_trans
      (hMa n)
      (le_max_left Ma 1)

  have hBbound :
      ∀ n : ℕ, |b n| ≤ B := by
    intro n

    exact le_trans
      (hMb n)
      (le_max_left Mb 1)

  /-
  Now prove the Cauchy condition for the product.
  -/
  intro ε hε

  /-
  We want the a-sequence to vary by at most

      ε / (2B),

  because that error will later be multiplied by B.
  -/
  have hEpsB :
      0 < ε / (2 * B) := by
    apply div_pos hε
    exact mul_pos (by norm_num) hBpos

  /-
  Similarly for b.
  -/
  have hEpsA :
      0 < ε / (2 * A) := by
    apply div_pos hε
    exact mul_pos (by norm_num) hApos

  obtain ⟨Na, hNa⟩ :=
    ha (ε / (2 * B)) hEpsB

  obtain ⟨Nb, hNb⟩ :=
    hb (ε / (2 * A)) hEpsA

  refine ⟨max Na Nb, ?_⟩

  intro j k hj hk

  have hNaj :
      Na ≤ j := by
    exact le_trans
      (le_max_left Na Nb)
      hj

  have hNak :
      Na ≤ k := by
    exact le_trans
      (le_max_left Na Nb)
      hk

  have hNbj :
      Nb ≤ j := by
    exact le_trans
      (le_max_right Na Nb)
      hj

  have hNbk :
      Nb ≤ k := by
    exact le_trans
      (le_max_right Na Nb)
      hk

  have haDiff :
      |a j - a k| ≤ ε / (2 * B) :=
    hNa j k hNaj hNak

  have hbDiff :
      |b j - b k| ≤ ε / (2 * A) :=
    hNb j k hNbj hNbk

  /-
  Bounds for individual terms.
  -/
  have haJ :
      |a j| ≤ A :=
    hAbound j

  have hbK :
      |b k| ≤ B :=
    hBbound k

  /-
  First error term:

      |a_j| |b_j-b_k| ≤ ε/2.
  -/
  have hterm1 :
      |a j| * |b j - b k| ≤ ε / 2 := by

    calc
      |a j| * |b j - b k|
          ≤ A * |b j - b k| := by
              exact mul_le_mul_of_nonneg_right
                haJ
                (abs_nonneg (b j - b k))

      _ ≤ A * (ε / (2 * A)) := by
            exact mul_le_mul_of_nonneg_left
              hbDiff
              (le_of_lt hApos)

      _ = ε / 2 := by
            field_simp [ne_of_gt hApos]


  /-
  Second error term:

      |b_k| |a_j-a_k| ≤ ε/2.
  -/
  have hterm2 :
      |b k| * |a j - a k| ≤ ε / 2 := by

    calc
      |b k| * |a j - a k|
          ≤ B * |a j - a k| := by
              exact mul_le_mul_of_nonneg_right
                hbK
                (abs_nonneg (a j - a k))

      _ ≤ B * (ε / (2 * B)) := by
            exact mul_le_mul_of_nonneg_left
              haDiff
              (le_of_lt hBpos)

      _ = ε / 2 := by
            field_simp [ne_of_gt hBpos]


  /-
  Algebraic decomposition:

      a_j b_j - a_k b_k
        =
      a_j (b_j-b_k)
        +
      b_k (a_j-a_k).
  -/
  have hdecomp :
      a j * b j - a k * b k
        =
      a j * (b j - b k)
        +
      b k * (a j - a k) := by
    ring

  unfold seqMul

  rw [hdecomp]

  calc
    |a j * (b j - b k)
        +
      b k * (a j - a k)|
        ≤
      |a j * (b j - b k)|
        +
      |b k * (a j - a k)| := by
          exact abs_add_le
            (a j * (b j - b k))
            (b k * (a j - a k))

    _ =
      |a j| * |b j - b k|
        +
      |b k| * |a j - a k| := by
          rw [abs_mul, abs_mul]

    _ ≤ ε / 2 + ε / 2 := by
          exact add_le_add hterm1 hterm2

    _ = ε := by
          ring


/-!
The product of two formal real numbers is therefore represented
by the pointwise product of their Cauchy sequences.
-/

def cauchyMul
    (x y : CauchySeq) :
    CauchySeq where
  seq := seqMul x.seq y.seq
  isCauchy :=
    mul_cauchy
      x.seq
      y.seq
      x.isCauchy
      y.isCauchy


/--
Exercise 5.3.2 / Proposition 5.3.10.
-/
theorem proposition_5_3_10
    (x y : CauchySeq) :
    IsCauchySeq
      (fun n => x.seq n * y.seq n) := by

  exact mul_cauchy
    x.seq
    y.seq
    x.isCauchy
    y.isCauchy

end TaoExercise5_3_2
