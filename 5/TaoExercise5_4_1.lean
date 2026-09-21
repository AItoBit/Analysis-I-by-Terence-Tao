import Mathlib

namespace TaoExercise5_4_1

/-!
============================================================
Basic definitions
============================================================
-/

/--
A rational sequence is Cauchy.
-/
def IsCauchySeq (a : ℕ → ℚ) : Prop :=
  ∀ ε : ℚ, 0 < ε →
    ∃ N : ℕ, ∀ j k : ℕ,
      N ≤ j →
      N ≤ k →
      |a j - a k| ≤ ε


/--
Two rational sequences are equivalent when their difference
converges to zero.
-/
def SeqEquivalent
    (a b : ℕ → ℚ) : Prop :=
  ∀ ε : ℚ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ,
      N ≤ n →
      |a n - b n| ≤ ε


/--
The constant zero sequence.
-/
def zeroSeq : ℕ → ℚ :=
  fun _ => 0


/--
A sequence represents the real number zero when it is
equivalent to the constant zero sequence.
-/
def IsZero (a : ℕ → ℚ) : Prop :=
  SeqEquivalent a zeroSeq


/--
A sequence is eventually positively bounded away from zero.
-/
def IsPositive (a : ℕ → ℚ) : Prop :=
  ∃ c : ℚ,
    0 < c ∧
    ∃ N : ℕ, ∀ n : ℕ,
      N ≤ n →
      c ≤ a n


/--
A sequence is eventually negatively bounded away from zero.
-/
def IsNegative (a : ℕ → ℚ) : Prop :=
  ∃ c : ℚ,
    0 < c ∧
    ∃ N : ℕ, ∀ n : ℕ,
      N ≤ n →
      a n ≤ -c


/--
A formal real number is represented by a Cauchy sequence
of rational numbers.
-/
structure CauchySeq where
  seq : ℕ → ℚ
  isCauchy : IsCauchySeq seq


/-!
============================================================
Zero and positive are incompatible
============================================================
-/

theorem not_zero_and_positive
    {a : ℕ → ℚ} :
    ¬ (IsZero a ∧ IsPositive a) := by

  rintro ⟨hzero, hpos⟩

  obtain ⟨c, hc, N₁, hN₁⟩ := hpos

  have hc2 :
      0 < c / 2 := by
    linarith

  obtain ⟨N₂, hN₂⟩ :=
    hzero (c / 2) hc2

  let N : ℕ := max N₁ N₂

  have hN_ge₁ :
      N₁ ≤ N := by
    exact le_max_left N₁ N₂

  have hN_ge₂ :
      N₂ ≤ N := by
    exact le_max_right N₁ N₂

  have hposN :
      c ≤ a N := by
    exact hN₁ N hN_ge₁

  have hzeroN :
      |a N| ≤ c / 2 := by
    have h :=
      hN₂ N hN_ge₂

    simpa [zeroSeq] using h

  have haN_nonneg :
      0 ≤ a N := by
    linarith

  rw [abs_of_nonneg haN_nonneg] at hzeroN

  linarith


/-!
============================================================
Zero and negative are incompatible
============================================================
-/

theorem not_zero_and_negative
    {a : ℕ → ℚ} :
    ¬ (IsZero a ∧ IsNegative a) := by

  rintro ⟨hzero, hneg⟩

  obtain ⟨c, hc, N₁, hN₁⟩ := hneg

  have hc2 :
      0 < c / 2 := by
    linarith

  obtain ⟨N₂, hN₂⟩ :=
    hzero (c / 2) hc2

  let N : ℕ := max N₁ N₂

  have hN_ge₁ :
      N₁ ≤ N := by
    exact le_max_left N₁ N₂

  have hN_ge₂ :
      N₂ ≤ N := by
    exact le_max_right N₁ N₂

  have hnegN :
      a N ≤ -c := by
    exact hN₁ N hN_ge₁

  have hzeroN :
      |a N| ≤ c / 2 := by
    have h :=
      hN₂ N hN_ge₂

    simpa [zeroSeq] using h

  have haN_nonpos :
      a N ≤ 0 := by
    linarith

  rw [abs_of_nonpos haN_nonpos] at hzeroN

  linarith


/-!
============================================================
Positive and negative are incompatible
============================================================
-/

theorem not_positive_and_negative
    {a : ℕ → ℚ} :
    ¬ (IsPositive a ∧ IsNegative a) := by

  rintro ⟨hpos, hneg⟩

  obtain ⟨c, hc, N₁, hN₁⟩ := hpos
  obtain ⟨d, hd, N₂, hN₂⟩ := hneg

  let N : ℕ := max N₁ N₂

  have hN_ge₁ :
      N₁ ≤ N := by
    exact le_max_left N₁ N₂

  have hN_ge₂ :
      N₂ ≤ N := by
    exact le_max_right N₁ N₂

  have hp :
      c ≤ a N := by
    exact hN₁ N hN_ge₁

  have hn :
      a N ≤ -d := by
    exact hN₂ N hN_ge₂

  linarith


/-!
============================================================
Nonzero implies eventually bounded away from zero.

This formalizes the role of Tao's Lemma 5.3.14.
============================================================
-/

theorem nonzero_eventually_abs_bounded_away
    {a : ℕ → ℚ}
    (ha : IsCauchySeq a)
    (hzero : ¬ IsZero a) :
    ∃ c : ℚ,
      0 < c ∧
      ∃ N : ℕ, ∀ n : ℕ,
        N ≤ n →
        c ≤ |a n| := by

  unfold IsZero at hzero
  unfold SeqEquivalent at hzero

  push Not at hzero

  obtain ⟨ε, hε, hfail⟩ := hzero

  /-
  Failure of equivalence with zero means that,
  no matter how far out we go, we can find a term
  whose absolute value is greater than ε.
  -/
  have hfail' :
      ∀ N : ℕ,
        ∃ n : ℕ,
          N ≤ n ∧
          ε < |a n| := by

    intro N

    obtain ⟨n, hn, hbad⟩ :=
      hfail N

    refine ⟨n, hn, ?_⟩

    simpa [zeroSeq] using hbad

  have heps2 :
      0 < ε / 2 := by
    linarith

  /-
  Use the Cauchy property with ε/2.
  -/
  obtain ⟨N, hCauchy⟩ :=
    ha (ε / 2) heps2

  refine ⟨ε / 2, heps2, N, ?_⟩

  intro n hn

  /-
  Find some k ≥ N with |a k| > ε.
  -/
  obtain ⟨k, hk, hklarge⟩ :=
    hfail' N

  have hclose :
      |a k - a n| ≤ ε / 2 := by
    exact hCauchy k n hk hn

  /-
  Triangle inequality:

      |a k|
        ≤ |a k - a n| + |a n|.
  -/
  have htriangle :
      |a k| ≤ |a k - a n| + |a n| := by

    simpa only [sub_add_cancel] using
      abs_add_le
        (a k - a n)
        (a n)

  /-
  Since

      |a k| > ε
      |a k - a n| ≤ ε/2,

  we obtain

      |a n| ≥ ε/2.
  -/
  linarith


/-!
============================================================
A Cauchy sequence bounded away from zero eventually
has a fixed sign.
============================================================
-/

theorem eventually_positive_or_negative
    {a : ℕ → ℚ}
    (ha : IsCauchySeq a)
    {c : ℚ}
    (hc : 0 < c)
    (hab :
      ∃ N : ℕ, ∀ n : ℕ,
        N ≤ n →
        c ≤ |a n|) :
    IsPositive a ∨ IsNegative a := by

  obtain ⟨N₀, hN₀⟩ := hab

  have hc2 :
      0 < c / 2 := by
    linarith

  /-
  Since a is Cauchy, after N₁ any two terms differ
  by at most c/2.
  -/
  obtain ⟨N₁, hCauchy⟩ :=
    ha (c / 2) hc2

  let N : ℕ := max N₀ N₁

  have hN_ge₀ :
      N₀ ≤ N := by
    exact le_max_left N₀ N₁

  have hN_ge₁ :
      N₁ ≤ N := by
    exact le_max_right N₀ N₁

  have hN_abs :
      c ≤ |a N| := by
    exact hN₀ N hN_ge₀

  /-
  Look at the sign of a N.
  -/
  by_cases hsign : 0 ≤ a N

  /-
  ============================================================
  Positive case
  ============================================================
  -/
  · have hNc :
        c ≤ a N := by
      rw [abs_of_nonneg hsign] at hN_abs
      exact hN_abs

    refine Or.inl ?_

    refine ⟨c / 2, hc2, N, ?_⟩

    intro n hn

    have hnCauchy :
        N₁ ≤ n := by
      exact le_trans hN_ge₁ hn

    have hclose :
        |a n - a N| ≤ c / 2 := by
      exact hCauchy
        n
        N
        hnCauchy
        hN_ge₁

    /-
    From |a n - a N| ≤ c/2 we get

        -(c/2) ≤ a n - a N.
    -/
    have hlower :
        -(c / 2) ≤ a n - a N := by
      exact (abs_le.mp hclose).1

    /-
    Since a N ≥ c,

        a n ≥ c/2.
    -/
    linarith


  /-
  ============================================================
  Negative case
  ============================================================
  -/
  · have hsign' :
        a N < 0 := by
      exact lt_of_not_ge hsign

    have hNc :
        c ≤ -a N := by
      rw [abs_of_neg hsign'] at hN_abs
      exact hN_abs

    refine Or.inr ?_

    refine ⟨c / 2, hc2, N, ?_⟩

    intro n hn

    have hnCauchy :
        N₁ ≤ n := by
      exact le_trans hN_ge₁ hn

    have hclose :
        |a n - a N| ≤ c / 2 := by
      exact hCauchy
        n
        N
        hnCauchy
        hN_ge₁

    /-
    From |a n - a N| ≤ c/2 we get

        a n - a N ≤ c/2.
    -/
    have hupper :
        a n - a N ≤ c / 2 := by
      exact (abs_le.mp hclose).2

    /-
    Since a N ≤ -c,

        a n ≤ -c/2.
    -/
    linarith


/-!
============================================================
At least one of zero / positive / negative holds
============================================================
-/

theorem zero_or_positive_or_negative
    (x : CauchySeq) :
    IsZero x.seq ∨
    IsPositive x.seq ∨
    IsNegative x.seq := by

  by_cases hzero : IsZero x.seq

  /-
  x = 0.
  -/
  · exact Or.inl hzero

  /-
  x ≠ 0.
  -/
  · have hab :
        ∃ c : ℚ,
          0 < c ∧
          ∃ N : ℕ, ∀ n : ℕ,
            N ≤ n →
            c ≤ |x.seq n| :=
      nonzero_eventually_abs_bounded_away
        x.isCauchy
        hzero

    obtain ⟨c, hc, hbound⟩ := hab

    have hsign :
        IsPositive x.seq ∨
        IsNegative x.seq :=
      eventually_positive_or_negative
        x.isCauchy
        hc
        hbound

    exact Or.inr hsign


/-!
============================================================
Proposition 5.4.4

Exactly one of the following is true:

1. x = 0
2. x is positive
3. x is negative
============================================================
-/

theorem proposition_5_4_4
    (x : CauchySeq) :
    (IsZero x.seq ∨
      IsPositive x.seq ∨
      IsNegative x.seq)
    ∧
    ¬ (IsZero x.seq ∧ IsPositive x.seq)
    ∧
    ¬ (IsZero x.seq ∧ IsNegative x.seq)
    ∧
    ¬ (IsPositive x.seq ∧ IsNegative x.seq) := by

  constructor

  /-
  At least one of the three cases holds.
  -/
  · exact zero_or_positive_or_negative x

  constructor

  /-
  Zero and positive cannot both hold.
  -/
  · exact not_zero_and_positive

  constructor

  /-
  Zero and negative cannot both hold.
  -/
  · exact not_zero_and_negative

  /-
  Positive and negative cannot both hold.
  -/
  · exact not_positive_and_negative

end TaoExercise5_4_1
