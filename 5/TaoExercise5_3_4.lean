import Mathlib

namespace TaoExercise5_3_4

/--
A rational sequence is bounded if there exists a rational `M`
such that every term has absolute value at most `M`.
-/
def IsBoundedSeq (a : ℕ → ℚ) : Prop :=
  ∃ M : ℚ, ∀ n : ℕ, |a n| ≤ M


/--
Two rational sequences are equivalent if, for every positive ε,
they are eventually ε-close.
-/
def SeqEquivalent
    (a b : ℕ → ℚ) : Prop :=
  ∀ ε : ℚ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ,
      N ≤ n →
      |a n - b n| ≤ ε


/--
Every finite initial segment

    a 0, ..., a (N-1)

is bounded.
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


/--
If `a` is bounded and `a` and `b` are eventually ε-close
for one positive ε, then `b` is bounded.
-/
theorem bounded_of_eventually_close
    {a b : ℕ → ℚ}
    {ε : ℚ}
    (hε : 0 < ε)
    (ha : IsBoundedSeq a)
    (hclose :
      ∃ N : ℕ, ∀ n : ℕ,
        N ≤ n →
        |a n - b n| ≤ ε) :
    IsBoundedSeq b := by

  /-
  Choose a bound M₁ for a.
  -/
  obtain ⟨M₁, hM₁⟩ := ha

  /-
  Choose N after which a and b are ε-close.
  -/
  obtain ⟨N, hN⟩ := hclose

  /-
  Bound the finite prefix of b.
  -/
  obtain ⟨M₂, hM₂⟩ :=
    finite_prefix_bounded b N

  /-
  One global bound for b.
  -/
  let M : ℚ :=
    max M₂ (M₁ + ε)

  refine ⟨M, ?_⟩

  intro n

  by_cases hn : n < N

  /-
  Finite prefix.
  -/
  · have hprefix :
        |b n| ≤ M₂ :=
      hM₂ n hn

    exact le_trans
      hprefix
      (le_max_left M₂ (M₁ + ε))

  /-
  Tail.
  -/
  · have hnN :
        N ≤ n := by
      omega

    have hab :
        |a n - b n| ≤ ε :=
      hN n hnN

    have hba :
        |b n - a n| ≤ ε := by
      have h :
          b n - a n = -(a n - b n) := by
        ring
      rw [h, abs_neg]
      exact hab

    have haBound :
        |a n| ≤ M₁ :=
      hM₁ n

    have hrewrite :
        b n = (b n - a n) + a n := by
      ring

    rw [hrewrite]

    calc
      |(b n - a n) + a n|
          ≤ |b n - a n| + |a n| := by
              exact abs_add_le
                (b n - a n)
                (a n)

      _ ≤ ε + M₁ := by
            linarith

      _ = M₁ + ε := by
            ring

      _ ≤ M := by
            exact le_max_right
              M₂
              (M₁ + ε)


/--
Exercise 5.3.4.

If `a` is bounded and `b` is equivalent to `a`,
then `b` is bounded.
-/
theorem exercise_5_3_4
    (a b : ℕ → ℚ)
    (ha : IsBoundedSeq a)
    (hab : SeqEquivalent a b) :
    IsBoundedSeq b := by

  /-
  Since equivalent sequences are eventually ε-close
  for every positive ε, use ε = 1.
  -/
  have hε :
      (0 : ℚ) < 1 := by
    norm_num

  obtain ⟨N, hN⟩ :=
    hab 1 hε

  exact bounded_of_eventually_close
    hε
    ha
    ⟨N, hN⟩

end TaoExercise5_3_4
