import Mathlib

namespace TaoExercise5_2_2

/--
A rational sequence is bounded if there exists a rational number `M`
such that every term has absolute value at most `M`.
-/
def IsBoundedSeq (a : ℕ → ℚ) : Prop :=
  ∃ M : ℚ, ∀ n : ℕ, |a n| ≤ M


/--
Two sequences are eventually `ε`-close if, from some index onward,

    |a n - b n| ≤ ε.
-/
def EventuallyEpsilonClose
    (a b : ℕ → ℚ)
    (ε : ℚ) : Prop :=
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
Absolute difference is symmetric.
-/
theorem abs_sub_symm
    (x y : ℚ) :
    |x - y| = |y - x| := by

  have h :
      y - x = -(x - y) := by
    ring

  rw [h]

  exact (abs_neg (x - y)).symm


/--
Eventually `ε`-close is symmetric.
-/
theorem eventuallyEpsilonClose_symm
    {a b : ℕ → ℚ}
    {ε : ℚ}
    (h : EventuallyEpsilonClose a b ε) :
    EventuallyEpsilonClose b a ε := by

  obtain ⟨N, hN⟩ := h

  refine ⟨N, ?_⟩

  intro n hn

  have hab :
      |a n - b n| ≤ ε :=
    hN n hn

  rw [abs_sub_symm]

  exact hab


/--
One direction of Exercise 5.2.2.

If `a` is bounded and `a` and `b` are eventually `ε`-close,
then `b` is bounded.
-/
theorem bounded_of_eventually_epsilon_close
    {a b : ℕ → ℚ}
    {ε : ℚ}
    (hε : 0 < ε)
    (hclose : EventuallyEpsilonClose a b ε)
    (ha : IsBoundedSeq a) :
    IsBoundedSeq b := by

  /-
  Since `a` is bounded, choose M₁ such that

      |a n| ≤ M₁

  for every n.
  -/
  obtain ⟨M₁, hM₁⟩ := ha

  /-
  Since a and b are eventually ε-close, choose N such that

      |a n - b n| ≤ ε

  whenever n ≥ N.
  -/
  obtain ⟨N, hN⟩ := hclose

  /-
  The finite prefix b 0, ..., b (N-1) is bounded.
  -/
  obtain ⟨M₂, hM₂⟩ :=
    finite_prefix_bounded b N

  /-
  A bound for the whole sequence.
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

    have hcloseAB :
        |a n - b n| ≤ ε :=
      hN n hnN

    have hcloseBA :
        |b n - a n| ≤ ε := by
      rw [abs_sub_symm]
      exact hcloseAB

    have haBound :
        |a n| ≤ M₁ :=
      hM₁ n

    /-
    b_n = (b_n - a_n) + a_n.
    -/
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
Exercise 5.2.2.

Let ε > 0. If two rational sequences are eventually ε-close,
then one is bounded iff the other is bounded.
-/
theorem exercise_5_2_2
    (a b : ℕ → ℚ)
    (ε : ℚ)
    (hε : 0 < ε)
    (hclose : EventuallyEpsilonClose a b ε) :
    IsBoundedSeq a ↔ IsBoundedSeq b := by

  constructor

  /-
  a bounded -> b bounded.
  -/
  · intro ha

    exact bounded_of_eventually_epsilon_close
      hε
      hclose
      ha

  /-
  b bounded -> a bounded.

  Use symmetry of eventual ε-closeness.
  -/
  · intro hb

    have hclose' :
        EventuallyEpsilonClose b a ε :=
      eventuallyEpsilonClose_symm hclose

    exact bounded_of_eventually_epsilon_close
      hε
      hclose'
      hb

end TaoExercise5_2_2
