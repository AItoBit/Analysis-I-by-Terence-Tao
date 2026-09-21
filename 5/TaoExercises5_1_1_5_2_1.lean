import Mathlib

namespace TaoExercises5_1_1_5_2_1

def IsCauchySeq (a : ℕ → ℚ) : Prop :=
  ∀ ε : ℚ, 0 < ε →
    ∃ N : ℕ, ∀ j k : ℕ,
      N ≤ j →
      N ≤ k →
      |a j - a k| ≤ ε

def IsBoundedSeq (a : ℕ → ℚ) : Prop :=
  ∃ B : ℚ, ∀ n : ℕ, |a n| ≤ B

def EventuallyClose (a b : ℕ → ℚ) : Prop :=
  ∀ ε : ℚ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ,
      N ≤ n →
      |a n - b n| ≤ ε


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


theorem cauchy_seq_bounded
    (a : ℕ → ℚ)
    (ha : IsCauchySeq a) :
    IsBoundedSeq a := by

  obtain ⟨N, hN⟩ :=
    ha 1 (by norm_num : (0 : ℚ) < 1)

  obtain ⟨M, hM⟩ :=
    finite_prefix_bounded a N

  let B : ℚ :=
    max M (1 + |a N|)

  refine ⟨B, ?_⟩

  intro n

  by_cases hn : n < N

  · have hprefix :
        |a n| ≤ M :=
      hM n hn

    exact le_trans
      hprefix
      (le_max_left M (1 + |a N|))

  · have hnN :
        N ≤ n := by
      omega

    have hclose :
        |a n - a N| ≤ 1 := by
      exact hN n N hnN (le_refl N)

    have hrewrite :
        a n =
          (a n - a N) + a N := by
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


theorem exercise_5_1_1
    (a : ℕ → ℚ) :
    IsCauchySeq a →
    IsBoundedSeq a := by

  intro ha
  exact cauchy_seq_bounded a ha


theorem abs_sub_symm
    (x y : ℚ) :
    |x - y| = |y - x| := by

  have h :
      y - x = -(x - y) := by
    ring

  rw [h]

  exact (abs_neg (x - y)).symm


theorem eventuallyClose_symm
    {a b : ℕ → ℚ}
    (h : EventuallyClose a b) :
    EventuallyClose b a := by

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


theorem cauchy_of_eventuallyClose
    {a b : ℕ → ℚ}
    (hclose : EventuallyClose a b)
    (ha : IsCauchySeq a) :
    IsCauchySeq b := by

  intro ε hε

  have heps3 :
      0 < ε / 3 := by
    linarith

  obtain ⟨N₁, hN₁⟩ :=
    hclose (ε / 3) heps3

  obtain ⟨N₂, hN₂⟩ :=
    ha (ε / 3) heps3

  refine ⟨max N₁ N₂, ?_⟩

  intro j k hj hk

  have hN₁j :
      N₁ ≤ j := by
    exact le_trans
      (le_max_left N₁ N₂)
      hj

  have hN₁k :
      N₁ ≤ k := by
    exact le_trans
      (le_max_left N₁ N₂)
      hk

  have hN₂j :
      N₂ ≤ j := by
    exact le_trans
      (le_max_right N₁ N₂)
      hj

  have hN₂k :
      N₂ ≤ k := by
    exact le_trans
      (le_max_right N₁ N₂)
      hk

  have hajbj :
      |a j - b j| ≤ ε / 3 :=
    hN₁ j hN₁j

  have hakbk :
      |a k - b k| ≤ ε / 3 :=
    hN₁ k hN₁k

  have hajak :
      |a j - a k| ≤ ε / 3 :=
    hN₂ j k hN₂j hN₂k

  have hbjaj :
      |b j - a j| ≤ ε / 3 := by
    rw [abs_sub_symm]
    exact hajbj

  have hdecomp :
      b j - b k =
        (b j - a j)
          +
        (a j - a k)
          +
        (a k - b k) := by
    ring

  rw [hdecomp]

  calc
    |(b j - a j)
        +
      (a j - a k)
        +
      (a k - b k)|
        ≤
      |(b j - a j)
        +
       (a j - a k)|
        +
      |a k - b k| := by
          exact abs_add_le
            ((b j - a j) + (a j - a k))
            (a k - b k)

    _ ≤
      (|b j - a j| + |a j - a k|)
        +
      |a k - b k| := by

        have htri :
            |(b j - a j) + (a j - a k)|
              ≤
            |b j - a j| + |a j - a k| :=
          abs_add_le
            (b j - a j)
            (a j - a k)

        linarith

    _ ≤
      (ε / 3 + ε / 3) + ε / 3 := by
        linarith

    _ = ε := by
          ring


theorem exercise_5_2_1
    (a b : ℕ → ℚ)
    (hclose : EventuallyClose a b) :
    IsCauchySeq a ↔ IsCauchySeq b := by

  constructor

  · intro ha
    exact cauchy_of_eventuallyClose
      hclose
      ha

  · intro hb

    have hclose' :
        EventuallyClose b a :=
      eventuallyClose_symm hclose

    exact cauchy_of_eventuallyClose
      hclose'
      hb

end TaoExercises5_1_1_5_2_1
