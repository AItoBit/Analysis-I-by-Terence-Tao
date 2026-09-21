import Mathlib

namespace TaoExercise5_5_4

/-!
============================================================
Basic definitions
============================================================
-/

/--
A rational sequence is Cauchy.
-/
def IsCauchySeq (q : ℕ → ℚ) : Prop :=
  ∀ ε : ℚ, 0 < ε →
    ∃ N : ℕ, ∀ n n' : ℕ,
      N ≤ n →
      N ≤ n' →
      |q n - q n'| ≤ ε


/--
A rational sequence converges to the real number `S`.
-/
def ConvergesTo
    (q : ℕ → ℚ)
    (S : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ,
      N ≤ n →
      |(q n : ℝ) - S| < ε


/-!
============================================================
Auxiliary limit lemmas
============================================================
-/

/--
If a sequence converges to `S` and is eventually bounded above by `c`,
then `S ≤ c`.
-/
theorem limit_le_of_eventually_le
    (q : ℕ → ℚ)
    (S c : ℝ)
    (hlim : ConvergesTo q S)
    (N₀ : ℕ)
    (hbound :
      ∀ n : ℕ, N₀ ≤ n →
        (q n : ℝ) ≤ c) :
    S ≤ c := by

  by_contra h

  have hcS :
      c < S := by
    exact lt_of_not_ge h

  let ε : ℝ :=
    (S - c) / 2

  have hε :
      0 < ε := by
    dsimp [ε]
    linarith

  obtain ⟨N₁, hN₁⟩ :=
    hlim ε hε

  let N : ℕ :=
    max N₀ N₁

  have hN0 :
      N₀ ≤ N := by
    exact le_max_left N₀ N₁

  have hN1 :
      N₁ ≤ N := by
    exact le_max_right N₀ N₁

  have hclose :
      |(q N : ℝ) - S| < ε := by
    exact hN₁ N hN1

  have hlower :
      -ε < (q N : ℝ) - S := by
    exact (abs_lt.mp hclose).1

  have hq_gt :
      c < (q N : ℝ) := by
    dsimp [ε] at hlower
    linarith

  have hq_le :
      (q N : ℝ) ≤ c :=
    hbound N hN0

  linarith


/--
If a sequence converges to `S` and is eventually bounded below by `c`,
then `c ≤ S`.
-/
theorem le_limit_of_eventually_le
    (q : ℕ → ℚ)
    (S c : ℝ)
    (hlim : ConvergesTo q S)
    (N₀ : ℕ)
    (hbound :
      ∀ n : ℕ, N₀ ≤ n →
        c ≤ (q n : ℝ)) :
    c ≤ S := by

  by_contra h

  have hSc :
      S < c := by
    exact lt_of_not_ge h

  let ε : ℝ :=
    (c - S) / 2

  have hε :
      0 < ε := by
    dsimp [ε]
    linarith

  obtain ⟨N₁, hN₁⟩ :=
    hlim ε hε

  let N : ℕ :=
    max N₀ N₁

  have hN0 :
      N₀ ≤ N := by
    exact le_max_left N₀ N₁

  have hN1 :
      N₁ ≤ N := by
    exact le_max_right N₀ N₁

  have hclose :
      |(q N : ℝ) - S| < ε := by
    exact hN₁ N hN1

  have hupper :
      (q N : ℝ) - S < ε := by
    exact (abs_lt.mp hclose).2

  have hq_lt :
      (q N : ℝ) < c := by
    dsimp [ε] at hupper
    linarith

  have hc_le :
      c ≤ (q N : ℝ) :=
    hbound N hN0

  linarith


/-!
============================================================
Part 1: the sequence is Cauchy
============================================================
-/

/--
The hypothesis of Exercise 5.5.4 implies that `q` is Cauchy.
-/
theorem cauchy_of_inverse_bound
    (q : ℕ → ℚ)
    (h :
      ∀ M n n' : ℕ,
        1 ≤ M →
        M ≤ n →
        M ≤ n' →
        |q n - q n'| ≤
          (1 : ℚ) / (M : ℚ)) :
    IsCauchySeq q := by

  intro ε hε

  /-
  Choose M such that

      1 / ε < M.
  -/
  obtain ⟨M, hM⟩ :=
    exists_nat_gt (1 / ε)

  have hinvPos :
      (0 : ℚ) < 1 / ε := by
    positivity

  have hMposQ :
      (0 : ℚ) < (M : ℚ) := by
    exact lt_trans hinvPos hM

  have hMpos :
      0 < M := by
    exact_mod_cast hMposQ

  have hMone :
      1 ≤ M := by
    omega

  /-
  From

      1/ε < M

  obtain

      1/M ≤ ε.
  -/
  have hInvLe :
      (1 : ℚ) / (M : ℚ) ≤ ε := by

    have hmul :
        (1 : ℚ) < (M : ℚ) * ε := by
      exact (div_lt_iff₀ hε).mp hM

    apply (div_le_iff₀ hMposQ).2

    have hmul' :
        (1 : ℚ) ≤ ε * (M : ℚ) := by
      simpa [mul_comm] using le_of_lt hmul

    exact hmul'

  refine ⟨M, ?_⟩

  intro n n' hn hn'

  have hqq :
      |q n - q n'|
        ≤ (1 : ℚ) / (M : ℚ) :=
    h M n n' hMone hn hn'

  exact le_trans hqq hInvLe


/-!
============================================================
Part 2: distance from q_M to its limit
============================================================
-/

/--
If `S` is the limit of `q`, then for every `M ≥ 1`,

    |q_M - S| ≤ 1/M.
-/
theorem term_close_to_limit
    (q : ℕ → ℚ)
    (S : ℝ)
    (h :
      ∀ M n n' : ℕ,
        1 ≤ M →
        M ≤ n →
        M ≤ n' →
        |q n - q n'| ≤
          (1 : ℚ) / (M : ℚ))
    (hlim : ConvergesTo q S)
    (M : ℕ)
    (hM : 1 ≤ M) :
    |(q M : ℝ) - S|
      ≤ (1 : ℝ) / (M : ℝ) := by

  /-
  First obtain the tail estimate in ℝ.
  -/
  have hdist :
      ∀ n : ℕ, M ≤ n →
        |(q n : ℝ) - (q M : ℝ)|
          ≤ (1 : ℝ) / (M : ℝ) := by

    intro n hn

    have hq :
        |q n - q M|
          ≤ (1 : ℚ) / (M : ℚ) :=
      h M n M hM hn (le_refl M)

    have hqBounds :
        -((1 : ℚ) / (M : ℚ))
            ≤ q n - q M
        ∧
        q n - q M
            ≤ (1 : ℚ) / (M : ℚ) := by
      exact abs_le.mp hq

    have hLowerCast :
        ((-((1 : ℚ) / (M : ℚ)) : ℚ) : ℝ)
          ≤
        ((q n - q M : ℚ) : ℝ) := by
      exact_mod_cast hqBounds.1

    have hUpperCast :
        ((q n - q M : ℚ) : ℝ)
          ≤
        (((1 : ℚ) / (M : ℚ) : ℚ) : ℝ) := by
      exact_mod_cast hqBounds.2

    push_cast at hLowerCast hUpperCast

    apply abs_le.mpr

    constructor

    · exact hLowerCast

    · exact hUpperCast


  /-
  Hence, for every n ≥ M,

      q_M - 1/M ≤ q_n.
  -/
  have hlower :
      ∀ n : ℕ, M ≤ n →
        (q M : ℝ) - (1 : ℝ) / (M : ℝ)
          ≤ (q n : ℝ) := by

    intro n hn

    have hh :
        |(q n : ℝ) - (q M : ℝ)|
          ≤ (1 : ℝ) / (M : ℝ) :=
      hdist n hn

    have hbounds :
        -((1 : ℝ) / (M : ℝ))
            ≤ (q n : ℝ) - (q M : ℝ)
        ∧
        (q n : ℝ) - (q M : ℝ)
            ≤ (1 : ℝ) / (M : ℝ) :=
      abs_le.mp hh

    linarith


  /-
  Similarly, for every n ≥ M,

      q_n ≤ q_M + 1/M.
  -/
  have hupper :
      ∀ n : ℕ, M ≤ n →
        (q n : ℝ)
          ≤ (q M : ℝ) + (1 : ℝ) / (M : ℝ) := by

    intro n hn

    have hh :
        |(q n : ℝ) - (q M : ℝ)|
          ≤ (1 : ℝ) / (M : ℝ) :=
      hdist n hn

    have hbounds :
        -((1 : ℝ) / (M : ℝ))
            ≤ (q n : ℝ) - (q M : ℝ)
        ∧
        (q n : ℝ) - (q M : ℝ)
            ≤ (1 : ℝ) / (M : ℝ) :=
      abs_le.mp hh

    linarith


  /-
  Pass the lower bound to the limit.
  -/
  have hLimitLower :
      (q M : ℝ) - (1 : ℝ) / (M : ℝ)
        ≤ S := by

    exact le_limit_of_eventually_le
      q
      S
      ((q M : ℝ) - (1 : ℝ) / (M : ℝ))
      hlim
      M
      hlower


  /-
  Pass the upper bound to the limit.
  -/
  have hLimitUpper :
      S ≤
        (q M : ℝ) + (1 : ℝ) / (M : ℝ) := by

    exact limit_le_of_eventually_le
      q
      S
      ((q M : ℝ) + (1 : ℝ) / (M : ℝ))
      hlim
      M
      hupper


  /-
  Conclude

      |q_M - S| ≤ 1/M.
  -/
  apply abs_le.mpr

  constructor

  · linarith

  · linarith


/-!
============================================================
Exercise 5.5.4 packaged together
============================================================
-/

theorem exercise_5_5_4
    (q : ℕ → ℚ)
    (S : ℝ)
    (h :
      ∀ M n n' : ℕ,
        1 ≤ M →
        M ≤ n →
        M ≤ n' →
        |q n - q n'| ≤
          (1 : ℚ) / (M : ℚ))
    (hlim : ConvergesTo q S) :
    IsCauchySeq q
    ∧
    ∀ M : ℕ, 1 ≤ M →
      |(q M : ℝ) - S|
        ≤ (1 : ℝ) / (M : ℝ) := by

  constructor

  · exact cauchy_of_inverse_bound q h

  · intro M hM

    exact term_close_to_limit
      q
      S
      h
      hlim
      M
      hM

end TaoExercise5_5_4
