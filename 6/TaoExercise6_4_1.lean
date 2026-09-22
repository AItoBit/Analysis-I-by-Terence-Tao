import Mathlib

namespace TaoExercise6_4_1

/--
A real sequence `a` converges to `L` starting from index `m`.
-/
def ConvergesFrom
    (a : ℕ → ℝ)
    (m : ℕ)
    (L : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ,
      m ≤ N ∧
      ∀ n : ℕ,
        N ≤ n →
        |a n - L| ≤ ε


/--
`c` is a limit point of the sequence `a` from index `m`
if for every ε > 0 and every N ≥ m, there is some k ≥ N
such that

    |a k - c| ≤ ε.
-/
def IsLimitPointFrom
    (a : ℕ → ℝ)
    (m : ℕ)
    (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ N : ℕ, m ≤ N →
      ∃ k : ℕ,
        N ≤ k ∧
        |a k - c| ≤ ε


/-!
============================================================
Part 1

If a_n → c, then c is a limit point.
============================================================
-/

theorem limit_is_limitPoint
    (a : ℕ → ℝ)
    (m : ℕ)
    (c : ℝ)
    (hconv : ConvergesFrom a m c) :
    IsLimitPointFrom a m c := by

  intro ε hε

  obtain ⟨N', hmN', hN'⟩ :=
    hconv ε hε

  intro N hNm

  let k : ℕ := max N N'

  refine ⟨k, ?_, ?_⟩

  · exact le_max_left N N'

  · have hN'k :
        N' ≤ k := by
      exact le_max_right N N'

    exact hN' k hN'k


/-!
============================================================
Part 2

If a_n → c, then c is the only limit point.
============================================================
-/

theorem limitPoint_unique
    (a : ℕ → ℝ)
    (m : ℕ)
    (c c' : ℝ)
    (hconv : ConvergesFrom a m c)
    (hlimitPoint : IsLimitPointFrom a m c') :
    c' = c := by

  by_contra hneq

  have hdistPos :
      0 < |c - c'| := by
    exact abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hneq))

  let ε : ℝ := |c - c'| / 3

  have hε :
      0 < ε := by
    dsimp [ε]
    positivity

  /-
  Since a_n → c, eventually

      |a_n - c| ≤ ε.
  -/
  obtain ⟨N, hmN, hN⟩ :=
    hconv ε hε

  /-
  Since c' is a limit point, there exists n₀ ≥ N with

      |a_n₀ - c'| ≤ ε.
  -/
  obtain ⟨n₀, hNn₀, hn₀c'⟩ :=
    hlimitPoint ε hε N hmN

  have hn₀c :
      |a n₀ - c| ≤ ε := by
    exact hN n₀ hNn₀

  /-
  Triangle inequality:

      |c - c'|
        ≤ |c - a_n₀| + |a_n₀ - c'|.
  -/
  have htriangle :
      |c - c'|
        ≤ |c - a n₀| + |a n₀ - c'| := by

    have hdecomp :
        c - c' =
          (c - a n₀) + (a n₀ - c') := by
      ring

    rw [hdecomp]

    exact abs_add_le _ _

  have hcn₀ :
      |c - a n₀| ≤ ε := by
    simpa [abs_sub_comm] using hn₀c

  have hupper :
      |c - c'| ≤ ε + ε := by
    exact le_trans
      htriangle
      (add_le_add hcn₀ hn₀c')

  dsimp [ε] at hupper

  linarith


/-!
============================================================
Proposition 6.4.5

If a sequence converges to c, then:

1. c is a limit point;
2. c is the unique limit point.
============================================================
-/

theorem proposition_6_4_5
    (a : ℕ → ℝ)
    (m : ℕ)
    (c : ℝ)
    (hconv : ConvergesFrom a m c) :
    IsLimitPointFrom a m c
    ∧
    ∀ c' : ℝ,
      IsLimitPointFrom a m c' →
      c' = c := by

  constructor

  · exact limit_is_limitPoint
      a
      m
      c
      hconv

  · intro c' hc'

    exact limitPoint_unique
      a
      m
      c
      c'
      hconv
      hc'


/-!
============================================================
Exercise wrapper
============================================================
-/

theorem exercise_6_4_1
    (a : ℕ → ℝ)
    (m : ℕ)
    (c : ℝ)
    (hconv : ConvergesFrom a m c) :
    IsLimitPointFrom a m c
    ∧
    ∀ c' : ℝ,
      IsLimitPointFrom a m c' →
      c' = c := by

  exact proposition_6_4_5
    a
    m
    c
    hconv

end TaoExercise6_4_1
