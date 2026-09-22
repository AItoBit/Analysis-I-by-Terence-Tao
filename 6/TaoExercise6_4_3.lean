import Mathlib

namespace TaoExercise6_4_3

/-!
Exercise 6.4.3
Parts (c), (d), and (e) of Proposition 6.4.12.

We assume throughout that the liminf and limsup are finite real numbers.
-/


/-!
============================================================
Basic definitions
============================================================
-/

/--
`c` is a limit point of the sequence `a`, starting at index `m`.
-/
def IsLimitPointFrom
    (a : ℕ → ℝ)
    (m : ℕ)
    (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ N : ℕ, m ≤ N →
      ∃ n : ℕ,
        N ≤ n ∧
        |a n - c| ≤ ε


/--
The sequence converges to `c` starting at `m`.
-/
def ConvergesFrom
    (a : ℕ → ℝ)
    (m : ℕ)
    (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ,
      m ≤ N ∧
      ∀ n : ℕ,
        N ≤ n →
        |a n - c| ≤ ε


/--
Property of a finite limsup:

if `Lplus < x`, then eventually every term is below `x`.
This corresponds to Proposition 6.4.12(a).
-/
def HasFiniteLimsupProperty
    (a : ℕ → ℝ)
    (m : ℕ)
    (Lplus : ℝ) : Prop :=
  ∀ x : ℝ,
    Lplus < x →
    ∃ N : ℕ,
      m ≤ N ∧
      ∀ n : ℕ,
        N ≤ n →
        a n < x


/--
Property of a finite liminf:

if `y < Lminus`, then eventually every term is above `y`.
This corresponds to Proposition 6.4.12(b).
-/
def HasFiniteLiminfProperty
    (a : ℕ → ℝ)
    (m : ℕ)
    (Lminus : ℝ) : Prop :=
  ∀ y : ℝ,
    y < Lminus →
    ∃ N : ℕ,
      m ≤ N ∧
      ∀ n : ℕ,
        N ≤ n →
        y < a n


/-!
============================================================
(c)

Lminus ≤ Lplus.

The complete statement in Tao is

    inf(a_n) ≤ Lminus ≤ Lplus ≤ sup(a_n).

The two exterior inequalities follow immediately from the
definitions of liminf/limsup as suprema/infima of tail bounds.

The nontrivial middle inequality is proved here.
============================================================
-/

theorem liminf_le_limsup
    (a : ℕ → ℝ)
    (m : ℕ)
    (Lminus Lplus : ℝ)
    (hplus : HasFiniteLimsupProperty a m Lplus)
    (hminus : HasFiniteLiminfProperty a m Lminus) :
    Lminus ≤ Lplus := by

  by_contra h

  have hgap :
      Lplus < Lminus := by
    exact lt_of_not_ge h

  /-
  Choose ε = (Lminus - Lplus) / 3.
  -/
  let ε : ℝ := (Lminus - Lplus) / 3

  have hε :
      0 < ε := by
    dsimp [ε]
    linarith

  have hplusBound :
      Lplus < Lplus + ε := by
    linarith

  have hminusBound :
      Lminus - ε < Lminus := by
    linarith

  obtain ⟨N₁, hmN₁, hN₁⟩ :=
    hplus (Lplus + ε) hplusBound

  obtain ⟨N₂, hmN₂, hN₂⟩ :=
    hminus (Lminus - ε) hminusBound

  let N : ℕ := max N₁ N₂

  have hN₁N :
      N₁ ≤ N := by
    exact le_max_left N₁ N₂

  have hN₂N :
      N₂ ≤ N := by
    exact le_max_right N₁ N₂

  have hUpper :
      a N < Lplus + ε := by
    exact hN₁ N hN₁N

  have hLower :
      Lminus - ε < a N := by
    exact hN₂ N hN₂N

  dsimp [ε] at hUpper hLower

  linarith


/--
Part (c), packaged with the two outside inequalities.

`seqInf` and `seqSup` stand for the infimum and supremum
of the entire sequence starting from `m`.
-/
theorem proposition_6_4_12_c
    (a : ℕ → ℝ)
    (m : ℕ)
    (seqInf Lminus Lplus seqSup : ℝ)
    (hInf :
      seqInf ≤ Lminus)
    (hSup :
      Lplus ≤ seqSup)
    (hplus :
      HasFiniteLimsupProperty a m Lplus)
    (hminus :
      HasFiniteLiminfProperty a m Lminus) :
    seqInf ≤ Lminus ∧
    Lminus ≤ Lplus ∧
    Lplus ≤ seqSup := by

  constructor

  · exact hInf

  constructor

  · exact liminf_le_limsup
      a m Lminus Lplus hplus hminus

  · exact hSup


/-!
============================================================
(d)

Every limit point c satisfies

    Lminus ≤ c ≤ Lplus.
============================================================
-/

theorem limitPoint_le_limsup
    (a : ℕ → ℝ)
    (m : ℕ)
    (Lplus c : ℝ)
    (hplus : HasFiniteLimsupProperty a m Lplus)
    (hc : IsLimitPointFrom a m c) :
    c ≤ Lplus := by

  by_contra h

  have hLc :
      Lplus < c := by
    exact lt_of_not_ge h

  let ε : ℝ := (c - Lplus) / 3

  have hε :
      0 < ε := by
    dsimp [ε]
    linarith

  have hthreshold :
      Lplus < Lplus + ε := by
    linarith

  /-
  Eventually

      a_n < Lplus + ε.
  -/
  obtain ⟨N, hmN, hN⟩ :=
    hplus (Lplus + ε) hthreshold

  /-
  Since c is a limit point, choose n ≥ N with

      |a_n - c| ≤ ε.
  -/
  obtain ⟨n, hNn, hnclose⟩ :=
    hc ε hε N hmN

  have hnUpper :
      a n < Lplus + ε := by
    exact hN n hNn

  have hbounds :
      -ε ≤ a n - c ∧
      a n - c ≤ ε := by
    exact abs_le.mp hnclose

  have hnLower :
      c - ε ≤ a n := by
    linarith [hbounds.1]

  dsimp [ε] at hnUpper hnLower

  linarith


theorem liminf_le_limitPoint
    (a : ℕ → ℝ)
    (m : ℕ)
    (Lminus c : ℝ)
    (hminus : HasFiniteLiminfProperty a m Lminus)
    (hc : IsLimitPointFrom a m c) :
    Lminus ≤ c := by

  by_contra h

  have hcL :
      c < Lminus := by
    exact lt_of_not_ge h

  let ε : ℝ := (Lminus - c) / 3

  have hε :
      0 < ε := by
    dsimp [ε]
    linarith

  have hthreshold :
      Lminus - ε < Lminus := by
    linarith

  /-
  Eventually

      Lminus - ε < a_n.
  -/
  obtain ⟨N, hmN, hN⟩ :=
    hminus (Lminus - ε) hthreshold

  /-
  Because c is a limit point, choose n ≥ N with

      |a_n - c| ≤ ε.
  -/
  obtain ⟨n, hNn, hnclose⟩ :=
    hc ε hε N hmN

  have hnLower :
      Lminus - ε < a n := by
    exact hN n hNn

  have hbounds :
      -ε ≤ a n - c ∧
      a n - c ≤ ε := by
    exact abs_le.mp hnclose

  have hnUpper :
      a n ≤ c + ε := by
    linarith [hbounds.2]

  dsimp [ε] at hnLower hnUpper

  linarith


theorem proposition_6_4_12_d
    (a : ℕ → ℝ)
    (m : ℕ)
    (Lminus Lplus c : ℝ)
    (hplus :
      HasFiniteLimsupProperty a m Lplus)
    (hminus :
      HasFiniteLiminfProperty a m Lminus)
    (hc :
      IsLimitPointFrom a m c) :
    Lminus ≤ c ∧ c ≤ Lplus := by

  constructor

  · exact liminf_le_limitPoint
      a m Lminus c hminus hc

  · exact limitPoint_le_limsup
      a m Lplus c hplus hc


/-!
============================================================
(e)

If Lplus is finite, then Lplus is a limit point.
Likewise for Lminus.

Besides the eventual-bound properties above, we need the
characteristic approximation properties of sup/inf:

for every y < Lplus and every starting index N,
some later term is greater than y;

for every Lminus < y and every starting index N,
some later term is less than y.
============================================================
-/

/--
Approximation property from below for a finite limsup.
-/
def LimsupApproximatedFromBelow
    (a : ℕ → ℝ)
    (m : ℕ)
    (Lplus : ℝ) : Prop :=
  ∀ y : ℝ,
    y < Lplus →
    ∀ N : ℕ,
      m ≤ N →
      ∃ n : ℕ,
        N ≤ n ∧
        y < a n


/--
Approximation property from above for a finite liminf.
-/
def LiminfApproximatedFromAbove
    (a : ℕ → ℝ)
    (m : ℕ)
    (Lminus : ℝ) : Prop :=
  ∀ y : ℝ,
    Lminus < y →
    ∀ N : ℕ,
      m ≤ N →
      ∃ n : ℕ,
        N ≤ n ∧
        a n < y


/--
A finite limsup is a limit point.
-/
theorem limsup_is_limitPoint
    (a : ℕ → ℝ)
    (m : ℕ)
    (Lplus : ℝ)
    (hplus :
      HasFiniteLimsupProperty a m Lplus)
    (happrox :
      LimsupApproximatedFromBelow a m Lplus) :
    IsLimitPointFrom a m Lplus := by

  intro ε hε
  intro N hmN

  /-
  Eventually all terms are below Lplus + ε.
  -/
  have hupperThreshold :
      Lplus < Lplus + ε := by
    linarith

  obtain ⟨N', hmN', hN'⟩ :=
    hplus (Lplus + ε) hupperThreshold

  let M : ℕ := max N N'

  have hNM :
      N ≤ M := by
    exact le_max_left N N'

  have hN'M :
      N' ≤ M := by
    exact le_max_right N N'

  have hmM :
      m ≤ M := by
    exact le_trans hmN hNM

  /-
  Since Lplus - ε < Lplus, some term after M
  is greater than Lplus - ε.
  -/
  have hlowerThreshold :
      Lplus - ε < Lplus := by
    linarith

  obtain ⟨n, hMn, hnLower⟩ :=
    happrox
      (Lplus - ε)
      hlowerThreshold
      M
      hmM

  have hnUpper :
      a n < Lplus + ε := by
    exact hN' n (le_trans hN'M hMn)

  refine ⟨n, le_trans hNM hMn, ?_⟩

  apply abs_le.mpr

  constructor

  · linarith

  · linarith


/--
A finite liminf is a limit point.
-/
theorem liminf_is_limitPoint
    (a : ℕ → ℝ)
    (m : ℕ)
    (Lminus : ℝ)
    (hminus :
      HasFiniteLiminfProperty a m Lminus)
    (happrox :
      LiminfApproximatedFromAbove a m Lminus) :
    IsLimitPointFrom a m Lminus := by

  intro ε hε
  intro N hmN

  /-
  Eventually all terms are above Lminus - ε.
  -/
  have hlowerThreshold :
      Lminus - ε < Lminus := by
    linarith

  obtain ⟨N', hmN', hN'⟩ :=
    hminus (Lminus - ε) hlowerThreshold

  let M : ℕ := max N N'

  have hNM :
      N ≤ M := by
    exact le_max_left N N'

  have hN'M :
      N' ≤ M := by
    exact le_max_right N N'

  have hmM :
      m ≤ M := by
    exact le_trans hmN hNM

  /-
  Since Lminus < Lminus + ε, some term after M
  lies below Lminus + ε.
  -/
  have hupperThreshold :
      Lminus < Lminus + ε := by
    linarith

  obtain ⟨n, hMn, hnUpper⟩ :=
    happrox
      (Lminus + ε)
      hupperThreshold
      M
      hmM

  have hnLower :
      Lminus - ε < a n := by
    exact hN' n (le_trans hN'M hMn)

  refine ⟨n, le_trans hNM hMn, ?_⟩

  apply abs_le.mpr

  constructor

  · linarith

  · linarith


/--
Part (e), both statements packaged together.
-/
theorem proposition_6_4_12_e
    (a : ℕ → ℝ)
    (m : ℕ)
    (Lminus Lplus : ℝ)
    (hplus :
      HasFiniteLimsupProperty a m Lplus)
    (hminus :
      HasFiniteLiminfProperty a m Lminus)
    (hplusApprox :
      LimsupApproximatedFromBelow a m Lplus)
    (hminusApprox :
      LiminfApproximatedFromAbove a m Lminus) :
    IsLimitPointFrom a m Lplus ∧
    IsLimitPointFrom a m Lminus := by

  constructor

  · exact limsup_is_limitPoint
      a m Lplus hplus hplusApprox

  · exact liminf_is_limitPoint
      a m Lminus hminus hminusApprox

end TaoExercise6_4_3
