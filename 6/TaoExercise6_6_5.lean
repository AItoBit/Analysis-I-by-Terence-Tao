import Mathlib

namespace TaoExercise6_6_5

/-!
============================================================
Basic definitions
============================================================
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


def IsLimitPointFrom
    (a : ℕ → ℝ)
    (m : ℕ)
    (L : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ N : ℕ, m ≤ N →
      ∃ n : ℕ,
        N ≤ n ∧
        |a n - L| ≤ ε


def IsSubsequence
    (a b : ℕ → ℝ) : Prop :=
  ∃ f : ℕ → ℕ,
    StrictMono f ∧
    ∀ n : ℕ,
      b n = a (f n)


/-!
============================================================
Preliminary result

A strictly increasing f : ℕ → ℕ satisfies n ≤ f n.
============================================================
-/

theorem le_of_strictMono_nat
    (f : ℕ → ℕ)
    (hf : StrictMono f) :
    ∀ n : ℕ, n ≤ f n := by

  intro n

  induction n with

  | zero =>
      exact Nat.zero_le (f 0)

  | succ n ih =>

      have hstep :
          f n < f (n + 1) := by
        exact hf (Nat.lt_succ_self n)

      have hn :
          n < f (n + 1) := by
        exact lt_of_le_of_lt ih hstep

      exact Nat.succ_le_iff.mpr hn


/-!
============================================================
(b) -> (a)

If a subsequence converges to L,
then L is a limit point of the original sequence.
============================================================
-/

theorem limitPoint_of_convergent_subsequence
    (a b : ℕ → ℝ)
    (L : ℝ)
    (hsub : IsSubsequence a b)
    (hconv : ConvergesFrom b 0 L) :
    IsLimitPointFrom a 0 L := by

  rcases hsub with ⟨f, hfmono, hbf⟩

  intro ε hε
  intro N h0N

  obtain ⟨M, h0M, hM⟩ :=
    hconv ε hε

  let p : ℕ := max M N

  have hMp :
      M ≤ p := by
    exact le_max_left M N

  have hNp :
      N ≤ p := by
    exact le_max_right M N

  have hp_f :
      p ≤ f p := by
    exact le_of_strictMono_nat f hfmono p

  have hNfp :
      N ≤ f p := by
    exact le_trans hNp hp_f

  have hcloseB :
      |b p - L| ≤ ε := by
    exact hM p hMp

  have hcloseA :
      |a (f p) - L| ≤ ε := by
    rw [← hbf p]
    exact hcloseB

  exact ⟨f p, hNfp, hcloseA⟩


/-!
============================================================
If L is a limit point, then after every K we can
find a later term within 1/(j+1) of L.
============================================================
-/

theorem exists_close_after
    (a : ℕ → ℝ)
    (L : ℝ)
    (hL : IsLimitPointFrom a 0 L)
    (j K : ℕ) :
    ∃ n : ℕ,
      K < n ∧
      |a n - L| ≤ 1 / ((j + 1 : ℕ) : ℝ) := by

  have hε :
      (0 : ℝ) < 1 / ((j + 1 : ℕ) : ℝ) := by
    positivity

  obtain ⟨n, hKn, hclose⟩ :=
    hL
      (1 / ((j + 1 : ℕ) : ℝ))
      hε
      (K + 1)
      (Nat.zero_le (K + 1))

  have hKlt :
      K < n := by
    omega

  exact ⟨n, hKlt, hclose⟩


/-!
============================================================
Recursive construction of n_j

n₀ = 0

n_(j+1) is the least n > n_j such that

    |a_n - L| ≤ 1/(j+1).
============================================================
-/

noncomputable def indexSeq
    (a : ℕ → ℝ)
    (L : ℝ)
    (hL : IsLimitPointFrom a 0 L) :
    ℕ → ℕ
  | 0 => 0
  | j + 1 =>
      Nat.find
        (exists_close_after
          a
          L
          hL
          j
          (indexSeq a L hL j))


/-!
============================================================
Specification of each recursive step
============================================================
-/

theorem indexSeq_step_spec
    (a : ℕ → ℝ)
    (L : ℝ)
    (hL : IsLimitPointFrom a 0 L)
    (j : ℕ) :
    indexSeq a L hL j
        < indexSeq a L hL (j + 1)
    ∧
    |a (indexSeq a L hL (j + 1)) - L|
        ≤ 1 / ((j + 1 : ℕ) : ℝ) := by

  rw [indexSeq]

  exact Nat.find_spec
    (exists_close_after
      a
      L
      hL
      j
      (indexSeq a L hL j))


/-!
============================================================
The chosen indices are strictly increasing
============================================================
-/

theorem indexSeq_strictMono
    (a : ℕ → ℝ)
    (L : ℝ)
    (hL : IsLimitPointFrom a 0 L) :
    StrictMono (indexSeq a L hL) := by

  intro i j hij

  induction j with

  | zero =>
      omega

  | succ j ih =>

      by_cases hijEq : i = j

      · subst i

        exact
          (indexSeq_step_spec
            a
            L
            hL
            j).1

      · have hij' :
            i < j := by
          omega

        have hPrev :
            indexSeq a L hL i
              < indexSeq a L hL j := by
          exact ih hij'

        have hStep :
            indexSeq a L hL j
              < indexSeq a L hL (j + 1) := by
          exact
            (indexSeq_step_spec
              a
              L
              hL
              j).1

        exact lt_trans hPrev hStep


/-!
============================================================
For every j > 0,

    |a_(n_j) - L| ≤ 1/j.
============================================================
-/

theorem indexSeq_close
    (a : ℕ → ℝ)
    (L : ℝ)
    (hL : IsLimitPointFrom a 0 L)
    (j : ℕ)
    (hj : 0 < j) :
    |a (indexSeq a L hL j) - L|
      ≤ 1 / (j : ℝ) := by

  cases j with

  | zero =>
      omega

  | succ k =>
      exact
        (indexSeq_step_spec
          a
          L
          hL
          k).2


/-!
============================================================
The selected subsequence
============================================================
-/

noncomputable def selectedSubsequence
    (a : ℕ → ℝ)
    (L : ℝ)
    (hL : IsLimitPointFrom a 0 L)
    (j : ℕ) : ℝ :=
  a (indexSeq a L hL j)


theorem selected_is_subsequence
    (a : ℕ → ℝ)
    (L : ℝ)
    (hL : IsLimitPointFrom a 0 L) :
    IsSubsequence
      a
      (selectedSubsequence a L hL) := by

  refine
    ⟨indexSeq a L hL, ?_, ?_⟩

  · exact indexSeq_strictMono
      a
      L
      hL

  · intro n
    rfl


/-!
============================================================
The selected subsequence converges to L
============================================================
-/

theorem selected_converges
    (a : ℕ → ℝ)
    (L : ℝ)
    (hL : IsLimitPointFrom a 0 L) :
    ConvergesFrom
      (selectedSubsequence a L hL)
      0
      L := by

  intro ε hε

  /-
  Choose J with

      1/ε < J.
  -/
  obtain ⟨J : ℕ, hJ⟩ :=
    exists_nat_gt (1 / ε)

  have hInvPos :
      (0 : ℝ) < 1 / ε := by
    exact one_div_pos.mpr hε

  have hJposR :
      (0 : ℝ) < (J : ℝ) := by
    exact lt_trans hInvPos hJ

  have hJne :
      J ≠ 0 := by
    intro h
    subst J
    norm_num at hJposR

  have hJpos :
      0 < J := by
    exact Nat.pos_of_ne_zero hJne

  refine ⟨J, Nat.zero_le J, ?_⟩

  intro k hk

  have hkpos :
      0 < k := by
    exact lt_of_lt_of_le hJpos hk

  have hclose :
      |a (indexSeq a L hL k) - L|
        ≤ 1 / (k : ℝ) := by

    exact indexSeq_close
      a
      L
      hL
      k
      hkpos

  /-
  From J ≤ k we have

      1/ε < k.
  -/
  have hJkR :
      (J : ℝ) ≤ (k : ℝ) := by
    exact Nat.cast_le.mpr hk

  have hInvK :
      1 / ε < (k : ℝ) := by
    exact lt_of_lt_of_le hJ hJkR

  have hkPosR :
      (0 : ℝ) < (k : ℝ) := by
    exact lt_of_lt_of_le hJposR hJkR

  /-
  1/ε < k  implies  1 < kε.
  -/
  have hOne :
      (1 : ℝ) < (k : ℝ) * ε := by
    exact (div_lt_iff₀ hε).mp hInvK

  have hOne' :
      (1 : ℝ) < ε * (k : ℝ) := by
    simpa [mul_comm] using hOne

  /-
  Hence 1/k < ε.
  -/
  have hInvLt :
      (1 : ℝ) / (k : ℝ) < ε := by
    exact
      (div_lt_iff₀ hkPosR).2
        hOne'

  have hInvLe :
      (1 : ℝ) / (k : ℝ) ≤ ε := by
    exact le_of_lt hInvLt

  unfold selectedSubsequence

  exact le_trans hclose hInvLe


/-!
============================================================
(a) -> (b)

Every limit point is the limit of a subsequence.
============================================================
-/

theorem exists_convergent_subsequence_of_limitPoint
    (a : ℕ → ℝ)
    (L : ℝ)
    (hL : IsLimitPointFrom a 0 L) :
    ∃ b : ℕ → ℝ,
      IsSubsequence a b
      ∧
      ConvergesFrom b 0 L := by

  refine
    ⟨selectedSubsequence a L hL, ?_, ?_⟩

  · exact selected_is_subsequence
      a
      L
      hL

  · exact selected_converges
      a
      L
      hL


/-!
============================================================
Proposition 6.6.6
============================================================

L is a limit point of a sequence iff
there exists a subsequence converging to L.
-/

theorem proposition_6_6_6
    (a : ℕ → ℝ)
    (L : ℝ) :
    IsLimitPointFrom a 0 L
      ↔
    ∃ b : ℕ → ℝ,
      IsSubsequence a b
      ∧
      ConvergesFrom b 0 L := by

  constructor

  /-
  (a) -> (b)
  -/
  · intro hL

    exact
      exists_convergent_subsequence_of_limitPoint
        a
        L
        hL

  /-
  (b) -> (a)
  -/
  · rintro ⟨b, hsub, hconv⟩

    exact
      limitPoint_of_convergent_subsequence
        a
        b
        L
        hsub
        hconv


/-!
============================================================
Exercise 6.6.5
============================================================
-/

theorem exercise_6_6_5
    (a : ℕ → ℝ)
    (L : ℝ) :
    IsLimitPointFrom a 0 L
      ↔
    ∃ b : ℕ → ℝ,
      IsSubsequence a b
      ∧
      ConvergesFrom b 0 L := by

  exact proposition_6_6_6 a L

end TaoExercise6_6_5
