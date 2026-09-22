import Mathlib

namespace TaoExercise6_6_4

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


/--
`b` is a subsequence of `a` if there exists a strictly increasing
index map `f : ℕ → ℕ` such that

    b n = a (f n)

for every `n`.
-/
def IsSubsequence
    (a b : ℕ → ℝ) : Prop :=
  ∃ f : ℕ → ℕ,
    StrictMono f ∧
    ∀ n : ℕ,
      b n = a (f n)


/-!
============================================================
Preliminary lemma

If f : ℕ → ℕ is strictly increasing, then

    n ≤ f n

for every n.
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

      have hn_lt :
          n < f (n + 1) := by
        exact lt_of_le_of_lt ih hstep

      exact Nat.succ_le_iff.mpr hn_lt


/-!
============================================================
A convergent sequence passes its limit to every subsequence
============================================================
-/

theorem subsequence_converges
    (a b : ℕ → ℝ)
    (L : ℝ)
    (ha : ConvergesFrom a 0 L)
    (hsub : IsSubsequence a b) :
    ConvergesFrom b 0 L := by

  rcases hsub with ⟨f, hfmono, hbf⟩

  intro ε hε

  obtain ⟨N, h0N, hN⟩ :=
    ha ε hε

  refine ⟨N, Nat.zero_le N, ?_⟩

  intro n hn

  have hnf :
      n ≤ f n := by
    exact le_of_strictMono_nat f hfmono n

  have hNfn :
      N ≤ f n := by
    exact le_trans hn hnf

  have hclose :
      |a (f n) - L| ≤ ε := by
    exact hN (f n) hNfn

  rw [hbf n]

  exact hclose


/-!
============================================================
The sequence is a subsequence of itself
============================================================
-/

theorem subsequence_refl
    (a : ℕ → ℝ) :
    IsSubsequence a a := by

  refine ⟨fun n => n, ?_, ?_⟩

  · exact strictMono_id

  · intro n
    rfl


/-!
============================================================
Proposition 6.6.5

A sequence converges to L iff every subsequence converges to L.
============================================================
-/

theorem proposition_6_6_5
    (a : ℕ → ℝ)
    (L : ℝ) :
    ConvergesFrom a 0 L
      ↔
    ∀ b : ℕ → ℝ,
      IsSubsequence a b →
      ConvergesFrom b 0 L := by

  constructor

  /-
  If a converges to L, then every subsequence converges to L.
  -/
  · intro ha
    intro b hsub

    exact subsequence_converges
      a
      b
      L
      ha
      hsub

  /-
  If every subsequence converges to L, then a itself converges to L,
  because a is a subsequence of itself.
  -/
  · intro hAll

    exact hAll
      a
      (subsequence_refl a)


/-!
============================================================
Exercise 6.6.4
============================================================
-/

theorem exercise_6_6_4
    (a : ℕ → ℝ)
    (L : ℝ) :
    ConvergesFrom a 0 L
      ↔
    ∀ b : ℕ → ℝ,
      IsSubsequence a b →
      ConvergesFrom b 0 L := by

  exact proposition_6_6_5 a L

end TaoExercise6_6_4
