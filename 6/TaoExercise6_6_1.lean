import Mathlib

namespace TaoExercise6_6_1

/--
`b` is a subsequence of `a` (both viewed from index 1 onward)
if there exists a strictly increasing map `φ : ℕ → ℕ`
such that `φ n ≥ 1` whenever `n ≥ 1`, and

    b n = a (φ n)

for every `n ≥ 1`.
-/
def IsSubsequence
    (a b : ℕ → ℝ) : Prop :=
  ∃ φ : ℕ → ℕ,
    StrictMono φ ∧
    (∀ n : ℕ, 1 ≤ n → 1 ≤ φ n) ∧
    ∀ n : ℕ, 1 ≤ n → b n = a (φ n)


/-!
============================================================
Reflexivity
============================================================
-/

theorem isSubsequence_refl
    (a : ℕ → ℝ) :
    IsSubsequence a a := by

  refine ⟨fun n => n, ?_, ?_, ?_⟩

  · exact strictMono_id

  · intro n hn
    exact hn

  · intro n hn
    rfl


/-!
============================================================
Transitivity
============================================================
-/

theorem isSubsequence_trans
    (a b c : ℕ → ℝ)
    (hab : IsSubsequence a b)
    (hbc : IsSubsequence b c) :
    IsSubsequence a c := by

  rcases hab with ⟨f, hfmono, hfpos, hbf⟩
  rcases hbc with ⟨g, hgmono, hgpos, hcg⟩

  refine ⟨fun n => f (g n), ?_, ?_, ?_⟩

  /-
  Composition of strictly increasing maps
  is strictly increasing.
  -/
  · exact hfmono.comp hgmono

  /-
  The composed map still takes positive indices
  to positive indices.
  -/
  · intro n hn

    have hgOne :
        1 ≤ g n := by
      exact hgpos n hn

    exact hfpos (g n) hgOne

  /-
  c_n = b_{g(n)} = a_{f(g(n))}.
  -/
  · intro n hn

    have hgOne :
        1 ≤ g n := by
      exact hgpos n hn

    calc
      c n = b (g n) := hcg n hn
      _ = a (f (g n)) := hbf (g n) hgOne


/-!
============================================================
Lemma 6.6.4
============================================================
-/

theorem lemma_6_6_4
    (a b c : ℕ → ℝ) :
    IsSubsequence a a
    ∧
    (IsSubsequence a b →
      IsSubsequence b c →
      IsSubsequence a c) := by

  constructor

  · exact isSubsequence_refl a

  · intro hab hbc
    exact isSubsequence_trans a b c hab hbc


/-!
============================================================
Exercise 6.6.1
============================================================
-/

theorem exercise_6_6_1
    (a b c : ℕ → ℝ) :
    IsSubsequence a a
    ∧
    (IsSubsequence a b →
      IsSubsequence b c →
      IsSubsequence a c) := by

  exact lemma_6_6_4 a b c

end TaoExercise6_6_1
