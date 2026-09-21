import Mathlib

namespace TaoExercise2_2_5

/-
Exercise 2.2.5

Strong induction for natural numbers.
-/

/--
Auxiliary lemma used in the proof:

a < succ b ↔ a ≤ b.
-/
lemma lt_succ_iff_le (a b : ℕ) :
    a < Nat.succ b ↔ a ≤ b := by
  exact Nat.lt_succ_iff


/--
Strong induction starting at an arbitrary natural number m₀.

Suppose that whenever m ≥ m₀, knowing P(m') for every
m₀ ≤ m' < m allows us to prove P(m).

Then P(m) holds for every m ≥ m₀.
-/
theorem strong_induction_from
    (m₀ : ℕ)
    (P : ℕ → Prop)
    (h :
      ∀ m : ℕ,
        m₀ ≤ m →
        (∀ m' : ℕ, m₀ ≤ m' → m' < m → P m') →
        P m) :
    ∀ m : ℕ, m₀ ≤ m → P m := by

  /-
  Q(n) means:

    P(m) holds for every m such that
    m₀ ≤ m < n.
  -/
  have hQ :
      ∀ n : ℕ,
        ∀ m : ℕ,
          m₀ ≤ m →
          m < n →
          P m := by

    intro n

    induction n with

    /-
    Q(0) is vacuously true because there is
    no natural number m with m < 0.
    -/
    | zero =>
        intro m hm₀ hm
        exact (Nat.not_lt_zero m hm).elim

    /-
    Assume Q(n), and prove Q(succ n).
    -/
    | succ n ih =>
        intro m hm₀ hm

        /-
        Since m < succ n, the auxiliary lemma gives m ≤ n.
        -/
        have hmn : m ≤ n := by
          exact (lt_succ_iff_le m n).mp hm

        /-
        Thus either m < n or m = n.
        -/
        rcases lt_or_eq_of_le hmn with hlt | heq

        /-
        Case m < n:
        Q(n) already gives P(m).
        -/
        · exact ih m hm₀ hlt

        /-
        Case m = n:
        we use the main hypothesis to prove P(n).
        -/
        · subst m

          apply h n hm₀

          intro m' hm₀' hm'n

          /-
          Q(n) gives P(m') because
          m₀ ≤ m' < n.
          -/
          exact ih m' hm₀' hm'n

  /-
  We now know Q(n) for every n.

  To prove P(m), apply Q(succ m).
  Since m < succ m, P(m) follows.
  -/
  intro m hm₀

  have hQsucc :
      ∀ k : ℕ,
        m₀ ≤ k →
        k < Nat.succ m →
        P k :=
    hQ (Nat.succ m)

  exact hQsucc m hm₀ (Nat.lt_succ_self m)

end TaoExercise2_2_5
