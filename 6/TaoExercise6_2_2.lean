import Mathlib

namespace TaoExercise6_2_2

/-!
Exercise 6.2.2 — Theorem 6.2.11

We use `EReal`, Mathlib's extended real numbers.

For a set `E : Set EReal`:

    sSup E

is its supremum, and

    sInf E

is its infimum.
-/


/-!
============================================================
(a)

For every x ∈ E,

    x ≤ sup(E)

and

    inf(E) ≤ x.
============================================================
-/

theorem theorem_6_2_11_a_sup
    (E : Set EReal)
    (x : EReal)
    (hx : x ∈ E) :
    x ≤ sSup E := by

  exact le_sSup hx


theorem theorem_6_2_11_a_inf
    (E : Set EReal)
    (x : EReal)
    (hx : x ∈ E) :
    sInf E ≤ x := by

  exact sInf_le hx


theorem theorem_6_2_11_a
    (E : Set EReal)
    (x : EReal)
    (hx : x ∈ E) :
    x ≤ sSup E ∧ sInf E ≤ x := by

  constructor

  · exact le_sSup hx

  · exact sInf_le hx


/-!
============================================================
(b)

If M is an upper bound for E, then

    sup(E) ≤ M.
============================================================
-/

theorem theorem_6_2_11_b
    (E : Set EReal)
    (M : EReal)
    (hM :
      ∀ x : EReal,
        x ∈ E →
        x ≤ M) :
    sSup E ≤ M := by

  exact sSup_le hM


/-!
============================================================
Symmetric lower-bound statement.

If M is a lower bound for E, then

    M ≤ inf(E).
============================================================
-/

theorem inf_ge_of_lower_bound
    (E : Set EReal)
    (M : EReal)
    (hM :
      ∀ x : EReal,
        x ∈ E →
        M ≤ x) :
    M ≤ sInf E := by

  exact le_sInf hM


/-!
============================================================
Useful reformulations
============================================================
-/

/--
The supremum is an upper bound of E.
-/
theorem sup_is_upper_bound
    (E : Set EReal) :
    ∀ x : EReal,
      x ∈ E →
      x ≤ sSup E := by

  intro x hx

  exact le_sSup hx


/--
The infimum is a lower bound of E.
-/
theorem inf_is_lower_bound
    (E : Set EReal) :
    ∀ x : EReal,
      x ∈ E →
      sInf E ≤ x := by

  intro x hx

  exact sInf_le hx


/--
Every upper bound M of E satisfies sSup E ≤ M.
-/
theorem sup_le_every_upper_bound
    (E : Set EReal)
    (M : EReal)
    (hM :
      ∀ x : EReal,
        x ∈ E →
        x ≤ M) :
    sSup E ≤ M := by

  exact sSup_le hM


/--
Every lower bound M of E satisfies M ≤ sInf E.
-/
theorem every_lower_bound_le_inf
    (E : Set EReal)
    (M : EReal)
    (hM :
      ∀ x : EReal,
        x ∈ E →
        M ≤ x) :
    M ≤ sInf E := by

  exact le_sInf hM


/-!
============================================================
Complete packaged version of Theorem 6.2.11
============================================================
-/

theorem theorem_6_2_11
    (E : Set EReal) :
    (∀ x : EReal,
      x ∈ E →
      x ≤ sSup E ∧
      sInf E ≤ x)
    ∧
    (∀ M : EReal,
      (∀ x : EReal,
        x ∈ E →
        x ≤ M) →
      sSup E ≤ M) := by

  constructor

  /-
  Part (a)
  -/
  · intro x hx

    constructor

    · exact le_sSup hx

    · exact sInf_le hx

  /-
  Part (b)
  -/
  · intro M hM

    exact sSup_le hM

end TaoExercise6_2_2
