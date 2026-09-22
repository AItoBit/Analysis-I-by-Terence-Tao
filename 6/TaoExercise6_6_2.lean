import Mathlib

namespace TaoExercise6_6_2

/--
For sequences indexed from 0 onward, `b` is a subsequence of `a`
if there is a strictly increasing map `φ : ℕ → ℕ` such that

    b n = a (φ n)

for every `n`.
-/
def IsSubsequence
    (a b : ℕ → ℝ) : Prop :=
  ∃ φ : ℕ → ℕ,
    StrictMono φ ∧
    ∀ n : ℕ, b n = a (φ n)


/-!
============================================================
The two sequences
============================================================
-/

def a (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n

def b (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n + 1)


/-!
============================================================
The shift n ↦ n + 1 is strictly increasing
============================================================
-/

theorem shift_strictMono :
    StrictMono (fun n : ℕ => n + 1) := by

  intro m n hmn

  change m + 1 < n + 1

  omega


/-!
============================================================
b is a subsequence of a

Indeed,

    b_n = a_{n+1}.
============================================================
-/

theorem b_subsequence_a :
    IsSubsequence a b := by

  refine ⟨fun n => n + 1, shift_strictMono, ?_⟩

  intro n

  unfold a b

  rfl


/-!
============================================================
a is a subsequence of b

We need

    a_n = b_{n+1}.

But

    b_{n+1}
      = (-1)^(n+2)
      = (-1)^n.
============================================================
-/

theorem a_subsequence_b :
    IsSubsequence b a := by

  refine ⟨fun n => n + 1, shift_strictMono, ?_⟩

  intro n

  unfold a b

  have hindex :
      (n + 1) + 1 = n + 2 := by
    omega

  rw [hindex, pow_add]

  norm_num


/-!
============================================================
The two sequences are not equal
============================================================
-/

theorem a_ne_b :
    a ≠ b := by

  intro h

  have h0 :
      a 0 = b 0 := by
    exact congrFun h 0

  unfold a b at h0

  norm_num at h0


/-!
============================================================
Exercise 6.6.2
============================================================
-/

theorem exercise_6_6_2 :
    a ≠ b
    ∧
    IsSubsequence a b
    ∧
    IsSubsequence b a := by

  constructor

  · exact a_ne_b

  constructor

  · exact b_subsequence_a

  · exact a_subsequence_b

end TaoExercise6_6_2
