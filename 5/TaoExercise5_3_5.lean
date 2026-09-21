import Mathlib

namespace TaoExercise5_3_5

def SeqEquivalent
    (a b : ℕ → ℚ) : Prop :=
  ∀ ε : ℚ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ,
      N ≤ n →
      |a n - b n| ≤ ε

def zeroSeq : ℕ → ℚ :=
  fun _ => 0

def invSeq : ℕ → ℚ :=
  fun n => 1 / (n + 1 : ℚ)


theorem exists_inv_le
    (ε : ℚ)
    (hε : 0 < ε) :
    ∃ N : ℕ,
      1 / (N + 1 : ℚ) ≤ ε := by

  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)

  refine ⟨N, ?_⟩

  have hNpos :
      (0 : ℚ) < N + 1 := by
    positivity

  have hNlt :
      1 / ε < (N + 1 : ℚ) := by
    linarith

  have hmul :
      1 ≤ ε * (N + 1 : ℚ) := by
    have h :=
      mul_lt_mul_of_pos_left hNlt hε
    field_simp at h
    linarith

  apply (div_le_iff₀ hNpos).2

  simpa using hmul


theorem exercise_5_3_5 :
    SeqEquivalent invSeq zeroSeq := by

  intro ε hε

  obtain ⟨N, hN⟩ :=
    exists_inv_le ε hε

  refine ⟨N, ?_⟩

  intro n hn

  unfold invSeq zeroSeq

  simp only [sub_zero]

  have hnpos :
      (0 : ℚ) < n + 1 := by
    positivity

  have hnonneg :
      0 ≤ 1 / (n + 1 : ℚ) := by
    exact le_of_lt (one_div_pos.mpr hnpos)

  rw [abs_of_nonneg hnonneg]

  have hnq :
      (N + 1 : ℚ) ≤ (n + 1 : ℚ) := by
    exact_mod_cast Nat.succ_le_succ hn

  have hNpos :
      (0 : ℚ) < N + 1 := by
    positivity

  have hinvmono :
      1 / (n + 1 : ℚ)
        ≤
      1 / (N + 1 : ℚ) := by
    exact one_div_le_one_div_of_le hNpos hnq

  exact le_trans hinvmono hN

end TaoExercise5_3_5
