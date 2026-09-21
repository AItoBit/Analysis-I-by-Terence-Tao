import Mathlib

namespace TaoExercise4_4_2

def NatInfiniteDescent (a : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, a (n + 1) < a n

theorem no_nat_infinite_descent :
    ¬ ∃ a : ℕ → ℕ, NatInfiniteDescent a := by

  rintro ⟨a, hdesc⟩

  let S : Set ℕ :=
    Set.range a

  have hSne : S.Nonempty := by
    refine ⟨a 0, ?_⟩
    exact ⟨0, rfl⟩

  let m : ℕ :=
    sInf S

  have hm_mem : m ∈ S := by
    exact Nat.sInf_mem hSne

  obtain ⟨k, hk⟩ := hm_mem

  have hkdesc :
      a (k + 1) < a k :=
    hdesc k

  have hnext_mem :
      a (k + 1) ∈ S := by
    exact ⟨k + 1, rfl⟩

  have hmin :
      m ≤ a (k + 1) := by
    exact Nat.sInf_le hnext_mem

  rw [hk] at hkdesc

  exact (not_lt_of_ge hmin) hkdesc

end TaoExercise4_4_2
