import Mathlib

namespace TaoExercise9_3_1

/-!
============================================================
Convergence of a sequence
============================================================

`SeqConverges a L` means

  ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - L| < ε.
-/

def SeqConverges
    (a : ℕ → ℝ)
    (L : ℝ) : Prop :=
  ∀ ε : ℝ,
    0 < ε →
    ∃ N : ℕ,
      ∀ n : ℕ,
        N ≤ n →
        |a n - L| < ε


/-!
============================================================
Convergence of f to L at x₀ within E
============================================================

This is the ε-δ definition used by Tao.
-/

def ConvergesAtWithin
    (f : ℝ → ℝ)
    (E : Set ℝ)
    (x₀ L : ℝ) : Prop :=
  ∀ ε : ℝ,
    0 < ε →
    ∃ δ : ℝ,
      0 < δ ∧
      ∀ x : ℝ,
        x ∈ E →
        |x - x₀| < δ →
        |f x - L| < ε


/-!
============================================================
(a) -> (b)

If f tends to L at x₀ within E, then it sends every
sequence in E converging to x₀ to a sequence converging
to L.
============================================================
-/

theorem convergence_implies_sequential
    (E : Set ℝ)
    (f : ℝ → ℝ)
    (x₀ L : ℝ)
    (hf : ConvergesAtWithin f E x₀ L) :
    ∀ a : ℕ → ℝ,
      (∀ n : ℕ, a n ∈ E) →
      SeqConverges a x₀ →
      SeqConverges (fun n : ℕ => f (a n)) L := by

  intro a haE ha

  unfold SeqConverges at ha ⊢

  intro ε hε

  obtain ⟨δ, hδpos, hδ⟩ :=
    hf ε hε

  obtain ⟨N, hN⟩ :=
    ha δ hδpos

  refine ⟨N, ?_⟩

  intro n hn

  exact hδ
    (a n)
    (haE n)
    (hN n hn)


/-!
============================================================
Failure of ε-δ convergence produces bad points
============================================================

For a fixed ε witnessing failure, every positive δ
contains a point x ∈ E close to x₀ whose image stays
at least ε away from L.
-/

theorem bad_points_of_not_converges
    (E : Set ℝ)
    (f : ℝ → ℝ)
    (x₀ L ε : ℝ)
    (hε : 0 < ε)
    (hfail :
      ¬ ∃ δ : ℝ,
          0 < δ ∧
          ∀ x : ℝ,
            x ∈ E →
            |x - x₀| < δ →
            |f x - L| < ε) :
    ∀ δ : ℝ,
      0 < δ →
      ∃ x : ℝ,
        x ∈ E ∧
        |x - x₀| < δ ∧
        ε ≤ |f x - L| := by

  intro δ hδpos

  by_contra hNoPoint

  apply hfail

  refine ⟨δ, hδpos, ?_⟩

  intro x hxE hxClose

  by_contra hNotClose

  apply hNoPoint

  refine ⟨x, hxE, hxClose, ?_⟩

  exact le_of_not_gt hNotClose


/-!
============================================================
1/(n+1) tends to zero: elementary ε-N version
============================================================
-/

theorem inv_nat_succ_small :
    ∀ ε : ℝ,
      0 < ε →
      ∃ N : ℕ,
        ∀ n : ℕ,
          N ≤ n →
          1 / (((n + 1 : ℕ) : ℝ)) < ε := by

  intro ε hε

  obtain ⟨N : ℕ, hN⟩ :=
    exists_nat_gt (1 / ε)

  refine ⟨N, ?_⟩

  intro n hn

  have hNn :
      (N : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn

  have hnSucc :
      (n : ℝ) <
        ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_succ_self n

  have hLarge :
      1 / ε <
        ((n + 1 : ℕ) : ℝ) := by
    linarith

  have hDenPos :
      0 <
        ((n + 1 : ℕ) : ℝ) := by
    positivity

  have hProd :
      1 <
        ε * ((n + 1 : ℕ) : ℝ) := by

    have h :=
      (div_lt_iff₀ hε).mp hLarge

    simpa [mul_comm] using h

  apply (div_lt_iff₀ hDenPos).mpr

  simpa [mul_comm] using hProd


/-!
============================================================
A sequence bounded by 1/(n+1) converges to x₀
============================================================
-/

theorem seqConverges_of_inv_bound
    (a : ℕ → ℝ)
    (x₀ : ℝ)
    (hclose :
      ∀ n : ℕ,
        |a n - x₀| <
          1 / (((n + 1 : ℕ) : ℝ))) :
    SeqConverges a x₀ := by

  unfold SeqConverges

  intro ε hε

  obtain ⟨N, hN⟩ :=
    inv_nat_succ_small ε hε

  refine ⟨N, ?_⟩

  intro n hn

  exact lt_trans
    (hclose n)
    (hN n hn)


/-!
============================================================
(b) -> (a)

Contrapositive construction from Tao:
choose aₙ ∈ E within 1/(n+1) of x₀, while keeping
f(aₙ) at least ε away from L.
============================================================
-/

theorem sequential_implies_convergence
    (E : Set ℝ)
    (f : ℝ → ℝ)
    (x₀ L : ℝ)
    (hseq :
      ∀ a : ℕ → ℝ,
        (∀ n : ℕ, a n ∈ E) →
        SeqConverges a x₀ →
        SeqConverges (fun n : ℕ => f (a n)) L) :
    ConvergesAtWithin f E x₀ L := by

  unfold ConvergesAtWithin

  intro ε hε

  by_contra hNoDelta

  have hbad :
      ∀ δ : ℝ,
        0 < δ →
        ∃ x : ℝ,
          x ∈ E ∧
          |x - x₀| < δ ∧
          ε ≤ |f x - L| := by

    exact bad_points_of_not_converges
      E
      f
      x₀
      L
      ε
      hε
      hNoDelta

  have hExists :
      ∀ n : ℕ,
        ∃ x : ℝ,
          x ∈ E ∧
          |x - x₀| <
            1 / (((n + 1 : ℕ) : ℝ)) ∧
          ε ≤ |f x - L| := by

    intro n

    have hRadius :
        0 <
          1 / (((n + 1 : ℕ) : ℝ)) := by
      positivity

    exact hbad
      (1 / (((n + 1 : ℕ) : ℝ)))
      hRadius

  choose a ha using hExists

  have haE :
      ∀ n : ℕ, a n ∈ E := by
    intro n
    exact (ha n).1

  have haClose :
      ∀ n : ℕ,
        |a n - x₀| <
          1 / (((n + 1 : ℕ) : ℝ)) := by
    intro n
    exact (ha n).2.1

  have haFar :
      ∀ n : ℕ,
        ε ≤ |f (a n) - L| := by
    intro n
    exact (ha n).2.2

  have haLim :
      SeqConverges a x₀ := by
    exact seqConverges_of_inv_bound
      a
      x₀
      haClose

  have hfaLim :
      SeqConverges
        (fun n : ℕ => f (a n))
        L := by
    exact hseq
      a
      haE
      haLim

  obtain ⟨N, hN⟩ :=
    hfaLim ε hε

  have hNear :
      |f (a N) - L| < ε := by
    exact hN N le_rfl

  have hFar :
      ε ≤ |f (a N) - L| := by
    exact haFar N

  linarith


/-!
============================================================
Proposition 9.3.9
============================================================
-/

theorem proposition_9_3_9
    (E : Set ℝ)
    (f : ℝ → ℝ)
    (x₀ L : ℝ) :
    ConvergesAtWithin f E x₀ L
      ↔
    ∀ a : ℕ → ℝ,
      (∀ n : ℕ, a n ∈ E) →
      SeqConverges a x₀ →
      SeqConverges (fun n : ℕ => f (a n)) L := by

  constructor

  · intro hf

    exact convergence_implies_sequential
      E
      f
      x₀
      L
      hf

  · intro hseq

    exact sequential_implies_convergence
      E
      f
      x₀
      L
      hseq


/-!
============================================================
Exercise 9.3.1
============================================================
-/

theorem exercise_9_3_1
    (E : Set ℝ)
    (f : ℝ → ℝ)
    (x₀ L : ℝ) :
    ConvergesAtWithin f E x₀ L
      ↔
    ∀ a : ℕ → ℝ,
      (∀ n : ℕ, a n ∈ E) →
      SeqConverges a x₀ →
      SeqConverges (fun n : ℕ => f (a n)) L := by

  exact proposition_9_3_9
    E
    f
    x₀
    L

end TaoExercise9_3_1
