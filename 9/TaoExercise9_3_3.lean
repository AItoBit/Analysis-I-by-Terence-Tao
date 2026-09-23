import Mathlib

namespace TaoExercise9_3_3

open Set

/-!
============================================================
Convergence of f to L at x₀ within E
============================================================
-/

def ConvergesAtWithin
    (f : ℝ → ℝ)
    (E : Set ℝ)
    (x₀ L : ℝ) : Prop :=
  ∀ ε : ℝ,
    0 < ε →
    ∃ α : ℝ,
      0 < α ∧
      ∀ x : ℝ,
        x ∈ E →
        abs (x - x₀) < α →
        abs (f x - L) < ε


/-!
============================================================
The local restriction of E to a δ-neighborhood of x₀
============================================================
-/

def LocalSet
    (E : Set ℝ)
    (x₀ δ : ℝ) : Set ℝ :=
  E ∩ Set.Ioo (x₀ - δ) (x₀ + δ)


/-!
============================================================
If f converges on E, then it converges on any subset
============================================================
-/

theorem convergesAtWithin_mono
    (f : ℝ → ℝ)
    (E F : Set ℝ)
    (x₀ L : ℝ)
    (hFE : F ⊆ E)
    (hf : ConvergesAtWithin f E x₀ L) :
    ConvergesAtWithin f F x₀ L := by

  unfold ConvergesAtWithin at hf ⊢

  intro ε hε

  obtain ⟨α, hαpos, hα⟩ :=
    hf ε hε

  refine ⟨α, hαpos, ?_⟩

  intro x hxF hxα

  exact hα
    x
    (hFE hxF)
    hxα


/-!
============================================================
If |x - x₀| < δ, then x lies in (x₀ - δ, x₀ + δ)
============================================================
-/

theorem mem_Ioo_of_abs_sub_lt
    (x x₀ δ : ℝ)
    (h : abs (x - x₀) < δ) :
    x ∈ Set.Ioo (x₀ - δ) (x₀ + δ) := by

  have habs :
      -δ < x - x₀ ∧ x - x₀ < δ := by
    exact abs_lt.mp h

  constructor

  · linarith [habs.1]

  · linarith [habs.2]


/-!
============================================================
Restricted limit -> original limit
============================================================

Suppose f converges after restricting E to

  E ∩ (x₀ - δ, x₀ + δ).

For a given ε, let α be supplied by the restricted
limit and take

  γ = min α δ.

Then |x-x₀| < γ implies both

  |x-x₀| < α
and
  |x-x₀| < δ.

Thus x belongs to the restricted set.
-/

theorem convergesAtWithin_of_local
    (f : ℝ → ℝ)
    (E : Set ℝ)
    (x₀ L δ : ℝ)
    (hδ : 0 < δ)
    (hf :
      ConvergesAtWithin
        f
        (LocalSet E x₀ δ)
        x₀
        L) :
    ConvergesAtWithin f E x₀ L := by

  unfold ConvergesAtWithin at hf ⊢

  intro ε hε

  obtain ⟨α, hαpos, hα⟩ :=
    hf ε hε

  let γ : ℝ := min α δ

  have hγpos :
      0 < γ := by
    dsimp [γ]
    exact lt_min hαpos hδ

  refine ⟨γ, hγpos, ?_⟩

  intro x hxE hxγ

  have hγα :
      γ ≤ α := by
    dsimp [γ]
    exact min_le_left α δ

  have hγδ :
      γ ≤ δ := by
    dsimp [γ]
    exact min_le_right α δ

  have hxα :
      abs (x - x₀) < α := by
    exact lt_of_lt_of_le hxγ hγα

  have hxδ :
      abs (x - x₀) < δ := by
    exact lt_of_lt_of_le hxγ hγδ

  have hxIoo :
      x ∈ Set.Ioo (x₀ - δ) (x₀ + δ) := by
    exact mem_Ioo_of_abs_sub_lt
      x
      x₀
      δ
      hxδ

  have hxLocal :
      x ∈ LocalSet E x₀ δ := by
    exact ⟨hxE, hxIoo⟩

  exact hα
    x
    hxLocal
    hxα


/-!
============================================================
Original limit -> restricted limit
============================================================
-/

theorem convergesAtWithin_local_of_converges
    (f : ℝ → ℝ)
    (E : Set ℝ)
    (x₀ L δ : ℝ)
    (hf : ConvergesAtWithin f E x₀ L) :
    ConvergesAtWithin
      f
      (LocalSet E x₀ δ)
      x₀
      L := by

  apply convergesAtWithin_mono
    f
    E
    (LocalSet E x₀ δ)
    x₀
    L

  · intro x hx
    exact hx.1

  · exact hf


/-!
============================================================
Lemma 9.3.18
============================================================
-/

theorem lemma_9_3_18
    (f : ℝ → ℝ)
    (E : Set ℝ)
    (x₀ L δ : ℝ)
    (hδ : 0 < δ) :
    ConvergesAtWithin
        f
        (E ∩ Set.Ioo (x₀ - δ) (x₀ + δ))
        x₀
        L
      ↔
    ConvergesAtWithin
        f
        E
        x₀
        L := by

  constructor

  · intro hf

    exact convergesAtWithin_of_local
      f
      E
      x₀
      L
      δ
      hδ
      hf

  · intro hf

    exact convergesAtWithin_local_of_converges
      f
      E
      x₀
      L
      δ
      hf


/-!
============================================================
Exercise 9.3.3
============================================================
-/

theorem exercise_9_3_3
    (f : ℝ → ℝ)
    (E : Set ℝ)
    (x₀ L δ : ℝ)
    (hδ : 0 < δ) :
    ConvergesAtWithin
        f
        (E ∩ Set.Ioo (x₀ - δ) (x₀ + δ))
        x₀
        L
      ↔
    ConvergesAtWithin
        f
        E
        x₀
        L := by

  exact lemma_9_3_18
    f
    E
    x₀
    L
    δ
    hδ

end TaoExercise9_3_3
