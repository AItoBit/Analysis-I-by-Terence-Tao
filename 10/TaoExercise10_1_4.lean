import Mathlib

namespace TaoExercise10_1_4

/-!
============================================================
(a) Constant function
============================================================
-/

theorem derivative_const
    (c x₀ : ℝ) :
    HasDerivAt (fun _ : ℝ => c) 0 x₀ := by
  exact hasDerivAt_const x₀ c


/-!
============================================================
(b) Identity
============================================================
-/

theorem derivative_id
    (x₀ : ℝ) :
    HasDerivAt (fun x : ℝ => x) 1 x₀ := by
  change HasDerivAt id 1 x₀
  exact hasDerivAt_id x₀


/-!
============================================================
(c) Sum rule
============================================================
-/

theorem derivative_add
    (f g : ℝ → ℝ)
    (x₀ f' g' : ℝ)
    (hf : HasDerivAt f f' x₀)
    (hg : HasDerivAt g g' x₀) :
    HasDerivAt
      (fun x => f x + g x)
      (f' + g')
      x₀ := by
  exact hf.add hg


/-!
============================================================
(d) Product rule
============================================================
-/

theorem derivative_mul
    (f g : ℝ → ℝ)
    (x₀ f' g' : ℝ)
    (hf : HasDerivAt f f' x₀)
    (hg : HasDerivAt g g' x₀) :
    HasDerivAt
      (fun x => f x * g x)
      (f' * g x₀ + f x₀ * g')
      x₀ := by
  exact hf.mul hg


/-!
============================================================
(e) Constant multiple
============================================================
-/

theorem derivative_const_mul
    (f : ℝ → ℝ)
    (c x₀ f' : ℝ)
    (hf : HasDerivAt f f' x₀) :
    HasDerivAt
      (fun x => c * f x)
      (c * f')
      x₀ := by
  exact hf.const_mul c


/-!
============================================================
(f) Negation
============================================================
-/

theorem derivative_neg
    (f : ℝ → ℝ)
    (x₀ f' : ℝ)
    (hf : HasDerivAt f f' x₀) :
    HasDerivAt
      (fun x => -f x)
      (-f')
      x₀ := by
  exact hf.neg


theorem derivative_sub
    (f g : ℝ → ℝ)
    (x₀ f' g' : ℝ)
    (hf : HasDerivAt f f' x₀)
    (hg : HasDerivAt g g' x₀) :
    HasDerivAt
      (fun x => f x - g x)
      (f' - g')
      x₀ := by
  exact hf.sub hg


/-!
============================================================
(g) Reciprocal
============================================================
-/

theorem derivative_inv
    (g : ℝ → ℝ)
    (x₀ g' : ℝ)
    (hg : HasDerivAt g g' x₀)
    (hg0 : g x₀ ≠ 0) :
    HasDerivAt
      (fun x => (g x)⁻¹)
      (-g' / (g x₀) ^ 2)
      x₀ := by

  change
    HasDerivAt
      (g⁻¹)
      (-g' / (g x₀) ^ 2)
      x₀

  exact hg.inv hg0


/-!
Same reciprocal written 1 / g(x).
-/

theorem derivative_one_div
    (g : ℝ → ℝ)
    (x₀ g' : ℝ)
    (hg : HasDerivAt g g' x₀)
    (hg0 : g x₀ ≠ 0) :
    HasDerivAt
      (fun x => 1 / g x)
      (-g' / (g x₀) ^ 2)
      x₀ := by

  have h :
      HasDerivAt
        (fun x => (g x)⁻¹)
        (-g' / (g x₀) ^ 2)
        x₀ := by
    exact derivative_inv g x₀ g' hg hg0

  simpa [one_div] using h


/-!
============================================================
(h) Quotient
============================================================
-/

theorem derivative_div
    (f g : ℝ → ℝ)
    (x₀ f' g' : ℝ)
    (hf : HasDerivAt f f' x₀)
    (hg : HasDerivAt g g' x₀)
    (hg0 : g x₀ ≠ 0) :
    HasDerivAt
      (fun x => f x / g x)
      ((f' * g x₀ - f x₀ * g') / (g x₀) ^ 2)
      x₀ := by
  exact hf.div hg hg0


/-!
============================================================
Theorem 10.1.13
============================================================
-/

theorem theorem_10_1_13
    (f g : ℝ → ℝ)
    (x₀ f' g' c : ℝ)
    (hf : HasDerivAt f f' x₀)
    (hg : HasDerivAt g g' x₀)
    (hg0 : g x₀ ≠ 0) :
    HasDerivAt (fun _ : ℝ => c) 0 x₀
      ∧
    HasDerivAt (fun x : ℝ => x) 1 x₀
      ∧
    HasDerivAt
      (fun x => f x + g x)
      (f' + g')
      x₀
      ∧
    HasDerivAt
      (fun x => f x * g x)
      (f' * g x₀ + f x₀ * g')
      x₀
      ∧
    HasDerivAt
      (fun x => c * f x)
      (c * f')
      x₀
      ∧
    HasDerivAt
      (fun x => -f x)
      (-f')
      x₀
      ∧
    HasDerivAt
      (fun x => 1 / g x)
      (-g' / (g x₀) ^ 2)
      x₀
      ∧
    HasDerivAt
      (fun x => f x / g x)
      ((f' * g x₀ - f x₀ * g') / (g x₀) ^ 2)
      x₀ := by

  refine ⟨derivative_const c x₀, ?_⟩
  refine ⟨derivative_id x₀, ?_⟩
  refine ⟨derivative_add f g x₀ f' g' hf hg, ?_⟩
  refine ⟨derivative_mul f g x₀ f' g' hf hg, ?_⟩
  refine ⟨derivative_const_mul f c x₀ f' hf, ?_⟩
  refine ⟨derivative_neg f x₀ f' hf, ?_⟩
  refine ⟨derivative_one_div g x₀ g' hg hg0, ?_⟩

  exact derivative_div
    f
    g
    x₀
    f'
    g'
    hf
    hg
    hg0


/-!
============================================================
Exercise 10.1.4
============================================================
-/

theorem exercise_10_1_4
    (f g : ℝ → ℝ)
    (x₀ f' g' c : ℝ)
    (hf : HasDerivAt f f' x₀)
    (hg : HasDerivAt g g' x₀)
    (hg0 : g x₀ ≠ 0) :
    HasDerivAt (fun _ : ℝ => c) 0 x₀
      ∧
    HasDerivAt (fun x : ℝ => x) 1 x₀
      ∧
    HasDerivAt
      (fun x => f x + g x)
      (f' + g')
      x₀
      ∧
    HasDerivAt
      (fun x => f x * g x)
      (f' * g x₀ + f x₀ * g')
      x₀
      ∧
    HasDerivAt
      (fun x => c * f x)
      (c * f')
      x₀
      ∧
    HasDerivAt
      (fun x => -f x)
      (-f')
      x₀
      ∧
    HasDerivAt
      (fun x => 1 / g x)
      (-g' / (g x₀) ^ 2)
      x₀
      ∧
    HasDerivAt
      (fun x => f x / g x)
      ((f' * g x₀ - f x₀ * g') / (g x₀) ^ 2)
      x₀ := by

  exact theorem_10_1_13
    f
    g
    x₀
    f'
    g'
    c
    hf
    hg
    hg0

end TaoExercise10_1_4
