import Mathlib

namespace TaoExercise6_1_8

/--
A real sequence `a` converges to `L` starting from index `m`.
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


/-!
============================================================
Useful preliminary lemma: constant sequences converge.
============================================================
-/

theorem converges_const
    (c : ℝ)
    (m : ℕ) :
    ConvergesFrom (fun _ : ℕ => c) m c := by

  intro ε hε

  refine ⟨m, le_rfl, ?_⟩

  intro n hn

  simp [le_of_lt hε]


/-!
============================================================
(a) Sum law

If aₙ → x and bₙ → y, then

    aₙ + bₙ → x + y.
============================================================
-/

theorem converges_add
    (a b : ℕ → ℝ)
    (m : ℕ)
    (x y : ℝ)
    (ha : ConvergesFrom a m x)
    (hb : ConvergesFrom b m y) :
    ConvergesFrom
      (fun n => a n + b n)
      m
      (x + y) := by

  intro ε hε

  have hε2 :
      0 < ε / 2 := by
    linarith

  obtain ⟨Na, hmNa, hNa⟩ :=
    ha (ε / 2) hε2

  obtain ⟨Nb, hmNb, hNb⟩ :=
    hb (ε / 2) hε2

  let N : ℕ := max Na Nb

  refine ⟨N, ?_, ?_⟩

  · dsimp [N]
    omega

  · intro n hn

    have hNaN :
        Na ≤ n := by
      dsimp [N] at hn
      omega

    have hNbN :
        Nb ≤ n := by
      dsimp [N] at hn
      omega

    have haClose :
        |a n - x| ≤ ε / 2 := by
      exact hNa n hNaN

    have hbClose :
        |b n - y| ≤ ε / 2 := by
      exact hNb n hNbN

    have hrewrite :
        (a n + b n) - (x + y) =
          (a n - x) + (b n - y) := by
      ring

    rw [hrewrite]

    calc
      |(a n - x) + (b n - y)|
          ≤ |a n - x| + |b n - y| := by
            exact abs_add_le _ _

      _ ≤ ε / 2 + ε / 2 := by
            exact add_le_add haClose hbClose

      _ = ε := by
            ring


/-!
============================================================
(b) Product law

If aₙ → x and bₙ → y, then

    aₙbₙ → xy.
============================================================
-/

theorem converges_mul
    (a b : ℕ → ℝ)
    (m : ℕ)
    (x y : ℝ)
    (ha : ConvergesFrom a m x)
    (hb : ConvergesFrom b m y) :
    ConvergesFrom
      (fun n => a n * b n)
      m
      (x * y) := by

  intro ε hε

  /-
  We eventually bound |aₙ| by |x| + 1.
  -/
  obtain ⟨Nbound, hmNbound, hNbound⟩ :=
    ha 1 (by norm_num)

  have hApos :
      0 < |x| + 1 := by
    positivity

  have hYpos :
      0 < |y| + 1 := by
    positivity

  /-
  Required accuracy for bₙ - y.
  -/
  have hδb :
      0 < ε / (2 * (|x| + 1)) := by
    positivity

  obtain ⟨Nb, hmNb, hNb⟩ :=
    hb (ε / (2 * (|x| + 1))) hδb

  /-
  Required accuracy for aₙ - x.
  -/
  have hδa :
      0 < ε / (2 * (|y| + 1)) := by
    positivity

  obtain ⟨Na, hmNa, hNa⟩ :=
    ha (ε / (2 * (|y| + 1))) hδa

  let N : ℕ := max Nbound (max Na Nb)

  refine ⟨N, ?_, ?_⟩

  · dsimp [N]
    omega

  · intro n hn

    have hnBound :
        Nbound ≤ n := by
      dsimp [N] at hn
      omega

    have hnA :
        Na ≤ n := by
      dsimp [N] at hn
      omega

    have hnB :
        Nb ≤ n := by
      dsimp [N] at hn
      omega

    have haOne :
        |a n - x| ≤ 1 := by
      exact hNbound n hnBound

    have haBound :
        |a n| ≤ |x| + 1 := by

      have htriangle :
          |a n| ≤ |a n - x| + |x| := by
        calc
          |a n|
              =
            |(a n - x) + x| := by
              ring_nf

          _ ≤ |a n - x| + |x| := by
              exact abs_add_le _ _

      linarith

    have hbClose :
        |b n - y| ≤ ε / (2 * (|x| + 1)) := by
      exact hNb n hnB

    have haClose :
        |a n - x| ≤ ε / (2 * (|y| + 1)) := by
      exact hNa n hnA

    have hterm1 :
        |a n| * |b n - y| ≤ ε / 2 := by

      calc
        |a n| * |b n - y|
            ≤
          (|x| + 1) *
            (ε / (2 * (|x| + 1))) := by

              exact
                mul_le_mul
                  haBound
                  hbClose
                  (abs_nonneg _)
                  (le_of_lt hApos)

        _ = ε / 2 := by
              field_simp [ne_of_gt hApos]

    have hyBound :
        |y| ≤ |y| + 1 := by
      linarith

    have hterm2 :
        |y| * |a n - x| ≤ ε / 2 := by

      calc
        |y| * |a n - x|
            ≤
          (|y| + 1) *
            (ε / (2 * (|y| + 1))) := by

              exact
                mul_le_mul
                  hyBound
                  haClose
                  (abs_nonneg _)
                  (le_of_lt hYpos)

        _ = ε / 2 := by
              field_simp [ne_of_gt hYpos]

    have halgebra :
        a n * b n - x * y =
          a n * (b n - y) +
          y * (a n - x) := by
      ring

    rw [halgebra]

    calc
      |a n * (b n - y) + y * (a n - x)|
          ≤
        |a n * (b n - y)| +
          |y * (a n - x)| := by
            exact abs_add_le _ _

      _ =
        |a n| * |b n - y| +
          |y| * |a n - x| := by
            rw [abs_mul, abs_mul]

      _ ≤ ε / 2 + ε / 2 := by
            exact add_le_add hterm1 hterm2

      _ = ε := by
            ring


/-!
============================================================
(c) Scalar multiplication

If aₙ → x, then

    c aₙ → c x.
============================================================
-/

theorem converges_const_mul
    (a : ℕ → ℝ)
    (m : ℕ)
    (x c : ℝ)
    (ha : ConvergesFrom a m x) :
    ConvergesFrom
      (fun n => c * a n)
      m
      (c * x) := by

  have hc :
      ConvergesFrom
        (fun _ : ℕ => c)
        m
        c := by
    exact converges_const c m

  exact converges_mul
    (fun _ : ℕ => c)
    a
    m
    c
    x
    hc
    ha


/-!
============================================================
(d) Difference law

If aₙ → x and bₙ → y, then

    aₙ - bₙ → x - y.
============================================================
-/

theorem converges_sub
    (a b : ℕ → ℝ)
    (m : ℕ)
    (x y : ℝ)
    (ha : ConvergesFrom a m x)
    (hb : ConvergesFrom b m y) :
    ConvergesFrom
      (fun n => a n - b n)
      m
      (x - y) := by

  have hneg :
      ConvergesFrom
        (fun n => (-1 : ℝ) * b n)
        m
        ((-1 : ℝ) * y) := by
    exact converges_const_mul b m y (-1) hb

  have hadd :
      ConvergesFrom
        (fun n =>
          a n + ((-1 : ℝ) * b n))
        m
        (x + ((-1 : ℝ) * y)) := by

    exact converges_add
      a
      (fun n => (-1 : ℝ) * b n)
      m
      x
      ((-1 : ℝ) * y)
      ha
      hneg

  simpa [sub_eq_add_neg] using hadd


/-!
============================================================
(e) Reciprocal law

If bₙ → y and y ≠ 0, then

    1 / bₙ → 1 / y.
============================================================
-/

theorem converges_inv
    (b : ℕ → ℝ)
    (m : ℕ)
    (y : ℝ)
    (hb : ConvergesFrom b m y)
    (hy : y ≠ 0) :
    ConvergesFrom
      (fun n => 1 / b n)
      m
      (1 / y) := by

  intro ε hε

  have habsyPos :
      0 < |y| := by
    exact abs_pos.mpr hy

  /-
  First force bₙ away from zero.
  -/
  have hhalf :
      0 < |y| / 2 := by
    positivity

  obtain ⟨N₀, hmN₀, hN₀⟩ :=
    hb (|y| / 2) hhalf

  /-
  Then request enough accuracy to control the reciprocal.
  -/
  let δ : ℝ :=
    ε * (|y| * |y| / 2)

  have hδ :
      0 < δ := by
    dsimp [δ]
    positivity

  obtain ⟨N₁, hmN₁, hN₁⟩ :=
    hb δ hδ

  let N : ℕ := max N₀ N₁

  refine ⟨N, ?_, ?_⟩

  · dsimp [N]
    omega

  · intro n hn

    have hn₀ :
        N₀ ≤ n := by
      dsimp [N] at hn
      omega

    have hn₁ :
        N₁ ≤ n := by
      dsimp [N] at hn
      omega

    have hcloseHalf :
        |b n - y| ≤ |y| / 2 := by
      exact hN₀ n hn₀

    have htriangle :
        |y| ≤ |y - b n| + |b n| := by
      calc
        |y|
            =
          |(y - b n) + b n| := by
            ring_nf

        _ ≤ |y - b n| + |b n| := by
            exact abs_add_le _ _

    have htriangle' :
        |y| ≤ |b n - y| + |b n| := by
      simpa [abs_sub_comm] using htriangle

    have hbnLower :
        |y| / 2 ≤ |b n| := by
      linarith

    have hbnAbsPos :
        0 < |b n| := by
      exact lt_of_lt_of_le hhalf hbnLower

    have hbn0 :
        b n ≠ 0 := by
      exact abs_pos.mp hbnAbsPos

    have hcloseδ :
        |b n - y| ≤ δ := by
      exact hN₁ n hn₁

    have hnum :
        |y - b n|
          ≤ ε * (|y| * |y| / 2) := by
      dsimp [δ] at hcloseδ
      simpa [abs_sub_comm] using hcloseδ

    have hdenLower :
        |y| * |y| / 2
          ≤ |b n| * |y| := by

      calc
        |y| * |y| / 2
            =
          (|y| / 2) * |y| := by
            ring

        _ ≤ |b n| * |y| := by
            exact
              mul_le_mul_of_nonneg_right
                hbnLower
                (abs_nonneg y)

    have hscaled :
        ε * (|y| * |y| / 2)
          ≤
        ε * (|b n| * |y|) := by

      exact
        mul_le_mul_of_nonneg_left
          hdenLower
          (le_of_lt hε)

    have hnumFinal :
        |y - b n|
          ≤
        ε * (|b n| * |y|) := by
      exact le_trans hnum hscaled

    have halgebra :
        1 / b n - 1 / y =
          (y - b n) / (b n * y) := by
      field_simp [hbn0, hy]

    rw [halgebra, abs_div, abs_mul]

    have hdenPos :
        0 < |b n| * |y| := by
      exact mul_pos hbnAbsPos habsyPos

    apply (div_le_iff₀ hdenPos).2

    exact hnumFinal


/-!
============================================================
(f) Quotient law

If aₙ → x, bₙ → y and y ≠ 0, then

    aₙ / bₙ → x / y.
============================================================
-/

theorem converges_div
    (a b : ℕ → ℝ)
    (m : ℕ)
    (x y : ℝ)
    (ha : ConvergesFrom a m x)
    (hb : ConvergesFrom b m y)
    (hy : y ≠ 0) :
    ConvergesFrom
      (fun n => a n / b n)
      m
      (x / y) := by

  have hinv :
      ConvergesFrom
        (fun n => 1 / b n)
        m
        (1 / y) := by

    exact converges_inv
      b
      m
      y
      hb
      hy

  have hmul :
      ConvergesFrom
        (fun n => a n * (1 / b n))
        m
        (x * (1 / y)) := by

    exact converges_mul
      a
      (fun n => 1 / b n)
      m
      x
      (1 / y)
      ha
      hinv

  simpa [div_eq_mul_inv] using hmul


/-!
============================================================
(g) Maximum law

If aₙ → x and bₙ → y, then

    max(aₙ,bₙ) → max(x,y).
============================================================
-/

theorem converges_max
    (a b : ℕ → ℝ)
    (m : ℕ)
    (x y : ℝ)
    (ha : ConvergesFrom a m x)
    (hb : ConvergesFrom b m y) :
    ConvergesFrom
      (fun n => max (a n) (b n))
      m
      (max x y) := by

  intro ε hε

  obtain ⟨Na, hmNa, hNa⟩ :=
    ha ε hε

  obtain ⟨Nb, hmNb, hNb⟩ :=
    hb ε hε

  let N : ℕ := max Na Nb

  refine ⟨N, ?_, ?_⟩

  · dsimp [N]
    omega

  · intro n hn

    have hnA :
        Na ≤ n := by
      dsimp [N] at hn
      omega

    have hnB :
        Nb ≤ n := by
      dsimp [N] at hn
      omega

    have haClose :
        |a n - x| ≤ ε := by
      exact hNa n hnA

    have hbClose :
        |b n - y| ≤ ε := by
      exact hNb n hnB

    have haBounds :
        -ε ≤ a n - x ∧
        a n - x ≤ ε :=
      abs_le.mp haClose

    have hbBounds :
        -ε ≤ b n - y ∧
        b n - y ≤ ε :=
      abs_le.mp hbClose

    by_cases hxy : y ≤ x

    /-
    Case x ≥ y.
    -/
    · rw [max_eq_left hxy]

      apply abs_le.mpr

      constructor

      · have hLower :
            x - ε ≤ max (a n) (b n) := by

          have hax :
              x - ε ≤ a n := by
            linarith [haBounds.1]

          exact le_trans hax (le_max_left _ _)

        linarith

      · have haUpper :
            a n ≤ x + ε := by
          linarith [haBounds.2]

        have hbUpper :
            b n ≤ x + ε := by
          have :
              b n ≤ y + ε := by
            linarith [hbBounds.2]

          linarith

        have hUpper :
            max (a n) (b n) ≤ x + ε := by
          exact max_le haUpper hbUpper

        linarith

    /-
    Case x < y.
    -/
    · have hxy' :
          x ≤ y := by
        exact le_of_lt (lt_of_not_ge hxy)

      rw [max_eq_right hxy']

      apply abs_le.mpr

      constructor

      · have hLower :
            y - ε ≤ max (a n) (b n) := by

          have hby :
              y - ε ≤ b n := by
            linarith [hbBounds.1]

          exact le_trans hby (le_max_right _ _)

        linarith

      · have hbUpper :
            b n ≤ y + ε := by
          linarith [hbBounds.2]

        have haUpper :
            a n ≤ y + ε := by

          have :
              a n ≤ x + ε := by
            linarith [haBounds.2]

          linarith

        have hUpper :
            max (a n) (b n) ≤ y + ε := by
          exact max_le haUpper hbUpper

        linarith


/-!
============================================================
(h) Minimum law

If aₙ → x and bₙ → y, then

    min(aₙ,bₙ) → min(x,y).
============================================================
-/

theorem converges_min
    (a b : ℕ → ℝ)
    (m : ℕ)
    (x y : ℝ)
    (ha : ConvergesFrom a m x)
    (hb : ConvergesFrom b m y) :
    ConvergesFrom
      (fun n => min (a n) (b n))
      m
      (min x y) := by

  intro ε hε

  obtain ⟨Na, hmNa, hNa⟩ :=
    ha ε hε

  obtain ⟨Nb, hmNb, hNb⟩ :=
    hb ε hε

  let N : ℕ := max Na Nb

  refine ⟨N, ?_, ?_⟩

  · dsimp [N]
    omega

  · intro n hn

    have hnA :
        Na ≤ n := by
      dsimp [N] at hn
      omega

    have hnB :
        Nb ≤ n := by
      dsimp [N] at hn
      omega

    have haClose :
        |a n - x| ≤ ε := by
      exact hNa n hnA

    have hbClose :
        |b n - y| ≤ ε := by
      exact hNb n hnB

    have haBounds :
        -ε ≤ a n - x ∧
        a n - x ≤ ε :=
      abs_le.mp haClose

    have hbBounds :
        -ε ≤ b n - y ∧
        b n - y ≤ ε :=
      abs_le.mp hbClose

    by_cases hxy : x ≤ y

    /-
    Case x ≤ y.
    -/
    · rw [min_eq_left hxy]

      apply abs_le.mpr

      constructor

      · have haLower :
            x - ε ≤ a n := by
          linarith [haBounds.1]

        have hbLower :
            x - ε ≤ b n := by

          have :
              y - ε ≤ b n := by
            linarith [hbBounds.1]

          linarith

        have hLower :
            x - ε ≤ min (a n) (b n) := by
          exact le_min haLower hbLower

        linarith

      · have hUpper :
            min (a n) (b n) ≤ x + ε := by

          have haUpper :
              a n ≤ x + ε := by
            linarith [haBounds.2]

          exact le_trans (min_le_left _ _) haUpper

        linarith

    /-
    Case y < x.
    -/
    · have hyx :
          y ≤ x := by
        exact le_of_lt (lt_of_not_ge hxy)

      rw [min_eq_right hyx]

      apply abs_le.mpr

      constructor

      · have hbLower :
            y - ε ≤ b n := by
          linarith [hbBounds.1]

        have haLower :
            y - ε ≤ a n := by

          have :
              x - ε ≤ a n := by
            linarith [haBounds.1]

          linarith

        have hLower :
            y - ε ≤ min (a n) (b n) := by
          exact le_min haLower hbLower

        linarith

      · have hUpper :
            min (a n) (b n) ≤ y + ε := by

          have hbUpper :
              b n ≤ y + ε := by
            linarith [hbBounds.2]

          exact le_trans (min_le_right _ _) hbUpper

        linarith


/-!
============================================================
Theorem 6.1.19 — convenient wrappers
============================================================
-/

/-- Part (a). -/
theorem theorem_6_1_19_a
    (a b : ℕ → ℝ)
    (m : ℕ)
    (x y : ℝ)
    (ha : ConvergesFrom a m x)
    (hb : ConvergesFrom b m y) :
    ConvergesFrom (fun n => a n + b n) m (x + y) := by

  exact converges_add a b m x y ha hb


/-- Part (b). -/
theorem theorem_6_1_19_b
    (a b : ℕ → ℝ)
    (m : ℕ)
    (x y : ℝ)
    (ha : ConvergesFrom a m x)
    (hb : ConvergesFrom b m y) :
    ConvergesFrom (fun n => a n * b n) m (x * y) := by

  exact converges_mul a b m x y ha hb


/-- Part (c). -/
theorem theorem_6_1_19_c
    (a : ℕ → ℝ)
    (m : ℕ)
    (x c : ℝ)
    (ha : ConvergesFrom a m x) :
    ConvergesFrom (fun n => c * a n) m (c * x) := by

  exact converges_const_mul a m x c ha


/-- Part (d). -/
theorem theorem_6_1_19_d
    (a b : ℕ → ℝ)
    (m : ℕ)
    (x y : ℝ)
    (ha : ConvergesFrom a m x)
    (hb : ConvergesFrom b m y) :
    ConvergesFrom (fun n => a n - b n) m (x - y) := by

  exact converges_sub a b m x y ha hb


/-- Part (e). -/
theorem theorem_6_1_19_e
    (b : ℕ → ℝ)
    (m : ℕ)
    (y : ℝ)
    (hb : ConvergesFrom b m y)
    (hy : y ≠ 0) :
    ConvergesFrom (fun n => 1 / b n) m (1 / y) := by

  exact converges_inv b m y hb hy


/-- Part (f). -/
theorem theorem_6_1_19_f
    (a b : ℕ → ℝ)
    (m : ℕ)
    (x y : ℝ)
    (ha : ConvergesFrom a m x)
    (hb : ConvergesFrom b m y)
    (hy : y ≠ 0) :
    ConvergesFrom (fun n => a n / b n) m (x / y) := by

  exact converges_div a b m x y ha hb hy


/-- Part (g). -/
theorem theorem_6_1_19_g
    (a b : ℕ → ℝ)
    (m : ℕ)
    (x y : ℝ)
    (ha : ConvergesFrom a m x)
    (hb : ConvergesFrom b m y) :
    ConvergesFrom
      (fun n => max (a n) (b n))
      m
      (max x y) := by

  exact converges_max a b m x y ha hb


/-- Part (h). -/
theorem theorem_6_1_19_h
    (a b : ℕ → ℝ)
    (m : ℕ)
    (x y : ℝ)
    (ha : ConvergesFrom a m x)
    (hb : ConvergesFrom b m y) :
    ConvergesFrom
      (fun n => min (a n) (b n))
      m
      (min x y) := by

  exact converges_min a b m x y ha hb

end TaoExercise6_1_8
