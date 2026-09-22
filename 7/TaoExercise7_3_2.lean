import Mathlib

namespace TaoExercise7_3_2

def partialSum
    (a : ℕ → ℝ)
    (N : ℕ) : ℝ :=
  (Finset.range (N + 1)).sum a

def SeriesHasSum
    (a : ℕ → ℝ)
    (L : ℝ) : Prop :=
  Filter.Tendsto
    (partialSum a)
    Filter.atTop
    (nhds L)

def SeriesConverges
    (a : ℕ → ℝ) : Prop :=
  ∃ L : ℝ, SeriesHasSum a L

def AbsolutelyConverges
    (a : ℕ → ℝ) : Prop :=
  SeriesConverges
    (fun n => abs (a n))

theorem partialSum_succ
    (a : ℕ → ℝ)
    (N : ℕ) :
    partialSum a (N + 1)
      =
    partialSum a N + a (N + 1) := by
  unfold partialSum
  rw [Finset.sum_range_succ]

theorem term_eq_partialSum_sub
    (a : ℕ → ℝ)
    (n : ℕ)
    (hn : 1 ≤ n) :
    a n
      =
    partialSum a n
      -
    partialSum a (n - 1) := by
  have hnEq :
      (n - 1) + 1 = n := by
    omega
  have hrec :=
    partialSum_succ a (n - 1)
  rw [hnEq] at hrec
  linarith

theorem terms_tendsto_zero_of_seriesHasSum
    (a : ℕ → ℝ)
    (L : ℝ)
    (h : SeriesHasSum a L) :
    Filter.Tendsto
      a
      Filter.atTop
      (nhds 0) := by

  apply Metric.tendsto_atTop.mpr
  intro ε hε

  have hhalf :
      0 < ε / 2 := by
    linarith

  have hmetric :=
    Metric.tendsto_atTop.mp h

  obtain ⟨M, hM⟩ :=
    hmetric (ε / 2) hhalf

  refine ⟨M + 1, ?_⟩
  intro n hn

  have hnPos :
      1 ≤ n := by
    omega

  have hMn :
      M ≤ n := by
    omega

  have hMprev :
      M ≤ n - 1 := by
    omega

  have hnClose :
      dist
        (partialSum a n)
        L
        < ε / 2 := by
    exact hM n hMn

  have hprevClose :
      dist
        (partialSum a (n - 1))
        L
        < ε / 2 := by
    exact hM (n - 1) hMprev

  have hterm :
      a n
        =
      partialSum a n
        -
      partialSum a (n - 1) := by
    exact term_eq_partialSum_sub
      a
      n
      hnPos

  rw [Real.dist_eq] at hnClose hprevClose ⊢
  rw [hterm]

  have hrearrange :
      (
        partialSum a n
          -
        partialSum a (n - 1)
      ) - 0
        =
      (
        partialSum a n - L
      )
        -
      (
        partialSum a (n - 1) - L
      ) := by
    ring

  rw [hrearrange]

  calc
    abs
      (
        (partialSum a n - L)
          -
        (partialSum a (n - 1) - L)
      )
        =
      abs
        (
          (partialSum a n - L)
            +
          (L - partialSum a (n - 1))
        ) := by
          congr 1
          ring

    _ ≤
      abs (partialSum a n - L)
        +
      abs (L - partialSum a (n - 1)) := by
          exact abs_add_le _ _

    _ =
      abs (partialSum a n - L)
        +
      abs (partialSum a (n - 1) - L) := by
          rw [
            abs_sub_comm
              L
              (partialSum a (n - 1))
          ]

    _ <
      ε / 2 + ε / 2 := by
          exact add_lt_add
            hnClose
            hprevClose

    _ = ε := by
      ring

theorem geometric_partial_sum_formula
    (x : ℝ)
    (hx : x ≠ 1)
    (N : ℕ) :
    partialSum
        (fun n => x ^ n)
        N
      =
    (1 - x ^ (N + 1)) / (1 - x) := by

  have hden :
      1 - x ≠ 0 := by
    exact sub_ne_zero.mpr
      (Ne.symm hx)

  induction N with

  | zero =>
      unfold partialSum
      simp
      field_simp [hden]

  | succ N ih =>
      rw [partialSum_succ]
      rw [ih]

      have hpow :
          x ^ (N + 2)
            =
          x ^ (N + 1) * x := by
        rw [pow_succ]

      rw [hpow]
      field_simp [hden]
      ring

theorem pow_succ_tendsto_zero
    (x : ℝ)
    (hx : abs x < 1) :
    Filter.Tendsto
      (fun N : ℕ => x ^ (N + 1))
      Filter.atTop
      (nhds 0) := by

  have hpow :
      Filter.Tendsto
        (fun N : ℕ => x ^ N)
        Filter.atTop
        (nhds 0) := by
    exact
      tendsto_pow_atTop_nhds_zero_of_abs_lt_one
        hx

  have hmul :
      Filter.Tendsto
        (fun N : ℕ => x ^ N * x)
        Filter.atTop
        (nhds (0 * x)) := by
    exact hpow.mul_const x

  simpa [pow_succ] using hmul

theorem geometric_series_hasSum
    (x : ℝ)
    (hx : abs x < 1) :
    SeriesHasSum
      (fun n => x ^ n)
      (1 / (1 - x)) := by

  have hx1 :
      x ≠ 1 := by
    intro hxEq
    subst x
    norm_num at hx

  have hpow :
      Filter.Tendsto
        (fun N : ℕ => x ^ (N + 1))
        Filter.atTop
        (nhds 0) := by
    exact pow_succ_tendsto_zero
      x
      hx

  have hone :
      Filter.Tendsto
        (fun _ : ℕ => (1 : ℝ))
        Filter.atTop
        (nhds 1) := by
    exact tendsto_const_nhds

  have hnum :
      Filter.Tendsto
        (fun N : ℕ =>
          1 - x ^ (N + 1))
        Filter.atTop
        (nhds (1 - 0)) := by
    exact hone.sub hpow

  have hconst :
      Filter.Tendsto
        (fun _ : ℕ =>
          ((1 - x)⁻¹ : ℝ))
        Filter.atTop
        (nhds ((1 - x)⁻¹)) := by
    exact tendsto_const_nhds

  have hmul :
      Filter.Tendsto
        (fun N : ℕ =>
          (1 - x ^ (N + 1))
            *
          (1 - x)⁻¹)
        Filter.atTop
        (nhds
          (
            (1 - 0)
              *
            (1 - x)⁻¹
          )) := by
    exact hnum.mul hconst

  unfold SeriesHasSum

  have hEq :
      partialSum
        (fun n => x ^ n)
        =
      (fun N =>
        (1 - x ^ (N + 1))
          /
        (1 - x)) := by
    funext N
    exact geometric_partial_sum_formula
      x
      hx1
      N

  rw [hEq]

  simpa [div_eq_mul_inv] using hmul

theorem geometric_series_converges
    (x : ℝ)
    (hx : abs x < 1) :
    SeriesConverges
      (fun n => x ^ n) := by
  exact
    ⟨1 / (1 - x),
      geometric_series_hasSum x hx⟩

theorem abs_pow_eq
    (x : ℝ)
    (n : ℕ) :
    abs (x ^ n)
      =
    (abs x) ^ n := by

  induction n with

  | zero =>
      simp

  | succ n ih =>
      rw [pow_succ, pow_succ, abs_mul, ih]

theorem geometric_series_absolutelyConverges
    (x : ℝ)
    (hx : abs x < 1) :
    AbsolutelyConverges
      (fun n => x ^ n) := by

  unfold AbsolutelyConverges

  have habsx :
      abs (abs x) < 1 := by
    rw [abs_of_nonneg (abs_nonneg x)]
    exact hx

  have hgeom :
      SeriesConverges
        (fun n => (abs x) ^ n) := by
    exact geometric_series_converges
      (abs x)
      habsx

  have hEq :
      (fun n : ℕ => abs (x ^ n))
        =
      (fun n : ℕ => (abs x) ^ n) := by
    funext n
    exact abs_pow_eq
      x
      n

  rw [hEq]

  exact hgeom

theorem powers_tendsto_zero_of_series_converges
    (x : ℝ)
    (hconv :
      SeriesConverges
        (fun n => x ^ n)) :
    Filter.Tendsto
      (fun n : ℕ => x ^ n)
      Filter.atTop
      (nhds 0) := by

  rcases hconv with
    ⟨L, hL⟩

  exact
    terms_tendsto_zero_of_seriesHasSum
      (fun n => x ^ n)
      L
      hL

theorem abs_lt_one_of_powers_tendsto_zero
    (x : ℝ)
    (hpow :
      Filter.Tendsto
        (fun n : ℕ => x ^ n)
        Filter.atTop
        (nhds 0)) :
    abs x < 1 := by

  by_contra hnot

  have hx :
      1 ≤ abs x := by
    exact le_of_not_gt hnot

  have hLower :
      ∀ n : ℕ,
        (1 : ℝ) ≤ abs (x ^ n) := by

    intro n

    induction n with

    | zero =>
        norm_num

    | succ n ih =>

        rw [pow_succ, abs_mul]

        have hnonnegPow :
            0 ≤ abs (x ^ n) := by
          exact abs_nonneg _

        have hnonnegX :
            0 ≤ abs x := by
          exact abs_nonneg _

        nlinarith

  have hmetric :=
    Metric.tendsto_atTop.mp hpow

  obtain ⟨N, hN⟩ :=
    hmetric (1 / 2) (by norm_num)

  have hclose :
      dist
        (x ^ N)
        0
        < 1 / 2 := by
    exact hN N le_rfl

  rw [Real.dist_eq] at hclose

  have hsmall :
      abs (x ^ N) < 1 / 2 := by
    simpa using hclose

  have hlarge :
      1 ≤ abs (x ^ N) := by
    exact hLower N

  linarith

theorem abs_lt_one_of_geometric_series_converges
    (x : ℝ)
    (hconv :
      SeriesConverges
        (fun n => x ^ n)) :
    abs x < 1 := by

  have hpow :
      Filter.Tendsto
        (fun n : ℕ => x ^ n)
        Filter.atTop
        (nhds 0) := by
    exact powers_tendsto_zero_of_series_converges
      x
      hconv

  exact abs_lt_one_of_powers_tendsto_zero
    x
    hpow

theorem geometric_series_diverges
    (x : ℝ)
    (hx : 1 ≤ abs x) :
    ¬ SeriesConverges
        (fun n => x ^ n) := by

  intro hconv

  have hlt :
      abs x < 1 := by
    exact
      abs_lt_one_of_geometric_series_converges
        x
        hconv

  exact
    (not_lt_of_ge hx)
      hlt

theorem geometric_series_converges_iff
    (x : ℝ) :
    SeriesConverges
        (fun n => x ^ n)
      ↔
    abs x < 1 := by

  constructor

  · intro hconv
    exact
      abs_lt_one_of_geometric_series_converges
        x
        hconv

  · intro hx
    exact
      geometric_series_converges
        x
        hx

theorem lemma_7_3_3
    (x : ℝ) :
    (
      SeriesConverges
          (fun n => x ^ n)
        ↔
      abs x < 1
    )
    ∧
    (
      abs x < 1 →
      SeriesHasSum
        (fun n => x ^ n)
        (1 / (1 - x))
    )
    ∧
    (
      abs x < 1 →
      AbsolutelyConverges
        (fun n => x ^ n)
    ) := by

  constructor

  · exact geometric_series_converges_iff
      x

  constructor

  · intro hx
    exact geometric_series_hasSum
      x
      hx

  · intro hx
    exact geometric_series_absolutelyConverges
      x
      hx

theorem exercise_7_3_2
    (x : ℝ) :
    (
      SeriesConverges
          (fun n => x ^ n)
        ↔
      abs x < 1
    )
    ∧
    (
      abs x < 1 →
      SeriesHasSum
        (fun n => x ^ n)
        (1 / (1 - x))
    )
    ∧
    (
      abs x < 1 →
      AbsolutelyConverges
        (fun n => x ^ n)
    ) := by

  exact lemma_7_3_3 x

end TaoExercise7_3_2
