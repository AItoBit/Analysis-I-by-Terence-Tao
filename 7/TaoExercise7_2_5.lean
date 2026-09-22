import Mathlib

namespace TaoExercise7_2_5

/-!
============================================================
Definitions
============================================================
-/

def partialSum
    (a : ℕ → ℝ)
    (m N : ℕ) : ℝ :=
  (Finset.Ico m N).sum a


def SeriesHasSum
    (a : ℕ → ℝ)
    (m : ℕ)
    (L : ℝ) : Prop :=
  Filter.Tendsto
    (partialSum a m)
    Filter.atTop
    (nhds L)


def SeriesConverges
    (a : ℕ → ℝ)
    (m : ℕ) : Prop :=
  ∃ L : ℝ, SeriesHasSum a m L


/-!
============================================================
Finite sum: addition
============================================================
-/

theorem partialSum_add
    (a b : ℕ → ℝ)
    (m N : ℕ) :
    partialSum
        (fun n => a n + b n)
        m N
      =
    partialSum a m N
      +
    partialSum b m N := by

  unfold partialSum

  let s : Finset ℕ := Finset.Ico m N

  change
    s.sum (fun n => a n + b n)
      =
    s.sum a + s.sum b

  induction s using Finset.induction_on with

  | empty =>
      simp

  | @insert x s hx ih =>
      simp [hx, ih, add_left_comm, add_comm]


/-!
============================================================
Finite sum: scalar multiplication
============================================================
-/

theorem partialSum_const_mul
    (a : ℕ → ℝ)
    (c : ℝ)
    (m N : ℕ) :
    partialSum
        (fun n => c * a n)
        m N
      =
    c * partialSum a m N := by

  unfold partialSum

  let s : Finset ℕ := Finset.Ico m N

  change
    s.sum (fun n => c * a n)
      =
    c * s.sum a

  induction s using Finset.induction_on with

  | empty =>
      simp

  | @insert x s hx ih =>
      simp [hx, ih, mul_add]


/-!
============================================================
Interval decomposition
============================================================
-/

theorem ico_union_ico
    {m p N : ℕ}
    (hmp : m ≤ p)
    (hpN : p ≤ N) :
    Finset.Ico m p ∪ Finset.Ico p N
      =
    Finset.Ico m N := by

  ext i

  simp only [
    Finset.mem_union,
    Finset.mem_Ico
  ]

  constructor

  · intro hi

    rcases hi with hi | hi

    · exact
        ⟨hi.1, lt_of_lt_of_le hi.2 hpN⟩

    · exact
        ⟨le_trans hmp hi.1, hi.2⟩

  · intro hi

    by_cases hip : i < p

    · left
      exact ⟨hi.1, hip⟩

    · right
      exact ⟨by omega, hi.2⟩


theorem ico_ico_disjoint
    (m p N : ℕ) :
    Disjoint
      (Finset.Ico m p)
      (Finset.Ico p N) := by

  apply Finset.disjoint_left.mpr

  intro i hi₁ hi₂

  have hi₁' :
      m ≤ i ∧ i < p :=
    Finset.mem_Ico.mp hi₁

  have hi₂' :
      p ≤ i ∧ i < N :=
    Finset.mem_Ico.mp hi₂

  omega


/-!
============================================================
Split a partial sum
============================================================
-/

theorem partialSum_split
    (a : ℕ → ℝ)
    {m p N : ℕ}
    (hmp : m ≤ p)
    (hpN : p ≤ N) :
    partialSum a m N
      =
    partialSum a m p
      +
    partialSum a p N := by

  unfold partialSum

  have hdis :
      Disjoint
        (Finset.Ico m p)
        (Finset.Ico p N) := by
    exact ico_ico_disjoint m p N

  have hunion :
      Finset.Ico m p ∪ Finset.Ico p N
        =
      Finset.Ico m N := by
    exact ico_union_ico hmp hpN

  calc
    (Finset.Ico m N).sum a
        =
      (Finset.Ico m p ∪
        Finset.Ico p N).sum a := by
          rw [hunion]

    _ =
      (Finset.Ico m p).sum a
        +
      (Finset.Ico p N).sum a := by
          exact Finset.sum_union hdis


/-!
============================================================
(a)

Sum of two convergent series
============================================================
-/

theorem seriesHasSum_add
    (a b : ℕ → ℝ)
    (m : ℕ)
    (A B : ℝ)
    (ha : SeriesHasSum a m A)
    (hb : SeriesHasSum b m B) :
    SeriesHasSum
      (fun n => a n + b n)
      m
      (A + B) := by

  have hadd :
      Filter.Tendsto
        (fun N =>
          partialSum a m N
            +
          partialSum b m N)
        Filter.atTop
        (nhds (A + B)) := by
    exact ha.add hb

  have hEq :
      partialSum
        (fun n => a n + b n)
        m
      =
      (fun N =>
        partialSum a m N
          +
        partialSum b m N) := by

    funext N

    exact partialSum_add
      a b m N

  unfold SeriesHasSum

  rw [hEq]

  exact hadd


theorem seriesConverges_add
    (a b : ℕ → ℝ)
    (m : ℕ)
    (ha : SeriesConverges a m)
    (hb : SeriesConverges b m) :
    SeriesConverges
      (fun n => a n + b n)
      m := by

  rcases ha with ⟨A, hA⟩
  rcases hb with ⟨B, hB⟩

  exact
    ⟨A + B,
      seriesHasSum_add
        a b m A B hA hB⟩


/-!
============================================================
(b)

Scalar multiplication
============================================================
-/

theorem seriesHasSum_const_mul
    (a : ℕ → ℝ)
    (m : ℕ)
    (A c : ℝ)
    (ha : SeriesHasSum a m A) :
    SeriesHasSum
      (fun n => c * a n)
      m
      (c * A) := by

  have hc :
      Filter.Tendsto
        (fun _ : ℕ => c)
        Filter.atTop
        (nhds c) := by
    exact tendsto_const_nhds

  have hmul :
      Filter.Tendsto
        (fun N =>
          c * partialSum a m N)
        Filter.atTop
        (nhds (c * A)) := by
    exact hc.mul ha

  have hEq :
      partialSum
        (fun n => c * a n)
        m
      =
      (fun N =>
        c * partialSum a m N) := by

    funext N

    exact partialSum_const_mul
      a c m N

  unfold SeriesHasSum

  rw [hEq]

  exact hmul


theorem seriesConverges_const_mul
    (a : ℕ → ℝ)
    (m : ℕ)
    (c : ℝ)
    (ha : SeriesConverges a m) :
    SeriesConverges
      (fun n => c * a n)
      m := by

  rcases ha with ⟨A, hA⟩

  exact
    ⟨c * A,
      seriesHasSum_const_mul
        a m A c hA⟩


/-!
============================================================
(c)

Removing finitely many initial terms
============================================================
-/

theorem seriesHasSum_drop_forward
    (a : ℕ → ℝ)
    (m k : ℕ)
    (L : ℝ)
    (h : SeriesHasSum a m L) :
    SeriesHasSum
      a
      (m + k)
      (L - partialSum a m (m + k)) := by

  apply Metric.tendsto_atTop.mpr

  intro ε hε

  have hmetric :
      ∀ δ : ℝ, 0 < δ →
        ∃ M : ℕ,
          ∀ N : ℕ,
            M ≤ N →
            dist
              (partialSum a m N)
              L
              < δ := by
    exact Metric.tendsto_atTop.mp h

  obtain ⟨M, hM⟩ :=
    hmetric ε hε

  let M' : ℕ :=
    max M (m + k)

  refine ⟨M', ?_⟩

  intro N hM'N

  have hMN :
      M ≤ N := by
    exact le_trans
      (le_max_left M (m + k))
      hM'N

  have hmkN :
      m + k ≤ N := by
    exact le_trans
      (le_max_right M (m + k))
      hM'N

  have hsplit :
      partialSum a m N
        =
      partialSum a m (m + k)
        +
      partialSum a (m + k) N := by

    exact partialSum_split
      a
      (Nat.le_add_right m k)
      hmkN

  have horig :
      dist
        (partialSum a m N)
        L
        < ε := by
    exact hM N hMN

  rw [Real.dist_eq] at horig ⊢

  have heq :
      partialSum a (m + k) N
          -
        (L - partialSum a m (m + k))
        =
      partialSum a m N - L := by

    rw [hsplit]

    ring

  rw [heq]

  exact horig


theorem seriesHasSum_drop_backward
    (a : ℕ → ℝ)
    (m k : ℕ)
    (L : ℝ)
    (h :
      SeriesHasSum
        a
        (m + k)
        (L - partialSum a m (m + k))) :
    SeriesHasSum a m L := by

  apply Metric.tendsto_atTop.mpr

  intro ε hε

  have hmetric :
      ∀ δ : ℝ, 0 < δ →
        ∃ M : ℕ,
          ∀ N : ℕ,
            M ≤ N →
            dist
              (partialSum a (m + k) N)
              (L - partialSum a m (m + k))
              < δ := by
    exact Metric.tendsto_atTop.mp h

  obtain ⟨M, hM⟩ :=
    hmetric ε hε

  let M' : ℕ :=
    max M (m + k)

  refine ⟨M', ?_⟩

  intro N hM'N

  have hMN :
      M ≤ N := by
    exact le_trans
      (le_max_left M (m + k))
      hM'N

  have hmkN :
      m + k ≤ N := by
    exact le_trans
      (le_max_right M (m + k))
      hM'N

  have hsplit :
      partialSum a m N
        =
      partialSum a m (m + k)
        +
      partialSum a (m + k) N := by

    exact partialSum_split
      a
      (Nat.le_add_right m k)
      hmkN

  have htail :
      dist
        (partialSum a (m + k) N)
        (L - partialSum a m (m + k))
        < ε := by
    exact hM N hMN

  rw [Real.dist_eq] at htail ⊢

  have heq :
      partialSum a m N - L
        =
      partialSum a (m + k) N
        -
      (L - partialSum a m (m + k)) := by

    rw [hsplit]

    ring

  rw [heq]

  exact htail


theorem seriesHasSum_drop_iff
    (a : ℕ → ℝ)
    (m k : ℕ)
    (L : ℝ) :
    SeriesHasSum a m L
      ↔
    SeriesHasSum
      a
      (m + k)
      (L - partialSum a m (m + k)) := by

  constructor

  · intro h
    exact seriesHasSum_drop_forward
      a m k L h

  · intro h
    exact seriesHasSum_drop_backward
      a m k L h


theorem seriesConverges_drop_iff
    (a : ℕ → ℝ)
    (m k : ℕ) :
    SeriesConverges a m
      ↔
    SeriesConverges a (m + k) := by

  constructor

  · rintro ⟨L, hL⟩

    exact
      ⟨L - partialSum a m (m + k),
        seriesHasSum_drop_forward
          a m k L hL⟩

  · rintro ⟨T, hT⟩

    let P : ℝ :=
      partialSum a m (m + k)

    have hTail :
        SeriesHasSum
          a
          (m + k)
          ((T + P) - P) := by
      simpa [P] using hT

    have hBack :
        SeriesHasSum
          a
          m
          (T + P) := by
      exact seriesHasSum_drop_backward
        a
        m
        k
        (T + P)
        hTail

    exact ⟨T + P, hBack⟩


/-!
============================================================
(d)

Translation of the indices
============================================================
-/

/--
Translation `i ↦ i+k` maps `[m,N)` onto
`[m+k,N+k)`.
-/
theorem image_Ico_add
    (m N k : ℕ) :
    (Finset.Ico m N).image
        (fun i : ℕ => i + k)
      =
    Finset.Ico (m + k) (N + k) := by

  ext j

  constructor

  · intro hj

    rcases Finset.mem_image.mp hj with
      ⟨i, hi, hij⟩

    have hiBounds :
        m ≤ i ∧ i < N :=
      Finset.mem_Ico.mp hi

    apply Finset.mem_Ico.mpr

    rw [← hij]

    constructor

    · exact Nat.add_le_add_right hiBounds.1 k

    · exact Nat.add_lt_add_right hiBounds.2 k

  · intro hj

    have hjBounds :
        m + k ≤ j ∧ j < N + k :=
      Finset.mem_Ico.mp hj

    have hkj :
        k ≤ j := by
      omega

    let i : ℕ := j - k

    have hiLower :
        m ≤ i := by
      dsimp [i]
      omega

    have hiUpper :
        i < N := by
      dsimp [i]
      omega

    have hi :
        i ∈ Finset.Ico m N := by
      exact Finset.mem_Ico.mpr
        ⟨hiLower, hiUpper⟩

    have hiShift :
        i + k = j := by
      dsimp [i]
      exact Nat.sub_add_cancel hkj

    apply Finset.mem_image.mpr

    exact ⟨i, hi, hiShift⟩


theorem add_k_injective
    (k : ℕ) :
    Function.Injective
      (fun i : ℕ => i + k) := by

  intro i j hij

  exact Nat.add_right_cancel hij


/--
Shifted finite partial sums are exactly equal.
-/
theorem partialSum_shift_add
    (a : ℕ → ℝ)
    (m N k : ℕ) :
    partialSum
        (fun j => a (j - k))
        (m + k)
        (N + k)
      =
    partialSum a m N := by

  unfold partialSum

  let shift : ℕ → ℕ :=
    fun i => i + k

  have hImage :
      (Finset.Ico m N).image shift
        =
      Finset.Ico (m + k) (N + k) := by

    exact image_Ico_add
      m N k

  have hInj :
      Set.InjOn
        shift
        (↑(Finset.Ico m N) : Set ℕ) := by

    intro x hx y hy hxy

    apply add_k_injective k

    exact hxy

  have hSumImage :
      ((Finset.Ico m N).image shift).sum
          (fun j => a (j - k))
        =
      (Finset.Ico m N).sum
          (fun i => a (shift i - k)) := by

    exact Finset.sum_image hInj

  calc
    (Finset.Ico (m + k) (N + k)).sum
        (fun j => a (j - k))
        =
    ((Finset.Ico m N).image shift).sum
        (fun j => a (j - k)) := by

      rw [hImage]

    _ =
    (Finset.Ico m N).sum
        (fun i => a (shift i - k)) := by

      exact hSumImage

    _ =
    (Finset.Ico m N).sum a := by

      apply Finset.sum_congr rfl

      intro i hi

      simp [shift]


/--
For sufficiently large N,

    shifted partial sum at N
      =
    original partial sum at N-k.
-/
theorem partialSum_shift
    (a : ℕ → ℝ)
    (m k N : ℕ)
    (hN : m + k ≤ N) :
    partialSum
        (fun j => a (j - k))
        (m + k)
        N
      =
    partialSum a m (N - k) := by

  have hkN :
      k ≤ N := by
    omega

  have hNk :
      (N - k) + k = N := by
    exact Nat.sub_add_cancel hkN

  have h :=
    partialSum_shift_add
      a
      m
      (N - k)
      k

  rw [hNk] at h

  exact h


theorem seriesHasSum_shift
    (a : ℕ → ℝ)
    (m k : ℕ)
    (L : ℝ)
    (h : SeriesHasSum a m L) :
    SeriesHasSum
      (fun n => a (n - k))
      (m + k)
      L := by

  apply Metric.tendsto_atTop.mpr

  intro ε hε

  have hmetric :
      ∀ δ : ℝ, 0 < δ →
        ∃ M : ℕ,
          ∀ N : ℕ,
            M ≤ N →
            dist
              (partialSum a m N)
              L
              < δ := by

    exact Metric.tendsto_atTop.mp h

  obtain ⟨M, hM⟩ :=
    hmetric ε hε

  let M' : ℕ :=
    max (M + k) (m + k)

  refine ⟨M', ?_⟩

  intro N hM'N

  have hmkN :
      m + k ≤ N := by

    exact le_trans
      (le_max_right (M + k) (m + k))
      hM'N

  have hMkN :
      M + k ≤ N := by

    exact le_trans
      (le_max_left (M + k) (m + k))
      hM'N

  have hMsub :
      M ≤ N - k := by
    omega

  have hOrig :
      dist
        (partialSum a m (N - k))
        L
        < ε := by

    exact hM
      (N - k)
      hMsub

  have hShift :
      partialSum
          (fun n => a (n - k))
          (m + k)
          N
        =
      partialSum a m (N - k) := by

    exact partialSum_shift
      a
      m
      k
      N
      hmkN

  rw [hShift]

  exact hOrig


/-!
============================================================
Proposition 7.2.14
============================================================
-/

theorem proposition_7_2_14_a
    (a b : ℕ → ℝ)
    (m : ℕ)
    (A B : ℝ)
    (ha : SeriesHasSum a m A)
    (hb : SeriesHasSum b m B) :
    SeriesHasSum
      (fun n => a n + b n)
      m
      (A + B) := by

  exact seriesHasSum_add
    a b m A B ha hb


theorem proposition_7_2_14_b
    (a : ℕ → ℝ)
    (m : ℕ)
    (A c : ℝ)
    (ha : SeriesHasSum a m A) :
    SeriesHasSum
      (fun n => c * a n)
      m
      (c * A) := by

  exact seriesHasSum_const_mul
    a m A c ha


theorem proposition_7_2_14_c
    (a : ℕ → ℝ)
    (m k : ℕ)
    (L : ℝ) :
    SeriesHasSum a m L
      ↔
    SeriesHasSum
      a
      (m + k)
      (L - partialSum a m (m + k)) := by

  exact seriesHasSum_drop_iff
    a m k L


theorem proposition_7_2_14_d
    (a : ℕ → ℝ)
    (m k : ℕ)
    (L : ℝ)
    (ha : SeriesHasSum a m L) :
    SeriesHasSum
      (fun n => a (n - k))
      (m + k)
      L := by

  exact seriesHasSum_shift
    a m k L ha


/-!
============================================================
Exercise 7.2.5
============================================================
-/

theorem exercise_7_2_5
    (a b : ℕ → ℝ)
    (m k : ℕ)
    (A B c : ℝ)
    (ha : SeriesHasSum a m A)
    (hb : SeriesHasSum b m B) :
    SeriesHasSum
        (fun n => a n + b n)
        m
        (A + B)
    ∧
    SeriesHasSum
        (fun n => c * a n)
        m
        (c * A)
    ∧
    (
      SeriesHasSum a m A
        ↔
      SeriesHasSum
        a
        (m + k)
        (A - partialSum a m (m + k))
    )
    ∧
    SeriesHasSum
        (fun n => a (n - k))
        (m + k)
        A := by

  constructor

  · exact proposition_7_2_14_a
      a b m A B ha hb

  constructor

  · exact proposition_7_2_14_b
      a m A c ha

  constructor

  · exact proposition_7_2_14_c
      a m k A

  · exact proposition_7_2_14_d
      a m k A ha

end TaoExercise7_2_5
