import Mathlib

namespace TaoExercise7_2_4

def partialSum
    (a : ℕ → ℝ)
    (m N : ℕ) : ℝ :=
  (Finset.Ico m N).sum a

def tailOpenSum
    (a : ℕ → ℝ)
    (p q : ℕ) : ℝ :=
  (Finset.Ico p q).sum a

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
  ∃ L : ℝ,
    SeriesHasSum a m L

def AbsolutelyConverges
    (a : ℕ → ℝ)
    (m : ℕ) : Prop :=
  SeriesConverges
    (fun n => abs (a n))
    m

theorem ico_union_ico
    {m p q : ℕ}
    (hmp : m ≤ p)
    (hpq : p ≤ q) :
    Finset.Ico m p ∪ Finset.Ico p q
      =
    Finset.Ico m q := by
  ext i
  simp only [
    Finset.mem_union,
    Finset.mem_Ico
  ]
  constructor
  · intro hi
    rcases hi with hi | hi
    · exact ⟨hi.1, lt_of_lt_of_le hi.2 hpq⟩
    · exact ⟨le_trans hmp hi.1, hi.2⟩
  · intro hi
    by_cases hip : i < p
    · left
      exact ⟨hi.1, hip⟩
    · right
      exact ⟨by omega, hi.2⟩

theorem ico_ico_disjoint
    (m p q : ℕ) :
    Disjoint
      (Finset.Ico m p)
      (Finset.Ico p q) := by
  apply Finset.disjoint_left.mpr
  intro i hi₁ hi₂
  have hi₁' :
      m ≤ i ∧ i < p :=
    Finset.mem_Ico.mp hi₁
  have hi₂' :
      p ≤ i ∧ i < q :=
    Finset.mem_Ico.mp hi₂
  omega

theorem tailOpenSum_eq_partialSum_sub
    (a : ℕ → ℝ)
    {m p q : ℕ}
    (hmp : m ≤ p)
    (hpq : p ≤ q) :
    tailOpenSum a p q
      =
    partialSum a m q
      -
    partialSum a m p := by
  unfold tailOpenSum partialSum

  have hdis :
      Disjoint
        (Finset.Ico m p)
        (Finset.Ico p q) := by
    exact ico_ico_disjoint m p q

  have hunion :
      Finset.Ico m p ∪ Finset.Ico p q
        =
      Finset.Ico m q := by
    exact ico_union_ico hmp hpq

  have hsum :
      (Finset.Ico m p).sum a
        +
      (Finset.Ico p q).sum a
        =
      (Finset.Ico m q).sum a := by
    calc
      (Finset.Ico m p).sum a
          +
        (Finset.Ico p q).sum a
          =
        (Finset.Ico m p ∪ Finset.Ico p q).sum a := by
            symm
            exact Finset.sum_union hdis
      _ =
        (Finset.Ico m q).sum a := by
          rw [hunion]

  linarith

theorem abs_finset_sum_le
    {α : Type*}
    [DecidableEq α]
    (s : Finset α)
    (f : α → ℝ) :
    abs (s.sum f)
      ≤
    s.sum (fun x => abs (f x)) := by
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert x s hx ih =>
      simp only [Finset.sum_insert hx]
      calc
        abs (f x + s.sum f)
            ≤ abs (f x) + abs (s.sum f) := by
              exact abs_add_le _ _
        _ ≤
            abs (f x)
              + s.sum (fun y => abs (f y)) := by
              exact add_le_add_right ih (abs (f x))

theorem abs_tailOpenSum_le
    (a : ℕ → ℝ)
    (p q : ℕ) :
    abs (tailOpenSum a p q)
      ≤
    tailOpenSum
      (fun n => abs (a n))
      p q := by
  unfold tailOpenSum
  exact abs_finset_sum_le
    (Finset.Ico p q)
    a

theorem abs_partialSum_le
    (a : ℕ → ℝ)
    (m N : ℕ) :
    abs (partialSum a m N)
      ≤
    partialSum
      (fun n => abs (a n))
      m N := by
  unfold partialSum
  exact abs_finset_sum_le
    (Finset.Ico m N)
    a

theorem tailOpenSum_abs_nonneg
    (a : ℕ → ℝ)
    (p q : ℕ) :
    0 ≤
      tailOpenSum
        (fun n => abs (a n))
        p q := by
  unfold tailOpenSum
  apply Finset.sum_nonneg
  intro i hi
  exact abs_nonneg (a i)

theorem cauchySeq_of_abs_hasSum
    (a : ℕ → ℝ)
    (m : ℕ)
    (B : ℝ)
    (habs :
      SeriesHasSum
        (fun n => abs (a n))
        m
        B) :
    CauchySeq (partialSum a m) := by

  have hcauchyAbs :
      CauchySeq
        (partialSum
          (fun n => abs (a n))
          m) := by
    exact habs.cauchySeq

  rw [Metric.cauchySeq_iff] at hcauchyAbs
  rw [Metric.cauchySeq_iff]

  intro ε hε

  obtain ⟨N₀, hN₀⟩ :=
    hcauchyAbs ε hε

  let N : ℕ := max m N₀

  refine ⟨N, ?_⟩

  intro r hr s hs

  have hmN :
      m ≤ N := by
    exact le_max_left m N₀

  have hN₀N :
      N₀ ≤ N := by
    exact le_max_right m N₀

  have hmr :
      m ≤ r := by
    exact le_trans hmN hr

  have hms :
      m ≤ s := by
    exact le_trans hmN hs

  have hN₀r :
      N₀ ≤ r := by
    exact le_trans hN₀N hr

  have hN₀s :
      N₀ ≤ s := by
    exact le_trans hN₀N hs

  by_cases hrs : r = s

  · subst s
    simpa using hε

  · by_cases hrsle : r ≤ s

    · have htail :
          tailOpenSum a r s
            =
          partialSum a m s
            -
          partialSum a m r := by
        exact tailOpenSum_eq_partialSum_sub
          a
          hmr
          hrsle

      have htailAbs :
          tailOpenSum
              (fun n => abs (a n))
              r s
            =
          partialSum
              (fun n => abs (a n))
              m s
            -
          partialSum
              (fun n => abs (a n))
              m r := by
        exact tailOpenSum_eq_partialSum_sub
          (fun n => abs (a n))
          hmr
          hrsle

      have hdistAbs :
          dist
            (partialSum
              (fun n => abs (a n))
              m s)
            (partialSum
              (fun n => abs (a n))
              m r)
            < ε := by
        exact hN₀
          s
          hN₀s
          r
          hN₀r

      have hAbsDifference :
          abs
            (
              partialSum
                  (fun n => abs (a n))
                  m s
                -
              partialSum
                  (fun n => abs (a n))
                  m r
            )
            < ε := by
        simpa [Real.dist_eq] using hdistAbs

      have hTailAbsNonneg :
          0 ≤
            tailOpenSum
              (fun n => abs (a n))
              r s := by
        exact tailOpenSum_abs_nonneg
          a
          r
          s

      have hDiffNonneg :
          0 ≤
            partialSum
                (fun n => abs (a n))
                m s
              -
            partialSum
                (fun n => abs (a n))
                m r := by
        rw [← htailAbs]
        exact hTailAbsNonneg

      have hAbsTailLt :
          tailOpenSum
              (fun n => abs (a n))
              r s
            < ε := by

        have hDiffLt :
            partialSum
                (fun n => abs (a n))
                m s
              -
            partialSum
                (fun n => abs (a n))
                m r
              < ε := by
          rw [abs_of_nonneg hDiffNonneg] at hAbsDifference
          exact hAbsDifference

        rw [htailAbs]
        exact hDiffLt

      have hTriangle :
          abs (tailOpenSum a r s)
            ≤
          tailOpenSum
            (fun n => abs (a n))
            r s := by
        exact abs_tailOpenSum_le
          a
          r
          s

      rw [Real.dist_eq]

      calc
        abs
          (partialSum a m r
            - partialSum a m s)
            =
        abs
          (partialSum a m s
            - partialSum a m r) := by
          exact abs_sub_comm
            (partialSum a m r)
            (partialSum a m s)

        _ =
          abs (tailOpenSum a r s) := by
          rw [htail]

        _ ≤
          tailOpenSum
            (fun n => abs (a n))
            r s := hTriangle

        _ < ε := hAbsTailLt

    · have hsr :
          s < r := by
        omega

      have hsrle :
          s ≤ r := by
        exact le_of_lt hsr

      have htail :
          tailOpenSum a s r
            =
          partialSum a m r
            -
          partialSum a m s := by
        exact tailOpenSum_eq_partialSum_sub
          a
          hms
          hsrle

      have htailAbs :
          tailOpenSum
              (fun n => abs (a n))
              s r
            =
          partialSum
              (fun n => abs (a n))
              m r
            -
          partialSum
              (fun n => abs (a n))
              m s := by
        exact tailOpenSum_eq_partialSum_sub
          (fun n => abs (a n))
          hms
          hsrle

      have hdistAbs :
          dist
            (partialSum
              (fun n => abs (a n))
              m r)
            (partialSum
              (fun n => abs (a n))
              m s)
            < ε := by
        exact hN₀
          r
          hN₀r
          s
          hN₀s

      have hAbsDifference :
          abs
            (
              partialSum
                  (fun n => abs (a n))
                  m r
                -
              partialSum
                  (fun n => abs (a n))
                  m s
            )
            < ε := by
        simpa [Real.dist_eq] using hdistAbs

      have hTailAbsNonneg :
          0 ≤
            tailOpenSum
              (fun n => abs (a n))
              s r := by
        exact tailOpenSum_abs_nonneg
          a
          s
          r

      have hDiffNonneg :
          0 ≤
            partialSum
                (fun n => abs (a n))
                m r
              -
            partialSum
                (fun n => abs (a n))
                m s := by
        rw [← htailAbs]
        exact hTailAbsNonneg

      have hAbsTailLt :
          tailOpenSum
              (fun n => abs (a n))
              s r
            < ε := by

        have hDiffLt :
            partialSum
                (fun n => abs (a n))
                m r
              -
            partialSum
                (fun n => abs (a n))
                m s
              < ε := by
          rw [abs_of_nonneg hDiffNonneg] at hAbsDifference
          exact hAbsDifference

        rw [htailAbs]
        exact hDiffLt

      have hTriangle :
          abs (tailOpenSum a s r)
            ≤
          tailOpenSum
            (fun n => abs (a n))
            s r := by
        exact abs_tailOpenSum_le
          a
          s
          r

      rw [Real.dist_eq]

      calc
        abs
          (partialSum a m r
            - partialSum a m s)
            =
        abs (tailOpenSum a s r) := by
          rw [htail]

        _ ≤
          tailOpenSum
            (fun n => abs (a n))
            s r := hTriangle

        _ < ε := hAbsTailLt

theorem converges_of_absolutelyConverges
    (a : ℕ → ℝ)
    (m : ℕ)
    (habs : AbsolutelyConverges a m) :
    SeriesConverges a m := by

  rcases habs with ⟨B, hB⟩

  have hcauchy :
      CauchySeq (partialSum a m) := by
    exact cauchySeq_of_abs_hasSum
      a
      m
      B
      hB

  obtain ⟨A, hA⟩ :=
    cauchySeq_tendsto_of_complete hcauchy

  exact ⟨A, hA⟩

theorem abs_limit_le_abs_series_limit
    (a : ℕ → ℝ)
    (m : ℕ)
    (A B : ℝ)
    (hA : SeriesHasSum a m A)
    (hB :
      SeriesHasSum
        (fun n => abs (a n))
        m
        B) :
    abs A ≤ B := by

  by_contra hNot

  have hBA :
      B < abs A := by
    exact lt_of_not_ge hNot

  let ε : ℝ :=
    (abs A - B) / 3

  have hε :
      0 < ε := by
    dsimp [ε]
    linarith

  have hAmetric :
      ∀ δ : ℝ, 0 < δ →
        ∃ N : ℕ,
          ∀ n : ℕ,
            N ≤ n →
            dist (partialSum a m n) A < δ := by
    exact Metric.tendsto_atTop.mp hA

  have hBmetric :
      ∀ δ : ℝ, 0 < δ →
        ∃ N : ℕ,
          ∀ n : ℕ,
            N ≤ n →
            dist
              (partialSum
                (fun k => abs (a k))
                m n)
              B
              < δ := by
    exact Metric.tendsto_atTop.mp hB

  obtain ⟨N₁, hN₁⟩ :=
    hAmetric ε hε

  obtain ⟨N₂, hN₂⟩ :=
    hBmetric ε hε

  let N : ℕ := max N₁ N₂

  have hN₁N :
      N₁ ≤ N := by
    exact le_max_left N₁ N₂

  have hN₂N :
      N₂ ≤ N := by
    exact le_max_right N₁ N₂

  have hAcloseDist :
      dist
        (partialSum a m N)
        A
        < ε := by
    exact hN₁ N hN₁N

  have hBcloseDist :
      dist
        (partialSum
          (fun k => abs (a k))
          m N)
        B
        < ε := by
    exact hN₂ N hN₂N

  have hAclose :
      abs
        (partialSum a m N - A)
        < ε := by
    simpa [Real.dist_eq] using hAcloseDist

  have hBclose :
      abs
        (
          partialSum
              (fun k => abs (a k))
              m N
            -
          B
        )
        < ε := by
    simpa [Real.dist_eq] using hBcloseDist

  have hFinite :
      abs (partialSum a m N)
        ≤
      partialSum
        (fun k => abs (a k))
        m N := by
    exact abs_partialSum_le
      a
      m
      N

  have hAcloseReverse :
      abs
        (A - partialSum a m N)
        < ε := by
    simpa [abs_sub_comm] using hAclose

  have hTriangle :
      abs A
        ≤
      abs (A - partialSum a m N)
        +
      abs (partialSum a m N) := by
    calc
      abs A
          =
      abs
        (
          (A - partialSum a m N)
            +
          partialSum a m N
        ) := by
          congr 1
          ring

      _ ≤
        abs (A - partialSum a m N)
          +
        abs (partialSum a m N) := by
          exact abs_add_le _ _

  have hA_lt :
      abs A
        <
      ε + abs (partialSum a m N) := by
    exact lt_of_le_of_lt
      hTriangle
      (add_lt_add_left
        hAcloseReverse
        (abs (partialSum a m N)))

  have hA_lt_T :
      abs A
        <
      ε
        +
      partialSum
        (fun k => abs (a k))
        m N := by
    exact lt_of_lt_of_le
      hA_lt
      (add_le_add_right hFinite ε)

  have hBbounds :=
    abs_lt.mp hBclose

  have hT_lt :
      partialSum
          (fun k => abs (a k))
          m N
        <
      B + ε := by
    linarith [hBbounds.2]

  have hA_lt_B :
      abs A
        <
      B + 2 * ε := by
    linarith [hA_lt_T, hT_lt]

  dsimp [ε] at hA_lt_B

  linarith

theorem proposition_7_2_9
    (a : ℕ → ℝ)
    (m : ℕ)
    (habs : AbsolutelyConverges a m) :
    ∃ A B : ℝ,
      SeriesHasSum a m A
      ∧
      SeriesHasSum
        (fun n => abs (a n))
        m
        B
      ∧
      abs A ≤ B := by

  rcases habs with ⟨B, hB⟩

  have hcauchy :
      CauchySeq (partialSum a m) := by
    exact cauchySeq_of_abs_hasSum
      a
      m
      B
      hB

  obtain ⟨A, hA⟩ :=
    cauchySeq_tendsto_of_complete hcauchy

  have hineq :
      abs A ≤ B := by
    exact abs_limit_le_abs_series_limit
      a
      m
      A
      B
      hA
      hB

  exact ⟨A, B, hA, hB, hineq⟩

theorem exercise_7_2_4
    (a : ℕ → ℝ)
    (m : ℕ)
    (habs : AbsolutelyConverges a m) :
    SeriesConverges a m
      ∧
    ∃ A B : ℝ,
      SeriesHasSum a m A
      ∧
      SeriesHasSum
        (fun n => abs (a n))
        m
        B
      ∧
      abs A ≤ B := by

  have hprop :=
    proposition_7_2_9
      a
      m
      habs

  rcases hprop with
    ⟨A, B, hA, hB, hineq⟩

  constructor

  · exact ⟨A, hA⟩

  · exact ⟨A, B, hA, hB, hineq⟩

end TaoExercise7_2_4
