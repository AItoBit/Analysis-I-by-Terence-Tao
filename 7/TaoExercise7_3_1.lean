import Mathlib

namespace TaoExercise7_3_1

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

def AbsolutelyConverges
    (a : ℕ → ℝ)
    (m : ℕ) : Prop :=
  SeriesConverges
    (fun n => abs (a n))
    m


/-!
============================================================
Split an interval
============================================================
-/

theorem ico_union_ico
    {m p q : ℕ}
    (hmp : m ≤ p)
    (hpq : p ≤ q) :
    Finset.Ico m p ∪ Finset.Ico p q =
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


theorem partialSum_split
    (a : ℕ → ℝ)
    {m p q : ℕ}
    (hmp : m ≤ p)
    (hpq : p ≤ q) :
    partialSum a m q =
      partialSum a m p +
      partialSum a p q := by

  unfold partialSum

  have hdis :
      Disjoint
        (Finset.Ico m p)
        (Finset.Ico p q) := by
    exact ico_ico_disjoint m p q

  have hunion :
      Finset.Ico m p ∪ Finset.Ico p q =
        Finset.Ico m q := by
    exact ico_union_ico hmp hpq

  calc
    (Finset.Ico m q).sum a
        =
      (Finset.Ico m p ∪
        Finset.Ico p q).sum a := by
          rw [hunion]

    _ =
      (Finset.Ico m p).sum a +
      (Finset.Ico p q).sum a := by
          exact Finset.sum_union hdis


/-!
============================================================
Comparison of finite sums
============================================================
-/

theorem partialSum_le_partialSum
    (a b : ℕ → ℝ)
    (m N : ℕ)
    (hab :
      ∀ n : ℕ,
        m ≤ n →
        a n ≤ b n) :
    partialSum a m N ≤
      partialSum b m N := by

  unfold partialSum

  apply Finset.sum_le_sum

  intro i hi

  have hmi :
      m ≤ i :=
    (Finset.mem_Ico.mp hi).1

  exact hab i hmi


/-!
============================================================
Nonnegative partial sums
============================================================
-/

theorem partialSum_nonneg
    (a : ℕ → ℝ)
    (m N : ℕ)
    (ha :
      ∀ n : ℕ,
        m ≤ n →
        0 ≤ a n) :
    0 ≤ partialSum a m N := by

  unfold partialSum

  apply Finset.sum_nonneg

  intro i hi

  have hmi :
      m ≤ i :=
    (Finset.mem_Ico.mp hi).1

  exact ha i hmi


/-!
============================================================
Finite triangle inequality
============================================================
-/

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
            ≤
          abs (f x) + abs (s.sum f) := by
            exact abs_add_le _ _

        _ ≤
          abs (f x)
            +
          s.sum (fun y => abs (f y)) := by
            exact add_le_add_right
              ih
              (abs (f x))


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


/-!
============================================================
|a_n| ≤ b_n implies b_n ≥ 0
============================================================
-/

theorem majorant_nonneg
    (a b : ℕ → ℝ)
    (m : ℕ)
    (hab :
      ∀ n : ℕ,
        m ≤ n →
        abs (a n) ≤ b n) :
    ∀ n : ℕ,
      m ≤ n →
      0 ≤ b n := by

  intro n hmn

  exact le_trans
    (abs_nonneg (a n))
    (hab n hmn)


/-!
============================================================
Comparison: convergence of b implies convergence of |a|
============================================================
-/

theorem abs_partialSums_cauchy_of_majorant
    (a b : ℕ → ℝ)
    (m B : ℕ := 0) :
    True := by
  trivial


theorem cauchy_abs_of_comparison
    (a b : ℕ → ℝ)
    (m : ℕ)
    (B : ℝ)
    (hB : SeriesHasSum b m B)
    (hab :
      ∀ n : ℕ,
        m ≤ n →
        abs (a n) ≤ b n) :
    CauchySeq
      (partialSum
        (fun n => abs (a n))
        m) := by

  have hbNonneg :
      ∀ n : ℕ,
        m ≤ n →
        0 ≤ b n := by
    exact majorant_nonneg
      a b m hab

  have hcauchyB :
      CauchySeq (partialSum b m) := by
    exact hB.cauchySeq

  rw [Metric.cauchySeq_iff] at hcauchyB
  rw [Metric.cauchySeq_iff]

  intro ε hε

  obtain ⟨N₀, hN₀⟩ :=
    hcauchyB ε hε

  let N : ℕ := max m N₀

  refine ⟨N, ?_⟩

  intro p hp q hq

  have hmN :
      m ≤ N := by
    exact le_max_left m N₀

  have hN₀N :
      N₀ ≤ N := by
    exact le_max_right m N₀

  have hmp :
      m ≤ p := by
    exact le_trans hmN hp

  have hmq :
      m ≤ q := by
    exact le_trans hmN hq

  have hN₀p :
      N₀ ≤ p := by
    exact le_trans hN₀N hp

  have hN₀q :
      N₀ ≤ q := by
    exact le_trans hN₀N hq

  by_cases hpq : p ≤ q

  · have hAbsSplit :
        partialSum
            (fun n => abs (a n))
            m q
          =
        partialSum
            (fun n => abs (a n))
            m p
          +
        partialSum
            (fun n => abs (a n))
            p q := by

      exact partialSum_split
        (fun n => abs (a n))
        hmp
        hpq

    have hBSplit :
        partialSum b m q
          =
        partialSum b m p
          +
        partialSum b p q := by

      exact partialSum_split
        b
        hmp
        hpq

    have hBdist :
        dist
          (partialSum b m q)
          (partialSum b m p)
          < ε := by

      exact hN₀
        q hN₀q
        p hN₀p

    have hBTailNonneg :
        0 ≤ partialSum b p q := by

      apply partialSum_nonneg

      intro n hpn

      exact hbNonneg
        n
        (le_trans hmp hpn)

    have hBTailLt :
        partialSum b p q < ε := by

      rw [Real.dist_eq] at hBdist
      rw [hBSplit] at hBdist

      have heq :
          abs
            (
              partialSum b m p
                +
              partialSum b p q
                -
              partialSum b m p
            )
            =
          partialSum b p q := by

        ring_nf

        exact abs_of_nonneg hBTailNonneg

      rw [heq] at hBdist

      exact hBdist

    have hCompare :
        partialSum
            (fun n => abs (a n))
            p q
          ≤
        partialSum b p q := by

      exact partialSum_le_partialSum
        (fun n => abs (a n))
        b
        p
        q
        (by
          intro n hpn
          exact hab
            n
            (le_trans hmp hpn))

    have hAbsTailNonneg :
        0 ≤
          partialSum
            (fun n => abs (a n))
            p q := by

      apply partialSum_nonneg

      intro n hn

      exact abs_nonneg (a n)

    rw [Real.dist_eq]

    have heq :
        partialSum
            (fun n => abs (a n))
            m p
          -
        partialSum
            (fun n => abs (a n))
            m q
        =
        - partialSum
            (fun n => abs (a n))
            p q := by

      rw [hAbsSplit]

      ring

    rw [heq, abs_neg, abs_of_nonneg hAbsTailNonneg]

    exact lt_of_le_of_lt
      hCompare
      hBTailLt

  · have hqp :
        q ≤ p := by
      omega

    have hAbsSplit :
        partialSum
            (fun n => abs (a n))
            m p
          =
        partialSum
            (fun n => abs (a n))
            m q
          +
        partialSum
            (fun n => abs (a n))
            q p := by

      exact partialSum_split
        (fun n => abs (a n))
        hmq
        hqp

    have hBSplit :
        partialSum b m p
          =
        partialSum b m q
          +
        partialSum b q p := by

      exact partialSum_split
        b
        hmq
        hqp

    have hBdist :
        dist
          (partialSum b m p)
          (partialSum b m q)
          < ε := by

      exact hN₀
        p hN₀p
        q hN₀q

    have hBTailNonneg :
        0 ≤ partialSum b q p := by

      apply partialSum_nonneg

      intro n hqn

      exact hbNonneg
        n
        (le_trans hmq hqn)

    have hBTailLt :
        partialSum b q p < ε := by

      rw [Real.dist_eq] at hBdist
      rw [hBSplit] at hBdist

      have heq :
          abs
            (
              partialSum b m q
                +
              partialSum b q p
                -
              partialSum b m q
            )
            =
          partialSum b q p := by

        ring_nf

        exact abs_of_nonneg hBTailNonneg

      rw [heq] at hBdist

      exact hBdist

    have hCompare :
        partialSum
            (fun n => abs (a n))
            q p
          ≤
        partialSum b q p := by

      exact partialSum_le_partialSum
        (fun n => abs (a n))
        b
        q
        p
        (by
          intro n hqn
          exact hab
            n
            (le_trans hmq hqn))

    have hAbsTailNonneg :
        0 ≤
          partialSum
            (fun n => abs (a n))
            q p := by

      apply partialSum_nonneg

      intro n hn

      exact abs_nonneg (a n)

    rw [Real.dist_eq]

    have heq :
        partialSum
            (fun n => abs (a n))
            m p
          -
        partialSum
            (fun n => abs (a n))
            m q
        =
        partialSum
            (fun n => abs (a n))
            q p := by

      rw [hAbsSplit]

      ring

    rw [heq, abs_of_nonneg hAbsTailNonneg]

    exact lt_of_le_of_lt
      hCompare
      hBTailLt


/-!
============================================================
Absolute convergence gives ordinary convergence
============================================================
-/

theorem cauchy_original_of_abs_cauchy
    (a : ℕ → ℝ)
    (m : ℕ)
    (hAbs :
      CauchySeq
        (partialSum
          (fun n => abs (a n))
          m)) :
    CauchySeq (partialSum a m) := by

  rw [Metric.cauchySeq_iff] at hAbs
  rw [Metric.cauchySeq_iff]

  intro ε hε

  obtain ⟨N₀, hN₀⟩ :=
    hAbs ε hε

  let N : ℕ := max m N₀

  refine ⟨N, ?_⟩

  intro p hp q hq

  have hmN :
      m ≤ N := by
    exact le_max_left m N₀

  have hN₀N :
      N₀ ≤ N := by
    exact le_max_right m N₀

  have hmp :
      m ≤ p := by
    exact le_trans hmN hp

  have hmq :
      m ≤ q := by
    exact le_trans hmN hq

  have hN₀p :
      N₀ ≤ p := by
    exact le_trans hN₀N hp

  have hN₀q :
      N₀ ≤ q := by
    exact le_trans hN₀N hq

  by_cases hpq : p ≤ q

  · have hsplit :
        partialSum a m q
          =
        partialSum a m p +
        partialSum a p q := by

      exact partialSum_split
        a hmp hpq

    have hsplitAbs :
        partialSum
            (fun n => abs (a n))
            m q
          =
        partialSum
            (fun n => abs (a n))
            m p
          +
        partialSum
            (fun n => abs (a n))
            p q := by

      exact partialSum_split
        (fun n => abs (a n))
        hmp hpq

    have hdistAbs :
        dist
          (partialSum
            (fun n => abs (a n))
            m q)
          (partialSum
            (fun n => abs (a n))
            m p)
          < ε := by

      exact hN₀
        q hN₀q
        p hN₀p

    have hTailNonneg :
        0 ≤
          partialSum
            (fun n => abs (a n))
            p q := by

      apply partialSum_nonneg

      intro n hn

      exact abs_nonneg (a n)

    have hTailLt :
        partialSum
            (fun n => abs (a n))
            p q
          < ε := by

      rw [Real.dist_eq] at hdistAbs
      rw [hsplitAbs] at hdistAbs

      have heq :
          abs
            (
              partialSum
                  (fun n => abs (a n))
                  m p
                +
              partialSum
                  (fun n => abs (a n))
                  p q
                -
              partialSum
                  (fun n => abs (a n))
                  m p
            )
            =
          partialSum
            (fun n => abs (a n))
            p q := by

        ring_nf

        exact abs_of_nonneg hTailNonneg

      rw [heq] at hdistAbs

      exact hdistAbs

    have htriangle :
        abs (partialSum a p q)
          ≤
        partialSum
          (fun n => abs (a n))
          p q := by

      exact abs_partialSum_le
        a p q

    rw [Real.dist_eq]

    have heq :
        partialSum a m p
          -
        partialSum a m q
        =
        - partialSum a p q := by

      rw [hsplit]

      ring

    rw [heq, abs_neg]

    exact lt_of_le_of_lt
      htriangle
      hTailLt

  · have hqp :
        q ≤ p := by
      omega

    have hsplit :
        partialSum a m p
          =
        partialSum a m q +
        partialSum a q p := by

      exact partialSum_split
        a hmq hqp

    have hsplitAbs :
        partialSum
            (fun n => abs (a n))
            m p
          =
        partialSum
            (fun n => abs (a n))
            m q
          +
        partialSum
            (fun n => abs (a n))
            q p := by

      exact partialSum_split
        (fun n => abs (a n))
        hmq hqp

    have hdistAbs :
        dist
          (partialSum
            (fun n => abs (a n))
            m p)
          (partialSum
            (fun n => abs (a n))
            m q)
          < ε := by

      exact hN₀
        p hN₀p
        q hN₀q

    have hTailNonneg :
        0 ≤
          partialSum
            (fun n => abs (a n))
            q p := by

      apply partialSum_nonneg

      intro n hn

      exact abs_nonneg (a n)

    have hTailLt :
        partialSum
            (fun n => abs (a n))
            q p
          < ε := by

      rw [Real.dist_eq] at hdistAbs
      rw [hsplitAbs] at hdistAbs

      have heq :
          abs
            (
              partialSum
                  (fun n => abs (a n))
                  m q
                +
              partialSum
                  (fun n => abs (a n))
                  q p
                -
              partialSum
                  (fun n => abs (a n))
                  m q
            )
            =
          partialSum
            (fun n => abs (a n))
            q p := by

        ring_nf

        exact abs_of_nonneg hTailNonneg

      rw [heq] at hdistAbs

      exact hdistAbs

    have htriangle :
        abs (partialSum a q p)
          ≤
        partialSum
          (fun n => abs (a n))
          q p := by

      exact abs_partialSum_le
        a q p

    rw [Real.dist_eq]

    have heq :
        partialSum a m p
          -
        partialSum a m q
        =
        partialSum a q p := by

      rw [hsplit]

      ring

    rw [heq]

    exact lt_of_le_of_lt
      htriangle
      hTailLt


/-!
============================================================
Limit inequality |A| ≤ C
============================================================
-/

theorem abs_sum_le_abs_sum
    (a : ℕ → ℝ)
    (m : ℕ)
    (A C : ℝ)
    (hA : SeriesHasSum a m A)
    (hC :
      SeriesHasSum
        (fun n => abs (a n))
        m C) :
    abs A ≤ C := by

  by_contra hNot

  have hCA :
      C < abs A := by
    exact lt_of_not_ge hNot

  let ε : ℝ :=
    (abs A - C) / 3

  have hε :
      0 < ε := by
    dsimp [ε]
    linarith

  have hAmetric :=
    Metric.tendsto_atTop.mp hA

  have hCmetric :=
    Metric.tendsto_atTop.mp hC

  obtain ⟨N₁, hN₁⟩ :=
    hAmetric ε hε

  obtain ⟨N₂, hN₂⟩ :=
    hCmetric ε hε

  let N : ℕ := max N₁ N₂

  have hN₁N :
      N₁ ≤ N :=
    le_max_left N₁ N₂

  have hN₂N :
      N₂ ≤ N :=
    le_max_right N₁ N₂

  have hAcloseDist :=
    hN₁ N hN₁N

  have hCcloseDist :=
    hN₂ N hN₂N

  have hAclose :
      abs (partialSum a m N - A) < ε := by
    simpa [Real.dist_eq] using hAcloseDist

  have hCclose :
      abs
        (
          partialSum
              (fun n => abs (a n))
              m N
            - C
        )
        < ε := by
    simpa [Real.dist_eq] using hCcloseDist

  have hfinite :
      abs (partialSum a m N)
        ≤
      partialSum
        (fun n => abs (a n))
        m N := by
    exact abs_partialSum_le a m N

  have hAcloseReverse :
      abs (A - partialSum a m N) < ε := by
    simpa [abs_sub_comm] using hAclose

  have htriangle :
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
      abs A <
        ε + abs (partialSum a m N) := by

    exact lt_of_le_of_lt
      htriangle
      (add_lt_add_left
        hAcloseReverse
        (abs (partialSum a m N)))

  have hA_lt_Cpart :
      abs A <
        ε +
        partialSum
          (fun n => abs (a n))
          m N := by

    exact lt_of_lt_of_le
      hA_lt
      (add_le_add_right hfinite ε)

  have hCbounds :=
    abs_lt.mp hCclose

  have hPartial_lt :
      partialSum
          (fun n => abs (a n))
          m N
        <
      C + ε := by

    linarith [hCbounds.2]

  have hcontr :
      abs A < C + 2 * ε := by
    linarith [hA_lt_Cpart, hPartial_lt]

  dsimp [ε] at hcontr

  linarith


/-!
============================================================
Limit comparison C ≤ B
============================================================
-/

theorem abs_sum_le_majorant_sum
    (a b : ℕ → ℝ)
    (m : ℕ)
    (C B : ℝ)
    (hC :
      SeriesHasSum
        (fun n => abs (a n))
        m C)
    (hB : SeriesHasSum b m B)
    (hab :
      ∀ n : ℕ,
        m ≤ n →
        abs (a n) ≤ b n) :
    C ≤ B := by

  by_contra hNot

  have hBC :
      B < C := by
    exact lt_of_not_ge hNot

  let ε : ℝ :=
    (C - B) / 3

  have hε :
      0 < ε := by
    dsimp [ε]
    linarith

  have hCmetric :=
    Metric.tendsto_atTop.mp hC

  have hBmetric :=
    Metric.tendsto_atTop.mp hB

  obtain ⟨N₁, hN₁⟩ :=
    hCmetric ε hε

  obtain ⟨N₂, hN₂⟩ :=
    hBmetric ε hε

  let N : ℕ :=
    max m (max N₁ N₂)

  have hmN :
      m ≤ N := by
    exact le_max_left m (max N₁ N₂)

  have hN₁N :
      N₁ ≤ N := by
    exact le_trans
      (le_max_left N₁ N₂)
      (le_max_right m (max N₁ N₂))

  have hN₂N :
      N₂ ≤ N := by
    exact le_trans
      (le_max_right N₁ N₂)
      (le_max_right m (max N₁ N₂))

  have hCcloseDist :=
    hN₁ N hN₁N

  have hBcloseDist :=
    hN₂ N hN₂N

  have hCclose :
      abs
        (
          partialSum
              (fun n => abs (a n))
              m N
            -
          C
        )
        < ε := by
    simpa [Real.dist_eq] using hCcloseDist

  have hBclose :
      abs
        (
          partialSum b m N
            -
          B
        )
        < ε := by
    simpa [Real.dist_eq] using hBcloseDist

  have hcompare :
      partialSum
          (fun n => abs (a n))
          m N
        ≤
      partialSum b m N := by

    exact partialSum_le_partialSum
      (fun n => abs (a n))
      b
      m
      N
      hab

  have hCbounds :=
    abs_lt.mp hCclose

  have hBbounds :=
    abs_lt.mp hBclose

  have hC_lower :
      C - ε <
      partialSum
        (fun n => abs (a n))
        m N := by
    linarith [hCbounds.1]

  have hB_upper :
      partialSum b m N <
      B + ε := by
    linarith [hBbounds.2]

  have hCB :
      C - ε < B + ε := by

    exact lt_of_lt_of_le
      hC_lower
      (le_of_lt
        (lt_of_le_of_lt
          hcompare
          hB_upper))

  dsimp [ε] at hCB

  linarith


/-!
============================================================
Corollary 7.3.2
============================================================
-/

theorem corollary_7_3_2
    (a b : ℕ → ℝ)
    (m : ℕ)
    (hb : SeriesConverges b m)
    (hab :
      ∀ n : ℕ,
        m ≤ n →
        abs (a n) ≤ b n) :
    ∃ A C B : ℝ,
      SeriesHasSum a m A
      ∧
      SeriesHasSum
        (fun n => abs (a n))
        m C
      ∧
      SeriesHasSum b m B
      ∧
      abs A ≤ C
      ∧
      C ≤ B := by

  rcases hb with ⟨B, hB⟩

  have hcauchyAbs :
      CauchySeq
        (partialSum
          (fun n => abs (a n))
          m) := by

    exact cauchy_abs_of_comparison
      a b m B hB hab

  obtain ⟨C, hC⟩ :=
    cauchySeq_tendsto_of_complete
      hcauchyAbs

  have hcauchyA :
      CauchySeq
        (partialSum a m) := by

    exact cauchy_original_of_abs_cauchy
      a m hcauchyAbs

  obtain ⟨A, hA⟩ :=
    cauchySeq_tendsto_of_complete
      hcauchyA

  have hAC :
      abs A ≤ C := by

    exact abs_sum_le_abs_sum
      a m A C hA hC

  have hCB :
      C ≤ B := by

    exact abs_sum_le_majorant_sum
      a b m C B hC hB hab

  exact
    ⟨A, C, B,
      hA,
      hC,
      hB,
      hAC,
      hCB⟩


/-!
============================================================
Exercise 7.3.1
============================================================
-/

theorem exercise_7_3_1
    (a b : ℕ → ℝ)
    (m : ℕ)
    (hb : SeriesConverges b m)
    (hab :
      ∀ n : ℕ,
        m ≤ n →
        abs (a n) ≤ b n) :
    ∃ A C B : ℝ,
      SeriesHasSum a m A
      ∧
      SeriesHasSum
        (fun n => abs (a n))
        m C
      ∧
      SeriesHasSum b m B
      ∧
      abs A ≤ C
      ∧
      C ≤ B := by

  exact corollary_7_3_2
    a b m hb hab

end TaoExercise7_3_1
