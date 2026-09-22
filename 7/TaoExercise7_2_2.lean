import Mathlib

namespace TaoExercise7_2_2

/-!
============================================================
Partial sums
============================================================

We use the half-open convention

    S N = ∑_{m ≤ i < N} a_i.

Thus

    S m = 0

and, for p ≤ q,

    ∑_{i=p}^q a_i = S (q+1) - S p.
-/

def partialSum
    (a : ℕ → ℝ)
    (m N : ℕ) : ℝ :=
  (Finset.Ico m N).sum a


/--
The inclusive finite tail

    ∑_{i=p}^q a_i.
-/
def tailSum
    (a : ℕ → ℝ)
    (p q : ℕ) : ℝ :=
  (Finset.Icc p q).sum a


/-!
============================================================
Series convergence
============================================================
-/

/--
The series starting at `m` converges iff its
sequence of partial sums converges.
-/
def SeriesConverges
    (a : ℕ → ℝ)
    (m : ℕ) : Prop :=
  ∃ L : ℝ,
    Filter.Tendsto
      (partialSum a m)
      Filter.atTop
      (nhds L)


/-!
============================================================
Cauchy criterion for tails
============================================================

For every ε > 0, all sufficiently late finite
tails have absolute value at most ε.
-/

def TailCauchyCriterion
    (a : ℕ → ℝ)
    (m : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ,
      m ≤ N ∧
      ∀ p q : ℕ,
        N ≤ p →
        p ≤ q →
        |tailSum a p q| ≤ ε


/-!
============================================================
Interval decomposition

For m ≤ p ≤ q,

    [m,q+1) = [m,p) ∪ [p,q].
============================================================
-/

theorem ico_union_icc
    {m p q : ℕ}
    (hmp : m ≤ p)
    (hpq : p ≤ q) :
    Finset.Ico m p ∪ Finset.Icc p q
      =
    Finset.Ico m (q + 1) := by

  ext i

  simp only [
    Finset.mem_union,
    Finset.mem_Ico,
    Finset.mem_Icc
  ]

  constructor

  · intro hi

    rcases hi with hi | hi

    · constructor

      · exact hi.1

      · omega

    · constructor

      · exact le_trans hmp hi.1

      · omega

  · intro hi

    by_cases hip : i < p

    · left
      exact ⟨hi.1, hip⟩

    · right

      constructor

      · omega

      · omega


/-!
============================================================
The two pieces are disjoint
============================================================
-/

theorem ico_icc_disjoint
    (m p q : ℕ) :
    Disjoint
      (Finset.Ico m p)
      (Finset.Icc p q) := by

  apply Finset.disjoint_left.mpr

  intro i hi₁ hi₂

  have hi₁' :
      m ≤ i ∧ i < p :=
    Finset.mem_Ico.mp hi₁

  have hi₂' :
      p ≤ i ∧ i ≤ q :=
    Finset.mem_Icc.mp hi₂

  omega


/-!
============================================================
Tail = difference of partial sums
============================================================
-/

theorem tailSum_eq_partialSum_sub
    (a : ℕ → ℝ)
    {m p q : ℕ}
    (hmp : m ≤ p)
    (hpq : p ≤ q) :
    tailSum a p q
      =
    partialSum a m (q + 1)
      -
    partialSum a m p := by

  unfold tailSum partialSum

  have hdis :
      Disjoint
        (Finset.Ico m p)
        (Finset.Icc p q) := by

    exact ico_icc_disjoint m p q

  have hunion :
      Finset.Ico m p ∪ Finset.Icc p q
        =
      Finset.Ico m (q + 1) := by

    exact ico_union_icc hmp hpq

  have hsum :
      (Finset.Ico m p).sum a
        +
      (Finset.Icc p q).sum a
        =
      (Finset.Ico m (q + 1)).sum a := by

    calc
      (Finset.Ico m p).sum a
          +
        (Finset.Icc p q).sum a
          =
        (Finset.Ico m p ∪
          Finset.Icc p q).sum a := by

            symm
            exact Finset.sum_union hdis

      _ =
        (Finset.Ico m (q + 1)).sum a := by
          rw [hunion]

  linarith


/-!
============================================================
Convergence -> tail Cauchy criterion
============================================================
-/

theorem tailCauchy_of_seriesConverges
    (a : ℕ → ℝ)
    (m : ℕ)
    (hconv : SeriesConverges a m) :
    TailCauchyCriterion a m := by

  rcases hconv with ⟨L, hL⟩

  have hcauchy :
      CauchySeq (partialSum a m) := by

    exact hL.cauchySeq

  have hmetric :
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ,
          ∀ r : ℕ, N ≤ r →
          ∀ s : ℕ, N ≤ s →
            dist
              (partialSum a m r)
              (partialSum a m s)
              < ε := by

    exact Metric.cauchySeq_iff.mp hcauchy

  intro ε hε

  obtain ⟨N₀, hN₀⟩ :=
    hmetric ε hε

  let N : ℕ := max m N₀

  refine ⟨N, ?_, ?_⟩

  · exact le_max_left m N₀

  · intro p q hNp hpq

    have hmN :
        m ≤ N := by
      exact le_max_left m N₀

    have hN₀N :
        N₀ ≤ N := by
      exact le_max_right m N₀

    have hmp :
        m ≤ p := by
      exact le_trans hmN hNp

    have hN₀p :
        N₀ ≤ p := by
      exact le_trans hN₀N hNp

    have hN₀q :
        N₀ ≤ q := by
      exact le_trans hN₀p hpq

    have hN₀q1 :
        N₀ ≤ q + 1 := by
      omega

    have hdist :
        dist
          (partialSum a m (q + 1))
          (partialSum a m p)
          < ε := by

      exact hN₀
        (q + 1)
        hN₀q1
        p
        hN₀p

    have htail :
        tailSum a p q
          =
        partialSum a m (q + 1)
          -
        partialSum a m p := by

      exact tailSum_eq_partialSum_sub
        a
        hmp
        hpq

    rw [htail]

    have habs :
        |partialSum a m (q + 1)
            - partialSum a m p|
          < ε := by

      simpa [Real.dist_eq] using hdist

    exact le_of_lt habs


/-!
============================================================
Tail Cauchy criterion -> Cauchy partial sums
============================================================
-/

theorem cauchySeq_partialSum_of_tailCauchy
    (a : ℕ → ℝ)
    (m : ℕ)
    (htail : TailCauchyCriterion a m) :
    CauchySeq (partialSum a m) := by

  rw [Metric.cauchySeq_iff]

  intro ε hε

  have hhalf :
      0 < ε / 2 := by
    linarith

  obtain ⟨N, hmN, hN⟩ :=
    htail (ε / 2) hhalf

  refine ⟨N, ?_⟩

  intro r hr
  intro s hs

  by_cases hrs : r = s

  · subst s
    simpa using hε

  · by_cases hrs_le : r ≤ s

    /-
    Case r < s.

    S_s - S_r is the tail from r to s-1.
    -/
    · have hrs_lt :
          r < s := by
        exact lt_of_le_of_ne hrs_le hrs

      have hrsPred :
          r ≤ s - 1 := by
        omega

      have hmr :
          m ≤ r := by
        exact le_trans hmN hr

      have hbound :
          |tailSum a r (s - 1)|
            ≤ ε / 2 := by

        exact hN
          r
          (s - 1)
          hr
          hrsPred

      have htailEq :
          tailSum a r (s - 1)
            =
          partialSum a m ((s - 1) + 1)
            -
          partialSum a m r := by

        exact tailSum_eq_partialSum_sub
          a
          hmr
          hrsPred

      have hsEq :
          (s - 1) + 1 = s := by
        omega

      rw [hsEq] at htailEq

      rw [Real.dist_eq]

      calc
        |partialSum a m r
            - partialSum a m s|
            =
        |partialSum a m s
            - partialSum a m r| := by

          exact abs_sub_comm
            (partialSum a m r)
            (partialSum a m s)

        _ =
          |tailSum a r (s - 1)| := by
          rw [htailEq]

        _ ≤ ε / 2 := hbound

        _ < ε := by
          linarith

    /-
    Case s < r.

    S_r - S_s is the tail from s to r-1.
    -/
    · have hsr :
          s < r := by
        omega

      have hsrPred :
          s ≤ r - 1 := by
        omega

      have hms :
          m ≤ s := by
        exact le_trans hmN hs

      have hbound :
          |tailSum a s (r - 1)|
            ≤ ε / 2 := by

        exact hN
          s
          (r - 1)
          hs
          hsrPred

      have htailEq :
          tailSum a s (r - 1)
            =
          partialSum a m ((r - 1) + 1)
            -
          partialSum a m s := by

        exact tailSum_eq_partialSum_sub
          a
          hms
          hsrPred

      have hrEq :
          (r - 1) + 1 = r := by
        omega

      rw [hrEq] at htailEq

      rw [Real.dist_eq]

      calc
        |partialSum a m r
            - partialSum a m s|
            =
        |tailSum a s (r - 1)| := by
          rw [htailEq]

        _ ≤ ε / 2 := hbound

        _ < ε := by
          linarith


/-!
============================================================
Tail Cauchy criterion -> convergence
============================================================
-/

theorem seriesConverges_of_tailCauchy
    (a : ℕ → ℝ)
    (m : ℕ)
    (htail : TailCauchyCriterion a m) :
    SeriesConverges a m := by

  have hcauchy :
      CauchySeq (partialSum a m) := by

    exact cauchySeq_partialSum_of_tailCauchy
      a
      m
      htail

  obtain ⟨L, hL⟩ :=
    cauchySeq_tendsto_of_complete hcauchy

  exact ⟨L, hL⟩


/-!
============================================================
Proposition 7.2.5
============================================================
-/

theorem proposition_7_2_5
    (a : ℕ → ℝ)
    (m : ℕ) :
    SeriesConverges a m
      ↔
    TailCauchyCriterion a m := by

  constructor

  · intro hconv

    exact tailCauchy_of_seriesConverges
      a
      m
      hconv

  · intro htail

    exact seriesConverges_of_tailCauchy
      a
      m
      htail


/-!
============================================================
Exercise 7.2.2
============================================================
-/

theorem exercise_7_2_2
    (a : ℕ → ℝ)
    (m : ℕ) :
    SeriesConverges a m
      ↔
    (
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ,
          m ≤ N ∧
          ∀ p q : ℕ,
            N ≤ p →
            p ≤ q →
            |tailSum a p q| ≤ ε
    ) := by

  exact proposition_7_2_5 a m

end TaoExercise7_2_2
