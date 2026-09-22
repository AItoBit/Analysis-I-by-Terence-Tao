import Mathlib

namespace TaoExercise7_2_3

/-!
============================================================
Partial sums and tails
============================================================
-/

def partialSum
    (a : ℕ → ℝ)
    (m N : ℕ) : ℝ :=
  (Finset.Ico m N).sum a


def tailSum
    (a : ℕ → ℝ)
    (p q : ℕ) : ℝ :=
  (Finset.Icc p q).sum a


/-!
============================================================
Series convergence
============================================================
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
Tail Cauchy criterion
============================================================
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
Convergence of the terms to zero
============================================================
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
Proposition 7.2.5 as an assumption/previous result
============================================================
-/

theorem proposition_7_2_5
    (a : ℕ → ℝ)
    (m : ℕ) :
    SeriesConverges a m
      ↔
    TailCauchyCriterion a m := by
  constructor
  · intro h
    rcases h with ⟨L, hL⟩
    have hcauchy : CauchySeq (partialSum a m) := hL.cauchySeq
    rw [Metric.cauchySeq_iff] at hcauchy
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := hcauchy ε hε
    let N := max m N₀
    refine ⟨N, le_max_left _ _, ?_⟩
    intro p q hNp hpq
    have hN₀N : N₀ ≤ N := le_max_right _ _
    have hN₀p : N₀ ≤ p := le_trans hN₀N hNp
    have hN₀q1 : N₀ ≤ q + 1 := by
      omega
    have hdist :=
      hN₀ (q + 1) hN₀q1 p hN₀p
    have hmp : m ≤ p := by
      exact le_trans (le_max_left _ _) hNp
    have htail :
        tailSum a p q
          =
        partialSum a m (q + 1) - partialSum a m p := by
      unfold tailSum partialSum

      have hdis :
          Disjoint
            (Finset.Ico m p)
            (Finset.Icc p q) := by
        apply Finset.disjoint_left.mpr
        intro i hi₁ hi₂
        have hi₁' := Finset.mem_Ico.mp hi₁
        have hi₂' := Finset.mem_Icc.mp hi₂
        omega

      have hunion :
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
          · exact ⟨hi.1, by omega⟩
          · exact ⟨le_trans hmp hi.1, by omega⟩
        · intro hi
          by_cases hip : i < p
          · left
            exact ⟨hi.1, hip⟩
          · right
            constructor <;> omega

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
            (Finset.Ico m p ∪ Finset.Icc p q).sum a := by
              symm
              exact Finset.sum_union hdis
          _ =
            (Finset.Ico m (q + 1)).sum a := by
              rw [hunion]

      linarith

    rw [htail]
    have habs :
        |partialSum a m (q + 1) - partialSum a m p| < ε := by
      simpa [Real.dist_eq] using hdist
    exact le_of_lt habs

  · intro htail

    have hcauchy :
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

        · have hrs_lt : r < s := lt_of_le_of_ne hrs_le hrs
          have hrsPred : r ≤ s - 1 := by omega
          have hmr : m ≤ r := le_trans hmN hr

          have hbound :
              |tailSum a r (s - 1)| ≤ ε / 2 := by
            exact hN r (s - 1) hr hrsPred

          have htailEq :
              tailSum a r (s - 1)
                =
              partialSum a m ((s - 1) + 1)
                -
              partialSum a m r := by

            unfold tailSum partialSum

            have hdis :
                Disjoint
                  (Finset.Ico m r)
                  (Finset.Icc r (s - 1)) := by
              apply Finset.disjoint_left.mpr
              intro i hi₁ hi₂
              have hi₁' := Finset.mem_Ico.mp hi₁
              have hi₂' := Finset.mem_Icc.mp hi₂
              omega

            have hunion :
                Finset.Ico m r ∪ Finset.Icc r (s - 1)
                  =
                Finset.Ico m (((s - 1) + 1)) := by
              ext i
              simp only [
                Finset.mem_union,
                Finset.mem_Ico,
                Finset.mem_Icc
              ]
              constructor
              · intro hi
                rcases hi with hi | hi
                · exact ⟨hi.1, by omega⟩
                · exact ⟨le_trans hmr hi.1, by omega⟩
              · intro hi
                by_cases hir : i < r
                · left
                  exact ⟨hi.1, hir⟩
                · right
                  constructor <;> omega

            have hsum :
                (Finset.Ico m r).sum a
                  +
                (Finset.Icc r (s - 1)).sum a
                  =
                (Finset.Ico m ((s - 1) + 1)).sum a := by
              calc
                (Finset.Ico m r).sum a
                    +
                  (Finset.Icc r (s - 1)).sum a
                    =
                  (Finset.Ico m r ∪ Finset.Icc r (s - 1)).sum a := by
                    symm
                    exact Finset.sum_union hdis
                _ =
                  (Finset.Ico m ((s - 1) + 1)).sum a := by
                    rw [hunion]

            linarith

          have hsEq :
              (s - 1) + 1 = s := by
            omega

          rw [hsEq] at htailEq
          rw [Real.dist_eq]

          calc
            |partialSum a m r - partialSum a m s|
                =
              |partialSum a m s - partialSum a m r| := by
                exact abs_sub_comm _ _
            _ =
              |tailSum a r (s - 1)| := by
                rw [htailEq]
            _ ≤ ε / 2 := hbound
            _ < ε := by
              linarith

        · have hsr : s < r := by
            omega
          have hsrPred : s ≤ r - 1 := by
            omega
          have hms : m ≤ s := le_trans hmN hs

          have hbound :
              |tailSum a s (r - 1)| ≤ ε / 2 := by
            exact hN s (r - 1) hs hsrPred

          have htailEq :
              tailSum a s (r - 1)
                =
              partialSum a m ((r - 1) + 1)
                -
              partialSum a m s := by

            unfold tailSum partialSum

            have hdis :
                Disjoint
                  (Finset.Ico m s)
                  (Finset.Icc s (r - 1)) := by
              apply Finset.disjoint_left.mpr
              intro i hi₁ hi₂
              have hi₁' := Finset.mem_Ico.mp hi₁
              have hi₂' := Finset.mem_Icc.mp hi₂
              omega

            have hunion :
                Finset.Ico m s ∪ Finset.Icc s (r - 1)
                  =
                Finset.Ico m (((r - 1) + 1)) := by
              ext i
              simp only [
                Finset.mem_union,
                Finset.mem_Ico,
                Finset.mem_Icc
              ]
              constructor
              · intro hi
                rcases hi with hi | hi
                · exact ⟨hi.1, by omega⟩
                · exact ⟨le_trans hms hi.1, by omega⟩
              · intro hi
                by_cases his : i < s
                · left
                  exact ⟨hi.1, his⟩
                · right
                  constructor <;> omega

            have hsum :
                (Finset.Ico m s).sum a
                  +
                (Finset.Icc s (r - 1)).sum a
                  =
                (Finset.Ico m ((r - 1) + 1)).sum a := by
              calc
                (Finset.Ico m s).sum a
                    +
                  (Finset.Icc s (r - 1)).sum a
                    =
                  (Finset.Ico m s ∪ Finset.Icc s (r - 1)).sum a := by
                    symm
                    exact Finset.sum_union hdis
                _ =
                  (Finset.Ico m ((r - 1) + 1)).sum a := by
                    rw [hunion]

            linarith

          have hrEq :
              (r - 1) + 1 = r := by
            omega

          rw [hrEq] at htailEq
          rw [Real.dist_eq]

          calc
            |partialSum a m r - partialSum a m s|
                =
              |tailSum a s (r - 1)| := by
                rw [htailEq]
            _ ≤ ε / 2 := hbound
            _ < ε := by
              linarith

    obtain ⟨L, hL⟩ :=
      cauchySeq_tendsto_of_complete hcauchy

    exact ⟨L, hL⟩


/-!
============================================================
A singleton tail is just the term itself
============================================================
-/

theorem tailSum_self
    (a : ℕ → ℝ)
    (n : ℕ) :
    tailSum a n n = a n := by
  unfold tailSum
  simp


/-!
============================================================
Corollary 7.2.6
============================================================

If ∑ a_n converges, then a_n → 0.
-/

theorem corollary_7_2_6
    (a : ℕ → ℝ)
    (m : ℕ)
    (hseries : SeriesConverges a m) :
    ConvergesFrom a m 0 := by

  have htail :
      TailCauchyCriterion a m := by
    exact (proposition_7_2_5 a m).mp hseries

  intro ε hε

  obtain ⟨N, hmN, hN⟩ :=
    htail ε hε

  refine ⟨N, hmN, ?_⟩

  intro n hn

  have hsingle :
      |tailSum a n n| ≤ ε := by
    exact hN n n hn (le_rfl)

  rw [tailSum_self] at hsingle

  simpa using hsingle


/-!
============================================================
Exercise 7.2.3
============================================================
-/

theorem exercise_7_2_3
    (a : ℕ → ℝ)
    (m : ℕ)
    (hseries : SeriesConverges a m) :
    ConvergesFrom a m 0 := by

  exact corollary_7_2_6
    a
    m
    hseries

end TaoExercise7_2_3
