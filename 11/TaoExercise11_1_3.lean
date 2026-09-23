import Mathlib

namespace TaoExercise11_1_3

open Set

/-!
============================================================
Ambient interval: either (a,b) or [a,b)
============================================================
-/

def IsRightOpenInterval
    (I : Set ℝ)
    (a b : ℝ) : Prop :=
  I = Ioo a b ∨ I = Ico a b


lemma mem_ambient_lt_right
    {I : Set ℝ}
    {a b x : ℝ}
    (hI : IsRightOpenInterval I a b)
    (hx : x ∈ I) :
    x < b := by

  rcases hI with hI | hI

  · rw [hI] at hx
    exact hx.2

  · rw [hI] at hx
    exact hx.2


lemma mem_ambient_left_le
    {I : Set ℝ}
    {a b x : ℝ}
    (hI : IsRightOpenInterval I a b)
    (hx : x ∈ I) :
    a ≤ x := by

  rcases hI with hI | hI

  · rw [hI] at hx
    exact le_of_lt hx.1

  · rw [hI] at hx
    exact hx.1


lemma interior_mem_ambient
    {I : Set ℝ}
    {a b x : ℝ}
    (hI : IsRightOpenInterval I a b)
    (hax : a < x)
    (hxb : x < b) :
    x ∈ I := by

  rcases hI with hI | hI

  · rw [hI]
    exact ⟨hax, hxb⟩

  · rw [hI]
    exact ⟨le_of_lt hax, hxb⟩


/-!
============================================================
Every piece is bounded above by b
============================================================
-/

lemma piece_bddAbove
    {ι : Type*}
    (I : Set ℝ)
    (P : ι → Set ℝ)
    (a b : ℝ)
    (hI : IsRightOpenInterval I a b)
    (hsub : ∀ j, P j ⊆ I)
    (j : ι) :
    BddAbove (P j) := by

  refine ⟨b, ?_⟩

  intro x hx

  exact le_of_lt
    (mem_ambient_lt_right
      hI
      (hsub j hx))


/-!
============================================================
Every piece is bounded below by a
============================================================
-/

lemma piece_bddBelow
    {ι : Type*}
    (I : Set ℝ)
    (P : ι → Set ℝ)
    (a b : ℝ)
    (hI : IsRightOpenInterval I a b)
    (hsub : ∀ j, P j ⊆ I)
    (j : ι) :
    BddBelow (P j) := by

  refine ⟨a, ?_⟩

  intro x hx

  exact mem_ambient_left_le
    hI
    (hsub j hx)


/-!
============================================================
For every piece, sup(P j) ≤ b
============================================================
-/

lemma piece_sSup_le_right
    {ι : Type*}
    (I : Set ℝ)
    (P : ι → Set ℝ)
    (a b : ℝ)
    (hI : IsRightOpenInterval I a b)
    (hsub : ∀ j, P j ⊆ I)
    (hne : ∀ j, (P j).Nonempty)
    (j : ι) :
    sSup (P j) ≤ b := by

  apply csSup_le (hne j)

  intro x hx

  exact le_of_lt
    (mem_ambient_lt_right
      hI
      (hsub j hx))


/-!
============================================================
A finite cover must contain a piece whose supremum is b
============================================================
-/

lemma exists_piece_sSup_eq_right
    {ι : Type*}
    [Fintype ι]
    [Nonempty ι]
    (I : Set ℝ)
    (P : ι → Set ℝ)
    (a b : ℝ)
    (hab : a < b)
    (hI : IsRightOpenInterval I a b)
    (hsub : ∀ j, P j ⊆ I)
    (hne : ∀ j, (P j).Nonempty)
    (hcover :
      ∀ x ∈ I,
        ∃ j, x ∈ P j) :
    ∃ j, sSup (P j) = b := by

  by_contra hnone

  push Not at hnone

  have hlt :
      ∀ j, sSup (P j) < b := by

    intro j

    have hle :
        sSup (P j) ≤ b := by
      exact piece_sSup_le_right
        I P a b hI hsub hne j

    exact lt_of_le_of_ne hle (hnone j)

  classical

  let S : Finset ℝ :=
    Finset.univ.image
      (fun j : ι => sSup (P j))

  have hS :
      S.Nonempty := by

    obtain ⟨j⟩ := ‹Nonempty ι›

    refine ⟨sSup (P j), ?_⟩

    simp [S]

  let m : ℝ :=
    S.max' hS

  have hm_mem :
      m ∈ S := by
    exact S.max'_mem hS

  obtain ⟨jmax, hjmax, hsup_eq⟩ :=
    Finset.mem_image.mp hm_mem

  have hm_eq :
      sSup (P jmax) = m := by
    exact hsup_eq

  have hm_lt_b :
      m < b := by

    rw [← hm_eq]

    exact hlt jmax

  have hsup_le_m :
      ∀ j, sSup (P j) ≤ m := by

    intro j

    exact Finset.le_max'
      S
      (sSup (P j))
      (by
        simp [S])

  /-
  Choose z strictly between max a m and b.
  -/

  let z : ℝ :=
    (max a m + b) / 2

  have hmax_lt_b :
      max a m < b := by
    exact max_lt hab hm_lt_b

  have hmax_lt_z :
      max a m < z := by

    dsimp [z]

    linarith

  have hz_lt_b :
      z < b := by

    dsimp [z]

    linarith

  have ha_lt_z :
      a < z := by

    exact lt_of_le_of_lt
      (le_max_left a m)
      hmax_lt_z

  have hm_lt_z :
      m < z := by

    exact lt_of_le_of_lt
      (le_max_right a m)
      hmax_lt_z

  have hzI :
      z ∈ I := by

    exact interior_mem_ambient
      hI
      ha_lt_z
      hz_lt_b

  obtain ⟨j, hzj⟩ :=
    hcover z hzI

  have hz_le_sup :
      z ≤ sSup (P j) := by

    exact le_csSup
      (piece_bddAbove I P a b hI hsub j)
      hzj

  have hsupj_le_m :
      sSup (P j) ≤ m := by

    exact hsup_le_m j

  linarith


/-!
============================================================
If c = inf P and z > c, there is a point of P below z
============================================================
-/

lemma exists_mem_lt_of_sInf_lt
    {S : Set ℝ}
    (hne : S.Nonempty)
    (hbdd : BddBelow S)
    {z : ℝ}
    (hz : sInf S < z) :
    ∃ x ∈ S, x < z := by

  by_contra h

  push Not at h

  have hzLower :
      z ∈ lowerBounds S := by

    intro x hx

    exact h x hx

  have hz_le_inf :
      z ≤ sInf S := by

    exact le_csInf hne hzLower

  linarith


/-!
============================================================
If z < sup P, there is a point of P above z
============================================================
-/

lemma exists_lt_mem_of_lt_sSup
    {S : Set ℝ}
    (hne : S.Nonempty)
    (hbdd : BddAbove S)
    {z : ℝ}
    (hz : z < sSup S) :
    ∃ y ∈ S, z < y := by

  by_contra h

  push Not at h

  have hzUpper :
      z ∈ upperBounds S := by

    intro y hy

    exact h y hy

  have hsup_le_z :
      sSup S ≤ z := by

    exact csSup_le hne hzUpper

  linarith


/-!
============================================================
An interval piece whose supremum is b has shape
(c,b) or [c,b)
============================================================
-/

lemma piece_eq_Ioo_or_Ico_of_sSup_eq
    {ι : Type*}
    (I : Set ℝ)
    (P : ι → Set ℝ)
    (a b : ℝ)
    (hI : IsRightOpenInterval I a b)
    (hsub : ∀ j, P j ⊆ I)
    (hne : ∀ j, (P j).Nonempty)
    (hconn : ∀ j, (P j).OrdConnected)
    (j : ι)
    (hsup : sSup (P j) = b) :
    ∃ c : ℝ,
      a ≤ c ∧
      c ≤ b ∧
      (P j = Ioo c b ∨
       P j = Ico c b) := by

  let c : ℝ := sInf (P j)

  have hbelow :
      BddBelow (P j) := by

    exact piece_bddBelow
      I P a b hI hsub j

  have habove :
      BddAbove (P j) := by

    exact piece_bddAbove
      I P a b hI hsub j

  have hac :
      a ≤ c := by

    dsimp [c]

    apply le_csInf (hne j)

    intro x hx

    exact mem_ambient_left_le
      hI
      (hsub j hx)

  have hcb :
      c ≤ b := by

    obtain ⟨x, hx⟩ := hne j

    have hcx :
        c ≤ x := by

      dsimp [c]

      exact csInf_le hbelow hx

    have hxb :
        x ≤ b := by

      exact le_of_lt
        (mem_ambient_lt_right
          hI
          (hsub j hx))

    exact le_trans hcx hxb

  /-
  Every element of P lies in [c,b).
  -/

  have hmem_bounds :
      ∀ x ∈ P j,
        c ≤ x ∧ x < b := by

    intro x hx

    constructor

    · dsimp [c]

      exact csInf_le hbelow hx

    · exact mem_ambient_lt_right
        hI
        (hsub j hx)

  /-
  Every point strictly between c and b lies in P.
  -/

  have hinterior :
      ∀ z : ℝ,
        c < z →
        z < b →
        z ∈ P j := by

    intro z hcz hzb

    have hinf_lt_z :
        sInf (P j) < z := by

      simpa [c] using hcz

    have hz_lt_sup :
        z < sSup (P j) := by

      rw [hsup]

      exact hzb

    obtain ⟨x, hxP, hxz⟩ :=
      exists_mem_lt_of_sInf_lt
        (hne j)
        hbelow
        hinf_lt_z

    obtain ⟨y, hyP, hzy⟩ :=
      exists_lt_mem_of_lt_sSup
        (hne j)
        habove
        hz_lt_sup

    have hzIcc :
        z ∈ Icc x y := by

      exact
        ⟨le_of_lt hxz,
         le_of_lt hzy⟩

    exact (hconn j).out
      hxP
      hyP
      hzIcc

  /-
  Now decide whether the left endpoint c belongs to P.
  -/

  by_cases hcP : c ∈ P j

  · refine ⟨c, hac, hcb, Or.inr ?_⟩

    apply Set.Subset.antisymm

    · intro x hx

      have hb := hmem_bounds x hx

      exact ⟨hb.1, hb.2⟩

    · intro x hx

      rcases hx with ⟨hcx, hxb⟩

      rcases hcx.eq_or_lt with hcxEq | hcxLt

      · subst x
        exact hcP

      · exact hinterior x hcxLt hxb

  · refine ⟨c, hac, hcb, Or.inl ?_⟩

    apply Set.Subset.antisymm

    · intro x hx

      have hb := hmem_bounds x hx

      have hcx :
          c < x := by

        exact lt_of_le_of_ne
          hb.1
          (by
            intro hxc
            apply hcP
            simpa [hxc] using hx)

      exact ⟨hcx, hb.2⟩

    · intro x hx

      exact hinterior
        x
        hx.1
        hx.2


/-!
============================================================
Exercise 11.1.3
============================================================
-/

theorem exercise_11_1_3
    {ι : Type*}
    [Fintype ι]
    [Nonempty ι]
    (I : Set ℝ)
    (P : ι → Set ℝ)
    (a b : ℝ)
    (hab : a < b)
    (hI : IsRightOpenInterval I a b)
    (hsub : ∀ j, P j ⊆ I)
    (hne : ∀ j, (P j).Nonempty)
    (hinterval :
      ∀ j, (P j).OrdConnected)
    (hcover :
      ∀ x ∈ I,
        ∃ j, x ∈ P j) :
    ∃ j c,
      a ≤ c ∧
      c ≤ b ∧
      (P j = Ioo c b ∨
       P j = Ico c b) := by

  obtain ⟨j, hsup⟩ :=
    exists_piece_sSup_eq_right
      I
      P
      a
      b
      hab
      hI
      hsub
      hne
      hcover

  obtain ⟨c, hac, hcb, hshape⟩ :=
    piece_eq_Ioo_or_Ico_of_sSup_eq
      I
      P
      a
      b
      hI
      hsub
      hne
      hinterval
      j
      hsup

  exact
    ⟨j,
     c,
     hac,
     hcb,
     hshape⟩

end TaoExercise11_1_3
