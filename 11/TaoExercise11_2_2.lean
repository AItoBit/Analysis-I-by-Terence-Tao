import Mathlib

namespace TaoExercise11_2_2

open Set

/-!
============================================================
Partitions
============================================================
-/

def IsPartitionTao
    (I : Set ℝ)
    (P : Set (Set ℝ)) : Prop :=
  (∀ J ∈ P, J ⊆ I) ∧
  (∀ x ∈ I,
    ∃! J : Set ℝ,
      J ∈ P ∧ x ∈ J)


/-!
============================================================
Refinement
============================================================
-/

def FinerThan
    (Q P : Set (Set ℝ)) : Prop :=
  ∀ S ∈ Q,
    ∃ J ∈ P,
      S ⊆ J


/-!
============================================================
Common refinement
============================================================
-/

def CommonRefinement
    (P P' : Set (Set ℝ)) :
    Set (Set ℝ) :=
  {S : Set ℝ |
    ∃ J ∈ P,
      ∃ K ∈ P',
        S = J ∩ K}


/-!
============================================================
Piecewise constant with respect to one partition
============================================================
-/

def PiecewiseConstantOn
    (f : ℝ → ℝ)
    (P : Set (Set ℝ)) : Prop :=
  ∀ J ∈ P,
    ∃ c : ℝ,
      ∀ x ∈ J,
        f x = c


/-!
============================================================
Piecewise constant on I
============================================================
-/

def PiecewiseConstant
    (I : Set ℝ)
    (f : ℝ → ℝ) : Prop :=
  ∃ P : Set (Set ℝ),
    IsPartitionTao I P ∧
    PiecewiseConstantOn f P


/-!
============================================================
Lemma 11.1.18:
common refinement is a partition
============================================================
-/

lemma commonRefinement_isPartition
    (I : Set ℝ)
    (P P' : Set (Set ℝ))
    (hP : IsPartitionTao I P)
    (hP' : IsPartitionTao I P') :
    IsPartitionTao I (CommonRefinement P P') := by

  rcases hP with ⟨hPsub, hPuniq⟩
  rcases hP' with ⟨hP'sub, hP'uniq⟩

  constructor

  · intro S hS

    rcases hS with
      ⟨J, hJP, K, hKP', rfl⟩

    intro x hx

    exact hPsub J hJP hx.1

  · intro x hxI

    obtain ⟨J, hJ, hJuniq⟩ :=
      hPuniq x hxI

    obtain ⟨K, hK, hKuniq⟩ :=
      hP'uniq x hxI

    refine ⟨J ∩ K, ?_, ?_⟩

    · constructor

      · exact
          ⟨J, hJ.1,
           K, hK.1,
           rfl⟩

      · exact ⟨hJ.2, hK.2⟩

    · intro S hS

      rcases hS.1 with
        ⟨J', hJ'P,
         K', hK'P',
         hS_eq⟩

      have hxInter :
          x ∈ J' ∩ K' := by
        rw [← hS_eq]
        exact hS.2

      have hJJ :
          J' = J := by
        exact hJuniq
          J'
          ⟨hJ'P, hxInter.1⟩

      have hKK :
          K' = K := by
        exact hKuniq
          K'
          ⟨hK'P', hxInter.2⟩

      rw [hS_eq, hJJ, hKK]


/-!
============================================================
Common refinement is finer than P
============================================================
-/

lemma commonRefinement_finer_left
    (P P' : Set (Set ℝ)) :
    FinerThan
      (CommonRefinement P P')
      P := by

  intro S hS

  rcases hS with
    ⟨J, hJP, K, hKP', rfl⟩

  refine ⟨J, hJP, ?_⟩

  intro x hx

  exact hx.1


/-!
============================================================
Common refinement is finer than P'
============================================================
-/

lemma commonRefinement_finer_right
    (P P' : Set (Set ℝ)) :
    FinerThan
      (CommonRefinement P P')
      P' := by

  intro S hS

  rcases hS with
    ⟨J, hJP, K, hKP', rfl⟩

  refine ⟨K, hKP', ?_⟩

  intro x hx

  exact hx.2


/-!
============================================================
Lemma 11.2.7:
piecewise constant survives refinement
============================================================
-/

lemma piecewiseConstantOn_of_finer
    (f : ℝ → ℝ)
    (P Q : Set (Set ℝ))
    (hf : PiecewiseConstantOn f P)
    (hQP : FinerThan Q P) :
    PiecewiseConstantOn f Q := by

  intro S hS

  obtain ⟨J, hJP, hSJ⟩ :=
    hQP S hS

  obtain ⟨c, hc⟩ :=
    hf J hJP

  refine ⟨c, ?_⟩

  intro x hx

  exact hc x (hSJ hx)


/-!
============================================================
Binary operations preserve piecewise constancy
on the same partition
============================================================
-/

lemma piecewiseConstantOn_binary
    (f g : ℝ → ℝ)
    (op : ℝ → ℝ → ℝ)
    (P : Set (Set ℝ))
    (hf : PiecewiseConstantOn f P)
    (hg : PiecewiseConstantOn g P) :
    PiecewiseConstantOn
      (fun x => op (f x) (g x))
      P := by

  intro J hJ

  obtain ⟨c, hc⟩ :=
    hf J hJ

  obtain ⟨d, hd⟩ :=
    hg J hJ

  refine ⟨op c d, ?_⟩

  intro x hx

  change op (f x) (g x) = op c d

  rw [hc x hx, hd x hx]


/-!
============================================================
Put f and g on a common partition
============================================================
-/

lemma common_partition
    (I : Set ℝ)
    (f g : ℝ → ℝ)
    (hf : PiecewiseConstant I f)
    (hg : PiecewiseConstant I g) :
    ∃ Q : Set (Set ℝ),
      IsPartitionTao I Q ∧
      PiecewiseConstantOn f Q ∧
      PiecewiseConstantOn g Q := by

  rcases hf with
    ⟨P, hPpart, hfP⟩

  rcases hg with
    ⟨P', hP'part, hgP'⟩

  let Q :=
    CommonRefinement P P'

  have hQpart :
      IsPartitionTao I Q := by

    dsimp [Q]

    exact commonRefinement_isPartition
      I
      P
      P'
      hPpart
      hP'part

  have hQ_finer_P :
      FinerThan Q P := by

    dsimp [Q]

    exact commonRefinement_finer_left
      P
      P'

  have hQ_finer_P' :
      FinerThan Q P' := by

    dsimp [Q]

    exact commonRefinement_finer_right
      P
      P'

  have hfQ :
      PiecewiseConstantOn f Q := by

    exact piecewiseConstantOn_of_finer
      f
      P
      Q
      hfP
      hQ_finer_P

  have hgQ :
      PiecewiseConstantOn g Q := by

    exact piecewiseConstantOn_of_finer
      g
      P'
      Q
      hgP'
      hQ_finer_P'

  exact
    ⟨Q,
     hQpart,
     hfQ,
     hgQ⟩


/-!
============================================================
Addition
============================================================
-/

theorem piecewiseConstant_add
    (I : Set ℝ)
    (f g : ℝ → ℝ)
    (hf : PiecewiseConstant I f)
    (hg : PiecewiseConstant I g) :
    PiecewiseConstant I
      (fun x => f x + g x) := by

  obtain ⟨Q, hQpart, hfQ, hgQ⟩ :=
    common_partition I f g hf hg

  refine ⟨Q, hQpart, ?_⟩

  exact piecewiseConstantOn_binary
    f
    g
    (fun a b => a + b)
    Q
    hfQ
    hgQ


/-!
============================================================
Subtraction
============================================================
-/

theorem piecewiseConstant_sub
    (I : Set ℝ)
    (f g : ℝ → ℝ)
    (hf : PiecewiseConstant I f)
    (hg : PiecewiseConstant I g) :
    PiecewiseConstant I
      (fun x => f x - g x) := by

  obtain ⟨Q, hQpart, hfQ, hgQ⟩ :=
    common_partition I f g hf hg

  refine ⟨Q, hQpart, ?_⟩

  exact piecewiseConstantOn_binary
    f
    g
    (fun a b => a - b)
    Q
    hfQ
    hgQ


/-!
============================================================
Maximum
============================================================
-/

theorem piecewiseConstant_max
    (I : Set ℝ)
    (f g : ℝ → ℝ)
    (hf : PiecewiseConstant I f)
    (hg : PiecewiseConstant I g) :
    PiecewiseConstant I
      (fun x => max (f x) (g x)) := by

  obtain ⟨Q, hQpart, hfQ, hgQ⟩ :=
    common_partition I f g hf hg

  refine ⟨Q, hQpart, ?_⟩

  exact piecewiseConstantOn_binary
    f
    g
    max
    Q
    hfQ
    hgQ


/-!
============================================================
Multiplication
============================================================
-/

theorem piecewiseConstant_mul
    (I : Set ℝ)
    (f g : ℝ → ℝ)
    (hf : PiecewiseConstant I f)
    (hg : PiecewiseConstant I g) :
    PiecewiseConstant I
      (fun x => f x * g x) := by

  obtain ⟨Q, hQpart, hfQ, hgQ⟩ :=
    common_partition I f g hf hg

  refine ⟨Q, hQpart, ?_⟩

  exact piecewiseConstantOn_binary
    f
    g
    (fun a b => a * b)
    Q
    hfQ
    hgQ


/-!
============================================================
Division
============================================================
-/

theorem piecewiseConstant_div
    (I : Set ℝ)
    (f g : ℝ → ℝ)
    (hf : PiecewiseConstant I f)
    (hg : PiecewiseConstant I g)
    (hg_nonzero :
      ∀ x ∈ I,
        g x ≠ 0) :
    PiecewiseConstant I
      (fun x => f x / g x) := by

  obtain ⟨Q, hQpart, hfQ, hgQ⟩ :=
    common_partition I f g hf hg

  refine ⟨Q, hQpart, ?_⟩

  intro J hJ

  obtain ⟨c, hc⟩ :=
    hfQ J hJ

  obtain ⟨d, hd⟩ :=
    hgQ J hJ

  refine ⟨c / d, ?_⟩

  intro x hx

  change f x / g x = c / d

  rw [hc x hx, hd x hx]


/-!
============================================================
Lemma 11.2.8
============================================================
-/

theorem lemma_11_2_8
    (I : Set ℝ)
    (f g : ℝ → ℝ)
    (hf : PiecewiseConstant I f)
    (hg : PiecewiseConstant I g) :
    PiecewiseConstant I
        (fun x => f x + g x)
      ∧
    PiecewiseConstant I
        (fun x => f x - g x)
      ∧
    PiecewiseConstant I
        (fun x => max (f x) (g x))
      ∧
    PiecewiseConstant I
        (fun x => f x * g x)
      ∧
    ((∀ x ∈ I, g x ≠ 0) →
      PiecewiseConstant I
        (fun x => f x / g x)) := by

  refine ⟨piecewiseConstant_add I f g hf hg, ?_⟩

  refine ⟨piecewiseConstant_sub I f g hf hg, ?_⟩

  refine ⟨piecewiseConstant_max I f g hf hg, ?_⟩

  refine ⟨piecewiseConstant_mul I f g hf hg, ?_⟩

  intro hg_nonzero

  exact piecewiseConstant_div
    I
    f
    g
    hf
    hg
    hg_nonzero


/-!
============================================================
Exercise 11.2.2
============================================================
-/

theorem exercise_11_2_2
    (I : Set ℝ)
    (f g : ℝ → ℝ)
    (hf : PiecewiseConstant I f)
    (hg : PiecewiseConstant I g) :
    PiecewiseConstant I
        (fun x => f x + g x)
      ∧
    PiecewiseConstant I
        (fun x => f x - g x)
      ∧
    PiecewiseConstant I
        (fun x => max (f x) (g x))
      ∧
    PiecewiseConstant I
        (fun x => f x * g x)
      ∧
    ((∀ x ∈ I, g x ≠ 0) →
      PiecewiseConstant I
        (fun x => f x / g x)) := by

  exact lemma_11_2_8
    I
    f
    g
    hf
    hg

end TaoExercise11_2_2
