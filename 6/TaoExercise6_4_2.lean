import Mathlib

namespace TaoExercise6_4_2

/-!
============================================================
Basic definitions
============================================================
-/

/--
`c` is a limit point of the real sequence `a`, starting at `m`.
-/
def IsLimitPointFrom
    (a : ℕ → ℝ)
    (m : ℕ)
    (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ N : ℕ, m ≤ N →
      ∃ n : ℕ,
        N ≤ n ∧
        |a n - c| ≤ ε


/--
The set of values of `a` from index `N` onward,
viewed as extended real numbers.
-/
def tailSet
    (a : ℕ → ℝ)
    (N : ℕ) : Set EReal :=
  {x | ∃ n : ℕ,
      N ≤ n ∧
      x = (a n : EReal)}


/--
a_N^+ in Tao's notation:
the supremum of the tail beginning at N.
-/
noncomputable def tailSup
    (a : ℕ → ℝ)
    (N : ℕ) : EReal :=
  sSup (tailSet a N)


/--
a_N^- in Tao's notation:
the infimum of the tail beginning at N.
-/
noncomputable def tailInf
    (a : ℕ → ℝ)
    (N : ℕ) : EReal :=
  sInf (tailSet a N)


/--
The collection of all tail suprema beginning at indices N ≥ m.
-/
def tailSupValues
    (a : ℕ → ℝ)
    (m : ℕ) : Set EReal :=
  {x | ∃ N : ℕ,
      m ≤ N ∧
      x = tailSup a N}


/--
The collection of all tail infima beginning at indices N ≥ m.
-/
def tailInfValues
    (a : ℕ → ℝ)
    (m : ℕ) : Set EReal :=
  {x | ∃ N : ℕ,
      m ≤ N ∧
      x = tailInf a N}


/--
Limit superior:

    limsup a = inf_N sup_{n ≥ N} a_n.
-/
noncomputable def limsupFrom
    (a : ℕ → ℝ)
    (m : ℕ) : EReal :=
  sInf (tailSupValues a m)


/--
Limit inferior:

    liminf a = sup_N inf_{n ≥ N} a_n.
-/
noncomputable def liminfFrom
    (a : ℕ → ℝ)
    (m : ℕ) : EReal :=
  sSup (tailInfValues a m)


/-!
============================================================
Tail supremum is decreasing
============================================================
-/

theorem tailSup_antitone
    (a : ℕ → ℝ)
    {N M : ℕ}
    (hNM : N ≤ M) :
    tailSup a M ≤ tailSup a N := by

  unfold tailSup

  apply sSup_le

  intro x hx

  rcases hx with ⟨n, hMn, rfl⟩

  apply le_sSup

  exact ⟨n, le_trans hNM hMn, rfl⟩


/-!
============================================================
Tail infimum is increasing
============================================================
-/

theorem tailInf_mono
    (a : ℕ → ℝ)
    {N M : ℕ}
    (hNM : N ≤ M) :
    tailInf a N ≤ tailInf a M := by

  unfold tailInf

  apply le_sInf

  intro x hx

  rcases hx with ⟨n, hMn, rfl⟩

  apply sInf_le

  exact ⟨n, le_trans hNM hMn, rfl⟩


/-!
============================================================
Analogue of Exercise 6.1.3
PART 1: Limit points do not depend on the initial index.
============================================================
-/

theorem limitPoint_start_invariant
    (a : ℕ → ℝ)
    (m m' : ℕ)
    (c : ℝ)
    (hmm' : m ≤ m') :
    IsLimitPointFrom a m c ↔
    IsLimitPointFrom a m' c := by

  constructor

  /-
  Starting at m -> starting at m'.
  -/
  · intro h

    intro ε hε
    intro N hNm'

    have hNm :
        m ≤ N := by
      exact le_trans hmm' hNm'

    exact h ε hε N hNm

  /-
  Starting at m' -> starting at m.
  -/
  · intro h

    intro ε hε
    intro N hNm

    let N' : ℕ := max N m'

    have hm'N' :
        m' ≤ N' := by
      exact le_max_right N m'

    obtain ⟨n, hN'n, hnclose⟩ :=
      h ε hε N' hm'N'

    refine ⟨n, ?_, hnclose⟩

    have hNN' :
        N ≤ N' := by
      exact le_max_left N m'

    exact le_trans hNN' hN'n


/-!
============================================================
Analogue of Exercise 6.1.3
PART 2: limsup does not depend on the initial index.
============================================================
-/

theorem limsup_start_invariant
    (a : ℕ → ℝ)
    (m m' : ℕ)
    (hmm' : m ≤ m') :
    limsupFrom a m = limsupFrom a m' := by

  apply le_antisymm

  /-
  Since the set of tail suprema beginning at m'
  is contained in the one beginning at m,

      limsup_m ≤ limsup_m'.
  -/
  · unfold limsupFrom

    apply le_sInf

    intro x hx

    rcases hx with ⟨N, hm'N, rfl⟩

    apply sInf_le

    exact ⟨N, le_trans hmm' hm'N, rfl⟩

  /-
  Conversely, for any N ≥ m choose

      K = max N m'.

  Since K ≥ N,

      tailSup K ≤ tailSup N.

  And limsup from m' ≤ tailSup K.
  -/
  · unfold limsupFrom

    apply le_sInf

    intro x hx

    rcases hx with ⟨N, hmN, rfl⟩

    let K : ℕ := max N m'

    have hNK :
        N ≤ K := by
      exact le_max_left N m'

    have hm'K :
        m' ≤ K := by
      exact le_max_right N m'

    have hlimK :
        sInf (tailSupValues a m') ≤ tailSup a K := by

      apply sInf_le

      exact ⟨K, hm'K, rfl⟩

    have hKN :
        tailSup a K ≤ tailSup a N := by
      exact tailSup_antitone a hNK

    exact le_trans hlimK hKN


/-!
============================================================
Analogue of Exercise 6.1.3
PART 3: liminf does not depend on the initial index.
============================================================
-/

theorem liminf_start_invariant
    (a : ℕ → ℝ)
    (m m' : ℕ)
    (hmm' : m ≤ m') :
    liminfFrom a m = liminfFrom a m' := by

  apply le_antisymm

  /-
  For N ≥ m choose K = max N m'.

  tailInf N ≤ tailInf K ≤ liminf from m'.
  -/
  · unfold liminfFrom

    apply sSup_le

    intro x hx

    rcases hx with ⟨N, hmN, rfl⟩

    let K : ℕ := max N m'

    have hNK :
        N ≤ K := by
      exact le_max_left N m'

    have hm'K :
        m' ≤ K := by
      exact le_max_right N m'

    have hNKinf :
        tailInf a N ≤ tailInf a K := by
      exact tailInf_mono a hNK

    have hKlim :
        tailInf a K ≤ sSup (tailInfValues a m') := by

      apply le_sSup

      exact ⟨K, hm'K, rfl⟩

    exact le_trans hNKinf hKlim

  /-
  Every tail infimum starting after m' also occurs
  among those starting after m.
  -/
  · unfold liminfFrom

    apply sSup_le

    intro x hx

    rcases hx with ⟨N, hm'N, rfl⟩

    apply le_sSup

    exact ⟨N, le_trans hmm' hm'N, rfl⟩


/-!
============================================================
Analogue of Exercise 6.1.4
PART 1: Limit points are invariant under finite shifts.
============================================================
-/

theorem limitPoint_shift_invariant
    (a : ℕ → ℝ)
    (m k : ℕ)
    (c : ℝ) :
    IsLimitPointFrom a m c ↔
    IsLimitPointFrom (fun n => a (n + k)) m c := by

  constructor

  /-
  a_n -> a_{n+k}.
  -/
  · intro h

    intro ε hε
    intro N hmN

    obtain ⟨t, hNt, htclose⟩ :=
      h ε hε (N + k)
        (by omega)

    let n : ℕ := t - k

    have hkt :
        k ≤ t := by
      omega

    have hNn :
        N ≤ n := by
      dsimp [n]
      omega

    refine ⟨n, hNn, ?_⟩

    have hnk :
        n + k = t := by
      dsimp [n]
      exact Nat.sub_add_cancel hkt

    simpa [hnk] using htclose

  /-
  a_{n+k} -> a_n.
  -/
  · intro h

    intro ε hε
    intro N hmN

    let N' : ℕ := max N m

    have hmN' :
        m ≤ N' := by
      exact le_max_right N m

    obtain ⟨n, hN'n, hnclose⟩ :=
      h ε hε N' hmN'

    refine ⟨n + k, ?_, hnclose⟩

    have hNN' :
        N ≤ N' := by
      exact le_max_left N m

    omega


/-!
============================================================
Tail sets after shifting
============================================================
-/

theorem tailSet_shift
    (a : ℕ → ℝ)
    (N k : ℕ) :
    tailSet (fun n => a (n + k)) N =
    tailSet a (N + k) := by

  ext x

  constructor

  · intro hx

    rcases hx with ⟨n, hNn, hx⟩

    refine ⟨n + k, ?_, ?_⟩

    · omega

    · exact hx

  · intro hx

    rcases hx with ⟨t, hNt, hx⟩

    have hkt :
        k ≤ t := by
      omega

    let n : ℕ := t - k

    have hNn :
        N ≤ n := by
      dsimp [n]
      omega

    refine ⟨n, hNn, ?_⟩

    have hnk :
        n + k = t := by
      dsimp [n]
      exact Nat.sub_add_cancel hkt

    simpa [hnk] using hx


theorem tailSup_shift
    (a : ℕ → ℝ)
    (N k : ℕ) :
    tailSup (fun n => a (n + k)) N =
    tailSup a (N + k) := by

  unfold tailSup

  rw [tailSet_shift]


theorem tailInf_shift
    (a : ℕ → ℝ)
    (N k : ℕ) :
    tailInf (fun n => a (n + k)) N =
    tailInf a (N + k) := by

  unfold tailInf

  rw [tailSet_shift]


/-!
============================================================
Sets of tail suprema after shifting
============================================================
-/

theorem tailSupValues_shift
    (a : ℕ → ℝ)
    (m k : ℕ) :
    tailSupValues (fun n => a (n + k)) m =
    tailSupValues a (m + k) := by

  ext x

  constructor

  · intro hx

    rcases hx with ⟨N, hmN, hx⟩

    refine ⟨N + k, ?_, ?_⟩

    · omega

    · calc
        x = tailSup (fun n => a (n + k)) N := hx
        _ = tailSup a (N + k) := tailSup_shift a N k

  · intro hx

    rcases hx with ⟨M, hmkM, hx⟩

    have hkM :
        k ≤ M := by
      omega

    let N : ℕ := M - k

    have hmN :
        m ≤ N := by
      dsimp [N]
      omega

    have hNk :
        N + k = M := by
      dsimp [N]
      exact Nat.sub_add_cancel hkM

    refine ⟨N, hmN, ?_⟩

    calc
      x = tailSup a M := hx
      _ = tailSup a (N + k) := by rw [hNk]
      _ = tailSup (fun n => a (n + k)) N := by
        symm
        exact tailSup_shift a N k


/-!
============================================================
Sets of tail infima after shifting
============================================================
-/

theorem tailInfValues_shift
    (a : ℕ → ℝ)
    (m k : ℕ) :
    tailInfValues (fun n => a (n + k)) m =
    tailInfValues a (m + k) := by

  ext x

  constructor

  · intro hx

    rcases hx with ⟨N, hmN, hx⟩

    refine ⟨N + k, ?_, ?_⟩

    · omega

    · calc
        x = tailInf (fun n => a (n + k)) N := hx
        _ = tailInf a (N + k) := tailInf_shift a N k

  · intro hx

    rcases hx with ⟨M, hmkM, hx⟩

    have hkM :
        k ≤ M := by
      omega

    let N : ℕ := M - k

    have hmN :
        m ≤ N := by
      dsimp [N]
      omega

    have hNk :
        N + k = M := by
      dsimp [N]
      exact Nat.sub_add_cancel hkM

    refine ⟨N, hmN, ?_⟩

    calc
      x = tailInf a M := hx
      _ = tailInf a (N + k) := by rw [hNk]
      _ = tailInf (fun n => a (n + k)) N := by
        symm
        exact tailInf_shift a N k


/-!
============================================================
Shifted limsup = limsup starting from m+k
============================================================
-/

theorem limsup_shift_eq_start_add
    (a : ℕ → ℝ)
    (m k : ℕ) :
    limsupFrom (fun n => a (n + k)) m =
    limsupFrom a (m + k) := by

  unfold limsupFrom

  rw [tailSupValues_shift]


/-!
============================================================
Shifted liminf = liminf starting from m+k
============================================================
-/

theorem liminf_shift_eq_start_add
    (a : ℕ → ℝ)
    (m k : ℕ) :
    liminfFrom (fun n => a (n + k)) m =
    liminfFrom a (m + k) := by

  unfold liminfFrom

  rw [tailInfValues_shift]


/-!
============================================================
Analogue of Exercise 6.1.4:
limsup is invariant under finite shifts.
============================================================
-/

theorem limsup_shift_invariant
    (a : ℕ → ℝ)
    (m k : ℕ) :
    limsupFrom (fun n => a (n + k)) m =
    limsupFrom a m := by

  calc
    limsupFrom (fun n => a (n + k)) m
        = limsupFrom a (m + k) := by
            exact limsup_shift_eq_start_add a m k

    _ = limsupFrom a m := by
          symm

          exact limsup_start_invariant
            a
            m
            (m + k)
            (by omega)


/-!
============================================================
Analogue of Exercise 6.1.4:
liminf is invariant under finite shifts.
============================================================
-/

theorem liminf_shift_invariant
    (a : ℕ → ℝ)
    (m k : ℕ) :
    liminfFrom (fun n => a (n + k)) m =
    liminfFrom a m := by

  calc
    liminfFrom (fun n => a (n + k)) m
        = liminfFrom a (m + k) := by
            exact liminf_shift_eq_start_add a m k

    _ = liminfFrom a m := by
          symm

          exact liminf_start_invariant
            a
            m
            (m + k)
            (by omega)


/-!
============================================================
Exercise 6.4.2 packaged:
analogue of Exercise 6.1.3
============================================================
-/

theorem exercise_6_4_2_start_index
    (a : ℕ → ℝ)
    (m m' : ℕ)
    (c : ℝ)
    (hmm' : m ≤ m') :
    (IsLimitPointFrom a m c ↔
      IsLimitPointFrom a m' c)
    ∧
    limsupFrom a m = limsupFrom a m'
    ∧
    liminfFrom a m = liminfFrom a m' := by

  constructor

  · exact limitPoint_start_invariant
      a m m' c hmm'

  constructor

  · exact limsup_start_invariant
      a m m' hmm'

  · exact liminf_start_invariant
      a m m' hmm'


/-!
============================================================
Exercise 6.4.2 packaged:
analogue of Exercise 6.1.4
============================================================
-/

theorem exercise_6_4_2_shift
    (a : ℕ → ℝ)
    (m k : ℕ)
    (c : ℝ) :
    (IsLimitPointFrom a m c ↔
      IsLimitPointFrom
        (fun n => a (n + k))
        m
        c)
    ∧
    limsupFrom (fun n => a (n + k)) m =
      limsupFrom a m
    ∧
    liminfFrom (fun n => a (n + k)) m =
      liminfFrom a m := by

  constructor

  · exact limitPoint_shift_invariant
      a m k c

  constructor

  · exact limsup_shift_invariant
      a m k

  · exact liminf_shift_invariant
      a m k

end TaoExercise6_4_2
