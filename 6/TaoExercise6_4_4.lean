import Mathlib

namespace TaoExercise6_4_4

/-!
Exercise 6.4.4 — Lemma 6.4.13

If

    a n ≤ b n

for every n ≥ m, then

1. sup a ≤ sup b
2. inf a ≤ inf b
3. limsup a ≤ limsup b
4. liminf a ≤ liminf b

We work in `EReal`, so all suprema and infima exist,
including the cases ±∞.
-/


/-!
============================================================
Basic definitions
============================================================
-/

/--
The set of values of a sequence from index `m` onward.
-/
def seqSet
    (a : ℕ → EReal)
    (m : ℕ) : Set EReal :=
  {x | ∃ n : ℕ, m ≤ n ∧ x = a n}


/--
Supremum of the sequence from index `m`.
-/
noncomputable def seqSup
    (a : ℕ → EReal)
    (m : ℕ) : EReal :=
  sSup (seqSet a m)


/--
Infimum of the sequence from index `m`.
-/
noncomputable def seqInf
    (a : ℕ → EReal)
    (m : ℕ) : EReal :=
  sInf (seqSet a m)


/--
Limit superior:

    limsup a = inf_N≥m sup_{n≥N} a_n.
-/
noncomputable def limsupFrom
    (a : ℕ → EReal)
    (m : ℕ) : EReal :=
  seqInf (fun N => seqSup a N) m


/--
Limit inferior:

    liminf a = sup_N≥m inf_{n≥N} a_n.
-/
noncomputable def liminfFrom
    (a : ℕ → EReal)
    (m : ℕ) : EReal :=
  seqSup (fun N => seqInf a N) m


/-!
============================================================
Part 1

If a_n ≤ b_n for n ≥ m, then

    sup a ≤ sup b.
============================================================
-/

theorem seqSup_mono
    (a b : ℕ → EReal)
    (m : ℕ)
    (h :
      ∀ n : ℕ,
        m ≤ n →
        a n ≤ b n) :
    seqSup a m ≤ seqSup b m := by

  unfold seqSup

  apply sSup_le

  intro x hx

  rcases hx with ⟨n, hn, rfl⟩

  have hab :
      a n ≤ b n := by
    exact h n hn

  have hbSup :
      b n ≤ sSup (seqSet b m) := by

    apply le_sSup

    exact ⟨n, hn, rfl⟩

  exact le_trans hab hbSup


/-!
============================================================
Part 2

If a_n ≤ b_n for n ≥ m, then

    inf a ≤ inf b.
============================================================
-/

theorem seqInf_mono
    (a b : ℕ → EReal)
    (m : ℕ)
    (h :
      ∀ n : ℕ,
        m ≤ n →
        a n ≤ b n) :
    seqInf a m ≤ seqInf b m := by

  unfold seqInf

  apply le_sInf

  intro x hx

  rcases hx with ⟨n, hn, rfl⟩

  have hInfA :
      sInf (seqSet a m) ≤ a n := by

    apply sInf_le

    exact ⟨n, hn, rfl⟩

  have hab :
      a n ≤ b n := by
    exact h n hn

  exact le_trans hInfA hab


/-!
============================================================
The pointwise inequality also holds on every later tail.
============================================================
-/

theorem tail_pointwise
    (a b : ℕ → EReal)
    (m N : ℕ)
    (hmN : m ≤ N)
    (h :
      ∀ n : ℕ,
        m ≤ n →
        a n ≤ b n) :
    ∀ n : ℕ,
      N ≤ n →
      a n ≤ b n := by

  intro n hNn

  exact h n (le_trans hmN hNn)


/-!
============================================================
Tail suprema preserve the inequality.
============================================================
-/

theorem tailSup_mono
    (a b : ℕ → EReal)
    (m N : ℕ)
    (hmN : m ≤ N)
    (h :
      ∀ n : ℕ,
        m ≤ n →
        a n ≤ b n) :
    seqSup a N ≤ seqSup b N := by

  apply seqSup_mono

  intro n hNn

  exact h n (le_trans hmN hNn)


/-!
============================================================
Tail infima preserve the inequality.
============================================================
-/

theorem tailInf_mono
    (a b : ℕ → EReal)
    (m N : ℕ)
    (hmN : m ≤ N)
    (h :
      ∀ n : ℕ,
        m ≤ n →
        a n ≤ b n) :
    seqInf a N ≤ seqInf b N := by

  apply seqInf_mono

  intro n hNn

  exact h n (le_trans hmN hNn)


/-!
============================================================
Part 3

If a_n ≤ b_n eventually from m, then

    limsup a ≤ limsup b.
============================================================
-/

theorem limsup_mono
    (a b : ℕ → EReal)
    (m : ℕ)
    (h :
      ∀ n : ℕ,
        m ≤ n →
        a n ≤ b n) :
    limsupFrom a m ≤ limsupFrom b m := by

  unfold limsupFrom

  apply seqInf_mono

  intro N hmN

  exact tailSup_mono
    a
    b
    m
    N
    hmN
    h


/-!
============================================================
Part 4

If a_n ≤ b_n eventually from m, then

    liminf a ≤ liminf b.
============================================================
-/

theorem liminf_mono
    (a b : ℕ → EReal)
    (m : ℕ)
    (h :
      ∀ n : ℕ,
        m ≤ n →
        a n ≤ b n) :
    liminfFrom a m ≤ liminfFrom b m := by

  unfold liminfFrom

  apply seqSup_mono

  intro N hmN

  exact tailInf_mono
    a
    b
    m
    N
    hmN
    h


/-!
============================================================
Lemma 6.4.13 packaged
============================================================
-/

theorem lemma_6_4_13
    (a b : ℕ → EReal)
    (m : ℕ)
    (h :
      ∀ n : ℕ,
        m ≤ n →
        a n ≤ b n) :
    seqSup a m ≤ seqSup b m
    ∧
    seqInf a m ≤ seqInf b m
    ∧
    limsupFrom a m ≤ limsupFrom b m
    ∧
    liminfFrom a m ≤ liminfFrom b m := by

  constructor

  /-
  (1) Supremum.
  -/
  · exact seqSup_mono a b m h

  constructor

  /-
  (2) Infimum.
  -/
  · exact seqInf_mono a b m h

  constructor

  /-
  (3) Limit superior.
  -/
  · exact limsup_mono a b m h

  /-
  (4) Limit inferior.
  -/
  · exact liminf_mono a b m h


/-!
============================================================
Version for ordinary real-valued sequences
============================================================
-/

theorem exercise_6_4_4
    (a b : ℕ → ℝ)
    (m : ℕ)
    (h :
      ∀ n : ℕ,
        m ≤ n →
        a n ≤ b n) :
    seqSup (fun n => (a n : EReal)) m
        ≤ seqSup (fun n => (b n : EReal)) m
    ∧
    seqInf (fun n => (a n : EReal)) m
        ≤ seqInf (fun n => (b n : EReal)) m
    ∧
    limsupFrom (fun n => (a n : EReal)) m
        ≤ limsupFrom (fun n => (b n : EReal)) m
    ∧
    liminfFrom (fun n => (a n : EReal)) m
        ≤ liminfFrom (fun n => (b n : EReal)) m := by

  apply lemma_6_4_13

  intro n hn

  exact_mod_cast h n hn

end TaoExercise6_4_4
