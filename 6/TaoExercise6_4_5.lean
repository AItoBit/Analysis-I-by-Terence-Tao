import Mathlib

namespace TaoExercise6_4_5

/-!
Exercise 6.4.5 — Corollary 6.4.14

Squeeze theorem.

If

    aₙ ≤ bₙ ≤ cₙ

for all n ≥ m, and

    aₙ → L
    cₙ → L,

then

    bₙ → L.

We prove this using:

* Lemma 6.4.13:
      limsup a ≤ limsup b ≤ limsup c
      liminf a ≤ liminf b ≤ liminf c

* Proposition 6.4.12(f):
      a sequence converges to L iff
      liminf = L and limsup = L.
-/


/-!
============================================================
Basic definitions
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


/--
Values of an EReal-valued sequence from index m onward.
-/
def seqSet
    (a : ℕ → EReal)
    (m : ℕ) : Set EReal :=
  {x | ∃ n : ℕ,
      m ≤ n ∧
      x = a n}


/--
Supremum of a sequence from m onward.
-/
noncomputable def seqSup
    (a : ℕ → EReal)
    (m : ℕ) : EReal :=
  sSup (seqSet a m)


/--
Infimum of a sequence from m onward.
-/
noncomputable def seqInf
    (a : ℕ → EReal)
    (m : ℕ) : EReal :=
  sInf (seqSet a m)


/--
Limit superior.
-/
noncomputable def limsupFrom
    (a : ℕ → EReal)
    (m : ℕ) : EReal :=
  seqInf (fun N => seqSup a N) m


/--
Limit inferior.
-/
noncomputable def liminfFrom
    (a : ℕ → EReal)
    (m : ℕ) : EReal :=
  seqSup (fun N => seqInf a N) m


/-!
============================================================
Lemma 6.4.13
Supremum monotonicity
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

  have hb :
      b n ≤ sSup (seqSet b m) := by

    apply le_sSup

    exact ⟨n, hn, rfl⟩

  exact le_trans hab hb


/-!
============================================================
Lemma 6.4.13
Infimum monotonicity
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

  have ha :
      sInf (seqSet a m) ≤ a n := by

    apply sInf_le

    exact ⟨n, hn, rfl⟩

  have hab :
      a n ≤ b n := by
    exact h n hn

  exact le_trans ha hab


/-!
============================================================
Tail versions
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
Lemma 6.4.13:
limsup monotonicity
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
    a b m N hmN h


/-!
============================================================
Lemma 6.4.13:
liminf monotonicity
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
    a b m N hmN h


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
    limsupFrom a m ≤ limsupFrom b m
    ∧
    liminfFrom a m ≤ liminfFrom b m := by

  constructor

  · exact limsup_mono a b m h

  · exact liminf_mono a b m h


/-!
============================================================
Corollary 6.4.14

We use Proposition 6.4.12(f) in the following form:

    ConvergesFrom s m L
      ↔
    liminf s = L ∧ limsup s = L.

Because our liminf/limsup live in EReal,
the real limit is coerced to EReal.
============================================================
-/

theorem corollary_6_4_14
    (a b c : ℕ → ℝ)
    (m : ℕ)
    (L : ℝ)

    (hab :
      ∀ n : ℕ,
        m ≤ n →
        a n ≤ b n)

    (hbc :
      ∀ n : ℕ,
        m ≤ n →
        b n ≤ c n)

    (ha :
      ConvergesFrom a m L)

    (hc :
      ConvergesFrom c m L)

    /-
    Proposition 6.4.12(f), instantiated for a.
    -/
    (ha_char :
      ConvergesFrom a m L ↔
        liminfFrom (fun n => (a n : EReal)) m = (L : EReal)
        ∧
        limsupFrom (fun n => (a n : EReal)) m = (L : EReal))

    /-
    Proposition 6.4.12(f), instantiated for b.
    -/
    (hb_char :
      ConvergesFrom b m L ↔
        liminfFrom (fun n => (b n : EReal)) m = (L : EReal)
        ∧
        limsupFrom (fun n => (b n : EReal)) m = (L : EReal))

    /-
    Proposition 6.4.12(f), instantiated for c.
    -/
    (hc_char :
      ConvergesFrom c m L ↔
        liminfFrom (fun n => (c n : EReal)) m = (L : EReal)
        ∧
        limsupFrom (fun n => (c n : EReal)) m = (L : EReal)) :

    ConvergesFrom b m L := by

  /-
  Since a and c converge to L, Proposition 6.4.12(f)
  identifies all their liminf/limsup values with L.
  -/
  have haLimits :
      liminfFrom (fun n => (a n : EReal)) m = (L : EReal)
      ∧
      limsupFrom (fun n => (a n : EReal)) m = (L : EReal) := by

    exact ha_char.mp ha

  have hcLimits :
      liminfFrom (fun n => (c n : EReal)) m = (L : EReal)
      ∧
      limsupFrom (fun n => (c n : EReal)) m = (L : EReal) := by

    exact hc_char.mp hc

  /-
  Convert a_n ≤ b_n to EReal.
  -/
  have habE :
      ∀ n : ℕ,
        m ≤ n →
        (a n : EReal) ≤ (b n : EReal) := by

    intro n hn

    exact_mod_cast hab n hn

  /-
  Convert b_n ≤ c_n to EReal.
  -/
  have hbcE :
      ∀ n : ℕ,
        m ≤ n →
        (b n : EReal) ≤ (c n : EReal) := by

    intro n hn

    exact_mod_cast hbc n hn

  /-
  Lemma 6.4.13 gives

      limsup a ≤ limsup b ≤ limsup c.
  -/
  have hSupAB :
      limsupFrom (fun n => (a n : EReal)) m
        ≤
      limsupFrom (fun n => (b n : EReal)) m := by

    exact limsup_mono
      (fun n => (a n : EReal))
      (fun n => (b n : EReal))
      m
      habE

  have hSupBC :
      limsupFrom (fun n => (b n : EReal)) m
        ≤
      limsupFrom (fun n => (c n : EReal)) m := by

    exact limsup_mono
      (fun n => (b n : EReal))
      (fun n => (c n : EReal))
      m
      hbcE

  /-
  Since both outside limsups equal L,

      L ≤ limsup b ≤ L,

  hence limsup b = L.
  -/
  have hSupB :
      limsupFrom (fun n => (b n : EReal)) m =
        (L : EReal) := by

    apply le_antisymm

    · rw [hcLimits.2] at hSupBC
      exact hSupBC

    · rw [haLimits.2] at hSupAB
      exact hSupAB

  /-
  Likewise,

      liminf a ≤ liminf b ≤ liminf c.
  -/
  have hInfAB :
      liminfFrom (fun n => (a n : EReal)) m
        ≤
      liminfFrom (fun n => (b n : EReal)) m := by

    exact liminf_mono
      (fun n => (a n : EReal))
      (fun n => (b n : EReal))
      m
      habE

  have hInfBC :
      liminfFrom (fun n => (b n : EReal)) m
        ≤
      liminfFrom (fun n => (c n : EReal)) m := by

    exact liminf_mono
      (fun n => (b n : EReal))
      (fun n => (c n : EReal))
      m
      hbcE

  /-
  Since both outside liminfs equal L,

      L ≤ liminf b ≤ L,

  hence liminf b = L.
  -/
  have hInfB :
      liminfFrom (fun n => (b n : EReal)) m =
        (L : EReal) := by

    apply le_antisymm

    · rw [hcLimits.1] at hInfBC
      exact hInfBC

    · rw [haLimits.1] at hInfAB
      exact hInfAB

  /-
  Finally use Proposition 6.4.12(f) backwards.
  -/
  apply hb_char.mpr

  exact ⟨hInfB, hSupB⟩

end TaoExercise6_4_5
