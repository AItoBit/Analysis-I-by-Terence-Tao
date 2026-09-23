import Mathlib

namespace TaoExercise11_4_1

open Set

/-!
============================================================
Basic notions
============================================================
-/

def Majorizes
    (I : Set ℝ)
    (f g : ℝ → ℝ) : Prop :=
  ∀ x ∈ I, g x ≤ f x


def Minorizes
    (I : Set ℝ)
    (f g : ℝ → ℝ) : Prop :=
  ∀ x ∈ I, f x ≤ g x


def RiemannIntegrableTao
    (upperIntegral lowerIntegral :
      Set ℝ → (ℝ → ℝ) → ℝ)
    (I : Set ℝ)
    (f : ℝ → ℝ) : Prop :=
  upperIntegral I f = lowerIntegral I f


noncomputable def riemannIntegral
    (upperIntegral :
      Set ℝ → (ℝ → ℝ) → ℝ)
    (I : Set ℝ)
    (f : ℝ → ℝ) : ℝ :=
  upperIntegral I f


/-!
============================================================
Pointwise operations
============================================================
-/

def addFun
    (f g : ℝ → ℝ) :
    ℝ → ℝ :=
  fun x => f x + g x


def subFun
    (f g : ℝ → ℝ) :
    ℝ → ℝ :=
  fun x => f x - g x


def constMulFun
    (c : ℝ)
    (f : ℝ → ℝ) :
    ℝ → ℝ :=
  fun x => c * f x


def constFun
    (c : ℝ) :
    ℝ → ℝ :=
  fun _ => c


/-!
============================================================
Basic identities between pointwise operations
============================================================
-/

lemma add_neg_eq_sub
    (f g : ℝ → ℝ) :
    addFun f (constMulFun (-1) g) =
      subFun f g := by

  funext x

  simp [addFun, constMulFun, subFun, sub_eq_add_neg]


lemma constMul_neg_one
    (f : ℝ → ℝ) :
    constMulFun (-1) f =
      fun x => -f x := by

  funext x

  simp [constMulFun]


/-!
============================================================
Elementary order lemmas
============================================================
-/

lemma sub_nonneg_of_le
    {a b : ℝ}
    (h : b ≤ a) :
    0 ≤ a - b := by

  linarith


lemma le_of_sub_nonneg
    {a b : ℝ}
    (h : 0 ≤ a - b) :
    b ≤ a := by

  linarith


/-!
============================================================
(c) Subtraction from addition and scalar multiplication
============================================================
-/

theorem integral_sub_of_add_neg
    (Int : (ℝ → ℝ) → ℝ)
    (f g : ℝ → ℝ)
    (hadd :
      Int (addFun f (constMulFun (-1) g)) =
        Int f + Int (constMulFun (-1) g))
    (hneg :
      Int (constMulFun (-1) g) =
        (-1 : ℝ) * Int g) :
    Int (subFun f g) =
      Int f - Int g := by

  have hfun :
      addFun f (constMulFun (-1) g) =
        subFun f g := by
    exact add_neg_eq_sub f g

  calc
    Int (subFun f g)
        =
      Int (addFun f (constMulFun (-1) g)) := by
        rw [hfun]

    _ =
      Int f +
        Int (constMulFun (-1) g) := by
        exact hadd

    _ =
      Int f + (-1 : ℝ) * Int g := by
        rw [hneg]

    _ =
      Int f - Int g := by
        ring


/-!
============================================================
(e) Monotonicity from positivity and subtraction
============================================================
-/

theorem integral_mono_of_nonneg
    (I : Set ℝ)
    (Int : (ℝ → ℝ) → ℝ)
    (f g : ℝ → ℝ)
    (hfg :
      ∀ x ∈ I,
        g x ≤ f x)
    (hsub :
      Int (subFun f g) =
        Int f - Int g)
    (hnonneg :
      (∀ x ∈ I,
        0 ≤ subFun f g x) →
      0 ≤ Int (subFun f g)) :
    Int g ≤ Int f := by

  have hpoint :
      ∀ x ∈ I,
        0 ≤ subFun f g x := by

    intro x hx

    unfold subFun

    exact sub_nonneg_of_le
      (hfg x hx)

  have hint :
      0 ≤ Int (subFun f g) := by

    exact hnonneg hpoint

  rw [hsub] at hint

  linarith


/-!
============================================================
Zero extension
============================================================
-/

noncomputable def zeroExtension
    (I : Set ℝ)
    (f : ℝ → ℝ) :
    ℝ → ℝ := by

  classical

  exact fun x =>
    if x ∈ I then f x else 0


lemma zeroExtension_eq
    (I : Set ℝ)
    (f : ℝ → ℝ)
    (x : ℝ)
    (hx : x ∈ I) :
    zeroExtension I f x = f x := by

  unfold zeroExtension

  simp [hx]


lemma zeroExtension_eq_zero
    (I : Set ℝ)
    (f : ℝ → ℝ)
    (x : ℝ)
    (hx : x ∉ I) :
    zeroExtension I f x = 0 := by

  unfold zeroExtension

  simp [hx]


/-!
============================================================
Restriction extended by zero
============================================================
-/

noncomputable def restrictZero
    (A : Set ℝ)
    (f : ℝ → ℝ) :
    ℝ → ℝ :=
  zeroExtension A f


lemma add_restrictZero_eq
    (I J K : Set ℝ)
    (f : ℝ → ℝ)
    (hcover :
      ∀ x ∈ I,
        x ∈ J ∨ x ∈ K)
    (hdisjoint :
      ∀ x,
        x ∈ J →
        x ∈ K →
        False) :
    ∀ x ∈ I,
      addFun
        (restrictZero J f)
        (restrictZero K f)
        x
      =
      f x := by

  intro x hxI

  obtain hxJ | hxK :=
    hcover x hxI

  · have hxNotK :
        x ∉ K := by

      intro hxK

      exact hdisjoint
        x
        hxJ
        hxK

    unfold addFun restrictZero

    rw [zeroExtension_eq
      J
      f
      x
      hxJ]

    rw [zeroExtension_eq_zero
      K
      f
      x
      hxNotK]

    ring

  · have hxNotJ :
        x ∉ J := by

      intro hxJ

      exact hdisjoint
        x
        hxJ
        hxK

    unfold addFun restrictZero

    rw [zeroExtension_eq_zero
      J
      f
      x
      hxNotJ]

    rw [zeroExtension_eq
      K
      f
      x
      hxK]

    ring


/-!
============================================================
Theorem 11.4.1, parts (a)-(f)

The algebraic hypotheses are now polymorphic in arbitrary
integrable functions u and v. This is essential because
part (c) applies part (a) to f and -g.
============================================================
-/

theorem theorem_11_4_1
    (I : Set ℝ)
    (Int : (ℝ → ℝ) → ℝ)
    (Integrable : (ℝ → ℝ) → Prop)
    (f g : ℝ → ℝ)

    (hf : Integrable f)
    (hg : Integrable g)

    /- Part (a) -/
    (hAddIntegrable :
      ∀ u v : ℝ → ℝ,
        Integrable u →
        Integrable v →
        Integrable (addFun u v))

    (hAdd :
      ∀ u v : ℝ → ℝ,
        Int (addFun u v) =
          Int u + Int v)

    /- Part (b) -/
    (hScalarIntegrable :
      ∀ c : ℝ,
      ∀ u : ℝ → ℝ,
        Integrable u →
        Integrable (constMulFun c u))

    (hScalar :
      ∀ c : ℝ,
      ∀ u : ℝ → ℝ,
        Int (constMulFun c u) =
          c * Int u)

    /- Part (d) -/
    (hNonneg :
      ∀ u : ℝ → ℝ,
        Integrable u →
        (∀ x ∈ I, 0 ≤ u x) →
        0 ≤ Int u)

    /- Part (f) -/
    (len : Set ℝ → ℝ)

    (hConstIntegrable :
      ∀ c : ℝ,
        Integrable (constFun c))

    (hConst :
      ∀ c : ℝ,
        Int (constFun c) =
          c * len I) :
    Integrable (addFun f g)
      ∧
    Int (addFun f g) =
      Int f + Int g
      ∧
    (∀ c : ℝ,
      Integrable (constMulFun c f)
        ∧
      Int (constMulFun c f) =
        c * Int f)
      ∧
    Integrable (subFun f g)
      ∧
    Int (subFun f g) =
      Int f - Int g
      ∧
    ((∀ x ∈ I, 0 ≤ f x) →
      0 ≤ Int f)
      ∧
    ((∀ x ∈ I, g x ≤ f x) →
      Int g ≤ Int f)
      ∧
    (∀ c : ℝ,
      Integrable (constFun c)
        ∧
      Int (constFun c) =
        c * len I) := by

  have hAddInt :
      Integrable (addFun f g) := by

    exact hAddIntegrable
      f
      g
      hf
      hg

  /-
  Integrability of -g.
  -/

  have hNegGInt :
      Integrable
        (constMulFun (-1) g) := by

    exact hScalarIntegrable
      (-1)
      g
      hg

  /-
  Integrability of f + (-g).
  -/

  have htmp :
      Integrable
        (addFun f
          (constMulFun (-1) g)) := by

    exact hAddIntegrable
      f
      (constMulFun (-1) g)
      hf
      hNegGInt

  have hfun :
      addFun f
          (constMulFun (-1) g)
        =
      subFun f g := by

    exact add_neg_eq_sub
      f
      g

  /-
  Hence f-g is integrable.
  -/

  have hSubInt :
      Integrable (subFun f g) := by

    rw [← hfun]

    exact htmp

  /-
  Integral of f-g.
  -/

  have hSub :
      Int (subFun f g) =
        Int f - Int g := by

    have haddNeg :
        Int
            (addFun f
              (constMulFun (-1) g))
          =
        Int f +
          Int (constMulFun (-1) g) := by

      exact hAdd
        f
        (constMulFun (-1) g)

    have hneg :
        Int (constMulFun (-1) g) =
          (-1 : ℝ) * Int g := by

      exact hScalar
        (-1)
        g

    exact integral_sub_of_add_neg
      Int
      f
      g
      haddNeg
      hneg

  /-
  Positivity.
  -/

  have hPos :
      (∀ x ∈ I, 0 ≤ f x) →
      0 ≤ Int f := by

    intro hpoint

    exact hNonneg
      f
      hf
      hpoint

  /-
  Monotonicity.
  -/

  have hMono :
      (∀ x ∈ I, g x ≤ f x) →
      Int g ≤ Int f := by

    intro hfg

    have hSubNonneg :
        ∀ x ∈ I,
          0 ≤ subFun f g x := by

      intro x hx

      unfold subFun

      exact sub_nonneg_of_le
        (hfg x hx)

    have hIntSubNonneg :
        0 ≤ Int (subFun f g) := by

      exact hNonneg
        (subFun f g)
        hSubInt
        hSubNonneg

    rw [hSub] at hIntSubNonneg

    linarith

  refine ⟨hAddInt, ?_⟩

  refine ⟨hAdd f g, ?_⟩

  refine ⟨?_, ?_⟩

  · intro c

    constructor

    · exact hScalarIntegrable
        c
        f
        hf

    · exact hScalar
        c
        f

  · refine ⟨hSubInt, ?_⟩

    refine ⟨hSub, ?_⟩

    refine ⟨hPos, ?_⟩

    refine ⟨hMono, ?_⟩

    intro c

    constructor

    · exact hConstIntegrable c

    · exact hConst c


/-!
============================================================
Part (g): extension by zero
============================================================
-/

theorem theorem_11_4_1_g
    (I J : Set ℝ)
    (f : ℝ → ℝ)
    (IntegrableOn :
      Set ℝ → (ℝ → ℝ) → Prop)
    (IntOn :
      Set ℝ → (ℝ → ℝ) → ℝ)
    (hIJ : I ⊆ J)
    (hf : IntegrableOn I f)
    (hZeroExtIntegrable :
      I ⊆ J →
      IntegrableOn I f →
      IntegrableOn J
        (zeroExtension I f))
    (hZeroExtIntegral :
      I ⊆ J →
      IntOn J
          (zeroExtension I f)
        =
      IntOn I f) :
    IntegrableOn J
        (zeroExtension I f)
      ∧
    IntOn J
        (zeroExtension I f)
      =
    IntOn I f := by

  constructor

  · exact hZeroExtIntegrable
      hIJ
      hf

  · exact hZeroExtIntegral
      hIJ


/-!
============================================================
Part (h): splitting an interval
============================================================
-/

theorem theorem_11_4_1_h
    (I J K : Set ℝ)
    (f : ℝ → ℝ)
    (IntegrableOn :
      Set ℝ → (ℝ → ℝ) → Prop)
    (IntOn :
      Set ℝ → (ℝ → ℝ) → ℝ)
    (hJInt :
      IntegrableOn J f)
    (hKInt :
      IntegrableOn K f)
    (hSplit :
      IntegrableOn J f →
      IntegrableOn K f →
      IntegrableOn I f
        ∧
      IntOn I f =
        IntOn J f +
        IntOn K f) :
    IntegrableOn I f
      ∧
    IntOn I f =
      IntOn J f +
        IntOn K f := by

  exact hSplit
    hJInt
    hKInt


/-!
============================================================
Exercise 11.4.1(c), isolated

This directly formalizes Tao's:
"Simply combine (a) and (b) with c = -1."
============================================================
-/

theorem exercise_11_4_1_subtraction
    (Int : (ℝ → ℝ) → ℝ)
    (Integrable : (ℝ → ℝ) → Prop)
    (f g : ℝ → ℝ)
    (hf : Integrable f)
    (hg : Integrable g)
    (hAddIntegrable :
      ∀ u v : ℝ → ℝ,
        Integrable u →
        Integrable v →
        Integrable (addFun u v))
    (hAdd :
      ∀ u v : ℝ → ℝ,
        Int (addFun u v) =
          Int u + Int v)
    (hScalarIntegrable :
      ∀ c : ℝ,
      ∀ u : ℝ → ℝ,
        Integrable u →
        Integrable (constMulFun c u))
    (hScalar :
      ∀ c : ℝ,
      ∀ u : ℝ → ℝ,
        Int (constMulFun c u) =
          c * Int u) :
    Integrable (subFun f g)
      ∧
    Int (subFun f g) =
      Int f - Int g := by

  have hneg :
      Integrable
        (constMulFun (-1) g) := by

    exact hScalarIntegrable
      (-1)
      g
      hg

  have hadd :
      Integrable
        (addFun f
          (constMulFun (-1) g)) := by

    exact hAddIntegrable
      f
      (constMulFun (-1) g)
      hf
      hneg

  have hfun :
      addFun f
          (constMulFun (-1) g)
        =
      subFun f g := by

    exact add_neg_eq_sub
      f
      g

  have hint :
      Int (subFun f g) =
        Int f - Int g := by

    calc
      Int (subFun f g)
          =
        Int
          (addFun f
            (constMulFun (-1) g)) := by

          rw [hfun]

      _ =
        Int f +
          Int (constMulFun (-1) g) := by

          exact hAdd
            f
            (constMulFun (-1) g)

      _ =
        Int f +
          (-1 : ℝ) * Int g := by

          rw [hScalar (-1) g]

      _ =
        Int f - Int g := by

          ring

  constructor

  · rw [← hfun]

    exact hadd

  · exact hint

end TaoExercise11_4_1
