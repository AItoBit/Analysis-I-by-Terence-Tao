import Mathlib

namespace TaoExercise7_1_3

/-!
============================================================
Definitions
============================================================
-/

/--
Finite product over an integer interval:

    ∏_{i=m}^n a_i

If `n < m`, then `Finset.Icc m n` is empty and
the product is automatically `1`.
-/
noncomputable def taoProd
    (a : ℤ → ℝ)
    (m n : ℤ) : ℝ :=
  (Finset.Icc m n).prod a


/--
Finite product over a finite set.
-/
noncomputable def finiteSetProd
    {α : Type*}
    (X : Finset α)
    (f : α → ℝ) : ℝ :=
  X.prod f


/-!
============================================================
Empty interval

If n < m,

    ∏_{i=m}^n a_i = 1.
============================================================
-/

theorem taoProd_eq_one_of_lt
    (a : ℤ → ℝ)
    {m n : ℤ}
    (h : n < m) :
    taoProd a m n = 1 := by

  unfold taoProd

  have hEmpty :
      Finset.Icc m n = ∅ := by

    ext i

    simp

    omega

  simp [hEmpty]


/-!
============================================================
Analogue of Lemma 7.1.4(a)

For m ≤ n ≤ p,

    (∏_{i=m}^n a_i)
      *
    (∏_{i=n+1}^p a_i)
      =
    ∏_{i=m}^p a_i.
============================================================
-/

theorem prod_split
    (a : ℤ → ℝ)
    (m n p : ℤ)
    (hmn : m ≤ n)
    (hnp : n ≤ p) :
    taoProd a m n
      * taoProd a (n + 1) p
      =
    taoProd a m p := by

  unfold taoProd

  have hDisjoint :
      Disjoint
        (Finset.Icc m n)
        (Finset.Icc (n + 1) p) := by

    apply Finset.disjoint_left.mpr

    intro x hx₁ hx₂

    have hx₁' :
        m ≤ x ∧ x ≤ n :=
      Finset.mem_Icc.mp hx₁

    have hx₂' :
        n + 1 ≤ x ∧ x ≤ p :=
      Finset.mem_Icc.mp hx₂

    omega

  have hUnion :
      Finset.Icc m n ∪
        Finset.Icc (n + 1) p
        =
      Finset.Icc m p := by

    ext x

    simp only [
      Finset.mem_union,
      Finset.mem_Icc
    ]

    constructor

    · intro hx

      rcases hx with hx | hx

      · exact
          ⟨hx.1, le_trans hx.2 hnp⟩

      · exact
          ⟨le_trans hmn (by omega), hx.2⟩

    · intro hx

      by_cases hxn : x ≤ n

      · left
        exact ⟨hx.1, hxn⟩

      · right

        constructor

        · omega

        · exact hx.2

  calc
    (Finset.Icc m n).prod a
        *
      (Finset.Icc (n + 1) p).prod a
        =
      (Finset.Icc m n ∪
        Finset.Icc (n + 1) p).prod a := by

          symm

          exact Finset.prod_union hDisjoint

    _ =
      (Finset.Icc m p).prod a := by
        rw [hUnion]


/-!
============================================================
Analogue of Lemma 7.1.4(b)

Translation of indices.
============================================================
-/

theorem prod_shift
    (a : ℤ → ℝ)
    (m n k : ℤ)
    (_hmn : m ≤ n) :
    taoProd a m n
      =
    taoProd
      (fun j : ℤ => a (j - k))
      (m + k)
      (n + k) := by

  unfold taoProd

  let shift : ℤ → ℤ :=
    fun i => i + k

  have hInjective :
      Set.InjOn
        shift
        (↑(Finset.Icc m n) : Set ℤ) := by

    intro x hx y hy hxy

    dsimp [shift] at hxy

    omega

  have hImage :
      (Finset.Icc m n).image shift
        =
      Finset.Icc (m + k) (n + k) := by

    ext j

    constructor

    · intro hj

      rcases Finset.mem_image.mp hj with
        ⟨i, hi, hij⟩

      have hiBounds :
          m ≤ i ∧ i ≤ n :=
        Finset.mem_Icc.mp hi

      apply Finset.mem_Icc.mpr

      dsimp [shift] at hij

      subst j

      constructor <;> omega

    · intro hj

      have hjBounds :
          m + k ≤ j ∧
          j ≤ n + k :=
        Finset.mem_Icc.mp hj

      let i : ℤ := j - k

      have hi :
          i ∈ Finset.Icc m n := by

        apply Finset.mem_Icc.mpr

        dsimp [i]

        constructor <;> omega

      apply Finset.mem_image.mpr

      refine ⟨i, hi, ?_⟩

      dsimp [shift, i]

      omega

  have hProdImage :
      ((Finset.Icc m n).image shift).prod
          (fun j : ℤ => a (j - k))
        =
      (Finset.Icc m n).prod
          (fun i : ℤ => a (shift i - k)) := by

    exact Finset.prod_image hInjective

  calc
    (Finset.Icc m n).prod a
        =
      (Finset.Icc m n).prod
        (fun i : ℤ => a (shift i - k)) := by

          apply Finset.prod_congr rfl

          intro i hi

          dsimp [shift]

          congr 1

          omega

    _ =
      ((Finset.Icc m n).image shift).prod
        (fun j : ℤ => a (j - k)) := by

          exact hProdImage.symm

    _ =
      (Finset.Icc (m + k) (n + k)).prod
        (fun j : ℤ => a (j - k)) := by

          rw [hImage]


/-!
============================================================
Analogue of Lemma 7.1.4(c)

Product distributes over pointwise multiplication:

    ∏ (a_i b_i)
      =
    (∏ a_i)(∏ b_i).
============================================================
-/

theorem prod_mul
    (a b : ℤ → ℝ)
    (m n : ℤ) :
    taoProd
        (fun i : ℤ => a i * b i)
        m n
      =
    taoProd a m n
      * taoProd b m n := by

  unfold taoProd

  let s : Finset ℤ := Finset.Icc m n

  change
    s.prod (fun i : ℤ => a i * b i)
      =
    s.prod a * s.prod b

  induction s using Finset.induction_on with

  | empty =>
      simp

  | @insert x s hx ih =>
      simp [hx, ih, mul_assoc, mul_left_comm, mul_comm]


/-!
============================================================
Analogue involving scalar multiplication

For products the direct analogue

    ∏ (c a_i) = c ∏ a_i

is FALSE in general.

The correct formula is

    ∏_{x∈X} c f(x)
      =
    c^(card X) * ∏_{x∈X} f(x).
============================================================
-/

theorem finiteSetProd_const_mul
    {α : Type*}
    [DecidableEq α]
    (X : Finset α)
    (f : α → ℝ)
    (c : ℝ) :
    finiteSetProd X
        (fun x => c * f x)
      =
    c ^ X.card * finiteSetProd X f := by

  unfold finiteSetProd

  induction X using Finset.induction_on with

  | empty =>
      simp

  | @insert x X hx ih =>

      simp [hx, ih, pow_succ, mul_assoc, mul_left_comm, mul_comm]


/-!
============================================================
Absolute value

For products we get an equality, stronger than the
triangle inequality for sums:

    |∏ a_i| = ∏ |a_i|.
============================================================
-/

theorem abs_prod
    (a : ℤ → ℝ)
    (m n : ℤ) :
    |taoProd a m n|
      =
    taoProd
      (fun i : ℤ => |a i|)
      m n := by

  unfold taoProd

  let s : Finset ℤ := Finset.Icc m n

  change
    |s.prod a|
      =
    s.prod (fun i : ℤ => |a i|)

  induction s using Finset.induction_on with

  | empty =>
      simp

  | @insert x s hx ih =>

      simp only [Finset.prod_insert hx]

      rw [abs_mul, ih]


/-!
============================================================
Product monotonicity DOES NOT hold without sign assumptions.

A correct version:

if

    0 ≤ a_i ≤ b_i

for every index, then

    ∏ a_i ≤ ∏ b_i.
============================================================
-/

theorem finiteSetProd_mono_nonneg
    {α : Type*}
    [DecidableEq α]
    (X : Finset α)
    (a b : α → ℝ)
    (ha :
      ∀ x : α,
        x ∈ X →
        0 ≤ a x)
    (hab :
      ∀ x : α,
        x ∈ X →
        a x ≤ b x) :
    finiteSetProd X a
      ≤
    finiteSetProd X b := by

  unfold finiteSetProd

  induction X using Finset.induction_on with

  | empty =>
      simp

  | @insert x X hx ih =>

      have hax :
          0 ≤ a x := by
        exact ha x (by simp)

      have haxb :
          a x ≤ b x := by
        exact hab x (by simp)

      have hbx :
          0 ≤ b x := by
        exact le_trans hax haxb

      have haX :
          ∀ y : α,
            y ∈ X →
            0 ≤ a y := by

        intro y hy

        exact ha y (by
          simp [hy])

      have habX :
          ∀ y : α,
            y ∈ X →
            a y ≤ b y := by

        intro y hy

        exact hab y (by
          simp [hy])

      have ih' :
          X.prod a ≤ X.prod b := by
        exact ih haX habX

      have hprodA :
          0 ≤ X.prod a := by

        apply Finset.prod_nonneg

        intro y hy

        exact haX y hy

      rw [
        Finset.prod_insert hx,
        Finset.prod_insert hx
      ]

      exact mul_le_mul
        haxb
        ih'
        hprodA
        hbx


/-!
============================================================
Finite-set product:
empty set
============================================================
-/

theorem finiteSetProd_empty
    {α : Type*}
    (f : α → ℝ) :
    finiteSetProd
      (∅ : Finset α)
      f
      =
    1 := by

  simp [finiteSetProd]


/-!
============================================================
Finite-set product:
singleton
============================================================
-/

theorem finiteSetProd_singleton
    {α : Type*}
    [DecidableEq α]
    (f : α → ℝ)
    (x : α) :
    finiteSetProd
      ({x} : Finset α)
      f
      =
    f x := by

  simp [finiteSetProd]


/-!
============================================================
Finite-set product:
disjoint union
============================================================
-/

theorem finiteSetProd_union
    {α : Type*}
    [DecidableEq α]
    (X Y : Finset α)
    (f : α → ℝ)
    (hXY : Disjoint X Y) :
    finiteSetProd (X ∪ Y) f
      =
    finiteSetProd X f
      *
    finiteSetProd Y f := by

  unfold finiteSetProd

  exact Finset.prod_union hXY


/-!
============================================================
Finite-set product:
pointwise multiplication
============================================================
-/

theorem finiteSetProd_mul
    {α : Type*}
    [DecidableEq α]
    (X : Finset α)
    (f g : α → ℝ) :
    finiteSetProd X
        (fun x => f x * g x)
      =
    finiteSetProd X f
      *
    finiteSetProd X g := by

  unfold finiteSetProd

  induction X using Finset.induction_on with

  | empty =>
      simp

  | @insert x X hx ih =>
      simp [hx, ih, mul_assoc, mul_left_comm, mul_comm]


/-!
============================================================
Finite-set product:
absolute value
============================================================
-/

theorem finiteSetProd_abs
    {α : Type*}
    [DecidableEq α]
    (X : Finset α)
    (f : α → ℝ) :
    |finiteSetProd X f|
      =
    finiteSetProd X
      (fun x => |f x|) := by

  unfold finiteSetProd

  induction X using Finset.induction_on with

  | empty =>
      simp

  | @insert x X hx ih =>

      simp only [Finset.prod_insert hx]

      rw [abs_mul, ih]


/-!
============================================================
Summary theorem for Exercise 7.1.3
============================================================
-/

theorem exercise_7_1_3
    {α : Type*}
    [DecidableEq α]
    (X Y : Finset α)
    (f g : α → ℝ)
    (c : ℝ)
    (hXY : Disjoint X Y) :
    finiteSetProd (∅ : Finset α) f = 1
    ∧
    (∀ x : α,
      finiteSetProd ({x} : Finset α) f = f x)
    ∧
    finiteSetProd (X ∪ Y) f
      =
      finiteSetProd X f * finiteSetProd Y f
    ∧
    finiteSetProd X (fun x => f x * g x)
      =
      finiteSetProd X f * finiteSetProd X g
    ∧
    finiteSetProd X (fun x => c * f x)
      =
      c ^ X.card * finiteSetProd X f
    ∧
    |finiteSetProd X f|
      =
      finiteSetProd X (fun x => |f x|) := by

  constructor

  · exact finiteSetProd_empty f

  constructor

  · intro x
    exact finiteSetProd_singleton f x

  constructor

  · exact finiteSetProd_union
      X Y f hXY

  constructor

  · exact finiteSetProd_mul
      X f g

  constructor

  · exact finiteSetProd_const_mul
      X f c

  · exact finiteSetProd_abs
      X f

end TaoExercise7_1_3
