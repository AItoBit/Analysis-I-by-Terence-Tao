import Mathlib

namespace TaoExercise7_1_2

/-!
============================================================
Finite-set sum
============================================================
-/

/--
The sum of a real-valued function over a finite set.
-/
noncomputable def finiteSetSum
    {α : Type*}
    (X : Finset α)
    (f : α → ℝ) : ℝ :=
  X.sum f


/--
Tao's finite interval sum over integer indices.
-/
noncomputable def taoSum
    (a : ℤ → ℝ)
    (m n : ℤ) : ℝ :=
  (Finset.Icc m n).sum a


/-!
============================================================
(a)

If X = ∅, then

    ∑_{x ∈ X} f(x) = 0.
============================================================
-/

theorem proposition_7_1_11_a
    {α : Type*}
    (f : α → ℝ) :
    finiteSetSum (∅ : Finset α) f = 0 := by

  simp [finiteSetSum]


/-!
============================================================
(b)

If X = {x₀}, then

    ∑_{x ∈ X} f(x) = f(x₀).
============================================================
-/

theorem proposition_7_1_11_b
    {α : Type*}
    [DecidableEq α]
    (f : α → ℝ)
    (x₀ : α) :
    finiteSetSum ({x₀} : Finset α) f = f x₀ := by

  simp [finiteSetSum]


/-!
============================================================
(c)

Reindexing a finite sum by a bijection.

`g` maps Y bijectively onto X.
============================================================
-/

theorem proposition_7_1_11_c
    {α β : Type*}
    [DecidableEq α]
    [DecidableEq β]
    (X : Finset α)
    (Y : Finset β)
    (F : α → ℝ)
    (g : β → α)
    (hg_mem :
      ∀ y : β,
        y ∈ Y →
        g y ∈ X)
    (hg_inj :
      Set.InjOn
        g
        (↑Y : Set β))
    (hg_surj :
      Set.SurjOn
        g
        (↑Y : Set β)
        (↑X : Set α)) :
    finiteSetSum X F
      =
    finiteSetSum Y (fun y => F (g y)) := by

  unfold finiteSetSum

  have hReindex :
      Y.sum (fun y => F (g y))
        =
      X.sum F := by

    exact Finset.sum_nbij
      (s := Y)
      (t := X)
      (f := fun y => F (g y))
      (g := F)
      g
      hg_mem
      hg_inj
      hg_surj
      (by
        intro y hy
        rfl)

  exact hReindex.symm


/-!
============================================================
(d)

For the integer interval

    X = { i : ℤ | n ≤ i ≤ m },

the interval sum agrees with the finite-set sum.
============================================================
-/

theorem proposition_7_1_11_d
    (a : ℤ → ℝ)
    (n m : ℤ) :
    taoSum a n m
      =
    finiteSetSum (Finset.Icc n m) a := by

  rfl


/-!
============================================================
(e)

If X and Y are disjoint, then

    ∑_{z ∈ X ∪ Y} f(z)
      =
    ∑_{x ∈ X} f(x) + ∑_{y ∈ Y} f(y).
============================================================
-/

theorem proposition_7_1_11_e
    {α : Type*}
    [DecidableEq α]
    (X Y : Finset α)
    (f : α → ℝ)
    (hDisjoint : Disjoint X Y) :
    finiteSetSum (X ∪ Y) f
      =
    finiteSetSum X f
      + finiteSetSum Y f := by

  unfold finiteSetSum

  exact Finset.sum_union hDisjoint


/-!
============================================================
(f)

Sum distributes over addition:

    ∑ (f(x) + g(x))
      =
    ∑ f(x) + ∑ g(x).
============================================================
-/

theorem proposition_7_1_11_f
    {α : Type*}
    [DecidableEq α]
    (X : Finset α)
    (f g : α → ℝ) :
    finiteSetSum X
        (fun x => f x + g x)
      =
    finiteSetSum X f
      + finiteSetSum X g := by

  unfold finiteSetSum

  induction X using Finset.induction_on with

  | empty =>
      simp

  | @insert x X hx ih =>
      simp [hx, ih, add_left_comm, add_comm]


/-!
============================================================
(g)

Scalar multiplication:

    ∑ c f(x)
      =
    c ∑ f(x).
============================================================
-/

theorem proposition_7_1_11_g
    {α : Type*}
    [DecidableEq α]
    (X : Finset α)
    (f : α → ℝ)
    (c : ℝ) :
    finiteSetSum X
        (fun x => c * f x)
      =
    c * finiteSetSum X f := by

  unfold finiteSetSum

  induction X using Finset.induction_on with

  | empty =>
      simp

  | @insert x X hx ih =>
      simp [hx, ih, mul_add]


/-!
============================================================
(h)

Monotonicity:

if

    f(x) ≤ g(x)

for every x ∈ X, then

    ∑ f(x) ≤ ∑ g(x).
============================================================
-/

theorem proposition_7_1_11_h
    {α : Type*}
    [DecidableEq α]
    (X : Finset α)
    (f g : α → ℝ)
    (h :
      ∀ x : α,
        x ∈ X →
        f x ≤ g x) :
    finiteSetSum X f
      ≤
    finiteSetSum X g := by

  unfold finiteSetSum

  apply Finset.sum_le_sum

  intro x hx

  exact h x hx


/-!
============================================================
(i)

Triangle inequality:

    |∑ f(x)| ≤ ∑ |f(x)|.
============================================================
-/

theorem proposition_7_1_11_i
    {α : Type*}
    [DecidableEq α]
    (X : Finset α)
    (f : α → ℝ) :
    |finiteSetSum X f|
      ≤
    finiteSetSum X
      (fun x => |f x|) := by

  unfold finiteSetSum

  induction X using Finset.induction_on with

  | empty =>
      simp

  | @insert x X hx ih =>

      simp only [Finset.sum_insert hx]

      calc
        |f x + X.sum f|
            ≤ |f x| + |X.sum f| := by
              exact abs_add_le _ _

        _ ≤
            |f x|
              + X.sum (fun y => |f y|) := by
              exact add_le_add_right ih |f x|


/-!
============================================================
Proposition 7.1.11 — a convenient packaged version
============================================================
-/

theorem proposition_7_1_11
    {α β : Type*}
    [DecidableEq α]
    [DecidableEq β]

    (X Z : Finset α)
    (Y : Finset β)

    (f gfun : α → ℝ)
    (x₀ : α)
    (c : ℝ)

    /-
    Bijection Y -> X for part (c).
    -/
    (reindex : β → α)

    (hreindex_mem :
      ∀ y : β,
        y ∈ Y →
        reindex y ∈ X)

    (hreindex_inj :
      Set.InjOn
        reindex
        (↑Y : Set β))

    (hreindex_surj :
      Set.SurjOn
        reindex
        (↑Y : Set β)
        (↑X : Set α))

    /-
    Disjointness for part (e).
    -/
    (hXZ :
      Disjoint X Z)

    /-
    Pointwise inequality for part (h).
    -/
    (hfg :
      ∀ x : α,
        x ∈ X →
        f x ≤ gfun x) :

    /- (a) -/
    finiteSetSum (∅ : Finset α) f = 0

    ∧

    /- (b) -/
    finiteSetSum ({x₀} : Finset α) f = f x₀

    ∧

    /- (c) -/
    finiteSetSum X f
      =
    finiteSetSum Y
      (fun y => f (reindex y))

    ∧

    /- (e) -/
    finiteSetSum (X ∪ Z) f
      =
    finiteSetSum X f
      + finiteSetSum Z f

    ∧

    /- (f) -/
    finiteSetSum X
        (fun x => f x + gfun x)
      =
    finiteSetSum X f
      + finiteSetSum X gfun

    ∧

    /- (g) -/
    finiteSetSum X
        (fun x => c * f x)
      =
    c * finiteSetSum X f

    ∧

    /- (h) -/
    finiteSetSum X f
      ≤
    finiteSetSum X gfun

    ∧

    /- (i) -/
    |finiteSetSum X f|
      ≤
    finiteSetSum X
      (fun x => |f x|) := by

  constructor

  · exact proposition_7_1_11_a f

  constructor

  · exact proposition_7_1_11_b f x₀

  constructor

  · exact proposition_7_1_11_c
      X
      Y
      f
      reindex
      hreindex_mem
      hreindex_inj
      hreindex_surj

  constructor

  · exact proposition_7_1_11_e
      X
      Z
      f
      hXZ

  constructor

  · exact proposition_7_1_11_f
      X
      f
      gfun

  constructor

  · exact proposition_7_1_11_g
      X
      f
      c

  constructor

  · exact proposition_7_1_11_h
      X
      f
      gfun
      hfg

  · exact proposition_7_1_11_i
      X
      f


/-!
============================================================
Exercise 7.1.2
============================================================
-/

theorem exercise_7_1_2
    {α β : Type*}
    [DecidableEq α]
    [DecidableEq β]

    (X Z : Finset α)
    (Y : Finset β)

    (f gfun : α → ℝ)
    (x₀ : α)
    (c : ℝ)

    (reindex : β → α)

    (hreindex_mem :
      ∀ y : β,
        y ∈ Y →
        reindex y ∈ X)

    (hreindex_inj :
      Set.InjOn
        reindex
        (↑Y : Set β))

    (hreindex_surj :
      Set.SurjOn
        reindex
        (↑Y : Set β)
        (↑X : Set α))

    (hXZ :
      Disjoint X Z)

    (hfg :
      ∀ x : α,
        x ∈ X →
        f x ≤ gfun x) :

    finiteSetSum (∅ : Finset α) f = 0

    ∧

    finiteSetSum ({x₀} : Finset α) f = f x₀

    ∧

    finiteSetSum X f
      =
    finiteSetSum Y
      (fun y => f (reindex y))

    ∧

    finiteSetSum (X ∪ Z) f
      =
    finiteSetSum X f
      + finiteSetSum Z f

    ∧

    finiteSetSum X
        (fun x => f x + gfun x)
      =
    finiteSetSum X f
      + finiteSetSum X gfun

    ∧

    finiteSetSum X
        (fun x => c * f x)
      =
    c * finiteSetSum X f

    ∧

    finiteSetSum X f
      ≤
    finiteSetSum X gfun

    ∧

    |finiteSetSum X f|
      ≤
    finiteSetSum X
      (fun x => |f x|) := by

  exact proposition_7_1_11
    X
    Z
    Y
    f
    gfun
    x₀
    c
    reindex
    hreindex_mem
    hreindex_inj
    hreindex_surj
    hXZ
    hfg


/-!
============================================================
Part (d), included separately because its index type is ℤ
============================================================
-/

theorem exercise_7_1_2_part_d
    (a : ℤ → ℝ)
    (n m : ℤ) :
    taoSum a n m
      =
    finiteSetSum
      (Finset.Icc n m)
      a := by

  exact proposition_7_1_11_d a n m

end TaoExercise7_1_2
