import Mathlib

namespace TaoExercise7_1_1

/-!
============================================================
Definition of Tao's finite sum
============================================================
-/

/--
`taoSum a m n` represents

    a_m + a_{m+1} + ... + a_n.

If `n < m`, then `Finset.Icc m n` is empty,
hence the sum is zero.
-/
noncomputable def taoSum
    (a : ℤ → ℝ)
    (m n : ℤ) : ℝ :=
  (Finset.Icc m n).sum a


/-!
============================================================
(a)

For m ≤ n ≤ p,

    sum(m,n) + sum(n+1,p) = sum(m,p).
============================================================
-/

theorem lemma_7_1_4_a
    (a : ℤ → ℝ)
    (m n p : ℤ)
    (hmn : m ≤ n)
    (hnp : n ≤ p) :
    taoSum a m n
      + taoSum a (n + 1) p
      =
    taoSum a m p := by

  unfold taoSum

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

      · constructor
        · exact hx.1
        · exact le_trans hx.2 hnp

      · constructor
        · exact le_trans hmn (by omega)
        · exact hx.2

    · intro hx

      by_cases hxn : x ≤ n

      · left
        exact ⟨hx.1, hxn⟩

      · right

        constructor

        · omega

        · exact hx.2

  calc
    (Finset.Icc m n).sum a
        +
      (Finset.Icc (n + 1) p).sum a
        =
      (Finset.Icc m n ∪
        Finset.Icc (n + 1) p).sum a := by

          symm
          exact Finset.sum_union hDisjoint

    _ =
      (Finset.Icc m p).sum a := by
        rw [hUnion]


/-!
============================================================
(b)

For any integer k,

    sum_{i=m}^n a_i
      =
    sum_{j=m+k}^{n+k} a_{j-k}.
============================================================
-/

theorem lemma_7_1_4_b
    (a : ℤ → ℝ)
    (m n k : ℤ)
    (_hmn : m ≤ n) :
    taoSum a m n
      =
    taoSum
      (fun j : ℤ => a (j - k))
      (m + k)
      (n + k) := by

  unfold taoSum

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

  have hSumImage :
      ((Finset.Icc m n).image shift).sum
          (fun j : ℤ => a (j - k))
        =
      (Finset.Icc m n).sum
          (fun i : ℤ => a (shift i - k)) := by

    exact Finset.sum_image hInjective

  calc
    (Finset.Icc m n).sum a
        =
      (Finset.Icc m n).sum
        (fun i : ℤ => a (shift i - k)) := by

          apply Finset.sum_congr rfl

          intro i hi

          dsimp [shift]

          congr 1

          omega

    _ =
      ((Finset.Icc m n).image shift).sum
        (fun j : ℤ => a (j - k)) := by

          exact hSumImage.symm

    _ =
      (Finset.Icc (m + k) (n + k)).sum
        (fun j : ℤ => a (j - k)) := by

          rw [hImage]


/-!
============================================================
(c)

    sum (a_i + b_i)
      =
    sum a_i + sum b_i.
============================================================
-/

theorem lemma_7_1_4_c
    (a b : ℤ → ℝ)
    (m n : ℤ)
    (_hmn : m ≤ n) :
    taoSum
        (fun i : ℤ => a i + b i)
        m n
      =
    taoSum a m n
      + taoSum b m n := by

  unfold taoSum

  let s : Finset ℤ := Finset.Icc m n

  change
    s.sum (fun i : ℤ => a i + b i)
      =
    s.sum a + s.sum b

  induction s using Finset.induction_on with

  | empty =>
      simp

  | @insert x s hx ih =>
      simp [hx, ih, add_left_comm, add_comm]


/-!
============================================================
(d)

    sum (c * a_i)
      =
    c * sum a_i.
============================================================
-/

theorem lemma_7_1_4_d
    (a : ℤ → ℝ)
    (c : ℝ)
    (m n : ℤ)
    (_hmn : m ≤ n) :
    taoSum
        (fun i : ℤ => c * a i)
        m n
      =
    c * taoSum a m n := by

  unfold taoSum

  let s : Finset ℤ := Finset.Icc m n

  change
    s.sum (fun i : ℤ => c * a i)
      =
    c * s.sum a

  induction s using Finset.induction_on with

  | empty =>
      simp

  | @insert x s hx ih =>
      simp [hx, ih, mul_add]


/-!
============================================================
(e)

Triangle inequality:

    |sum a_i| ≤ sum |a_i|.
============================================================
-/

theorem lemma_7_1_4_e
    (a : ℤ → ℝ)
    (m n : ℤ)
    (_hmn : m ≤ n) :
    |taoSum a m n|
      ≤
    taoSum
      (fun i : ℤ => |a i|)
      m n := by

  unfold taoSum

  let s : Finset ℤ := Finset.Icc m n

  change
    |s.sum a|
      ≤
    s.sum (fun i : ℤ => |a i|)

  induction s using Finset.induction_on with

  | empty =>
      simp

  | @insert x s hx ih =>

      simp only [Finset.sum_insert hx]

      calc
        |a x + s.sum a|
            ≤ |a x| + |s.sum a| := by
              exact abs_add_le _ _

        _ ≤
            |a x| + s.sum (fun i : ℤ => |a i|) := by
              exact add_le_add_right ih |a x|


/-!
============================================================
(f)

If

    a_i ≤ b_i

for every m ≤ i ≤ n, then

    sum a_i ≤ sum b_i.
============================================================
-/

theorem lemma_7_1_4_f
    (a b : ℤ → ℝ)
    (m n : ℤ)
    (_hmn : m ≤ n)
    (h :
      ∀ i : ℤ,
        m ≤ i →
        i ≤ n →
        a i ≤ b i) :
    taoSum a m n
      ≤
    taoSum b m n := by

  unfold taoSum

  apply Finset.sum_le_sum

  intro i hi

  have hiBounds :
      m ≤ i ∧ i ≤ n :=
    Finset.mem_Icc.mp hi

  exact h
    i
    hiBounds.1
    hiBounds.2


/-!
============================================================
Lemma 7.1.4 packaged
============================================================
-/

theorem lemma_7_1_4
    (a b : ℤ → ℝ)
    (m n p k : ℤ)
    (c : ℝ)
    (hmn : m ≤ n)
    (hnp : n ≤ p)
    (hab :
      ∀ i : ℤ,
        m ≤ i →
        i ≤ n →
        a i ≤ b i) :
    (
      taoSum a m n
        + taoSum a (n + 1) p
        =
      taoSum a m p
    )
    ∧
    (
      taoSum a m n
        =
      taoSum
        (fun j : ℤ => a (j - k))
        (m + k)
        (n + k)
    )
    ∧
    (
      taoSum
        (fun i : ℤ => a i + b i)
        m n
        =
      taoSum a m n
        + taoSum b m n
    )
    ∧
    (
      taoSum
        (fun i : ℤ => c * a i)
        m n
        =
      c * taoSum a m n
    )
    ∧
    (
      |taoSum a m n|
        ≤
      taoSum
        (fun i : ℤ => |a i|)
        m n
    )
    ∧
    (
      taoSum a m n
        ≤
      taoSum b m n
    ) := by

  constructor

  · exact lemma_7_1_4_a
      a
      m
      n
      p
      hmn
      hnp

  constructor

  · exact lemma_7_1_4_b
      a
      m
      n
      k
      hmn

  constructor

  · exact lemma_7_1_4_c
      a
      b
      m
      n
      hmn

  constructor

  · exact lemma_7_1_4_d
      a
      c
      m
      n
      hmn

  constructor

  · exact lemma_7_1_4_e
      a
      m
      n
      hmn

  · exact lemma_7_1_4_f
      a
      b
      m
      n
      hmn
      hab


/-!
============================================================
Exercise 7.1.1
============================================================
-/

theorem exercise_7_1_1
    (a b : ℤ → ℝ)
    (m n p k : ℤ)
    (c : ℝ)
    (hmn : m ≤ n)
    (hnp : n ≤ p)
    (hab :
      ∀ i : ℤ,
        m ≤ i →
        i ≤ n →
        a i ≤ b i) :
    (
      taoSum a m n
        + taoSum a (n + 1) p
        =
      taoSum a m p
    )
    ∧
    (
      taoSum a m n
        =
      taoSum
        (fun j : ℤ => a (j - k))
        (m + k)
        (n + k)
    )
    ∧
    (
      taoSum
        (fun i : ℤ => a i + b i)
        m n
        =
      taoSum a m n
        + taoSum b m n
    )
    ∧
    (
      taoSum
        (fun i : ℤ => c * a i)
        m n
        =
      c * taoSum a m n
    )
    ∧
    (
      |taoSum a m n|
        ≤
      taoSum
        (fun i : ℤ => |a i|)
        m n
    )
    ∧
    (
      taoSum a m n
        ≤
      taoSum b m n
    ) := by

  exact lemma_7_1_4
    a
    b
    m
    n
    p
    k
    c
    hmn
    hnp
    hab

end TaoExercise7_1_1
