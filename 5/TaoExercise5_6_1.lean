import Mathlib

namespace TaoExercise5_6_1

/-!
Exercise 5.6.1 / Lemma 5.6.6.

We work with `NNReal = ℝ≥0`, since Tao's n-th root
is defined here for non-negative real numbers.
-/

/--
The n-th root of a non-negative real number.
-/
noncomputable def nthRoot (x : NNReal) (n : ℕ) : NNReal :=
  x ^ ((n : ℝ)⁻¹)


/-!
============================================================
(a)

If y = x^(1/n), then y^n = x.
============================================================
-/

theorem nthRoot_pow
    (x : NNReal)
    {n : ℕ}
    (hn : n ≠ 0) :
    (nthRoot x n) ^ n = x := by

  simpa [nthRoot] using
    NNReal.rpow_inv_natCast_pow x hn


/--
Version with an explicit `y`.
-/
theorem pow_eq_of_eq_nthRoot
    (x y : NNReal)
    {n : ℕ}
    (hn : n ≠ 0)
    (hy : y = nthRoot x n) :
    y ^ n = x := by

  rw [hy]

  exact nthRoot_pow x hn


/-!
============================================================
(b)

Conversely, if y^n = x, then y = x^(1/n).
============================================================
-/

/--
The identity

    (x^n)^(1/n) = x.
-/
theorem nthRoot_pow_cancel
    (x : NNReal)
    {n : ℕ}
    (hn : n ≠ 0) :
    nthRoot (x ^ n) n = x := by

  simpa [nthRoot] using
    NNReal.pow_rpow_inv_natCast x hn


theorem eq_nthRoot_of_pow_eq
    (x y : NNReal)
    {n : ℕ}
    (hn : n ≠ 0)
    (hpow : y ^ n = x) :
    y = nthRoot x n := by

  calc
    y = nthRoot (y ^ n) n := by
      symm
      exact nthRoot_pow_cancel y hn

    _ = nthRoot x n := by
      rw [hpow]


/-!
============================================================
(c)

x^(1/n) is non-negative, and it is positive iff x is positive.
============================================================
-/

/--
Every NNReal is non-negative.
-/
theorem nthRoot_nonneg
    (x : NNReal)
    (n : ℕ) :
    0 ≤ nthRoot x n := by

  exact bot_le


theorem nthRoot_pos_iff
    (x : NNReal)
    {n : ℕ}
    (hn : 0 < n) :
    0 < nthRoot x n ↔ 0 < x := by

  have hnR :
      (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn

  have hInvPos :
      (0 : ℝ) < (n : ℝ)⁻¹ := by
    exact inv_pos.mpr hnR

  have hInvNe :
      (n : ℝ)⁻¹ ≠ 0 := by
    exact ne_of_gt hInvPos

  constructor

  /-
  root > 0 -> x > 0.
  -/
  · intro hroot

    by_contra hx

    have hxzero :
        x = 0 := by
      apply le_antisymm

      · exact le_of_not_gt hx

      · exact bot_le

    subst x

    unfold nthRoot at hroot

    rw [NNReal.zero_rpow hInvNe] at hroot

    exact (lt_irrefl 0) hroot


  /-
  x > 0 -> root > 0.
  -/
  · intro hx

    unfold nthRoot

    exact NNReal.rpow_pos hx


/-!
============================================================
(d)

For n > 0,

    x > y ↔ x^(1/n) > y^(1/n).
============================================================
-/

theorem gt_iff_nthRoot_gt
    (x y : NNReal)
    {n : ℕ}
    (hn : 0 < n) :
    x > y ↔ nthRoot x n > nthRoot y n := by

  have hnR :
      (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn

  have hExp :
      (0 : ℝ) < (n : ℝ)⁻¹ := by
    exact inv_pos.mpr hnR

  constructor

  · intro hxy

    unfold nthRoot

    exact NNReal.rpow_lt_rpow hxy hExp

  · intro hroots

    unfold nthRoot at hroots

    exact
      (NNReal.rpow_lt_rpow_iff hExp).mp hroots


/-!
============================================================
(e)

Behaviour of x^(1/k) as k varies.
============================================================
-/

/--
For positive integers l < k,

    1/k < 1/l.
-/
theorem inv_natCast_lt_inv_natCast
    {k l : ℕ}
    (hl : 0 < l)
    (hlk : l < k) :
    ((k : ℝ)⁻¹) < ((l : ℝ)⁻¹) := by

  have hlR :
      (0 : ℝ) < (l : ℝ) := by
    exact_mod_cast hl

  have hlkR :
      (l : ℝ) < (k : ℝ) := by
    exact_mod_cast hlk

  simpa [one_div] using
    one_div_lt_one_div_of_lt hlR hlkR


/--
If x > 1 and l < k, then

    x^(1/k) < x^(1/l).
-/
theorem nthRoot_decreasing_of_one_lt
    (x : NNReal)
    {k l : ℕ}
    (hx : 1 < x)
    (hl : 0 < l)
    (hlk : l < k) :
    nthRoot x k < nthRoot x l := by

  have hInv :
      ((k : ℝ)⁻¹) < ((l : ℝ)⁻¹) :=
    inv_natCast_lt_inv_natCast hl hlk

  unfold nthRoot

  exact
    NNReal.rpow_lt_rpow_of_exponent_lt
      hx
      hInv


/--
If 0 < x < 1 and l < k, then

    x^(1/l) < x^(1/k).
-/
theorem nthRoot_increasing_of_lt_one
    (x : NNReal)
    {k l : ℕ}
    (hx0 : 0 < x)
    (hx1 : x < 1)
    (hl : 0 < l)
    (hlk : l < k) :
    nthRoot x l < nthRoot x k := by

  have hInv :
      ((k : ℝ)⁻¹) < ((l : ℝ)⁻¹) :=
    inv_natCast_lt_inv_natCast hl hlk

  unfold nthRoot

  exact
    NNReal.rpow_lt_rpow_of_exponent_gt
      hx0
      hx1
      hInv


/--
Every n-th root of 1 is 1.
-/
theorem nthRoot_one
    (n : ℕ) :
    nthRoot 1 n = 1 := by

  simp [nthRoot]


/-!
============================================================
(f)

(xy)^(1/n) = x^(1/n) y^(1/n).
============================================================
-/

theorem nthRoot_mul
    (x y : NNReal)
    (n : ℕ) :
    nthRoot (x * y) n =
      nthRoot x n * nthRoot y n := by

  unfold nthRoot

  exact NNReal.mul_rpow


/-!
============================================================
(g)

(x^(1/n))^(1/m) = x^(1/(nm)).
============================================================
-/

theorem nthRoot_nthRoot
    (x : NNReal)
    {n m : ℕ}
    (hn : n ≠ 0)
    (hm : m ≠ 0) :
    nthRoot (nthRoot x n) m =
      nthRoot x (n * m) := by

  have hnR :
      (n : ℝ) ≠ 0 := by
    exact_mod_cast hn

  have hmR :
      (m : ℝ) ≠ 0 := by
    exact_mod_cast hm

  have hExp :
      (n : ℝ)⁻¹ * (m : ℝ)⁻¹
        =
      ((n * m : ℕ) : ℝ)⁻¹ := by

    rw [Nat.cast_mul]

    field_simp [hnR, hmR]

  unfold nthRoot

  calc
    (x ^ (n : ℝ)⁻¹) ^ (m : ℝ)⁻¹
        =
      x ^ ((n : ℝ)⁻¹ * (m : ℝ)⁻¹) := by
        symm
        exact
          NNReal.rpow_mul
            x
            ((n : ℝ)⁻¹)
            ((m : ℝ)⁻¹)

    _ = x ^ (((n * m : ℕ) : ℝ)⁻¹) := by
          rw [hExp]


/-!
============================================================
Packaged forms of Lemma 5.6.6
============================================================
-/

/--
Parts (a)-(d) packaged together.
-/
theorem lemma_5_6_6_basic
    (x y : NNReal)
    {n : ℕ}
    (hn : 0 < n) :
    ((nthRoot x n) ^ n = x)
    ∧
    (y ^ n = x → y = nthRoot x n)
    ∧
    (0 ≤ nthRoot x n)
    ∧
    (0 < nthRoot x n ↔ 0 < x)
    ∧
    (x > y ↔ nthRoot x n > nthRoot y n) := by

  have hn0 :
      n ≠ 0 := by
    exact Nat.ne_of_gt hn

  constructor

  /-
  (a)
  -/
  · exact nthRoot_pow x hn0

  constructor

  /-
  (b)
  -/
  · intro hpow
    exact eq_nthRoot_of_pow_eq x y hn0 hpow

  constructor

  /-
  (c), non-negativity
  -/
  · exact nthRoot_nonneg x n

  constructor

  /-
  (c), positivity
  -/
  · exact nthRoot_pos_iff x hn

  /-
  (d)
  -/
  · exact gt_iff_nthRoot_gt x y hn


/--
Part (e) for x > 1.
-/
theorem lemma_5_6_6_e_gt_one
    (x : NNReal)
    {k l : ℕ}
    (hx : 1 < x)
    (hl : 0 < l)
    (hlk : l < k) :
    nthRoot x k < nthRoot x l := by

  exact nthRoot_decreasing_of_one_lt
    x hx hl hlk


/--
Part (e) for 0 < x < 1.
-/
theorem lemma_5_6_6_e_lt_one
    (x : NNReal)
    {k l : ℕ}
    (hx0 : 0 < x)
    (hx1 : x < 1)
    (hl : 0 < l)
    (hlk : l < k) :
    nthRoot x l < nthRoot x k := by

  exact nthRoot_increasing_of_lt_one
    x hx0 hx1 hl hlk


/--
Part (e) for x = 1.
-/
theorem lemma_5_6_6_e_one
    (k : ℕ) :
    nthRoot 1 k = 1 := by

  exact nthRoot_one k


/--
Part (f).
-/
theorem lemma_5_6_6_f
    (x y : NNReal)
    (n : ℕ) :
    nthRoot (x * y) n =
      nthRoot x n * nthRoot y n := by

  exact nthRoot_mul x y n


/--
Part (g).
-/
theorem lemma_5_6_6_g
    (x : NNReal)
    {n m : ℕ}
    (hn : n ≠ 0)
    (hm : m ≠ 0) :
    nthRoot (nthRoot x n) m =
      nthRoot x (n * m) := by

  exact nthRoot_nthRoot x hn hm

end TaoExercise5_6_1
