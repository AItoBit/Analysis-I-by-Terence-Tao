import Mathlib

namespace TaoExercise5_6_2

/-!
Exercise 5.6.2 / Lemma 5.6.9.

For x > 0 and q ∈ ℚ, Tao's rational power x^q
is represented using NNReal.rpow with q cast to ℝ.
-/

noncomputable def ratPow
    (x : NNReal)
    (q : ℚ) : NNReal :=
  x ^ (q : ℝ)


/-!
============================================================
(a)

x^q is positive.
============================================================
-/

theorem ratPow_pos
    (x : NNReal)
    (q : ℚ)
    (hx : 0 < x) :
    0 < ratPow x q := by

  unfold ratPow

  exact NNReal.rpow_pos hx


/-!
============================================================
(b1)

x^(q+r) = x^q * x^r.
============================================================
-/

theorem ratPow_add
    (x : NNReal)
    (q r : ℚ)
    (hx : 0 < x) :
    ratPow x (q + r) =
      ratPow x q * ratPow x r := by

  unfold ratPow

  push_cast

  exact NNReal.rpow_add
    (ne_of_gt hx)
    (q : ℝ)
    (r : ℝ)


/-!
============================================================
(b2)

(x^q)^r = x^(qr).
============================================================
-/

theorem ratPow_mul_exponent
    (x : NNReal)
    (q r : ℚ) :
    ratPow (ratPow x q) r =
      ratPow x (q * r) := by

  unfold ratPow

  push_cast

  exact
    (NNReal.rpow_mul
      x
      (q : ℝ)
      (r : ℝ)).symm


/-!
============================================================
(c)

x^(-q) = 1 / x^q.
============================================================
-/

theorem ratPow_neg
    (x : NNReal)
    (q : ℚ) :
    ratPow x (-q) =
      1 / ratPow x q := by

  unfold ratPow

  push_cast

  rw [NNReal.rpow_neg]

  simp


/-!
Equivalent inverse formulation.
-/

theorem ratPow_neg_inv
    (x : NNReal)
    (q : ℚ) :
    ratPow x (-q) =
      (ratPow x q)⁻¹ := by

  unfold ratPow

  push_cast

  exact NNReal.rpow_neg x (q : ℝ)


/-!
============================================================
(d)

If q > 0, then

    x > y ↔ x^q > y^q.
============================================================
-/

theorem gt_iff_ratPow_gt
    (x y : NNReal)
    (q : ℚ)
    (hq : 0 < q) :
    x > y ↔
      ratPow x q > ratPow y q := by

  have hqR :
      (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast hq

  unfold ratPow

  constructor

  · intro hxy

    exact NNReal.rpow_lt_rpow
      hxy
      hqR

  · intro hxy

    exact
      (NNReal.rpow_lt_rpow_iff hqR).mp hxy


/-!
A version written with `<`.
-/

theorem ratPow_lt_ratPow_iff
    (x y : NNReal)
    (q : ℚ)
    (hq : 0 < q) :
    ratPow x q < ratPow y q ↔ x < y := by

  have hqR :
      (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast hq

  unfold ratPow

  exact NNReal.rpow_lt_rpow_iff hqR


/-!
============================================================
(e1)

If x > 1, then

    x^q > x^r ↔ q > r.
============================================================
-/

theorem ratPow_gt_iff_exponent_gt
    (x : NNReal)
    (q r : ℚ)
    (hx : 1 < x) :
    ratPow x q > ratPow x r ↔
      q > r := by

  constructor

  /-
  x^q > x^r -> q > r.
  -/
  · intro hp

    by_contra hqr

    have hqrQ :
        q ≤ r := by
      exact le_of_not_gt hqr

    have hqrR :
        (q : ℝ) ≤ (r : ℝ) := by
      exact_mod_cast hqrQ

    have hpow :
        ratPow x q ≤ ratPow x r := by
      unfold ratPow

      exact
        NNReal.rpow_le_rpow_of_exponent_le
          (le_of_lt hx)
          hqrR

    exact (not_lt_of_ge hpow) hp

  /-
  q > r -> x^q > x^r.
  -/
  · intro hqr

    have hqrR :
        (r : ℝ) < (q : ℝ) := by
      exact_mod_cast hqr

    unfold ratPow

    exact
      NNReal.rpow_lt_rpow_of_exponent_lt
        hx
        hqrR


/-!
============================================================
(e2)

If 0 < x < 1, then

    x^q > x^r ↔ q < r.
============================================================
-/

theorem ratPow_gt_iff_exponent_lt
    (x : NNReal)
    (q r : ℚ)
    (hx0 : 0 < x)
    (hx1 : x < 1) :
    ratPow x q > ratPow x r ↔
      q < r := by

  constructor

  /-
  x^q > x^r -> q < r.
  -/
  · intro hp

    by_contra hqr

    have hrqQ :
        r ≤ q := by
      exact le_of_not_gt hqr

    have hrqR :
        (r : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast hrqQ

    have hpow :
        ratPow x q ≤ ratPow x r := by
      unfold ratPow

      exact
        NNReal.rpow_le_rpow_of_exponent_ge
          hx0
          (le_of_lt hx1)
          hrqR

    exact (not_lt_of_ge hpow) hp

  /-
  q < r -> x^q > x^r.
  -/
  · intro hqr

    have hqrR :
        (q : ℝ) < (r : ℝ) := by
      exact_mod_cast hqr

    unfold ratPow

    exact
      NNReal.rpow_lt_rpow_of_exponent_gt
        hx0
        hx1
        hqrR


/-!
============================================================
(e3)

If x = 1, then x^q = 1 for every rational q.
============================================================
-/

theorem one_ratPow
    (q : ℚ) :
    ratPow 1 q = 1 := by

  unfold ratPow

  exact NNReal.one_rpow (q : ℝ)


/-!
============================================================
(f)

(xy)^q = x^q y^q.
============================================================
-/

theorem mul_ratPow
    (x y : NNReal)
    (q : ℚ) :
    ratPow (x * y) q =
      ratPow x q * ratPow y q := by

  unfold ratPow

  exact NNReal.mul_rpow


/-!
============================================================
Additional useful identities
============================================================
-/

/--
x^0 = 1.
-/
theorem ratPow_zero
    (x : NNReal) :
    ratPow x 0 = 1 := by

  unfold ratPow

  norm_num


/--
x^1 = x.
-/
theorem ratPow_one
    (x : NNReal) :
    ratPow x 1 = x := by

  unfold ratPow

  norm_num


/--
If x > 0 then x^q ≠ 0.
-/
theorem ratPow_ne_zero
    (x : NNReal)
    (q : ℚ)
    (hx : 0 < x) :
    ratPow x q ≠ 0 := by

  exact ne_of_gt (ratPow_pos x q hx)


/-!
============================================================
Lemma 5.6.9 packaged
============================================================
-/

theorem lemma_5_6_9
    (x y : NNReal)
    (q r : ℚ)
    (hx : 0 < x)
    (hy : 0 < y)
    (hq : 0 < q) :
    (0 < ratPow x q)
    ∧
    (ratPow x (q + r) =
      ratPow x q * ratPow x r)
    ∧
    (ratPow (ratPow x q) r =
      ratPow x (q * r))
    ∧
    (ratPow x (-q) =
      1 / ratPow x q)
    ∧
    (x > y ↔
      ratPow x q > ratPow y q)
    ∧
    (ratPow (x * y) q =
      ratPow x q * ratPow y q) := by

  constructor

  /-
  (a)
  -/
  · exact ratPow_pos x q hx

  constructor

  /-
  (b), addition of exponents
  -/
  · exact ratPow_add x q r hx

  constructor

  /-
  (b), multiplication of exponents
  -/
  · exact ratPow_mul_exponent x q r

  constructor

  /-
  (c)
  -/
  · exact ratPow_neg x q

  constructor

  /-
  (d)
  -/
  · exact gt_iff_ratPow_gt
      x y q hq

  /-
  (f)
  -/
  · exact mul_ratPow
      x y q


/-!
============================================================
Part (e) packaged separately because it has three cases.
============================================================
-/

theorem lemma_5_6_9_e_gt_one
    (x : NNReal)
    (q r : ℚ)
    (hx : 1 < x) :
    ratPow x q > ratPow x r ↔
      q > r := by

  exact ratPow_gt_iff_exponent_gt
    x q r hx


theorem lemma_5_6_9_e_lt_one
    (x : NNReal)
    (q r : ℚ)
    (hx0 : 0 < x)
    (hx1 : x < 1) :
    ratPow x q > ratPow x r ↔
      q < r := by

  exact ratPow_gt_iff_exponent_lt
    x q r hx0 hx1


theorem lemma_5_6_9_e_one
    (q : ℚ) :
    ratPow 1 q = 1 := by

  exact one_ratPow q

end TaoExercise5_6_2
