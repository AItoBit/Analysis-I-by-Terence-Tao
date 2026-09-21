import Mathlib

namespace TaoExercise4_1_7

/-
The pair (a,b) represents the integer a - b.
-/
structure RawInt where
  pos : ℕ
  neg : ℕ


/--
Equality of integer representatives:

    (a,b) = (c,d)  iff  a + d = c + b.
-/
def IntEq (x y : RawInt) : Prop :=
  x.pos + y.neg = y.pos + x.neg


/--
Addition:

    (a-b) + (c-d) = (a+c) - (b+d).
-/
def rawAdd (x y : RawInt) : RawInt :=
  ⟨x.pos + y.pos, x.neg + y.neg⟩


/--
Negation:

    -(a-b) = b-a.
-/
def rawNeg (x : RawInt) : RawInt :=
  ⟨x.neg, x.pos⟩


/--
Subtraction.
-/
def rawSub (x y : RawInt) : RawInt :=
  rawAdd x (rawNeg y)


/--
Multiplication:

    (a-b)(c-d)
      = (ac + bd) - (ad + bc).
-/
def rawMul (x y : RawInt) : RawInt :=
  ⟨x.pos * y.pos + x.neg * y.neg,
   x.pos * y.neg + x.neg * y.pos⟩


/--
Zero integer.
-/
def zeroInt : RawInt :=
  ⟨0, 0⟩


/--
Interpret a raw integer as a Mathlib integer.
-/
def value (x : RawInt) : ℤ :=
  (x.pos : ℤ) - (x.neg : ℤ)


/--
A raw integer is positive iff its represented value is positive.
-/
def IntPos (x : RawInt) : Prop :=
  0 < value x


/--
Strict order:

    x > y
-/
def IntGt (x y : RawInt) : Prop :=
  value y < value x


/-
Basic compatibility lemmas.
-/

theorem intEq_iff_value_eq
    (x y : RawInt) :
    IntEq x y ↔ value x = value y := by
  unfold IntEq value
  constructor
  · intro h
    omega
  · intro h
    omega


theorem value_zeroInt :
    value zeroInt = 0 := by
  simp [value, zeroInt]


theorem value_rawAdd
    (x y : RawInt) :
    value (rawAdd x y) = value x + value y := by
  unfold value rawAdd
  push_cast
  ring


theorem value_rawNeg
    (x : RawInt) :
    value (rawNeg x) = -value x := by
  unfold value rawNeg
  push_cast
  ring


theorem value_rawSub
    (x y : RawInt) :
    value (rawSub x y) = value x - value y := by
  unfold rawSub
  rw [value_rawAdd, value_rawNeg]
  ring


theorem value_rawMul
    (x y : RawInt) :
    value (rawMul x y) = value x * value y := by
  unfold value rawMul
  push_cast
  ring


/-
(a)

a > b iff a - b is positive.
-/

theorem gt_iff_sub_pos
    (a b : RawInt) :
    IntGt a b ↔ IntPos (rawSub a b) := by
  unfold IntGt IntPos
  rw [value_rawSub]
  exact sub_pos.symm


/-
(b)

Addition preserves order:

    a > b -> a + c > b + c.
-/

theorem add_preserves_order
    (a b c : RawInt)
    (h : IntGt a b) :
    IntGt (rawAdd a c) (rawAdd b c) := by
  unfold IntGt at h ⊢
  rw [value_rawAdd, value_rawAdd]
  simpa [add_comm] using add_lt_add_right h (value c)


/-
(c)

Positive multiplication preserves order:

    a > b ->
    c > 0 ->
    ac > bc.
-/

theorem positive_mul_preserves_order
    (a b c : RawInt)
    (hab : IntGt a b)
    (hc : IntPos c) :
    IntGt (rawMul a c) (rawMul b c) := by
  unfold IntGt at hab ⊢
  unfold IntPos at hc
  rw [value_rawMul, value_rawMul]
  exact mul_lt_mul_of_pos_right hab hc


/-
(d)

Negation reverses order:

    a > b -> -a < -b.

Since `IntGt x y` means x > y,
this is:

    IntGt (rawNeg b) (rawNeg a)
-/

theorem neg_reverses_order
    (a b : RawInt)
    (h : IntGt a b) :
    IntGt (rawNeg b) (rawNeg a) := by
  unfold IntGt at h ⊢
  rw [value_rawNeg, value_rawNeg]
  exact neg_lt_neg h


/-
(e)

Order is transitive:

    a > b ->
    b > c ->
    a > c.
-/

theorem order_trans
    (a b c : RawInt)
    (hab : IntGt a b)
    (hbc : IntGt b c) :
    IntGt a c := by
  unfold IntGt at hab hbc ⊢
  exact lt_trans hbc hab


/-
(f)

Trichotomy:

at least one of

    a > b,
    b > a,
    a = b

holds.
-/

theorem order_trichotomy
    (a b : RawInt) :
    IntGt a b ∨
    IntGt b a ∨
    IntEq a b := by

  rcases lt_trichotomy (value a) (value b) with hab | heq | hba

  · right
    left
    exact hab

  · right
    right
    exact (intEq_iff_value_eq a b).mpr heq

  · left
    exact hba


/-
The two strict inequalities cannot both hold.
-/

theorem not_gt_and_reverse_gt
    (a b : RawInt) :
    ¬ (IntGt a b ∧ IntGt b a) := by
  rintro ⟨hab, hba⟩
  unfold IntGt at hab hba
  exact (lt_asymm hab hba)


/-
If a > b then a != b.
-/

theorem gt_ne_eq
    (a b : RawInt)
    (h : IntGt a b) :
    ¬ IntEq a b := by
  intro heq

  have hEqValue :
      value a = value b :=
    (intEq_iff_value_eq a b).mp heq

  unfold IntGt at h
  omega


/-
Full exact trichotomy.

Exactly one of

    a > b,
    b > a,
    a = b

holds.
-/

theorem order_trichotomy_exact
    (a b : RawInt) :
    (IntGt a b ∧
      ¬ IntGt b a ∧
      ¬ IntEq a b)
    ∨
    (IntGt b a ∧
      ¬ IntGt a b ∧
      ¬ IntEq a b)
    ∨
    (IntEq a b ∧
      ¬ IntGt a b ∧
      ¬ IntGt b a) := by

  rcases lt_trichotomy (value a) (value b) with hab | heq | hba

  /-
  Case value a < value b:
  therefore b > a.
  -/
  · right
    left

    constructor
    · exact hab

    constructor
    · unfold IntGt
      exact not_lt_of_ge (le_of_lt hab)

    · intro hEq
      have hv :
          value a = value b :=
        (intEq_iff_value_eq a b).mp hEq
      omega

  /-
  Case value a = value b.
  -/
  · right
    right

    constructor
    · exact (intEq_iff_value_eq a b).mpr heq

    constructor
    · unfold IntGt
      omega

    · unfold IntGt
      omega

  /-
  Case value b < value a:
  therefore a > b.
  -/
  · left

    constructor
    · exact hba

    constructor
    · unfold IntGt
      exact not_lt_of_ge (le_of_lt hba)

    · intro hEq
      have hv :
          value a = value b :=
        (intEq_iff_value_eq a b).mp hEq
      omega


/--
Lemma 4.1.11 packaged together.
-/
theorem lemma_4_1_11
    (a b c : RawInt) :
    (IntGt a b ↔ IntPos (rawSub a b))
    ∧
    (IntGt a b →
      IntGt (rawAdd a c) (rawAdd b c))
    ∧
    (IntGt a b →
      IntPos c →
      IntGt (rawMul a c) (rawMul b c))
    ∧
    (IntGt a b →
      IntGt (rawNeg b) (rawNeg a))
    ∧
    (∀ d : RawInt,
      IntGt a b →
      IntGt b d →
      IntGt a d)
    ∧
    (IntGt a b ∨ IntGt b a ∨ IntEq a b) := by

  constructor
  · exact gt_iff_sub_pos a b

  constructor
  · intro hab
    exact add_preserves_order a b c hab

  constructor
  · intro hab hc
    exact positive_mul_preserves_order a b c hab hc

  constructor
  · intro hab
    exact neg_reverses_order a b hab

  constructor
  · intro d hab hbd
    exact order_trans a b d hab hbd

  · exact order_trichotomy a b

end TaoExercise4_1_7
