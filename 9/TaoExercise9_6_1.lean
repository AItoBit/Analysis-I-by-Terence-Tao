import Mathlib

namespace TaoExercise9_6_1

open Set

def IsBoundedFunction {α : Type*} (f : α → ℝ) : Prop :=
  ∃ M : ℝ, 0 < M ∧ ∀ x : α, abs (f x) ≤ M

def AttainsMinimum {α : Type*} (f : α → ℝ) : Prop :=
  ∃ x : α, ∀ y : α, f x ≤ f y

def AttainsMaximum {α : Type*} (f : α → ℝ) : Prop :=
  ∃ x : α, ∀ y : α, f y ≤ f x

def HasNoMinimum {α : Type*} (f : α → ℝ) : Prop :=
  ∀ x : α, ∃ y : α, f y < f x

def HasNoMaximum {α : Type*} (f : α → ℝ) : Prop :=
  ∀ x : α, ∃ y : α, f x < f y

def HasNoUpperBound {α : Type*} (f : α → ℝ) : Prop :=
  ∀ M : ℝ, ∃ x : α, M < f x

def HasNoLowerBound {α : Type*} (f : α → ℝ) : Prop :=
  ∀ M : ℝ, ∃ x : α, f x < M


/-!
============================================================
(a)
============================================================
-/

noncomputable def fA :
    Set.Ioo (1 : ℝ) 2 → ℝ :=
  fun x => abs ((x : ℝ) - 3 / 2)


theorem fA_continuous :
    Continuous fA := by
  unfold fA
  fun_prop


theorem fA_bounded :
    IsBoundedFunction fA := by
  refine ⟨1, by norm_num, ?_⟩

  intro x

  change abs (abs ((x : ℝ) - 3 / 2)) ≤ 1

  rw [abs_abs]

  apply abs_le.mpr

  constructor
  · linarith [x.property.1]
  · linarith [x.property.2]


theorem fA_attains_minimum :
    AttainsMinimum fA := by

  let x₀ : Set.Ioo (1 : ℝ) 2 :=
    ⟨3 / 2, by
      constructor <;> norm_num⟩

  refine ⟨x₀, ?_⟩

  intro y

  have hx₀ :
      fA x₀ = 0 := by
    norm_num [fA, x₀]

  rw [hx₀]

  exact abs_nonneg _


theorem fA_has_no_maximum :
    HasNoMaximum fA := by

  intro x

  by_cases hx :
      (3 / 2 : ℝ) ≤ (x : ℝ)

  · let yval : ℝ :=
      ((x : ℝ) + 2) / 2

    have hy1 :
        1 < yval := by
      dsimp [yval]
      linarith [x.property.1]

    have hy2 :
        yval < 2 := by
      dsimp [yval]
      linarith [x.property.2]

    let y : Set.Ioo (1 : ℝ) 2 :=
      ⟨yval, hy1, hy2⟩

    refine ⟨y, ?_⟩

    have hxnonneg :
        0 ≤ (x : ℝ) - 3 / 2 := by
      linarith

    have hygt :
        (x : ℝ) < (y : ℝ) := by
      dsimp [y, yval]
      linarith [x.property.2]

    have hynonneg :
        0 ≤ (y : ℝ) - 3 / 2 := by
      linarith

    change
      abs ((x : ℝ) - 3 / 2) <
        abs ((y : ℝ) - 3 / 2)

    rw [abs_of_nonneg hxnonneg]
    rw [abs_of_nonneg hynonneg]

    linarith

  · have hxlt :
        (x : ℝ) < 3 / 2 := by
      exact lt_of_not_ge hx

    let yval : ℝ :=
      (1 + (x : ℝ)) / 2

    have hy1 :
        1 < yval := by
      dsimp [yval]
      linarith [x.property.1]

    have hy2 :
        yval < 2 := by
      dsimp [yval]
      linarith [x.property.2]

    let y : Set.Ioo (1 : ℝ) 2 :=
      ⟨yval, hy1, hy2⟩

    refine ⟨y, ?_⟩

    have hylt :
        (y : ℝ) < (x : ℝ) := by
      dsimp [y, yval]
      linarith [x.property.1]

    have hxnonpos :
        (x : ℝ) - 3 / 2 ≤ 0 := by
      linarith

    have hynonpos :
        (y : ℝ) - 3 / 2 ≤ 0 := by
      linarith

    change
      abs ((x : ℝ) - 3 / 2) <
        abs ((y : ℝ) - 3 / 2)

    rw [abs_of_nonpos hxnonpos]
    rw [abs_of_nonpos hynonpos]

    linarith


/-!
============================================================
(b)
============================================================
-/

noncomputable def fB :
    Set.Ici (0 : ℝ) → ℝ :=
  fun x => 1 / ((x : ℝ) + 1)


theorem fB_continuous :
    Continuous fB := by

  unfold fB

  have hden :
      Continuous
        (fun x : Set.Ici (0 : ℝ) =>
          (x : ℝ) + 1) := by
    fun_prop

  have hne :
      ∀ x : Set.Ici (0 : ℝ),
        (x : ℝ) + 1 ≠ 0 := by
    intro x

    have hx :
        0 ≤ (x : ℝ) := x.property

    have hp :
        0 < (x : ℝ) + 1 := by
      linarith

    exact ne_of_gt hp

  exact continuous_const.div hden hne


theorem fB_bounded :
    IsBoundedFunction fB := by

  refine ⟨1, by norm_num, ?_⟩

  intro x

  have hx :
      0 ≤ (x : ℝ) := x.property

  have hden :
      0 < (x : ℝ) + 1 := by
    linarith

  have hpos :
      0 ≤ 1 / ((x : ℝ) + 1) := by
    exact le_of_lt (one_div_pos.mpr hden)

  change abs (1 / ((x : ℝ) + 1)) ≤ 1

  rw [abs_of_nonneg hpos]

  have hle :
      1 / ((x : ℝ) + 1) ≤ (1 : ℝ) := by
    apply (div_le_iff₀ hden).2
    linarith

  exact hle


theorem fB_attains_maximum :
    AttainsMaximum fB := by

  let z : Set.Ici (0 : ℝ) :=
    ⟨0, by norm_num⟩

  refine ⟨z, ?_⟩

  intro x

  have hx :
      0 ≤ (x : ℝ) := x.property

  have hden :
      0 < (x : ℝ) + 1 := by
    linarith

  have hle :
      1 / ((x : ℝ) + 1) ≤ (1 : ℝ) := by
    apply (div_le_iff₀ hden).2
    linarith

  change
    1 / ((x : ℝ) + 1) ≤
      1 / ((z : ℝ) + 1)

  have hz :
      (z : ℝ) = 0 := rfl

  rw [hz]

  norm_num

  simpa [one_div] using hle


theorem fB_has_no_minimum :
    HasNoMinimum fB := by

  intro x

  have hx0 :
      0 ≤ (x : ℝ) := x.property

  have hyMem :
      0 ≤ (x : ℝ) + 1 := by
    exact add_nonneg hx0 (by norm_num)

  let y : Set.Ici (0 : ℝ) :=
    ⟨(x : ℝ) + 1, hyMem⟩

  refine ⟨y, ?_⟩

  have hxden :
      0 < (x : ℝ) + 1 := by
    linarith

  have hyden :
      0 < (y : ℝ) + 1 := by
    dsimp [y]
    linarith

  change
    1 / ((y : ℝ) + 1) <
      1 / ((x : ℝ) + 1)

  have hdenlt :
      (x : ℝ) + 1 <
        (y : ℝ) + 1 := by
    dsimp [y]
    linarith

  exact one_div_lt_one_div_of_lt hxden hdenlt


/-!
============================================================
(c)

f(-1) = 0
f(1)  = 0
f(x)  = x otherwise
============================================================
-/

noncomputable def fC :
    Set.Icc (-1 : ℝ) 1 → ℝ :=
  fun x =>
    if (x : ℝ) = -1 ∨ (x : ℝ) = 1
    then 0
    else (x : ℝ)


theorem fC_bounded :
    IsBoundedFunction fC := by

  refine ⟨1, by norm_num, ?_⟩

  intro x

  unfold fC

  split
  next =>
    norm_num
  next =>
    exact abs_le.mpr x.property


theorem fC_has_no_minimum :
    HasNoMinimum fC := by

  intro x

  by_cases hEnd :
      (x : ℝ) = -1 ∨ (x : ℝ) = 1

  · let y : Set.Icc (-1 : ℝ) 1 :=
      ⟨-(1 / 2 : ℝ), by
        constructor <;> norm_num⟩

    refine ⟨y, ?_⟩

    have hxVal :
        fC x = 0 := by
      unfold fC
      split
      next =>
        rfl
      next h =>
        exact (h hEnd).elim

    have hyVal :
        fC y = -(1 / 2 : ℝ) := by
      unfold fC
      split
      next h =>
        dsimp [y] at h
        rcases h with h | h
        · norm_num at h
        · norm_num at h
      next =>
        dsimp [y]

    rw [hxVal, hyVal]

    norm_num

  · have hxNotLeft :
        (x : ℝ) ≠ -1 := by
      intro hx
      exact hEnd (Or.inl hx)

    have hxgt :
        -1 < (x : ℝ) := by
      have hxle :
          -1 ≤ (x : ℝ) := x.property.1
      exact lt_of_le_of_ne hxle (Ne.symm hxNotLeft)

    let yval : ℝ :=
      ((x : ℝ) - 1) / 2

    have hyLower :
        -1 ≤ yval := by
      dsimp [yval]
      linarith

    have hyUpper :
        yval ≤ 1 := by
      dsimp [yval]
      linarith [x.property.2]

    let y : Set.Icc (-1 : ℝ) 1 :=
      ⟨yval, hyLower, hyUpper⟩

    have hylt :
        (y : ℝ) < (x : ℝ) := by
      dsimp [y, yval]
      linarith

    have hyNotLeft :
        (y : ℝ) ≠ -1 := by
      intro hy
      dsimp [y, yval] at hy
      linarith

    have hyNotRight :
        (y : ℝ) ≠ 1 := by
      intro hy
      dsimp [y, yval] at hy
      linarith [x.property.2]

    have hyEnd :
        ¬ ((y : ℝ) = -1 ∨ (y : ℝ) = 1) := by
      intro h
      rcases h with h | h
      · exact hyNotLeft h
      · exact hyNotRight h

    have hxVal :
        fC x = (x : ℝ) := by
      unfold fC
      split
      next h =>
        exact (hEnd h).elim
      next =>
        rfl

    have hyVal :
        fC y = (y : ℝ) := by
      unfold fC
      split
      next h =>
        exact (hyEnd h).elim
      next =>
        rfl

    refine ⟨y, ?_⟩

    rw [hxVal, hyVal]

    exact hylt


theorem fC_has_no_maximum :
    HasNoMaximum fC := by

  intro x

  by_cases hEnd :
      (x : ℝ) = -1 ∨ (x : ℝ) = 1

  · let y : Set.Icc (-1 : ℝ) 1 :=
      ⟨(1 / 2 : ℝ), by
        constructor <;> norm_num⟩

    refine ⟨y, ?_⟩

    have hxVal :
        fC x = 0 := by
      unfold fC
      split
      next =>
        rfl
      next h =>
        exact (h hEnd).elim

    have hyVal :
        fC y = (1 / 2 : ℝ) := by
      unfold fC
      split
      next h =>
        dsimp [y] at h
        rcases h with h | h
        · norm_num at h
        · norm_num at h
      next =>
        dsimp [y]

    rw [hxVal, hyVal]

    norm_num

  · have hxNotRight :
        (x : ℝ) ≠ 1 := by
      intro hx
      exact hEnd (Or.inr hx)

    have hxlt :
        (x : ℝ) < 1 := by
      have hxle :
          (x : ℝ) ≤ 1 := x.property.2
      exact lt_of_le_of_ne hxle hxNotRight

    let yval : ℝ :=
      ((x : ℝ) + 1) / 2

    have hyLower :
        -1 ≤ yval := by
      dsimp [yval]
      linarith [x.property.1]

    have hyUpper :
        yval ≤ 1 := by
      dsimp [yval]
      linarith

    let y : Set.Icc (-1 : ℝ) 1 :=
      ⟨yval, hyLower, hyUpper⟩

    have hxltY :
        (x : ℝ) < (y : ℝ) := by
      dsimp [y, yval]
      linarith

    have hyNotLeft :
        (y : ℝ) ≠ -1 := by
      intro hy
      dsimp [y, yval] at hy
      linarith [x.property.1]

    have hyNotRight :
        (y : ℝ) ≠ 1 := by
      intro hy
      dsimp [y, yval] at hy
      linarith

    have hyEnd :
        ¬ ((y : ℝ) = -1 ∨ (y : ℝ) = 1) := by
      intro h
      rcases h with h | h
      · exact hyNotLeft h
      · exact hyNotRight h

    have hxVal :
        fC x = (x : ℝ) := by
      unfold fC
      split
      next h =>
        exact (hEnd h).elim
      next =>
        rfl

    have hyVal :
        fC y = (y : ℝ) := by
      unfold fC
      split
      next h =>
        exact (hyEnd h).elim
      next =>
        rfl

    refine ⟨y, ?_⟩

    rw [hxVal, hyVal]

    exact hxltY


/-!
============================================================
(d)

f(x) = 1/x if x ≠ 0
f(0) = 0
============================================================
-/

noncomputable def fD :
    Set.Icc (-1 : ℝ) 1 → ℝ :=
  fun x =>
    if (x : ℝ) = 0
    then 0
    else 1 / (x : ℝ)


theorem fD_has_no_upper_bound :
    HasNoUpperBound fD := by

  intro M

  let t : ℝ :=
    1 / (abs M + 1)

  have hden :
      0 < abs M + 1 := by
    positivity

  have hdenne :
      abs M + 1 ≠ 0 := by
    exact ne_of_gt hden

  have htpos :
      0 < t := by
    dsimp [t]
    positivity

  have htle :
      t ≤ 1 := by
    dsimp [t]

    apply (div_le_iff₀ hden).2

    nlinarith [abs_nonneg M]

  let x : Set.Icc (-1 : ℝ) 1 :=
    ⟨t, by
      constructor
      · linarith
      · exact htle⟩

  refine ⟨x, ?_⟩

  have hxne :
      (x : ℝ) ≠ 0 := by
    dsimp [x]
    exact ne_of_gt htpos

  have hfx :
      fD x = abs M + 1 := by
    unfold fD

    split
    next hzero =>
      exact (hxne hzero).elim
    next =>
      dsimp [x, t]
      field_simp [hdenne]

  rw [hfx]

  have hM :
      M ≤ abs M := by
    exact le_abs_self M

  linarith


theorem fD_has_no_lower_bound :
    HasNoLowerBound fD := by

  intro M

  let t : ℝ :=
    1 / (abs M + 1)

  have hden :
      0 < abs M + 1 := by
    positivity

  have hdenne :
      abs M + 1 ≠ 0 := by
    exact ne_of_gt hden

  have htpos :
      0 < t := by
    dsimp [t]
    positivity

  have htle :
      t ≤ 1 := by
    dsimp [t]

    apply (div_le_iff₀ hden).2

    nlinarith [abs_nonneg M]

  let x : Set.Icc (-1 : ℝ) 1 :=
    ⟨-t, by
      constructor
      · linarith
      · linarith⟩

  refine ⟨x, ?_⟩

  have hxne :
      (x : ℝ) ≠ 0 := by
    dsimp [x]
    exact neg_ne_zero.mpr (ne_of_gt htpos)

  have hfx :
      fD x = -(abs M + 1) := by
    unfold fD

    split
    next hzero =>
      exact (hxne hzero).elim
    next =>
      dsimp [x, t]
      field_simp [hdenne]

  rw [hfx]

  have hM :
      -abs M ≤ M := by
    exact neg_abs_le M

  linarith


/-!
============================================================
Exercise 9.6.1
============================================================
-/

theorem exercise_9_6_1_a :
    Continuous fA
      ∧ IsBoundedFunction fA
      ∧ AttainsMinimum fA
      ∧ HasNoMaximum fA := by
  exact
    ⟨fA_continuous,
     fA_bounded,
     fA_attains_minimum,
     fA_has_no_maximum⟩


theorem exercise_9_6_1_b :
    Continuous fB
      ∧ IsBoundedFunction fB
      ∧ AttainsMaximum fB
      ∧ HasNoMinimum fB := by
  exact
    ⟨fB_continuous,
     fB_bounded,
     fB_attains_maximum,
     fB_has_no_minimum⟩


theorem exercise_9_6_1_c :
    IsBoundedFunction fC
      ∧ HasNoMinimum fC
      ∧ HasNoMaximum fC := by
  exact
    ⟨fC_bounded,
     fC_has_no_minimum,
     fC_has_no_maximum⟩


theorem exercise_9_6_1_d :
    HasNoUpperBound fD
      ∧ HasNoLowerBound fD := by
  exact
    ⟨fD_has_no_upper_bound,
     fD_has_no_lower_bound⟩

end TaoExercise9_6_1
