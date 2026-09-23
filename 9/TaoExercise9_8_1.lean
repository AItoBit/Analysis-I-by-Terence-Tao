import Mathlib

namespace TaoExercise9_8_1

open Set

/-!
============================================================
Attaining minimum and maximum
============================================================
-/

def AttainsMinimum {α : Type*} (f : α → ℝ) : Prop :=
  ∃ x : α, ∀ y : α, f x ≤ f y

def AttainsMaximum {α : Type*} (f : α → ℝ) : Prop :=
  ∃ x : α, ∀ y : α, f y ≤ f x


/-!
============================================================
Monotone case

If f is increasing on [a,b], then

  minimum at a,
  maximum at b.
============================================================
-/

theorem monotone_attains_min_max
    (a b : ℝ)
    (hab : a ≤ b)
    (f : Set.Icc a b → ℝ)
    (hf : Monotone f) :
    AttainsMinimum f ∧ AttainsMaximum f := by

  let xmin : Set.Icc a b :=
    ⟨a, ⟨le_rfl, hab⟩⟩

  let xmax : Set.Icc a b :=
    ⟨b, ⟨hab, le_rfl⟩⟩

  constructor

  · refine ⟨xmin, ?_⟩

    intro x

    apply hf

    change a ≤ (x : ℝ)

    exact x.property.1

  · refine ⟨xmax, ?_⟩

    intro x

    apply hf

    change (x : ℝ) ≤ b

    exact x.property.2


/-!
============================================================
Antitone case

If f is decreasing on [a,b], then

  maximum at a,
  minimum at b.
============================================================
-/

theorem antitone_attains_min_max
    (a b : ℝ)
    (hab : a ≤ b)
    (f : Set.Icc a b → ℝ)
    (hf : Antitone f) :
    AttainsMinimum f ∧ AttainsMaximum f := by

  let xmin : Set.Icc a b :=
    ⟨b, ⟨hab, le_rfl⟩⟩

  let xmax : Set.Icc a b :=
    ⟨a, ⟨le_rfl, hab⟩⟩

  constructor

  · refine ⟨xmin, ?_⟩

    intro x

    apply hf

    change (x : ℝ) ≤ b

    exact x.property.2

  · refine ⟨xmax, ?_⟩

    intro x

    apply hf

    change a ≤ (x : ℝ)

    exact x.property.1


/-!
============================================================
Strictly monotone case

Strictly increasing implies increasing.
============================================================
-/

theorem strictMono_attains_min_max
    (a b : ℝ)
    (hab : a ≤ b)
    (f : Set.Icc a b → ℝ)
    (hf : StrictMono f) :
    AttainsMinimum f ∧ AttainsMaximum f := by

  exact monotone_attains_min_max
    a
    b
    hab
    f
    hf.monotone


/-!
============================================================
Strictly decreasing case

Strictly decreasing implies decreasing.
============================================================
-/

theorem strictAnti_attains_min_max
    (a b : ℝ)
    (hab : a ≤ b)
    (f : Set.Icc a b → ℝ)
    (hf : StrictAnti f) :
    AttainsMinimum f ∧ AttainsMaximum f := by

  exact antitone_attains_min_max
    a
    b
    hab
    f
    hf.antitone


/-!
============================================================
Monotone in either direction
============================================================
-/

theorem monotone_or_antitone_attains_min_max
    (a b : ℝ)
    (hab : a ≤ b)
    (f : Set.Icc a b → ℝ)
    (hf : Monotone f ∨ Antitone f) :
    AttainsMinimum f ∧ AttainsMaximum f := by

  rcases hf with hmono | hanti

  · exact monotone_attains_min_max
      a
      b
      hab
      f
      hmono

  · exact antitone_attains_min_max
      a
      b
      hab
      f
      hanti


/-!
============================================================
Strictly monotone in either direction
============================================================
-/

theorem strictMono_or_strictAnti_attains_min_max
    (a b : ℝ)
    (hab : a ≤ b)
    (f : Set.Icc a b → ℝ)
    (hf : StrictMono f ∨ StrictAnti f) :
    AttainsMinimum f ∧ AttainsMaximum f := by

  rcases hf with hmono | hanti

  · exact strictMono_attains_min_max
      a
      b
      hab
      f
      hmono

  · exact strictAnti_attains_min_max
      a
      b
      hab
      f
      hanti


/-!
============================================================
Exercise 9.8.1
============================================================
-/

theorem exercise_9_8_1_monotone
    (a b : ℝ)
    (hab : a ≤ b)
    (f : Set.Icc a b → ℝ)
    (hf : Monotone f ∨ Antitone f) :
    AttainsMinimum f ∧ AttainsMaximum f := by

  exact monotone_or_antitone_attains_min_max
    a
    b
    hab
    f
    hf


theorem exercise_9_8_1_strict
    (a b : ℝ)
    (hab : a ≤ b)
    (f : Set.Icc a b → ℝ)
    (hf : StrictMono f ∨ StrictAnti f) :
    AttainsMinimum f ∧ AttainsMaximum f := by

  exact strictMono_or_strictAnti_attains_min_max
    a
    b
    hab
    f
    hf

end TaoExercise9_8_1
