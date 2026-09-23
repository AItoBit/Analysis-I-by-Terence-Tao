import Mathlib

namespace TaoExercise8_1_8

open Function

universe u v

/-!
============================================================
Countably infinite
============================================================

A type is countably infinite when it is equivalent to ℕ.
-/

def CountablyInfinite (X : Type u) : Prop :=
  Nonempty (X ≃ ℕ)


/-!
============================================================
Corollary 8.1.13

ℕ × ℕ is countably infinite.
============================================================

We package the standard Mathlib equivalence here.
-/

theorem corollary_8_1_13 :
    CountablyInfinite (ℕ × ℕ) := by
  unfold CountablyInfinite

  exact ⟨Equiv.natProdNat⟩


/-!
============================================================
Product of two equivalences
============================================================

If

    f : X ≃ ℕ
    g : Y ≃ ℕ

then

    X × Y ≃ ℕ × ℕ.
-/

def productEquiv
    {X : Type u}
    {Y : Type v}
    (f : X ≃ ℕ)
    (g : Y ≃ ℕ) :
    X × Y ≃ ℕ × ℕ :=
  Equiv.prodCongr f g


/-!
============================================================
Injectivity of the product map
============================================================
-/

theorem productEquiv_injective
    {X : Type u}
    {Y : Type v}
    (f : X ≃ ℕ)
    (g : Y ≃ ℕ) :
    Function.Injective
      (fun p : X × Y =>
        (f p.1, g p.2)) := by

  intro p q hpq

  rcases p with ⟨x, y⟩
  rcases q with ⟨x', y'⟩

  simp only at hpq

  have hx :
      f x = f x' := by
    exact congrArg Prod.fst hpq

  have hy :
      g y = g y' := by
    exact congrArg Prod.snd hpq

  have hxx :
      x = x' := by
    exact f.injective hx

  have hyy :
      y = y' := by
    exact g.injective hy

  subst x'
  subst y'

  rfl


/-!
============================================================
Surjectivity of the product map
============================================================
-/

theorem productEquiv_surjective
    {X : Type u}
    {Y : Type v}
    (f : X ≃ ℕ)
    (g : Y ≃ ℕ) :
    Function.Surjective
      (fun p : X × Y =>
        (f p.1, g p.2)) := by

  intro q

  rcases q with ⟨n, m⟩

  refine ⟨(f.symm n, g.symm m), ?_⟩

  simp


/-!
============================================================
Explicit bijection X × Y ≃ ℕ × ℕ
============================================================
-/

theorem product_has_same_cardinality_as_nat_product
    {X : Type u}
    {Y : Type v}
    (f : X ≃ ℕ)
    (g : Y ≃ ℕ) :
    Nonempty (X × Y ≃ ℕ × ℕ) := by

  exact ⟨productEquiv f g⟩


/-!
============================================================
Corollary 8.1.14

If X and Y are countably infinite, then X × Y
is countably infinite.
============================================================
-/

theorem corollary_8_1_14
    {X : Type u}
    {Y : Type v}
    (hX : CountablyInfinite X)
    (hY : CountablyInfinite Y) :
    CountablyInfinite (X × Y) := by

  rcases hX with ⟨f⟩
  rcases hY with ⟨g⟩

  rcases corollary_8_1_13 with ⟨hNatProd⟩

  unfold CountablyInfinite

  refine ⟨?_⟩

  exact (Equiv.prodCongr f g).trans hNatProd


/-!
============================================================
Exercise 8.1.8
============================================================
-/

theorem exercise_8_1_8
    {X : Type u}
    {Y : Type v}
    (hX : CountablyInfinite X)
    (hY : CountablyInfinite Y) :
    CountablyInfinite (X × Y) := by

  exact corollary_8_1_14
    hX
    hY

end TaoExercise8_1_8
