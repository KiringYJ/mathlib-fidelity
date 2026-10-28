/-
Copyright (c) 2023 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.BigOperators.Expect

/-!
# Balancing a function

This file defines the balancing of a function `f`, defined as `f` minus its average.

This is the unique function `g` such that `f a - f b = g a - g b` for all `a` and `b`, and
`∑ a, g a = 0`. This is particularly useful in Fourier analysis as `f` and `g` then have the same
Fourier transform, except in the `0`-th frequency where the Fourier transform of `g` vanishes.
-/

@[expose] public section

open Finset Function
open scoped BigOperators

variable {ι H F G : Type*}

namespace Fintype

section AddCommGroup
variable [Fintype ι] [AddCommGroup G] [Module ℚ≥0 G] [AddCommGroup H] [Module ℚ≥0 H]

/-- The balancing of a function, namely the function minus its average.

The value at a point `x` subtracts the average of `f` over the whole index type, which `x` shows to
be nonempty. The balancing is therefore defined on every finite index type, and on an empty one it
is the empty function. -/
def balance (f : ι → G) : ι → G := fun x ↦ haveI : Nonempty ι := ⟨x⟩; f x - 𝔼 y, f y

lemma balance_apply (f : ι → G) (x : ι) :
    balance f x = haveI : Nonempty ι := ⟨x⟩; f x - 𝔼 y, f y := rfl

@[simp] lemma balance_zero : balance (0 : ι → G) = 0 := by
  ext x
  simp [balance_apply]

@[simp] lemma balance_add (f g : ι → G) : balance (f + g) = balance f + balance g := by
  ext x
  simp only [balance_apply, Pi.add_apply, expect_add_distrib, add_sub_add_comm]

@[simp] lemma balance_sub (f g : ι → G) : balance (f - g) = balance f - balance g := by
  ext x
  simp only [balance_apply, Pi.sub_apply, expect_sub_distrib, sub_sub_sub_comm]

@[simp] lemma balance_neg (f : ι → G) : balance (-f) = -balance f := by
  ext x
  simp only [balance_apply, Pi.neg_apply, expect_neg_distrib, neg_sub']

@[simp] lemma sum_balance (f : ι → G) : ∑ x, balance f x = 0 := by
  cases isEmpty_or_nonempty ι
  · simp
  · change ∑ x, (f x - 𝔼 y, f y) = 0
    rw [sum_sub_distrib, sum_const, card_univ, Fintype.card_smul_expect, sub_self]

@[simp] lemma expect_balance [Nonempty ι] (f : ι → G) : 𝔼 x, balance f x = 0 := by
  rw [expect_def, sum_balance, smul_zero]

@[simp] lemma balance_idem (f : ι → G) : balance (balance f) = balance f := by
  ext x
  have : Nonempty ι := ⟨x⟩
  change balance f x - 𝔼 y, balance f y = balance f x
  rw [expect_balance, sub_zero]

@[simp] lemma map_balance [FunLike F G H] [LinearMapClass F ℚ≥0 G H] (g : F) (f : ι → G) (a : ι) :
    g (balance f a) = balance (g ∘ f) a := by
  simp only [balance_apply, map_sub, map_expect, comp_apply]

end AddCommGroup
end Fintype
