/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
public import Mathlib.Data.Finset.Density

/-!
# Doubling and difference constants

This file defines the doubling and difference constants of two finsets in a group.
-/

@[expose] public section

open Finset
open scoped Pointwise

namespace Finset
section Group
variable {G : Type*} [Group G] [DecidableEq G] {A B : Finset G}

/-- The doubling constant `σₘ[A, B]` of finsets `A` and `B` in a group, with `A` nonempty, is
`|A * B| / |A|`.

The notation `σₘ[A, B]` is available in scope `Combinatorics.Additive`. -/
@[to_additive
/-- The doubling constant `σ[A, B]` of finsets `A` and `B` in a group, with `A` nonempty, is
`|A + B| / |A|`.

The notation `σ[A, B]` is available in scope `Combinatorics.Additive`. -/]
def mulConst (A B : Finset G) (hA : A.Nonempty := by
    first
    | assumption
    | apply Finset.inv_nonempty_iff.mpr; assumption
    | fail "doubling and difference constants require a nonempty left set") : ℚ≥0 :=
  NNRat.divNat #(A * B) #A hA.card_ne_zero

/-- The difference constant `δₘ[A, B]` of finsets `A` and `B` in a group, with `A` nonempty, is
`|A * B⁻¹| / |A|`.

The notation `δₘ[A, B]` is available in scope `Combinatorics.Additive`. -/
@[to_additive
/-- The difference constant `δ[A, B]` of finsets `A` and `B` in a group, with `A` nonempty, is
`|A - B| / |A|`.

The notation `δ[A, B]` is available in scope `Combinatorics.Additive`. -/]
def divConst (A B : Finset G) (hA : A.Nonempty := by
    first
    | assumption
    | apply Finset.inv_nonempty_iff.mpr; assumption
    | fail "doubling and difference constants require a nonempty left set") : ℚ≥0 :=
  NNRat.divNat #(A * B⁻¹) #A hA.card_ne_zero

/-- The doubling constant `σₘ[A, B]` of finsets `A` and `B` in a group, with `A` nonempty, is
`|A * B| / |A|`. -/
scoped[Combinatorics.Additive] notation:max "σₘ[" A ", " B "]" => Finset.mulConst A B

/-- The doubling constant `σₘ[A]` of a finset `A` in a group is `|A * A| / |A|`. -/
scoped[Combinatorics.Additive] notation:max "σₘ[" A "]" => Finset.mulConst A A

/-- The doubling constant `σ[A, B]` of finsets `A` and `B` in a group, with `A` nonempty, is
`|A + B| / |A|`. -/
scoped[Combinatorics.Additive] notation:max "σ[" A ", " B "]" => Finset.addConst A B

/-- The doubling constant `σ[A]` of a finset `A` in a group is `|A + A| / |A|`. -/
scoped[Combinatorics.Additive] notation:max "σ[" A "]" => Finset.addConst A A

/-- The difference constant `δₘ[A, B]` of finsets `A` and `B` in a group, with `A` nonempty, is
`|A * B⁻¹| / |A|`. -/
scoped[Combinatorics.Additive] notation:max "δₘ[" A ", " B "]" => Finset.divConst A B

/-- The difference constant `δₘ[A]` of a finset `A` in a group is `|A * A⁻¹| / |A|`. -/
scoped[Combinatorics.Additive] notation:max "δₘ[" A "]" => Finset.divConst A A

/-- The difference constant `δ[A, B]` of finsets `A` and `B` in a group, with `A` nonempty, is
`|A - B| / |A|`. -/
scoped[Combinatorics.Additive] notation:max "δ[" A ", " B "]" => Finset.subConst A B

/-- The difference constant `δ[A]` of a finset `A` in a group is `|A - A| / |A|`. -/
scoped[Combinatorics.Additive] notation:max "δ[" A "]" => Finset.subConst A A

open scoped Combinatorics.Additive

@[to_additive (attr := simp) addConst_mul_card]
lemma mulConst_mul_card (A B : Finset G) (hA : A.Nonempty) : σₘ[A, B] * #A = #(A * B) := by
  exact NNRat.divNat_mul_den _ _ _

@[to_additive (attr := simp) subConst_mul_card]
lemma divConst_mul_card (A B : Finset G) (hA : A.Nonempty) : δₘ[A, B] * #A = #(A * B⁻¹) := by
  exact NNRat.divNat_mul_den _ _ _

@[to_additive (attr := simp) card_mul_addConst]
lemma card_mul_mulConst (A B : Finset G) (hA : A.Nonempty) : #A * σₘ[A, B] = #(A * B) := by
  rw [mul_comm, mulConst_mul_card]

@[to_additive (attr := simp) card_mul_subConst]
lemma card_mul_divConst (A B : Finset G) (hA : A.Nonempty) : #A * δₘ[A, B] = #(A * B⁻¹) := by
  rw [mul_comm, divConst_mul_card]

@[to_additive (attr := simp)]
lemma mulConst_empty_right (A : Finset G) (hA : A.Nonempty) : σₘ[A, ∅] = 0 := by
  apply mul_right_cancel₀ (Nat.cast_ne_zero.mpr hA.card_ne_zero : (#A : ℚ≥0) ≠ 0)
  simp only [mulConst_mul_card, mul_empty, card_empty, Nat.cast_zero, zero_mul]

@[to_additive (attr := simp)]
lemma divConst_empty_right (A : Finset G) (hA : A.Nonempty) : δₘ[A, ∅] = 0 := by
  apply mul_right_cancel₀ (Nat.cast_ne_zero.mpr hA.card_ne_zero : (#A : ℚ≥0) ≠ 0)
  simp only [divConst_mul_card, inv_empty, mul_empty, card_empty, Nat.cast_zero, zero_mul]

@[to_additive (attr := simp)]
lemma mulConst_inv_right (A B : Finset G) (hA : A.Nonempty) : σₘ[A, B⁻¹] = δₘ[A, B] := by
  rfl

@[to_additive (attr := simp)]
lemma divConst_inv_right (A B : Finset G) (hA : A.Nonempty) : δₘ[A, B⁻¹] = σₘ[A, B] := by
  simp only [mulConst, divConst, inv_inv]

@[to_additive]
lemma one_le_mulConst (hA : A.Nonempty) (hB : B.Nonempty) : 1 ≤ σₘ[A, B] := by
  apply (mul_le_mul_iff_of_pos_right (Nat.cast_pos.mpr hA.card_pos : (0 : ℚ≥0) < #A)).mp
  rw [one_mul, mulConst_mul_card]
  exact_mod_cast card_le_card_mul_right hB

@[to_additive]
lemma one_le_mulConst_self (hA : A.Nonempty) : 1 ≤ σₘ[A] := one_le_mulConst hA hA

@[to_additive]
lemma one_le_divConst (hA : A.Nonempty) (hB : B.Nonempty) : 1 ≤ δₘ[A, B] := by
  rw [← mulConst_inv_right]
  apply one_le_mulConst hA (by simpa)

@[to_additive]
lemma one_le_divConst_self (hA : A.Nonempty) : 1 ≤ δₘ[A] := one_le_divConst hA hA

@[to_additive]
lemma mulConst_le_card (hA : A.Nonempty) : σₘ[A, B] ≤ #B := by
  apply (mul_le_mul_iff_of_pos_right (Nat.cast_pos.mpr hA.card_pos : (0 : ℚ≥0) < #A)).mp
  rw [mulConst_mul_card, mul_comm]
  exact mod_cast card_mul_le

@[to_additive]
lemma divConst_le_card (hA : A.Nonempty) : δₘ[A, B] ≤ #B := by
  apply (mul_le_mul_iff_of_pos_right (Nat.cast_pos.mpr hA.card_pos : (0 : ℚ≥0) < #A)).mp
  rw [divConst_mul_card, mul_comm]
  simpa only [card_inv] using (show (#(A * B⁻¹) : ℚ≥0) ≤ #A * #(B⁻¹) by
    exact_mod_cast card_mul_le)

section Fintype
variable [Fintype G]

/-- Dense sets have small doubling. -/
@[to_additive addConst_le_inv_dens /-- Dense sets have small doubling. -/]
lemma mulConst_le_inv_dens (hA : A.Nonempty) : σₘ[A, B] ≤ A.dens⁻¹ := by
  apply (mul_le_mul_iff_of_pos_right (Nat.cast_pos.mpr hA.card_pos : (0 : ℚ≥0) < #A)).mp
  rw [mulConst_mul_card]
  have hc : A.dens⁻¹ * #A = Fintype.card G := by
    conv_lhs => rw [← A.dens_mul_card]
    rw [← mul_assoc, inv_mul_cancel₀, one_mul]
  rw [hc]
  exact_mod_cast card_le_univ (A * B)

/-- Dense sets have small difference constant. -/
@[to_additive subConst_le_inv_dens /-- Dense sets have small difference constant. -/]
lemma divConst_le_inv_dens (hA : A.Nonempty) : δₘ[A, B] ≤ A.dens⁻¹ := by
  apply (mul_le_mul_iff_of_pos_right (Nat.cast_pos.mpr hA.card_pos : (0 : ℚ≥0) < #A)).mp
  rw [divConst_mul_card]
  have hc : A.dens⁻¹ * #A = Fintype.card G := by
    conv_lhs => rw [← A.dens_mul_card]
    rw [← mul_assoc, inv_mul_cancel₀, one_mul]
  rw [hc]
  exact_mod_cast card_le_univ (A * B⁻¹)

end Fintype

variable {𝕜 : Type*} [Semifield 𝕜] [CharZero 𝕜]

@[to_additive (dont_translate := 𝕜)]
lemma cast_mulConst (A B : Finset G) (hA : A.Nonempty) :
    (σₘ[A, B] : 𝕜) =
      Checked.div (#(A * B) : 𝕜) (#A : 𝕜) (Nat.cast_ne_zero.mpr hA.card_ne_zero).isUnit := by
  rw [eq_div_iff]
  exact_mod_cast mulConst_mul_card A B hA

@[to_additive (dont_translate := 𝕜)]
lemma cast_divConst (A B : Finset G) (hA : A.Nonempty) :
    (δₘ[A, B] : 𝕜) =
      Checked.div (#(A * B⁻¹) : 𝕜) (#A : 𝕜)
        (Nat.cast_ne_zero.mpr hA.card_ne_zero).isUnit := by
  rw [eq_div_iff]
  exact_mod_cast divConst_mul_card A B hA

@[to_additive (dont_translate := 𝕜) (attr := simp) cast_addConst_mul_card]
lemma cast_mulConst_mul_card (A B : Finset G) (hA : A.Nonempty) :
    (σₘ[A, B] * #A : 𝕜) = #(A * B) := by
  norm_cast; exact mulConst_mul_card _ _ hA

@[to_additive (dont_translate := 𝕜) (attr := simp) cast_subConst_mul_card]
lemma cast_divConst_mul_card (A B : Finset G) (hA : A.Nonempty) :
    (δₘ[A, B] * #A : 𝕜) = #(A * B⁻¹) := by
  norm_cast; exact divConst_mul_card _ _ hA

@[to_additive (dont_translate := 𝕜) (attr := simp) card_mul_cast_addConst]
lemma card_mul_cast_mulConst (A B : Finset G) (hA : A.Nonempty) :
    (#A * σₘ[A, B] : 𝕜) = #(A * B) := by
  norm_cast; exact card_mul_mulConst _ _ hA

@[to_additive (dont_translate := 𝕜) (attr := simp) card_mul_cast_subConst]
lemma card_mul_cast_divConst (A B : Finset G) (hA : A.Nonempty) :
    (#A * δₘ[A, B] : 𝕜) = #(A * B⁻¹) := by
  norm_cast; exact card_mul_divConst _ _ hA

/-- If `A` has small doubling, then it has small difference, with the constant squared.

This is a consequence of the Ruzsa triangle inequality. -/
@[to_additive
/-- If `A` has small doubling, then it has small difference, with the constant squared.

This is a consequence of the Ruzsa triangle inequality. -/]
lemma divConst_le_mulConst_sq (hA : A.Nonempty) : δₘ[A] ≤ σₘ[A] ^ 2 := by
  refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℚ≥0) < #A * #A)
  calc
    _ = #(A * A⁻¹) * (#A : ℚ≥0) := by rw [← mul_assoc, divConst_mul_card]
    _ ≤ #(A * A) * #(A * A) := by norm_cast; exact ruzsa_triangle_inequality_div_mul_mul ..
    _ = _ := by rw [← mulConst_mul_card A A hA, sq]; ac_rfl

end Group

open scoped Combinatorics.Additive

section CommGroup
variable {G : Type*} [CommGroup G] [DecidableEq G] {A B : Finset G}

@[to_additive (attr := simp)]
lemma mulConst_inv_left (A B : Finset G) (hA : A.Nonempty) : σₘ[A⁻¹, B] = δₘ[A, B] := by
  have hc : #(A⁻¹ * B) = #(A / B) := by
    rw [← card_inv (A⁻¹ * B), mul_inv_rev, inv_inv, div_eq_mul_inv, mul_comm]
  rw [div_eq_mul_inv] at hc
  simp only [mulConst, divConst, card_inv, hc]

@[to_additive (attr := simp)]
lemma divConst_inv_left (A B : Finset G) (hA : A.Nonempty) : δₘ[A⁻¹, B] = σₘ[A, B] := by
  have hc : #(A⁻¹ / B) = #(A * B) := by
    rw [← card_inv (A⁻¹ / B), div_eq_mul_inv, mul_inv_rev, inv_inv, inv_inv, mul_comm]
  rw [div_eq_mul_inv] at hc
  simp only [mulConst, divConst, card_inv, hc]

/-- If `A` has small difference, then it has small doubling, with the constant squared.

This is a consequence of the Ruzsa triangle inequality. -/
@[to_additive
/-- If `A` has small difference, then it has small doubling, with the constant squared.

This is a consequence of the Ruzsa triangle inequality. -/]
lemma mulConst_le_divConst_sq (hA : A.Nonempty) : σₘ[A] ≤ δₘ[A] ^ 2 := by
  refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℚ≥0) < #A * #A)
  calc
    _ = #(A * A) * (#A : ℚ≥0) := by rw [← mul_assoc, mulConst_mul_card]
    _ ≤ #(A / A) * #(A / A) := by norm_cast; exact ruzsa_triangle_inequality_mul_div_div ..
    _ = _ := by rw [div_eq_mul_inv, ← divConst_mul_card A A hA, sq]; ac_rfl

end CommGroup
end Finset
