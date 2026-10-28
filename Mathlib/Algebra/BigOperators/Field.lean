/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Daniel Weber
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Finset.Density

/-!
# Results about big operators with values in a field
-/

public section

open Fintype

variable {ι K : Type*} [DivisionSemiring K]

lemma Multiset.sum_map_div (s : Multiset ι) (f : ι → K) (a : K) {ha : IsUnit a} :
    (s.map (fun x ↦ f x / a)).sum = (s.map f).sum / a := by
  simp only [div_eq_mul_inv₀, Multiset.sum_map_mul_right]

lemma Finset.sum_div (s : Finset ι) (f : ι → K) (a : K) {ha : IsUnit a} :
    (∑ i ∈ s, f i) / a = ∑ i ∈ s, f i / a := by simp only [div_eq_mul_inv₀, sum_mul]

-- TODO: Move these to `Algebra.BigOperators.Group.Finset.Basic`, next to the corresponding `card`
-- lemmas, once `Finset.dens` doesn't depend on `Field` anymore.
namespace Finset
variable {α β : Type*} [Fintype β] [Nonempty β]

@[simp]
lemma dens_disjiUnion (s : Finset α) (t : α → Finset β) (h) :
    (s.disjiUnion t h).dens = ∑ a ∈ s, (t a).dens := by
  apply mul_right_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero : (Fintype.card β : ℚ≥0) ≠ 0)
  simp only [sum_mul, dens_mul_card, card_disjiUnion, Nat.cast_sum]

variable {s : Finset α} {t : α → Finset β}

lemma dens_biUnion [DecidableEq β] (h : (s : Set α).PairwiseDisjoint t) :
    (s.biUnion t).dens = ∑ u ∈ s, (t u).dens := by
  apply mul_right_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero : (Fintype.card β : ℚ≥0) ≠ 0)
  simp only [sum_mul, dens_mul_card, card_biUnion h, Nat.cast_sum]

lemma dens_biUnion_le [DecidableEq β] : (s.biUnion t).dens ≤ ∑ a ∈ s, (t a).dens := by
  apply (mul_le_mul_iff_of_pos_right
    (Nat.cast_pos.mpr Fintype.card_pos : (0 : ℚ≥0) < Fintype.card β)).mp
  simp only [sum_mul, dens_mul_card]
  exact_mod_cast card_biUnion_le

lemma dens_eq_sum_dens_fiberwise [DecidableEq α] {f : β → α} {t : Finset β}
    (h : (t : Set β).MapsTo f s) : t.dens = ∑ a ∈ s, {b ∈ t | f b = a}.dens := by
  apply mul_right_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero : (Fintype.card β : ℚ≥0) ≠ 0)
  simp only [sum_mul, dens_mul_card, card_eq_sum_card_fiberwise h, Nat.cast_sum]

lemma dens_eq_sum_dens_image [DecidableEq α] (f : β → α) (t : Finset β) :
    t.dens = ∑ a ∈ t.image f, {b ∈ t | f b = a}.dens :=
  dens_eq_sum_dens_fiberwise fun _ ↦ mem_image_of_mem _

end Finset
