/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Jireh Loreaux
-/
module

public import Mathlib.Algebra.Group.Center
public import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Center of a group with zero
-/

public section

assert_not_exists RelIso Finset Ring Subsemigroup

variable {M₀ G₀ : Type*}

namespace Set
section MulZeroClass
variable [MulZeroClass M₀] {s : Set M₀}

@[simp] lemma zero_mem_center : (0 : M₀) ∈ center M₀ where
  comm _ := by rw [commute_iff_eq, zero_mul, mul_zero]
  left_assoc _ _ := by rw [zero_mul, zero_mul, zero_mul]
  right_assoc _ _ := by rw [mul_zero, mul_zero, mul_zero]

@[simp] lemma zero_mem_centralizer : (0 : M₀) ∈ centralizer s := by simp [mem_centralizer_iff]

end MulZeroClass

section GroupWithZero
variable [GroupWithZero G₀] {s : Set G₀} {a b : G₀}

lemma center_units_subset : center G₀ˣ ⊆ ((↑) : G₀ˣ → G₀) ⁻¹' center G₀ := by
  simp_rw [subset_def, mem_preimage, _root_.Semigroup.mem_center_iff]
  intro u hu a
  obtain rfl | ha := eq_or_ne a 0
  · rw [zero_mul, mul_zero]
  · exact congr_arg Units.val <| hu <| Units.mk0 a ha

/-- In a group with zero, the center of the units is the preimage of the center. -/
lemma center_units_eq : center G₀ˣ = ((↑) : G₀ˣ → G₀) ⁻¹' center G₀ :=
  center_units_subset.antisymm subset_center_units

/-- Inversion of a unit preserves membership in a centralizer. -/
lemma units_inv_mem_centralizer {u : G₀ˣ} (hu : (u : G₀) ∈ centralizer s) :
    (↑u⁻¹ : G₀) ∈ centralizer s := by
  intro c hc
  exact (Commute.units_inv_right (hu c hc)).eq

/-- Division by a unit preserves a centralizer when both factors belong to it. -/
lemma divp_mem_centralizer {u : G₀ˣ} (ha : a ∈ centralizer s)
    (hu : (u : G₀) ∈ centralizer s) : a /ₚ u ∈ centralizer s :=
  mul_mem_centralizer ha (units_inv_mem_centralizer hu)

end GroupWithZero
end Set
