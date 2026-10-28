/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Algebra.Group.Conj
public import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Conjugacy in a group with zero
-/

public section

assert_not_exists Multiset Ring
-- TODO
-- assert_not_exists DenselyOrdered

namespace GroupWithZero

variable {α : Type*} [GroupWithZero α] {a b : α}

@[simp] lemma isConj_iff₀ : IsConj a b ↔ ∃ (c : α) (_ : c ≠ 0), c * a * c⁻¹ = b := by
  rw [IsConj, Units.exists_iff_ne_zero (p := (SemiconjBy · a b))]
  refine exists_congr fun c => ⟨fun ⟨hc, h⟩ => ⟨hc, ?_⟩, fun ⟨hc, h⟩ => ⟨hc, ?_⟩⟩
  · exact mul_inv_eq_iff_eq_mul₀.2 h
  · exact mul_inv_eq_iff_eq_mul₀.1 h

lemma conj_pow₀ {s : ℕ} {a d : α} {ha : IsUnit a} : (a⁻¹ * d * a) ^ s = a⁻¹ * d ^ s * a := by
  have h := Units.conj_pow' ha.unit d s
  rw [IsUnit.unit_spec] at h
  exact h

end GroupWithZero
