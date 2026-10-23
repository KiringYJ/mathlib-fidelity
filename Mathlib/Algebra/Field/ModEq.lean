/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.ModEq
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Tactic.MinImports

/-!
# Congruence modulo multiples of an element in a (semi)field

In this file we prove a few theorems about the congruence relation `_ ≡ _ [PMOD _]`
in a division semiring or a semifield.
-/

public section

namespace AddCommGroup

section Semiring
variable {K : Type*} [Semiring K] {a b p : K}

@[simp] lemma divp_modEq_divp (u : Kˣ) :
    a /ₚ u ≡ b /ₚ u [PMOD p] ↔ a ≡ b [PMOD (p * u)] := by
  simp [modEq_iff_nsmul, Units.add_divp, divp_left_inj, mul_assoc]

@[simp] lemma mul_modEq_mul_right (u : Kˣ) :
    a * u ≡ b * u [PMOD p] ↔ a ≡ b [PMOD (p /ₚ u)] := by
  simpa only [divp, inv_inv] using (divp_modEq_divp (a := a) (b := b) (p := p) u⁻¹)

end Semiring

section CommSemiring
variable {K : Type*} [CommSemiring K] {a b p : K}

@[simp] lemma mul_modEq_mul_left (u : Kˣ) :
    (u : K) * a ≡ (u : K) * b [PMOD p] ↔ a ≡ b [PMOD (p /ₚ u)] := by
  simpa only [mul_comm (u : K)] using (mul_modEq_mul_right (a := a) (b := b) (p := p) u)

end CommSemiring
end AddCommGroup
