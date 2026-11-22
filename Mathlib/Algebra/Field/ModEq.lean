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
variable {K : Type*} [Semiring K] {a b c p : K}

@[simp] lemma div_modEq_div {hc : IsUnit c} :
    Checked.div a c hc ≡ Checked.div b c hc [PMOD p] ↔ a ≡ b [PMOD (p * c)] := by
  simp [modEq_iff_nsmul, add_div', div_left_inj', mul_assoc]

@[simp] lemma mul_modEq_mul_right (hc : IsUnit c) :
    a * c ≡ b * c [PMOD p] ↔ a ≡ b [PMOD (p / c)] := by
  rw [div_eq_mul_inv₀, ← div_modEq_div (hc := hc.inv₀), div_inv_eq_mul₀, div_inv_eq_mul₀]

end Semiring

section CommSemiring
variable {K : Type*} [CommSemiring K] {a b c p : K}

@[simp] lemma mul_modEq_mul_left (hc : IsUnit c) :
    c * a ≡ c * b [PMOD p] ↔ a ≡ b [PMOD (p / c)] := by
  simpa only [mul_comm c] using (mul_modEq_mul_right (a := a) (b := b) (p := p) hc)

end CommSemiring
end AddCommGroup
