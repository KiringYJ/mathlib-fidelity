/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Checked

/-!
# Order comparisons for checked inverse and division

These lemmas expose the evidence-bearing operations through the existing unit order API.
They do not install ambient inverse or division instances.
-/

public section

namespace Checked

variable {α : Type*} [GroupWithZero α] [PartialOrder α]
variable {a b c : α} {ha : IsUnit a} {hb : IsUnit b} {hc : IsUnit c}

@[simp] theorem inv_pos [PosMulReflectLT α] : 0 < inv a ha ↔ 0 < a := by
  simpa only [inv, IsUnit.unit_spec] using Units.inv_pos ha.unit

@[simp] theorem inv_nonneg [PosMulReflectLT α] : 0 ≤ inv a ha ↔ 0 ≤ a := by
  simpa only [inv, IsUnit.unit_spec] using Units.inv_nonneg ha.unit

theorem div_pos [PosMulReflectLT α] (h₁ : 0 < a) (h₂ : 0 < b) : 0 < div a b hb := by
  simpa only [div, IsUnit.unit_spec] using divp_pos (u := hb.unit) h₁ h₂

theorem div_nonneg [PosMulReflectLT α] (h₁ : 0 ≤ a) (h₂ : 0 ≤ b) : 0 ≤ div a b hb := by
  simpa only [div, IsUnit.unit_spec] using divp_nonneg (u := hb.unit) h₁ h₂

theorem div_le_iff [MulPosReflectLT α] (h : 0 < c) : div a c hc ≤ b ↔ a ≤ b * c := by
  simpa only [div, IsUnit.unit_spec] using divp_le_iff (a := a) (b := b) (u := hc.unit) h

theorem le_div_iff [MulPosReflectLT α] (h : 0 < c) : a ≤ div b c hc ↔ a * c ≤ b := by
  simpa only [div, IsUnit.unit_spec] using le_divp_iff (a := a) (b := b) (u := hc.unit) h

theorem div_lt_iff [MulPosReflectLT α] (h : 0 < c) : div a c hc < b ↔ a < b * c := by
  simpa only [div, IsUnit.unit_spec] using divp_lt_iff (a := a) (b := b) (u := hc.unit) h

theorem lt_div_iff [MulPosReflectLT α] (h : 0 < c) : a < div b c hc ↔ a * c < b := by
  simpa only [div, IsUnit.unit_spec] using lt_divp_iff (a := a) (b := b) (u := hc.unit) h

theorem div_le_div_of_nonneg_right [MulPosReflectLT α] (h : a ≤ b) (h₀ : 0 ≤ c) :
    div a c hc ≤ div b c hc := by
  simpa only [div, IsUnit.unit_spec] using
    divp_le_divp_of_nonneg_right (u := hc.unit) h h₀

theorem div_lt_div_of_pos_right [MulPosReflectLT α] (h : a < b) (h₀ : 0 < c) :
    div a c hc < div b c hc := by
  simpa only [div, IsUnit.unit_spec] using divp_lt_divp_of_pos_right (u := hc.unit) h h₀

theorem div_le_div_iff_of_pos_right [MulPosReflectLT α] (h : 0 < c) :
    div a c hc ≤ div b c hc ↔ a ≤ b := by
  simpa only [div, IsUnit.unit_spec] using divp_le_divp_iff (a := a) (b := b) (u := hc.unit) h

theorem div_lt_div_iff_of_pos_right [MulPosReflectLT α] (h : 0 < c) :
    div a c hc < div b c hc ↔ a < b := by
  simpa only [div, IsUnit.unit_spec] using divp_lt_divp_iff (a := a) (b := b) (u := hc.unit) h

theorem inv_le_inv [PosMulReflectLT α] [MulPosReflectLT α] (h₁ : 0 < a) (h₂ : 0 < b) :
    inv a ha ≤ inv b hb ↔ b ≤ a := by
  simpa only [inv, IsUnit.unit_spec] using Units.inv_le_inv (u := ha.unit) (v := hb.unit) h₁ h₂

theorem inv_lt_inv [PosMulReflectLT α] [MulPosReflectLT α] (h₁ : 0 < a) (h₂ : 0 < b) :
    inv a ha < inv b hb ↔ b < a := by
  simpa only [inv, IsUnit.unit_spec] using Units.inv_lt_inv (u := ha.unit) (v := hb.unit) h₁ h₂

theorem div_le_div_of_nonneg_left [PosMulReflectLT α] [MulPosReflectLT α]
    (h₀ : 0 ≤ c) (h₁ : 0 < a) (h : a ≤ b) : div c b hb ≤ div c a ha := by
  simpa only [div, IsUnit.unit_spec] using
    divp_le_divp_of_nonneg_left (u := hb.unit) (v := ha.unit) h₀ h₁ h

theorem div_lt_div_of_pos_left [PosMulReflectLT α] [MulPosReflectLT α]
    (h₀ : 0 < c) (h₁ : 0 < a) (h : a < b) : div c b hb < div c a ha := by
  simpa only [div, IsUnit.unit_spec] using
    divp_lt_divp_of_pos_left (u := hb.unit) (v := ha.unit) h₀ h₁ h

end Checked
