/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
import Mathlib.Algebra.GroupWithZero.Inverse
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.Ring.Archimedean
import Mathlib.Algebra.Tropical.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.ENat.Basic

open scoped OrderDual
open LinearOrderedAddCommGroupWithTop (isAddUnit_iff)

noncomputable section

/-! ### Additive operations -/

/--
error: failed to synthesize
  Neg (WithTop ℤ)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth Neg (WithTop ℤ)

/--
error: failed to synthesize
  Sub (WithTop ℤ)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth Sub (WithTop ℤ)

/--
error: failed to synthesize
  SMul ℤ (WithTop ℤ)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth SMul ℤ (WithTop ℤ)

/--
error: failed to synthesize
  Neg (ArchimedeanClass ℝ)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth Neg (ArchimedeanClass ℝ)

/--
error: failed to synthesize
  Sub (ArchimedeanClass ℝ)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth Sub (ArchimedeanClass ℝ)

/--
error: failed to synthesize
  SMul ℤ (ArchimedeanClass ℝ)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth SMul ℤ (ArchimedeanClass ℝ)

/-! ### Multiplicative and tropical operations -/

/--
error: failed to synthesize
  Inv (Multiplicative (WithTop ℤ))

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth Inv (Multiplicative (WithTop ℤ))

/--
error: failed to synthesize
  Div (Multiplicative (WithTop ℤ))

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth Div (Multiplicative (WithTop ℤ))

/--
error: failed to synthesize
  Pow (Multiplicative (WithTop ℤ)) ℤ

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth Pow (Multiplicative (WithTop ℤ)) ℤ

/--
error: failed to synthesize
  ZPow (Multiplicative (WithTop ℤ))

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth ZPow (Multiplicative (WithTop ℤ))

/--
error: failed to synthesize
  Inv (MinTropical (WithTop ℤ))

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth Inv (MinTropical (WithTop ℤ))

/--
error: failed to synthesize
  Div (MinTropical (WithTop ℤ))

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth Div (MinTropical (WithTop ℤ))

/--
error: failed to synthesize
  Pow (MinTropical (WithTop ℤ)) ℤ

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth Pow (MinTropical (WithTop ℤ)) ℤ

/--
error: failed to synthesize
  ZPow (MinTropical (WithTop ℤ))

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth ZPow (MinTropical (WithTop ℤ))

/--
error: failed to synthesize
  Inv (MaxTropical (WithTop ℤ)ᵒᵈ)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth Inv (MaxTropical (WithTop ℤ)ᵒᵈ)

/--
error: failed to synthesize
  Div (MaxTropical (WithTop ℤ)ᵒᵈ)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth Div (MaxTropical (WithTop ℤ)ᵒᵈ)

/--
error: failed to synthesize
  Pow (MaxTropical (WithTop ℤ)ᵒᵈ) ℤ

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth Pow (MaxTropical (WithTop ℤ)ᵒᵈ) ℤ

/--
error: failed to synthesize
  ZPow (MaxTropical (WithTop ℤ)ᵒᵈ)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth ZPow (MaxTropical (WithTop ℤ)ᵒᵈ)

/--
error: failed to synthesize
  Zero (MaxTropical (WithTop ℤ))

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth Zero (MaxTropical (WithTop ℤ))

/--
error: failed to synthesize
  Inv (Multiplicative (WithTop ℤ)ᵒᵈ)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth Inv (Multiplicative (WithTop ℤ)ᵒᵈ)

/--
error: failed to synthesize
  Div (Multiplicative (WithTop ℤ)ᵒᵈ)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth Div (Multiplicative (WithTop ℤ)ᵒᵈ)

/--
error: failed to synthesize
  Pow (Multiplicative (WithTop ℤ)ᵒᵈ) ℤ

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth Pow (Multiplicative (WithTop ℤ)ᵒᵈ) ℤ

/--
error: failed to synthesize
  ZPow (Multiplicative (WithTop ℤ)ᵒᵈ)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth ZPow (Multiplicative (WithTop ℤ)ᵒᵈ)

/-! ### Group controls -/

section

variable {A : Type*} [AddCommGroup A]

example (a b : A) : a - b = a + -b := sub_eq_add_neg a b
example (a : A) : (-1 : ℤ) • a = -a := neg_one_zsmul a

example (a b : Multiplicative A) : a / b = a * b ^ (-1 : ℤ) := by
  rw [zpow_neg_one, div_eq_mul_inv]

example (a b : MinTropical A) : a / b = a * b ^ (-1 : ℤ) := by
  rw [zpow_neg_one, div_eq_mul_inv]

example (a b : MaxTropical Aᵒᵈ) : a / b = a * b ^ (-1 : ℤ) := by
  rw [zpow_neg_one, div_eq_mul_inv]

example (a b : Multiplicative Aᵒᵈ) : a / b = a * b ^ (-1 : ℤ) := by
  rw [zpow_neg_one, div_eq_mul_inv]

end

example (a b : FiniteArchimedeanClass ℝ) : a - b = a + -b := sub_eq_add_neg a b

example (a b c : WithTop ℕ) : a - b ≤ c ↔ a ≤ c + b := tsub_le_iff_right

/-! ### Checked additive operations -/

example (a : ℤ) :
    Checked.neg (a : WithTop ℤ) (WithTop.isAddUnit_coe a) =
      ((-a : ℤ) : WithTop ℤ) := by simp

example (a b : ℤ) :
    Checked.sub (a : WithTop ℤ) (b : WithTop ℤ) (WithTop.isAddUnit_coe b) =
      ((a - b : ℤ) : WithTop ℤ) := by simp

example (n a : ℤ) :
    Checked.zsmul n (a : WithTop ℤ) (fun _ ↦ WithTop.isAddUnit_coe a) =
      ((n • a : ℤ) : WithTop ℤ) := by simp

example (b : WithTop ℤ) (hb : b ≠ ⊤) : Checked.sub ⊤ b (isAddUnit_iff.mpr hb) = ⊤ := by
  simp [Checked.sub_eq_add_neg]

example (a b d : WithTop ℤ) (hb : b ≠ ⊤) :
    Checked.sub a b (isAddUnit_iff.mpr hb) = d ↔ d + b = a :=
  (Checked.sub_eq_iff_eq_add (isAddUnit_iff.mpr hb)).trans eq_comm

example : ¬ IsAddUnit (⊤ : WithTop ℤ) := by simp
example : ¬ IsAddUnit (⊤ : ArchimedeanClass ℝ) := by simp

/--
error: unsolved goals
⊢ False
-/
#guard_msgs in
example : WithTop ℤ := Checked.zsmul (-1) ⊤ (by simp)

example : Checked.zsmul 0 (⊤ : WithTop ℤ) (by simp) = 0 := zero_nsmul _

example : Checked.zsmul 2 (⊤ : WithTop ℤ) (by simp) = ⊤ := (two_nsmul _).trans (top_add ⊤)

example (x : ℝ) (hx : x ≠ 0) :
    Checked.neg (ArchimedeanClass.mk x) (ArchimedeanClass.isAddUnit_mk hx.isUnit) =
      ArchimedeanClass.mk (Checked.inv x hx.isUnit) := (ArchimedeanClass.mk_inv x).symm

example (x : ℝ) (hx : IsUnit x) : ArchimedeanClass.mk (Checked.div 0 x hx) = ⊤ := by
  rw [ArchimedeanClass.mk_div, ArchimedeanClass.mk_zero, Checked.sub_eq_add_neg, top_add]

example (n : ℤ) (x : ℝ) (hx : n < 0 → IsUnit x) :
    ArchimedeanClass.mk (Checked.zpow x n hx) =
      Checked.zsmul n (ArchimedeanClass.mk x) (fun hn ↦ ArchimedeanClass.isAddUnit_mk (hx hn)) :=
  ArchimedeanClass.mk_zpow n x

example (y : ArchimedeanClass ℝ) (hy : y ≠ ⊤) :
    Checked.sub ⊤ y (isAddUnit_iff.mpr hy) = ⊤ := by
  simp [Checked.sub_eq_add_neg]

/-! ### Checked multiplicative operations -/

section

variable {A : Type*} [LinearOrderedAddCommGroupWithTop A]

example (a : Multiplicative A) (ha : a.toAdd ≠ ⊤) : ∃ b, b * a = 1 := by
  have hu : IsUnit a := Multiplicative.isUnit_iff.mpr (isAddUnit_iff.mpr ha)
  exact ⟨a⁻¹, inv_mul_cancel₀⟩

example (a : MinTropical A) (ha : a.untrop ≠ ⊤) :
    Checked.inv a (MinTropical.isUnit_iff.mpr (isAddUnit_iff.mpr ha)) * a = 1 :=
  inv_mul_cancel₀

end

example (a : MaxTropical (WithTop ℤ)) (ha : a.untrop ≠ ⊤) :
    Checked.inv a (MaxTropical.isUnit_iff.mpr (isAddUnit_iff.mpr ha)) * a = 1 :=
  inv_mul_cancel₀

example (a : Multiplicative (WithTop ℤ)ᵒᵈ) (ha : a ≠ 0) :
    Checked.inv a ha.isUnit * a = 1 :=
  inv_mul_cancel₀

example (a : MinTropical (WithTop ℤ)) (ha : a.untrop ≠ ⊤) :
    Checked.div 0 a (MinTropical.isUnit_iff.mpr (isAddUnit_iff.mpr ha)) = 0 :=
  zero_mul _

/--
error: could not synthesize default value for parameter 'ha' using tactics
---
error: an invertibility proof is required
⊢ IsUnit 0
-/
#guard_msgs in
example : MinTropical (WithTop ℤ) := Checked.inv 0

/--
error: could not synthesize default value for parameter 'hb' using tactics
---
error: an invertibility proof is required
⊢ IsUnit 0
-/
#guard_msgs in
example : MinTropical (WithTop ℤ) := Checked.div 1 0

/--
error: unsolved goals
⊢ False
-/
#guard_msgs in
example : MinTropical (WithTop ℤ) := Checked.zpow 0 (-1 : ℤ)

example : Checked.zpow (0 : MinTropical (WithTop ℤ)) (0 : ℤ) = 1 :=
  zpow_zero₀ 0

example : Checked.zpow (0 : MinTropical (WithTop ℤ)) (2 : ℤ) = 0 := by
  simp
