/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Order.Field.Canonical
public import Mathlib.Algebra.Order.Nonneg.Ring
public import Mathlib.Algebra.Order.Positive.Ring
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.Rat.Cast.CharZero

/-!
# Semifield structure on the type of nonnegative elements

This file defines instances and prove some properties about the nonnegative elements
`Nonneg α` of an arbitrary type `α`.

This is used to derive algebraic structures on `ℝ≥0` and `ℚ≥0` automatically.
-/

@[expose] public section

assert_not_exists abs_inv

variable {α : Type*}

section NNRat
variable [DivisionSemiring α] [LinearOrder α] [IsStrictOrderedRing α] {a : α}

lemma NNRat.cast_nonneg (q : ℚ≥0) : 0 ≤ (q : α) := by
  apply nonneg_of_mul_nonneg_left (b := (q.den : α))
  · rw [NNRat.cast_mul_den]
    exact Nat.cast_nonneg _
  · exact Nat.cast_pos.mpr q.den_pos

lemma nnqsmul_nonneg (q : ℚ≥0) (ha : 0 ≤ a) : 0 ≤ q • a := by
  rw [NNRat.smul_def]; exact mul_nonneg q.cast_nonneg ha

end NNRat

namespace Nonneg

/-- Lift a nonnegative nonzero scalar to a unit of the nonnegative elements. -/
noncomputable def unit [DivisionSemiring α] [PartialOrder α] [IsStrictOrderedRing α]
    [PosMulReflectLT α] (a : Nonneg α) (ha : a ≠ 0) : (Nonneg α)ˣ := by
  have hn : (a : α) ≠ 0 := fun h => ha (Subtype.ext h)
  exact {
    val := a
    inv := ⟨(a : α)⁻¹, inv_nonneg.2 a.property⟩
    val_inv := Subtype.ext mul_inv_cancel₀
    inv_val := Subtype.ext inv_mul_cancel₀ }

@[simp] theorem coe_unit [DivisionSemiring α] [PartialOrder α] [IsStrictOrderedRing α]
    [PosMulReflectLT α] (a : Nonneg α) (ha : a ≠ 0) : (unit a ha : Nonneg α) = a := rfl

/-- In an ordered field, the units of the nonnegative elements are the positive elements. -/
@[simps]
noncomputable def unitsEquivPos (R : Type*) [DivisionSemiring R] [PartialOrder R]
    [IsStrictOrderedRing R] [PosMulReflectLT R] :
    (Nonneg R)ˣ ≃* { r : R // 0 < r } where
  toFun r := ⟨r, lt_of_le_of_ne r.1.2 (Subtype.val_injective.ne r.ne_zero.symm)⟩
  invFun r := unit ⟨r.1, r.2.le⟩ (fun h => r.2.ne' (congrArg Subtype.val h))
  left_inv r := by ext; rfl
  right_inv r := by ext; rfl
  map_mul' _ _ := rfl

section OrderedSemiring
variable [Semiring α] [PartialOrder α] [ZeroLEOneClass α] [AddLeftMono α] [PosMulMono α]

/-- The value of an invertible nonnegative element is invertible. -/
theorem isUnit_coe {a : Nonneg α} (ha : IsUnit a) : IsUnit (a : α) := ha.map coeRingHom

/- Evidence rule: the value of an invertible nonnegative element is invertible. -/
macro_rules | `(tactic| checked_unit) => `(tactic|
    solve
    | assumption
    | ((with_reducible apply Nonneg.isUnit_coe); checked_unit))

@[simp, norm_cast]
protected theorem coe_inv (a : Nonneg α) {ha : IsUnit a} : ((a⁻¹ : Nonneg α) : α) = (a : α)⁻¹ :=
  Eq.symm <| inv_eq_of_mul_eq_one_right₀ <| map_mul_eq_one coeRingHom mul_inv_cancel₀

@[simp, norm_cast]
protected theorem coe_div (a b : Nonneg α) {hb : IsUnit b} :
    ((Checked.div a b hb : Nonneg α) : α) = Checked.div (a : α) (b : α) (isUnit_coe hb) := by
  rw [div_eq_mul_inv₀, Nonneg.coe_mul, Nonneg.coe_inv, div_eq_mul_inv₀]

@[simp, norm_cast]
protected theorem coe_zpow (a : Nonneg α) (n : ℤ) {h : n < 0 → IsUnit a} :
    ((a ^ n : Nonneg α) : α) = (a : α) ^ n := by
  cases n with
  | ofNat k => exact Nonneg.coe_pow a k
  | negSucc k =>
    rw [zpow_negSucc₀, Nonneg.coe_inv, zpow_negSucc₀ (a : α) k]
    simp only [Nonneg.coe_pow]

end OrderedSemiring

section LinearOrderedDivisionSemiring

variable [DivisionSemiring α] [LinearOrder α] [IsStrictOrderedRing α] {x y : α}

@[simp]
theorem inv_mk (hx : 0 ≤ x) {h : IsUnit (⟨x, hx⟩ : Nonneg α)} :
    (⟨x, hx⟩ : Nonneg α)⁻¹ = ⟨Checked.inv x (isUnit_coe h), inv_nonneg.2 hx⟩ :=
  Subtype.ext (Nonneg.coe_inv ⟨x, hx⟩)

@[simp]
theorem mk_div_mk (hx : 0 ≤ x) (hy : 0 ≤ y) {h : IsUnit (⟨y, hy⟩ : Nonneg α)} :
    Checked.div (⟨x, hx⟩ : Nonneg α) ⟨y, hy⟩ h =
      ⟨Checked.div x y (isUnit_coe h), div_nonneg hx hy⟩ :=
  Subtype.ext (Nonneg.coe_div ⟨x, hx⟩ ⟨y, hy⟩)

@[simp]
theorem mk_zpow (hx : 0 ≤ x) (n : ℤ) {h : n < 0 → IsUnit (⟨x, hx⟩ : Nonneg α)} :
    (⟨x, hx⟩ : Nonneg α) ^ n =
      ⟨Checked.zpow x n fun hn ↦ isUnit_coe (h hn), zpow_nonneg hx n⟩ :=
  Subtype.ext (Nonneg.coe_zpow ⟨x, hx⟩ n)

/-- The nonnegative elements form a division semiring. Its embedding of `ℚ≥0` and its action
of `ℚ≥0` are those of `α`. -/
instance divisionSemiring : DivisionSemiring (Nonneg α) where
  __ := (inferInstance : Semiring (Nonneg α))
  __ := (inferInstance : Nontrivial (Nonneg α))
  isUnit_of_ne_zero {a} ha := ⟨unit a ha, rfl⟩
  nnratCastOfCharZero _ q := ⟨q, q.cast_nonneg⟩
  nnratCastOfCharZero_mul_den _ q := Subtype.ext (NNRat.cast_mul_den q)
  nnqsmulOfCharZero _ q a := ⟨q • (a : α), nnqsmul_nonneg q a.2⟩
  nnqsmulOfCharZero_eq_mul _ q a := Subtype.ext (NNRat.smul_def q (a : α))

@[simp, norm_cast] lemma coe_nnratCast (q : ℚ≥0) : ((q : Nonneg α) : α) = (q : α) := rfl

@[simp] lemma mk_nnratCast (q : ℚ≥0) : (⟨q, q.cast_nonneg⟩ : Nonneg α) = q := rfl

@[simp, norm_cast] lemma coe_nnqsmul (q : ℚ≥0) (a : Nonneg α) :
    (↑(q • a) : α) = (q • (a : α) : α) := rfl

@[simp] lemma mk_nnqsmul (q : ℚ≥0) (a : α) (ha : 0 ≤ a) :
    (⟨q • a, nnqsmul_nonneg q ha⟩ : Nonneg α) = q • (⟨a, ha⟩ : Nonneg α) := rfl

end LinearOrderedDivisionSemiring

section LinearOrderedSemifield

variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] {x y : α}

instance semifield : Semifield { x : α // 0 ≤ x } := fast_instance% {
  __ := divisionSemiring
  mul_comm := mul_comm
}

end LinearOrderedSemifield

instance linearOrderedCommGroupWithZero [Field α] [LinearOrder α] [IsStrictOrderedRing α] :
    LinearOrderedCommGroupWithZero (Nonneg α) :=
  fast_instance% CanonicallyOrderedAdd.toLinearOrderedCommGroupWithZero

end Nonneg
