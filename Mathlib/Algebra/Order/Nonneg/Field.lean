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
  let u := Units.mk0 (a : α) hn
  exact {
    val := a
    inv := ⟨u.inv, (Units.inv_nonneg u).mpr a.property⟩
    val_inv := Subtype.ext u.mul_inv
    inv_val := Subtype.ext u.inv_mul }

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

@[simp]
protected theorem coe_inv (u : (Nonneg α)ˣ) :
    (u.inv : α) = (Units.map coeRingHom.toMonoidHom u).inv := rfl

@[simp]
protected theorem coe_div (a : Nonneg α) (u : (Nonneg α)ˣ) :
    ((a /ₚ u : Nonneg α) : α) = (a : α) /ₚ Units.map coeRingHom.toMonoidHom u := rfl

@[simp]
protected theorem coe_zpow (u : (Nonneg α)ˣ) (n : ℤ) :
    (((u ^ n : (Nonneg α)ˣ) : Nonneg α) : α) =
      (Units.map coeRingHom.toMonoidHom u ^ n : αˣ) := by
  exact congrArg (fun v : αˣ => (v : α)) (map_zpow (Units.map coeRingHom.toMonoidHom) u n)

end OrderedSemiring

section LinearOrderedDivisionSemiring

variable [DivisionSemiring α] [LinearOrder α] [IsStrictOrderedRing α]

instance divisionSemiring : DivisionSemiring (Nonneg α) where
  __ := (inferInstance : Semiring (Nonneg α))
  __ := (inferInstance : Nontrivial (Nonneg α))
  isUnit_of_ne_zero {a} ha := ⟨unit a ha, rfl⟩

@[simp, norm_cast] lemma coe_nnratCast (q : ℚ≥0) : ((q : Nonneg α) : α) = (q : α) :=
  map_nnratCast coeRingHom q

@[simp] lemma mk_nnratCast (q : ℚ≥0) : (⟨q, q.cast_nonneg⟩ : Nonneg α) = q :=
  Subtype.ext (coe_nnratCast q).symm

@[simp, norm_cast] lemma coe_nnqsmul (q : ℚ≥0) (a : Nonneg α) :
    (↑(q • a) : α) = (q • (a : α) : α) := by
  simp only [NNRat.smul_def, Nonneg.coe_mul, coe_nnratCast]

@[simp] lemma mk_nnqsmul (q : ℚ≥0) (a : α) (ha : 0 ≤ a) :
    (⟨q • a, nnqsmul_nonneg q ha⟩ : Nonneg α) = q • (⟨a, ha⟩ : Nonneg α) :=
  Subtype.ext (coe_nnqsmul q ⟨a, ha⟩).symm

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
