/-
Copyright (c) 2025 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.SetLike

/-! # Lemmas for the `algebra` tactic.
-/

public section

open Mathlib.Meta.NormNum

namespace Mathlib.Tactic.Algebra

section ring

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/- evalCast -/
theorem isInt_negOfNat_eq {a : A} {lit : ℕ} (h : IsInt a (Int.negOfNat lit)) :
    a = algebraMap R A (Int.rawCast (Int.negOfNat lit) + 0 : R) + 0 := by
  simp [h.out]

end ring

section semifield

variable {R A : Type*} [Semifield R] [Semifield A] [Algebra R A]

/- evalCast -/
theorem isNNRat_eq_rawCast {a : A} {n d : ℕ} (h : IsNNRat a n d) :
    a = algebraMap R A (NNRat.rawCast n d (by
      intro hd
      exact h.den_nz (by simpa using congrArg (algebraMap R A) hd)) + 0 : R) + 0 := by
  rw [add_zero, map_add, map_zero, add_zero]
  have hdA : (d : A) ≠ 0 := h.den_nz
  have hdR : (d : R) ≠ 0 := fun hd ↦ h.den_nz (by simpa using congrArg (algebraMap R A) hd)
  calc
    a = NNRat.rawCast n d h.den_nz := h.to_raw_eq
    _ = algebraMap R A (NNRat.rawCast n d hdR : R) := by
      change (n : A) / (d : A) = algebraMap R A ((n : R) / (d : R))
      simp only [map_div₀, map_natCast]

end semifield

section field

variable {R A : Type*} [Field R] [Field A] [Algebra R A]

/- evalCast -/
theorem isRat_eq_rawCast {a : A} {n d : ℕ} (h : IsRat a (.negOfNat n) d) :
    a = algebraMap R A (Rat.rawCast (.negOfNat n) d (by
      intro hd
      exact h.den_nz (by simpa using congrArg (algebraMap R A) hd)) + 0 : R) + 0 := by
  rw [add_zero, map_add, map_zero, add_zero]
  have hdA : (d : A) ≠ 0 := h.den_nz
  have hdR : (d : R) ≠ 0 := fun hd ↦ h.den_nz (by simpa using congrArg (algebraMap R A) hd)
  calc
    a = Rat.rawCast (.negOfNat n) d h.den_nz := h.to_raw_eq
    _ = algebraMap R A (Rat.rawCast (.negOfNat n) d hdR : R) := by
      change ((Int.negOfNat n : ℤ) : A) / (d : A) =
        algebraMap R A (((Int.negOfNat n : ℤ) : R) / (d : R))
      simp only [map_div₀, map_intCast, map_natCast]

end field

variable {R A : Type*} [sR : CommSemiring R] [sA : CommSemiring A] [sAlg : Algebra R A]

/- evalCast -/
theorem isNat_zero_eq {a : A} (h : IsNat a 0) : a = 0 := by
  have := h.out
  simp [this]

/- evalCast -/
theorem isNat_eq_rawCast {a : A} {lit : ℕ} (h : IsNat a lit) :
    a = algebraMap R A (lit + 0 : R) + 0 := by
  simp [h.out]

section cleanup

variable {n d : ℕ}

section cleanupSMul

theorem add_assoc_rev (a b c : R) : a + (b + c) = a + b + c := (add_assoc ..).symm
theorem mul_assoc_rev (a b c : R) : a * (b * c) = a * b * c := (mul_assoc ..).symm
theorem mul_neg {R} [Ring R] (a b : R) : a * -b = -(a * b) := by simp
theorem add_neg {R} [Ring R] (a b : R) : a + -b = a - b := (sub_eq_add_neg ..).symm
theorem nat_rawCast_0 : (Nat.rawCast 0 : R) = 0 := by simp
theorem nat_rawCast_1 : (Nat.rawCast 1 : R) = 1 := by simp
theorem nat_rawCast_2 [Nat.AtLeastTwo n] : (Nat.rawCast n : R) = OfNat.ofNat n := rfl
theorem int_rawCast_neg {R} [Ring R] : (Int.rawCast (.negOfNat n) : R) = -Nat.rawCast n := by simp
theorem nnrat_rawCast {R} [DivisionSemiring R] (hd : (d : R) ≠ 0) :
    (NNRat.rawCast n d hd : R) = Nat.rawCast n / (Nat.rawCast d : R) := by rfl
theorem rat_rawCast_neg {R} [DivisionRing R] (hd : (d : R) ≠ 0) :
    (Rat.rawCast (.negOfNat n) d hd : R) = Int.rawCast (.negOfNat n) / (Nat.rawCast d : R) := by
  rfl

end cleanupSMul
section cleanupConsts

theorem ofNat_smul {R A} [CommSemiring R] [CommSemiring A] [Algebra R A]
    [n.AtLeastTwo] {a : A} :
    (ofNat(n) : R) • a = ofNat(n) * a := by
  simp_rw [← nat_rawCast_2]
  simp [Nat.cast_smul_eq_nsmul]

theorem neg_ofNat_smul {R A} [CommRing R] [CommRing A] [Algebra R A] {a : A} [n.AtLeastTwo] :
    (- ofNat(n) : R) • a = - (ofNat(n)) * a := by
  simpa [← nat_rawCast_2] using! ofNat_smul

theorem neg_1_smul {R A} [CommRing R] [CommRing A] [Algebra R A] {a : A} :
    (-1 : R) • a = - a := by
  simp

/-- The image of an invertible numeral of the scalar ring is an invertible numeral. -/
theorem isUnit_ofNat_algebraMap {R A} [CommSemiring R] [Semiring A] [Algebra R A]
    [d.AtLeastTwo] (hd : IsUnit (ofNat(d) : R)) : IsUnit (ofNat(d) : A) :=
  map_ofNat (algebraMap R A) d ▸ hd.map (algebraMap R A)

theorem nnRat_ofNat_smul_1 {R A} [Semifield R] [Semifield A] [Algebra R A] {a : A}
    [d.AtLeastTwo] {hd : IsUnit (ofNat(d) : R)} :
    (1 / ofNat(d) : R) • a = Checked.div 1 (ofNat(d) : A) (isUnit_ofNat_algebraMap hd) * a := by
  simp only [Algebra.smul_def, map_div₀, map_one, map_ofNat]

theorem nnRat_ofNat_smul_2 {R A} [Semifield R] [Semifield A] [Algebra R A] {a : A}
    [n.AtLeastTwo] [d.AtLeastTwo] {hd : IsUnit (ofNat(d) : R)} :
    (ofNat(n) / ofNat(d) : R) • a =
      Checked.div (ofNat(n) : A) (ofNat(d) : A) (isUnit_ofNat_algebraMap hd) * a := by
  simp only [Algebra.smul_def, map_div₀, map_ofNat]

theorem rat_ofNat_smul_1 {R A} [Field R] [Field A] [Algebra R A] {a : A}
    [d.AtLeastTwo] {hd : IsUnit (ofNat(d) : R)} :
    ((-1) / ofNat(d) : R) • a =
      Checked.div (-1 : A) (ofNat(d) : A) (isUnit_ofNat_algebraMap hd) * a := by
  simp only [Algebra.smul_def, map_div₀, map_neg, map_one, map_ofNat]

theorem rat_ofNat_smul_2 {R A} [Field R] [Field A] [Algebra R A] {a : A}
    [n.AtLeastTwo] [d.AtLeastTwo] {hd : IsUnit (ofNat(d) : R)} :
    ((-ofNat(n)) / ofNat(d) : R) • a =
      Checked.div (-ofNat(n) : A) (ofNat(d) : A) (isUnit_ofNat_algebraMap hd) * a := by
  simp only [Algebra.smul_def, map_div₀, map_neg, map_ofNat]

end cleanupConsts

end cleanup

section equateScalars

/- ExProd.equateZero -/
theorem smul_one_eq_zero {r : R} (h : r = 0) :
    r • (1 : A) = 0 := by
  simp [h]

/- ExProd.equateZero -/
theorem add_eq_zero {a b : A} (ha : a = 0) (hb : b = 0) :
    a + b = 0 := by
  simp [ha, hb]

/- ExProd.equateScalarsProd -/
theorem smul_one_eq_smul_one' {r s : R} (h : r = s) :
    r • (1 : A) = s • 1 := by
  simp [h]

/- equateScalarsSum -/
theorem add_eq_of_zero_add {a₁ a₂ b₁ b₂ : A}
    (ha₁ : a₁ = 0) (ha₂ : a₂ = b₁ + b₂) :
    a₁ + a₂ = b₁ + b₂ := by
  subst_vars
  simp

/- equateScalarsSum -/
theorem add_eq_of_add_zero {a₁ a₂ b₁ b₂ : A}
    (hb₁ : b₁ = 0) (ha : a₁ + a₂ = b₂) :
    a₁ + a₂ = b₁ + b₂ := by
  subst_vars
  simp

/- equateScalarsSum -/
theorem add_eq_of_eq_eq {a₁ a₂ b₁ b₂ : A}
    (ha : a₁ = b₁) (hb : a₂ = b₂) :
    a₁ + a₂ = b₁ + b₂ := by
  subst_vars
  rfl

/- matchScalarsAux -/
omit sA in
theorem eq_trans_trans {e₁ e₂ a b : A}
    (ha : e₁ = a) (hb : e₂ = b) (hab : a = b) :
    e₁ = e₂ := by
  subst_vars
  rfl

/- ExProd.equateScalarsProd -/
theorem mul_eq_mul_of_eq {c a b : A}
    (h : a = b) :
    c * a = c * b := by
  simp [h]

end equateScalars

section RingCompute

/- RingCompute.add -/
theorem add_algebraMap {r s t : R} (h : r + s = t) :
    algebraMap R A r + algebraMap R A s = algebraMap R A t := by
  rw [← map_add, h]

/- RingCompute.add -/
theorem add_algebraMap_isNat_zero {r s : R} (h : r + s = 0) :
    IsNat (algebraMap R A r + algebraMap R A s) 0 := by
  rw [← map_add, h, map_zero]
  exact ⟨by simp⟩

/- RingCompute.cast -/
theorem cast_zero_smul_eq_zero_mul {R' : Type*} [HSMul R' A A] {r' : R'} {r : R}
    (hr : r = 0) (h_smul : ∀ (a : A), r • a = r' • a) (a : A) :
    r' • a = (0 : A) * a := by
  simp [← h_smul, hr]

/- RingCompute.cast -/
theorem cast_smul_eq_mul {R' : Type*} [HSMul R' A A] {r' : R'} {r r'' : R}
    (hr : r = r'') (h_smul : ∀ (a : A), r • a = r' • a) (a : A) :
    r' • a = (algebraMap R A r'' + 0) * a := by
  simp [← h_smul, ← hr, Algebra.smul_def r a]

/- RingCompute.neg -/
theorem neg_algebraMap {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {r t : R} (h : -r = t) :
    -(algebraMap R A r) = algebraMap R A t := by
  rw [← map_neg, h]

/- RingCompute.pow -/
theorem pow_algebraMap {r s : R} {b : ℕ} (h : r ^ b = s) :
    (algebraMap R A r) ^ b = algebraMap R A s := by
  rw [← map_pow, h]

/- RingCompute.inv -/
theorem inv_algebraMap {R A : Type*} [Semifield R] [Semifield A] [Algebra R A]
    {r s : R} (hr : IsUnit r) (h : Checked.inv r hr = s) :
    Checked.inv (algebraMap R A r) (hr.map (algebraMap R A)) = algebraMap R A s := by
  subst s
  change ↑((hr.map (algebraMap R A)).unit⁻¹) = algebraMap R A ↑hr.unit⁻¹
  have hu : (hr.map (algebraMap R A)).unit =
      Units.map (algebraMap R A).toMonoidHom hr.unit := Units.ext rfl
  rw [hu]
  exact Units.coe_map_inv (algebraMap R A).toMonoidHom hr.unit

/- RingCompute.isOne -/
theorem isOne_algebraMap {r : R} (h : IsNat r 1) :
    IsNat (algebraMap R A (r + 0)) 1 := by
  simp only [h.out, Nat.cast_one, add_zero, map_one]
  exact ⟨by simp⟩

end RingCompute

end Mathlib.Tactic.Algebra
