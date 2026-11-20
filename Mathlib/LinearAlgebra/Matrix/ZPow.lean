/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Integer powers of square matrices

The unit group `(Matrix n n R)ˣ` supplies the usual group laws for integer powers. For powers of
an ambient matrix, `Checked.zpow` requires invertibility at negative exponents. This file records
the interaction of integer powers with determinants, transposition, and symmetry.
-/

public section

namespace Matrix

variable {n : Type*} [DecidableEq n] [Fintype n] {R : Type*} [CommRing R]

@[simp]
theorem unitsMap_det_zpow (A : (Matrix n n R)ˣ) (z : ℤ) :
    Units.map detMonoidHom (A ^ z) = Units.map detMonoidHom A ^ z :=
  MonoidHom.map_zpow (Units.map (detMonoidHom (n := n) (R := R))) A z

/-- The determinant of an integer power in the matrix unit group is the corresponding integer
power of the determinant unit. -/
theorem det_coe_units_zpow (A : (Matrix n n R)ˣ) (z : ℤ) :
    det (↑(A ^ z) : Matrix n n R) = (↑(Units.map detMonoidHom A ^ z) : R) := by
  rw [← unitsMap_det_zpow]
  rfl

theorem coe_units_zpow_ne_zero [Nonempty n] [Nontrivial R]
    (A : (Matrix n n R)ˣ) (z : ℤ) : (↑(A ^ z) : Matrix n n R) ≠ 0 :=
  (A ^ z).ne_zero

@[simp]
theorem transpose_zpow (A : Matrix n n R) (z : ℤ) {hz : z < 0 → IsUnit A} :
    (A ^ z)ᵀ = Aᵀ ^ z := by
  cases z with
  | ofNat k => exact transpose_pow A k
  | negSucc k => simp only [zpow_negSucc₀, transpose_nonsing_inv, transpose_pow]

@[simp]
theorem conjTranspose_zpow [StarRing R] (A : Matrix n n R) (z : ℤ)
    {hz : z < 0 → IsUnit A} :
    (A ^ z)ᴴ = Aᴴ ^ z := by
  cases z with
  | ofNat k => exact conjTranspose_pow A k
  | negSucc k => simp only [zpow_negSucc₀, conjTranspose_nonsing_inv, conjTranspose_pow]

/-- Integer powers of a symmetric matrix are symmetric, with invertibility required for a
negative exponent. -/
theorem IsSymm.zpow {A : Matrix n n R} (hA : A.IsSymm) (z : ℤ) {hz : z < 0 → IsUnit A} :
    (A ^ z).IsSymm := by
  cases z with
  | ofNat k => exact hA.pow k
  | negSucc k =>
    rw [zpow_negSucc₀]
    exact (hA.pow (k + 1)).inv

end Matrix
