/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Integer powers of invertible square matrices

Integer powers of a square matrix are defined on the unit group `(Matrix n n R)ˣ`. Negative powers
therefore carry invertibility in their type. There is no integer-power operation on every square
matrix and no singular-matrix fallback.

The group API supplies the usual laws for integer powers. This file records the matrix-specific
interaction with the determinant.
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

end Matrix
