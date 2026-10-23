/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ZPow

/-!
# Exact-domain matrix inverses

These tests ensure that square matrices do not acquire a total inverse or integer power. A matrix
with unit determinant has its canonical inverse, its unique linear-system solution, Cramer's rule,
and integer powers after it is bundled as a unit.
-/

namespace MatrixNonsingularInverseStrict

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [CommRing R]

/-! Raw matrices have no inverse, division, or integer-power operation, even over a field. -/

/--
error: failed to synthesize instance of type class
  Inv (Matrix (Fin 1) (Fin 1) ℚ)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (A : Matrix (Fin 1) (Fin 1) ℚ) : Matrix (Fin 1) (Fin 1) ℚ := A⁻¹

/--
error: failed to synthesize instance of type class
  HDiv (Matrix (Fin 1) (Fin 1) ℚ) (Matrix (Fin 1) (Fin 1) ℚ) (Matrix (Fin 1) (Fin 1) ℚ)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (A B : Matrix (Fin 1) (Fin 1) ℚ) : Matrix (Fin 1) (Fin 1) ℚ := A / B

/--
error: failed to synthesize instance of type class
  HPow (Matrix (Fin 1) (Fin 1) ℚ) ℤ (Matrix (Fin 1) (Fin 1) ℚ)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (A : Matrix (Fin 1) (Fin 1) ℚ) : Matrix (Fin 1) (Fin 1) ℚ := A ^ (-1 : ℤ)

/-! A nonzero determinant over a general ring is insufficient: `2` is not a unit in `ℤ`. -/

example : ¬IsUnit ((!![2] : Matrix (Fin 1) (Fin 1) ℤ).det) := by
  simp [Matrix.det_fin_one, isUnit_iff]

example (A : Matrix n n R) (h : IsUnit A.det) :
    A * nonsingularInverse A h = 1 :=
  mul_nonsingularInverse A h

example (A : Matrix n n R) (h : IsUnit A.det) (b : n → R) :
    ∃! x, A *ᵥ x = b := by
  refine ⟨nonsingularInverse A h *ᵥ b, mulVec_nonsingularInverse_mulVec A h b, ?_⟩
  intro y hy
  exact (mulVec_eq_iff_eq_nonsingularInverse_mulVec A h y b).mp hy

example (A : Matrix n n R) (h : IsUnit A.det) (b : n → R) :
    A.det • nonsingularInverse A h *ᵥ b = cramer A b :=
  det_smul_nonsingularInverse_mulVec_eq_cramer A b h

example (A : Matrix n n R) (h : IsUnit A.det) (z : ℤ) :
    Units.map detMonoidHom (unitOfIsUnitDet A h ^ z) =
      Units.map detMonoidHom (unitOfIsUnitDet A h) ^ z :=
  unitsMap_det_zpow (unitOfIsUnitDet A h) z

example (A : Matrix n n R) (h₁ h₂ : IsUnit A.det) :
    nonsingularInverse A h₁ = nonsingularInverse A h₂ := by
  cases Subsingleton.elim h₁ h₂
  rfl

example (A : Matrix Empty Empty R) :
    A * nonsingularInverse A (by simp) = 1 :=
  mul_nonsingularInverse A (by simp)

example [Subsingleton R] (A : Matrix n n R) :
    A * nonsingularInverse A (by simpa only [Subsingleton.elim A.det 1] using isUnit_one) = 1 :=
  mul_nonsingularInverse A _

end MatrixNonsingularInverseStrict
