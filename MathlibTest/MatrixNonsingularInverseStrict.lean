/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ZPow

/-!
# Exact-domain matrix inverses

These tests ensure that square matrices do not acquire a total inverse, quotient or integer power.
`A⁻¹`, `Checked.div A B` and `A ^ (-1 : ℤ)` are operations of the group of units of the matrix ring: they
require invertibility evidence, which is found from `IsUnit A` or `IsUnit A.det`, and over a field
also from `A.det ≠ 0`. An invertible matrix has its canonical inverse, its unique linear-system
solution, Cramer's rule, and integer powers.
-/

namespace MatrixNonsingularInverseStrict

open Matrix

/-- error: failed to synthesize
  Inv (Matrix (Fin 1) (Fin 1) ℚ)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. -/
#guard_msgs in
#synth Inv (Matrix (Fin 1) (Fin 1) ℚ)

/-- error: failed to synthesize
  Div (Matrix (Fin 1) (Fin 1) ℚ)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. -/
#guard_msgs in
#synth Div (Matrix (Fin 1) (Fin 1) ℚ)

/-- error: failed to synthesize
  Pow (Matrix (Fin 1) (Fin 1) ℚ) ℤ

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command. -/
#guard_msgs in
#synth Pow (Matrix (Fin 1) (Fin 1) ℚ) ℤ

/-! Without invertibility evidence a raw matrix has no inverse, quotient or negative power, even
over a field. The failure names the missing obligation. -/

/--
error: could not synthesize default value for parameter 'ha' using tactics
---
error: an invertibility proof is required
A : Matrix (Fin 1) (Fin 1) ℚ
⊢ IsUnit A
-/
#guard_msgs in
noncomputable example (A : Matrix (Fin 1) (Fin 1) ℚ) : Matrix (Fin 1) (Fin 1) ℚ := A⁻¹

/--
error: could not synthesize default value for parameter 'hb' using tactics
---
error: an invertibility proof is required
A B : Matrix (Fin 1) (Fin 1) ℚ
⊢ IsUnit B
-/
#guard_msgs in
noncomputable example (A B : Matrix (Fin 1) (Fin 1) ℚ) : Matrix (Fin 1) (Fin 1) ℚ :=
  Checked.div A B

/--
error: unsolved goals
A : Matrix (Fin 1) (Fin 1) ℚ
⊢ IsUnit A
-/
#guard_msgs in
noncomputable example (A : Matrix (Fin 1) (Fin 1) ℚ) : Matrix (Fin 1) (Fin 1) ℚ := A ^ (-1 : ℤ)

/-! A nonzero determinant over a general ring is insufficient: `2` is not a unit in `ℤ`. -/

example : ¬IsUnit ((!![2] : Matrix (Fin 1) (Fin 1) ℤ).det) := by
  simp [Int.isUnit_iff]

/--
error: could not synthesize default value for parameter 'ha' using tactics
---
error: an invertibility proof is required
A : Matrix (Fin 1) (Fin 1) ℤ
h : A.det ≠ 0
⊢ IsUnit A
-/
#guard_msgs in
noncomputable example (A : Matrix (Fin 1) (Fin 1) ℤ) (h : A.det ≠ 0) :
    Matrix (Fin 1) (Fin 1) ℤ :=
  A⁻¹

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [CommRing R]

/-! The evidence is found from a unit determinant and, over a field, from a nonzero one. -/

example (A : Matrix n n R) (h : IsUnit A.det) : A * A⁻¹ = 1 :=
  mul_inv_cancel₀

example {K : Type*} [Field K] (A : Matrix n n K) (h : A.det ≠ 0) : A⁻¹ * A = 1 :=
  inv_mul_cancel₀

example (A : Matrix n n R) (h : IsUnit A.det) : A⁻¹ = A.det⁻¹ • A.adjugate :=
  inv_def A

/-! Cramer's rule, and the unique solution of a linear system. -/

example (A : Matrix n n R) (h : IsUnit A.det) (b : n → R) :
    ∃! x, A *ᵥ x = b :=
  ⟨A⁻¹ *ᵥ b, mulVec_nonsing_inv_mulVec A b,
    fun y hy ↦ (mulVec_eq_iff_eq_nonsing_inv_mulVec A y b).mp hy⟩

example (A : Matrix n n R) (h : IsUnit A.det) (b : n → R) :
    A.det • A⁻¹ *ᵥ b = cramer A b :=
  det_smul_inv_mulVec_eq_cramer A b

/-! Integer powers of a matrix with a unit determinant. -/

example (A : Matrix n n R) (h : IsUnit A.det) (z : ℤ) :
    Units.map detMonoidHom (nonsingInvUnit A h ^ z) =
      Units.map detMonoidHom (nonsingInvUnit A h) ^ z :=
  unitsMap_det_zpow (nonsingInvUnit A h) z

/-! Transposition and symmetry for checked integer powers. -/

example : ((0 : Matrix (Fin 2) (Fin 2) ℤ) ^ (2 : ℤ)).IsSymm := by
  have h : (0 : Matrix (Fin 2) (Fin 2) ℤ).IsSymm := by simp [Matrix.IsSymm]
  exact h.zpow 2

example (A : Matrix n n R) (hA : IsUnit A) : (A ^ (-3 : ℤ))ᵀ = Aᵀ ^ (-3 : ℤ) := by simp

example [StarRing R] (A : Matrix n n R) (z : ℤ) (hz : z < 0 → IsUnit A) :
    (A ^ z)ᴴ = Aᴴ ^ z := by simp

/-! Different proofs of invertibility give the same inverse. -/

example (A : Matrix n n R) (h₁ h₂ : IsUnit A) : Checked.inv A h₁ = Checked.inv A h₂ :=
  rfl

/-! Empty dimensions and trivial coefficient rings. -/

example (A : Matrix Empty Empty R) :
    A * Checked.inv A ((isUnit_iff_isUnit_det A).2 (by simp)) = 1 :=
  mul_inv_cancel₀

example [Subsingleton R] (A : Matrix n n R) : A * Checked.inv A (isUnit_of_subsingleton A) = 1 :=
  mul_inv_cancel₀

end MatrixNonsingularInverseStrict
