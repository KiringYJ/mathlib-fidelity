/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
import Mathlib.Algebra.Lie.Weights.RootSystem

/-!
# Coroots exist only for roots

These tests ensure that the coroot `2 • (α h_α)⁻¹ • h_α` of a weight `α` requires evidence that
`α h_α` is invertible, which over a field of characteristic zero holds exactly for the roots, so
that the zero weight no longer has the coroot `0`. The evidence is found from a hypothesis that
the weight is nonzero and for the elements of `H.root`. The reflection along a weight needs the
weight to be a root.
-/

namespace LieCorootStrict

open LieModule LieAlgebra LieAlgebra.IsKilling

/-- info: Unknown constant `LieAlgebra.IsKilling.coroot_zero` -/
#guard_msgs in
#check_failure LieAlgebra.IsKilling.coroot_zero

/-- info: Unknown constant `LieAlgebra.IsKilling.coroot_eq_zero_iff` -/
#guard_msgs in
#check_failure LieAlgebra.IsKilling.coroot_eq_zero_iff

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [IsKilling K L]
  [FiniteDimensional K L] {H : LieSubalgebra K L} [H.IsCartanSubalgebra]
  [IsTriangularizable K H L]

/-! An arbitrary weight has no coroot; the failure names the missing obligation. -/

/--
error: could not synthesize default value for parameter 'hα' using tactics
---
error: an invertibility proof is required
K : Type u_1
L : Type u_2
inst✝⁷ : Field K
inst✝⁶ : CharZero K
inst✝⁵ : LieRing L
inst✝⁴ : LieAlgebra K L
inst✝³ : IsKilling K L
inst✝² : FiniteDimensional K L
H : LieSubalgebra K L
inst✝¹ : H.IsCartanSubalgebra
inst✝ : IsTriangularizable K (↥H) L
α : Weight K (↥H) L
⊢ IsUnit (α ((cartanEquivDual H).symm (Weight.toLinear K (↥H) L α)))
-/
#guard_msgs in
noncomputable example (α : Weight K H L) : H := coroot α

/--
error: Type mismatch
  reflectRoot α β
has type
  α.IsNonZero → Weight K (↥H) L
but is expected to have type
  Weight K (↥H) L
-/
#guard_msgs in
example (α β : Weight K H L) : Weight K H L := reflectRoot α β

/-! The evidence is found for a root and for an element of `H.root`. -/

noncomputable example (α : Weight K H L) (hα : α.IsNonZero) : H := coroot α

noncomputable example (α : H.root) : H := coroot α.1

example (α : Weight K H L) (hα : α.IsNonZero) : α (coroot α) = 2 := root_apply_coroot hα

example (α : Weight K H L) (hα : α.IsNonZero) : coroot α ≠ 0 := coroot_ne_zero hα

example (α : Weight K H L) (hα : α.IsNonZero) (hα' : (-α).IsNonZero) :
    coroot (-α) = -coroot α := by
  simp

example (α : H.root) : (rootSystem H).coroot α = coroot α.1 := rootSystem_coroot_apply H α

example (α β : Weight K H L) (hα : α.IsNonZero) (hβ : β.IsNonZero) :
    (reflectRoot α β hα).IsNonZero :=
  reflectRoot_isNonZero α β hα hβ

end LieCorootStrict
