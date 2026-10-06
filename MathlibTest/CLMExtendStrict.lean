import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Continuous extensions need their evidence

These tests ensure that the continuous extension of a continuous linear map along a map takes the
density of its range and its uniform inducing property, and that the extension of a linear map by
a norm estimate takes the density and the estimate, so that neither falls back to the zero map.
-/

/-- info: Unknown constant `LinearMap.compLeftInverse_apply_of_bdd` -/
#guard_msgs in
#check_failure LinearMap.compLeftInverse_apply_of_bdd

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace F]

/--
error: Type mismatch
  f.extend e
has type
  DenseRange ⇑e → IsUniformInducing ⇑e → E →L[ℝ] F
but is expected to have type
  E →L[ℝ] F
-/
#guard_msgs in
noncomputable example (f : E →L[ℝ] F) (e : E →L[ℝ] E) : E →L[ℝ] F := f.extend e

/-- The extension along the identity is the map itself. -/
example (f : E →L[ℝ] F) :
    f.extend (ContinuousLinearMap.id ℝ E) (by simpa using denseRange_id)
      (by simpa using IsUniformInducing.id) = f :=
  ContinuousLinearMap.extend_unique _ _ _ _ (by ext; simp)

/--
error: Type mismatch
  f.extendOfNorm e
has type
  DenseRange ⇑e → (∃ C, ∀ (x : E), ‖f x‖ ≤ C * ‖e x‖) → E →L[ℝ] F
but is expected to have type
  E →L[ℝ] F
-/
#guard_msgs in
noncomputable example (f : E →ₗ[ℝ] F) (e : E →ₗ[ℝ] E) : E →L[ℝ] F := f.extendOfNorm e
