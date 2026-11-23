import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

/-!
# The affine span of two points is not called a line

The affine span of two points is written and displayed as `affineSpan k {p₁, p₂}`. When the points
coincide it is a single point, so no notation presents it as a line.
-/

variable {k V P : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P] (p₁ p₂ : P)

/-- info: affineSpan k {p₁, p₂} : AffineSubspace k P -/
#guard_msgs in
#check affineSpan k {p₁, p₂}

example : p₁ ∈ affineSpan k {p₁, p₂} := left_mem_affineSpan_pair k p₁ p₂

example : p₂ ∈ affineSpan k {p₁, p₂} := right_mem_affineSpan_pair k p₁ p₂

/-! The span of a repeated point is that point. -/

example : (affineSpan k {p₁, p₁} : Set P) = {p₁} := by simp
