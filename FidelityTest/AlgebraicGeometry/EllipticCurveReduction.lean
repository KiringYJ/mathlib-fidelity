import Mathlib.Algebra.Field.ZMod
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction

/-! Regression tests for rational tangent directions in characteristics two and three. -/

open WeierstrassCurve

namespace EllipticCurveReduction

private lemma nodal_splits_iff {k : Type*} [Field k] (a b : k)
    (hc : (a ^ 2 + 4 * b) ^ 2 ≠ 0) :
    (WeierstrassCurve.mk a b 0 0 0).nodePolynomial.Splits ↔
      ∃ m₁ m₂ : k, m₁ ≠ m₂ ∧ m₁ ^ 2 + a * m₁ = b ∧ m₂ ^ 2 + a * m₂ = b := by
  simpa using splits_nodePolynomial_iff_of_singular
    (W := WeierstrassCurve.mk a b 0 0 0) (x := 0) (y := 0)
    (by simp [Affine.equation_zero]) (by simp [Affine.nonsingular_zero])
    (by simpa [c₄, b₂, b₄] using hc)

-- In characteristic two, the tangent polynomial is separable because the linear term is nonzero.
example : (WeierstrassCurve.mk (1 : ZMod 2) 0 0 0 0).nodePolynomial.Splits := by
  rw [nodal_splits_iff 1 0 (by decide)]
  decide

example : ¬ (WeierstrassCurve.mk (1 : ZMod 2) 1 0 0 0).nodePolynomial.Splits := by
  rw [nodal_splits_iff 1 1 (by decide)]
  decide

example : (WeierstrassCurve.mk (0 : ZMod 3) 1 0 0 0).nodePolynomial.Splits := by
  rw [nodal_splits_iff 0 1 (by decide)]
  decide

example : ¬ (WeierstrassCurve.mk (0 : ZMod 3) 2 0 0 0).nodePolynomial.Splits := by
  rw [nodal_splits_iff 0 2 (by decide)]
  decide

-- The node need not be at the origin; here it is (1, 1).
example : (WeierstrassCurve.mk (1 : ZMod 2) 1 1 0 1).nodePolynomial.Splits := by
  rw [splits_nodePolynomial_iff_of_singular (x := 1) (y := 1)
    (by rw [Affine.equation_iff']; decide)
    (by rw [Affine.nonsingular_iff', Affine.equation_iff']; decide) (by decide)]
  decide

-- A split polynomial alone is insufficient: this cuspidal reduction has only one tangent.
example : (WeierstrassCurve.mk (0 : ZMod 2) 1 0 0 0).nodePolynomial.Splits := by
  have h : (WeierstrassCurve.mk (0 : ZMod 2) 1 0 0 0).nodePolynomial = 0 := by
    simp [nodePolynomial, c₄, b₂, b₄, b₆, show (4 : ZMod 2) = 0 by decide]
  rw [h]
  exact Polynomial.Splits.zero

example : ¬ ∃ m₁ m₂ : ZMod 2, m₁ ≠ m₂ ∧ m₁ ^ 2 = 1 ∧ m₂ ^ 2 = 1 := by
  decide

end EllipticCurveReduction
