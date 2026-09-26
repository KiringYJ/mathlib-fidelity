import Mathlib.NumberTheory.Height.NumberField
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Absolute heights on algebraic inputs

The ordinary height operations require algebraicity over `ℚ`. Rational numbers, including
nonintegral rationals, remain valid inputs, while a transcendental rational-function generator
cannot supply the required evidence. Boundary simplification is independent of the supplied proof.
-/

open NumberField

section AlgebraicElement

variable {K : Type*} [Field K] [CharZero K] (x : K) (hx hy : IsIntegral ℚ x)

example : absMulHeight₁ x hx = absMulHeight₁ x hy := rfl

example : absLogHeight₁ x hx = absLogHeight₁ x hy := rfl

example : absLogHeight₁ x hx = Real.log (absMulHeight₁ x hx) := rfl

example : 0 < absMulHeight₁ x hx := absMulHeight₁_pos x hx

example : 0 ≤ absLogHeight₁ x hx := Real.log_nonneg (one_le_absMulHeight₁ x hx)

example (h0 : IsIntegral ℚ (0 : K)) (h1 : IsIntegral ℚ (1 : K)) :
    absMulHeight₁ (0 : K) h0 = 1 ∧ absMulHeight₁ (1 : K) h1 = 1 ∧
      absLogHeight₁ (0 : K) h0 = 0 ∧ absLogHeight₁ (1 : K) h1 = 0 := by
  simp

set_option linter.unusedVariables false in
example : True := by
  fail_if_success
    let _ : ℝ := absMulHeight₁ x
  fail_if_success
    let _ : ℝ := absLogHeight₁ x
  trivial

end AlgebraicElement

-- Number-field elements obtain the evidence from existing algebraicity instances.
example {K : Type*} [Field K] [NumberField K] (x : K) :
    0 < absMulHeight₁ x (Algebra.IsIntegral.isIntegral x) :=
  absMulHeight₁_pos x _

-- Algebraicity over ℚ does not impose integrality over ℤ.
example : 0 < absMulHeight₁ (1 / 2 : ℚ) (isIntegral_algebraMap (R := ℚ) (A := ℚ)) :=
  absMulHeight₁_pos _ _

example : ¬ IsIntegral ℚ (RatFunc.X : RatFunc ℚ) := by
  intro hx
  apply RatFunc.transcendental_X (K := ℚ)
  convert hx.isAlgebraic using 1
  exact Subsingleton.elim _ _

example : True := by
  fail_if_success
    let _ : ℝ := absMulHeight₁ (RatFunc.X : RatFunc ℚ)
  fail_if_success
    let _ : ℝ := absLogHeight₁ (RatFunc.X : RatFunc ℚ)
  trivial
