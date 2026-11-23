import Mathlib.Analysis.Distribution.Distribution
import Mathlib.Analysis.Distribution.FourierMultiplier

/-!
# Integration against a function and multiplication take their evidence

These tests ensure that integration of test functions against a function takes the integrability
of the function, that multiplication of Schwartz functions and tempered distributions by a function
and the Fourier multipliers take the temperate growth of the function, and that
`Measure.integrablePower` is the least integrable exponent, so that none of these operations is the
zero map or a chosen value outside its domain.
-/

open MeasureTheory SchwartzMap

/-- info: Unknown constant `TestFunction.integralAgainstBilinCLM_eq_zero` -/
#guard_msgs in
#check_failure TestFunction.integralAgainstBilinCLM_eq_zero

/-- info: Unknown constant `Distribution.ofFun_eq_zero` -/
#guard_msgs in
#check_failure Distribution.ofFun_eq_zero

/-- info: Unknown constant `Distribution.ofFun_apply_eq_ite` -/
#guard_msgs in
#check_failure Distribution.ofFun_apply_eq_ite

/-! The exponential has no temperate growth, so it is not a multiplier on Schwartz space. -/

/--
error: could not synthesize default value for parameter 'hg' using tactics
---
error: `fun_prop` was unable to prove `Function.HasTemperateGrowth fun x => Real.exp x`

Issues:
  No theorems found for `Real.exp` in order to prove `Function.HasTemperateGrowth fun x => Real.exp x`
-/
#guard_msgs in
noncomputable example : 𝓢(ℝ, ℝ) →L[ℝ] 𝓢(ℝ, ℝ) := smulLeftCLM ℝ (fun x : ℝ ↦ Real.exp x)

/-! Multipliers of temperate growth are found by `fun_prop`. -/

noncomputable example : 𝓢(ℝ, ℝ) →L[ℝ] 𝓢(ℝ, ℝ) := smulLeftCLM ℝ (fun x : ℝ ↦ x ^ 2)

example (f : 𝓢(ℝ, ℝ)) (x : ℝ) : (smulLeftCLM ℝ (fun x : ℝ ↦ x ^ 2)) f x = x ^ 2 • f x := by
  simp

/-! The integrable power of a measure of temperate growth is the least integrable exponent. -/

example (μ : Measure ℝ) [μ.HasTemperateGrowth] {l : ℕ}
    (hl : Integrable (fun x : ℝ ↦ (1 + ‖x‖) ^ (- (l : ℝ))) μ) : μ.integrablePower ≤ l :=
  Measure.integrablePower_le hl
