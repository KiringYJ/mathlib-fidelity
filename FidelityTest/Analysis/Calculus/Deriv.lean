module
import Mathlib

/-! Test simplification of derivatives in the fork's calculus API. -/

example : deriv Real.exp = Real.exp := by simp

example (x : ℝ) : fderivWithin ℝ (0 : ℝ → ℝ) (Set.Ici 0) x = 0 := by simp
