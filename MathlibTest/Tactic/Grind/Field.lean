import Mathlib

local grind_pattern div_eq_mul_inv₀ => Checked.div a b hb
local grind_pattern mul_inv_cancel₀ => Checked.inv a ha

example (x y : ℝ) (h : x ≠ y) : (x^2 - y^2)/(x - y) = x + y := by grind
example (x y : ℝ) (h : (x + y)^2 ≠ 0) : (x^2 - y^2)/(x + y) = x - y := by grind
