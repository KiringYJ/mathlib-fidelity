/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.NormNum.Pow

variable {K : Type*}

section DivisionSemiring
variable [DivisionSemiring K]

example : (0 : K) ^ (0 : ℤ) = 1 := by norm_num
example : (0 : K) ^ (3 : ℤ) = 0 := by norm_num
example : (2 : K) ^ (3 : ℤ) = 8 := by norm_num

-- The source unit evidence suffices in arbitrary characteristic.
example (h2 : (2 : K) ≠ 0) : (2 : K) ^ (-2 : ℤ) * 4 = 1 := by norm_num

-- `Int.negOfNat 0` has no invertibility requirement on the base.
example : Checked.zpow (0 : K) (Int.negOfNat 0)
    (by intro h; exact ((by decide : ¬ Int.negOfNat 0 < 0) h).elim) = 1 := by norm_num

end DivisionSemiring

section DivisionRing
variable [DivisionRing K]

example (h2 : (2 : K) ≠ 0) : (-2 : K) ^ (-3 : ℤ) * 8 = -1 := by norm_num
example : (-2 : K) ^ (3 : ℤ) = -8 := by norm_num

end DivisionRing
