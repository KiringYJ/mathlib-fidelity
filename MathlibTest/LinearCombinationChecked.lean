/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Order.Field.Basic

/-! Division in linear combinations retains exact denominator evidence. -/

section Field
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {a b c : K}

example (h : a = b) (hc : IsUnit c) : Checked.div a c hc = Checked.div b c hc := by
  linear_combination h / c

example (h : a ≤ b) (hc : 0 < c) :
    Checked.div a c (GroupWithZero.isUnit_of_ne_zero hc.ne') ≤
      Checked.div b c (GroupWithZero.isUnit_of_ne_zero hc.ne') := by
  linear_combination h / c

example (h : a < b) (hc : 0 < c) :
    Checked.div a c (GroupWithZero.isUnit_of_ne_zero hc.ne') <
      Checked.div b c (GroupWithZero.isUnit_of_ne_zero hc.ne') := by
  linear_combination h / c

example (h : a < b) (hc : 0 ≤ c) (hu : IsUnit c) :
    Checked.div a c hu ≤ Checked.div b c hu := by
  linear_combination h / c

/-- error: division in a linear combination requires valid denominator evidence -/
#guard_msgs in
example (h : a = b) : a = b := by
  linear_combination (norm := skip) h / (0 : K)

/-- error: division in a linear combination requires valid denominator evidence -/
#guard_msgs in
example (h : a ≤ b) : a ≤ b := by
  have hz : (0 : K) ≤ 0 := le_rfl
  linear_combination (norm := skip) h / (0 : K)

end Field

-- Genuine integer quotients keep their existing contract.
example (a b : Int) (h : a = b) : a / 2 = b / 2 := by
  linear_combination h / 2
