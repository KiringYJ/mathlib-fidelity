/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
import Mathlib.Algebra.Order.Field.Power
/-! Order automation for checked operations on their valid domains. -/

section Field
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {a b : K}
example (ha : 0 < a) (hb : 0 < b) :
    0 < Checked.div a b (GroupWithZero.isUnit_of_ne_zero hb.ne') := by positivity
example (ha : 0 ≤ a) (hb : 0 < b) :
    0 ≤ Checked.div a b (GroupWithZero.isUnit_of_ne_zero hb.ne') := by positivity
example (ha : 0 < a) :
    0 < Checked.inv a (GroupWithZero.isUnit_of_ne_zero ha.ne') := by positivity
example (ha : IsUnit a) : Checked.inv a ha ≠ 0 := by positivity
example (a : K) : Checked.div a 2 + Checked.div a 2 = a := by rw [add_halves]
example (ha : 0 < a) : 0 < Checked.div a 2 := half_pos ha

example (ha : 0 < a) (n : Int) :
    0 < Checked.zpow a n (fun _ => GroupWithZero.isUnit_of_ne_zero ha.ne') := by positivity
example (ha : IsUnit a) : 0 ≤ Checked.zpow a (-2) (fun _ => ha) := by positivity
example (a : K) : 0 ≤ Checked.zpow a 2 (by intro h; omega) := by positivity
end Field
section GroupWithZero
variable {G : Type*} [GroupWithZero G] [PartialOrder G] {a b : G}
example (ha : IsUnit a) : Checked.inv a ha ≠ 0 := by positivity
example (ha : a ≠ 0) (hb : IsUnit b) : Checked.div a b hb ≠ 0 := by positivity
end GroupWithZero
