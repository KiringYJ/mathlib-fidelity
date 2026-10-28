/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.Inverse

/-! As in the official elaborator, `⁻¹` is a leaf of the surrounding operator tree: a coerced
element is inverted before the coercion, while groups with zero use the checked inverse. -/

section Group

variable {G : Type*} [Group G] (H : Subgroup G) (x : G) (g : H)

set_option pp.coercions.types true in
/-- info: x * (↑g⁻¹ : G) : G -/
#guard_msgs in
#check x * g⁻¹

end Group

section GroupWithZero

variable {K : Type*} [CommGroupWithZero K] (a b : K) (hb : b ≠ 0)

/-- info: a * b⁻¹ : K -/
#guard_msgs in
#check a * b⁻¹

example : a * b⁻¹ = a * Checked.inv b := rfl

example (u : Kˣ) : a * (u : K)⁻¹ = a * Units.val u⁻¹ := rfl

end GroupWithZero
