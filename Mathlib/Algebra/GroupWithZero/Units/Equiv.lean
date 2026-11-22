/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Multiplication by a nonzero element in a `GroupWithZero` is a permutation.

Division on the right by a nonzero element is a permutation as well. Division on the left,
`x ↦ a / x`, is not: its denominator `x` must be a unit, so it permutes the group of units `G₀ˣ`,
where it is `Equiv.divLeft`.
-/

@[expose] public section

assert_not_exists DenselyOrdered Ring

variable {G₀ : Type*}

namespace Equiv
section GroupWithZero
variable [GroupWithZero G₀]

/-- In a `GroupWithZero` `G₀`, the unit group `G₀ˣ` is equivalent to the subtype of nonzero
elements. -/
@[simps] noncomputable def _root_.unitsEquivNeZero : G₀ˣ ≃ {a : G₀ // a ≠ 0} where
  toFun a := ⟨a, a.ne_zero⟩
  invFun a := Units.mk0 _ a.prop

/-- Left multiplication by a nonzero element in a `GroupWithZero` is a permutation of the
underlying type. -/
@[simps! -fullyApplied]
protected noncomputable def mulLeft₀ (a : G₀) (ha : a ≠ 0) : Perm G₀ :=
  (Units.mk0 a ha).mulLeft

theorem _root_.mulLeft_bijective₀ (a : G₀) (ha : a ≠ 0) : Function.Bijective (a * · : G₀ → G₀) :=
  (Equiv.mulLeft₀ a ha).bijective

/-- Right multiplication by a nonzero element in a `GroupWithZero` is a permutation of the
underlying type. -/
@[simps! -fullyApplied]
protected noncomputable def mulRight₀ (a : G₀) (ha : a ≠ 0) : Perm G₀ :=
  (Units.mk0 a ha).mulRight

theorem _root_.mulRight_bijective₀ (a : G₀) (ha : a ≠ 0) : Function.Bijective ((· * a) : G₀ → G₀) :=
  (Equiv.mulRight₀ a ha).bijective

/-- Right division by a nonzero element in a `GroupWithZero` is a permutation of the
underlying type. -/
@[simps! +simpRhs]
noncomputable def divRight₀ (a : G₀) (ha : a ≠ 0) : Perm G₀ where
  toFun x := Checked.div x a ha.isUnit
  invFun := (· * a)
  left_inv _ := by simp
  right_inv _ := by simp

end GroupWithZero
end Equiv
