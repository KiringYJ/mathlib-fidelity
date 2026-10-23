/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Group.Semiconj.Units

/-!
# Lemmas about semiconjugate elements in a `GroupWithZero`.

-/

public section

assert_not_exists DenselyOrdered Ring

variable {G₀ : Type*}

namespace SemiconjBy

@[simp]
theorem zero_right [MulZeroClass G₀] (a : G₀) : SemiconjBy a 0 0 := by
  simp only [SemiconjBy, mul_zero, zero_mul]

@[simp]
theorem zero_left [MulZeroClass G₀] (x y : G₀) : SemiconjBy 0 x y := by
  simp only [SemiconjBy, mul_zero, zero_mul]

variable [MonoidWithZero G₀] {a x y : G₀} {u v : G₀ˣ}

/-- Semiconjugacy is preserved by division by corresponding unit denominators. -/
theorem divp_right (h : SemiconjBy a x y) (hu : SemiconjBy a u v) :
    SemiconjBy a (x /ₚ u) (y /ₚ v) :=
  h.mul_right hu.units_inv_right

end SemiconjBy
