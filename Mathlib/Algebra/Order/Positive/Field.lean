/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Order.Positive.Ring

/-!
# Algebraic structures on the set of positive numbers

In this file we prove that the set of positive elements of a linear ordered field is a linear
ordered commutative group.
-/

public section


variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

namespace Positive

/-- Every positive element is invertible, and its inverse is positive. -/
noncomputable instance Subtype.inv : Inv { x : K // 0 < x } :=
  ⟨fun x => ⟨Checked.inv (x : K) x.2.ne'.isUnit, inv_pos_of_pos x.2⟩⟩

@[simp]
theorem coe_inv (x : { x : K // 0 < x }) : ↑x⁻¹ = Checked.inv (x : K) x.2.ne'.isUnit :=
  rfl

noncomputable instance : Pow { x : K // 0 < x } ℤ :=
  ⟨fun x n => ⟨Checked.zpow (x : K) n fun _ => x.2.ne'.isUnit, zpow_pos x.2 _⟩⟩

@[simp]
theorem coe_zpow (x : { x : K // 0 < x }) (n : ℤ) :
    ↑(x ^ n) = Checked.zpow (x : K) n fun _ => x.2.ne'.isUnit :=
  rfl

noncomputable instance : CommGroup { x : K // 0 < x } where
  inv_mul_cancel a := Subtype.ext <| inv_mul_cancel₀
  zpow_zero' x := Subtype.ext <| zpow_zero₀ _
  zpow_succ' n x := Subtype.ext <| by
    simp only [coe_zpow, val_mul, zpow_natCast₀, pow_succ]
  zpow_neg' n x := Subtype.ext <| by
    simp only [coe_zpow, coe_inv, zpow_negSucc₀, zpow_natCast₀]

end Positive
