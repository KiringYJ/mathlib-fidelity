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

The lemmas about inversion, division and integer powers hold in any monoid. As in
`Mathlib.Algebra.GroupWithZero.Inverse`, each takes the invertibility evidence of the operations in
its conclusion as an implicit argument; an integer power needs it only for a negative exponent.
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

section Monoid

variable {M : Type*} [Monoid M] {a x y x' y' : M}

/-- If `a` is invertible, then `a⁻¹` semiconjugates `x` to `y` if and only if `a` semiconjugates
`y` to `x`. -/
@[simp]
theorem inv_symm_left_iff₀ {ha : IsUnit a} : SemiconjBy a⁻¹ x y ↔ SemiconjBy a y x :=
  units_inv_symm_left_iff (a := ha.unit) (x := y) (y := x)

/-- If an invertible element `a` semiconjugates `x` to `y`, then `a⁻¹` semiconjugates `y` to
`x`. -/
theorem inv_symm_left₀ {ha : IsUnit a} (h : SemiconjBy a x y) : SemiconjBy a⁻¹ y x :=
  inv_symm_left_iff₀.2 h

/-- If `a` semiconjugates an invertible `x` to an invertible `y`, then it semiconjugates `x⁻¹` to
`y⁻¹`. -/
theorem inv_right₀ {hx : IsUnit x} {hy : IsUnit y} (h : SemiconjBy a x y) :
    SemiconjBy a x⁻¹ y⁻¹ :=
  units_inv_right (x := hx.unit) (y := hy.unit) h

/-- For invertible `x` and `y`, the element `a` semiconjugates `x⁻¹` to `y⁻¹` if and only if it
semiconjugates `x` to `y`. -/
@[simp]
theorem inv_right_iff₀ {hx : IsUnit x} {hy : IsUnit y} :
    SemiconjBy a x⁻¹ y⁻¹ ↔ SemiconjBy a x y where
  mp h := by simpa only [inv_inv₀] using h.inv_right₀ (hx := hx.inv₀) (hy := hy.inv₀)
  mpr h := h.inv_right₀

/-- If `a` semiconjugates `x` to `y` and an invertible `x'` to an invertible `y'`, then it
semiconjugates `(x / x')` to `(y / y')`. -/
theorem div_right {hx' : IsUnit x'} {hy' : IsUnit y'} (h : SemiconjBy a x y)
    (h' : SemiconjBy a x' y') : SemiconjBy a (x / x') (y / y') := by
  rw [div_eq_mul_inv₀, div_eq_mul_inv₀]
  exact h.mul_right h'.inv_right₀

/-- If `a` semiconjugates `x` to `y`, then it semiconjugates `x ^ m` to `y ^ m`. A negative
exponent requires `x` and `y` to be invertible. -/
lemma zpow_right₀ (h : SemiconjBy a x y) (m : ℤ) {hx : m < 0 → IsUnit x}
    {hy : m < 0 → IsUnit y} : SemiconjBy a (x ^ m) (y ^ m) := by
  cases m with
  | ofNat n => exact h.pow_right n
  | negSucc n =>
    exact units_zpow_right (x := (hx (Int.negSucc_lt_zero n)).unit)
      (y := (hy (Int.negSucc_lt_zero n)).unit) h (Int.negSucc n)

end Monoid

end SemiconjBy

namespace Commute

variable {M : Type*} [Monoid M] {a b : M}

/-- If `a` commutes with `b`, then it commutes with `b ^ m`. A negative exponent requires `b` to
be invertible. -/
lemma zpow_right₀ (h : Commute a b) (m : ℤ) {hb : m < 0 → IsUnit b} : Commute a (b ^ m) :=
  SemiconjBy.zpow_right₀ h m

/-- If `a` commutes with `b`, then `a ^ m` commutes with `b`. A negative exponent requires `a` to
be invertible. -/
lemma zpow_left₀ (h : Commute a b) (m : ℤ) {ha : m < 0 → IsUnit a} : Commute (a ^ m) b :=
  (h.symm.zpow_right₀ m).symm

/-- If `a` commutes with `b`, then `a ^ m` commutes with `b ^ n`. A negative exponent requires its
base to be invertible. -/
lemma zpow_zpow₀ (h : Commute a b) (m n : ℤ) {ha : m < 0 → IsUnit a} {hb : n < 0 → IsUnit b} :
    Commute (a ^ m) (b ^ n) :=
  (h.zpow_left₀ m).zpow_right₀ n

/-- An integer power of `a` commutes with `a`. A negative exponent requires `a` to be
invertible. -/
lemma zpow_self₀ (a : M) (n : ℤ) {ha : n < 0 → IsUnit a} : Commute (a ^ n) a :=
  (Commute.refl a).zpow_left₀ n

/-- An element commutes with its integer powers. A negative exponent requires `a` to be
invertible. -/
lemma self_zpow₀ (a : M) (n : ℤ) {ha : n < 0 → IsUnit a} : Commute a (a ^ n) :=
  (Commute.refl a).zpow_right₀ n

/-- Integer powers of `a` commute with each other. A negative exponent requires `a` to be
invertible. -/
lemma zpow_zpow_self₀ (a : M) (m n : ℤ) {hm : m < 0 → IsUnit a} {hn : n < 0 → IsUnit a} :
    Commute (a ^ m) (a ^ n) :=
  (Commute.refl a).zpow_zpow₀ m n

end Commute
