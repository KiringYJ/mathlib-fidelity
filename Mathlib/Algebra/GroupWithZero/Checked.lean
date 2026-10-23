/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public meta import Lean.Elab.App
public meta import Lean.Elab.BuiltinNotation
public meta import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Inversion and division with explicit invertibility

`Checked.inv` and `Checked.div` operate on an ambient monoid element with evidence that the
denominator is a unit. Their implementations use the group of units, without an ambient inverse
operation or a value at an invalid denominator. `Checked.zpow` requires invertibility only for a
negative exponent.

The default evidence tactics use local hypotheses, unit and nonzero closure, and simplification.
They never assume that an arbitrary sum or a numeral in arbitrary characteristic is nonzero.
-/

@[expose] public section

/-- Find a nonzero proof from the local context and standard closure facts. -/
syntax (name := checkedNonzero) "checked_nonzero" : tactic

macro_rules
  | `(tactic| checked_nonzero) => `(tactic|
      first
      | assumption
      | exact NeZero.ne _
      | exact one_ne_zero
      | exact $(Lean.mkIdent `Nat.cast_add_one_ne_zero) _
      | (apply neg_ne_zero.mpr; checked_nonzero)
      | exact Units.ne_zero _
      | (apply ne_of_gt; assumption)
      | (apply ne_of_lt; assumption)
      | (apply mul_ne_zero <;> checked_nonzero)
      | (apply pow_ne_zero <;> checked_nonzero)
      | decide
      | simp_all
      | fail "a nonzero denominator proof is required")

/-- Find invertibility without installing an ambient inverse operation. -/
syntax (name := checkedUnit) "checked_unit" : tactic

macro_rules
  | `(tactic| checked_unit) => `(tactic|
      first
      | assumption
      | exact Units.isUnit _
      | exact isUnit_one
      | (apply IsUnit.mul <;> checked_unit)
      | (apply IsUnit.pow <;> checked_unit)
      | (apply GroupWithZero.isUnit_of_ne_zero; checked_nonzero)
      | fail "an invertibility proof is required")

/-- Invertibility is needed only on the negative-exponent branch. -/
syntax (name := checkedPower) "checked_power" : tactic

macro_rules
  | `(tactic| checked_power) => `(tactic| (intro h; first | checked_unit | omega | simp_all))

namespace Checked

variable {M : Type*} [Monoid M]

/-- The inverse of an ambient element, with its exact invertibility obligation. -/
noncomputable def inv (a : M) (ha : IsUnit a := by checked_unit) : M :=
  ↑ha.unit⁻¹

/-- Divide an arbitrary numerator by a denominator known to be a unit. -/
noncomputable def div (a b : M) (hb : IsUnit b := by checked_unit) : M :=
  a /ₚ hb.unit

/-- Integer powers of an ambient element; only negative exponents require a unit. -/
noncomputable def zpow (a : M) (n : Int)
    (ha : n < 0 → IsUnit a := by checked_power) : M :=
  match n with
  | .ofNat k => a ^ k
  | .negSucc k => ↑((ha (Int.negSucc_lt_zero k)).unit ^ (Int.negSucc k))

@[simp] theorem mul_inv_cancel (a : M) (ha : IsUnit a) : a * inv a ha = 1 :=
  ha.mul_val_inv

@[simp] theorem inv_mul_cancel (a : M) (ha : IsUnit a) : inv a ha * a = 1 :=
  ha.val_inv_mul

@[simp] theorem div_mul_cancel (a b : M) (hb : IsUnit b) : div a b hb * b = a :=
  divp_mul_cancel a hb.unit

@[simp] theorem mul_div_cancel (a b : M) (hb : IsUnit b) : div (a * b) b hb = a :=
  mul_divp_cancel a hb.unit

@[simp] theorem isUnit_inv (a : M) (ha : IsUnit a) : IsUnit (inv a ha) :=
  (ha.unit⁻¹).isUnit

@[simp] theorem zpow_ofNat (a : M) (n : Nat) (ha) : zpow a (Int.ofNat n) ha = a ^ n :=
  rfl

@[simp] theorem zpow_zero (a : M) (ha) : zpow a 0 ha = 1 :=
  pow_zero a

section Algebra
variable {a b : M} {ha : IsUnit a} {hb : IsUnit b}

theorem div_eq_mul_inv (a b : M) {hb : IsUnit b} : div a b hb = a * inv b hb := rfl

theorem eq_div_iff_mul_eq {a b c : M} {hc : IsUnit c} :
    a = div b c hc ↔ a * c = b := by
  simpa only [div, IsUnit.unit_spec] using
    (_root_.eq_divp_iff_mul_eq (x := a) (y := b) (u := hc.unit))

theorem div_eq_iff_mul_eq {a b c : M} {hc : IsUnit c} :
    div a c hc = b ↔ b * c = a := by
  simpa only [div, IsUnit.unit_spec] using
    (_root_.divp_eq_iff_mul_eq (x := a) (y := b) (u := hc.unit))

@[simp] theorem one_div (a : M) {ha : IsUnit a} : div 1 a ha = inv a ha := one_mul _

@[simp] theorem div_one (a : M) {h : IsUnit (1 : M)} : div a 1 h = a := by
  have hu : h.unit = (1 : Mˣ) := Units.ext h.unit_spec
  simp only [div, hu, divp, inv_one, Units.val_one, mul_one]

@[simp] theorem inv_one {h : IsUnit (1 : M)} : inv 1 h = 1 := by
  simpa only [one_div] using (div_one (1 : M) (h := h))

@[simp] theorem inv_inv (a : M) {ha : IsUnit a} {hi : IsUnit (inv a ha)} :
    inv (inv a ha) hi = a := by
  have hu : hi.unit = ha.unit⁻¹ := Units.ext rfl
  change (↑hi.unit⁻¹ : M) = a
  rw [hu, _root_.inv_inv, IsUnit.unit_spec]

end Algebra

section GroupWithZero
variable {G : Type*} [GroupWithZero G] {a b : G} {ha : IsUnit a} {hb : IsUnit b}

@[simp] theorem inv_ne_zero : inv a ha ≠ 0 := ha.unit⁻¹.ne_zero

theorem div_ne_zero (h : a ≠ 0) : div a b hb ≠ 0 := (divp_ne_zero_iff hb.unit).mpr h

end GroupWithZero

section Monoid
variable {M : Type*} [Monoid M]

theorem zpow_congr {a b : M} (hab : a = b) (n : ℤ)
    (ha : n < 0 → IsUnit a) (hb : n < 0 → IsUnit b) : zpow a n ha = zpow b n hb := by
  cases hab
  rfl

theorem zpow_eq_unit (a : M) (n : ℤ) (ha : IsUnit a) (h : n < 0 → IsUnit a) :
    zpow a n h = (↑(ha.unit ^ n) : M) := by
  cases n with
  | ofNat k =>
    change a ^ k = (↑(ha.unit ^ (k : ℤ)) : M)
    calc
      _ = (↑(ha.unit ^ k) : M) := (Units.val_pow_eq_pow_val ha.unit k).symm
      _ = _ := congrArg Units.val (_root_.zpow_natCast ha.unit k).symm
  | negSucc k => rfl

theorem zpow_negSucc (a : M) (k : ℕ) (h : Int.negSucc k < 0 → IsUnit a) :
    zpow a (Int.negSucc k) h = inv a (h (Int.negSucc_lt_zero k)) ^ (k + 1) := by
  simp only [zpow, _root_.zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val, inv]

@[simp] theorem zpow_one (n : ℤ) (h : n < 0 → IsUnit (1 : M)) : zpow (1 : M) n h = 1 := by
  have hu : (isUnit_one : IsUnit (1 : M)).unit = 1 := Units.ext rfl
  rw [zpow_eq_unit 1 n isUnit_one h, hu, one_zpow, Units.val_one]

@[simp] theorem inv_inj {a b : M} {ha : IsUnit a} {hb : IsUnit b} :
    inv a ha = inv b hb ↔ a = b := by
  simpa only [inv, IsUnit.unit_spec] using
    (Units.val_inv_inj (u₁ := ha.unit) (u₂ := hb.unit))


end Monoid

section GroupWithZero
variable {M : Type*} [GroupWithZero M]

theorem zpow_ne_zero {a : M} (ha : a ≠ 0) (n : ℤ) (h : n < 0 → IsUnit a) :
    zpow a n h ≠ 0 := by
  rw [zpow_eq_unit a n (GroupWithZero.isUnit_of_ne_zero ha) h]
  exact Units.ne_zero _

@[simp] theorem zpow_eq_zero_iff {a : M} {n : ℤ} (hn : n ≠ 0) (h : n < 0 → IsUnit a) :
    zpow a n h = 0 ↔ a = 0 := by
  cases n with
  | ofNat k =>
    have hk : k ≠ 0 := by intro hk; subst k; exact hn rfl
    simpa only [zpow_ofNat] using (pow_eq_zero_iff hk : a ^ k = 0 ↔ a = 0)
  | negSucc k =>
    exact iff_of_false (zpow_ne_zero (h (Int.negSucc_lt_zero k)).ne_zero _ h)
      (h (Int.negSucc_lt_zero k)).ne_zero

end GroupWithZero


end Checked
