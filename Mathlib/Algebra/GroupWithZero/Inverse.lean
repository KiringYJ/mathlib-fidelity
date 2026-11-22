/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Checked.Notation

/-!
# Inverse, division and integer powers of invertible elements

In a monoid, an invertible element `a` has an inverse `a⁻¹` and a right quotient `Checked.div b a`.
Integer powers `a ^ n` require invertibility when `n` is negative.
This file develops their algebra: closure of invertibility, cancellation, uniqueness of inverses,
inverses of products and quotients, and rearrangement of fractions.

Each theorem takes the invertibility evidence carried by the operations on its left-hand side
as implicit arguments, which a rewrite or simplification unifies with the matched terms. The
evidence used on the right-hand side is derived from it whenever possible, so that rewriting
from left to right creates no side goals. Where a factor's invertibility cannot be recovered from
a product in an arbitrary monoid, the theorem is stated for Dedekind-finite or commutative
monoids, which include groups with zero.

Theorems whose established name belongs to a group or division-monoid theorem about a total
inverse take the suffix `₀`, as mathlib does for groups with zero.
-/

@[expose] public section

variable {M : Type*}

section Monoid
variable [Monoid M] {a b c d : M}

/-! ### Closure of invertibility -/

/-- The inverse of an invertible element is invertible. -/
theorem IsUnit.inv₀ (ha : IsUnit a) : IsUnit a⁻¹ := (ha.unit⁻¹).isUnit

/-- A quotient of invertible elements is invertible. -/
theorem IsUnit.div₀ (ha : IsUnit a) (hb : IsUnit b) : IsUnit (Checked.div a b) :=
  ha.mul hb.inv₀

/-- An integer power of an invertible element is invertible. -/
theorem IsUnit.zpow₀ (ha : IsUnit a) (n : ℤ) : IsUnit (a ^ n) := by
  cases n with
  | ofNat k => exact ha.pow k
  | negSucc k => exact Units.isUnit _

/-! ### Cancellation -/

@[simp] theorem mul_inv_cancel₀ {ha : IsUnit a} : a * a⁻¹ = 1 := ha.mul_val_inv

@[simp] theorem inv_mul_cancel₀ {ha : IsUnit a} : a⁻¹ * a = 1 := ha.val_inv_mul

@[simp] theorem mul_inv_cancel_right₀ {hb : IsUnit b} (a : M) : a * b * b⁻¹ = a := by
  rw [mul_assoc, mul_inv_cancel₀, mul_one]

@[simp] theorem inv_mul_cancel_right₀ {hb : IsUnit b} (a : M) : a * b⁻¹ * b = a := by
  rw [mul_assoc, inv_mul_cancel₀, mul_one]

@[simp] theorem mul_inv_cancel_left₀ {ha : IsUnit a} (b : M) : a * (a⁻¹ * b) = b := by
  rw [← mul_assoc, mul_inv_cancel₀, one_mul]

@[simp] theorem inv_mul_cancel_left₀ {ha : IsUnit a} (b : M) : a⁻¹ * (a * b) = b := by
  rw [← mul_assoc, inv_mul_cancel₀, one_mul]

theorem div_eq_mul_inv₀ (a b : M) {hb : IsUnit b} : Checked.div a b = a * b⁻¹ := rfl

@[simp] theorem div_mul_cancel₀ (a : M) {hb : IsUnit b} : Checked.div a b * b = a :=
  inv_mul_cancel_right₀ a

@[simp] theorem mul_div_cancel_right₀ (a : M) {hb : IsUnit b} : Checked.div (a * b) b = a :=
  mul_inv_cancel_right₀ a

@[simp] theorem div_self {ha : IsUnit a} : Checked.div a a = 1 := mul_inv_cancel₀

theorem mul_one_div_cancel {ha : IsUnit a} : a * Checked.div 1 a = 1 := by
  rw [div_eq_mul_inv₀, one_mul, mul_inv_cancel₀]

theorem one_div_mul_cancel {ha : IsUnit a} : Checked.div 1 a * a = 1 := by
  rw [div_eq_mul_inv₀, one_mul, inv_mul_cancel₀]

theorem mul_mul_div {hb : IsUnit b} (a : M) : a = a * b * Checked.div 1 b := by
  rw [mul_assoc, mul_one_div_cancel, mul_one]

/-- The numerator of an invertible quotient by an invertible element is invertible. -/
theorem IsUnit.of_div₀ {hb : IsUnit b} (hab : IsUnit (Checked.div a b)) : IsUnit a := by
  simpa only [div_mul_cancel₀] using hab.mul hb

/-! ### Uniqueness of inverses -/

theorem inv_eq_of_mul_eq_one_right₀ {ha : IsUnit a} (h : a * b = 1) : a⁻¹ = b := by
  rw [← mul_one a⁻¹, ← h, inv_mul_cancel_left₀]

theorem inv_eq_of_mul_eq_one_left₀ {hb : IsUnit b} (h : a * b = 1) : b⁻¹ = a := by
  rw [← one_mul b⁻¹, ← h, mul_inv_cancel_right₀]

theorem eq_inv_of_mul_eq_one_left₀ {hb : IsUnit b} (h : a * b = 1) : a = b⁻¹ :=
  (inv_eq_of_mul_eq_one_left₀ h).symm

theorem eq_inv_of_mul_eq_one_right₀ {ha : IsUnit a} (h : a * b = 1) : b = a⁻¹ :=
  (inv_eq_of_mul_eq_one_right₀ h).symm

theorem eq_one_div_of_mul_eq_one_left₀ {ha : IsUnit a} (h : b * a = 1) : b = Checked.div 1 a := by
  rw [div_eq_mul_inv₀, one_mul]; exact eq_inv_of_mul_eq_one_left₀ h

theorem eq_one_div_of_mul_eq_one_right₀ {ha : IsUnit a} (h : a * b = 1) : b = Checked.div 1 a := by
  rw [div_eq_mul_inv₀, one_mul]; exact eq_inv_of_mul_eq_one_right₀ h

@[simp] theorem inv_one₀ : (1 : M)⁻¹ = 1 :=
  inv_eq_of_mul_eq_one_right₀ (one_mul 1)

@[simp] theorem div_one₀ (a : M) : Checked.div a 1 = a := by
  rw [div_eq_mul_inv₀, inv_one₀, mul_one]

theorem one_div_one₀ : Checked.div (1 : M) 1 = 1 := div_one₀ 1

@[simp] theorem inv_inv₀ (a : M) {ha : IsUnit a} : a⁻¹⁻¹ = a :=
  inv_eq_of_mul_eq_one_right₀ inv_mul_cancel₀

@[simp] theorem inv_inj₀ {ha : IsUnit a} {hb : IsUnit b} : a⁻¹ = b⁻¹ ↔ a = b where
  mp h := calc
    a = a⁻¹⁻¹ := (inv_inv₀ a).symm
    _ = b⁻¹⁻¹ := by simp only [h]
    _ = b := inv_inv₀ b
  mpr h := by subst h; rfl

theorem inv_eq_iff_eq_inv₀ {ha : IsUnit a} {hb : IsUnit b} : a⁻¹ = b ↔ a = b⁻¹ where
  mp h := eq_inv_of_mul_eq_one_left₀ (h ▸ mul_inv_cancel₀)
  mpr h := inv_eq_of_mul_eq_one_right₀ (by rw [h]; exact inv_mul_cancel₀)

@[simp] theorem inv_eq_one₀ {ha : IsUnit a} : a⁻¹ = 1 ↔ a = 1 := by
  rw [inv_eq_iff_eq_inv₀ (hb := isUnit_one), inv_one₀]

theorem inv_ne_one₀ {ha : IsUnit a} : a⁻¹ ≠ 1 ↔ a ≠ 1 := inv_eq_one₀.not

/-! ### Equations involving inverses -/

theorem eq_mul_inv_iff_mul_eq₀ {hc : IsUnit c} : a = b * c⁻¹ ↔ a * c = b where
  mp h := by rw [h, inv_mul_cancel_right₀]
  mpr h := by rw [← h, mul_inv_cancel_right₀]

theorem eq_inv_mul_iff_mul_eq₀ {hb : IsUnit b} : a = b⁻¹ * c ↔ b * a = c where
  mp h := by rw [h, mul_inv_cancel_left₀]
  mpr h := by rw [← h, inv_mul_cancel_left₀]

theorem inv_mul_eq_iff_eq_mul₀ {ha : IsUnit a} : a⁻¹ * b = c ↔ b = a * c where
  mp h := by rw [← h, mul_inv_cancel_left₀]
  mpr h := by rw [h, inv_mul_cancel_left₀]

theorem mul_inv_eq_iff_eq_mul₀ {hb : IsUnit b} : a * b⁻¹ = c ↔ a = c * b where
  mp h := by rw [← h, inv_mul_cancel_right₀]
  mpr h := by rw [h, mul_inv_cancel_right₀]

theorem mul_inv_eq_one₀ {hb : IsUnit b} : a * b⁻¹ = 1 ↔ a = b := by
  rw [mul_inv_eq_iff_eq_mul₀, one_mul]

theorem inv_mul_eq_one₀ {ha : IsUnit a} : a⁻¹ * b = 1 ↔ a = b := by
  rw [inv_mul_eq_iff_eq_mul₀, mul_one, eq_comm]

theorem mul_eq_one_iff_eq_inv₀ {hb : IsUnit b} : a * b = 1 ↔ a = b⁻¹ := by
  rw [← mul_inv_eq_one₀ (hb := hb.inv₀), inv_inv₀]

theorem mul_eq_one_iff_inv_eq₀ {ha : IsUnit a} : a * b = 1 ↔ a⁻¹ = b := by
  rw [← inv_mul_eq_one₀ (ha := ha.inv₀), inv_inv₀]

theorem mul_eq_of_eq_mul_inv₀ {hb : IsUnit b} (h : a = c * b⁻¹) : a * b = c := by
  rwa [← eq_mul_inv_iff_mul_eq₀]

theorem mul_eq_of_eq_inv_mul₀ {ha : IsUnit a} (h : b = a⁻¹ * c) : a * b = c := by
  rwa [← eq_inv_mul_iff_mul_eq₀]

theorem eq_mul_of_inv_mul_eq₀ {hb : IsUnit b} (h : b⁻¹ * a = c) : a = b * c := by
  rwa [← inv_mul_eq_iff_eq_mul₀]

theorem eq_mul_of_mul_inv_eq₀ {hc : IsUnit c} (h : a * c⁻¹ = b) : a = b * c := by
  rwa [← mul_inv_eq_iff_eq_mul₀]

/-! ### Equations involving quotients -/

theorem div_eq_iff {hb : IsUnit b} : Checked.div a b = c ↔ a = c * b := mul_inv_eq_iff_eq_mul₀

theorem eq_div_iff {hb : IsUnit b} : c = Checked.div a b ↔ c * b = a := eq_mul_inv_iff_mul_eq₀

theorem div_eq_iff_mul_eq {hb : IsUnit b} : Checked.div a b = c ↔ c * b = a :=
  div_eq_iff.trans eq_comm

theorem eq_div_iff_mul_eq {hc : IsUnit c} : a = Checked.div b c ↔ a * c = b := eq_div_iff

theorem div_eq_of_eq_mul {hb : IsUnit b} : a = c * b → Checked.div a b = c := div_eq_iff.2

theorem eq_div_of_mul_eq {hc : IsUnit c} : a * c = b → a = Checked.div b c := eq_div_iff.2

theorem div_eq_one_iff_eq {hb : IsUnit b} : Checked.div a b = 1 ↔ a = b := mul_inv_eq_one₀

theorem eq_of_div_eq_one₀ {hb : IsUnit b} (h : Checked.div a b = 1) : a = b := div_eq_one_iff_eq.1 h

theorem div_ne_one_of_ne₀ {hb : IsUnit b} (h : a ≠ b) : Checked.div a b ≠ 1 :=
  mt eq_of_div_eq_one₀ h

@[simp]
theorem div_left_inj' {hc : IsUnit c} : Checked.div a c = Checked.div b c ↔ a = b where
  mp h := by rw [← div_mul_cancel₀ a (hb := hc), h, div_mul_cancel₀]
  mpr h := by subst h; rfl

/-! ### Rearranging quotients -/

@[simp] theorem one_div₀ (a : M) {ha : IsUnit a} : Checked.div 1 a = a⁻¹ := one_mul _

theorem inv_eq_one_div₀ (a : M) {ha : IsUnit a} : a⁻¹ = Checked.div 1 a := (one_div₀ a).symm

theorem mul_one_div₀ (a b : M) {hb : IsUnit b} : a * Checked.div 1 b = Checked.div a b := by
  rw [one_div₀, div_eq_mul_inv₀]

theorem div_eq_mul_one_div₀ (a b : M) {hb : IsUnit b} : Checked.div a b = a * Checked.div 1 b :=
  (mul_one_div₀ a b).symm

theorem mul_div_assoc₀ (a b c : M) {hc : IsUnit c} :
    Checked.div (a * b) c = a * Checked.div b c := mul_assoc _ _ _

theorem mul_div₀ (a b c : M) {hc : IsUnit c} :
    a * Checked.div b c = Checked.div (a * b) c := (mul_assoc _ _ _).symm

theorem div_mul_eq_mul_div_assoc₀ (a b c : M) {hc : IsUnit c} :
    Checked.div (a * b) c = a * Checked.div b c :=
  mul_div_assoc₀ a b c

theorem div_inv_eq_mul₀ {hb : IsUnit b} : Checked.div a b⁻¹ = a * b := by
  rw [div_eq_mul_inv₀, inv_inv₀]

@[simp] theorem div_div_eq_mul_div₀ {hc : IsUnit c} {hbc : IsUnit (Checked.div b c)} :
    Checked.div a (Checked.div b c) = Checked.div (a * c) b := by
  have hb : IsUnit b := IsUnit.of_div₀ hbc
  rw [div_eq_iff, div_eq_mul_inv₀ (a * c), div_eq_mul_inv₀ b, mul_assoc (a * c),
    inv_mul_cancel_left₀, mul_inv_cancel_right₀]

theorem one_div_div₀ {hb : IsUnit b} {hab : IsUnit (Checked.div a b)} :
    Checked.div 1 (Checked.div a b) = Checked.div b a := by
  rw [div_div_eq_mul_div₀, one_mul]

theorem one_div_one_div₀ {ha : IsUnit a} : Checked.div 1 (Checked.div 1 a) = a := by
  simp only [one_div₀, inv_inv₀]

@[simp] theorem inv_div₀ {hb : IsUnit b} {hab : IsUnit (Checked.div a b)} :
    (Checked.div a b)⁻¹ = Checked.div b a := by
  rw [← one_div₀, one_div_div₀]

theorem div_div_div_cancel_right₀ {hc : IsUnit c} (a b : M) {hbc : IsUnit (Checked.div b c)} :
    Checked.div (Checked.div a c) (Checked.div b c) = Checked.div a b := by
  rw [div_div_eq_mul_div₀, div_mul_cancel₀]

theorem div_mul_div_cancel₀ {hb : IsUnit b} {hc : IsUnit c} :
    Checked.div a b * Checked.div b c = Checked.div a c := by
  rw [← mul_div_assoc₀, div_mul_cancel₀]

/-! ### Inverses of powers -/

@[simp] theorem inv_pow₀ {ha : IsUnit a} (n : ℕ) : a⁻¹ ^ n = (a ^ n)⁻¹ := by
  induction n with
  | zero => simp only [pow_zero, inv_one₀]
  | succ n ih =>
    rw [pow_succ, ih]
    refine (inv_eq_of_mul_eq_one_right₀ ?_).symm
    rw [pow_succ', mul_assoc, mul_inv_cancel_left₀, mul_inv_cancel₀]

/-! ### Integer powers -/

@[simp, norm_cast] theorem zpow_natCast₀ (a : M) (n : ℕ) : a ^ (n : ℤ) = a ^ n := rfl

theorem zpow_zero₀ (a : M) : a ^ (0 : ℤ) = 1 := pow_zero a

theorem zpow_one₀ (a : M) : a ^ (1 : ℤ) = a := pow_one a

@[simp] theorem zpow_ofNat₀ (a : M) (n : ℕ) {h : (OfNat.ofNat n : ℤ) < 0 → IsUnit a} :
    a ^ (ofNat(n) : ℤ) = a ^ (OfNat.ofNat n : ℕ) := rfl

theorem zpow_two₀ (a : M) : a ^ (2 : ℤ) = a * a := pow_two a

/-- An integer power of an invertible element is the corresponding power in the group of units. -/
theorem IsUnit.zpow_eq_val_unit_zpow (ha : IsUnit a) (n : ℤ) :
    a ^ n = (↑(ha.unit ^ n) : M) := by
  cases n with
  | ofNat k =>
    change a ^ k = (↑(ha.unit ^ (k : ℤ)) : M)
    rw [zpow_natCast, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
  | negSucc k => rfl

theorem zpow_negSucc₀ (a : M) (n : ℕ) {h : Int.negSucc n < 0 → IsUnit a} :
    a ^ Int.negSucc n =
      Checked.inv (a ^ (n + 1)) ((h (Int.negSucc_lt_zero n)).pow (n + 1)) := by
  have ha := h (Int.negSucc_lt_zero n)
  have e : a ^ (n + 1) = (↑(ha.unit ^ (n + 1)) : M) := by
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec]
  refine eq_inv_of_mul_eq_one_left₀ ?_
  rw [ha.zpow_eq_val_unit_zpow, e, ← Units.val_mul, zpow_negSucc, inv_mul_cancel, Units.val_one]

@[simp] theorem zpow_neg_one₀ (a : M) {h : (-1 : ℤ) < 0 → IsUnit a} :
    a ^ (-1 : ℤ) = Checked.inv a (h (by decide)) := by
  have ha := h (by decide)
  rw [ha.zpow_eq_val_unit_zpow, zpow_neg_one]
  rfl

@[simp] theorem one_zpow₀ (n : ℤ) : (1 : M) ^ n = 1 := by
  cases n with
  | ofNat k => exact one_pow k
  | negSucc k =>
    rw [zpow_negSucc₀]
    simp only [one_pow, inv_one₀]

/-- An element equal to a unit has that unit's inverse as its inverse. -/
theorem inv_eq_val_inv_of_eq_val₀ {hb : IsUnit b} (u : Mˣ) (h : b = u) : b⁻¹ = ↑u⁻¹ :=
  inv_eq_of_mul_eq_one_right₀ (by rw [h, Units.mul_inv])

/-- The coercion of the inverse of a unit is the inverse of its coercion. The notation
elaborates `(↑u)⁻¹` as `↑u⁻¹`, so this lemma is needed only once `↑u` has been rewritten. -/
theorem Units.val_inv_eq_inv_val₀ (u : Mˣ) : (↑u⁻¹ : M) = Checked.inv (u : M) u.isUnit :=
  (inv_eq_val_inv_of_eq_val₀ (hb := u.isUnit) u rfl).symm

@[simp] theorem inv_zpow₀ (a : M) (n : ℤ) {ha : IsUnit a} : a⁻¹ ^ n = (a ^ n)⁻¹ := by
  have hi : IsUnit a⁻¹ := ha.inv₀
  rw [hi.zpow_eq_val_unit_zpow, inv_eq_val_inv_of_eq_val₀ (ha.unit ^ n)
    (ha.zpow_eq_val_unit_zpow n)]
  congr 1
  rw [← inv_zpow]
  congr 1
  ext
  rfl

end Monoid

/-! ### Dedekind-finite monoids

In a Dedekind-finite monoid, invertibility of a product gives invertibility of its factors, so the
evidence for a product determines the evidence for the right-hand sides below. -/

section DedekindFinite
variable [Monoid M] [IsDedekindFiniteMonoid M] {a b c d : M}

@[simp] theorem mul_inv_rev₀ {hab : IsUnit (a * b)} : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  have ha : IsUnit a := isUnit_of_mul_isUnit_left hab
  have hb : IsUnit b := isUnit_of_mul_isUnit_right hab
  refine inv_eq_of_mul_eq_one_right₀ ?_
  rw [mul_assoc, mul_inv_cancel_left₀, mul_inv_cancel₀]

theorem div_mul_cancel_right₀ {hab : IsUnit (a * b)} : Checked.div b (a * b) = a⁻¹ := by
  have hb : IsUnit b := isUnit_of_mul_isUnit_right hab
  rw [div_eq_mul_inv₀, mul_inv_rev₀, mul_inv_cancel_left₀]

theorem div_mul_eq_div_div_swap₀ {hbc : IsUnit (b * c)} :
    Checked.div a (b * c) = Checked.div (Checked.div a c) b := by
  have hb : IsUnit b := isUnit_of_mul_isUnit_left hbc
  have hc : IsUnit c := isUnit_of_mul_isUnit_right hbc
  rw [div_eq_mul_inv₀, mul_inv_rev₀, ← mul_assoc]
  rfl

end DedekindFinite

section CommMonoid
variable [CommMonoid M] {a b c d : M}

@[simp] theorem mul_div_cancel_left₀ (b : M) {ha : IsUnit a} : Checked.div (a * b) a = b := by
  rw [mul_comm, mul_div_cancel_right₀]

theorem mul_inv₀ {hab : IsUnit (a * b)} : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  rw [mul_inv_rev₀, mul_comm]

theorem div_eq_inv_mul₀ (a b : M) {hb : IsUnit b} : Checked.div a b = b⁻¹ * a := mul_comm _ _

theorem inv_mul_eq_div₀ {ha : IsUnit a} : a⁻¹ * b = Checked.div b a := mul_comm _ _

theorem div_mul_eq_mul_div₀ (a b c : M) {hc : IsUnit c} :
    Checked.div a c * b = Checked.div (a * b) c := by
  rw [div_eq_mul_inv₀, div_eq_mul_inv₀, mul_right_comm]

theorem mul_div_right_comm₀ {hc : IsUnit c} : Checked.div (a * b) c = Checked.div a c * b :=
  (div_mul_eq_mul_div₀ a b c).symm

theorem mul_comm_div₀ {hb : IsUnit b} : Checked.div a b * c = a * Checked.div c b := by
  rw [div_mul_eq_mul_div₀, mul_div_assoc₀]

theorem div_mul_comm₀ {hb : IsUnit b} : Checked.div a b * c = Checked.div c b * a := by
  rw [div_mul_eq_mul_div₀, div_mul_eq_mul_div₀, mul_comm]

theorem mul_div_left_comm₀ {hc : IsUnit c} : a * Checked.div b c = b * Checked.div a c := by
  rw [mul_div₀, mul_div₀, mul_comm]

theorem div_div₀ {hb : IsUnit b} {hc : IsUnit c} :
    Checked.div (Checked.div a b) c = Checked.div a (b * c) := by
  rw [div_eq_mul_inv₀ a (b * c), mul_inv₀, ← mul_assoc]
  rfl

theorem div_mul_eq_div_div₀ {hbc : IsUnit (b * c)} :
    Checked.div a (b * c) = Checked.div (Checked.div a b) c := div_div₀.symm

theorem div_right_comm₀ {hb : IsUnit b} {hc : IsUnit c} :
    Checked.div (Checked.div a b) c = Checked.div (Checked.div a c) b := by
  simp only [div_eq_mul_inv₀, mul_right_comm]

theorem div_mul_div_comm₀ {hb : IsUnit b} {hd : IsUnit d} :
    Checked.div a b * Checked.div c d = Checked.div (a * c) (b * d) := by
  rw [div_eq_mul_inv₀, div_eq_mul_inv₀, div_eq_mul_inv₀, mul_inv₀, mul_mul_mul_comm]

theorem mul_div_mul_comm₀ {hcd : IsUnit (c * d)} :
    Checked.div (a * b) (c * d) = Checked.div a c * Checked.div b d :=
  div_mul_div_comm₀.symm

theorem one_div_mul_one_div₀ {ha : IsUnit a} {hb : IsUnit b} :
    Checked.div 1 a * Checked.div 1 b = Checked.div 1 (a * b) := by
  rw [div_mul_div_comm₀, one_mul]

theorem one_div_mul_eq_div₀ {ha : IsUnit a} : Checked.div 1 a * b = Checked.div b a := by
  rw [div_mul_eq_mul_div₀, one_mul]

theorem div_mul_eq_div_mul_one_div₀ {hbc : IsUnit (b * c)} :
    Checked.div a (b * c) = Checked.div a b * Checked.div 1 c := by
  rw [div_mul_eq_div_div₀, div_eq_mul_one_div₀ (Checked.div a b)]

@[simp] theorem div_pow₀ (a b : M) (n : ℕ) {hb : IsUnit b} :
    (Checked.div a b) ^ n = Checked.div (a ^ n) (b ^ n) := by
  rw [div_eq_mul_inv₀, mul_pow, inv_pow₀]; rfl

theorem inv_div_inv₀ {ha : IsUnit a} {hb : IsUnit b} :
    Checked.div a⁻¹ b⁻¹ = Checked.div b a := by
  rw [div_inv_eq_mul₀, inv_mul_eq_div₀]

theorem inv_div₀' {hb : IsUnit b} {hab : IsUnit (Checked.div a b)} :
    (Checked.div a b)⁻¹ = Checked.div a⁻¹ b⁻¹ := by
  rw [inv_div₀, inv_div_inv₀]

theorem inv_mul₀' {hab : IsUnit (a * b)} : (a * b)⁻¹ = Checked.div a⁻¹ b := by
  rw [mul_inv₀, div_eq_mul_inv₀]

theorem div_div_div_comm₀ {hb : IsUnit b} {hd : IsUnit d} {hcd : IsUnit (Checked.div c d)} :
    Checked.div (Checked.div a b) (Checked.div c d) =
      Checked.div (Checked.div a c) (Checked.div b d) := by
  have hc : IsUnit c := IsUnit.of_div₀ hcd
  rw [div_div_eq_mul_div₀, div_div_eq_mul_div₀, div_mul_eq_mul_div₀, div_mul_eq_mul_div₀,
    div_right_comm₀]

theorem div_div_cancel₀ {hb : IsUnit b} {hab : IsUnit (Checked.div a b)} :
    Checked.div a (Checked.div a b) = b := by
  rw [div_div_eq_mul_div₀, mul_div_cancel_left₀]

theorem div_div_cancel_left' {ha : IsUnit a} {hb : IsUnit b} :
    Checked.div (Checked.div a b) a = b⁻¹ := by
  rw [div_eq_mul_inv₀, div_eq_mul_inv₀, mul_right_comm, mul_inv_cancel₀, one_mul]

theorem mul_div_cancel₀ (a : M) {hb : IsUnit b} : b * Checked.div a b = a := by
  rw [mul_comm, div_mul_cancel₀]

theorem div_eq_div_iff {hb : IsUnit b} {hd : IsUnit d} :
    Checked.div a b = Checked.div c d ↔ a * d = c * b := by
  rw [div_eq_iff, div_mul_eq_mul_div₀, eq_div_iff]

theorem mul_eq_mul_of_div_eq_div (a c : M) {hb : IsUnit b} {hd : IsUnit d}
    (h : Checked.div a b = Checked.div c d) : a * d = c * b :=
  div_eq_div_iff.mp h

theorem mul_inv_eq_mul_inv_iff {hb : IsUnit b} {hd : IsUnit d} :
    a * b⁻¹ = c * d⁻¹ ↔ a * d = c * b := by
  rw [← div_eq_mul_inv₀, ← div_eq_mul_inv₀, div_eq_div_iff]

theorem inv_mul_eq_inv_mul_iff {hb : IsUnit b} {hd : IsUnit d} :
    b⁻¹ * a = d⁻¹ * c ↔ a * d = c * b := by
  rw [← div_eq_inv_mul₀, ← div_eq_inv_mul₀, div_eq_div_iff]

/-- The commutative version of `div_eq_div_iff_div_eq_div`. -/
theorem div_eq_div_iff_div_eq_div' {hb : IsUnit b} {hc : IsUnit c} {hd : IsUnit d} :
    Checked.div a b = Checked.div c d ↔ Checked.div a c = Checked.div b d := by
  rw [div_eq_div_iff, div_eq_div_iff, mul_comm c b]

theorem div_eq_div_of_div_eq_div {hc : IsUnit c} {hd : IsUnit d} {hb : IsUnit b}
    (h : Checked.div a b = Checked.div c d) : Checked.div a c = Checked.div b d :=
  div_eq_div_iff_div_eq_div'.mp h

theorem mul_div_mul_right (a b : M) {hbc : IsUnit (b * c)} :
    Checked.div (a * c) (b * c) = Checked.div a b := by
  rw [mul_div_mul_comm₀, div_self, mul_one]

theorem mul_div_mul_left (a b : M) {hcb : IsUnit (c * b)} :
    Checked.div (c * a) (c * b) = Checked.div a b := by
  rw [mul_div_mul_comm₀, div_self, one_mul]

theorem div_mul_cancel_left₀ {hab : IsUnit (a * b)} : Checked.div a (a * b) = b⁻¹ := by
  have ha : IsUnit a := isUnit_of_mul_isUnit_left hab
  rw [div_eq_mul_inv₀, mul_inv₀, mul_inv_cancel_left₀]

theorem div_sq_cancel (a b : M) {ha : IsUnit a} : Checked.div (a ^ 2 * b) a = a * b := by
  rw [sq, mul_assoc, mul_div_cancel_left₀]

theorem div_helper (b : M) {hab : IsUnit (a * b)} :
    Checked.div 1 (a * b) * a = Checked.div 1 b := by
  rw [div_mul_eq_mul_div₀, one_mul, div_mul_cancel_left₀, one_div₀]

theorem div_div_div_cancel_left' (a b : M) {ha : IsUnit a} {hb : IsUnit b}
    {hcb : IsUnit (Checked.div c b)} :
    Checked.div (Checked.div c a) (Checked.div c b) = Checked.div b a := by
  rw [div_div_div_comm₀, div_self, one_div_div₀]

@[simp] theorem div_mul_div_cancel₀' {ha : IsUnit a} (b c : M) {hb : IsUnit b} :
    Checked.div a b * Checked.div c a = Checked.div c b := by
  rw [mul_comm, div_mul_div_cancel₀]

theorem mul_zpow₀ (a b : M) (n : ℤ) {h : n < 0 → IsUnit (a * b)} :
    (a * b) ^ n = Checked.zpow a n (fun hn => isUnit_of_mul_isUnit_left (h hn)) *
      Checked.zpow b n (fun hn => isUnit_of_mul_isUnit_right (h hn)) := by
  cases n with
  | ofNat k => exact mul_pow a b k
  | negSucc k =>
    have hab := h (Int.negSucc_lt_zero k)
    have ha := isUnit_of_mul_isUnit_left hab
    have hb := isUnit_of_mul_isUnit_right hab
    rw [hab.zpow_eq_val_unit_zpow, ha.zpow_eq_val_unit_zpow, hb.zpow_eq_val_unit_zpow,
      ← Units.val_mul, ← mul_zpow]
    congr 2
    ext
    rfl

theorem div_zpow₀ (a b : M) (n : ℤ) {hb : IsUnit b} {h : n < 0 → IsUnit (Checked.div a b)} :
    (Checked.div a b) ^ n =
      Checked.div (Checked.zpow a n (fun hn => IsUnit.of_div₀ (h hn))) (b ^ n) := by
  cases n with
  | ofNat k => exact div_pow₀ a b k
  | negSucc k =>
    have hab := h (Int.negSucc_lt_zero k)
    have ha : IsUnit a := IsUnit.of_div₀ hab
    have hbn : IsUnit (b ^ Int.negSucc k) := hb.zpow₀ _
    rw [div_eq_mul_inv₀ _ (b ^ Int.negSucc k), ← inv_zpow₀ b _ (ha := hb),
      hab.zpow_eq_val_unit_zpow, ha.zpow_eq_val_unit_zpow, hb.inv₀.zpow_eq_val_unit_zpow,
      ← Units.val_mul, ← mul_zpow]
    congr 2
    ext
    rfl

end CommMonoid

/-! ### Monoids with zero -/

section MonoidWithZero
variable [MonoidWithZero M] {a b : M}

@[simp] theorem zero_div (a : M) {ha : IsUnit a} : Checked.div 0 a = 0 := zero_mul _

@[simp] theorem div_eq_zero_iff {hb : IsUnit b} : Checked.div a b = 0 ↔ a = 0 where
  mp h := by rw [← div_mul_cancel₀ a (hb := hb), h, zero_mul]
  mpr h := by subst h; exact zero_div b

theorem div_ne_zero_iff {hb : IsUnit b} : Checked.div a b ≠ 0 ↔ a ≠ 0 := div_eq_zero_iff.not

theorem div_ne_zero (ha : a ≠ 0) {hb : IsUnit b} : Checked.div a b ≠ 0 := div_ne_zero_iff.2 ha

variable [Nontrivial M]

@[simp] theorem inv_ne_zero {ha : IsUnit a} : a⁻¹ ≠ 0 := fun h => by
  have e := mul_inv_cancel₀ (ha := ha)
  rw [h, mul_zero] at e
  exact zero_ne_one e

theorem one_div_ne_zero {ha : IsUnit a} : Checked.div 1 a ≠ 0 := by
  rw [one_div₀]; exact inv_ne_zero

end MonoidWithZero

/-! ### Groups with zero -/

section GroupWithZero
variable [GroupWithZero M]

instance (priority := 100) GroupWithZero.toIsDedekindFiniteMonoid : IsDedekindFiniteMonoid M where
  mul_eq_one_symm {a b} h := by
    have ha : a ≠ 0 := by rintro rfl; exact zero_ne_one (by rwa [zero_mul] at h)
    have := GroupWithZero.isUnit_of_ne_zero ha
    rw [← inv_eq_of_mul_eq_one_right₀ (ha := this) h, inv_mul_cancel₀]

end GroupWithZero
