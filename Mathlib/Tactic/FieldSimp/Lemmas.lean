/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Arend Mellendijk, Michael Rothgang
-/
module

public import Mathlib.Algebra.GroupWithZero.Checked
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Units
public meta import Mathlib.Util.Qq

/-!
# Certificates for clearing unit denominators

Every normalized fraction has an actual unit as denominator. Inversion transports the original
invertibility evidence to its normalized numerator before reversing the fraction.
-/

public section

namespace Mathlib.Tactic.FieldSimp

variable {M : Type*}

/-- A unit gives the nonzero evidence needed for an order-preserving square multiplier. -/
theorem unit_sq_pos [CommRing M] [LinearOrder M] [IsStrictOrderedRing M]
    (u : Mˣ) : 0 < (u : M) ^ (2 : ℕ) := by
  rw [pow_two]
  exact mul_self_pos.mpr u.ne_zero

/-- The product form also recognizes a repeated common denominator. -/
theorem unit_mul_self_pos [CommRing M] [LinearOrder M] [IsStrictOrderedRing M]
    (u : Mˣ) : 0 < (↑(u * u) : M) := mul_self_pos.mpr u.ne_zero

section CommMonoid
variable [CommMonoid M]

/-- The numerator of a normalized unit is a unit, with its original numerator as value. -/
@[expose] noncomputable def numeratorUnit (a n : M) (u : Mˣ)
    (ha : IsUnit a) (h : a = n /ₚ u) : Mˣ :=
  (ha.unit * u).copy n (by
    change n = a * u
    rw [h, divp_mul_cancel]) _ rfl

@[simp] theorem numeratorUnit_val (a n : M) (u : Mˣ) (ha : IsUnit a) (h : a = n /ₚ u) :
    (numeratorUnit a n u ha h : M) = n := rfl

theorem normalize_atom (a : M) : a = a /ₚ (1 : Mˣ) := (divp_one a).symm

theorem normalize_mul {a b na nb : M} {u v : Mˣ}
    (ha : a = na /ₚ u) (hb : b = nb /ₚ v) :
    a * b = (na * nb) /ₚ (u * v) := by
  rw [ha, hb, divp_mul_divp]

theorem normalize_pow {a n : M} {u : Mˣ} (ha : a = n /ₚ u) (k : ℕ) :
    a ^ k = n ^ k /ₚ (u ^ k) := by
  rw [ha]
  simp only [divp, mul_pow]
  rw [← Units.val_pow_eq_pow_val, inv_pow]

theorem normalize_inv {a n : M} {u : Mˣ} (ha : IsUnit a) (h : a = n /ₚ u) :
    Checked.inv a ha = (u : M) /ₚ numeratorUnit a n u ha h := by
  apply eq_divp_iff_mul_eq.mpr
  change Checked.inv a ha * n = u
  rw [← eq_divp_iff_mul_eq.mp h, ← mul_assoc, Checked.inv_mul_cancel, one_mul]

theorem normalize_div {a b na nb : M} {u v : Mˣ} (hb : IsUnit b)
    (ha' : a = na /ₚ u) (hb' : b = nb /ₚ v) :
    Checked.div a b hb = (na * v) /ₚ (u * numeratorUnit b nb v hb hb') := by
  apply eq_divp_iff_mul_eq.mpr
  change Checked.div a b hb * ((u : M) * nb) = na * v
  rw [← eq_divp_iff_mul_eq.mp hb']
  calc
    Checked.div a b hb * ((u : M) * (b * v)) =
        (Checked.div a b hb * b) * u * v := by ac_rfl
    _ = a * u * v := by rw [Checked.div_mul_cancel]
    _ = na * v := by rw [eq_divp_iff_mul_eq.mp ha']

theorem normalize_divp {a na nb : M} {u v w : Mˣ}
    (ha : a = na /ₚ u) (hb : (w : M) = nb /ₚ v) :
    a /ₚ w = (na * v) /ₚ (u * numeratorUnit (w : M) nb v w.isUnit hb) := by
  simpa only [Checked.div, IsUnit.unit_of_val_units] using normalize_div w.isUnit ha hb

theorem clear_eq {a b na nb : M} {u v : Mˣ}
    (ha : a = na /ₚ u) (hb : b = nb /ₚ v) :
    (a = b) = (na * v = nb * u) := by
  rw [ha, hb]
  exact propext divp_eq_divp_iff

theorem common_denominator {a n : M} {u : Mˣ} (ha : a = n /ₚ u) (v : Mˣ) :
    a * (↑(u * v) : M) = n * v := by
  rw [ha, Units.val_mul, ← mul_assoc, divp_mul_cancel]

theorem common_denominator_right {a n : M} {v : Mˣ} (ha : a = n /ₚ v) (u : Mˣ) :
    a * (↑(u * v) : M) = n * u := by
  rw [mul_comm u v]
  exact common_denominator ha u

theorem square_denominator {a n c : M} (h : a * c = n) :
    a * c ^ 2 = n * c := by rw [pow_two, ← mul_assoc, h]

end CommMonoid

theorem normalize_add [CommSemiring M] {a b na nb : M} {u v : Mˣ}
    (ha : a = na /ₚ u) (hb : b = nb /ₚ v) :
    a + b = (na * v + nb * u) /ₚ (u * v) := by
  rw [ha, hb, Units.divp_add_divp, mul_comm (u : M) nb]

theorem normalize_sub [CommRing M] {a b na nb : M} {u v : Mˣ}
    (ha : a = na /ₚ u) (hb : b = nb /ₚ v) :
    a - b = (na * v - nb * u) /ₚ (u * v) := by
  rw [ha, hb, Units.divp_sub_divp, mul_comm (u : M) nb]

theorem normalize_neg [Ring M] {a n : M} {u : Mˣ} (ha : a = n /ₚ u) :
    -a = -n /ₚ u := by rw [ha, Units.neg_divp]

theorem checked_zpow_negSucc [Monoid M] (a : M) (k : ℕ)
    (ha : (Int.negSucc k : ℤ) < 0 → IsUnit a) :
    Checked.zpow a (Int.negSucc k) ha =
      Checked.inv a (ha (Int.negSucc_lt_zero _)) ^ (k + 1) := by
  simp only [Checked.zpow, zpow_negSucc, Checked.inv]
  rw [← inv_pow, Units.val_pow_eq_pow_val]

theorem clear_le [MonoidWithZero M] [PartialOrder M] [MulPosMono M] [MulPosReflectLE M]
    {a b c na nb : M} (hc : 0 < c) (ha : a * c = na) (hb : b * c = nb) :
    (a ≤ b) = (na ≤ nb) := by
  calc
    (a ≤ b) = (a * c ≤ b * c) := propext (mul_le_mul_iff_of_pos_right hc).symm
    _ = (na ≤ nb) := by rw [ha, hb]

theorem clear_lt [MonoidWithZero M] [PartialOrder M] [MulPosStrictMono M]
    [MulPosReflectLT M] {a b c na nb : M} (hc : 0 < c)
    (ha : a * c = na) (hb : b * c = nb) :
    (a < b) = (na < nb) := by
  calc
    (a < b) = (a * c < b * c) := propext (mul_lt_mul_iff_of_pos_right hc).symm
    _ = (na < nb) := by rw [ha, hb]

end Mathlib.Tactic.FieldSimp
