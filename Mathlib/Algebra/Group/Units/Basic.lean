/-
Copyright (c) 2017 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johannes Hölzl, Chris Hughes, Jens Wagemaker, Jon Eugster
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Commute.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Basic.Unique
public import Mathlib.Tactic.Lift
public import Mathlib.Tactic.Subsingleton
public import Mathlib.Tactic.Attr.Core


/-!
# Units (i.e., invertible elements) of a monoid

An element of a `Monoid` is a unit if it has a two-sided inverse.
This file contains the basic lemmas on units in a monoid, especially focusing on singleton types
and unique types.

## TODO

The results here should be used to golf the basic `Group` lemmas.
-/

public section

assert_not_exists Multiplicative MonoidWithZero DenselyOrdered

open Function

universe u

variable {α : Type u}

section HasElem

@[to_additive]
theorem unique_one {α : Type*} [Unique α] [One α] : default = (1 : α) :=
  Unique.default_eq 1

end HasElem

namespace Units
section Monoid
variable [Monoid α]

variable (b c : αˣ) {u : αˣ}

@[to_additive (attr := simp)]
theorem mul_inv_cancel_right (a : α) (b : αˣ) : a * b * ↑b⁻¹ = a := by
  rw [mul_assoc, mul_inv, mul_one]

@[to_additive (attr := simp)]
theorem inv_mul_cancel_right (a : α) (b : αˣ) : a * ↑b⁻¹ * b = a := by
  rw [mul_assoc, inv_mul, mul_one]

@[to_additive (attr := simp)]
theorem mul_right_inj (a : αˣ) {b c : α} : (a : α) * b = a * c ↔ b = c :=
  ⟨fun h => by simpa only [inv_mul_cancel_left] using congr_arg (fun x : α => ↑(a⁻¹ : αˣ) * x) h,
    congr_arg _⟩

@[to_additive (attr := simp)]
theorem mul_left_inj (a : αˣ) {b c : α} : b * a = c * a ↔ b = c :=
  ⟨fun h => by simpa only [mul_inv_cancel_right] using congr_arg (fun x : α => x * ↑(a⁻¹ : αˣ)) h,
    congr_arg (· * a.val)⟩

@[to_additive]
theorem eq_mul_inv_iff_mul_eq {a b : α} : a = b * ↑c⁻¹ ↔ a * c = b :=
  ⟨fun h => by rw [h, inv_mul_cancel_right], fun h => by rw [← h, mul_inv_cancel_right]⟩

@[to_additive]
theorem eq_inv_mul_iff_mul_eq {a c : α} : a = ↑b⁻¹ * c ↔ ↑b * a = c :=
  ⟨fun h => by rw [h, mul_inv_cancel_left], fun h => by rw [← h, inv_mul_cancel_left]⟩

@[to_additive]
theorem mul_inv_eq_iff_eq_mul {a c : α} : a * ↑b⁻¹ = c ↔ a = c * b :=
  ⟨fun h => by rw [← h, inv_mul_cancel_right], fun h => by rw [h, mul_inv_cancel_right]⟩

@[to_additive]
protected theorem inv_eq_of_mul_eq_one_left {a : α} (h : a * u = 1) : ↑u⁻¹ = a :=
  calc
    ↑u⁻¹ = 1 * ↑u⁻¹ := by rw [one_mul]
    _ = a := by rw [← h, mul_inv_cancel_right]

@[to_additive]
protected theorem inv_eq_of_mul_eq_one_right {a : α} (h : ↑u * a = 1) : ↑u⁻¹ = a :=
  calc
    ↑u⁻¹ = ↑u⁻¹ * 1 := by rw [mul_one]
    _ = a := by rw [← h, inv_mul_cancel_left]

@[to_additive]
protected theorem eq_inv_of_mul_eq_one_left {a : α} (h : ↑u * a = 1) : a = ↑u⁻¹ :=
  (Units.inv_eq_of_mul_eq_one_right h).symm

@[to_additive]
protected theorem eq_inv_of_mul_eq_one_right {a : α} (h : a * u = 1) : a = ↑u⁻¹ :=
  (Units.inv_eq_of_mul_eq_one_left h).symm

@[to_additive (attr := simp)]
theorem mul_inv_eq_one {a : α} : a * ↑u⁻¹ = 1 ↔ a = u :=
  ⟨inv_inv u ▸ Units.eq_inv_of_mul_eq_one_right, fun h => mul_inv_of_eq h.symm⟩

@[to_additive (attr := simp)]
theorem inv_mul_eq_one {a : α} : ↑u⁻¹ * a = 1 ↔ ↑u = a :=
  ⟨inv_inv u ▸ Units.inv_eq_of_mul_eq_one_right, inv_mul_of_eq⟩

@[to_additive]
theorem mul_eq_one_iff_eq_inv {a : α} : a * u = 1 ↔ a = ↑u⁻¹ := by rw [← mul_inv_eq_one, inv_inv]

@[to_additive]
theorem mul_eq_one_iff_inv_eq {a : α} : ↑u * a = 1 ↔ ↑u⁻¹ = a := by rw [← inv_mul_eq_one, inv_inv]

@[to_additive]
theorem inv_unique {u₁ u₂ : αˣ} (h : (↑u₁ : α) = ↑u₂) : (↑u₁⁻¹ : α) = ↑u₂⁻¹ :=
  Units.inv_eq_of_mul_eq_one_right <| by rw [h, u₂.mul_inv]

@[to_additive (attr := simp)]
theorem val_inv_inj {u₁ u₂ : αˣ} : ((u₁⁻¹ : αˣ) : α) = u₂⁻¹ ↔ (u₁ : α) = u₂ :=
  Units.ext_iff.symm.trans <| inv_inj.trans Units.ext_iff

end Monoid

section CommMonoid

variable [CommMonoid α] (a c : α) (b d : αˣ)

@[to_additive]
theorem mul_inv_eq_mul_inv_iff : a * b⁻¹ = c * d⁻¹ ↔ a * d = c * b := by
  rw [mul_comm c, Units.mul_inv_eq_iff_eq_mul, mul_assoc, Units.eq_inv_mul_iff_mul_eq, mul_comm]

@[to_additive]
theorem inv_mul_eq_inv_mul_iff : b⁻¹ * a = d⁻¹ * c ↔ a * d = c * b := by
  rw [mul_comm, mul_comm _ c, mul_inv_eq_mul_inv_iff]

end CommMonoid

end Units

section Monoid

variable [Monoid α]

@[simp]
theorem divp_left_inj (u : αˣ) {a b : α} : a /ₚ u = b /ₚ u ↔ a = b :=
  Units.mul_left_inj _

theorem divp_eq_iff_mul_eq {x : α} {u : αˣ} {y : α} : x /ₚ u = y ↔ y * u = x :=
  u.mul_left_inj.symm.trans <| by rw [divp_mul_cancel]; exact ⟨Eq.symm, Eq.symm⟩

theorem eq_divp_iff_mul_eq {x : α} {u : αˣ} {y : α} : x = y /ₚ u ↔ x * u = y := by
  rw [eq_comm, divp_eq_iff_mul_eq]

theorem divp_eq_one_iff_eq {a : α} {u : αˣ} : a /ₚ u = 1 ↔ a = u :=
  (Units.mul_left_inj u).symm.trans <| by rw [divp_mul_cancel, one_mul]

theorem inv_eq_one_divp' (u : αˣ) : ((1 / u : αˣ) : α) = 1 /ₚ u := by
  rw [one_div, one_divp]

end Monoid

section IsDedekindFiniteMonoid

variable [Monoid α] [IsDedekindFiniteMonoid α] [Subsingleton αˣ] {a b : α}

@[to_additive]
theorem eq_one_of_mul_right (h : a * b = 1) : a = 1 :=
  congr_arg Units.inv <| Subsingleton.elim (Units.mk _ _ (mul_eq_one_symm h) h) 1

@[to_additive]
theorem eq_one_of_mul_left (h : a * b = 1) : b = 1 := by
  rwa [eq_one_of_mul_right h, one_mul] at h

@[to_additive (attr := simp)]
theorem mul_eq_one : a * b = 1 ↔ a = 1 ∧ b = 1 :=
  ⟨fun h => ⟨eq_one_of_mul_right h, eq_one_of_mul_left h⟩, by
    rintro ⟨rfl, rfl⟩
    exact mul_one _⟩

@[to_additive]
theorem mul_ne_one : a * b ≠ 1 ↔ a ≠ 1 ∨ b ≠ 1 := by rw [not_iff_comm]; simp

@[to_additive (attr := deprecated (since := "2026-07-07"))]
alias eq_one_of_mul_left' := eq_one_of_mul_left

@[to_additive (attr := deprecated (since := "2026-07-07"))]
alias eq_one_of_mul_right' := eq_one_of_mul_right

@[to_additive (attr := deprecated (since := "2026-07-07"))]
alias mul_eq_one' := mul_eq_one

@[to_additive (attr := deprecated (since := "2026-07-07"))]
alias mul_ne_one' := mul_ne_one

end IsDedekindFiniteMonoid

section CommMonoid

variable [CommMonoid α]

theorem divp_mul_eq_mul_divp (x y : α) (u : αˣ) : x /ₚ u * y = x * y /ₚ u := by
  rw [divp, divp, mul_right_comm]

theorem divp_eq_divp_iff {x y : α} {ux uy : αˣ} : x /ₚ ux = y /ₚ uy ↔ x * uy = y * ux := by
  rw [divp_eq_iff_mul_eq, divp_mul_eq_mul_divp, divp_eq_iff_mul_eq]

theorem divp_mul_divp (x y : α) (ux uy : αˣ) : x /ₚ ux * (y /ₚ uy) = x * y /ₚ (ux * uy) := by
  rw [divp_mul_eq_mul_divp, ← divp_assoc, divp_divp_eq_divp_mul]

end CommMonoid

/-!
### `IsUnit` predicate
-/


section IsUnit

variable {M : Type*}

@[to_additive (attr := nontriviality)]
theorem isUnit_of_subsingleton [Monoid M] [Subsingleton M] (a : M) : IsUnit a :=
  ⟨⟨a, a, by subsingleton, by subsingleton⟩, rfl⟩

@[to_additive]
instance [Monoid M] : CanLift M Mˣ Units.val IsUnit :=
  { prf := fun _ ↦ id }

/-- A subsingleton `Monoid` has a unique unit. -/
@[to_additive /-- A subsingleton `AddMonoid` has a unique additive unit. -/]
instance [Monoid M] [Subsingleton M] : Unique Mˣ where
  uniq _ := Units.val_eq_one.mp (by subsingleton)

namespace IsUnit

section Monoid

variable [Monoid M] {a b c : M}

@[simp]
protected lemma div_mul_cancel (h : IsUnit b) (a : M) : a /ₚ h.unit * b = a :=
  divp_mul_cancel a h.unit

@[simp]
protected lemma mul_div_cancel_right (h : IsUnit b) (a : M) : a * b /ₚ h.unit = a :=
  mul_divp_cancel a h.unit

protected lemma mul_one_div_cancel (h : IsUnit a) : a * (1 /ₚ h.unit) = 1 := by
  rw [one_divp, h.mul_val_inv]

protected lemma one_div_mul_cancel (h : IsUnit a) : (1 /ₚ h.unit) * a = 1 := by
  rw [one_divp, h.val_inv_mul]

protected lemma div_left_inj (h : IsUnit c) : a /ₚ h.unit = b /ₚ h.unit ↔ a = b :=
  divp_left_inj h.unit

protected lemma div_eq_iff (h : IsUnit b) : a /ₚ h.unit = c ↔ a = c * b :=
  divp_eq_iff_mul_eq.trans eq_comm

protected lemma eq_div_iff (h : IsUnit c) : a = b /ₚ h.unit ↔ a * c = b :=
  eq_divp_iff_mul_eq

protected lemma div_eq_of_eq_mul (h : IsUnit b) : a = c * b → a /ₚ h.unit = c :=
  h.div_eq_iff.2

protected lemma eq_div_of_mul_eq (h : IsUnit c) : a * c = b → a = b /ₚ h.unit :=
  h.eq_div_iff.2

protected lemma mul_mul_div (a : M) (h : IsUnit b) : a * b * (1 /ₚ h.unit) = a := by
  rw [one_divp]
  exact Units.mul_inv_cancel_right a h.unit

protected lemma div_eq_one_iff_eq (h : IsUnit b) : a /ₚ h.unit = 1 ↔ a = b :=
  divp_eq_one_iff_eq

@[to_additive]
theorem mul_left_inj (h : IsUnit a) : b * a = c * a ↔ b = c :=
  let ⟨u, hu⟩ := h
  hu ▸ u.mul_left_inj

@[to_additive]
theorem mul_right_inj (h : IsUnit a) : a * b = a * c ↔ b = c :=
  let ⟨u, hu⟩ := h
  hu ▸ u.mul_right_inj

@[to_additive]
protected theorem mul_left_cancel (h : IsUnit a) : a * b = a * c → b = c :=
  h.mul_right_inj.1

@[to_additive]
protected theorem mul_right_cancel (h : IsUnit b) : a * b = c * b → a = c :=
  h.mul_left_inj.1

@[to_additive]
theorem mul_eq_right (h : IsUnit b) : a * b = b ↔ a = 1 := calc
  a * b = b ↔ a * b = 1 * b := by rw [one_mul]
    _ ↔ a = 1 := by rw [h.mul_left_inj]

@[to_additive]
theorem mul_eq_left (h : IsUnit a) : a * b = a ↔ b = 1 := calc
  a * b = a ↔ a * b = a * 1 := by rw [mul_one]
    _ ↔ b = 1 := by rw [h.mul_right_inj]

@[to_additive]
protected theorem mul_right_injective (h : IsUnit a) : Injective (a * ·) :=
  fun _ _ => h.mul_left_cancel

@[to_additive]
protected theorem mul_left_injective (h : IsUnit b) : Injective (· * b) :=
  fun _ _ => h.mul_right_cancel

@[to_additive]
theorem isUnit_iff_mulLeft_bijective {a : M} :
    IsUnit a ↔ Function.Bijective (a * ·) :=
  ⟨fun h ↦ ⟨h.mul_right_injective, fun y ↦ ⟨h.unit⁻¹ * y, by simp [← mul_assoc]⟩⟩, fun h ↦
    ⟨⟨a, _, (h.2 1).choose_spec, h.1
      (by simpa [mul_assoc] using congr_arg (· * a) (h.2 1).choose_spec)⟩, rfl⟩⟩

@[to_additive]
theorem isUnit_iff_mulRight_bijective {a : M} :
    IsUnit a ↔ Function.Bijective (· * a) :=
  ⟨fun h ↦ ⟨h.mul_left_injective, fun y ↦ ⟨y * h.unit⁻¹, by simp [mul_assoc]⟩⟩,
    fun h ↦ ⟨⟨a, _, h.1 (by simpa [mul_assoc] using congr_arg (a * ·) (h.2 1).choose_spec),
      (h.2 1).choose_spec⟩, rfl⟩⟩

end Monoid

section CommMonoid
variable [CommMonoid M] {a b c d : M}

protected lemma mul_div_cancel_left (h : IsUnit a) (b : M) : a * b /ₚ h.unit = b := by
  rw [mul_comm, h.mul_div_cancel_right]

protected lemma mul_div_cancel (h : IsUnit a) (b : M) : a * (b /ₚ h.unit) = b := by
  rw [mul_comm, h.div_mul_cancel]

protected lemma div_eq_div_iff (hb : IsUnit b) (hd : IsUnit d) :
    a /ₚ hb.unit = c /ₚ hd.unit ↔ a * d = c * b :=
  divp_eq_divp_iff

protected lemma mul_eq_mul_of_div_eq_div (hb : IsUnit b) (hd : IsUnit d)
    (a c : M) (h : a /ₚ hb.unit = c /ₚ hd.unit) : a * d = c * b :=
  (hb.div_eq_div_iff hd).mp h

end CommMonoid

section DivisionMonoid
variable [DivisionMonoid α] {a b c : α}

@[to_additive (attr := simp)]
protected lemma mul_inv_cancel_right (h : IsUnit b) (a : α) : a * b * b⁻¹ = a :=
  h.unit'.mul_inv_cancel_right _

@[to_additive (attr := simp)]
protected lemma inv_mul_cancel_right (h : IsUnit b) (a : α) : a * b⁻¹ * b = a :=
  h.unit'.inv_mul_cancel_right _

@[to_additive]
protected lemma eq_mul_inv_iff_mul_eq (h : IsUnit c) : a = b * c⁻¹ ↔ a * c = b :=
  h.unit'.eq_mul_inv_iff_mul_eq

@[to_additive]
protected lemma eq_inv_mul_iff_mul_eq (h : IsUnit b) : a = b⁻¹ * c ↔ b * a = c :=
  h.unit'.eq_inv_mul_iff_mul_eq

@[to_additive]
protected lemma inv_mul_eq_iff_eq_mul (h : IsUnit a) : a⁻¹ * b = c ↔ b = a * c :=
  h.unit'.inv_mul_eq_iff_eq_mul

@[to_additive]
protected lemma mul_inv_eq_iff_eq_mul (h : IsUnit b) : a * b⁻¹ = c ↔ a = c * b :=
  h.unit'.mul_inv_eq_iff_eq_mul

@[to_additive]
protected lemma mul_inv_eq_one (h : IsUnit b) : a * b⁻¹ = 1 ↔ a = b :=
  @Units.mul_inv_eq_one _ _ h.unit' _

@[to_additive]
protected lemma inv_mul_eq_one (h : IsUnit a) : a⁻¹ * b = 1 ↔ a = b :=
  @Units.inv_mul_eq_one _ _ h.unit' _

@[to_additive]
protected lemma mul_eq_one_iff_eq_inv (h : IsUnit b) : a * b = 1 ↔ a = b⁻¹ :=
  @Units.mul_eq_one_iff_eq_inv _ _ h.unit' _

@[to_additive]
protected lemma mul_eq_one_iff_inv_eq (h : IsUnit a) : a * b = 1 ↔ a⁻¹ = b :=
  @Units.mul_eq_one_iff_inv_eq _ _ h.unit' _

end DivisionMonoid

section DivisionCommMonoid
variable [DivisionCommMonoid α] {a b c d : α}

@[to_additive]
protected lemma mul_inv_eq_mul_inv_iff (hb : IsUnit b) (hd : IsUnit d) :
    a * b⁻¹ = c * d⁻¹ ↔ a * d = c * b :=
  Units.mul_inv_eq_mul_inv_iff a c hb.unit' hd.unit'

@[to_additive]
protected lemma inv_mul_eq_inv_mul_iff (hb : IsUnit b) (hd : IsUnit d) :
    b⁻¹ * a = d⁻¹ * c ↔ a * d = c * b :=
  Units.inv_mul_eq_inv_mul_iff a c hb.unit' hd.unit'

@[to_additive IsAddUnit.add_neg_add_neg_cancel]
protected lemma div_div_cancel (h : IsUnit a) :
    a * (a * b⁻¹)⁻¹ = b := by
  rw [mul_inv_rev, inv_inv, mul_left_comm, h.mul_inv_cancel, mul_one]

protected lemma div_div_cancel_left (h : IsUnit a) : a * b⁻¹ /ₚ h.unit = b⁻¹ :=
  h.mul_div_cancel_left _

end DivisionCommMonoid
end IsUnit

namespace IsAddUnit
section SubtractionMonoid
variable [SubtractionMonoid α] {a b c : α}

@[simp]
protected lemma sub_add_cancel (h : IsAddUnit b) (a : α) : a - b + b = a := by
  rw [sub_eq_add_neg, h.neg_add_cancel_right]

@[simp]
protected lemma add_sub_cancel_right (h : IsAddUnit b) (a : α) : a + b - b = a := by
  rw [sub_eq_add_neg, h.add_neg_cancel_right]

protected lemma add_zero_sub_cancel (h : IsAddUnit a) : a + (0 - a) = 0 := by simp [h]

protected lemma zero_sub_add_cancel (h : IsAddUnit a) : 0 - a + a = 0 := by simp [h]

protected lemma sub_left_inj (h : IsAddUnit c) : a - c = b - c ↔ a = b := by
  simp only [sub_eq_add_neg]
  exact AddUnits.add_left_inj h.neg.addUnit'

protected lemma sub_eq_iff (h : IsAddUnit b) : a - b = c ↔ a = c + b := by
  rw [sub_eq_add_neg, h.add_neg_eq_iff_eq_add]

protected lemma eq_sub_iff (h : IsAddUnit c) : a = b - c ↔ a + c = b := by
  rw [sub_eq_add_neg, h.eq_add_neg_iff_add_eq]

protected lemma sub_eq_of_eq_add (h : IsAddUnit b) : a = c + b → a - b = c :=
  h.sub_eq_iff.2

protected lemma eq_sub_of_add_eq (h : IsAddUnit c) : a + c = b → a = b - c :=
  h.eq_sub_iff.2

protected lemma add_add_sub (a : α) (h : IsAddUnit b) : a + b + (0 - b) = a := by simp [h]

protected lemma sub_eq_zero_iff_eq (h : IsAddUnit b) : a - b = 0 ↔ a = b := by
  rw [sub_eq_add_neg, h.add_neg_eq_zero]

protected lemma sub_add_left (h : IsAddUnit b) : b - (a + b) = 0 - a := by
  rw [h.sub_add_cancel_right, zero_sub]

end SubtractionMonoid

section SubtractionCommMonoid
variable [SubtractionCommMonoid α] {a b c d : α}

protected lemma add_sub_cancel_left (h : IsAddUnit a) (b : α) : a + b - a = b := by
  rw [add_comm, h.add_sub_cancel_right]

protected lemma add_sub_cancel (h : IsAddUnit a) (b : α) : a + (b - a) = b := by
  rw [add_comm, h.sub_add_cancel]

protected lemma sub_eq_sub_iff (hb : IsAddUnit b) (hd : IsAddUnit d) :
    a - b = c - d ↔ a + d = c + b := by
  rw [← (hb.add hd).add_left_inj, ← add_assoc, hb.sub_add_cancel, ← add_assoc, add_right_comm,
    hd.sub_add_cancel]

protected lemma sub_sub_cancel_left (h : IsAddUnit a) : a - b - a = -b := by
  rw [sub_eq_add_neg, sub_eq_add_neg, add_right_comm, h.add_neg_cancel, zero_add]

protected lemma sub_sub_cancel (h : IsAddUnit a) : a - (a - b) = b := by
  simpa only [sub_eq_add_neg] using h.add_neg_add_neg_cancel (b := b)

protected lemma sub_add_right (h : IsAddUnit a) (b : α) : a - (a + b) = 0 - b := by
  rw [h.sub_add_cancel_left, zero_sub]

protected lemma add_eq_add_of_sub_eq_sub (hb : IsAddUnit b) (hd : IsAddUnit d)
    (a c : α) (h : a - b = c - d) : a + d = c + b :=
  (hb.sub_eq_sub_iff hd).mp h

end SubtractionCommMonoid
end IsAddUnit

-- namespace
end IsUnit
