/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Order.Quantale
public import Mathlib.Basic.ENNReal.Operations

/-!
# Results about division in extended non-negative reals

This file establishes properties of reciprocal, integer powers, and quotients on `ℝ≥0∞`.
For finite inputs with positive denominator, `ENNReal.coe_div` gives agreement with exact
division under the embedding `ℝ≥0 → ℝ≥0∞`. The continuous quotient `ENNReal.extendedDiv`
also allows a nonzero numerator over zero.

The total infimum quotient `ENNReal.divInf a b` is `sInf {q | a ≤ b * q}`.
The quantale residual `b ⇨ₗ a` is `sSup {q | q * b ≤ a}`. They agree exactly on the
domain of the continuous quotient.

## Main results

A few order isomorphisms are worthy of mention:

  - `OrderIso.invENNReal : ℝ≥0∞ ≃o ℝ≥0∞ᵒᵈ`: The map `x ↦ x⁻¹` as an order isomorphism to the dual.

  - `orderIsoIicOneBirational : ℝ≥0∞ ≃o Iic (1 : ℝ≥0∞)`: The birational order isomorphism between
    `ℝ≥0∞` and the unit interval `Set.Iic (1 : ℝ≥0∞)` given by `x ↦ (x⁻¹ + 1)⁻¹` with inverse
    `x ↦ (x⁻¹ - 1)⁻¹`

  - `orderIsoIicCoe (a : ℝ≥0) : Iic (a : ℝ≥0∞) ≃o Iic a`: Order isomorphism between an initial
    interval in `ℝ≥0∞` and an initial interval in `ℝ≥0` given by the identity map.

  - `orderIsoUnitIntervalBirational : ℝ≥0∞ ≃o Icc (0 : ℝ) 1`: An order isomorphism between
    the extended nonnegative real numbers and the unit interval. This is `orderIsoIicOneBirational`
    composed with the identity order isomorphism between `Iic (1 : ℝ≥0∞)` and `Icc (0 : ℝ) 1`.
-/

@[expose] public section

assert_not_exists Finset

open Set NNReal

namespace ENNReal

noncomputable section Inv

variable {a b c d : ℝ≥0∞} {r p q : ℝ≥0}

theorem extendedDiv_eq_mul_inv (a b : ℝ≥0∞) (h) : extendedDiv a b h = a * b⁻¹ := rfl

protected theorem div_eq_mul_inv (a b : ℝ≥0∞) (h) : div a b h = a * b⁻¹ := rfl

protected theorem div_eq_inv_mul (a b : ℝ≥0∞) (h) : div a b h = b⁻¹ * a := mul_comm _ _

@[simp] theorem one_div (a : ℝ≥0∞) (ha : a ≠ 0) :
    div 1 a ⟨ha, Or.inl one_ne_top⟩ = a⁻¹ := one_mul _

protected theorem div_right_comm (hab h₁ hac h₂) :
    div (div a b hab) c h₁ = div (div a c hac) b h₂ :=
  mul_right_comm _ _ _

@[simp] theorem inv_zero : (0 : ℝ≥0∞)⁻¹ = ∞ :=
  show sInf { b : ℝ≥0∞ | 1 ≤ 0 * b } = ∞ by simp

@[simp] theorem inv_top : ∞⁻¹ = 0 :=
  bot_unique <| le_of_forall_gt_imp_ge_of_dense fun a (h : 0 < a) => sInf_le <| by
    simp [*, h.ne', top_mul]

/-- The inverse of an invertible element of `ℝ≥0` is its inverse in `ℝ≥0∞`. -/
@[simp, norm_cast]
theorem coe_inv {hr : IsUnit r} : (↑r⁻¹ : ℝ≥0∞) = (↑r)⁻¹ := by
  refine le_antisymm (le_sInf fun b (hb : 1 ≤ ↑r * b) => coe_le_iff.2 ?_) <|
    sInf_le <| mem_ofPred.2 <| by rw [← coe_mul, mul_inv_cancel₀, coe_one]
  rintro b rfl
  rw [← coe_mul, ← coe_one, coe_le_coe] at hb
  exact NNReal.inv_le.2 hb

@[norm_cast]
theorem coe_inv_two : ((2⁻¹ : ℝ≥0) : ℝ≥0∞) = 2⁻¹ := by rw [coe_inv, coe_two]

@[simp, norm_cast]
theorem coe_div {hr : IsUnit r} :
    (↑(p / r) : ℝ≥0∞) = div p r ⟨coe_ne_zero.2 hr.ne_zero, Or.inr coe_ne_top⟩ := by
  rw [div_eq_mul_inv₀, ENNReal.div_eq_mul_inv, coe_mul, coe_inv]

@[simp] theorem extendedDiv_zero (ha : a ≠ 0) :
    extendedDiv a 0 ⟨Or.inl ha, Or.inr zero_ne_top⟩ = ∞ := by
  simp [extendedDiv, ha]

@[simp] theorem extendedDiv_top (ha : a ≠ ∞) :
    extendedDiv a ∞ ⟨Or.inr top_ne_zero, Or.inl ha⟩ = 0 := by
  simp [extendedDiv]

@[simp] protected theorem inv_one : (1 : ℝ≥0∞)⁻¹ = 1 := by
  simpa only [coe_inv, coe_one] using coe_inj.2 (inv_one₀ (M := ℝ≥0))

@[simp] protected theorem div_one (a : ℝ≥0∞) :
    div a 1 ⟨one_ne_zero, Or.inr one_ne_top⟩ = a := by
  simp [ENNReal.div_eq_mul_inv]

protected theorem inv_pow : ∀ {a : ℝ≥0∞} {n : ℕ}, (a ^ n)⁻¹ = a⁻¹ ^ n
  | _, 0 => by simp only [pow_zero, ENNReal.inv_one]
  | ⊤, n + 1 => by simp [top_pow]
  | (a : ℝ≥0), n + 1 => by
    rcases eq_or_ne a 0 with (rfl | ha)
    · simp [top_pow]
    · have := pow_ne_zero (n + 1) ha
      rw [← coe_pow, ← coe_inv (hr := this.isUnit), ← coe_inv (hr := ha.isUnit), ← coe_pow,
        inv_pow₀]

protected theorem mul_inv_cancel (h0 : a ≠ 0) (ht : a ≠ ∞) : a * a⁻¹ = 1 := by
  lift a to ℝ≥0 using ht
  norm_cast at h0
  rw [← coe_inv (hr := Ne.isUnit h0), ← coe_mul, mul_inv_cancel₀, coe_one]

protected theorem inv_mul_cancel (h0 : a ≠ 0) (ht : a ≠ ∞) : a⁻¹ * a = 1 :=
  mul_comm a a⁻¹ ▸ ENNReal.mul_inv_cancel h0 ht

/-- See `ENNReal.inv_mul_cancel_left` for a simpler version assuming `a ≠ 0`, `a ≠ ∞`. -/
protected lemma inv_mul_cancel_left' (ha₀ : a = 0 → b = 0) (ha : a = ∞ → b = 0) :
    a⁻¹ * (a * b) = b := by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp_all
  obtain rfl | ha := eq_or_ne a ⊤
  · simp_all
  · simp [← mul_assoc, ENNReal.inv_mul_cancel, *]

/-- See `ENNReal.inv_mul_cancel_left'` for a stronger version. -/
protected lemma inv_mul_cancel_left (ha₀ : a ≠ 0) (ha : a ≠ ∞) : a⁻¹ * (a * b) = b :=
  ENNReal.inv_mul_cancel_left' (by simp [ha₀]) (by simp [ha])

/-- See `ENNReal.mul_inv_cancel_left` for a simpler version assuming `a ≠ 0`, `a ≠ ∞`. -/
protected lemma mul_inv_cancel_left' (ha₀ : a = 0 → b = 0) (ha : a = ∞ → b = 0) :
    a * (a⁻¹ * b) = b := by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp_all
  obtain rfl | ha := eq_or_ne a ⊤
  · simp_all
  · simp [← mul_assoc, ENNReal.mul_inv_cancel, *]

/-- See `ENNReal.mul_inv_cancel_left'` for a stronger version. -/
protected lemma mul_inv_cancel_left (ha₀ : a ≠ 0) (ha : a ≠ ∞) : a * (a⁻¹ * b) = b :=
  ENNReal.mul_inv_cancel_left' (by simp [ha₀]) (by simp [ha])

/-- See `ENNReal.mul_inv_cancel_right` for a simpler version assuming `b ≠ 0`, `b ≠ ∞`. -/
protected lemma mul_inv_cancel_right' (hb₀ : b = 0 → a = 0) (hb : b = ∞ → a = 0) :
    a * b * b⁻¹ = a := by
  obtain rfl | hb₀ := eq_or_ne b 0
  · simp_all
  obtain rfl | hb := eq_or_ne b ⊤
  · simp_all
  · simp [mul_assoc, ENNReal.mul_inv_cancel, *]

/-- See `ENNReal.mul_inv_cancel_right'` for a stronger version. -/
protected lemma mul_inv_cancel_right (hb₀ : b ≠ 0) (hb : b ≠ ∞) : a * b * b⁻¹ = a :=
  ENNReal.mul_inv_cancel_right' (by simp [hb₀]) (by simp [hb])

/-- See `ENNReal.inv_mul_cancel_right` for a simpler version assuming `b ≠ 0`, `b ≠ ∞`. -/
protected lemma inv_mul_cancel_right' (hb₀ : b = 0 → a = 0) (hb : b = ∞ → a = 0) :
    a * b⁻¹ * b = a := by
  obtain rfl | hb₀ := eq_or_ne b 0
  · simp_all
  obtain rfl | hb := eq_or_ne b ⊤
  · simp_all
  · simp [mul_assoc, ENNReal.inv_mul_cancel, *]

/-- See `ENNReal.inv_mul_cancel_right'` for a stronger version. -/
protected lemma inv_mul_cancel_right (hb₀ : b ≠ 0) (hb : b ≠ ∞) : a * b⁻¹ * b = a :=
  ENNReal.inv_mul_cancel_right' (by simp [hb₀]) (by simp [hb])

protected lemma mul_div_cancel_right (hb₀ : b ≠ 0) (hb : b ≠ ∞) :
    div (a * b) b ⟨hb₀, Or.inr hb⟩ = a :=
  ENNReal.mul_inv_cancel_right hb₀ hb

protected lemma div_mul_cancel (ha₀ : a ≠ 0) (ha : a ≠ ∞) :
    div b a ⟨ha₀, Or.inr ha⟩ * a = b :=
  ENNReal.inv_mul_cancel_right ha₀ ha

protected lemma mul_div_cancel (ha₀ : a ≠ 0) (ha : a ≠ ∞) :
    a * div b a ⟨ha₀, Or.inr ha⟩ = b := by
  rw [mul_comm, ENNReal.div_mul_cancel ha₀ ha]

protected theorem mul_comm_div (h₁ h₂) : div a b h₁ * c = a * div c b h₂ := by
  simp only [ENNReal.div_eq_mul_inv, mul_assoc, mul_comm b⁻¹]

protected theorem mul_div_right_comm (h₁ h₂) : div (a * b) c h₁ = div a c h₂ * b :=
  mul_right_comm _ _ _

protected theorem mul_div_assoc (a b c : ℝ≥0∞) (h₁ h₂) :
    div (a * b) c h₁ = a * div b c h₂ :=
  mul_assoc a b c⁻¹

protected lemma div_mul_div_cancel (hb₀ : b ≠ 0) (hb : b ≠ ∞) (h₁ h₂) :
    div a b ⟨hb₀, Or.inr hb⟩ * div b c h₁ = div a c h₂ := by
  simp only [ENNReal.div_eq_mul_inv, ← mul_assoc, ENNReal.inv_mul_cancel_right hb₀ hb]

instance : InvolutiveInv ℝ≥0∞ where
  inv_inv a := by
    cases a with
    | top => simp
    | coe r =>
      rcases eq_or_ne r 0 with rfl | hr
      · simp
      · rw [← coe_inv (hr := hr.isUnit), ← coe_inv (hr := hr.isUnit.inv₀), inv_inv₀]

@[simp] protected lemma inv_eq_one : a⁻¹ = 1 ↔ a = 1 := by rw [← inv_inj, inv_inv, ENNReal.inv_one]

@[simp] theorem inv_eq_top : a⁻¹ = ∞ ↔ a = 0 := inv_zero ▸ inv_inj

theorem inv_ne_top : a⁻¹ ≠ ∞ ↔ a ≠ 0 := by simp

@[aesop (rule_sets := [finiteness]) safe apply]
protected alias ⟨_, Finiteness.inv_ne_top⟩ := ENNReal.inv_ne_top

@[simp]
theorem inv_lt_top {x : ℝ≥0∞} : x⁻¹ < ∞ ↔ 0 < x := by
  simp only [lt_top_iff_ne_top, inv_ne_top, pos_iff_ne_zero]

theorem div_lt_top {x y : ℝ≥0∞} (h1 : x ≠ ∞) (h2 : y ≠ 0) : div x y ⟨h2, Or.inl h1⟩ < ∞ :=
  mul_lt_top h1.lt_top (inv_ne_top.mpr h2).lt_top

@[aesop (rule_sets := [finiteness]) safe apply]
theorem div_ne_top {x y : ℝ≥0∞} (h1 : x ≠ ∞) (h2 : y ≠ 0) : div x y ⟨h2, Or.inl h1⟩ ≠ ∞ :=
  (div_lt_top h1 h2).ne

@[simp]
protected theorem inv_eq_zero : a⁻¹ = 0 ↔ a = ∞ :=
  inv_top ▸ inv_inj

protected theorem inv_ne_zero : a⁻¹ ≠ 0 ↔ a ≠ ∞ := by simp

protected theorem div_pos (ha : a ≠ 0) (hb₀ : b ≠ 0) (hb : b ≠ ∞) :
    0 < div a b ⟨hb₀, Or.inr hb⟩ :=
  ENNReal.mul_pos ha <| ENNReal.inv_ne_zero.2 hb

protected theorem inv_mul_le_iff {x y z : ℝ≥0∞} (h1 : x ≠ 0) (h2 : x ≠ ∞) :
    x⁻¹ * y ≤ z ↔ y ≤ x * z := by
  rw [← ENNReal.mul_le_mul_iff_right h1 h2, ← mul_assoc, ENNReal.mul_inv_cancel h1 h2, one_mul]

protected theorem mul_inv_le_iff {x y z : ℝ≥0∞} (h1 : y ≠ 0) (h2 : y ≠ ∞) :
    x * y⁻¹ ≤ z ↔ x ≤ z * y := by
  rw [mul_comm, ENNReal.inv_mul_le_iff h1 h2, mul_comm]

protected theorem div_le_iff {x y z : ℝ≥0∞} (h₀ : y ≠ 0) (ht : y ≠ ∞) :
    div x y ⟨h₀, Or.inr ht⟩ ≤ z ↔ x ≤ z * y :=
  ENNReal.mul_inv_le_iff h₀ ht

protected theorem div_le_iff' {x y z : ℝ≥0∞} (h₀ : y ≠ 0) (ht : y ≠ ∞) :
    div x y ⟨h₀, Or.inr ht⟩ ≤ z ↔ x ≤ y * z := by
  rw [mul_comm, ENNReal.div_le_iff h₀ ht]

/-- The infimum quotient measures the multipliers sufficient in the order comparison.
An empty set gives `∞`, and with an infinite denominator arbitrarily small positive
multipliers suffice. -/
theorem divInf_eq_sInf (a b : ℝ≥0∞) : divInf a b = sInf {q : ℝ≥0∞ | a ≤ b * q} := by
  obtain rfl | h₀ := eq_or_ne b 0
  · obtain rfl | ha := eq_or_ne a 0
    · simp [divInf]
    · rw [show divInf a 0 = ∞ by simp [divInf, ha]]
      refine le_antisymm (le_sInf fun q hq => ?_) le_top
      exact (ha (by simpa using hq)).elim
  obtain rfl | ht := eq_or_ne b ∞
  · rw [divInf, inv_top, mul_zero]
    refine le_antisymm bot_le (le_of_forall_gt_imp_ge_of_dense fun q hq => sInf_le ?_)
    exact mem_ofPred.2 (by rw [top_mul hq.ne']; exact le_top)
  have H (q : ℝ≥0∞) : divInf a b ≤ q ↔ a ≤ b * q := by
    simpa only [divInf, mul_comm b q] using
      (ENNReal.mul_inv_le_iff (x := a) (z := q) h₀ ht)
  exact le_antisymm (le_sInf fun q hq => (H q).2 hq) (sInf_le ((H _).1 le_rfl))

protected theorem mul_inv {a b : ℝ≥0∞} (ha : a ≠ 0 ∨ b ≠ ∞) (hb : a ≠ ∞ ∨ b ≠ 0) :
    (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  cases b
  case top =>
    simp_all only [Ne, not_true_eq_false, or_false, top_ne_zero, not_false_eq_true, or_true,
      mul_top, inv_top, mul_zero]
  cases a
  case top =>
    simp_all only [Ne, top_ne_zero, not_false_eq_true, coe_ne_top, or_self, not_true_eq_false,
      coe_eq_zero, false_or, top_mul, inv_top, zero_mul]
  rename_i b a
  rcases eq_or_ne a 0 with rfl | ha'
  · rcases eq_or_ne b 0 with rfl | hb'
    · simp
    · rw [coe_zero, zero_mul, inv_zero, ← coe_inv (hr := hb'.isUnit),
        top_mul (coe_ne_zero.2 (inv_ne_zero (ha := hb'.isUnit)))]
  rcases eq_or_ne b 0 with rfl | hb'
  · rw [coe_zero, mul_zero, inv_zero, ← coe_inv (hr := ha'.isUnit),
      mul_top (coe_ne_zero.2 (inv_ne_zero (ha := ha'.isUnit)))]
  rw [← coe_mul, ← coe_inv (hr := ha'.isUnit), ← coe_inv (hr := hb'.isUnit),
    ← coe_inv (hr := (mul_ne_zero ha' hb').isUnit), ← coe_mul, mul_inv₀]

protected theorem inv_extendedDiv
    (h : (a ≠ 0 ∨ b ≠ 0) ∧ (a ≠ ∞ ∨ b ≠ ∞)) :
    (extendedDiv a b h)⁻¹ = extendedDiv b a ⟨h.1.symm, h.2.symm⟩ := by
  simp only [extendedDiv_eq_mul_inv,
    ENNReal.mul_inv (a := a) (b := b⁻¹) (by simpa using h.1) (by simpa using h.2),
    inv_inv, mul_comm]

protected theorem inv_div (ha : a ≠ 0) (hb : b ≠ 0) (h : a ≠ ∞ ∨ b ≠ ∞) :
    (div a b ⟨hb, h⟩)⁻¹ = div b a ⟨ha, h.symm⟩ :=
  ENNReal.inv_extendedDiv ⟨Or.inr hb, h⟩

protected theorem mul_div_mul_left (a b : ℝ≥0∞) (hc : c ≠ 0) (hct : c ≠ ∞) (h₁ h₂) :
    div (c * a) (c * b) h₁ = div a b h₂ := by
  simp only [ENNReal.div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inl hc) (Or.inl hct), mul_mul_mul_comm,
    ENNReal.mul_inv_cancel hc hct, one_mul]

protected theorem mul_div_mul_right (a b : ℝ≥0∞) (hc : c ≠ 0) (hct : c ≠ ∞) (h₁ h₂) :
    div (a * c) (b * c) h₁ = div a b h₂ := by
  simp only [ENNReal.div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inr hct) (Or.inr hc), mul_mul_mul_comm,
    ENNReal.mul_inv_cancel hc hct, mul_one]

protected theorem monus_div (h : 0 < b → b < a → c ≠ 0) (h₁ h₂ h₃) :
    div (monus a b) c h₁ = monus (div a c h₂) (div b c h₃) := by
  simp only [ENNReal.div_eq_mul_inv]
  exact ENNReal.monus_mul (by simpa using h)

@[simp]
protected theorem inv_pos : 0 < a⁻¹ ↔ a ≠ ∞ :=
  pos_iff_ne_zero.trans ENNReal.inv_ne_zero

theorem inv_strictAnti : StrictAnti (Inv.inv : ℝ≥0∞ → ℝ≥0∞) := by
  intro a b h
  lift a to ℝ≥0 using h.ne_top
  cases b; · simp
  rw [coe_lt_coe] at h
  rcases eq_or_ne a 0 with (rfl | ha); · simp [h]
  rw [← coe_inv (hr := h.ne_bot.isUnit), ← coe_inv (hr := ha.isUnit), coe_lt_coe]
  exact NNReal.inv_lt_inv h

@[simp]
protected theorem inv_lt_inv : a⁻¹ < b⁻¹ ↔ b < a :=
  inv_strictAnti.lt_iff_gt

theorem inv_lt_iff_inv_lt : a⁻¹ < b ↔ b⁻¹ < a := by
  simpa only [inv_inv] using @ENNReal.inv_lt_inv a b⁻¹

theorem lt_inv_iff_lt_inv : a < b⁻¹ ↔ b < a⁻¹ := by
  simpa only [inv_inv] using @ENNReal.inv_lt_inv a⁻¹ b

@[simp]
protected theorem inv_le_inv : a⁻¹ ≤ b⁻¹ ↔ b ≤ a :=
  inv_strictAnti.le_iff_ge

theorem inv_le_iff_inv_le : a⁻¹ ≤ b ↔ b⁻¹ ≤ a := by
  simpa only [inv_inv] using @ENNReal.inv_le_inv a b⁻¹

theorem le_inv_iff_le_inv : a ≤ b⁻¹ ↔ b ≤ a⁻¹ := by
  simpa only [inv_inv] using @ENNReal.inv_le_inv a⁻¹ b

@[gcongr] protected theorem inv_le_inv' (h : a ≤ b) : b⁻¹ ≤ a⁻¹ :=
  ENNReal.inv_strictAnti.antitone h

@[gcongr] protected theorem inv_lt_inv' (h : a < b) : b⁻¹ < a⁻¹ := ENNReal.inv_strictAnti h

@[simp]
protected theorem inv_le_one : a⁻¹ ≤ 1 ↔ 1 ≤ a := by rw [inv_le_iff_inv_le, ENNReal.inv_one]

protected theorem one_le_inv : 1 ≤ a⁻¹ ↔ a ≤ 1 := by rw [le_inv_iff_le_inv, ENNReal.inv_one]

@[simp]
protected theorem inv_lt_one : a⁻¹ < 1 ↔ 1 < a := by rw [inv_lt_iff_inv_lt, ENNReal.inv_one]

@[simp]
protected theorem one_lt_inv : 1 < a⁻¹ ↔ a < 1 := by rw [lt_inv_iff_lt_inv, ENNReal.inv_one]

/-- The inverse map `fun x ↦ x⁻¹` is an order isomorphism between `ℝ≥0∞` and its `OrderDual` -/
@[simps! apply]
def _root_.OrderIso.invENNReal : ℝ≥0∞ ≃o ℝ≥0∞ᵒᵈ where
  map_rel_iff' := ENNReal.inv_le_inv
  toEquiv := (Equiv.inv ℝ≥0∞).trans OrderDual.toDual

@[simp]
theorem _root_.OrderIso.invENNReal_symm_apply (a : ℝ≥0∞ᵒᵈ) :
    OrderIso.invENNReal.symm a = (OrderDual.ofDual a)⁻¹ :=
  rfl

@[simp] theorem div_top (ha : a ≠ ∞) :
    div a ∞ ⟨top_ne_zero, Or.inl ha⟩ = 0 := extendedDiv_top ha

@[simp] theorem top_div (h : a ≠ 0 ∧ (∞ ≠ ∞ ∨ a ≠ ∞)) :
    div ∞ a h = ∞ := by
  rw [ENNReal.div_eq_mul_inv,
    top_mul (ENNReal.inv_ne_zero.2 (h.2.resolve_left (not_not_intro rfl)))]

theorem top_div_of_ne_top (ht : a ≠ ∞) (h₀ : a ≠ 0) :
    div ∞ a ⟨h₀, Or.inr ht⟩ = ∞ := top_div ⟨h₀, Or.inr ht⟩

theorem top_div_coe (hp : p ≠ 0) :
    div ∞ p ⟨coe_ne_zero.2 hp, Or.inr coe_ne_top⟩ = ∞ :=
  top_div_of_ne_top coe_ne_top (coe_ne_zero.2 hp)

theorem top_div_of_lt_top (ht : a < ∞) (h₀ : a ≠ 0) :
    div ∞ a ⟨h₀, Or.inr ht.ne⟩ = ∞ := top_div_of_ne_top ht.ne h₀

@[simp] protected theorem zero_div (hb : b ≠ 0) :
    div 0 b ⟨hb, Or.inl zero_ne_top⟩ = 0 := zero_mul _

theorem divInf_eq_top : divInf a b = ∞ ↔ a ≠ 0 ∧ b = 0 ∨ a = ∞ ∧ b ≠ ∞ := by
  simp [divInf, ENNReal.mul_eq_top]

theorem div_eq_top (h) : div a b h = ∞ ↔ a = ∞ := by
  change divInf a b = ∞ ↔ a = ∞
  simp only [divInf_eq_top, h.1, and_false, false_or, and_iff_left_iff_imp]
  exact fun ha => h.2.resolve_left (not_not_intro ha)

theorem le_extendedDiv_iff_mul_le
    (h : (c ≠ 0 ∨ b ≠ 0) ∧ (c ≠ ∞ ∨ b ≠ ∞)) :
    a ≤ extendedDiv c b h ↔ a * b ≤ c := by
  change a ≤ c * b⁻¹ ↔ a * b ≤ c
  obtain rfl | hb₀ := eq_or_ne b 0
  · have hc := h.1.resolve_right (not_not_intro rfl)
    simp [hc]
  obtain rfl | hbt := eq_or_ne b ∞
  · have hc := h.2.resolve_right (not_not_intro rfl)
    obtain rfl | ha := eq_or_ne a 0
    · simp
    · simp [ha, hc, mul_top, top_le_iff]
  rw [← ENNReal.mul_le_mul_iff_left hb₀ hbt,
    ENNReal.inv_mul_cancel_right hb₀ hbt]

protected theorem le_div_iff_mul_le (h) :
    a ≤ div c b h ↔ a * b ≤ c :=
  le_extendedDiv_iff_mul_le ⟨Or.inr h.1, h.2⟩

protected theorem extendedDiv_lt_iff (h) : extendedDiv c b h < a ↔ c < a * b :=
  lt_iff_lt_of_le_iff_le (le_extendedDiv_iff_mul_le h)

protected theorem mul_inv_le_iff_le_mul (hb₀ : b ≠ 0 ∨ c ≠ ∞) (hbt : b ≠ ∞ ∨ c ≠ 0) :
    a * b⁻¹ ≤ c ↔ a ≤ c * b := by
  simpa only [extendedDiv_eq_mul_inv, inv_inv] using
    (le_extendedDiv_iff_mul_le (a := a) (b := b⁻¹) (c := c)
      ⟨by simpa [or_comm] using hbt, by simpa [or_comm] using hb₀⟩).symm

protected theorem div_le_iff_le_mul (h) (hb₀ : b ≠ 0 ∨ c ≠ ∞) (hbt : b ≠ ∞ ∨ c ≠ 0) :
    div a b h ≤ c ↔ a ≤ c * b :=
  ENNReal.mul_inv_le_iff_le_mul hb₀ hbt

protected theorem lt_div_iff_mul_lt (h) (hb₀ : b ≠ 0 ∨ c ≠ ∞) (hbt : b ≠ ∞ ∨ c ≠ 0) :
    c < div a b h ↔ c * b < a :=
  lt_iff_lt_of_le_iff_le (ENNReal.div_le_iff_le_mul h hb₀ hbt)

theorem mul_inv_le_of_le_mul (h : a ≤ b * c) : a * c⁻¹ ≤ b := by
  by_cases h₀ : c = 0
  · have : a = 0 := by simpa [h₀] using h
    simp [*]
  by_cases ht : c = ∞
  · simp [ht]
  exact (ENNReal.mul_inv_le_iff h₀ ht).2 h

theorem div_le_of_le_mul (h₀) (h : a ≤ b * c) : div a c h₀ ≤ b :=
  mul_inv_le_of_le_mul h

theorem div_le_of_le_mul' (h₀) (h : a ≤ b * c) : div a b h₀ ≤ c :=
  div_le_of_le_mul h₀ <| mul_comm b c ▸ h

@[simp] protected lemma mul_inv_le_one (a : ℝ≥0∞) : a * a⁻¹ ≤ 1 :=
  mul_inv_le_of_le_mul (by rw [one_mul])

@[simp] protected lemma inv_mul_le_one (a : ℝ≥0∞) : a⁻¹ * a ≤ 1 := by simp [mul_comm]

@[aesop (rule_sets := [finiteness]) safe apply, simp]
lemma mul_inv_ne_top (a : ℝ≥0∞) : a * a⁻¹ ≠ ⊤ :=
  ne_top_of_le_ne_top one_ne_top a.mul_inv_le_one

@[aesop (rule_sets := [finiteness]) safe apply, simp]
lemma inv_mul_ne_top (a : ℝ≥0∞) : a⁻¹ * a ≠ ⊤ := by simp [mul_comm]

theorem mul_le_of_le_mul_inv (h : a ≤ b * c⁻¹) : a * c ≤ b := by
  rw [← inv_inv c]
  exact mul_inv_le_of_le_mul h

theorem mul_le_of_le_div (h₀) (h : a ≤ div b c h₀) : a * c ≤ b :=
  mul_le_of_le_mul_inv h

theorem mul_le_of_le_div' (h₀) (h : a ≤ div b c h₀) : c * a ≤ b :=
  mul_comm a c ▸ mul_le_of_le_div h₀ h

protected theorem div_lt_iff (h) : div c b h < a ↔ c < a * b :=
  lt_iff_lt_of_le_iff_le <| ENNReal.le_div_iff_mul_le h

theorem mul_lt_of_lt_mul_inv (h : a < b * c⁻¹) : a * c < b := by
  contrapose! h
  exact mul_inv_le_of_le_mul h

theorem mul_lt_of_lt_div (h₀) (h : a < div b c h₀) : a * c < b :=
  mul_lt_of_lt_mul_inv h

theorem mul_lt_of_lt_div' (h₀) (h : a < div b c h₀) : c * a < b :=
  mul_comm a c ▸ mul_lt_of_lt_div h₀ h

theorem mul_inv_lt_of_lt_mul (h : a < b * c) : a * c⁻¹ < b :=
  mul_lt_of_lt_mul_inv <| by rwa [inv_inv]

theorem div_lt_of_lt_mul (h₀) (h : a < b * c) : div a c h₀ < b :=
  mul_inv_lt_of_lt_mul h

theorem div_lt_of_lt_mul' (h₀) (h : a < b * c) : div a b h₀ < c :=
  div_lt_of_lt_mul h₀ <| by rwa [mul_comm]

protected lemma div_lt_div_iff_left (hc₀ : c ≠ 0) (hc : c ≠ ∞) :
    div a c ⟨hc₀, Or.inr hc⟩ < div b c ⟨hc₀, Or.inr hc⟩ ↔ a < b :=
  ENNReal.mul_lt_mul_iff_left (by simpa) (by simpa)

protected lemma div_lt_div_iff_right (ha₀ : a ≠ 0) (ha : a ≠ ∞) (h₁ h₂) :
    div a b h₁ < div a c h₂ ↔ c < b :=
  (ENNReal.mul_lt_mul_iff_right ha₀ ha).trans ENNReal.inv_lt_inv

@[gcongr]
protected lemma div_lt_div_right (hc₀ : c ≠ 0) (hc : c ≠ ∞) (hab : a < b) :
    div a c ⟨hc₀, Or.inr hc⟩ < div b c ⟨hc₀, Or.inr hc⟩ :=
  (ENNReal.div_lt_div_iff_left hc₀ hc).2 hab

@[gcongr]
protected lemma div_lt_div_left (ha₀ : a ≠ 0) (ha : a ≠ ∞) (hcb : c < b) (h₁ h₂) :
    div a b h₁ < div a c h₂ :=
  (ENNReal.div_lt_div_iff_right ha₀ ha h₁ h₂).2 hcb

protected lemma exists_pos_mul_lt (ha : a ≠ ∞) (hb₀ : b ≠ 0) : ∃ c, 0 < c ∧ c * a < b := by
  obtain rfl | hb := eq_or_ne b ∞
  · exact ⟨1, by simpa [lt_top_iff_ne_top]⟩
  refine ⟨b * (a + 1)⁻¹, ENNReal.mul_pos hb₀ (ENNReal.inv_ne_zero.2 (by finiteness)),
    mul_lt_of_lt_mul_inv ?_⟩
  gcongr
  exact ENNReal.lt_add_right ha one_ne_zero

theorem inv_le_iff_le_mul (h₁ : b = ∞ → a ≠ 0) (h₂ : a = ∞ → b ≠ 0) : a⁻¹ ≤ b ↔ 1 ≤ a * b := by
  rw [← one_mul a⁻¹, ENNReal.mul_inv_le_iff_le_mul, mul_comm]
  exacts [or_not_of_imp h₁, not_or_of_imp h₂]

@[simp 900]
theorem le_inv_iff_mul_le : a ≤ b⁻¹ ↔ a * b ≤ 1 := by
  simpa only [extendedDiv_eq_mul_inv, one_mul] using
    (le_extendedDiv_iff_mul_le (a := a) (b := b) (c := 1)
      ⟨Or.inl one_ne_zero, Or.inl one_ne_top⟩)

@[gcongr] protected theorem div_le_div (hab : a ≤ b) (hdc : d ≤ c) (h₁ h₂) :
    div a c h₁ ≤ div b d h₂ :=
  mul_le_mul' hab (ENNReal.inv_le_inv.mpr hdc)

protected theorem div_le_div_left (h : a ≤ b) (c : ℝ≥0∞) (h₁ h₂) :
    div c b h₁ ≤ div c a h₂ :=
  ENNReal.div_le_div le_rfl h h₁ h₂

protected theorem div_le_div_right (h : a ≤ b) (c : ℝ≥0∞) (h₁ h₂) :
    div a c h₁ ≤ div b c h₂ :=
  ENNReal.div_le_div h le_rfl h₁ h₂

protected theorem eq_inv_of_mul_eq_one_left (h : a * b = 1) : a = b⁻¹ := by
  rw [← mul_one a, ← ENNReal.mul_inv_cancel (right_ne_zero_of_mul_eq_one h), ← mul_assoc, h,
    one_mul]
  rintro rfl
  simp [left_ne_zero_of_mul_eq_one h] at h

theorem mul_le_iff_le_inv {a b r : ℝ≥0∞} (hr₀ : r ≠ 0) (hr₁ : r ≠ ∞) : r * a ≤ b ↔ a ≤ r⁻¹ * b := by
  rw [← @ENNReal.mul_le_mul_iff_right _ a _ hr₀ hr₁, ← mul_assoc, ENNReal.mul_inv_cancel hr₀ hr₁,
    one_mul]

theorem le_of_forall_nnreal_lt {x y : ℝ≥0∞} (h : ∀ r : ℝ≥0, ↑r < x → ↑r ≤ y) : x ≤ y := by
  refine le_of_forall_lt_imp_le_of_dense fun r hr => ?_
  lift r to ℝ≥0 using ne_top_of_lt hr
  exact h r hr

lemma eq_of_forall_nnreal_le_iff {x y : ℝ≥0∞} : (∀ r : ℝ≥0, ↑r ≤ x ↔ ↑r ≤ y) → x = y :=
  WithTop.eq_of_forall_coe_le_iff

lemma eq_of_forall_le_nnreal_iff {x y : ℝ≥0∞} : (∀ r : ℝ≥0, x ≤ r ↔ y ≤ r) → x = y :=
  WithTop.eq_of_forall_le_coe_iff

theorem le_of_forall_pos_nnreal_lt {x y : ℝ≥0∞} (h : ∀ r : ℝ≥0, 0 < r → ↑r < x → ↑r ≤ y) : x ≤ y :=
  le_of_forall_nnreal_lt fun r hr =>
    (eq_zero_or_pos r).elim (fun h => h ▸ zero_le) fun h0 => h r h0 hr

theorem eq_top_of_forall_nnreal_le {x : ℝ≥0∞} (h : ∀ r : ℝ≥0, ↑r ≤ x) : x = ∞ :=
  top_unique <| le_of_forall_nnreal_lt fun r _ => h r

protected theorem add_div (h₁ h₂ h₃) :
    div (a + b) c h₁ = div a c h₂ + div b c h₃ :=
  right_distrib a b c⁻¹

protected theorem div_add_div_same (h₁ h₂ h₃) :
    div a c h₁ + div b c h₂ = div (a + b) c h₃ :=
  (ENNReal.add_div h₃ h₁ h₂).symm

protected theorem div_self (h₀ : a ≠ 0) (ht : a ≠ ∞) :
    div a a ⟨h₀, Or.inr ht⟩ = 1 :=
  ENNReal.mul_inv_cancel h₀ ht

theorem mul_mul_inv_le : a * (b * a⁻¹) ≤ b :=
  mul_comm a (b * a⁻¹) ▸ mul_le_of_le_mul_inv le_rfl

theorem mul_div_le (h) : a * div b a h ≤ b := mul_mul_inv_le

theorem eq_div_iff (ha : a ≠ 0) (hat : a ≠ ∞) :
    b = div c a ⟨ha, Or.inr hat⟩ ↔ a * b = c := by
  refine ⟨fun h => h ▸ ENNReal.mul_div_cancel ha hat, fun h => ?_⟩
  rw [← h, ENNReal.div_eq_mul_inv, mul_comm a b, ENNReal.mul_inv_cancel_right ha hat]

protected theorem div_eq_div_iff (ha : a ≠ 0) (ha' : a ≠ ∞) (hb : b ≠ 0) (hb' : b ≠ ∞) :
    div c b ⟨hb, Or.inr hb'⟩ = div d a ⟨ha, Or.inr ha'⟩ ↔ a * c = b * d := by
  rw [eq_div_iff ha ha']
  conv_rhs => rw [eq_comm]
  rw [← eq_div_iff hb hb', ENNReal.mul_div_assoc, eq_comm]

theorem div_eq_one_iff {a b : ℝ≥0∞} (hb₀ : b ≠ 0) (hb₁ : b ≠ ∞) :
    div a b ⟨hb₀, Or.inr hb₁⟩ = 1 ↔ a = b :=
  ⟨fun h => by rw [← (eq_div_iff hb₀ hb₁).mp h.symm, mul_one], fun h =>
    h.symm ▸ ENNReal.div_self hb₀ hb₁⟩

theorem inv_two_add_inv_two : (2 : ℝ≥0∞)⁻¹ + 2⁻¹ = 1 := by
  rw [← two_mul]
  exact ENNReal.mul_inv_cancel two_ne_zero ofNat_ne_top

theorem inv_three_add_inv_three : (3 : ℝ≥0∞)⁻¹ + 3⁻¹ + 3⁻¹ = 1 := by
  rw [← ENNReal.mul_inv_cancel three_ne_zero ofNat_ne_top]
  ring

@[simp]
protected theorem add_halves (a : ℝ≥0∞) :
    div a 2 ⟨two_ne_zero, Or.inr ofNat_ne_top⟩ + div a 2 ⟨two_ne_zero, Or.inr ofNat_ne_top⟩ =
      a := by
  simp only [ENNReal.div_eq_mul_inv, ← mul_add, inv_two_add_inv_two, mul_one]

@[simp]
theorem add_thirds (a : ℝ≥0∞) :
    div a 3 ⟨three_ne_zero, Or.inr ofNat_ne_top⟩ + div a 3 ⟨three_ne_zero, Or.inr ofNat_ne_top⟩ +
      div a 3 ⟨three_ne_zero, Or.inr ofNat_ne_top⟩ = a := by
  simp only [ENNReal.div_eq_mul_inv, ← mul_add, inv_three_add_inv_three, mul_one]

@[simp] theorem div_eq_zero_iff (h) : div a b h = 0 ↔ a = 0 ∨ b = ∞ := by
  simp [ENNReal.div_eq_mul_inv]

@[simp] theorem div_pos_iff (h) : 0 < div a b h ↔ a ≠ 0 ∧ b ≠ ∞ := by
  simp [pos_iff_ne_zero, not_or]

protected lemma div_ne_zero (h) : div a b h ≠ 0 ↔ a ≠ 0 ∧ b ≠ ∞ := by
  rw [← pos_iff_ne_zero, div_pos_iff]

protected lemma div_mul (a : ℝ≥0∞) (h₁ h₂ h₃) :
    div a b h₁ * c = div a (div b c h₂) h₃ := by
  simp only [ENNReal.div_eq_mul_inv]
  rw [ENNReal.mul_inv, inv_inv]
  · ring
  · simp [h₂.1]
  · simpa using h₂.2

protected lemma mul_div_mul_comm (hc : c ≠ 0 ∨ d ≠ ∞) (hd : c ≠ ∞ ∨ d ≠ 0) (h₁ h₂ h₃) :
    div (a * b) (c * d) h₁ = div a c h₂ * div b d h₃ := by
  simp only [ENNReal.div_eq_mul_inv, ENNReal.mul_inv hc hd]
  ring

protected theorem half_pos (h : a ≠ 0) : 0 < div a 2 ⟨two_ne_zero, Or.inr ofNat_ne_top⟩ :=
  ENNReal.div_pos h two_ne_zero ofNat_ne_top

protected theorem one_half_lt_one : (2⁻¹ : ℝ≥0∞) < 1 :=
  ENNReal.inv_lt_one.2 <| one_lt_two

protected theorem half_lt_self (hz : a ≠ 0) (ht : a ≠ ∞) :
    div a 2 ⟨two_ne_zero, Or.inr ofNat_ne_top⟩ < a := by
  lift a to ℝ≥0 using ht
  rw [coe_ne_zero] at hz
  simpa only [coe_div (hr := (two_ne_zero' ℝ≥0).isUnit), coe_two] using
    coe_lt_coe.2 (NNReal.half_lt_self hz)

protected theorem half_le_self : div a 2 ⟨two_ne_zero, Or.inr ofNat_ne_top⟩ ≤ a :=
  le_add_self.trans_eq <| ENNReal.add_halves _

theorem monus_half (h : a ≠ ∞) :
    monus a (div a 2 ⟨two_ne_zero, Or.inr ofNat_ne_top⟩) =
      div a 2 ⟨two_ne_zero, Or.inr ofNat_ne_top⟩ :=
  ENNReal.monus_eq_of_eq_add' h a.add_halves.symm

@[simp]
theorem one_monus_inv_two : monus 1 2⁻¹ = 2⁻¹ := by
  rw [← one_div 2 two_ne_zero, monus_half one_ne_top]

private lemma exists_lt_mul_left {a b c : ℝ≥0∞} (hc : c < a * b) : ∃ a' < a, c < a' * b := by
  have hd : (c ≠ 0 ∨ b ≠ 0) ∧ (c ≠ ∞ ∨ b ≠ ∞) :=
    ⟨Or.inr (by rintro rfl; simp at hc), Or.inl hc.ne_top⟩
  obtain ⟨a', hc, ha'⟩ := exists_between ((ENNReal.extendedDiv_lt_iff hd).2 hc)
  exact ⟨_, ha', (ENNReal.extendedDiv_lt_iff hd).1 hc⟩

private lemma exists_lt_mul_right {a b c : ℝ≥0∞} (hc : c < a * b) : ∃ b' < b, c < a * b' := by
  simp_rw [mul_comm a] at hc ⊢; exact exists_lt_mul_left hc

lemma mul_le_of_forall_lt {a b c : ℝ≥0∞} (h : ∀ a' < a, ∀ b' < b, a' * b' ≤ c) : a * b ≤ c := by
  refine le_of_forall_lt_imp_le_of_dense fun d hd ↦ ?_
  obtain ⟨a', ha', hd⟩ := exists_lt_mul_left hd
  obtain ⟨b', hb', hd⟩ := exists_lt_mul_right hd
  exact le_trans hd.le <| h _ ha' _ hb'

lemma le_mul_of_forall_lt {a b c : ℝ≥0∞} (h₁ : a ≠ 0 ∨ b ≠ ∞) (h₂ : a ≠ ∞ ∨ b ≠ 0)
    (h : ∀ a' > a, ∀ b' > b, c ≤ a' * b') : c ≤ a * b := by
  rw [← ENNReal.inv_le_inv, ENNReal.mul_inv h₁ h₂]
  exact mul_le_of_forall_lt fun a' ha' b' hb' ↦ ENNReal.le_inv_iff_le_inv.1 <|
    (h _ (ENNReal.lt_inv_iff_lt_inv.1 ha') _ (ENNReal.lt_inv_iff_lt_inv.1 hb')).trans_eq
    (ENNReal.mul_inv (Or.inr hb'.ne_top) (Or.inl ha'.ne_top)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The birational order isomorphism between `ℝ≥0∞` and the unit interval `Set.Iic (1 : ℝ≥0∞)`. -/
@[simps! apply_coe]
def orderIsoIicOneBirational : ℝ≥0∞ ≃o Iic (1 : ℝ≥0∞) := by
  refine StrictMono.orderIsoOfRightInverse
    (fun x => ⟨(x⁻¹ + 1)⁻¹, ENNReal.inv_le_one.2 <| le_add_self⟩)
    (fun x y hxy => ?_) (fun x => (monus x.1⁻¹ 1)⁻¹) fun x => Subtype.ext ?_
  · simpa only [Subtype.mk_lt_mk, ENNReal.inv_lt_inv, ENNReal.add_lt_add_iff_right one_ne_top]
  · have : (1 : ℝ≥0∞) ≤ x.1⁻¹ := ENNReal.one_le_inv.2 x.2
    simp only [inv_inv, monus_add_cancel_of_le this]

@[simp]
theorem orderIsoIicOneBirational_symm_apply (x : Iic (1 : ℝ≥0∞)) :
    orderIsoIicOneBirational.symm x = (monus x.1⁻¹ 1)⁻¹ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Order isomorphism between an initial interval in `ℝ≥0∞` and an initial interval in `ℝ≥0`. -/
@[simps! apply_coe]
def orderIsoIicCoe (a : ℝ≥0) : Iic (a : ℝ≥0∞) ≃o Iic a :=
  OrderIso.symm
    { toFun := fun x => ⟨x, coe_le_coe.2 x.2⟩
      invFun := fun x => ⟨ENNReal.toNNReal x, coe_le_coe.1 <| coe_toNNReal_le_self.trans x.2⟩
      left_inv := fun _ => Subtype.ext <| toNNReal_coe _
      right_inv := fun x => Subtype.ext <| coe_toNNReal (ne_top_of_le_ne_top coe_ne_top x.2)
      map_rel_iff' := fun {_ _} => by
        simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk, coe_le_coe, Subtype.coe_le_coe] }

@[simp]
theorem orderIsoIicCoe_symm_apply_coe (a : ℝ≥0) (b : Iic a) :
    ((orderIsoIicCoe a).symm b : ℝ≥0∞) = b :=
  rfl

/-- An order isomorphism between the extended nonnegative real numbers and the unit interval. -/
def orderIsoUnitIntervalBirational : ℝ≥0∞ ≃o Icc (0 : ℝ) 1 :=
  orderIsoIicOneBirational.trans <| (orderIsoIicCoe 1).trans <| (NNReal.orderIsoIccZeroCoe 1).symm

@[simp]
theorem orderIsoUnitIntervalBirational_apply_coe (x : ℝ≥0∞) :
    (orderIsoUnitIntervalBirational x : ℝ) = (x⁻¹ + 1)⁻¹.toReal :=
  rfl

theorem exists_inv_nat_lt {a : ℝ≥0∞} (h : a ≠ 0) : ∃ n : ℕ, (n : ℝ≥0∞)⁻¹ < a :=
  inv_inv a ▸ by simp only [ENNReal.inv_lt_inv, ENNReal.exists_nat_gt (inv_ne_top.2 h)]

theorem exists_nat_pos_mul_gt (ha : a ≠ 0) (hb : b ≠ ∞) : ∃ n > 0, b < (n : ℕ) * a :=
  let ⟨n, hn⟩ := ENNReal.exists_nat_gt (div_lt_top hb ha).ne
  ⟨n, Nat.cast_pos.1 hn.pos, by
    rwa [← ENNReal.div_lt_iff ⟨ha, Or.inl hb⟩]⟩

theorem exists_nat_mul_gt (ha : a ≠ 0) (hb : b ≠ ∞) : ∃ n : ℕ, b < n * a :=
  (exists_nat_pos_mul_gt ha hb).imp fun _ => And.right

theorem exists_nat_pos_inv_mul_lt (ha : a ≠ ∞) (hb : b ≠ 0) :
    ∃ n > 0, ((n : ℕ) : ℝ≥0∞)⁻¹ * a < b := by
  rcases exists_nat_pos_mul_gt hb ha with ⟨n, npos, hn⟩
  use n, npos
  rw [mul_comm]
  exact mul_inv_lt_of_lt_mul (by rwa [mul_comm] at hn)

theorem exists_nnreal_pos_mul_lt (ha : a ≠ ∞) (hb : b ≠ 0) : ∃ n > 0, ↑(n : ℝ≥0) * a < b := by
  rcases exists_nat_pos_inv_mul_lt ha hb with ⟨n, npos : 0 < n, hn⟩
  use (n : ℝ≥0)⁻¹
  simp [*]

theorem exists_inv_two_pow_lt (ha : a ≠ 0) : ∃ n : ℕ, 2⁻¹ ^ n < a := by
  rcases exists_inv_nat_lt ha with ⟨n, hn⟩
  refine ⟨n, lt_trans ?_ hn⟩
  rw [← ENNReal.inv_pow, ENNReal.inv_lt_inv]
  norm_cast
  exact n.lt_two_pow_self

@[simp, norm_cast]
theorem coe_zpow (n : ℤ) {h : n < 0 → IsUnit r} : (↑(r ^ n) : ℝ≥0∞) = (r : ℝ≥0∞) ^ n := by
  rcases n with n | n
  · simp only [Int.ofNat_eq_natCast, zpow_natCast₀, coe_pow, ENNReal.zpow_natCast]
  · rw [zpow_negSucc₀, coe_inv, coe_pow, ENNReal.zpow_negSucc]

lemma zero_zpow_def (n : ℤ) : (0 : ℝ≥0∞) ^ n = if n = 0 then 1 else if 0 < n then 0 else ⊤ := by
  obtain ((_ | n) | n) := n <;> simp [-Nat.cast_add, -Int.natCast_add]

lemma top_zpow_def (n : ℤ) : (⊤ : ℝ≥0∞) ^ n = if n = 0 then 1 else if 0 < n then ⊤ else 0 := by
  obtain ((_ | n) | n) := n <;> simp [-Nat.cast_add, -Int.natCast_add]

theorem zpow_pos (ha : a ≠ 0) (h'a : a ≠ ∞) (n : ℤ) : 0 < a ^ n := by
  cases n
  · simpa using ENNReal.pow_pos ha.bot_lt _
  · simp only [h'a, pow_eq_top_iff, ENNReal.zpow_negSucc, Ne, ENNReal.inv_pos, false_and,
      not_false_eq_true]

theorem zpow_lt_top (ha : a ≠ 0) (h'a : a ≠ ∞) (n : ℤ) : a ^ n < ∞ := by
  cases n
  · simpa using ENNReal.pow_lt_top h'a.lt_top
  · simp only [ENNReal.pow_pos ha.bot_lt, ENNReal.zpow_negSucc, inv_lt_top]

@[aesop (rule_sets := [finiteness]) unsafe apply]
lemma zpow_ne_top {a : ℝ≥0∞} (ha : a ≠ 0) (h'a : a ≠ ∞) (n : ℤ) : a ^ n ≠ ∞ :=
  (ENNReal.zpow_lt_top ha h'a n).ne

theorem exists_mem_Ico_zpow {x y : ℝ≥0∞} (hx : x ≠ 0) (h'x : x ≠ ∞) (hy : 1 < y) (h'y : y ≠ ⊤) :
    ∃ n : ℤ, x ∈ Ico (y ^ n) (y ^ (n + 1)) := by
  lift x to ℝ≥0 using h'x
  lift y to ℝ≥0 using h'y
  have A : y ≠ 0 := by simpa only [Ne, coe_eq_zero] using (zero_lt_one.trans hy).ne'
  obtain ⟨n, hn, h'n⟩ : ∃ n : ℤ, y ^ n ≤ x ∧ x < y ^ (n + 1) := by
    refine NNReal.exists_mem_Ico_zpow ?_ (one_lt_coe_iff.1 hy)
    simpa only [Ne, coe_eq_zero] using hx
  refine ⟨n, ?_, ?_⟩
  · rwa [← ENNReal.coe_zpow (h := fun _ ↦ A.isUnit), ENNReal.coe_le_coe]
  · rwa [← ENNReal.coe_zpow (h := fun _ ↦ A.isUnit), ENNReal.coe_lt_coe]

theorem exists_mem_Ioc_zpow {x y : ℝ≥0∞} (hx : x ≠ 0) (h'x : x ≠ ∞) (hy : 1 < y) (h'y : y ≠ ⊤) :
    ∃ n : ℤ, x ∈ Ioc (y ^ n) (y ^ (n + 1)) := by
  lift x to ℝ≥0 using h'x
  lift y to ℝ≥0 using h'y
  have A : y ≠ 0 := by simpa only [Ne, coe_eq_zero] using (zero_lt_one.trans hy).ne'
  obtain ⟨n, hn, h'n⟩ : ∃ n : ℤ, y ^ n < x ∧ x ≤ y ^ (n + 1) := by
    refine NNReal.exists_mem_Ioc_zpow ?_ (one_lt_coe_iff.1 hy)
    simpa only [Ne, coe_eq_zero] using hx
  refine ⟨n, ?_, ?_⟩
  · rwa [← ENNReal.coe_zpow (h := fun _ ↦ A.isUnit), ENNReal.coe_lt_coe]
  · rwa [← ENNReal.coe_zpow (h := fun _ ↦ A.isUnit), ENNReal.coe_le_coe]

theorem Ioo_zero_top_eq_iUnion_Ico_zpow {y : ℝ≥0∞} (hy : 1 < y) (h'y : y ≠ ⊤) :
    Ioo (0 : ℝ≥0∞) (∞ : ℝ≥0∞) = ⋃ n : ℤ, Ico (y ^ n) (y ^ (n + 1)) := by
  ext x
  simp only [mem_iUnion, mem_Ioo, mem_Ico]
  constructor
  · rintro ⟨hx, h'x⟩
    exact exists_mem_Ico_zpow hx.ne' h'x.ne hy h'y
  · rintro ⟨n, hn, h'n⟩
    constructor
    · apply lt_of_lt_of_le _ hn
      exact ENNReal.zpow_pos (zero_lt_one.trans hy).ne' h'y _
    · apply lt_trans h'n _
      exact ENNReal.zpow_lt_top (zero_lt_one.trans hy).ne' h'y _

@[gcongr]
theorem zpow_le_of_le {x : ℝ≥0∞} (hx : 1 ≤ x) {a b : ℤ} (h : a ≤ b) : x ^ a ≤ x ^ b := by
  obtain a | a := a <;> obtain b | b := b
  · simp only [Int.ofNat_eq_natCast, ENNReal.zpow_natCast]
    exact pow_right_mono₀ hx (Int.le_of_ofNat_le_ofNat h)
  · apply absurd h (not_le_of_gt _)
    exact lt_of_lt_of_le (Int.negSucc_lt_zero _) (Int.natCast_nonneg _)
  · simp only [ENNReal.zpow_negSucc, Int.ofNat_eq_natCast, ENNReal.zpow_natCast]
    refine (ENNReal.inv_le_one.2 ?_).trans ?_ <;> exact one_le_pow_of_one_le' hx _
  · simp only [ENNReal.zpow_negSucc, ENNReal.inv_le_inv]
    apply pow_right_mono₀ hx
    simpa only [← Int.ofNat_le, neg_le_neg_iff, Int.natCast_add, Int.ofNat_one] using! h

theorem monotone_zpow {x : ℝ≥0∞} (hx : 1 ≤ x) : Monotone ((x ^ ·) : ℤ → ℝ≥0∞) := fun _ _ h =>
  zpow_le_of_le hx h

protected theorem zpow_add {x : ℝ≥0∞} (hx : x ≠ 0) (h'x : x ≠ ∞) (m n : ℤ) :
    x ^ (m + n) = x ^ m * x ^ n := by
  lift x to ℝ≥0 using h'x
  replace hx : x ≠ 0 := by simpa only [Ne, coe_eq_zero] using hx
  simp only [← coe_zpow (h := fun _ ↦ hx.isUnit), zpow_add₀ hx, coe_mul]

protected theorem zpow_neg (x : ℝ≥0∞) (m : ℤ) : x ^ (-m) = (x ^ m)⁻¹ := by
  obtain hx₀ | hx₀ := eq_or_ne x 0
  · obtain hm | hm | hm := lt_trichotomy m 0 <;>
      simp_all [zero_zpow_def, ne_of_lt, ne_of_gt, lt_asymm]
  obtain hx | hx := eq_or_ne x ⊤
  · obtain hm | hm | hm := lt_trichotomy m 0 <;>
      simp_all [top_zpow_def, ne_of_lt, ne_of_gt, lt_asymm]
  exact ENNReal.eq_inv_of_mul_eq_one_left (by simp [← ENNReal.zpow_add hx₀ hx])

protected theorem zpow_sub {x : ℝ≥0∞} (x_ne_zero : x ≠ 0) (x_ne_top : x ≠ ⊤) (m n : ℤ) :
    x ^ (m - n) = (x ^ m) * (x ^ n)⁻¹ := by
  rw [sub_eq_add_neg, ENNReal.zpow_add x_ne_zero x_ne_top, ENNReal.zpow_neg]

protected lemma inv_zpow (x : ℝ≥0∞) (n : ℤ) : x⁻¹ ^ n = (x ^ n)⁻¹ := by
  cases n <;> simp [ENNReal.inv_pow]

protected lemma inv_zpow' (x : ℝ≥0∞) (n : ℤ) : x⁻¹ ^ n = x ^ (-n) := by
  rw [ENNReal.zpow_neg, ENNReal.inv_zpow]

lemma zpow_le_one_of_nonpos {n : ℤ} (hn : n ≤ 0) {x : ℝ≥0∞} (hx : 1 ≤ x) : x ^ n ≤ 1 := by
  obtain ⟨m, rfl⟩ := neg_surjective n
  lift m to ℕ using by simpa using hn
  rw [← ENNReal.inv_zpow', ENNReal.inv_zpow, ENNReal.inv_le_one]
  exact mod_cast one_le_pow₀ hx

lemma isUnit_iff : IsUnit a ↔ a ≠ 0 ∧ a ≠ ∞ := by
  exact ⟨fun ha ↦ ⟨ha.ne_zero, isUnit_ne_top ha⟩,
    fun ha ↦ ⟨⟨a, a⁻¹, ENNReal.mul_inv_cancel ha.1 ha.2, ENNReal.inv_mul_cancel ha.1 ha.2⟩, rfl⟩⟩

/-- Checked division by a unit agrees with ordinary extended-real division. -/
theorem checkedDiv_eq_div (a b : ℝ≥0∞) (hb : IsUnit b) :
    Checked.div a b hb = div a b ⟨hb.ne_zero, Or.inr (isUnit_iff.1 hb).2⟩ :=
  congrArg (a * ·) (ENNReal.eq_inv_of_mul_eq_one_left hb.val_inv_mul)

/-- Left multiplication by a nonzero finite `a` as an order isomorphism. -/
@[simps! toEquiv apply symm_apply]
def mulLeftOrderIso (a : ℝ≥0∞) (ha : IsUnit a) : ℝ≥0∞ ≃o ℝ≥0∞ where
  toEquiv := ha.unit.mulLeft
  map_rel_iff' := by simp [ENNReal.mul_le_mul_iff_right, ha.ne_zero, (isUnit_iff.1 ha).2]

/-- Right multiplication by a nonzero finite `a` as an order isomorphism. -/
@[simps! toEquiv apply symm_apply]
def mulRightOrderIso (a : ℝ≥0∞) (ha : IsUnit a) : ℝ≥0∞ ≃o ℝ≥0∞ where
  toEquiv := ha.unit.mulRight
  map_rel_iff' := by simp [ENNReal.mul_le_mul_iff_left, ha.ne_zero, (isUnit_iff.1 ha).2]

variable {ι κ : Sort*} {f g : ι → ℝ≥0∞} {s : Set ℝ≥0∞} {a : ℝ≥0∞}

lemma mul_iSup (a : ℝ≥0∞) (f : ι → ℝ≥0∞) : a * ⨆ i, f i = ⨆ i, a * f i := by
  by_cases hf : ∀ i, f i = 0
  · simp [hf]
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp
  obtain rfl | ha := eq_or_ne a ∞
  · obtain ⟨i, hi⟩ := not_forall.1 hf
    simpa [iSup_eq_zero.not.2 hf, eq_comm (a := ⊤)]
      using le_iSup_of_le (f := fun i => ⊤ * f i) i (top_mul hi).ge
  · exact (mulLeftOrderIso _ <| isUnit_iff.2 ⟨ha₀, ha⟩).map_iSup _

lemma iSup_mul (f : ι → ℝ≥0∞) (a : ℝ≥0∞) : (⨆ i, f i) * a = ⨆ i, f i * a := by
  simp [mul_comm, mul_iSup]

lemma mul_sSup {a : ℝ≥0∞} : a * sSup s = ⨆ b ∈ s, a * b := by
  simp only [sSup_eq_iSup, mul_iSup]

lemma sSup_mul {a : ℝ≥0∞} : sSup s * a = ⨆ b ∈ s, b * a := by
  simp only [sSup_eq_iSup, iSup_mul]

instance : IsQuantale ℝ≥0∞ where
  mul_sSup_distrib _ _ := ENNReal.mul_sSup
  sSup_mul_distrib _ _ := ENNReal.sSup_mul

open scoped Quantale

theorem leftMulResiduation_eq_extendedDiv
    (h : (a ≠ 0 ∨ b ≠ 0) ∧ (a ≠ ∞ ∨ b ≠ ∞)) : (b ⇨ₗ a) = extendedDiv a b h := by
  apply le_antisymm
  · exact (le_extendedDiv_iff_mul_le h).2
      (Quantale.leftMulResiduation_le_iff_mul_le.1 le_rfl)
  · exact Quantale.leftMulResiduation_le_iff_mul_le.2
      ((le_extendedDiv_iff_mul_le h).1 le_rfl)

@[simp] theorem zero_leftMulResiduation (a : ℝ≥0∞) : (0 ⇨ₗ a) = ∞ :=
  top_unique (Quantale.leftMulResiduation_le_iff_mul_le.2 (by simp))

@[simp] theorem leftMulResiduation_top (b : ℝ≥0∞) : (b ⇨ₗ ∞) = ∞ :=
  top_unique (Quantale.leftMulResiduation_le_iff_mul_le.2 le_top)

theorem leftMulResiduation_eq_divInf_iff (a b : ℝ≥0∞) :
    (b ⇨ₗ a) = divInf a b ↔ (a ≠ 0 ∨ b ≠ 0) ∧ (a ≠ ∞ ∨ b ≠ ∞) := by
  constructor
  · intro he
    constructor
    · by_contra! h
      obtain ⟨rfl, rfl⟩ := h
      simp [divInf] at he
    · by_contra! h
      obtain ⟨rfl, rfl⟩ := h
      simp [divInf] at he
  · exact leftMulResiduation_eq_extendedDiv

/-- Very general version for distributivity of multiplication over an infimum.

See `ENNReal.mul_iInf_of_ne` for the special case assuming `a ≠ 0` and `a ≠ ∞`, and
`ENNReal.mul_iInf` for the special case assuming `Nonempty ι`. -/
lemma mul_iInf' (hinfty : a = ∞ → ⨅ i, f i = 0 → ∃ i, f i = 0) (h₀ : a = 0 → Nonempty ι) :
    a * ⨅ i, f i = ⨅ i, a * f i := by
  obtain rfl | ha₀ := eq_or_ne a 0
  · simp [h₀ rfl]
  obtain rfl | ha := eq_or_ne a ∞
  · obtain ⟨i, hi⟩ | hf := em (∃ i, f i = 0)
    · rw [iInf_eq_bot.2, iInf_eq_bot.2, bot_eq_zero, mul_zero] <;>
        exact fun _ _ ↦ ⟨i, by simpa [hi]⟩
    · rw [top_mul (mt (hinfty rfl) hf), eq_comm, iInf_eq_top]
      exact fun i ↦ top_mul fun hi ↦ hf ⟨i, hi⟩
  · exact (mulLeftOrderIso _ <| isUnit_iff.2 ⟨ha₀, ha⟩).map_iInf _

/-- Very general version for distributivity of multiplication over an infimum.

See `ENNReal.iInf_mul_of_ne` for the special case assuming `a ≠ 0` and `a ≠ ∞`, and
`ENNReal.iInf_mul` for the special case assuming `Nonempty ι`. -/
lemma iInf_mul' (hinfty : a = ∞ → ⨅ i, f i = 0 → ∃ i, f i = 0) (h₀ : a = 0 → Nonempty ι) :
    (⨅ i, f i) * a = ⨅ i, f i * a := by simpa only [mul_comm a] using mul_iInf' hinfty h₀

/-- If `a ≠ 0` and `a ≠ ∞`, then right multiplication by `a` maps infimum to infimum.

See `ENNReal.mul_iInf'` for the general case, and `ENNReal.iInf_mul` for another special case that
assumes `Nonempty ι` but does not require `a ≠ 0`, and `ENNReal`. -/
lemma mul_iInf_of_ne (ha₀ : a ≠ 0) (ha : a ≠ ∞) : a * ⨅ i, f i = ⨅ i, a * f i :=
  mul_iInf' (by simp [ha]) (by simp [ha₀])

/-- If `a ≠ 0` and `a ≠ ∞`, then right multiplication by `a` maps infimum to infimum.

See `ENNReal.iInf_mul'` for the general case, and `ENNReal.iInf_mul` for another special case that
assumes `Nonempty ι` but does not require `a ≠ 0`. -/
lemma iInf_mul_of_ne (ha₀ : a ≠ 0) (ha : a ≠ ∞) : (⨅ i, f i) * a = ⨅ i, f i * a :=
  iInf_mul' (by simp [ha]) (by simp [ha₀])

/-- See `ENNReal.mul_iInf'` for the general case, and `ENNReal.mul_iInf_of_ne` for another special
case that assumes `a ≠ 0` but does not require `Nonempty ι`. -/
lemma mul_iInf [Nonempty ι] (hinfty : a = ∞ → ⨅ i, f i = 0 → ∃ i, f i = 0) :
    a * ⨅ i, f i = ⨅ i, a * f i := mul_iInf' hinfty fun _ ↦ ‹Nonempty ι›

/-- See `ENNReal.iInf_mul'` for the general case, and `ENNReal.iInf_mul_of_ne` for another special
case that assumes `a ≠ 0` but does not require `Nonempty ι`. -/
lemma iInf_mul [Nonempty ι] (hinfty : a = ∞ → ⨅ i, f i = 0 → ∃ i, f i = 0) :
    (⨅ i, f i) * a = ⨅ i, f i * a := iInf_mul' hinfty fun _ ↦ ‹Nonempty ι›

lemma inv_iInf (f : ι → ℝ≥0∞) : (⨅ i, f i)⁻¹ = ⨆ i, (f i)⁻¹ := OrderIso.invENNReal.map_iInf _
lemma inv_iSup (f : ι → ℝ≥0∞) : (⨆ i, f i)⁻¹ = ⨅ i, (f i)⁻¹ := OrderIso.invENNReal.map_iSup _

lemma inv_sInf (s : Set ℝ≥0∞) : (sInf s)⁻¹ = ⨆ a ∈ s, a⁻¹ := by simp [sInf_eq_iInf, inv_iInf]
lemma inv_sSup (s : Set ℝ≥0∞) : (sSup s)⁻¹ = ⨅ a ∈ s, a⁻¹ := by simp [sSup_eq_iSup, inv_iSup]

lemma le_iInf_mul {ι : Type*} (u v : ι → ℝ≥0∞) :
    (⨅ i, u i) * ⨅ i, v i ≤ ⨅ i, u i * v i :=
  le_iInf fun i ↦ mul_le_mul' (iInf_le u i) (iInf_le v i)

lemma iSup_mul_le {ι : Type*} {u v : ι → ℝ≥0∞} :
    ⨆ i, u i * v i ≤ (⨆ i, u i) * ⨆ i, v i :=
  iSup_le fun i ↦ mul_le_mul' (le_iSup u i) (le_iSup v i)


lemma le_iInf_mul_iInf {g : κ → ℝ≥0∞} (hf : ∃ i, f i ≠ ∞) (hg : ∃ j, g j ≠ ∞)
    (ha : ∀ i j, a ≤ f i * g j) : a ≤ (⨅ i, f i) * ⨅ j, g j := by
  rw [← iInf_ne_top_subtype]
  have := nonempty_subtype.2 hf
  have := hg.nonempty
  replace hg : ⨅ j, g j ≠ ∞ := by simpa using hg
  rw [iInf_mul fun h ↦ (hg h).elim, le_iInf_iff]
  rintro ⟨i, hi⟩
  simpa [mul_iInf fun h ↦ (hi h).elim] using ha i

lemma iInf_mul_iInf {f g : ι → ℝ≥0∞} (hf : ∃ i, f i ≠ ∞) (hg : ∃ j, g j ≠ ∞)
    (h : ∀ i j, ∃ k, f k * g k ≤ f i * g j) : (⨅ i, f i) * ⨅ i, g i = ⨅ i, f i * g i := by
  refine le_antisymm (le_iInf fun i ↦ mul_le_mul' (iInf_le ..) (iInf_le ..))
    (le_iInf_mul_iInf hf hg fun i j ↦ ?_)
  obtain ⟨k, hk⟩ := h i j
  exact iInf_le_of_le k hk

lemma smul_iSup {R} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (f : ι → ℝ≥0∞) (c : R) :
    c • ⨆ i, f i = ⨆ i, c • f i := by
  simp only [← smul_one_mul c (f _), ← smul_one_mul c (iSup _), ENNReal.mul_iSup]

lemma smul_sSup {R} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (s : Set ℝ≥0∞) (c : R) :
    c • sSup s = ⨆ a ∈ s, c • a := by
  simp_rw [← smul_one_mul c (sSup s), ENNReal.mul_sSup, smul_one_mul]

@[simp]
theorem ofReal_inv_of_pos {x : ℝ} (hx : 0 < x) : ENNReal.ofReal x⁻¹ = (ENNReal.ofReal x)⁻¹ := by
  rw [ENNReal.ofReal, ENNReal.ofReal, ← coe_inv (hr := (Real.toNNReal_pos.2 hx).ne'.isUnit),
    coe_inj, Real.toNNReal_inv hx]

theorem ofReal_inv_le {x : ℝ} {hx : IsUnit x} : ENNReal.ofReal x⁻¹ ≤ (ENNReal.ofReal x)⁻¹ := by
  obtain hx' | hx' := lt_or_ge 0 x
  · simp [ofReal_inv_of_pos hx']
  · simp [ofReal_of_nonpos hx']

theorem ofReal_div_of_pos {x y : ℝ} (hy : 0 < y) :
    ENNReal.ofReal (x / y) =
      div (ENNReal.ofReal x) (ENNReal.ofReal y)
        ⟨coe_ne_zero.2 (Real.toNNReal_pos.2 hy).ne', Or.inr ofReal_ne_top⟩ := by
  rw [div_eq_mul_inv₀, ENNReal.div_eq_mul_inv, ofReal_mul' (inv_nonneg.2 hy.le),
    ofReal_inv_of_pos hy]

/-- The inverse commutes with `toNNReal` exactly where `a.toNNReal` is invertible, that is, for
`a ≠ 0` and `a ≠ ∞`. -/
theorem toNNReal_inv (a : ℝ≥0∞) {ha : IsUnit a.toNNReal} :
    a⁻¹.toNNReal = a.toNNReal⁻¹ := by
  cases a with
  | top => simp at ha
  | coe a =>
    have ha' : IsUnit a := ha
    rw [← coe_inv (hr := ha'), toNNReal_coe]
    rfl

theorem toNNReal_div (a b : ℝ≥0∞) {hb : IsUnit b.toNNReal} :
    (div a b ⟨(toNNReal_ne_zero.1 hb.ne_zero).1,
      Or.inr (toNNReal_ne_zero.1 hb.ne_zero).2⟩).toNNReal = a.toNNReal / b.toNNReal := by
  rw [ENNReal.div_eq_mul_inv, toNNReal_mul, toNNReal_inv b (ha := hb), div_eq_mul_inv₀]

theorem toReal_inv (a : ℝ≥0∞) {ha : IsUnit a.toReal} : a⁻¹.toReal = a.toReal⁻¹ := by
  have ha' : IsUnit a.toNNReal := (NNReal.coe_ne_zero.1 ha.ne_zero).isUnit
  simp only [ENNReal.toReal, toNNReal_inv a (ha := ha'), NNReal.coe_inv]

theorem toReal_div (a b : ℝ≥0∞) {hb : IsUnit b.toReal} :
    (div a b ⟨(toReal_ne_zero.1 hb.ne_zero).1,
      Or.inr (toReal_ne_zero.1 hb.ne_zero).2⟩).toReal = a.toReal / b.toReal := by
  rw [ENNReal.div_eq_mul_inv, toReal_mul, toReal_inv b (ha := hb), div_eq_mul_inv₀]

/-- Projecting a finite nonzero input's inverse to `ℝ≥0` gives its checked inverse. -/
@[simp] theorem toNNReal_inv_of_toNNReal_ne_zero (a : ℝ≥0∞) (ha : a.toNNReal ≠ 0) :
    a⁻¹.toNNReal = Checked.inv a.toNNReal ha.isUnit :=
  toNNReal_inv a (ha := ha.isUnit)

/-- `toNNReal` takes a quotient with a finite nonzero denominator to checked division. -/
@[simp] theorem toNNReal_div_of_toNNReal_ne_zero (a b : ℝ≥0∞) (hb : b.toNNReal ≠ 0) :
    (div a b ⟨(toNNReal_ne_zero.1 hb).1, Or.inr (toNNReal_ne_zero.1 hb).2⟩).toNNReal =
      Checked.div a.toNNReal b.toNNReal hb.isUnit :=
  toNNReal_div a b (hb := hb.isUnit)

/-- Projecting a finite nonzero input's inverse to `ℝ` gives its checked inverse. -/
@[simp] theorem toReal_inv_of_toReal_ne_zero (a : ℝ≥0∞) (ha : a.toReal ≠ 0) :
    a⁻¹.toReal = Checked.inv a.toReal ha.isUnit :=
  toReal_inv a (ha := ha.isUnit)

/-- `toReal` takes a quotient with a finite nonzero denominator to checked division. -/
@[simp] theorem toReal_div_of_toReal_ne_zero (a b : ℝ≥0∞) (hb : b.toReal ≠ 0) :
    (div a b ⟨(toReal_ne_zero.1 hb).1, Or.inr (toReal_ne_zero.1 hb).2⟩).toReal =
      Checked.div a.toReal b.toReal hb.isUnit :=
  toReal_div a b (hb := hb.isUnit)

end Inv
end ENNReal
