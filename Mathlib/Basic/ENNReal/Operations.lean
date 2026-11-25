/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Tactic.Finiteness

/-!
# Properties of addition, multiplication and monus on extended nonnegative real numbers

In this file we prove elementary properties of algebraic operations on `ℝ≥0∞`, including addition,
multiplication, natural powers and monus, as well as how these interact with the
order structure on `ℝ≥0∞`. Notably excluded from this list are inversion and division, the
definitions and properties of which can be found in `Mathlib/Basic/ENNReal/Inv.lean`.

Note: the definitions of the operations included in this file can be found in
`Mathlib/Basic/ENNReal/Basic.lean`.
-/

public section

assert_not_exists Finset

open Set NNReal ENNReal

namespace ENNReal

variable {a b c d : ℝ≥0∞} {r p q : ℝ≥0}

section Mul

@[mono, gcongr]
theorem mul_lt_mul (ac : a < c) (bd : b < d) : a * b < c * d := WithTop.mul_lt_mul ac bd

protected lemma pow_right_strictMono {n : ℕ} (hn : n ≠ 0) : StrictMono fun a : ℝ≥0∞ ↦ a ^ n :=
  WithTop.pow_right_strictMono hn

protected lemma pow_le_pow_left_iff {n : ℕ} (hn : n ≠ 0) : a ^ n ≤ b ^ n ↔ a ≤ b :=
  (ENNReal.pow_right_strictMono hn).le_iff_le

protected lemma pow_lt_pow_left_iff {n : ℕ} (hn : n ≠ 0) : a ^ n < b ^ n ↔ a < b :=
  (ENNReal.pow_right_strictMono hn).lt_iff_lt

@[mono, gcongr] protected lemma pow_le_pow_left {n : ℕ} (h : a ≤ b) : a ^ n ≤ b ^ n :=
  pow_le_pow_left' h n
@[mono, gcongr] protected alias ⟨_, pow_lt_pow_left⟩ := ENNReal.pow_lt_pow_left_iff

lemma mul_left_strictMono (h₀ : a ≠ 0) (hinf : a ≠ ∞) : StrictMono (· * a) :=
  WithTop.mul_left_strictMono (pos_iff_ne_zero.2 h₀) hinf

lemma mul_right_strictMono (h₀ : a ≠ 0) (hinf : a ≠ ∞) : StrictMono (a * ·) :=
  WithTop.mul_right_strictMono (pos_iff_ne_zero.2 h₀) hinf

@[gcongr] protected theorem mul_lt_mul_right (h0 : a ≠ 0) (hinf : a ≠ ⊤) (bc : b < c) :
    a * b < a * c :=
  ENNReal.mul_right_strictMono h0 hinf bc

@[gcongr] protected theorem mul_lt_mul_left (h0 : a ≠ 0) (hinf : a ≠ ⊤) (bc : b < c) :
    b * a < c * a :=
  mul_comm b a ▸ mul_comm c a ▸ ENNReal.mul_right_strictMono h0 hinf bc

-- TODO: generalize to `WithTop`
protected theorem mul_right_inj (h0 : a ≠ 0) (hinf : a ≠ ∞) : a * b = a * c ↔ b = c :=
  (mul_right_strictMono h0 hinf).injective.eq_iff

-- TODO: generalize to `WithTop`
protected theorem mul_left_inj (h0 : c ≠ 0) (hinf : c ≠ ∞) : a * c = b * c ↔ a = b :=
  mul_comm c a ▸ mul_comm c b ▸ ENNReal.mul_right_inj h0 hinf

-- TODO: generalize to `WithTop`
protected lemma mul_le_mul_iff_right (h0 : a ≠ 0) (hinf : a ≠ ∞) : a * b ≤ a * c ↔ b ≤ c :=
  (mul_right_strictMono h0 hinf).le_iff_le

-- TODO: generalize to `WithTop`
protected lemma mul_le_mul_iff_left (h0 : c ≠ 0) (hinf : c ≠ ∞) : a * c ≤ b * c ↔ a ≤ b :=
  (mul_left_strictMono h0 hinf).le_iff_le

-- TODO: generalize to `WithTop`
protected lemma mul_lt_mul_iff_right (h0 : a ≠ 0) (hinf : a ≠ ∞) : a * b < a * c ↔ b < c :=
  (mul_right_strictMono h0 hinf).lt_iff_lt

-- TODO: generalize to `WithTop`
protected lemma mul_lt_mul_iff_left (h0 : c ≠ 0) (hinf : c ≠ ∞) : a * c < b * c ↔ a < b :=
  (mul_left_strictMono h0 hinf).lt_iff_lt

protected lemma mul_eq_left (ha₀ : a ≠ 0) (ha : a ≠ ∞) : a * b = a ↔ b = 1 := by
  simpa using ENNReal.mul_right_inj ha₀ ha (c := 1)

protected lemma mul_eq_right (hb₀ : b ≠ 0) (hb : b ≠ ∞) : a * b = b ↔ a = 1 := by
  simpa using ENNReal.mul_left_inj hb₀ hb (b := 1)

end Mul

section OperationsAndOrder

protected theorem pow_pos : 0 < a → ∀ n : ℕ, 0 < a ^ n :=
  CanonicallyOrderedAdd.pow_pos

protected theorem pow_ne_zero : a ≠ 0 → ∀ n : ℕ, a ^ n ≠ 0 := by
  simpa only [pos_iff_ne_zero] using ENNReal.pow_pos

theorem not_lt_zero : ¬a < 0 := by simp

protected theorem le_of_add_le_add_left : a ≠ ∞ → a + b ≤ a + c → b ≤ c :=
  WithTop.le_of_add_le_add_left

protected theorem le_of_add_le_add_right : a ≠ ∞ → b + a ≤ c + a → b ≤ c :=
  WithTop.le_of_add_le_add_right

@[gcongr] protected theorem add_lt_add_left : a ≠ ∞ → b < c → a + b < a + c :=
  WithTop.add_lt_add_left

@[gcongr] protected theorem add_lt_add_right : a ≠ ∞ → b < c → b + a < c + a :=
  WithTop.add_lt_add_right

protected theorem add_le_add_iff_left : a ≠ ∞ → (a + b ≤ a + c ↔ b ≤ c) :=
  WithTop.add_le_add_iff_left

protected theorem add_le_add_iff_right : a ≠ ∞ → (b + a ≤ c + a ↔ b ≤ c) :=
  WithTop.add_le_add_iff_right

protected theorem add_lt_add_iff_left : a ≠ ∞ → (a + b < a + c ↔ b < c) :=
  WithTop.add_lt_add_iff_left

protected theorem add_lt_add_iff_right : a ≠ ∞ → (b + a < c + a ↔ b < c) :=
  WithTop.add_lt_add_iff_right

protected theorem add_lt_add_of_le_of_lt : a ≠ ∞ → a ≤ b → c < d → a + c < b + d :=
  WithTop.add_lt_add_of_le_of_lt

protected theorem add_lt_add_of_lt_of_le : c ≠ ∞ → a < b → c ≤ d → a + c < b + d :=
  WithTop.add_lt_add_of_lt_of_le

instance addLeftReflectLT : AddLeftReflectLT ℝ≥0∞ :=
  WithTop.addLeftReflectLT

theorem lt_add_right (ha : a ≠ ∞) (hb : b ≠ 0) : a < a + b := by
  rwa [← pos_iff_ne_zero, ← ENNReal.add_lt_add_iff_left ha, add_zero] at hb

end OperationsAndOrder

section OperationsAndInfty

variable {α : Type*} {n : ℕ}

@[simp] theorem add_eq_top : a + b = ∞ ↔ a = ∞ ∨ b = ∞ := WithTop.add_eq_top

@[simp] theorem add_lt_top : a + b < ∞ ↔ a < ∞ ∧ b < ∞ := WithTop.add_lt_top

theorem toNNReal_add {r₁ r₂ : ℝ≥0∞} (h₁ : r₁ ≠ ∞) (h₂ : r₂ ≠ ∞) :
    (r₁ + r₂).toNNReal = r₁.toNNReal + r₂.toNNReal := by
  lift r₁ to ℝ≥0 using h₁
  lift r₂ to ℝ≥0 using h₂
  rfl

/-- If `a ≤ b + c` and `a = ∞` whenever `b = ∞` or `c = ∞`, then
`ENNReal.toReal a ≤ ENNReal.toReal b + ENNReal.toReal c`. This lemma is useful to transfer
triangle-like inequalities from `ENNReal`s to `Real`s. -/
theorem toReal_le_add' (hle : a ≤ b + c) (hb : b = ∞ → a = ∞) (hc : c = ∞ → a = ∞) :
    a.toReal ≤ b.toReal + c.toReal := by
  refine le_trans (toReal_mono' hle ?_) toReal_add_le
  simpa only [add_eq_top, or_imp] using And.intro hb hc

/-- If `a ≤ b + c`, `b ≠ ∞`, and `c ≠ ∞`, then
`ENNReal.toReal a ≤ ENNReal.toReal b + ENNReal.toReal c`. This lemma is useful to transfer
triangle-like inequalities from `ENNReal`s to `Real`s. -/
theorem toReal_le_add (hle : a ≤ b + c) (hb : b ≠ ∞) (hc : c ≠ ∞) :
    a.toReal ≤ b.toReal + c.toReal :=
  toReal_le_add' hle (flip absurd hb) (flip absurd hc)

theorem not_lt_top {x : ℝ≥0∞} : ¬x < ∞ ↔ x = ∞ := by rw [lt_top_iff_ne_top, Classical.not_not]

theorem add_ne_top : a + b ≠ ∞ ↔ a ≠ ∞ ∧ b ≠ ∞ := by simpa only [lt_top_iff_ne_top] using add_lt_top

@[aesop (rule_sets := [finiteness]) safe apply]
protected lemma Finiteness.add_ne_top {a b : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞) : a + b ≠ ∞ :=
  ENNReal.add_ne_top.2 ⟨ha, hb⟩

theorem mul_top' : a * ∞ = if a = 0 then 0 else ∞ := by convert! WithTop.mul_top' a

@[simp] theorem mul_top (h : a ≠ 0) : a * ∞ = ∞ := WithTop.mul_top h

theorem top_mul' : ∞ * a = if a = 0 then 0 else ∞ := by convert! WithTop.top_mul' a

@[simp] theorem top_mul (h : a ≠ 0) : ∞ * a = ∞ := WithTop.top_mul h

theorem top_mul_top : ∞ * ∞ = ∞ := WithTop.top_mul_top

theorem mul_eq_top : a * b = ∞ ↔ a ≠ 0 ∧ b = ∞ ∨ a = ∞ ∧ b ≠ 0 :=
  WithTop.mul_eq_top_iff

theorem mul_lt_top : a < ∞ → b < ∞ → a * b < ∞ := WithTop.mul_lt_top

-- This is unsafe because we could have `a = ∞` and `b = 0` or vice-versa
@[aesop (rule_sets := [finiteness]) unsafe 75% apply]
theorem mul_ne_top : a ≠ ∞ → b ≠ ∞ → a * b ≠ ∞ := WithTop.mul_ne_top

theorem lt_top_of_mul_ne_top_left (h : a * b ≠ ∞) (hb : b ≠ 0) : a < ∞ :=
  lt_top_iff_ne_top.2 fun ha => h <| mul_eq_top.2 (Or.inr ⟨ha, hb⟩)

theorem lt_top_of_mul_ne_top_right (h : a * b ≠ ∞) (ha : a ≠ 0) : b < ∞ :=
  lt_top_of_mul_ne_top_left (by rwa [mul_comm]) ha

theorem mul_lt_top_iff {a b : ℝ≥0∞} : a * b < ∞ ↔ a < ∞ ∧ b < ∞ ∨ a = 0 ∨ b = 0 := by
  constructor
  · intro h
    rw [← or_assoc, or_iff_not_imp_right, or_iff_not_imp_right]
    intro hb ha
    exact ⟨lt_top_of_mul_ne_top_left h.ne hb, lt_top_of_mul_ne_top_right h.ne ha⟩
  · rintro (⟨ha, hb⟩ | rfl | rfl) <;> [exact mul_lt_top ha hb; simp; simp]

theorem mul_self_lt_top_iff {a : ℝ≥0∞} : a * a < ⊤ ↔ a < ⊤ := by
  rw [ENNReal.mul_lt_top_iff, and_self, or_self, or_iff_left_iff_imp]
  rintro rfl
  exact zero_lt_top

theorem mul_pos_iff : 0 < a * b ↔ 0 < a ∧ 0 < b :=
  CanonicallyOrderedAdd.mul_pos

theorem mul_pos (ha : a ≠ 0) (hb : b ≠ 0) : 0 < a * b :=
  mul_pos_iff.2 ⟨pos_iff_ne_zero.2 ha, pos_iff_ne_zero.2 hb⟩

@[simp] lemma top_pow {n : ℕ} (hn : n ≠ 0) : (∞ : ℝ≥0∞) ^ n = ∞ := WithTop.top_pow hn

@[simp] lemma pow_eq_top_iff : a ^ n = ∞ ↔ a = ∞ ∧ n ≠ 0 := WithTop.pow_eq_top_iff

lemma pow_ne_top_iff : a ^ n ≠ ∞ ↔ a ≠ ∞ ∨ n = 0 := WithTop.pow_ne_top_iff

@[simp] lemma pow_lt_top_iff : a ^ n < ∞ ↔ a < ∞ ∨ n = 0 := WithTop.pow_lt_top_iff

lemma eq_top_of_pow (n : ℕ) (ha : a ^ n = ∞) : a = ∞ := WithTop.eq_top_of_pow n ha

@[aesop (rule_sets := [finiteness]) safe apply]
lemma pow_ne_top (ha : a ≠ ∞) : a ^ n ≠ ∞ := WithTop.pow_ne_top ha
lemma pow_lt_top (ha : a < ∞) : a ^ n < ∞ := WithTop.pow_lt_top ha

end OperationsAndInfty

@[gcongr] protected theorem add_lt_add (ac : a < c) (bd : b < d) : a + b < c + d :=
  WithTop.add_lt_add ac bd

section Cancel

/-- An element `a` is `AddLECancellable` if `a + b ≤ a + c` implies `b ≤ c` for all `b` and `c`.
  This is true in `ℝ≥0∞` for all elements except `∞`. -/
@[simp]
theorem addLECancellable_iff_ne {a : ℝ≥0∞} : AddLECancellable a ↔ a ≠ ∞ :=
  WithTop.addLECancellable_iff_ne_top

/-- This lemma has an abbreviated name because it is used frequently. -/
theorem cancel_of_ne {a : ℝ≥0∞} (h : a ≠ ∞) : AddLECancellable a :=
  addLECancellable_iff_ne.mpr h

/-- This lemma has an abbreviated name because it is used frequently. -/
theorem cancel_of_lt {a : ℝ≥0∞} (h : a < ∞) : AddLECancellable a :=
  cancel_of_ne h.ne

/-- This lemma has an abbreviated name because it is used frequently. -/
theorem cancel_of_lt' {a b : ℝ≥0∞} (h : a < b) : AddLECancellable a :=
  cancel_of_ne h.ne_top

/-- This lemma has an abbreviated name because it is used frequently. -/
theorem cancel_coe {a : ℝ≥0} : AddLECancellable (a : ℝ≥0∞) :=
  cancel_of_ne coe_ne_top

theorem add_right_inj (h : a ≠ ∞) : a + b = a + c ↔ b = c :=
  (cancel_of_ne h).inj_right

theorem add_left_inj (h : a ≠ ∞) : b + a = c + a ↔ b = c :=
  (cancel_of_ne h).inj_left

end Cancel

section Monus

theorem le_monus_add : a ≤ monus a b + b := monus_le_iff.mp le_rfl

/-- The least solution to `a ≤ q + b`, expressed as an infimum. -/
theorem monus_eq_sInf : monus a b = sInf {q | a ≤ q + b} :=
  le_antisymm (le_sInf fun _ h => monus_le_iff.mpr h) (sInf_le le_monus_add)

@[simp, norm_cast] theorem coe_monus : (↑(r - p) : ℝ≥0∞) = monus r p := rfl

@[simp] theorem top_monus_coe : monus ∞ r = ∞ := rfl

@[simp] theorem top_monus (ha : a ≠ ∞) : monus ∞ a = ∞ := by
  lift a to ℝ≥0 using ha
  exact top_monus_coe

@[simp] theorem monus_top : monus a ∞ = 0 := by
  cases a <;> rfl

@[simp] theorem monus_eq_top_iff : monus a b = ∞ ↔ a = ∞ ∧ b ≠ ∞ :=
  WithTop.sub_eq_top_iff (a := (a : WithTop ℝ≥0)) (b := (b : WithTop ℝ≥0))

lemma monus_ne_top_iff : monus a b ≠ ∞ ↔ a ≠ ∞ ∨ b = ∞ :=
  WithTop.sub_ne_top_iff (a := (a : WithTop ℝ≥0)) (b := (b : WithTop ℝ≥0))

-- The result can also be finite when both arguments are infinite.
@[aesop (rule_sets := [finiteness]) unsafe 75% apply]
theorem monus_ne_top (ha : a ≠ ∞) : monus a b ≠ ∞ :=
  monus_ne_top_iff.2 (.inl ha)

@[simp, norm_cast] theorem natCast_monus (m n : ℕ) :
    (↑(m - n) : ℝ≥0∞) = monus m n := by
  rw [← coe_natCast, Nat.cast_tsub, coe_monus, coe_natCast, coe_natCast]

theorem monus_eq_zero_iff_le : monus a b = 0 ↔ a ≤ b := by
  rw [← nonpos_iff_eq_zero, monus_le_iff, zero_add]

theorem monus_eq_zero_of_le (h : a ≤ b) : monus a b = 0 :=
  monus_eq_zero_iff_le.2 h

@[simp] theorem monus_pos_iff_lt : 0 < monus a b ↔ b < a := by
  rw [pos_iff_ne_zero, Ne, monus_eq_zero_iff_le, not_le]

theorem monus_pos_of_lt (h : b < a) : 0 < monus a b :=
  monus_pos_iff_lt.2 h

theorem lt_monus_iff_add_lt_right : a < monus b c ↔ a + c < b := by
  rw [← not_le, monus_le_iff, not_le]

theorem lt_monus_iff_add_lt_left : a < monus b c ↔ c + a < b := by
  rw [lt_monus_iff_add_lt_right, add_comm]

theorem lt_monus_comm : a < monus b c ↔ c < monus b a := by
  rw [lt_monus_iff_add_lt_right, lt_monus_iff_add_lt_left]

@[simp] theorem monus_self (a : ℝ≥0∞) : monus a a = 0 :=
  monus_eq_zero_of_le le_rfl

@[simp] theorem monus_zero (a : ℝ≥0∞) : monus a 0 = a := by
  apply eq_of_forall_ge_iff
  simp [monus_le_iff]

@[simp] theorem zero_monus (a : ℝ≥0∞) : monus 0 a = 0 :=
  monus_eq_zero_of_le zero_le

theorem monus_le_self : monus a b ≤ a := monus_le_iff.2 le_self_add

@[gcongr] theorem monus_le_monus (hac : a ≤ c) (hdb : d ≤ b) :
    monus a b ≤ monus c d :=
  monus_le_iff.2 (hac.trans <| (le_monus_add (a := c) (b := d)).trans <| add_le_add_right hdb _)

theorem monus_add_cancel_of_le (h : b ≤ a) : monus a b + b = a :=
  tsub_add_cancel_of_le (α := WithTop ℝ≥0) h

theorem add_le_of_le_monus_right_of_le (hcb : c ≤ b) (h : a ≤ monus b c) : a + c ≤ b :=
  (add_le_add_left h c).trans_eq (monus_add_cancel_of_le hcb)

theorem add_le_of_le_monus_left_of_le (hcb : c ≤ b) (h : a ≤ monus b c) : c + a ≤ b := by
  rw [add_comm]
  exact add_le_of_le_monus_right_of_le hcb h

/-- Recover the remaining summand when the removed summand is finite. -/
protected theorem monus_eq_of_eq_add (hb : b ≠ ∞) : a = c + b → monus a b = c :=
  AddLECancellable.tsub_eq_of_eq_add (α := WithTop ℝ≥0) (cancel_of_ne hb)

/-- Recover the remaining summand when the sum is finite. -/
protected theorem monus_eq_of_eq_add' (ha : a ≠ ∞) : a = c + b → monus a b = c :=
  AddLECancellable.tsub_eq_of_eq_add' (α := WithTop ℝ≥0) (cancel_of_ne ha)

protected theorem eq_monus_of_add_eq (hc : c ≠ ∞) (h : a + c = b) : a = monus b c :=
  (ENNReal.monus_eq_of_eq_add hc h.symm).symm

protected theorem eq_monus_of_add_eq' (hb : b ≠ ∞) (h : a + c = b) : a = monus b c :=
  (ENNReal.monus_eq_of_eq_add' hb h.symm).symm

protected theorem monus_eq_of_eq_add_rev (hb : b ≠ ∞) (h : a = b + c) : monus a b = c :=
  ENNReal.monus_eq_of_eq_add hb (h.trans (add_comm _ _))

protected theorem monus_eq_of_eq_add_rev' (ha : a ≠ ∞) (h : a = b + c) : monus a b = c :=
  ENNReal.monus_eq_of_eq_add' ha (h.trans (add_comm _ _))

protected theorem add_monus_cancel_left (ha : a ≠ ∞) : monus (a + b) a = b :=
  ENNReal.monus_eq_of_eq_add_rev ha rfl

protected theorem add_monus_cancel_right (hb : b ≠ ∞) : monus (a + b) b = a :=
  ENNReal.monus_eq_of_eq_add hb rfl

protected theorem monus_add_eq_add_monus (hab : b ≤ a) (hb : b ≠ ∞) :
    monus a b + c = monus (a + c) b := by
  apply ENNReal.eq_monus_of_add_eq hb
  rw [add_right_comm, monus_add_cancel_of_le hab]

lemma add_monus_add_eq_monus_right (hc : c ≠ ∞ := by finiteness) :
    monus (a + c) (b + c) = monus a b := by
  refine eq_of_forall_ge_iff fun q => ?_
  rw [monus_le_iff, monus_le_iff, ← add_assoc, ENNReal.add_le_add_iff_right hc]

lemma add_monus_add_eq_monus_left (hc : c ≠ ∞ := by finiteness) :
    monus (c + a) (c + b) = monus a b := by
  simpa only [add_comm c] using add_monus_add_eq_monus_right (a := a) (b := b) hc

protected theorem lt_add_of_monus_lt_left (h : a ≠ ∞ ∨ b ≠ ∞) :
    monus a b < c → a < b + c := by
  obtain rfl | hb := eq_or_ne b ∞
  · rw [top_add, lt_top_iff_ne_top]
    exact fun _ => h.resolve_right (Classical.not_not.2 rfl)
  · exact AddLECancellable.lt_add_of_tsub_lt_left (α := WithTop ℝ≥0) (cancel_of_ne hb)

protected theorem lt_add_of_monus_lt_right (h : a ≠ ∞ ∨ c ≠ ∞) :
    monus a c < b → a < b + c :=
  add_comm c b ▸ ENNReal.lt_add_of_monus_lt_left h

theorem le_monus_of_add_le_left (ha : a ≠ ∞) : a + b ≤ c → b ≤ monus c a :=
  AddLECancellable.le_tsub_of_add_le_left (α := WithTop ℝ≥0) (cancel_of_ne ha)

theorem le_monus_of_add_le_right (hb : b ≠ ∞) : a + b ≤ c → a ≤ monus c b :=
  AddLECancellable.le_tsub_of_add_le_right (α := WithTop ℝ≥0) (cancel_of_ne hb)

protected theorem monus_lt_iff_lt_right (hb : b ≠ ∞) (hab : b ≤ a) :
    monus a b < c ↔ a < c + b :=
  AddLECancellable.tsub_lt_iff_right (α := WithTop ℝ≥0) (cancel_of_ne hb) hab

protected theorem monus_lt_iff_lt_left (hb : b ≠ ∞) (hab : b ≤ a) :
    monus a b < c ↔ a < b + c :=
  AddLECancellable.tsub_lt_iff_left (α := WithTop ℝ≥0) (cancel_of_ne hb) hab

protected theorem monus_lt_of_lt_add (hac : c ≤ a) (h : a < b + c) : monus a c < b :=
  (ENNReal.monus_lt_iff_lt_right (hac.trans_lt h).ne_top hac).2 h

theorem le_monus_iff_add_le_right (hc : c ≠ ∞) (hcb : c ≤ b) :
    a ≤ monus b c ↔ a + c ≤ b :=
  ⟨add_le_of_le_monus_right_of_le hcb,
    le_monus_of_add_le_right hc⟩

theorem le_monus_iff_add_le_left (hc : c ≠ ∞) (hcb : c ≤ b) :
    a ≤ monus b c ↔ c + a ≤ b := by
  rw [le_monus_iff_add_le_right hc hcb, add_comm]

protected theorem monus_lt_self (ha : a ≠ ∞) (ha₀ : a ≠ 0) (hb : b ≠ 0) : monus a b < a :=
  AddLECancellable.tsub_lt_self (α := WithTop ℝ≥0) (cancel_of_ne ha)
    (pos_iff_ne_zero.2 ha₀) (pos_iff_ne_zero.2 hb)

protected theorem monus_lt_self_iff (ha : a ≠ ∞) : monus a b < a ↔ 0 < a ∧ 0 < b :=
  AddLECancellable.tsub_lt_self_iff (α := WithTop ℝ≥0) (cancel_of_ne ha)

theorem monus_lt_of_monus_lt (h₂ : c ≤ a) (h₃ : a ≠ ∞ ∨ b ≠ ∞) (h₁ : monus a b < c) :
    monus a c < b :=
  ENNReal.monus_lt_of_lt_add h₂ (add_comm c b ▸ ENNReal.lt_add_of_monus_lt_right h₃ h₁)

theorem monus_monus_cancel (ha : a ≠ ∞) (h : b ≤ a) : monus a (monus a b) = b :=
  ENNReal.monus_eq_of_eq_add_rev (monus_ne_top ha) (monus_add_cancel_of_le h).symm

theorem monus_right_inj (ha : a ≠ ∞) (hb : b ≤ a) (hc : c ≤ a) :
    monus a b = monus a c ↔ b = c := by
  refine ⟨fun h => ?_, congrArg (monus a)⟩
  simpa only [monus_monus_cancel ha hb, monus_monus_cancel ha hc] using congrArg (monus a) h

protected theorem monus_mul (h : 0 < b → b < a → c ≠ ∞) :
    monus a b * c = monus (a * c) (b * c) := by
  rcases le_or_gt a b with hab | hab
  · simp [monus_eq_zero_of_le hab, monus_eq_zero_of_le (mul_left_mono hab)]
  rcases eq_zero_or_pos b with rfl | hb
  · simp
  apply ENNReal.eq_monus_of_add_eq (mul_ne_top hab.ne_top (h hb hab))
  rw [← add_mul, monus_add_cancel_of_le hab.le]

protected theorem mul_monus (h : 0 < c → c < b → a ≠ ∞) :
    a * monus b c = monus (a * b) (a * c) := by
  simp only [mul_comm a]
  exact ENNReal.monus_mul h

theorem monus_le_monus_iff_left (h : c ≤ a) (ha : a ≠ ∞) :
    monus a b ≤ monus a c ↔ c ≤ b :=
  AddLECancellable.tsub_le_tsub_iff_left (α := WithTop ℝ≥0) (cancel_of_ne ha)
    (cancel_of_ne (ne_top_of_le_ne_top ha h)) h

theorem le_toReal_monus (hb : b ≠ ∞) : a.toReal - b.toReal ≤ (monus a b).toReal := by
  lift b to ℝ≥0 using hb
  induction a
  · simp
  · simp only [← coe_monus, NNReal.sub_def, Real.coe_toNNReal', coe_toReal]
    exact le_max_left _ _

@[simp] lemma toNNReal_monus (hb : b ≠ ∞) :
    (monus a b).toNNReal = a.toNNReal - b.toNNReal := by
  lift b to ℝ≥0 using hb
  induction a <;> simp [← coe_monus]

@[simp] lemma toReal_monus_of_le (hba : b ≤ a) (ha : a ≠ ∞) :
    (monus a b).toReal = a.toReal - b.toReal := by
  simp [ENNReal.toReal, ne_top_of_le_ne_top ha hba, toNNReal_mono ha hba]

theorem ofReal_monus (p : ℝ) {q : ℝ} (hq : 0 ≤ q) :
    ENNReal.ofReal (p - q) = monus (ENNReal.ofReal p) (ENNReal.ofReal q) := by
  obtain h | h := le_total p q
  · rw [ofReal_of_nonpos (sub_nonpos_of_le h), monus_eq_zero_of_le (ofReal_le_ofReal h)]
  refine ENNReal.eq_monus_of_add_eq ofReal_ne_top ?_
  rw [← ofReal_add (sub_nonneg_of_le h) hq, sub_add_cancel]

lemma monus_monus_monus_cancel_left (ha : a ≠ ∞) (h : b ≤ a) :
    monus (monus a c) (monus a b) = monus b c := by
  have hb : b ≠ ∞ := ne_top_of_le_ne_top ha h
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  cases c
  · simp
  · simp only [← coe_monus, coe_inj]
    apply tsub_tsub_tsub_cancel_left
    exact coe_le_coe.mp h

end Monus

section Interval

variable {x y : ℝ≥0∞} {ε ε₁ ε₂ : ℝ≥0∞}

protected theorem Ico_eq_Iio : Ico 0 y = Iio y :=
  Ico_bot

theorem mem_Iio_self_add : x ≠ ∞ → ε ≠ 0 → x ∈ Iio (x + ε) := fun xt ε0 => lt_add_right xt ε0

theorem mem_Ioo_self_monus_add : x ≠ ∞ → x ≠ 0 → ε₁ ≠ 0 → ε₂ ≠ 0 →
    x ∈ Ioo (monus x ε₁) (x + ε₂) :=
  fun xt x0 ε0 ε0' => ⟨ENNReal.monus_lt_self xt x0 ε0, lt_add_right xt ε0'⟩

@[simp]
theorem image_coe_Iic (x : ℝ≥0) : (↑) '' Iic x = Iic (x : ℝ≥0∞) := WithTop.image_coe_Iic

@[simp]
theorem image_coe_Ici (x : ℝ≥0) : (↑) '' Ici x = Ico ↑x ∞ := WithTop.image_coe_Ici

@[simp]
theorem image_coe_Iio (x : ℝ≥0) : (↑) '' Iio x = Iio (x : ℝ≥0∞) := WithTop.image_coe_Iio

@[simp]
theorem image_coe_Ioi (x : ℝ≥0) : (↑) '' Ioi x = Ioo ↑x ∞ := WithTop.image_coe_Ioi

@[simp]
theorem image_coe_Icc (x y : ℝ≥0) : (↑) '' Icc x y = Icc (x : ℝ≥0∞) y := WithTop.image_coe_Icc

@[simp]
theorem image_coe_Ico (x y : ℝ≥0) : (↑) '' Ico x y = Ico (x : ℝ≥0∞) y := WithTop.image_coe_Ico

@[simp]
theorem image_coe_Ioc (x y : ℝ≥0) : (↑) '' Ioc x y = Ioc (x : ℝ≥0∞) y := WithTop.image_coe_Ioc

@[simp]
theorem image_coe_Ioo (x y : ℝ≥0) : (↑) '' Ioo x y = Ioo (x : ℝ≥0∞) y := WithTop.image_coe_Ioo

@[simp]
theorem image_coe_uIcc (x y : ℝ≥0) : (↑) '' uIcc x y = uIcc (x : ℝ≥0∞) y := by simp [uIcc]

@[simp]
theorem image_coe_uIoc (x y : ℝ≥0) : (↑) '' uIoc x y = uIoc (x : ℝ≥0∞) y := by simp [uIoc]

@[simp]
theorem image_coe_uIoo (x y : ℝ≥0) : (↑) '' uIoo x y = uIoo (x : ℝ≥0∞) y := by simp [uIoo]

end Interval

section iInf

variable {ι : Sort*} {f g : ι → ℝ≥0∞}
variable {a b c d : ℝ≥0∞} {r : ℝ≥0}

theorem toNNReal_iInf (hf : ∀ i, f i ≠ ∞) : (iInf f).toNNReal = ⨅ i, (f i).toNNReal := by
  cases isEmpty_or_nonempty ι
  · rw [iInf_of_empty, toNNReal_top, NNReal.iInf_empty]
  · lift f to ι → ℝ≥0 using hf
    simp_rw [← coe_iInf, toNNReal_coe]

theorem toNNReal_sInf (s : Set ℝ≥0∞) (hs : ∀ r ∈ s, r ≠ ∞) :
    (sInf s).toNNReal = sInf (ENNReal.toNNReal '' s) := by
  have hf : ∀ i, ((↑) : s → ℝ≥0∞) i ≠ ∞ := fun ⟨r, rs⟩ => hs r rs
  simpa only [← sInf_range, ← image_eq_range, Subtype.range_coe_subtype] using! (toNNReal_iInf hf)

theorem toReal_iInf (hf : ∀ i, f i ≠ ∞) : (iInf f).toReal = ⨅ i, (f i).toReal := by
  simp only [ENNReal.toReal, toNNReal_iInf hf, NNReal.coe_iInf]

set_option backward.isDefEq.respectTransparency false in
theorem toReal_sInf (s : Set ℝ≥0∞) (hf : ∀ r ∈ s, r ≠ ∞) :
    (sInf s).toReal = sInf (ENNReal.toReal '' s) := by
  simp only [ENNReal.toReal, toNNReal_sInf s hf, NNReal.coe_sInf, Set.image_image]

@[simp] lemma ofReal_iInf [Nonempty ι] (f : ι → ℝ) :
    ENNReal.ofReal (⨅ i, f i) = ⨅ i, ENNReal.ofReal (f i) := by
  obtain ⟨i, hi⟩ | h := em (∃ i, f i ≤ 0)
  · rw [iInf_eq_bot.2 fun _ _ ↦ ⟨i, by simpa [ofReal_of_nonpos hi]⟩]
    simp [Real.iInf_nonpos' ⟨i, hi⟩]
  replace h i : 0 ≤ f i := le_of_not_ge fun hi ↦ h ⟨i, hi⟩
  refine eq_of_forall_le_iff fun a ↦ ?_
  obtain rfl | ha := eq_or_ne a ∞
  · simp
  rw [le_iInf_iff, le_ofReal_iff_toReal_le ha, le_ciInf_iff ⟨0, by simpa [mem_lowerBounds]⟩]
  · exact forall_congr' fun i ↦ (le_ofReal_iff_toReal_le ha (h _)).symm
  · exact Real.iInf_nonneg h

theorem iInf_add : iInf f + a = ⨅ i, f i + a :=
  le_antisymm (le_iInf fun i => add_le_add_left (iInf_le f i) a)
    (monus_le_iff.1 <| le_iInf fun i => monus_le_iff.2 <| iInf_le (fun j => f j + a) i)

theorem monus_iInf : monus a (iInf f) = ⨆ i, monus a (f i) := by
  refine eq_of_forall_ge_iff fun c => ?_
  rw [monus_le_iff, add_comm, iInf_add]
  simp [monus_le_iff, add_comm]

theorem sInf_add {s : Set ℝ≥0∞} : sInf s + a = ⨅ b ∈ s, b + a := by simp [sInf_eq_iInf, iInf_add]

theorem add_iInf {a : ℝ≥0∞} : a + iInf f = ⨅ b, a + f b := by
  rw [add_comm, iInf_add]; simp [add_comm]

theorem iInf_add_iInf (h : ∀ i j, ∃ k, f k + g k ≤ f i + g j) : iInf f + iInf g = ⨅ a, f a + g a :=
  suffices ⨅ a, f a + g a ≤ iInf f + iInf g from
    le_antisymm (le_iInf fun _ => add_le_add (iInf_le _ _) (iInf_le _ _)) this
  calc
    ⨅ a, f a + g a ≤ ⨅ (a) (a'), f a + g a' :=
      le_iInf₂ fun a a' => let ⟨k, h⟩ := h a a'; iInf_le_of_le k h
    _ = iInf f + iInf g := by simp_rw [iInf_add, add_iInf]

lemma iInf_add_iInf_of_monotone {ι : Type*} [Preorder ι] [IsCodirectedOrder ι] {f g : ι → ℝ≥0∞}
    (hf : Monotone f) (hg : Monotone g) : iInf f + iInf g = ⨅ a, f a + g a :=
  iInf_add_iInf fun i j ↦ (exists_le_le i j).imp fun _k ⟨hi, hj⟩ ↦ by gcongr <;> apply_rules

lemma add_iInf₂ {κ : ι → Sort*} (f : (i : ι) → κ i → ℝ≥0∞) :
    a + ⨅ (i) (j), f i j = ⨅ (i) (j), a + f i j := by
  simp [add_iInf]

lemma iInf₂_add {κ : ι → Sort*} (f : (i : ι) → κ i → ℝ≥0∞) :
    (⨅ (i) (j), f i j) + a = ⨅ (i) (j), f i j + a := by
  simp only [add_comm, add_iInf₂]

lemma add_sInf {s : Set ℝ≥0∞} : a + sInf s = ⨅ b ∈ s, a + b := by
  rw [sInf_eq_iInf, add_iInf₂]

variable {κ : Sort*}

lemma le_iInf_add_iInf {g : κ → ℝ≥0∞} (h : ∀ i j, a ≤ f i + g j) :
    a ≤ iInf f + iInf g := by
  simp_rw [iInf_add, add_iInf]; exact le_iInf₂ h

lemma le_iInf₂_add_iInf₂ {q₁ : ι → Sort*} {q₂ : κ → Sort*}
    {f : (i : ι) → q₁ i → ℝ≥0∞} {g : (k : κ) → q₂ k → ℝ≥0∞}
    (h : ∀ i pi k qk, a ≤ f i pi + g k qk) :
    a ≤ (⨅ (i) (qi), f i qi) + ⨅ (k) (qk), g k qk := by
  simp_rw [iInf₂_add, add_iInf₂]
  exact le_iInf₂ fun i hi => le_iInf₂ (h i hi)

@[simp] lemma iInf_gt_eq_self (a : ℝ≥0∞) : ⨅ b, ⨅ _ : a < b, b = a := by
  refine le_antisymm ?_ (le_iInf₂ fun b hb ↦ hb.le)
  refine le_of_forall_gt fun c hac ↦ ?_
  obtain ⟨d, had, hdc⟩ := exists_between hac
  exact (iInf₂_le_of_le d had le_rfl).trans_lt hdc

lemma exists_add_lt_of_add_lt {x y z : ℝ≥0∞} (h : y + z < x) :
    ∃ y' > y, ∃ z' > z, y' + z' < x := by
  contrapose! h
  simpa using le_iInf₂_add_iInf₂ h

end iInf

section iSup

variable {ι κ : Sort*} {f g : ι → ℝ≥0∞} {s : Set ℝ≥0∞} {a : ℝ≥0∞}

theorem toNNReal_iSup (hf : ∀ i, f i ≠ ∞) : (iSup f).toNNReal = ⨆ i, (f i).toNNReal := by
  lift f to ι → ℝ≥0 using hf
  simp_rw [toNNReal_coe]
  by_cases h : BddAbove (range f)
  · rw [← coe_iSup h, toNNReal_coe]
  · rw [NNReal.iSup_of_not_bddAbove h, iSup_coe_eq_top.2 h, toNNReal_top]

theorem toNNReal_sSup (s : Set ℝ≥0∞) (hs : ∀ r ∈ s, r ≠ ∞) :
    (sSup s).toNNReal = sSup (ENNReal.toNNReal '' s) := by
  have hf : ∀ i, ((↑) : s → ℝ≥0∞) i ≠ ∞ := fun ⟨r, rs⟩ => hs r rs
  simpa only [← sSup_range, ← image_eq_range, Subtype.range_coe_subtype] using! (toNNReal_iSup hf)

theorem toReal_iSup (hf : ∀ i, f i ≠ ∞) : (iSup f).toReal = ⨆ i, (f i).toReal := by
  simp only [ENNReal.toReal, toNNReal_iSup hf, NNReal.coe_iSup]

set_option backward.isDefEq.respectTransparency false in
theorem toReal_sSup (s : Set ℝ≥0∞) (hf : ∀ r ∈ s, r ≠ ∞) :
    (sSup s).toReal = sSup (ENNReal.toReal '' s) := by
  simp only [ENNReal.toReal, toNNReal_sSup s hf, NNReal.coe_sSup, Set.image_image]

theorem iSup_monus : monus (iSup f) a = ⨆ i, monus (f i) a := by
  refine eq_of_forall_ge_iff fun q => ?_
  simp only [monus_le_iff, iSup_le_iff]

@[simp] lemma iSup_eq_zero : ⨆ i, f i = 0 ↔ ∀ i, f i = 0 := iSup_eq_bot

@[simp] lemma iSup_zero : ⨆ _ : ι, (0 : ℝ≥0∞) = 0 := by simp

lemma iSup_natCast : ⨆ n : ℕ, (n : ℝ≥0∞) = ∞ :=
  iSup_eq_top.2 fun _b hb => ENNReal.exists_nat_gt (lt_top_iff_ne_top.1 hb)

lemma add_iSup [Nonempty ι] (f : ι → ℝ≥0∞) : a + ⨆ i, f i = ⨆ i, a + f i := by
  obtain rfl | ha := eq_or_ne a ∞
  · simp
  refine le_antisymm ?_ (iSup_le fun i => add_le_add_right (le_iSup f i) a)
  have h : a ≤ ⨆ i, a + f i :=
    le_iSup_of_le (Classical.arbitrary ι) le_self_add
  apply (le_monus_iff_add_le_left ha h).1
  exact iSup_le fun i => le_monus_of_add_le_left ha (le_iSup (fun j => a + f j) i)

lemma iSup_add [Nonempty ι] (f : ι → ℝ≥0∞) : (⨆ i, f i) + a = ⨆ i, f i + a := by
  simp [add_comm, add_iSup]

lemma add_biSup' {p : ι → Prop} (h : ∃ i, p i) (f : ι → ℝ≥0∞) :
    a + ⨆ i, ⨆ _ : p i, f i = ⨆ i, ⨆ _ : p i, a + f i := by
  have : Nonempty {i // p i} := nonempty_subtype.2 h
  simp only [iSup_subtype', add_iSup]

lemma biSup_add' {p : ι → Prop} (h : ∃ i, p i) (f : ι → ℝ≥0∞) :
    (⨆ i, ⨆ _ : p i, f i) + a = ⨆ i, ⨆ _ : p i, f i + a := by simp only [add_comm, add_biSup' h]

lemma add_biSup {ι : Type*} {s : Set ι} (hs : s.Nonempty) (f : ι → ℝ≥0∞) :
    a + ⨆ i ∈ s, f i = ⨆ i ∈ s, a + f i := add_biSup' hs _

lemma biSup_add {ι : Type*} {s : Set ι} (hs : s.Nonempty) (f : ι → ℝ≥0∞) :
    (⨆ i ∈ s, f i) + a = ⨆ i ∈ s, f i + a := biSup_add' hs _

lemma add_sSup (hs : s.Nonempty) : a + sSup s = ⨆ b ∈ s, a + b := by
  rw [sSup_eq_iSup, add_biSup hs]

lemma sSup_add (hs : s.Nonempty) : sSup s + a = ⨆ b ∈ s, b + a := by
  rw [sSup_eq_iSup, biSup_add hs]

lemma iSup_add_iSup_le [Nonempty ι] [Nonempty κ] {g : κ → ℝ≥0∞} (h : ∀ i j, f i + g j ≤ a) :
    iSup f + iSup g ≤ a := by simp_rw [iSup_add, add_iSup]; exact iSup₂_le h

lemma biSup_add_biSup_le' {p : ι → Prop} {q : κ → Prop} (hp : ∃ i, p i) (hq : ∃ j, q j)
    {g : κ → ℝ≥0∞} (h : ∀ i, p i → ∀ j, q j → f i + g j ≤ a) :
    (⨆ i, ⨆ _ : p i, f i) + ⨆ j, ⨆ _ : q j, g j ≤ a := by
  simp_rw [biSup_add' hp, add_biSup' hq]
  exact iSup₂_le fun i hi => iSup₂_le (h i hi)

lemma biSup_add_biSup_le {ι κ : Type*} {s : Set ι} {t : Set κ} (hs : s.Nonempty) (ht : t.Nonempty)
    {f : ι → ℝ≥0∞} {g : κ → ℝ≥0∞} {a : ℝ≥0∞} (h : ∀ i ∈ s, ∀ j ∈ t, f i + g j ≤ a) :
    (⨆ i ∈ s, f i) + ⨆ j ∈ t, g j ≤ a := biSup_add_biSup_le' hs ht h

lemma iSup_add_iSup (h : ∀ i j, ∃ k, f i + g j ≤ f k + g k) : iSup f + iSup g = ⨆ i, f i + g i := by
  cases isEmpty_or_nonempty ι
  · simp
  · refine le_antisymm ?_ (iSup_le fun a => add_le_add (le_iSup _ _) (le_iSup _ _))
    refine iSup_add_iSup_le fun i j => ?_
    rcases h i j with ⟨k, hk⟩
    exact le_iSup_of_le k hk

lemma iSup_add_iSup_of_monotone {ι : Type*} [Preorder ι] [IsDirectedOrder ι] {f g : ι → ℝ≥0∞}
    (hf : Monotone f) (hg : Monotone g) : iSup f + iSup g = ⨆ a, f a + g a :=
  iSup_add_iSup fun i j ↦ (exists_ge_ge i j).imp fun _k ⟨hi, hj⟩ ↦ by gcongr <;> apply_rules

lemma monus_iSup [Nonempty ι] (ha : a ≠ ∞) :
    monus a (iSup f) = ⨅ i, monus a (f i) := by
  refine le_antisymm (le_iInf fun i => monus_le_monus le_rfl (le_iSup f i)) ?_
  by_cases h : ∃ i, a < f i
  · obtain ⟨i, hi⟩ := h
    exact (iInf_le (fun j => monus a (f j)) i).trans
      ((monus_eq_zero_of_le hi.le).le.trans zero_le)
  simp only [not_exists, not_lt] at h
  let q := ⨅ i, monus a (f i)
  have hqa : q ≤ a :=
    (iInf_le (fun i => monus a (f i)) (Classical.arbitrary ι)).trans monus_le_self
  have hsum : iSup f ≤ monus a q := by
    refine iSup_le fun i => ?_
    calc
      f i = monus a (monus a (f i)) := (monus_monus_cancel ha (h i)).symm
      _ ≤ monus a q := monus_le_monus le_rfl (iInf_le _ i)
  exact le_monus_of_add_le_left (ne_top_of_le_ne_top ha (iSup_le h))
    ((le_monus_iff_add_le_right (ne_top_of_le_ne_top ha hqa) hqa).1 hsum)

@[simp] lemma iSup_lt_eq_self (a : ℝ≥0∞) : ⨆ b, ⨆ _ : b < a, b = a := by
  refine le_antisymm (iSup₂_le fun b hb ↦ hb.le) ?_
  refine le_of_forall_lt fun c hca ↦ ?_
  obtain ⟨d, hcd, hdb⟩ := exists_between hca
  exact hcd.trans_le <| le_iSup₂_of_le d hdb le_rfl

-- TODO: Prove the two one-side versions
lemma exists_lt_add_of_lt_add {x y z : ℝ≥0∞} (h : x < y + z) (hy : y ≠ 0) (hz : z ≠ 0) :
    ∃ y' < y, ∃ z' < z, x < y' + z' := by
  contrapose! h
  simpa using biSup_add_biSup_le' (by exact ⟨0, hy.bot_lt⟩) (by exact ⟨0, hz.bot_lt⟩) h

end iSup

end ENNReal
