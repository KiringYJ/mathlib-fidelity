/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Yuyang Zhao
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Tactic.Bound.Attribute
public import Mathlib.Tactic.Monotonicity.Attr

import Mathlib.Data.Set.Function
public import Mathlib.Data.Int.Order.Basic

/-!
# Lemmas on the monotone multiplication typeclasses

This file builds on `Mathlib/Algebra/Order/GroupWithZero/Unbundled/Defs.lean` by proving several
lemmas that do not immediately follow from the typeclass specifications.
-/

public section

open Function

variable {α M₀ G₀ : Type*}

section MulZeroClass

variable [MulZeroClass α] {a b c d : α}

section Preorder

variable [Preorder α]

/-- Assumes left covariance. -/
theorem Left.mul_pos [PosMulStrictMono α] (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  simpa only [mul_zero] using mul_lt_mul_of_pos_left hb ha

alias mul_pos := Left.mul_pos

theorem mul_neg_of_pos_of_neg [PosMulStrictMono α] (ha : 0 < a) (hb : b < 0) : a * b < 0 := by
  simpa only [mul_zero] using mul_lt_mul_of_pos_left hb ha

@[simp]
theorem mul_pos_iff_of_pos_left [PosMulStrictMono α] [PosMulReflectLT α] (h : 0 < a) :
    0 < a * b ↔ 0 < b := by simpa using mul_lt_mul_iff_right₀ (b := 0) h

/-- Assumes right covariance. -/
theorem Right.mul_pos [MulPosStrictMono α] (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  simpa only [zero_mul] using mul_lt_mul_of_pos_right ha hb

theorem mul_neg_of_neg_of_pos [MulPosStrictMono α] (ha : a < 0) (hb : 0 < b) : a * b < 0 := by
  simpa only [zero_mul] using mul_lt_mul_of_pos_right ha hb

@[simp]
theorem mul_pos_iff_of_pos_right [MulPosStrictMono α] [MulPosReflectLT α] (h : 0 < b) :
    0 < a * b ↔ 0 < a := by simpa using mul_lt_mul_iff_left₀ (b := 0) h

/-- Assumes left covariance. -/
theorem Left.mul_nonneg [PosMulMono α] (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  simpa only [mul_zero] using mul_le_mul_of_nonneg_left hb ha

alias mul_nonneg := Left.mul_nonneg

theorem mul_nonpos_of_nonneg_of_nonpos [PosMulMono α] (ha : 0 ≤ a) (hb : b ≤ 0) : a * b ≤ 0 := by
  simpa only [mul_zero] using mul_le_mul_of_nonneg_left hb ha

/-- Assumes right covariance. -/
theorem Right.mul_nonneg [MulPosMono α] (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  simpa only [zero_mul] using mul_le_mul_of_nonneg_right ha hb

theorem mul_nonpos_of_nonpos_of_nonneg [MulPosMono α] (ha : a ≤ 0) (hb : 0 ≤ b) : a * b ≤ 0 := by
  simpa only [zero_mul] using mul_le_mul_of_nonneg_right ha hb

theorem pos_of_mul_pos_right [PosMulReflectLT α] (h : 0 < a * b) (ha : 0 ≤ a) : 0 < b :=
  lt_of_mul_lt_mul_left ((mul_zero a).symm ▸ h : a * 0 < a * b) ha

theorem pos_of_mul_pos_left [MulPosReflectLT α] (h : 0 < a * b) (hb : 0 ≤ b) : 0 < a :=
  lt_of_mul_lt_mul_right ((zero_mul b).symm ▸ h : 0 * b < a * b) hb

theorem pos_iff_pos_of_mul_pos [PosMulReflectLT α] [MulPosReflectLT α] (hab : 0 < a * b) :
    0 < a ↔ 0 < b :=
  ⟨pos_of_mul_pos_right hab ∘ le_of_lt, pos_of_mul_pos_left hab ∘ le_of_lt⟩

/-- Assumes left strict covariance. -/
theorem Left.mul_lt_mul_of_nonneg [PosMulStrictMono α] [MulPosMono α]
    (h₁ : a < b) (h₂ : c < d) (a0 : 0 ≤ a) (c0 : 0 ≤ c) : a * c < b * d :=
  mul_lt_mul_of_le_of_lt_of_nonneg_of_pos h₁.le h₂ c0 (a0.trans_lt h₁)

/-- Assumes right strict covariance. -/
theorem Right.mul_lt_mul_of_nonneg [PosMulMono α] [MulPosStrictMono α]
    (h₁ : a < b) (h₂ : c < d) (a0 : 0 ≤ a) (c0 : 0 ≤ c) : a * c < b * d :=
  mul_lt_mul_of_lt_of_le_of_nonneg_of_pos h₁ h₂.le a0 (c0.trans_lt h₂)

alias mul_lt_mul_of_nonneg := Left.mul_lt_mul_of_nonneg

alias mul_lt_mul'' := Left.mul_lt_mul_of_nonneg
attribute [gcongr] mul_lt_mul''

theorem mul_self_le_mul_self [PosMulMono α] [MulPosMono α] (ha : 0 ≤ a) (hab : a ≤ b) :
    a * a ≤ b * b :=
  mul_le_mul hab hab ha <| ha.trans hab

end Preorder

section PartialOrder

/-- Local notation for the positive elements of a type `α`. -/
local notation3 "α>0" => { x : α // 0 < x }

variable [PartialOrder α]

theorem posMulMono_iff_covariant_pos :
    PosMulMono α ↔ CovariantClass α>0 α (fun x y => x * y) (· ≤ ·) where
  mp _ := PosMulMono.to_covariantClass_pos_mul_le
  mpr h :=
    { mul_le_mul_of_nonneg_left a ha b c hbc := by
        obtain ha | ha := ha.eq_or_lt
        · simp [← ha]
        · exact @CovariantClass.elim α>0 α (fun x y => x * y) (· ≤ ·) _ ⟨_, ha⟩ _ _ hbc }

theorem mulPosMono_iff_covariant_pos :
    MulPosMono α ↔ CovariantClass α>0 α (fun x y => y * x) (· ≤ ·) where
  mp _ := MulPosMono.to_covariantClass_pos_mul_le
  mpr h :=
    { mul_le_mul_of_nonneg_right a ha b c hbc := by
        obtain ha | ha := ha.eq_or_lt
        · simp [← ha]
        · exact @CovariantClass.elim α>0 α (fun x y => y * x) (· ≤ ·) _ ⟨_, ha⟩ _ _ hbc }

theorem posMulReflectLT_iff_contravariant_pos :
    PosMulReflectLT α ↔ ContravariantClass α>0 α (fun x y => x * y) (· < ·) :=
  ⟨@PosMulReflectLT.to_contravariantClass_pos_mul_lt _ _ _ _, fun h =>
    { elim a b c h := by
        obtain ha | ha := a.prop.eq_or_lt
        · simp [← ha] at h
        · exact @ContravariantClass.elim α>0 α (fun x y => x * y) (· < ·) _ ⟨_, ha⟩ _ _ h }⟩

theorem mulPosReflectLT_iff_contravariant_pos :
    MulPosReflectLT α ↔ ContravariantClass α>0 α (fun x y => y * x) (· < ·) :=
  ⟨@MulPosReflectLT.to_contravariantClass_pos_mul_lt _ _ _ _, fun h =>
    { elim a b c h := by
        obtain ha | ha := a.prop.eq_or_lt
        · simp [← ha] at h
        · exact @ContravariantClass.elim α>0 α (fun x y => y * x) (· < ·) _ ⟨_, ha⟩ _ _ h }⟩

-- see Note [lower instance priority]
instance (priority := 100) PosMulStrictMono.toPosMulMono [PosMulStrictMono α] : PosMulMono α :=
  posMulMono_iff_covariant_pos.2 (covariantClass_le_of_lt _ _ _)

-- see Note [lower instance priority]
instance (priority := 100) MulPosStrictMono.toMulPosMono [MulPosStrictMono α] : MulPosMono α :=
  mulPosMono_iff_covariant_pos.2 (covariantClass_le_of_lt _ _ _)

-- see Note [lower instance priority]
instance (priority := 100) PosMulReflectLE.toPosMulReflectLT [PosMulReflectLE α] :
    PosMulReflectLT α :=
  posMulReflectLT_iff_contravariant_pos.2
    ⟨fun a b c h =>
      (le_of_mul_le_mul_of_pos_left h.le a.2).lt_of_ne <| by
        rintro rfl
        simp at h⟩

-- see Note [lower instance priority]
instance (priority := 100) MulPosReflectLE.toMulPosReflectLT [MulPosReflectLE α] :
    MulPosReflectLT α :=
  mulPosReflectLT_iff_contravariant_pos.2
    ⟨fun a b c h =>
      (le_of_mul_le_mul_of_pos_right h.le a.2).lt_of_ne <| by
        rintro rfl
        simp at h⟩

theorem mul_left_cancel_iff_of_pos [PosMulReflectLE α] (a0 : 0 < a) : a * b = a * c ↔ b = c :=
  ⟨fun h => (le_of_mul_le_mul_of_pos_left h.le a0).antisymm <|
    le_of_mul_le_mul_of_pos_left h.ge a0, congr_arg _⟩

theorem mul_right_cancel_iff_of_pos [MulPosReflectLE α] (b0 : 0 < b) : a * b = c * b ↔ a = c :=
  ⟨fun h => (le_of_mul_le_mul_of_pos_right h.le b0).antisymm <|
    le_of_mul_le_mul_of_pos_right h.ge b0, congr_arg (· * b)⟩

theorem mul_eq_mul_iff_eq_and_eq_of_pos [PosMulStrictMono α] [MulPosStrictMono α]
    (hab : a ≤ b) (hcd : c ≤ d) (a0 : 0 < a) (d0 : 0 < d) :
    a * c = b * d ↔ a = b ∧ c = d := by
  refine ⟨fun h ↦ ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  simp only [eq_iff_le_not_lt, hab, hcd, true_and]
  refine ⟨fun hab ↦ h.not_lt ?_, fun hcd ↦ h.not_lt ?_⟩
  · exact (mul_le_mul_of_nonneg_left hcd a0.le).trans_lt (mul_lt_mul_of_pos_right hab d0)
  · exact (mul_lt_mul_of_pos_left hcd a0).trans_le (mul_le_mul_of_nonneg_right hab d0.le)

theorem mul_eq_mul_iff_eq_and_eq_of_pos' [PosMulStrictMono α] [MulPosStrictMono α]
    (hab : a ≤ b) (hcd : c ≤ d) (b0 : 0 < b) (c0 : 0 < c) :
    a * c = b * d ↔ a = b ∧ c = d := by
  refine ⟨fun h ↦ ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  simp only [eq_iff_le_not_lt, hab, hcd, true_and]
  refine ⟨fun hab ↦ h.not_lt ?_, fun hcd ↦ h.not_lt ?_⟩
  · exact (mul_lt_mul_of_pos_right hab c0).trans_le (mul_le_mul_of_nonneg_left hcd b0.le)
  · exact (mul_le_mul_of_nonneg_right hab c0.le).trans_lt (mul_lt_mul_of_pos_left hcd b0)

theorem eq_and_eq_of_pos_of_le_of_mul_le_mul [PosMulReflectLE α] [MulPosReflectLE α]
    [PosMulMono α] [MulPosMono α] (ha : 0 < a) (hc : 0 < c) (hab : a ≤ b) (hcd : c ≤ d)
    (h : b * d ≤ a * c) : a = b ∧ c = d := by
  refine ⟨le_antisymm hab ?_, le_antisymm hcd ?_⟩
  · grw [hcd] at h
    · exact le_of_mul_le_mul_of_pos_right h <| hc.trans_le hcd
    · exact ha.le
  · grw [hab] at h
    · exact le_of_mul_le_mul_of_pos_left h <| ha.trans_le hab
    · exact hc.le

theorem PosMulMono.toPosMulStrictMono [IsLeftCancelMulZero α] [PosMulMono α] :
    PosMulStrictMono α where
  mul_lt_mul_of_pos_left _a ha _b _c hbc :=
    (mul_le_mul_of_nonneg_left hbc.le ha.le).lt_of_ne (hbc.ne ∘ mul_left_cancel₀ ha.ne')

theorem posMulMono_iff_posMulStrictMono [IsLeftCancelMulZero α] :
    PosMulMono α ↔ PosMulStrictMono α :=
  ⟨(·.toPosMulStrictMono), (·.toPosMulMono)⟩

theorem MulPosMono.toMulPosStrictMono [IsRightCancelMulZero α] [MulPosMono α] :
    MulPosStrictMono α where
  mul_lt_mul_of_pos_right _a ha _b _c hbc :=
    (mul_le_mul_of_nonneg_right hbc.le ha.le).lt_of_ne (hbc.ne ∘ mul_right_cancel₀ ha.ne')

theorem mulPosMono_iff_mulPosStrictMono [IsRightCancelMulZero α] :
    MulPosMono α ↔ MulPosStrictMono α :=
  ⟨(·.toMulPosStrictMono), (·.toMulPosMono)⟩

theorem PosMulReflectLT.toPosMulReflectLE [IsLeftCancelMulZero α] [PosMulReflectLT α] :
    PosMulReflectLE α where
  elim := fun x _ _ h =>
    h.eq_or_lt.elim (le_of_eq ∘ mul_left_cancel₀ x.2.ne.symm) fun h' =>
      (lt_of_mul_lt_mul_left h' x.2.le).le

theorem posMulReflectLE_iff_posMulReflectLT [IsLeftCancelMulZero α] :
    PosMulReflectLE α ↔ PosMulReflectLT α :=
  ⟨(·.toPosMulReflectLT), (·.toPosMulReflectLE)⟩

theorem MulPosReflectLT.toMulPosReflectLE [IsRightCancelMulZero α] [MulPosReflectLT α] :
    MulPosReflectLE α where
  elim := fun x _ _ h => h.eq_or_lt.elim (le_of_eq ∘ mul_right_cancel₀ x.2.ne.symm) fun h' =>
    (lt_of_mul_lt_mul_right h' x.2.le).le

theorem mulPosReflectLE_iff_mulPosReflectLT [IsRightCancelMulZero α] :
    MulPosReflectLE α ↔ MulPosReflectLT α :=
  ⟨(·.toMulPosReflectLT), (·.toMulPosReflectLE)⟩

end PartialOrder

section LinearOrder

variable [LinearOrder α]

theorem pos_and_pos_or_neg_and_neg_of_mul_pos [PosMulMono α] [MulPosMono α] (hab : 0 < a * b) :
    0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 := by
  rcases lt_trichotomy a 0 with (ha | rfl | ha)
  · refine Or.inr ⟨ha, lt_imp_lt_of_le_imp_le (fun hb => ?_) hab⟩
    exact mul_nonpos_of_nonpos_of_nonneg ha.le hb
  · rw [zero_mul] at hab
    exact hab.false.elim
  · refine Or.inl ⟨ha, lt_imp_lt_of_le_imp_le (fun hb => ?_) hab⟩
    exact mul_nonpos_of_nonneg_of_nonpos ha.le hb

theorem neg_of_mul_pos_right [PosMulMono α] [MulPosMono α] (h : 0 < a * b) (ha : a ≤ 0) : b < 0 :=
  ((pos_and_pos_or_neg_and_neg_of_mul_pos h).resolve_left fun h => h.1.not_ge ha).2

theorem neg_of_mul_pos_left [PosMulMono α] [MulPosMono α] (h : 0 < a * b) (ha : b ≤ 0) : a < 0 :=
  ((pos_and_pos_or_neg_and_neg_of_mul_pos h).resolve_left fun h => h.2.not_ge ha).1

theorem neg_iff_neg_of_mul_pos [PosMulMono α] [MulPosMono α] (hab : 0 < a * b) : a < 0 ↔ b < 0 :=
  ⟨neg_of_mul_pos_right hab ∘ le_of_lt, neg_of_mul_pos_left hab ∘ le_of_lt⟩

theorem Left.neg_of_mul_neg_right [PosMulMono α] (h : a * b < 0) (a0 : 0 ≤ a) : b < 0 :=
  lt_of_not_ge fun b0 : b ≥ 0 => (Left.mul_nonneg a0 b0).not_gt h

alias neg_of_mul_neg_right := Left.neg_of_mul_neg_right

theorem Right.neg_of_mul_neg_right [MulPosMono α] (h : a * b < 0) (a0 : 0 ≤ a) : b < 0 :=
  lt_of_not_ge fun b0 : b ≥ 0 => (Right.mul_nonneg a0 b0).not_gt h

theorem Left.neg_of_mul_neg_left [PosMulMono α] (h : a * b < 0) (b0 : 0 ≤ b) : a < 0 :=
  lt_of_not_ge fun a0 : a ≥ 0 => (Left.mul_nonneg a0 b0).not_gt h

alias neg_of_mul_neg_left := Left.neg_of_mul_neg_left

theorem Right.neg_of_mul_neg_left [MulPosMono α] (h : a * b < 0) (b0 : 0 ≤ b) : a < 0 :=
  lt_of_not_ge fun a0 : a ≥ 0 => (Right.mul_nonneg a0 b0).not_gt h

end LinearOrder

end MulZeroClass

section MulOneClass

variable [MulOneClass α] [Zero α] {a b : α}

section Preorder

variable [Preorder α]

/-! Lemmas of the form `a ≤ a * b ↔ 1 ≤ b` and `a * b ≤ a ↔ b ≤ 1`, assuming left covariance. -/

lemma one_lt_of_lt_mul_left₀ [PosMulReflectLT α] (ha : 0 ≤ a) (h : a < a * b) : 1 < b :=
  lt_of_mul_lt_mul_left (by simpa) ha

lemma one_lt_of_lt_mul_right₀ [MulPosReflectLT α] (hb : 0 ≤ b) (h : b < a * b) : 1 < a :=
  lt_of_mul_lt_mul_right (by simpa) hb

lemma one_le_of_le_mul_left₀ [PosMulReflectLE α] (ha : 0 < a) (h : a ≤ a * b) : 1 ≤ b :=
  le_of_mul_le_mul_left (by simpa) ha

lemma one_le_of_le_mul_right₀ [MulPosReflectLE α] (hb : 0 < b) (h : b ≤ a * b) : 1 ≤ a :=
  le_of_mul_le_mul_right (by simpa) hb

@[simp]
lemma le_mul_iff_one_le_right [PosMulMono α] [PosMulReflectLE α] (a0 : 0 < a) : a ≤ a * b ↔ 1 ≤ b :=
  Iff.trans (by rw [mul_one]) (mul_le_mul_iff_right₀ a0)

@[simp]
theorem lt_mul_iff_one_lt_right [PosMulStrictMono α] [PosMulReflectLT α] (a0 : 0 < a) :
    a < a * b ↔ 1 < b :=
  Iff.trans (by rw [mul_one]) (mul_lt_mul_iff_right₀ a0)

@[simp]
lemma mul_le_iff_le_one_right [PosMulMono α] [PosMulReflectLE α] (a0 : 0 < a) : a * b ≤ a ↔ b ≤ 1 :=
  Iff.trans (by rw [mul_one]) (mul_le_mul_iff_right₀ a0)

@[simp]
theorem mul_lt_iff_lt_one_right [PosMulStrictMono α] [PosMulReflectLT α] (a0 : 0 < a) :
    a * b < a ↔ b < 1 :=
  Iff.trans (by rw [mul_one]) (mul_lt_mul_iff_right₀ a0)

/-! Lemmas of the form `a ≤ b * a ↔ 1 ≤ b` and `a * b ≤ b ↔ a ≤ 1`, assuming right covariance. -/

@[simp]
lemma le_mul_iff_one_le_left [MulPosMono α] [MulPosReflectLE α] (a0 : 0 < a) : a ≤ b * a ↔ 1 ≤ b :=
  Iff.trans (by rw [one_mul]) (mul_le_mul_iff_left₀ a0)

@[simp]
theorem lt_mul_iff_one_lt_left [MulPosStrictMono α] [MulPosReflectLT α] (a0 : 0 < a) :
    a < b * a ↔ 1 < b :=
  Iff.trans (by rw [one_mul]) (mul_lt_mul_iff_left₀ a0)

@[simp]
lemma mul_le_iff_le_one_left [MulPosMono α] [MulPosReflectLE α] (b0 : 0 < b) : a * b ≤ b ↔ a ≤ 1 :=
  Iff.trans (by rw [one_mul]) (mul_le_mul_iff_left₀ b0)

@[simp]
theorem mul_lt_iff_lt_one_left [MulPosStrictMono α] [MulPosReflectLT α] (b0 : 0 < b) :
    a * b < b ↔ a < 1 :=
  Iff.trans (by rw [one_mul]) (mul_lt_mul_iff_left₀ b0)

/-! Lemmas of the form `1 ≤ b → a ≤ a * b`.

Variants with `< 0` and `≤ 0` instead of `0 <` and `0 ≤` appear in `Mathlib/Algebra/Order/Ring/Defs`
(which imports this file) as they need additional results which are not yet available here. -/

theorem mul_le_of_le_one_left [MulPosMono α] (hb : 0 ≤ b) (h : a ≤ 1) : a * b ≤ b := by
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h hb

theorem le_mul_of_one_le_left [MulPosMono α] (hb : 0 ≤ b) (h : 1 ≤ a) : b ≤ a * b := by
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h hb

theorem mul_le_of_le_one_right [PosMulMono α] (ha : 0 ≤ a) (h : b ≤ 1) : a * b ≤ a := by
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h ha

theorem le_mul_of_one_le_right [PosMulMono α] (ha : 0 ≤ a) (h : 1 ≤ b) : a ≤ a * b := by
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h ha

theorem mul_lt_of_lt_one_left [MulPosStrictMono α] (hb : 0 < b) (h : a < 1) : a * b < b := by
  simpa only [one_mul] using mul_lt_mul_of_pos_right h hb

theorem lt_mul_of_one_lt_left [MulPosStrictMono α] (hb : 0 < b) (h : 1 < a) : b < a * b := by
  simpa only [one_mul] using mul_lt_mul_of_pos_right h hb

theorem mul_lt_of_lt_one_right [PosMulStrictMono α] (ha : 0 < a) (h : b < 1) : a * b < a := by
  simpa only [mul_one] using mul_lt_mul_of_pos_left h ha

theorem lt_mul_of_one_lt_right [PosMulStrictMono α] (ha : 0 < a) (h : 1 < b) : a < a * b := by
  simpa only [mul_one] using mul_lt_mul_of_pos_left h ha

end Preorder

end MulOneClass

section MulZero

variable [Mul M₀] [Zero M₀] [Preorder M₀] [Preorder α] {f g : α → M₀}

lemma Monotone.mul [PosMulMono M₀] [MulPosMono M₀] (hf : Monotone f) (hg : Monotone g)
    (hf₀ : ∀ x, 0 ≤ f x) (hg₀ : ∀ x, 0 ≤ g x) : Monotone (f * g) :=
  fun _ _ h ↦ mul_le_mul (hf h) (hg h) (hg₀ _) (hf₀ _)

lemma MonotoneOn.mul [PosMulMono M₀] [MulPosMono M₀] {s : Set α} (hf : MonotoneOn f s)
    (hg : MonotoneOn g s) (hf₀ : ∀ x ∈ s, 0 ≤ f x) (hg₀ : ∀ x ∈ s, 0 ≤ g x) :
    MonotoneOn (f * g) s :=
  fun _ ha _ hb h ↦ mul_le_mul (hf ha hb h) (hg ha hb h) (hg₀ _ ha) (hf₀ _ hb)

end MulZero

section MonoidWithZero
variable [MonoidWithZero M₀]

section Preorder
variable [Preorder M₀] {a b : M₀} {m n : ℕ}

@[simp] lemma pow_succ_nonneg [PosMulMono M₀] (ha : 0 ≤ a) : ∀ n, 0 ≤ a ^ (n + 1)
  | 0 => (pow_one a).symm ▸ ha
  | _ + 1 => pow_succ a _ ▸ mul_nonneg (pow_succ_nonneg ha _) ha

@[simp] lemma pow_nonneg [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 0 ≤ a) : ∀ n, 0 ≤ a ^ n
  | 0 => pow_zero a ▸ zero_le_one
  | n + 1 => pow_succ a n ▸ mul_nonneg (pow_nonneg ha _) ha

lemma zero_pow_le_one [ZeroLEOneClass M₀] : ∀ n : ℕ, (0 : M₀) ^ n ≤ 1
  | 0 => (pow_zero _).le
  | n + 1 => by rw [zero_pow n.succ_ne_zero]; exact zero_le_one

lemma pow_right_anti₀ [PosMulMono M₀] (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) : Antitone (fun n : ℕ ↦ a ^ n) :=
  antitone_nat_of_succ_le fun n ↦ by
    have : ZeroLEOneClass M₀ := ⟨ha₀.trans ha₁⟩
    rw [← mul_one (a ^ n), pow_succ]
    gcongr
    exact pow_nonneg ha₀ n

lemma pow_le_pow_of_le_one [PosMulMono M₀] (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) {m n : ℕ}
    (hmn : m ≤ n) : a ^ n ≤ a ^ m := pow_right_anti₀ ha₀ ha₁ hmn

lemma pow_le_of_le_one [PosMulMono M₀] (h₀ : 0 ≤ a) (h₁ : a ≤ 1) (hn : n ≠ 0) : a ^ n ≤ a :=
  (pow_one a).subst (pow_le_pow_of_le_one h₀ h₁ (Nat.pos_of_ne_zero hn))

lemma sq_le [PosMulMono M₀] (h₀ : 0 ≤ a) (h₁ : a ≤ 1) : a ^ 2 ≤ a :=
  pow_le_of_le_one h₀ h₁ two_ne_zero

lemma pow_le_one₀ [PosMulMono M₀] {n : ℕ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) : a ^ n ≤ 1 :=
  pow_zero a ▸ pow_right_anti₀ ha₀ ha₁ (Nat.zero_le n)

lemma one_le_mul_of_one_le_of_one_le [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (1 : M₀) ≤ a * b := ha.trans <| le_mul_of_one_le_right (zero_le_one.trans ha) hb

lemma one_lt_mul_of_le_of_lt [ZeroLEOneClass M₀] [MulPosMono M₀] (ha : 1 ≤ a) (hb : 1 < b) :
    1 < a * b := hb.trans_le <| le_mul_of_one_le_left (zero_le_one.trans hb.le) ha

lemma one_lt_mul_of_lt_of_le [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 < a) (hb : 1 ≤ b) :
    1 < a * b := ha.trans_le <| le_mul_of_one_le_right (zero_le_one.trans ha.le) hb

alias one_lt_mul := one_lt_mul_of_le_of_lt

@[deprecated "No replacement, use constituent lemmas from proof." (since := "2026-07-28")]
lemma mul_lt_one_of_nonneg_of_lt_one_left [PosMulMono M₀] (ha₀ : 0 ≤ a) (ha : a < 1) (hb : b ≤ 1) :
    a * b < 1 := (mul_le_of_le_one_right ha₀ hb).trans_lt ha

@[deprecated "No replacement, use constituent lemmas from proof." (since := "2026-07-28")]
lemma mul_lt_one_of_nonneg_of_lt_one_right [MulPosMono M₀] (ha : a ≤ 1) (hb₀ : 0 ≤ b) (hb : b < 1) :
    a * b < 1 := (mul_le_of_le_one_left hb₀ ha).trans_lt hb

@[bound]
protected lemma Bound.one_lt_mul [ZeroLEOneClass M₀] [PosMulMono M₀] [MulPosMono M₀] :
    1 ≤ a ∧ 1 < b ∨ 1 < a ∧ 1 ≤ b → 1 < a * b := by
  rintro (⟨ha, hb⟩ | ⟨ha, hb⟩); exacts [one_lt_mul ha hb, one_lt_mul_of_lt_of_le ha hb]

@[bound]
protected lemma Bound.mul_le_one [PosMulMono M₀] [MulPosMono M₀] (ha : a ≤ 1) (hb : b ≤ 1) :
    0 ≤ a ∨ 0 ≤ b → a * b ≤ 1 := by
  rintro (ha₀ | hb₀)
  exacts [(mul_le_of_le_one_right ha₀ hb).trans ha, (mul_le_of_le_one_left hb₀ ha).trans hb]

@[deprecated "No replacement, use constituent lemmas from proof." (since := "2026-07-28")]
lemma mul_le_one₀ [MulPosMono M₀] (ha : a ≤ 1) (hb₀ : 0 ≤ b) (hb : b ≤ 1) : a * b ≤ 1 :=
  (mul_le_of_le_one_left hb₀ ha).trans hb

lemma pow_lt_one₀ [PosMulMono M₀] (h₀ : 0 ≤ a) (h₁ : a < 1) : ∀ {n : ℕ}, n ≠ 0 → a ^ n < 1
  | 0, h => (h rfl).elim
  | n + 1, _ => by
    rw [pow_succ']; exact (mul_le_of_le_one_right h₀ (pow_le_one₀ h₀ h₁.le)).trans_lt h₁

lemma pow_right_mono₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (h : 1 ≤ a) : Monotone (a ^ ·) :=
  monotone_nat_of_le_succ fun n => by
    rw [pow_succ]; exact le_mul_of_one_le_right (pow_nonneg (zero_le_one.trans h) _) h

lemma one_le_pow₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 ≤ a) {n : ℕ} : 1 ≤ a ^ n :=
  pow_zero a ▸ pow_right_mono₀ ha n.zero_le

lemma one_lt_pow₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 < a) : ∀ {n : ℕ}, n ≠ 0 → 1 < a ^ n
  | 0, h => (h rfl).elim
  | n + 1, _ => by rw [pow_succ']; exact one_lt_mul_of_lt_of_le ha (one_le_pow₀ ha.le)

/-- `bound` lemma for branching on `1 ≤ a ∨ a ≤ 1` when proving `a ^ n ≤ a ^ m` -/
@[bound]
lemma Bound.pow_le_pow_right_of_le_one_or_one_le [ZeroLEOneClass M₀] [PosMulMono M₀]
    (h : 1 ≤ a ∧ n ≤ m ∨ 0 ≤ a ∧ a ≤ 1 ∧ m ≤ n) :
    a ^ n ≤ a ^ m := by
  obtain ⟨a1, nm⟩ | ⟨a0, a1, mn⟩ := h
  · exact pow_right_mono₀ a1 nm
  · exact pow_le_pow_of_le_one a0 a1 mn

@[gcongr]
lemma pow_le_pow_right₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 ≤ a) (hmn : m ≤ n) :
    a ^ m ≤ a ^ n :=
  pow_right_mono₀ ha hmn

lemma le_self_pow₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 ≤ a) (hn : n ≠ 0) : a ≤ a ^ n := by
  simpa only [pow_one] using pow_le_pow_right₀ ha <| Nat.pos_iff_ne_zero.2 hn

/-- The `bound` tactic can't handle `m ≠ 0` goals yet, so we express as `0 < m` -/
@[bound]
lemma Bound.le_self_pow_of_pos [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 ≤ a) (hn : 0 < n) :
    a ≤ a ^ n := le_self_pow₀ ha hn.ne'

@[mono, gcongr, bound]
theorem pow_le_pow_left₀ [PosMulMono M₀] [MulPosMono M₀]
    (ha : 0 ≤ a) (hab : a ≤ b) : ∀ n, a ^ n ≤ b ^ n
  | 0 => by simp
  | 1 => by simpa using hab
  | n + 2 => by simpa only [pow_succ']
      using mul_le_mul hab (pow_le_pow_left₀ ha hab _) (pow_succ_nonneg ha _) (ha.trans hab)

lemma pow_left_monotoneOn [PosMulMono M₀] [MulPosMono M₀] :
    MonotoneOn (fun a : M₀ ↦ a ^ n) {x | 0 ≤ x} :=
  fun _a ha _b _ hab ↦ pow_le_pow_left₀ ha hab _

variable [Preorder α] {f : α → M₀}

lemma monotone_mul_left_of_nonneg [PosMulMono M₀] (ha : 0 ≤ a) : Monotone fun x ↦ a * x :=
  fun _ _ h ↦ mul_le_mul_of_nonneg_left h ha

lemma monotone_mul_right_of_nonneg [MulPosMono M₀] (ha : 0 ≤ a) : Monotone fun x ↦ x * a :=
  fun _ _ h ↦ mul_le_mul_of_nonneg_right h ha

lemma Monotone.mul_const [MulPosMono M₀] (hf : Monotone f) (ha : 0 ≤ a) :
    Monotone fun x ↦ f x * a := (monotone_mul_right_of_nonneg ha).comp hf

lemma Monotone.const_mul [PosMulMono M₀] (hf : Monotone f) (ha : 0 ≤ a) :
    Monotone fun x ↦ a * f x := (monotone_mul_left_of_nonneg ha).comp hf

lemma Antitone.mul_const [MulPosMono M₀] (hf : Antitone f) (ha : 0 ≤ a) :
    Antitone fun x ↦ f x * a := (monotone_mul_right_of_nonneg ha).comp_antitone hf

lemma Antitone.const_mul [PosMulMono M₀] (hf : Antitone f) (ha : 0 ≤ a) :
    Antitone fun x ↦ a * f x := (monotone_mul_left_of_nonneg ha).comp_antitone hf

end Preorder

section PartialOrder
variable [PartialOrder M₀] {a b c d : M₀} {m n : ℕ}

lemma mul_self_lt_mul_self [PosMulStrictMono M₀] [MulPosMono M₀] (ha : 0 ≤ a) (hab : a < b) :
    a * a < b * b := mul_lt_mul' hab.le hab ha <| ha.trans_lt hab

-- In the next lemma, we used to write `Set.Ici 0` instead of `{x | 0 ≤ x}`.
-- As this lemma is not used outside this file,
-- and the import for `Set.Ici` is not otherwise needed until later,
-- we choose not to use it here.
lemma strictMonoOn_mul_self [PosMulStrictMono M₀] [MulPosMono M₀] :
    StrictMonoOn (fun x ↦ x * x) {x : M₀ | 0 ≤ x} := fun _ hx _ _ hxy ↦ mul_self_lt_mul_self hx hxy

-- See Note [decidable namespace]
protected lemma Decidable.mul_lt_mul'' [PosMulMono M₀] [PosMulStrictMono M₀] [MulPosStrictMono M₀]
    [DecidableLE M₀] (h1 : a < c) (h2 : b < d) (h3 : 0 ≤ a) (h4 : 0 ≤ b) : a * b < c * d :=
  h4.lt_or_eq_dec.elim (fun b0 ↦ mul_lt_mul h1 h2.le b0 <| h3.trans h1.le) fun b0 ↦ by
    rw [← b0, mul_zero]; exact mul_pos (h3.trans_lt h1) (h4.trans_lt h2)

lemma lt_mul_left [MulPosStrictMono M₀] (ha : 0 < a) (hb : 1 < b) : a < b * a := by
  simpa using mul_lt_mul_of_pos_right hb ha

lemma lt_mul_right [PosMulStrictMono M₀] (ha : 0 < a) (hb : 1 < b) : a < a * b := by
  simpa using mul_lt_mul_of_pos_left hb ha

lemma lt_mul_self [ZeroLEOneClass M₀] [MulPosStrictMono M₀] (ha : 1 < a) : a < a * a :=
  lt_mul_left (ha.trans_le' zero_le_one) ha

lemma sq_pos_of_pos [PosMulStrictMono M₀] (ha : 0 < a) : 0 < a ^ 2 := by
  simpa only [sq] using mul_pos ha ha

section strict_mono
variable [PosMulStrictMono M₀]

@[simp] lemma pow_succ_pos (ha : 0 < a) : ∀ n, 0 < a ^ (n + 1)
  | 0 => by simpa using ha
  | _ + 1 => pow_succ a _ ▸ mul_pos (pow_succ_pos ha _) ha

@[simp] lemma pow_pos [ZeroLEOneClass M₀] (ha : 0 < a) : ∀ n, 0 < a ^ n
  | 0 => by nontriviality; rw [pow_zero]; exact zero_lt_one
  | _ + 1 => pow_succ a _ ▸ mul_pos (pow_pos ha _) ha

@[gcongr, bound]
lemma pow_lt_pow_left₀ [MulPosMono M₀] (hab : a < b)
    (ha : 0 ≤ a) : ∀ {n : ℕ}, n ≠ 0 → a ^ n < b ^ n
  | 1, _ => by simpa using hab
  | n + 2, _ => by
    simpa only [pow_succ] using mul_lt_mul_of_le_of_lt_of_nonneg_of_pos
      (pow_le_pow_left₀ ha hab.le _) hab ha (pow_succ_pos (ha.trans_lt hab) _)

/-- See also `pow_left_strictMono₀` and `Nat.pow_left_strictMono`. -/
lemma pow_left_strictMonoOn₀ [MulPosMono M₀] (hn : n ≠ 0) :
    StrictMonoOn (· ^ n : M₀ → M₀) {a | 0 ≤ a} :=
  fun _a ha _b _ hab ↦ pow_lt_pow_left₀ hab ha hn

section ZeroLEOneClass

variable [ZeroLEOneClass M₀]

/-- See also `pow_right_strictMono'`. -/
lemma pow_right_strictMono₀ (h : 1 < a) : StrictMono (a ^ ·) :=
  strictMono_nat_of_lt_succ fun n => by
    simpa only [one_mul, pow_succ] using lt_mul_right (pow_pos (zero_le_one.trans_lt h) _) h

@[gcongr]
lemma pow_lt_pow_right₀ (h : 1 < a) (hmn : m < n) : a ^ m < a ^ n := pow_right_strictMono₀ h hmn

lemma pow_lt_pow_iff_right₀ (h : 1 < a) : a ^ n < a ^ m ↔ n < m :=
  (pow_right_strictMono₀ h).lt_iff_lt

lemma pow_le_pow_iff_right₀ (h : 1 < a) : a ^ n ≤ a ^ m ↔ n ≤ m :=
  (pow_right_strictMono₀ h).le_iff_le

lemma lt_self_pow₀ (h : 1 < a) (hm : 1 < m) : a < a ^ m := by
  simpa only [pow_one] using pow_lt_pow_right₀ h hm

end ZeroLEOneClass

lemma pow_right_strictAnti₀ (h₀ : 0 < a) (h₁ : a < 1) : StrictAnti (a ^ ·) :=
  strictAnti_nat_of_succ_lt fun n => by
    have : ZeroLEOneClass M₀ := ⟨(h₀.trans h₁).le⟩
    simpa only [pow_succ, mul_one] using mul_lt_mul_of_pos_left h₁ (pow_pos h₀ n)

lemma pow_le_pow_iff_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) : a ^ m ≤ a ^ n ↔ n ≤ m :=
  (pow_right_strictAnti₀ ha₀ ha₁).le_iff_ge

lemma pow_lt_pow_iff_right_of_lt_one₀ (h₀ : 0 < a) (h₁ : a < 1) : a ^ m < a ^ n ↔ n < m :=
  (pow_right_strictAnti₀ h₀ h₁).lt_iff_gt

lemma pow_lt_pow_right_of_lt_one₀ (h₀ : 0 < a) (h₁ : a < 1) (hmn : m < n) : a ^ n < a ^ m :=
  (pow_lt_pow_iff_right_of_lt_one₀ h₀ h₁).2 hmn

lemma pow_lt_self_of_lt_one₀ (h₀ : 0 < a) (h₁ : a < 1) (hn : 1 < n) : a ^ n < a := by
  simpa only [pow_one] using pow_lt_pow_right_of_lt_one₀ h₀ h₁ hn

end strict_mono

variable [Preorder α] {f g : α → M₀}

lemma strictMono_mul_left_of_pos [PosMulStrictMono M₀] (ha : 0 < a) :
    StrictMono fun x ↦ a * x := fun _ _ b_lt_c ↦ mul_lt_mul_of_pos_left b_lt_c ha

lemma strictMono_mul_right_of_pos [MulPosStrictMono M₀] (ha : 0 < a) :
    StrictMono fun x ↦ x * a := fun _ _ b_lt_c ↦ mul_lt_mul_of_pos_right b_lt_c ha

lemma StrictMono.mul_const [MulPosStrictMono M₀] (hf : StrictMono f) (ha : 0 < a) :
    StrictMono fun x ↦ f x * a := (strictMono_mul_right_of_pos ha).comp hf

lemma StrictMono.const_mul [PosMulStrictMono M₀] (hf : StrictMono f) (ha : 0 < a) :
    StrictMono fun x ↦ a * f x := (strictMono_mul_left_of_pos ha).comp hf

lemma StrictAnti.mul_const [MulPosStrictMono M₀] (hf : StrictAnti f) (ha : 0 < a) :
    StrictAnti fun x ↦ f x * a := (strictMono_mul_right_of_pos ha).comp_strictAnti hf

lemma StrictAnti.const_mul [PosMulStrictMono M₀] (hf : StrictAnti f) (ha : 0 < a) :
    StrictAnti fun x ↦ a * f x := (strictMono_mul_left_of_pos ha).comp_strictAnti hf

lemma StrictMono.mul_monotone [PosMulMono M₀] [MulPosStrictMono M₀] (hf : StrictMono f)
    (hg : Monotone g) (hf₀ : ∀ x, 0 ≤ f x) (hg₀ : ∀ x, 0 < g x) :
    StrictMono (f * g) := fun _ _ h ↦ mul_lt_mul (hf h) (hg h.le) (hg₀ _) (hf₀ _)

lemma Monotone.mul_strictMono [PosMulStrictMono M₀] [MulPosMono M₀] (hf : Monotone f)
    (hg : StrictMono g) (hf₀ : ∀ x, 0 < f x) (hg₀ : ∀ x, 0 ≤ g x) :
    StrictMono (f * g) := fun _ _ h ↦ mul_lt_mul' (hf h.le) (hg h) (hg₀ _) (hf₀ _)

lemma StrictMono.mul [PosMulStrictMono M₀] [MulPosStrictMono M₀] (hf : StrictMono f)
    (hg : StrictMono g) (hf₀ : ∀ x, 0 ≤ f x) (hg₀ : ∀ x, 0 ≤ g x) :
    StrictMono (f * g) := fun _ _ h ↦ mul_lt_mul'' (hf h) (hg h) (hf₀ _) (hg₀ _)

end PartialOrder

section LinearOrder
variable [LinearOrder M₀] [PosMulStrictMono M₀] {a b : M₀}
  {m n : ℕ}

lemma pow_le_pow_iff_left₀ [MulPosMono M₀] (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : n ≠ 0) :
    a ^ n ≤ b ^ n ↔ a ≤ b :=
  (pow_left_strictMonoOn₀ hn).le_iff_le ha hb

lemma pow_lt_pow_iff_left₀ [MulPosMono M₀] (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : n ≠ 0) :
    a ^ n < b ^ n ↔ a < b :=
  (pow_left_strictMonoOn₀ hn).lt_iff_lt ha hb

@[simp]
lemma pow_left_inj₀ [MulPosMono M₀] (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : n ≠ 0) :
    a ^ n = b ^ n ↔ a = b :=
  (pow_left_strictMonoOn₀ hn).eq_iff_eq ha hb

section ZeroLEOneClass

variable [ZeroLEOneClass M₀]

lemma pow_right_injective₀ (ha₀ : 0 < a) (ha₁ : a ≠ 1) : Injective (a ^ ·) := by
  obtain ha₁ | ha₁ := ha₁.lt_or_gt
  · exact (pow_right_strictAnti₀ ha₀ ha₁).injective
  · exact (pow_right_strictMono₀ ha₁).injective

@[simp]
lemma pow_right_inj₀ (ha₀ : 0 < a) (ha₁ : a ≠ 1) : a ^ m = a ^ n ↔ m = n :=
  (pow_right_injective₀ ha₀ ha₁).eq_iff

lemma pow_le_one_iff_of_nonneg (ha : 0 ≤ a) (hn : n ≠ 0) : a ^ n ≤ 1 ↔ a ≤ 1 := by
  refine ⟨fun h ↦ ?_, pow_le_one₀ ha⟩
  contrapose! h
  exact one_lt_pow₀ h hn

lemma one_le_pow_iff_of_nonneg (ha : 0 ≤ a) (hn : n ≠ 0) : 1 ≤ a ^ n ↔ 1 ≤ a := by
  refine ⟨fun h ↦ ?_, fun h ↦ one_le_pow₀ h⟩
  contrapose! h
  exact pow_lt_one₀ ha h hn

lemma pow_lt_one_iff_of_nonneg (ha : 0 ≤ a) (hn : n ≠ 0) : a ^ n < 1 ↔ a < 1 :=
  lt_iff_lt_of_le_iff_le (one_le_pow_iff_of_nonneg ha hn)

lemma one_lt_pow_iff_of_nonneg (ha : 0 ≤ a) (hn : n ≠ 0) : 1 < a ^ n ↔ 1 < a := by
  simp only [← not_le, pow_le_one_iff_of_nonneg ha hn]

lemma pow_eq_one_iff_of_nonneg (ha : 0 ≤ a) (hn : n ≠ 0) : a ^ n = 1 ↔ a = 1 := by
  simp only [le_antisymm_iff, pow_le_one_iff_of_nonneg ha hn, one_le_pow_iff_of_nonneg ha hn]

lemma sq_le_one_iff₀ (ha : 0 ≤ a) : a ^ 2 ≤ 1 ↔ a ≤ 1 :=
  pow_le_one_iff_of_nonneg ha (Nat.succ_ne_zero _)

lemma sq_lt_one_iff₀ (ha : 0 ≤ a) : a ^ 2 < 1 ↔ a < 1 :=
  pow_lt_one_iff_of_nonneg ha (Nat.succ_ne_zero _)

lemma one_le_sq_iff₀ (ha : 0 ≤ a) : 1 ≤ a ^ 2 ↔ 1 ≤ a :=
  one_le_pow_iff_of_nonneg ha (Nat.succ_ne_zero _)

lemma one_lt_sq_iff₀ (ha : 0 ≤ a) : 1 < a ^ 2 ↔ 1 < a :=
  one_lt_pow_iff_of_nonneg ha (Nat.succ_ne_zero _)

end ZeroLEOneClass

variable [MulPosMono M₀]

lemma lt_of_pow_lt_pow_left₀ (n : ℕ) (hb : 0 ≤ b) (h : a ^ n < b ^ n) : a < b :=
  lt_of_not_ge fun hn => not_lt_of_ge (pow_le_pow_left₀ hb hn _) h

lemma le_of_pow_le_pow_left₀ (hn : n ≠ 0) (hb : 0 ≤ b) (h : a ^ n ≤ b ^ n) : a ≤ b :=
  le_of_not_gt fun h1 => not_le_of_gt (pow_lt_pow_left₀ h1 hb hn) h

lemma sq_eq_sq₀ (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 2 = b ^ 2 ↔ a = b := by
  simp [ha, hb]

lemma lt_of_mul_self_lt_mul_self₀ (hb : 0 ≤ b) : a * a < b * b → a < b := by
  simp only [← sq]
  exact lt_of_pow_lt_pow_left₀ _ hb

lemma sq_lt_sq₀ (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 2 < b ^ 2 ↔ a < b :=
  pow_lt_pow_iff_left₀ ha hb two_ne_zero

lemma sq_le_sq₀ (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 2 ≤ b ^ 2 ↔ a ≤ b :=
  pow_le_pow_iff_left₀ ha hb two_ne_zero

end MonoidWithZero.LinearOrder

section UnitPositivity
variable [MonoidWithZero G₀] [PartialOrder G₀]

namespace Units

@[simp] lemma inv_pos [PosMulReflectLT G₀] (u : G₀ˣ) :
    (0 : G₀) < ↑u⁻¹ ↔ 0 < (u : G₀) := by
  have step : ∀ v : G₀ˣ, (0 : G₀) < v → (0 : G₀) < ↑v⁻¹ := by
    intro v hv
    apply lt_of_mul_lt_mul_left _ hv.le
    apply lt_of_mul_lt_mul_left _ hv.le
    simpa only [mul_zero, Units.mul_inv, mul_one] using hv
  exact ⟨fun h => by simpa only [inv_inv] using step u⁻¹ h, step u⟩

lemma inv_pos_right [MulPosReflectLT G₀] (u : G₀ˣ) :
    (0 : G₀) < ↑u⁻¹ ↔ 0 < (u : G₀) := by
  have step : ∀ v : G₀ˣ, (0 : G₀) < v → (0 : G₀) < ↑v⁻¹ := by
    intro v hv
    apply lt_of_mul_lt_mul_right _ hv.le
    apply lt_of_mul_lt_mul_right _ hv.le
    simpa only [zero_mul, Units.inv_mul, one_mul] using hv
  exact ⟨fun h => by simpa only [inv_inv] using step u⁻¹ h, step u⟩

end Units
end UnitPositivity

section Units
variable [GroupWithZero G₀] [PartialOrder G₀]

namespace Units

@[simp] lemma inv_nonneg [PosMulReflectLT G₀] (u : G₀ˣ) :
    (0 : G₀) ≤ ↑u⁻¹ ↔ 0 ≤ (u : G₀) := by
  simp only [le_iff_eq_or_lt, Ne.symm u.ne_zero, Ne.symm u⁻¹.ne_zero, false_or, inv_pos]

lemma inv_nonneg_right [MulPosReflectLT G₀] (u : G₀ˣ) :
    (0 : G₀) ≤ ↑u⁻¹ ↔ 0 ≤ (u : G₀) := by
  simp only [le_iff_eq_or_lt, Ne.symm u.ne_zero, Ne.symm u⁻¹.ne_zero, false_or, inv_pos_right]

end Units

variable (G₀) in
/-- Positivity reflection implies strict monotonicity, using the inverse of a positive unit. -/
theorem PosMulReflectLT.toPosMulStrictMono [PosMulReflectLT G₀] : PosMulStrictMono G₀ where
  mul_lt_mul_of_pos_left a ha b c hbc := by
    let u := Units.mk0 a ha.ne'
    apply lt_of_mul_lt_mul_left (a := (↑u⁻¹ : G₀)) ?_ ((Units.inv_pos u).2 ha).le
    change ↑u⁻¹ * ((u : G₀) * b) < ↑u⁻¹ * ((u : G₀) * c)
    simpa only [Units.inv_mul_cancel_left] using hbc

variable (G₀) in
/-- Right positivity reflection implies strict monotonicity via a positive unit inverse. -/
theorem MulPosReflectLT.toMulPosStrictMono [MulPosReflectLT G₀] : MulPosStrictMono G₀ where
  mul_lt_mul_of_pos_right a ha b c hbc := by
    let u := Units.mk0 a ha.ne'
    apply lt_of_mul_lt_mul_right (a := (↑u⁻¹ : G₀)) ?_ ((Units.inv_pos_right u).2 ha).le
    change b * (u : G₀) * ↑u⁻¹ < c * (u : G₀) * ↑u⁻¹
    simpa only [Units.mul_inv_cancel_right] using hbc

attribute [local instance] PosMulReflectLT.toPosMulStrictMono
  MulPosReflectLT.toMulPosStrictMono PosMulReflectLT.toPosMulReflectLE
  MulPosReflectLT.toMulPosReflectLE

namespace Units
variable {a b : G₀} {u v : G₀ˣ}

lemma le_inv_mul_iff [PosMulReflectLT G₀] (hu : (0 : G₀) < u) :
    a ≤ ↑u⁻¹ * b ↔ (u : G₀) * a ≤ b := by
  rw [← mul_le_mul_iff_of_pos_left hu, Units.mul_inv_cancel_left]

lemma inv_mul_le_iff [PosMulReflectLT G₀] (hu : (0 : G₀) < u) :
    ↑u⁻¹ * a ≤ b ↔ a ≤ (u : G₀) * b := by
  rw [← mul_le_mul_iff_of_pos_left hu, Units.mul_inv_cancel_left]

lemma lt_inv_mul_iff [PosMulReflectLT G₀] (hu : (0 : G₀) < u) :
    a < ↑u⁻¹ * b ↔ (u : G₀) * a < b := by
  rw [← mul_lt_mul_iff_of_pos_left hu, Units.mul_inv_cancel_left]

lemma inv_mul_lt_iff [PosMulReflectLT G₀] (hu : (0 : G₀) < u) :
    ↑u⁻¹ * a < b ↔ a < (u : G₀) * b := by
  rw [← mul_lt_mul_iff_of_pos_left hu, Units.mul_inv_cancel_left]

lemma inv_le_inv [PosMulReflectLT G₀] [MulPosReflectLT G₀]
    (hu : (0 : G₀) < u) (hv : (0 : G₀) < v) :
    (↑u⁻¹ : G₀) ≤ ↑v⁻¹ ↔ (v : G₀) ≤ u := by
  rw [← mul_le_mul_iff_of_pos_left hu, Units.mul_inv,
    ← mul_le_mul_iff_of_pos_right hv, one_mul, Units.inv_mul_cancel_right]

lemma inv_lt_inv [PosMulReflectLT G₀] [MulPosReflectLT G₀]
    (hu : (0 : G₀) < u) (hv : (0 : G₀) < v) :
    (↑u⁻¹ : G₀) < ↑v⁻¹ ↔ (v : G₀) < u := by
  rw [← mul_lt_mul_iff_of_pos_left hu, Units.mul_inv,
    ← mul_lt_mul_iff_of_pos_right hv, one_mul, Units.inv_mul_cancel_right]

end Units

section Right
variable [MulPosReflectLT G₀] {a b : G₀} {u : G₀ˣ}

lemma le_divp_iff (hu : (0 : G₀) < u) : a ≤ b /ₚ u ↔ a * u ≤ b := by
  rw [← mul_le_mul_iff_of_pos_right hu, divp_mul_cancel]

lemma divp_le_iff (hu : (0 : G₀) < u) : a /ₚ u ≤ b ↔ a ≤ b * u := by
  rw [← mul_le_mul_iff_of_pos_right hu, divp_mul_cancel]

lemma lt_divp_iff (hu : (0 : G₀) < u) : a < b /ₚ u ↔ a * u < b := by
  rw [← mul_lt_mul_iff_of_pos_right hu, divp_mul_cancel]

lemma divp_lt_iff (hu : (0 : G₀) < u) : a /ₚ u < b ↔ a < b * u := by
  rw [← mul_lt_mul_iff_of_pos_right hu, divp_mul_cancel]

lemma divp_le_divp_iff (hu : (0 : G₀) < u) : a /ₚ u ≤ b /ₚ u ↔ a ≤ b := by
  rw [divp_le_iff hu, divp_mul_cancel]

lemma divp_lt_divp_iff (hu : (0 : G₀) < u) : a /ₚ u < b /ₚ u ↔ a < b := by
  rw [divp_lt_iff hu, divp_mul_cancel]

lemma one_le_divp (hu : (0 : G₀) < u) : 1 ≤ a /ₚ u ↔ (u : G₀) ≤ a := by
  rw [le_divp_iff hu, one_mul]

lemma one_lt_divp (hu : (0 : G₀) < u) : 1 < a /ₚ u ↔ (u : G₀) < a := by
  rw [lt_divp_iff hu, one_mul]

lemma divp_le_one (hu : (0 : G₀) < u) : a /ₚ u ≤ 1 ↔ a ≤ (u : G₀) := by
  rw [divp_le_iff hu, one_mul]

lemma divp_lt_one (hu : (0 : G₀) < u) : a /ₚ u < 1 ↔ a < (u : G₀) := by
  rw [divp_lt_iff hu, one_mul]

end Right

lemma divp_pos [PosMulReflectLT G₀] {a : G₀} {u : G₀ˣ}
    (ha : 0 < a) (hu : (0 : G₀) < u) : 0 < a /ₚ u :=
  mul_pos ha ((Units.inv_pos u).2 hu)

lemma divp_nonneg [PosMulReflectLT G₀] {a : G₀} {u : G₀ˣ}
    (ha : 0 ≤ a) (hu : (0 : G₀) ≤ u) : 0 ≤ a /ₚ u :=
  mul_nonneg ha ((Units.inv_nonneg u).2 hu)

end Units

namespace Units
section OrderedPowers
variable [GroupWithZero G₀] [PartialOrder G₀] [PosMulReflectLT G₀] [ZeroLEOneClass G₀]
variable {a : G₀ˣ} {m n : ℤ}

attribute [local instance] PosMulReflectLT.toPosMulStrictMono

lemma zpow_nonneg (ha : 0 ≤ (a : G₀)) : ∀ n : ℤ, 0 ≤ (↑(a ^ n) : G₀)
  | (n : ℕ) => by rw [zpow_natCast, Units.val_pow_eq_pow_val]; exact pow_nonneg ha _
  | -(n + 1 : ℕ) => by
    rw [zpow_neg, Units.inv_nonneg, zpow_natCast, Units.val_pow_eq_pow_val]
    exact pow_nonneg ha _

lemma zpow_pos (ha : 0 < (a : G₀)) : ∀ n : ℤ, 0 < (↑(a ^ n) : G₀)
  | (n : ℕ) => by rw [zpow_natCast, Units.val_pow_eq_pow_val]; exact pow_pos ha _
  | -(n + 1 : ℕ) => by
    rw [zpow_neg, Units.inv_pos, zpow_natCast, Units.val_pow_eq_pow_val]
    exact pow_pos ha _

lemma zpow_right_mono (ha : 1 ≤ (a : G₀)) : Monotone fun n : ℤ ↦ (↑(a ^ n) : G₀) := by
  refine monotone_int_of_le_succ fun n ↦ ?_
  rw [zpow_add_one, Units.val_mul]
  exact le_mul_of_one_le_right (zpow_nonneg (zero_le_one.trans ha) _) ha

lemma zpow_right_anti (ha0 : 0 < (a : G₀)) (ha1 : (a : G₀) ≤ 1) :
    Antitone fun n : ℤ ↦ (↑(a ^ n) : G₀) := by
  refine antitone_int_of_succ_le fun n ↦ ?_
  rw [zpow_add_one, Units.val_mul]
  exact mul_le_of_le_one_right (zpow_nonneg ha0.le _) ha1

lemma zpow_right_strictMono (ha : 1 < (a : G₀)) : StrictMono fun n : ℤ ↦ (↑(a ^ n) : G₀) := by
  refine strictMono_int_of_lt_succ fun n ↦ ?_
  rw [zpow_add_one, Units.val_mul]
  exact lt_mul_of_one_lt_right (zpow_pos (zero_lt_one.trans ha) _) ha

lemma zpow_right_strictAnti (ha0 : 0 < (a : G₀)) (ha1 : (a : G₀) < 1) :
    StrictAnti fun n : ℤ ↦ (↑(a ^ n) : G₀) := by
  refine strictAnti_int_of_succ_lt fun n ↦ ?_
  rw [zpow_add_one, Units.val_mul]
  exact mul_lt_of_lt_one_right (zpow_pos ha0 _) ha1

lemma zpow_le_zpow_right (ha : 1 ≤ (a : G₀)) (hmn : m ≤ n) : (↑(a ^ m) : G₀) ≤ (↑(a ^ n) : G₀) :=
  zpow_right_mono ha hmn

lemma zpow_le_zpow_right_of_le_one (ha0 : 0 < (a : G₀)) (ha1 : (a : G₀) ≤ 1) (hmn : m ≤ n) :
    (↑(a ^ n) : G₀) ≤ (↑(a ^ m) : G₀) :=
  zpow_right_anti ha0 ha1 hmn

lemma one_le_zpow (ha : 1 ≤ (a : G₀)) (hn : 0 ≤ n) : 1 ≤ (↑(a ^ n) : G₀) := by
  simpa using zpow_right_mono ha hn

lemma zpow_le_one (ha0 : 0 < (a : G₀)) (ha1 : (a : G₀) ≤ 1) (hn : 0 ≤ n) : (↑(a ^ n) : G₀) ≤ 1 := by
  simpa using zpow_right_anti ha0 ha1 hn

lemma zpow_le_one_of_nonpos (ha : 1 ≤ (a : G₀)) (hn : n ≤ 0) : (↑(a ^ n) : G₀) ≤ 1 := by
  simpa using zpow_right_mono ha hn

lemma one_le_zpow_of_nonpos (ha0 : 0 < (a : G₀)) (ha1 : (a : G₀) ≤ 1) (hn : n ≤ 0) :
    1 ≤ (↑(a ^ n) : G₀) := by
  simpa using zpow_right_anti ha0 ha1 hn

lemma zpow_lt_zpow_right (ha : 1 < (a : G₀)) (hmn : m < n) : (↑(a ^ m) : G₀) < (↑(a ^ n) : G₀) :=
  zpow_right_strictMono ha hmn

lemma zpow_lt_zpow_right_of_lt_one (ha0 : 0 < (a : G₀)) (ha1 : (a : G₀) < 1) (hmn : m < n) :
    (↑(a ^ n) : G₀) < (↑(a ^ m) : G₀) :=
  zpow_right_strictAnti ha0 ha1 hmn

lemma one_lt_zpow (ha : 1 < (a : G₀)) (hn : 0 < n) : 1 < (↑(a ^ n) : G₀) := by
  simpa using zpow_right_strictMono ha hn

lemma zpow_lt_one (ha0 : 0 < (a : G₀)) (ha1 : (a : G₀) < 1) (hn : 0 < n) : (↑(a ^ n) : G₀) < 1 := by
  simpa using zpow_right_strictAnti ha0 ha1 hn

lemma zpow_lt_one_of_neg (ha : 1 < (a : G₀)) (hn : n < 0) : (↑(a ^ n) : G₀) < 1 := by
  simpa using zpow_right_strictMono ha hn

lemma one_lt_zpow_of_neg (ha0 : 0 < (a : G₀)) (ha1 : (a : G₀) < 1) (hn : n < 0) :
    1 < (↑(a ^ n) : G₀) := by
  simpa using zpow_right_strictAnti ha0 ha1 hn

@[simp] lemma zpow_le_zpow_iff_right (ha : 1 < (a : G₀)) :
    (↑(a ^ m) : G₀) ≤ (↑(a ^ n) : G₀) ↔ m ≤ n :=
  (zpow_right_strictMono ha).le_iff_le

@[simp] lemma zpow_lt_zpow_iff_right (ha : 1 < (a : G₀)) :
    (↑(a ^ m) : G₀) < (↑(a ^ n) : G₀) ↔ m < n :=
  (zpow_right_strictMono ha).lt_iff_lt

lemma zpow_le_zpow_iff_right_of_lt_one (ha0 : 0 < (a : G₀)) (ha1 : (a : G₀) < 1) :
    (↑(a ^ m) : G₀) ≤ (↑(a ^ n) : G₀) ↔ n ≤ m := (zpow_right_strictAnti ha0 ha1).le_iff_ge

lemma zpow_lt_zpow_iff_right_of_lt_one (ha0 : 0 < (a : G₀)) (ha1 : (a : G₀) < 1) :
    (↑(a ^ m) : G₀) < (↑(a ^ n) : G₀) ↔ n < m := (zpow_right_strictAnti ha0 ha1).lt_iff_gt

@[simp] lemma one_le_zpow_iff_right (ha : 1 < (a : G₀)) : 1 ≤ (↑(a ^ n) : G₀) ↔ 0 ≤ n := by
  simp [← zpow_le_zpow_iff_right ha]

@[simp] lemma one_lt_zpow_iff_right (ha : 1 < (a : G₀)) : 1 < (↑(a ^ n) : G₀) ↔ 0 < n := by
  simp [← zpow_lt_zpow_iff_right ha]

@[simp] lemma one_le_zpow_iff_right_of_lt_one (ha0 : 0 < (a : G₀)) (ha1 : (a : G₀) < 1) :
    1 ≤ (↑(a ^ n) : G₀) ↔ n ≤ 0 := by
  simp [← zpow_le_zpow_iff_right_of_lt_one ha0 ha1]

@[simp] lemma one_lt_zpow_iff_right_of_lt_one (ha0 : 0 < (a : G₀)) (ha1 : (a : G₀) < 1) :
    1 < (↑(a ^ n) : G₀) ↔ n < 0 := by
  simp [← zpow_lt_zpow_iff_right_of_lt_one ha0 ha1]

@[simp] lemma zpow_le_one_iff_right (ha : 1 < (a : G₀)) : (↑(a ^ n) : G₀) ≤ 1 ↔ n ≤ 0 := by
  simp [← zpow_le_zpow_iff_right ha]

@[simp] lemma zpow_lt_one_iff_right (ha : 1 < (a : G₀)) : (↑(a ^ n) : G₀) < 1 ↔ n < 0 := by
  simp [← zpow_lt_zpow_iff_right ha]

@[simp] lemma zpow_le_one_iff_right_of_lt_one (ha0 : 0 < (a : G₀)) (ha1 : (a : G₀) < 1) :
    (↑(a ^ n) : G₀) ≤ 1 ↔ 0 ≤ n := by
  simp [← zpow_le_zpow_iff_right_of_lt_one ha0 ha1]

@[simp] lemma zpow_lt_one_iff_right_of_lt_one (ha0 : 0 < (a : G₀)) (ha1 : (a : G₀) < 1) :
    (↑(a ^ n) : G₀) < 1 ↔ 0 < n := by
  simp [← zpow_lt_zpow_iff_right_of_lt_one ha0 ha1]

end OrderedPowers
end Units

section MixedOrder
variable [GroupWithZero G₀] [PartialOrder G₀]

variable (G₀) in
/-- Left positivity reflection upgrades right monotonicity to right order reflection. -/
theorem MulPosReflectLE.of_posMulReflectLT_of_mulPosMono
    [PosMulReflectLT G₀] [MulPosMono G₀] : MulPosReflectLE G₀ where
  elim := by
    rintro ⟨a, ha⟩ b c h
    let u := Units.mk0 a ha.ne'
    have h' : b * (u : G₀) ≤ c * (u : G₀) := h
    have hi := mul_le_mul_of_nonneg_right h' ((Units.inv_nonneg u).2 ha.le)
    simpa only [Units.mul_inv_cancel_right] using hi

attribute [local instance] PosMulReflectLT.toPosMulStrictMono
  MulPosReflectLT.toMulPosStrictMono

lemma divp_nonpos_of_nonpos_of_nonneg [MulPosReflectLT G₀] {a : G₀} {u : G₀ˣ}
    (ha : a ≤ 0) (hu : (0 : G₀) ≤ u) : a /ₚ u ≤ 0 :=
  mul_nonpos_of_nonpos_of_nonneg ha ((Units.inv_nonneg_right u).2 hu)

@[gcongr, bound] lemma divp_le_divp_of_nonneg_right [MulPosReflectLT G₀]
    {a b : G₀} {u : G₀ˣ} (hab : a ≤ b) (hu : (0 : G₀) ≤ u) : a /ₚ u ≤ b /ₚ u :=
  mul_le_mul_of_nonneg_right hab ((Units.inv_nonneg_right u).2 hu)

@[gcongr, bound] lemma divp_lt_divp_of_pos_right [MulPosReflectLT G₀]
    {a b : G₀} {u : G₀ˣ} (hab : a < b) (hu : (0 : G₀) < u) : a /ₚ u < b /ₚ u :=
  mul_lt_mul_of_pos_right hab ((Units.inv_pos_right u).2 hu)

lemma divp_le_divp_of_nonneg_left [PosMulReflectLT G₀] [MulPosReflectLT G₀]
    {a : G₀} {u v : G₀ˣ} (ha : 0 ≤ a) (hv : (0 : G₀) < v) (hvu : (v : G₀) ≤ u) :
    a /ₚ u ≤ a /ₚ v :=
  mul_le_mul_of_nonneg_left ((Units.inv_le_inv (hv.trans_le hvu) hv).2 hvu) ha

lemma divp_lt_divp_of_pos_left [PosMulReflectLT G₀] [MulPosReflectLT G₀]
    {a : G₀} {u v : G₀ˣ} (ha : 0 < a) (hv : (0 : G₀) < v) (hvu : (v : G₀) < u) :
    a /ₚ u < a /ₚ v :=
  mul_lt_mul_of_pos_left ((Units.inv_lt_inv (hv.trans hvu) hv).2 hvu) ha

end MixedOrder

section CommGroupWithZero
variable [CommGroupWithZero G₀] [PartialOrder G₀] [MulPosReflectLT G₀]
variable {a b : G₀} {u v : G₀ˣ}

lemma divp_le_divp_iff_cross (hu : (0 : G₀) < u) (hv : (0 : G₀) < v) :
    a /ₚ u ≤ b /ₚ v ↔ a * v ≤ b * u := by
  rw [divp_le_iff hu, divp_mul_eq_mul_divp, le_divp_iff hv]

lemma divp_lt_divp_iff_cross (hu : (0 : G₀) < u) (hv : (0 : G₀) < v) :
    a /ₚ u < b /ₚ v ↔ a * v < b * u := by
  rw [divp_lt_iff hu, divp_mul_eq_mul_divp, lt_divp_iff hv]

end CommGroupWithZero

namespace Units
variable [GroupWithZero G₀] [LinearOrder G₀] [PosMulMono G₀] (u : G₀ˣ)

lemma inv_neg_of_posMulMono : (↑u⁻¹ : G₀) < 0 ↔ (u : G₀) < 0 := by
  let := PosMulMono.toPosMulReflectLT (α := G₀)
  simp only [← not_le, inv_nonneg]

@[simp] lemma inv_nonpos : (↑u⁻¹ : G₀) ≤ 0 ↔ (u : G₀) ≤ 0 := by
  let := PosMulMono.toPosMulReflectLT (α := G₀)
  simp only [← not_lt, inv_pos]

end Units

namespace Units

/-- Inversion preserves negativity for units of an ordered monoid with positive identity. -/
@[simp] lemma inv_neg [MonoidWithZero M₀] [LinearOrder M₀] [ZeroLEOneClass M₀]
    [NeZero (1 : M₀)] [MulPosMono M₀] [PosMulMono M₀] (u : M₀ˣ) :
    (↑u⁻¹ : M₀) < 0 ↔ (u : M₀) < 0 := by
  have step : ∀ v : M₀ˣ, (v : M₀) < 0 → (↑v⁻¹ : M₀) < 0 := by
    intro v hv
    exact neg_of_mul_pos_right (v.mul_inv.symm ▸ zero_lt_one) hv.le
  exact ⟨fun h => by simpa only [inv_inv] using step u⁻¹ h, step u⟩

end Units

namespace Units
section PowerComparison
variable [GroupWithZero G₀] [LinearOrder G₀] [PosMulReflectLT G₀] [MulPosMono G₀]
variable {u v : G₀ˣ} {n : ℤ}

attribute [local instance] PosMulReflectLT.toPosMulStrictMono

lemma zpow_le_zpow_left (hn : 0 ≤ n) (hu : (0 : G₀) ≤ u) (huv : (u : G₀) ≤ v) :
    (↑(u ^ n) : G₀) ≤ ↑(v ^ n) := by
  lift n to ℕ using hn
  simpa only [zpow_natCast, Units.val_pow_eq_pow_val] using pow_le_pow_left₀ hu huv n

lemma zpow_lt_zpow_left (hn : 0 < n) (hu : (0 : G₀) ≤ u) (huv : (u : G₀) < v) :
    (↑(u ^ n) : G₀) < ↑(v ^ n) := by
  lift n to ℕ using hn.le
  have hn' : n ≠ 0 := by exact_mod_cast hn.ne'
  simpa only [zpow_natCast, Units.val_pow_eq_pow_val] using pow_lt_pow_left₀ huv hu hn'

lemma zpow_left_inj (hu : (0 : G₀) ≤ u) (hv : (0 : G₀) ≤ v) (hn : n ≠ 0) :
    u ^ n = v ^ n ↔ u = v := by
  have hp : ∀ k : ℕ, k ≠ 0 → (u ^ k = v ^ k ↔ u = v) := by
    intro k hk
    constructor
    · intro h
      apply Units.ext
      apply (pow_left_inj₀ hu hv hk).mp
      simpa only [Units.val_pow_eq_pow_val] using congr_arg Units.val h
    · rintro rfl; rfl
  cases n with
  | ofNat n =>
    have hn' : n ≠ 0 := fun h => hn (h ▸ rfl)
    simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hp n hn'
  | negSucc n => simpa only [zpow_negSucc, inv_inj] using hp (n + 1) (Nat.succ_ne_zero n)

end PowerComparison

section ExponentComparison
variable [GroupWithZero G₀] [LinearOrder G₀] [PosMulReflectLT G₀] [ZeroLEOneClass G₀]
variable {u : G₀ˣ} {m n : ℤ}

lemma zpow_right_injective (hu : (0 : G₀) < u) (hu1 : (u : G₀) ≠ 1) :
    Injective fun n : ℤ ↦ (↑(u ^ n) : G₀) := by
  obtain h | h := hu1.lt_or_gt
  · exact (zpow_right_strictAnti hu h).injective
  · exact (zpow_right_strictMono h).injective

lemma zpow_right_inj (hu : (0 : G₀) < u) (hu1 : (u : G₀) ≠ 1) :
    (↑(u ^ m) : G₀) = ↑(u ^ n) ↔ m = n := (zpow_right_injective hu hu1).eq_iff

end ExponentComparison
end Units
