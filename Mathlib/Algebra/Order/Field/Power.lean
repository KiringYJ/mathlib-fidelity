/-
Copyright (c) 2014 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Leonardo de Moura, Mario Carneiro, Floris van Doorn, Sabbir Rahman
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Tactic.Positivity.Core

/-!
# Integer powers on their invertible domain in ordered fields

`Checked.zpow a n h` keeps the entire ambient domain when `n` is nonnegative;
`h` supplies invertibility precisely when `n` is negative.
-/

public section

open Function Int

namespace Checked
section Ordered
variable {M : Type*} [GroupWithZero M] [PartialOrder M] [PosMulReflectLT M] [ZeroLEOneClass M]
attribute [local instance] PosMulReflectLT.toPosMulStrictMono

theorem zpow_nonneg {a : M} (ha : 0 ≤ a) (n : ℤ) (h : n < 0 → IsUnit a) :
    0 ≤ zpow a n h := by
  cases n with
  | ofNat k => exact pow_nonneg ha k
  | negSucc k => exact Units.zpow_nonneg (a := (h (Int.negSucc_lt_zero k)).unit) ha _

theorem zpow_pos {a : M} (ha : 0 < a) (n : ℤ) (h : n < 0 → IsUnit a) :
    0 < zpow a n h := by
  cases n with
  | ofNat k => exact pow_pos ha k
  | negSucc k => exact Units.zpow_pos (a := (h (Int.negSucc_lt_zero k)).unit) ha _

end Ordered
end Checked

variable {α : Type*}

section LinearOrderedField
variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a b : α} {n : ℤ}

protected theorem Even.zpow_nonneg (hn : Even n) (a : α) (h : n < 0 → IsUnit a) :
    0 ≤ Checked.zpow a n h := by
  cases n with
  | ofNat k => exact ((Int.even_coe_nat k).mp hn).pow_nonneg a
  | negSucc k =>
    change Even (-(↑(k + 1) : ℤ)) at hn
    have hk : Even (k + 1) := (Int.even_coe_nat (k + 1)).mp (even_neg.mp hn)
    rw [Checked.zpow_negSucc]
    exact hk.pow_nonneg _

lemma zpow_two_nonneg (a : α) : 0 ≤ Checked.zpow a 2 (by intro h; omega) :=
  even_two.zpow_nonneg a _

lemma zpow_neg_two_nonneg (a : α) (ha : IsUnit a) :
    0 ≤ Checked.zpow a (-2) (fun _ => ha) := even_neg_two.zpow_nonneg a _

protected lemma Even.zpow_pos (hn : Even n) (ha : a ≠ 0) :
    0 < Checked.zpow a n (fun _ => GroupWithZero.isUnit_of_ne_zero ha) :=
  (hn.zpow_nonneg _ _).lt_of_ne' (Checked.zpow_ne_zero ha n _)

lemma zpow_two_pos_of_ne_zero (ha : a ≠ 0) :
    0 < Checked.zpow a 2 (fun _ => GroupWithZero.isUnit_of_ne_zero ha) := even_two.zpow_pos ha

theorem Even.zpow_pos_iff (hn : Even n) (hn0 : n ≠ 0) (h : n < 0 → IsUnit a) :
    0 < Checked.zpow a n h ↔ a ≠ 0 := by
  refine ⟨fun hp ha => hp.ne' ((Checked.zpow_eq_zero_iff hn0 h).mpr ha), fun ha => ?_⟩
  exact hn.zpow_pos ha

theorem Odd.zpow_neg_iff (hn : Odd n) (h : n < 0 → IsUnit a) :
    Checked.zpow a n h < 0 ↔ a < 0 := by
  cases n with
  | ofNat k => exact ((Int.odd_coe_nat k).mp hn).pow_neg_iff
  | negSucc k =>
    change Odd (-(↑(k + 1) : ℤ)) at hn
    have hk : Odd (k + 1) := (Int.odd_coe_nat (k + 1)).mp (odd_neg.mp hn)
    rw [Checked.zpow_negSucc, hk.pow_neg_iff]
    exact inv_lt_zero'

protected lemma Odd.zpow_nonneg_iff (hn : Odd n) (h : n < 0 → IsUnit a) :
    0 ≤ Checked.zpow a n h ↔ 0 ≤ a :=
  le_iff_le_iff_lt_iff_lt.2 (hn.zpow_neg_iff h)

theorem Odd.zpow_nonpos_iff (hn : Odd n) (h : n < 0 → IsUnit a) :
    Checked.zpow a n h ≤ 0 ↔ a ≤ 0 := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq, hn.zpow_neg_iff h, Checked.zpow_eq_zero_iff hn0 h]

lemma Odd.zpow_pos_iff (hn : Odd n) (h : n < 0 → IsUnit a) :
    0 < Checked.zpow a n h ↔ 0 < a :=
  lt_iff_lt_of_le_iff_le (hn.zpow_nonpos_iff h)

alias ⟨_, Odd.zpow_neg⟩ := Odd.zpow_neg_iff
alias ⟨_, Odd.zpow_nonpos⟩ := Odd.zpow_nonpos_iff

@[simp] theorem abs_zpow (a : α) (p : ℤ) (h : p < 0 → IsUnit a) :
    |Checked.zpow a p h| = Checked.zpow |a| p (fun hp => (h hp).map (absHom : α →*₀ α)) := by
  cases p with
  | ofNat k => exact abs_pow a k
  | negSucc k =>
    calc
      _ = |Checked.inv a (h (Int.negSucc_lt_zero k)) ^ (k + 1)| :=
        congrArg abs (Checked.zpow_negSucc a k h)
      _ = |Checked.inv a (h (Int.negSucc_lt_zero k))| ^ (k + 1) := abs_pow _ _
      _ = Checked.inv |a| ((h (Int.negSucc_lt_zero k)).map (absHom : α →*₀ α)) ^ (k + 1) :=
        congrArg (fun x : α => x ^ (k + 1)) (abs_inv a (h (Int.negSucc_lt_zero k)))
      _ = _ := (Checked.zpow_negSucc |a| k
        (fun hn => (h hn).map (absHom : α →*₀ α))).symm

theorem abs_neg_one_zpow (p : ℤ) :
    |Checked.zpow (-1 : α) p (fun _ => isUnit_neg_one)| = 1 := by
  rw [abs_zpow]
  simpa only [abs_neg, abs_one] using Checked.zpow_one p _

end LinearOrderedField

/-- Absolute value preserves invertibility because it equals the original value or its negative. -/
theorem IsUnit.abs {R : Type*} [Ring R] [LinearOrder R] {a : R} (ha : IsUnit a) : IsUnit |a| := by
  rcases abs_choice a with h | h
  · exact h.symm ▸ ha
  · exact h.symm ▸ ha.neg

namespace Checked

theorem zpow_neg_of_even {R : Type*} [Ring R] {n : ℤ} (hn : Even n) (a : R)
    (h : n < 0 → IsUnit a) (hneg : n < 0 → IsUnit (-a)) :
    zpow (-a) n hneg = zpow a n h := by
  cases n with
  | ofNat k => exact ((Int.even_coe_nat k).mp hn).neg_pow a
  | negSucc k =>
    change Even (-(↑(k + 1) : ℤ)) at hn
    have hk : Even (k + 1) := (Int.even_coe_nat (k + 1)).mp (even_neg.mp hn)
    rw [zpow_negSucc, zpow_negSucc, inv_neg a (h (Int.negSucc_lt_zero k))]
    exact hk.neg_pow _

end Checked

section LinearOrderedField
variable [Field α] [LinearOrder α] {a b : α} {n : ℤ}

theorem Even.zpow_abs {p : ℤ} (hp : Even p) (a : α) (h : p < 0 → IsUnit a) :
    Checked.zpow |a| p (fun hn => (h hn).abs) = Checked.zpow a p h := by
  rcases abs_choice a with ha | ha
  · exact Checked.zpow_congr ha p (fun hn => (h hn).abs) h
  · exact (Checked.zpow_congr ha p (fun hn => (h hn).abs) (fun hn => (h hn).neg)).trans
      (Checked.zpow_neg_of_even hp a h (fun hn => (h hn).neg))

variable [IsStrictOrderedRing α]

lemma zpow_eq_zpow_iff_of_ne_zero₀ (hn : n ≠ 0)
    (ha : n < 0 → IsUnit a) (hb : n < 0 → IsUnit b) :
    Checked.zpow a n ha = Checked.zpow b n hb ↔ a = b ∨ a = -b ∧ Even n := by
  cases n with
  | ofNat k =>
    have hk : k ≠ 0 := by intro hk; subst k; exact hn rfl
    change a ^ k = b ^ k ↔ a = b ∨ a = -b ∧ Even (Int.ofNat k)
    simpa only [Int.ofNat_eq_natCast, Int.even_coe_nat] using
      (pow_eq_pow_iff_of_ne_zero hk : a ^ k = b ^ k ↔ a = b ∨ a = -b ∧ Even k)
  | negSucc k =>
    have he : Even (Int.negSucc k) ↔ Even (k + 1) := by
      change Even (-(↑(k + 1) : ℤ)) ↔ _
      rw [even_neg, Int.even_coe_nat]
    rw [Checked.zpow_negSucc, Checked.zpow_negSucc,
      pow_eq_pow_iff_of_ne_zero (Nat.succ_ne_zero k),
      ← Checked.inv_neg b (hb (Int.negSucc_lt_zero k))
        (hneg := (hb (Int.negSucc_lt_zero k)).neg), Checked.inv_inj, Checked.inv_inj, he]

lemma zpow_eq_zpow_iff_cases₀ (ha : n < 0 → IsUnit a) (hb : n < 0 → IsUnit b) :
    Checked.zpow a n ha = Checked.zpow b n hb ↔ n = 0 ∨ a = b ∨ a = -b ∧ Even n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [Checked.zpow_zero, true_or, eq_self]
  · rw [zpow_eq_zpow_iff_of_ne_zero₀ hn ha hb]
    simp only [hn, false_or]

lemma zpow_eq_one_iff_of_ne_zero₀ (hn : n ≠ 0) (ha : n < 0 → IsUnit a) :
    Checked.zpow a n ha = 1 ↔ a = 1 ∨ a = -1 ∧ Even n := by
  simpa only [Checked.zpow_one] using
    (zpow_eq_zpow_iff_of_ne_zero₀ (a := a) (b := 1) hn ha (fun _ => isUnit_one))

lemma zpow_eq_one_iff_cases₀ (ha : n < 0 → IsUnit a) :
    Checked.zpow a n ha = 1 ↔ n = 0 ∨ a = 1 ∨ a = -1 ∧ Even n := by
  simpa only [Checked.zpow_one] using
    (zpow_eq_zpow_iff_cases₀ (a := a) (b := 1) ha (fun _ => isUnit_one))

lemma zpow_eq_neg_zpow_iff₀ (hb0 : b ≠ 0)
    (ha : n < 0 → IsUnit a) (hb : n < 0 → IsUnit b) :
    Checked.zpow a n ha = -Checked.zpow b n hb ↔ a = -b ∧ Odd n := by
  cases n with
  | ofNat k =>
    change a ^ k = -b ^ k ↔ a = -b ∧ Odd (Int.ofNat k)
    simpa only [Int.ofNat_eq_natCast, Int.odd_coe_nat] using
      (pow_eq_neg_pow_iff hb0 : a ^ k = -b ^ k ↔ a = -b ∧ Odd k)
  | negSucc k =>
    have ho : Odd (Int.negSucc k) ↔ Odd (k + 1) := by
      change Odd (-(↑(k + 1) : ℤ)) ↔ _
      rw [odd_neg, Int.odd_coe_nat]
    rw [Checked.zpow_negSucc, Checked.zpow_negSucc,
      pow_eq_neg_pow_iff (Checked.inv_ne_zero (ha := hb (Int.negSucc_lt_zero k))),
      ← Checked.inv_neg b (hb (Int.negSucc_lt_zero k))
        (hneg := (hb (Int.negSucc_lt_zero k)).neg), Checked.inv_inj, ho]

lemma zpow_eq_neg_one_iff₀ (ha : n < 0 → IsUnit a) :
    Checked.zpow a n ha = -1 ↔ a = -1 ∧ Odd n := by
  simpa only [Checked.zpow_one] using
    (zpow_eq_neg_zpow_iff₀ (a := a) (b := 1) one_ne_zero ha (fun _ => isUnit_one))

/-- Bernoulli's inequality reformulated to estimate a natural-number cast. -/
theorem Nat.cast_le_pow_sub_div_sub (H : 1 < a) (n : ℕ) :
    (n : α) ≤ (a ^ n - 1) /ₚ Units.mk0 (a - 1) (sub_pos.mpr H).ne' :=
  (le_divp_iff (sub_pos.mpr H)).mpr <|
    le_sub_left_of_add_le <| one_add_mul_sub_le_pow ((neg_le_self zero_le_one).trans H.le) _

/-- A weaker form of Bernoulli's inequality with the full power in the numerator. -/
theorem Nat.cast_le_pow_div_sub (H : 1 < a) (n : ℕ) :
    (n : α) ≤ a ^ n /ₚ Units.mk0 (a - 1) (sub_pos.mpr H).ne' :=
  (n.cast_le_pow_sub_div_sub H).trans <|
    divp_le_divp_of_nonneg_right (sub_le_self _ zero_le_one) (sub_pos.mpr H).le

end LinearOrderedField

namespace Mathlib.Meta.Positivity
open Lean Meta Qq

/-- Positivity of integer powers with their original negative-exponent obligation retained. -/
@[positivity Checked.zpow _ _ _]
meta def evalZPow : PositivityExt where eval {u α} zα pα? e := do
  unless e.isAppOfArity ``Checked.zpow 5 do throwError "not a checked integer power"
  let _a ← synthInstanceQ q(GroupWithZero $α)
  assumeInstancesCommute
  let .app (.app (.app _ (a : Q($α))) (b : Q(ℤ))) (h : Q($b < 0 → IsUnit $a)) := e
    | throwError "not a checked integer power"
  haveI' : $e =Q Checked.zpow $a $b $h := ⟨⟩
  match (dependent := true) pα? with
  | none =>
    match ← catchNone (core zα pα? a) with
    | .nonzero pa => pure (.nonzero q(Checked.zpow_ne_zero $pa $b $h))
    | _ => pure .none
  | some pα =>
    let result ← catchNone do
      let _a ← synthInstanceQ q(Field $α)
      let _a ← synthInstanceQ q(LinearOrder $α)
      let _a ← synthInstanceQ q(IsStrictOrderedRing $α)
      assumeInstancesCommute
      match ← whnfR b with
      | .app (.app (.app (.const `OfNat.ofNat _) _) (.lit (Literal.natVal n))) _ =>
        guard (n % 2 = 0)
        have m : Q(ℕ) := mkRawNatLit (n / 2)
        haveI' : $b =Q $m + $m := ⟨⟩
        pure (.nonnegative q(Even.zpow_nonneg (Even.add_self _) $a $h))
      | .app (.app (.app (.const `Neg.neg _) _) _) b' =>
        let b' ← whnfR b'
        let .true := b'.isAppOfArity ``OfNat.ofNat 3 | throwError "not a literal negative exponent"
        let some n := (b'.getRevArg! 1).rawNatLit? | throwError "not a literal negative exponent"
        guard (n % 2 = 0)
        have m : Q(ℕ) := mkRawNatLit (n / 2)
        haveI' : $b =Q (-$m) + (-$m) := ⟨⟩
        pure (.nonnegative q(Even.zpow_nonneg (Even.add_self _) $a $h))
      | _ => throwError "not an even literal exponent"
    orElse result do
      let ra ← catchNone (core zα pα a)
      match ra with
      | .positive pa =>
        let _a ← synthInstanceQ q(Semifield $α)
        let _a ← synthInstanceQ q(LinearOrder $α)
        let _a ← synthInstanceQ q(IsStrictOrderedRing $α)
        assumeInstancesCommute
        pure (.positive q(Checked.zpow_pos $pa $b $h))
      | .nonnegative pa =>
        let _a ← synthInstanceQ q(Semifield $α)
        let _a ← synthInstanceQ q(LinearOrder $α)
        let _a ← synthInstanceQ q(IsStrictOrderedRing $α)
        assumeInstancesCommute
        pure (.nonnegative q(Checked.zpow_nonneg $pa $b $h))
      | .nonzero pa => pure (.nonzero q(Checked.zpow_ne_zero $pa $b $h))
      | .none => pure .none

end Mathlib.Meta.Positivity
