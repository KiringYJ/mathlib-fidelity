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
# Lemmas about powers in ordered fields.

An integer power `a ^ n` is defined when `n` is nonnegative or `a` is invertible. The lemmas take
the evidence carried by the powers in their statements as implicit arguments, or derive it from a
hypothesis such as `a ≠ 0`.
-/

public section


variable {α : Type*}

open Function Int

section LinearOrderedField

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a b : α} {n : ℤ}

protected theorem Even.zpow_nonneg (hn : Even n) (a : α) {ha : n < 0 → IsUnit a} :
    0 ≤ a ^ n := by
  obtain ⟨k, rfl⟩ := hn
  have hk : k < 0 → IsUnit a := fun hk ↦ ha (by omega)
  rw [zpow_add' (h₂ := hk) (h₃ := hk)]
  exact mul_self_nonneg _

lemma zpow_two_nonneg (a : α) : 0 ≤ a ^ (2 : ℤ) := even_two.zpow_nonneg _

lemma zpow_neg_two_nonneg (a : α) {ha : (-2 : ℤ) < 0 → IsUnit a} : 0 ≤ a ^ (-2 : ℤ) :=
  even_neg_two.zpow_nonneg _

protected lemma Even.zpow_pos (hn : Even n) (ha : a ≠ 0) : 0 < a ^ n :=
  (hn.zpow_nonneg _).lt_of_ne' (zpow_ne_zero _ ha)

lemma zpow_two_pos_of_ne_zero (ha : a ≠ 0) : 0 < a ^ (2 : ℤ) := even_two.zpow_pos ha

theorem Even.zpow_pos_iff {ha : n < 0 → IsUnit a} (hn : Even n) (h : n ≠ 0) :
    0 < a ^ n ↔ a ≠ 0 := by
  obtain ⟨k, rfl⟩ := hn
  have hk : k < 0 → IsUnit a := fun hk ↦ ha (by omega)
  rw [zpow_add' (h₂ := hk) (h₃ := hk), mul_self_pos, zpow_ne_zero_iff (by simpa using h)]

theorem Odd.zpow_neg_iff {ha : n < 0 → IsUnit a} (hn : Odd n) : a ^ n < 0 ↔ a < 0 := by
  refine ⟨lt_imp_lt_of_le_imp_le (zpow_nonneg · _), fun ha₀ ↦ ?_⟩
  obtain ⟨k, rfl⟩ := hn
  rw [zpow_add_one₀ ha₀.ne]
  exact mul_neg_of_pos_of_neg (Even.zpow_pos (even_two_mul _) ha₀.ne) ha₀

protected lemma Odd.zpow_nonneg_iff {ha : n < 0 → IsUnit a} (hn : Odd n) : 0 ≤ a ^ n ↔ 0 ≤ a :=
  le_iff_le_iff_lt_iff_lt.2 hn.zpow_neg_iff

theorem Odd.zpow_nonpos_iff {ha : n < 0 → IsUnit a} (hn : Odd n) : a ^ n ≤ 0 ↔ a ≤ 0 := by
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq, hn.zpow_neg_iff, zpow_eq_zero_iff]
  rintro rfl
  exact Int.not_even_iff_odd.2 hn .zero

lemma Odd.zpow_pos_iff {ha : n < 0 → IsUnit a} (hn : Odd n) : 0 < a ^ n ↔ 0 < a :=
  lt_iff_lt_of_le_iff_le hn.zpow_nonpos_iff

alias ⟨_, Odd.zpow_neg⟩ := Odd.zpow_neg_iff

alias ⟨_, Odd.zpow_nonpos⟩ := Odd.zpow_nonpos_iff

@[simp]
theorem abs_zpow (a : α) (p : ℤ) {h : p < 0 → IsUnit a} :
    |a ^ p| = Checked.zpow |a| p fun hp ↦ (abs_pos.mpr (h hp).ne_zero).ne'.isUnit :=
  map_zpow₀ absHom a p

theorem abs_neg_one_zpow (p : ℤ) : |(-1 : α) ^ p| = 1 := by simp

omit [IsStrictOrderedRing α] in
theorem Even.zpow_abs {p : ℤ} (hp : Even p) (a : α) {h : p < 0 → IsUnit |a|} :
    |a| ^ p = Checked.zpow a p fun hn ↦
      (abs_choice a).elim (fun e ↦ e ▸ h hn) fun e ↦ (IsUnit.neg_iff a).mp (e ▸ h hn) := by
  rcases abs_choice a with e | e <;> simp only [e, hp.neg_zpow₀]

lemma zpow_eq_zpow_iff_of_ne_zero₀ {ha : n < 0 → IsUnit a} {hb : n < 0 → IsUnit b} (hn : n ≠ 0) :
    a ^ n = b ^ n ↔ a = b ∨ a = -b ∧ Even n := by
  cases n with
  | ofNat m =>
    simp only [Int.ofNat_eq_natCast, ne_eq, Nat.cast_eq_zero, zpow_natCast₀,
      Int.even_coe_nat] at *
    exact pow_eq_pow_iff_of_ne_zero hn
  | negSucc m =>
    have he : Even (Int.negSucc m) ↔ Even (m + 1) := by
      change Even (-(↑(m + 1) : ℤ)) ↔ _
      rw [even_neg, Int.even_coe_nat]
    rw [zpow_negSucc₀, zpow_negSucc₀, inv_inj₀, pow_eq_pow_iff_of_ne_zero m.succ_ne_zero, he]

lemma zpow_eq_zpow_iff_cases₀ {ha : n < 0 → IsUnit a} {hb : n < 0 → IsUnit b} :
    a ^ n = b ^ n ↔ n = 0 ∨ a = b ∨ a = -b ∧ Even n := by
  rcases eq_or_ne n 0 with rfl | hn <;> simp [zpow_eq_zpow_iff_of_ne_zero₀, *]

lemma zpow_eq_one_iff_of_ne_zero₀ {ha : n < 0 → IsUnit a} (hn : n ≠ 0) :
    a ^ n = 1 ↔ a = 1 ∨ a = -1 ∧ Even n := by
  simpa using zpow_eq_zpow_iff_of_ne_zero₀ (b := 1) (ha := ha) (hb := fun _ ↦ isUnit_one) hn

lemma zpow_eq_one_iff_cases₀ {ha : n < 0 → IsUnit a} :
    a ^ n = 1 ↔ n = 0 ∨ a = 1 ∨ a = -1 ∧ Even n := by
  simpa using zpow_eq_zpow_iff_cases₀ (b := 1) (ha := ha) (hb := fun _ ↦ isUnit_one)

lemma zpow_eq_neg_zpow_iff₀ {ha : n < 0 → IsUnit a} (hb : b ≠ 0) :
    a ^ n = -b ^ n ↔ a = -b ∧ Odd n := by
  cases n with
  | ofNat m => simp [pow_eq_neg_pow_iff, hb]
  | negSucc m =>
    have ho : Odd (Int.negSucc m) ↔ Odd (m + 1) := by
      change Odd (-(↑(m + 1) : ℤ)) ↔ _
      rw [odd_neg, Int.odd_coe_nat]
    rw [zpow_negSucc₀, zpow_negSucc₀, neg_inv₀, inv_inj₀, pow_eq_neg_pow_iff hb, ho]

lemma zpow_eq_neg_one_iff₀ {ha : n < 0 → IsUnit a} : a ^ n = -1 ↔ a = -1 ∧ Odd n := by
  simpa using zpow_eq_neg_zpow_iff₀ (b := 1) (ha := ha) one_ne_zero

/-! ### Bernoulli's inequality -/

/-- Bernoulli's inequality reformulated to estimate `(n : α)`. -/
theorem Nat.cast_le_pow_sub_div_sub (H : 1 < a) (n : ℕ) : (n : α) ≤ (a ^ n - 1) / (a - 1) :=
  (le_div_iff₀ (sub_pos.2 H)).2 <|
    le_sub_left_of_add_le <| one_add_mul_sub_le_pow ((neg_le_self zero_le_one).trans H.le) _

/-- For any `a > 1` and a natural `n` we have `n ≤ a ^ n / (a - 1)`. See also
`Nat.cast_le_pow_sub_div_sub` for a stronger inequality with `a ^ n - 1` in the numerator. -/
theorem Nat.cast_le_pow_div_sub (H : 1 < a) (n : ℕ) : (n : α) ≤ a ^ n / (a - 1) :=
  (n.cast_le_pow_sub_div_sub H).trans <|
    div_le_div_of_nonneg_right (sub_le_self _ zero_le_one) (sub_nonneg.2 H.le)

end LinearOrderedField

namespace Mathlib.Meta.Positivity
open Lean Meta Qq

/-- The `positivity` extension which identifies expressions of the form `a ^ (b : ℤ)`,
such that `positivity` successfully recognises both `a` and `b`. The power carries the evidence
that `a` is invertible when `b` is negative. -/
@[positivity Checked.zpow _ _ _]
meta def evalZPow : PositivityExt where eval {u α} zα pα? e := do
  let e' ← withReducible (whnf e)
  unless e'.isAppOfArity ``Checked.zpow 5 do throwError "not ^"
  let _a ← synthInstanceQ q(GroupWithZero $α)
  assumeInstancesCommute
  let .app (.app (.app _ (a : Q($α))) (b : Q(ℤ))) (h : Q($b < 0 → IsUnit $a)) := e'
    | throwError "not ^"
  haveI' : $e =Q Checked.zpow $a $b $h := ⟨⟩
  match (dependent := true) pα? with
  | none =>
    match ← core zα pα? a with
    | .nonzero pa => pure (.nonzero q(zpow_ne_zero $b $pa))
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
        pure (.nonnegative q(Even.zpow_nonneg (Even.add_self _) $a (ha := $h)))
      | .app (.app (.app (.const `Neg.neg _) _) _) b' =>
        let b' ← whnfR b'
        let .true := b'.isAppOfArity ``OfNat.ofNat 3 | throwError "not a ^ -n where n is a literal"
        let some n := (b'.getRevArg! 1).rawNatLit? | throwError "not a ^ -n where n is a literal"
        guard (n % 2 = 0)
        have m : Q(ℕ) := mkRawNatLit (n / 2)
        haveI' : $b =Q (-$m) + (-$m) := ⟨⟩
        pure (.nonnegative q(Even.zpow_nonneg (Even.add_self _) $a (ha := $h)))
      | _ => throwError "not a ^ n where n is a literal or a negated literal"
    orElse result do
      let ra ← core zα pα a
      match ra with
      | .positive pa =>
        try
          let _a ← synthInstanceQ q(Semifield $α)
          let _a ← synthInstanceQ q(LinearOrder $α)
          let _a ← synthInstanceQ q(IsStrictOrderedRing $α)
          assumeInstancesCommute
          pure (.positive q(zpow_pos $pa $b))
        catch e : Exception =>
          trace[Tactic.positivity.failure] "{e.toMessageData}"
          pure (.nonzero q(zpow_ne_zero $b (ne_of_gt $pa)))
      | .nonnegative pa =>
        let _a ← synthInstanceQ q(Semifield $α)
        let _a ← synthInstanceQ q(LinearOrder $α)
        let _a ← synthInstanceQ q(IsStrictOrderedRing $α)
        assumeInstancesCommute
        pure (.nonnegative q(zpow_nonneg $pa $b (h := $h)))
      | .nonzero pa => pure (.nonzero q(zpow_ne_zero $b $pa))
      | .none => pure .none

end Mathlib.Meta.Positivity
