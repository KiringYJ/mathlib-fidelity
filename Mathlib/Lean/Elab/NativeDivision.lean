/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Init.Data.Int.DivMod.Lemmas
public meta import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linter.Header

/-!
# Natural and integer quotients

The natural and integer Euclidean quotients take a nonzero divisor. The exact integer quotient
also takes evidence that the divisor divides the dividend.
-/

public section

/-- Discharge a nonzero divisor condition in the foundational arithmetic layer. -/
syntax (name := checkedNativeNonzero) "checked_native_nonzero" : tactic

macro_rules
  | `(tactic| checked_native_nonzero) => `(tactic|
      first
      | done
      | assumption
      | exact Nat.succ_ne_zero _
      | decide
      | omega
      | fail "a nonzero divisor proof is required")

namespace Nat

/-- Recover the quotient from its complement modulo one more than the dividend. -/
private def euclideanDivFromMod (a b : Nat) (_hb : b ≠ 0) : Nat :=
  let c := a + 1
  a - ((c * a + a) % (c * b + 1)) % c

private theorem euclideanDivFromMod_eq (a b q r : Nat) (hq : q ≤ a) (hr : r < b)
    (he : b * q + r = a) :
    euclideanDivFromMod a b (Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le r) hr)) = q := by
  let c := a + 1
  have hsmall : a - q < c := Nat.lt_succ_of_le (Nat.sub_le ..)
  have hbound : c * r + (a - q) < c * b + 1 := by
    have h := Nat.mul_le_mul_left c hr
    rw [Nat.mul_succ] at h
    omega
  have hrepr : (c * b + 1) * q + (c * r + (a - q)) = c * a + a := by
    have h := congrArg (c * ·) he
    simp only [Nat.mul_add, ← Nat.mul_assoc] at h
    rw [Nat.add_mul, Nat.one_mul]
    omega
  change a - ((c * a + a) % (c * b + 1)) % c = q
  rw [← hrepr, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hbound, Nat.mul_add_mod_self_left,
    Nat.mod_eq_of_lt hsmall, Nat.sub_sub_self hq]

private def euclideanDivRemainder (a b : Nat) (hb : b ≠ 0) :
    { qr : Nat × Nat // b * qr.1 + qr.2 = a ∧ qr.2 < b } :=
  ⟨(euclideanDivFromMod a b hb, a % b),
    (congrArg (fun q ↦ b * q + a % b) (euclideanDivFromMod_eq a b _ _ (Nat.div_le_self a b)
      (Nat.mod_lt a (Nat.pos_of_ne_zero hb)) (Nat.div_add_mod a b))).trans (Nat.div_add_mod a b),
    Nat.mod_lt a (Nat.pos_of_ne_zero hb)⟩

/-- The Euclidean quotient of `a` by a nonzero natural number `b`. -/
def euclideanDiv (a b : Nat) (hb : b ≠ 0 := by checked_native_nonzero) : Nat :=
  (euclideanDivRemainder a b hb).val.1

private theorem euclideanDiv_le_of_remainder_eq {a b q q' r r' : Nat}
    (h : b * q + r = a) (h' : b * q' + r' = a) (hr' : r' < b) : q ≤ q' := by
  by_cases hqq' : q ≤ q'
  · exact hqq'
  · have hmul := Nat.mul_le_mul_left b (by omega : q' + 1 ≤ q)
    rw [Nat.mul_add, Nat.mul_one] at hmul
    omega

/-- The reconstruction and remainder bound determine the natural quotient. -/
theorem euclideanDiv_eq_of_remainder {a b q r : Nat} (hb : b ≠ 0)
    (h : a = b * q + r) (hr : r < b) : euclideanDiv a b hb = q := by
  let result := euclideanDivRemainder a b hb
  exact Nat.le_antisymm (euclideanDiv_le_of_remainder_eq result.property.1 h.symm hr)
    (euclideanDiv_le_of_remainder_eq h.symm result.property.1 result.property.2)

end Nat

/-- Prove agreement with Lean's natural quotient for a nonzero divisor.
The expansion uses the official Euclidean lemmas in the proof that requests it. -/
macro "Nat.euclideanDiv_eq_core" : term =>
  `(fun (a b : Nat) (hb : b ≠ 0) =>
    (show Nat.euclideanDiv a b hb = @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a b from
      Nat.euclideanDiv_eq_of_remainder hb (Nat.div_add_mod a b).symm
        (Nat.mod_lt a (Nat.pos_of_ne_zero hb))))

namespace Nat

/-- A nonzero divisor times its quotient, plus the remainder, recovers the dividend. -/
theorem euclideanDiv_mul_add_mod (a b : Nat) (hb : b ≠ 0) :
    b * euclideanDiv a b hb + a % b = a := by
  let qr := euclideanDivRemainder a b hb
  have hr : qr.val.2 = a % b := by
    simpa only [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt qr.property.2]
      using congrArg (fun x => x % b) qr.property.1
  change b * qr.val.1 + a % b = a
  exact hr ▸ qr.property.1

/-- Cancel a nonzero right factor in the Euclidean quotient. -/
@[simp] theorem euclideanDiv_mul_right_cancel (a : Nat) {b : Nat} (hb : b ≠ 0) :
    euclideanDiv (a * b) b hb = a :=
  euclideanDiv_eq_of_remainder (r := 0) hb (by simp [Nat.mul_comm]) (Nat.pos_of_ne_zero hb)

/-- Cancel a nonzero left factor in the Euclidean quotient. -/
@[simp] theorem euclideanDiv_mul_left_cancel (a : Nat) {b : Nat} (hb : b ≠ 0) :
    euclideanDiv (b * a) b hb = a :=
  euclideanDiv_eq_of_remainder (r := 0) hb (by simp) (Nat.pos_of_ne_zero hb)

end Nat

namespace Int

/-- The Euclidean quotient of `a` by `b`, with nonnegative remainder less than `b.natAbs`. -/
@[expose] def euclideanDiv (a b : Int) (hb : b ≠ 0 := by checked_native_nonzero) : Int :=
  match a, b, hb with
  | _, .ofNat 0, h => False.elim (h rfl)
  | .ofNat m, .ofNat (.succ n), _ => .ofNat (Nat.euclideanDiv m n.succ (Nat.succ_ne_zero _))
  | .ofNat m, .negSucc n, _ => -ofNat (Nat.euclideanDiv m n.succ (Nat.succ_ne_zero _))
  | .negSucc m, .ofNat (.succ n), _ => .negSucc (Nat.euclideanDiv m n.succ (Nat.succ_ne_zero _))
  | .negSucc m, .negSucc n, _ => .ofNat (Nat.euclideanDiv m n.succ (Nat.succ_ne_zero _)).succ

end Int

/-- Prove agreement with Lean's integer quotient for a nonzero divisor.
The signed cases use the agreement theorem for natural quotients. -/
macro "Int.euclideanDiv_eq_core" : term =>
  `(fun (a b : Int) (hb : b ≠ 0) =>
    (show Int.euclideanDiv a b hb = @HDiv.hDiv Int Int Int (@instHDiv Int Int.instDiv) a b from by
      change Int.euclideanDiv a b hb = Int.ediv a b
      cases b with
      | ofNat n =>
        cases n with
        | zero => exact (hb rfl).elim
        | succ n => cases a <;> simp only [Int.euclideanDiv, Int.ediv, Nat.euclideanDiv_eq_core]
      | negSucc n => cases a <;> simp only [Int.euclideanDiv, Int.ediv, Nat.euclideanDiv_eq_core]))

namespace Int

/-- A nonzero divisor times its quotient, plus the remainder, recovers the dividend. -/
theorem euclideanDiv_mul_add_mod (a b : Int) (hb : b ≠ 0) :
    b * euclideanDiv a b hb + a % b = a := by
  change b * euclideanDiv a b hb + Int.emod a b = a
  rcases b with (_ | n) | n
  · exact (hb rfl).elim
  all_goals cases a <;> rename_i m
  all_goals
    have h := congrArg Int.ofNat (Nat.euclideanDiv_mul_add_mod m n.succ (Nat.succ_ne_zero _))
    simp only [Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_mul, Int.natCast_succ] at h
    simp only [euclideanDiv, Int.emod, Int.natAbs, Int.subNatNat_eq_coe, Int.negSucc_eq,
      Int.ofNat_eq_natCast, Int.natCast_succ, Int.neg_mul, Int.mul_neg, Int.mul_add, Int.mul_one]
    simp only [Nat.succ_eq_add_one] at h ⊢
    omega

/-- The reconstruction and the nonnegative remainder bound determine the integer quotient. -/
theorem euclideanDiv_eq_of_remainder {a b q r : Int} (hb : b ≠ 0)
    (h : a = b * q + r) (hr₀ : 0 ≤ r) (hr : r < (b.natAbs : Int)) : euclideanDiv a b hb = q := by
  have hmod : a % b = r := by
    refine (Int.emod_eq_iff hb).2 ⟨hr₀, hr, -q, ?_⟩
    rw [h, Int.mul_neg]
    omega
  have hq := euclideanDiv_mul_add_mod a b hb
  rw [hmod] at hq
  exact Int.eq_of_mul_eq_mul_left hb (by omega)

/-- The unique integer `q` with `b * q = a` when `b` is nonzero and divides `a`. -/
@[expose] def exactQuotient (a b : Int) (_h : b ∣ a)
    (hb : b ≠ 0 := by checked_native_nonzero) : Int :=
  euclideanDiv a b hb

/-- Multiplication by the divisor recovers the dividend from the exact quotient. -/
theorem mul_exactQuotient (a b : Int) (h : b ∣ a) (hb : b ≠ 0) :
    b * exactQuotient a b h hb = a := by
  simpa only [exactQuotient, Int.dvd_iff_emod_eq_zero.mp h, Int.add_zero]
    using euclideanDiv_mul_add_mod a b hb

/-- The exact quotient is characterized by multiplication by the nonzero divisor. -/
theorem exactQuotient_eq_iff {a b q : Int} (h : b ∣ a) (hb : b ≠ 0) :
    exactQuotient a b h hb = q ↔ b * q = a := by
  constructor
  · rintro rfl
    exact mul_exactQuotient a b h hb
  · intro hq
    exact Int.eq_of_mul_eq_mul_left hb ((mul_exactQuotient a b h hb).trans hq.symm)

end Int
