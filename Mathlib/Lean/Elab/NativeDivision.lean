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

For a nonzero divisor `b`, `Nat.euclideanDiv` and `Int.euclideanDiv` give the unique quotient
`q` satisfying `b * q + r = a` with `0 ≤ r < |b|`. The natural and integer
`euclideanDiv_eq_of_remainder` theorems express this uniqueness. `Int.exactQuotient` gives the
unique integer `q` with `b * q = a`, using `b ≠ 0` and `b ∣ a`.

The remainder `a % b` chooses the representative of `a + bℤ` in `[0, |b|)` for `b ≠ 0`, viewing
natural numbers in `ℤ` when necessary. At divisor zero the class is a singleton, so `a % 0 = a`.
The reconstruction equation at `b = 0` determines the remainder and leaves the quotient
undetermined.

## Implementation notes

The natural quotient is computed from a remainder. Set `c = a + 1` and
`s = (c * a + a) % (c * b + 1)`. If `a = b * q + r` with `r < b` and `b ≠ 0`, then `q ≤ a`
and `s = c * r + (a - q)`. Hence `a - s % c = q`. The reconstruction proof uses induction
on the remainder algorithm.

## References

* [Graham, Knuth, and Patashnik, *Concrete Mathematics*, §3.4, equation (3.22)][GKP]
  gives the zero-modulus convention.
* [Rijke, *Lecture Notes on Number Theory*, Remark 9.1.4][Rijke] explains congruence modulo zero.

[GKP]: https://ptgmedia.pearsoncmg.com/images/9780201558029/samplepages/9780201558029.pdf#page=32
[Rijke]: https://egbertrijke.github.io/jhu-number-theory-spring-2025.pdf#page=96
-/

public section

/-- Discharge a nonzero divisor condition in the foundational arithmetic layer. -/
syntax (name := checkedNativeNonzero) "checked_native_nonzero" : tactic

macro_rules
  | `(tactic| checked_native_nonzero) => `(tactic|
      first
      | done
      | · repeat' first
            | assumption
            | exact Nat.succ_ne_zero _
            | decide
            | apply Nat.mul_ne_zero
            | apply Int.mul_ne_zero
            | omega
          done
      | fail "a nonzero divisor proof is required")

namespace Nat

/-- The Euclidean quotient of `a` by a nonzero natural number `b`. The quotient is
computed from its complement modulo one more than the dividend. -/
@[expose] def euclideanDiv (a b : Nat) (hb : b ≠ 0 := by checked_native_nonzero) : Nat :=
  have _ := hb
  let c := a + 1
  a - ((c * a + a) % (c * b + 1)) % c

private theorem euclideanDiv_eq_of_mul_add_eq (a b q r : Nat) (hq : q ≤ a) (hr : r < b)
    (he : b * q + r = a) :
    euclideanDiv a b (Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le r) hr)) = q := by
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

private theorem exists_mul_add_mod (a b : Nat) (hb : b ≠ 0) :
    ∃ q ≤ a, b * q + a % b = a := by
  induction a, b using Nat.mod.inductionOn with
  | base a b h =>
    have hab : a < b := Nat.lt_of_not_ge fun hab => h ⟨Nat.pos_of_ne_zero hb, hab⟩
    exact ⟨0, Nat.zero_le _, by rw [Nat.mul_zero, Nat.zero_add, Nat.mod_eq_of_lt hab]⟩
  | ind a b h ih =>
    obtain ⟨q, hq, he⟩ := ih hb
    have hlt := Nat.sub_lt (Nat.lt_of_lt_of_le h.1 h.2) h.1
    refine ⟨q + 1, Nat.succ_le_of_lt (Nat.lt_of_le_of_lt hq hlt), ?_⟩
    rw [Nat.mod_eq_sub_mod h.2, Nat.mul_succ, Nat.add_right_comm, he, Nat.sub_add_cancel h.2]

/-- A nonzero divisor times its quotient, plus the remainder, recovers the dividend. -/
theorem euclideanDiv_mul_add_mod (a b : Nat) (hb : b ≠ 0) :
    b * euclideanDiv a b hb + a % b = a := by
  have hr := Nat.mod_lt a (Nat.pos_of_ne_zero hb)
  obtain ⟨q, hq, he⟩ := exists_mul_add_mod a b hb
  rw [euclideanDiv_eq_of_mul_add_eq a b q (a % b) hq hr he, he]

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
  have hrec := euclideanDiv_mul_add_mod a b hb
  exact Nat.le_antisymm (euclideanDiv_le_of_remainder_eq hrec h.symm hr)
    (euclideanDiv_le_of_remainder_eq h.symm hrec (Nat.mod_lt _ (Nat.pos_of_ne_zero hb)))

/-- A natural number is at most the quotient iff multiplying by the divisor
gives a number at most the dividend. -/
theorem le_euclideanDiv_iff_mul_le {a b k : Nat} (hb : b ≠ 0) :
    k ≤ euclideanDiv a b hb ↔ b * k ≤ a := by
  constructor
  · intro h
    calc
      b * k ≤ b * euclideanDiv a b hb := Nat.mul_le_mul_left _ h
      _ ≤ b * euclideanDiv a b hb + a % b := Nat.le_add_right _ _
      _ = a := euclideanDiv_mul_add_mod a b hb
  · intro h
    apply Nat.lt_succ_iff.mp
    apply Nat.lt_of_mul_lt_mul_left
    calc
      b * k ≤ a := h
      _ = b * euclideanDiv a b hb + a % b := (euclideanDiv_mul_add_mod a b hb).symm
      _ < b * euclideanDiv a b hb + b := Nat.add_lt_add_left (Nat.mod_lt _ (Nat.pos_of_ne_zero hb)) _
      _ = b * (euclideanDiv a b hb).succ := (Nat.mul_succ _ _).symm

/-- Cancel a nonzero right factor in the Euclidean quotient. -/
@[simp] theorem euclideanDiv_mul_right_cancel (a : Nat) {b : Nat} (hb : b ≠ 0) :
    euclideanDiv (a * b) b hb = a :=
  euclideanDiv_eq_of_remainder (r := 0) hb (by simp [Nat.mul_comm]) (Nat.pos_of_ne_zero hb)

/-- Cancel a nonzero left factor in the Euclidean quotient. -/
@[simp] theorem euclideanDiv_mul_left_cancel (a : Nat) {b : Nat} (hb : b ≠ 0) :
    euclideanDiv (b * a) b hb = a :=
  euclideanDiv_eq_of_remainder (r := 0) hb (by simp) (Nat.pos_of_ne_zero hb)

@[simp] theorem euclideanDiv_zero (b : Nat) (hb : b ≠ 0) : euclideanDiv 0 b hb = 0 := by
  simpa only [Nat.mul_zero] using euclideanDiv_mul_left_cancel 0 hb

@[simp] theorem euclideanDiv_one (a : Nat) : euclideanDiv a 1 Nat.one_ne_zero = a := by
  simpa only [Nat.one_mul] using euclideanDiv_mul_left_cancel a Nat.one_ne_zero

@[simp] theorem euclideanDiv_self (a : Nat) (ha : a ≠ 0) : euclideanDiv a a ha = 1 := by
  simpa only [Nat.mul_one] using euclideanDiv_mul_left_cancel 1 ha

theorem euclideanDiv_eq_zero_of_lt {a b : Nat} (hb : b ≠ 0) (h : a < b) :
    euclideanDiv a b hb = 0 :=
  euclideanDiv_eq_of_remainder hb (r := a) (by simp) h

theorem euclideanDiv_lt_iff_lt_mul {a b k : Nat} (hb : b ≠ 0) :
    euclideanDiv a b hb < k ↔ a < b * k := by
  rw [← Nat.not_le, ← Nat.not_le, le_euclideanDiv_iff_mul_le hb]

theorem euclideanDiv_pos {a b : Nat} (hb : b ≠ 0) (h : b ≤ a) : 0 < euclideanDiv a b hb :=
  (le_euclideanDiv_iff_mul_le (k := 1) hb).2 (by simpa only [Nat.mul_one] using h)

theorem euclideanDiv_mul_le_self (a b : Nat) (hb : b ≠ 0) : euclideanDiv a b hb * b ≤ a := by
  rw [Nat.mul_comm]
  exact (le_euclideanDiv_iff_mul_le hb).1 (Nat.le_refl _)

theorem euclideanDiv_le_self (a b : Nat) (hb : b ≠ 0) : euclideanDiv a b hb ≤ a :=
  Nat.le_trans (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hb))
    (euclideanDiv_mul_le_self a b hb)

theorem euclideanDiv_lt_self {a b : Nat} (ha : 0 < a) (hb : 1 < b) :
    euclideanDiv a b (Nat.ne_of_gt (Nat.lt_trans Nat.zero_lt_one hb)) < a :=
  (euclideanDiv_lt_iff_lt_mul _).2 (by
    simpa only [Nat.one_mul] using Nat.mul_lt_mul_of_pos_right hb ha)

theorem mul_euclideanDiv_cancel {a b : Nat} (hb : b ≠ 0) (h : b ∣ a) :
    b * euclideanDiv a b hb = a := by
  obtain ⟨q, rfl⟩ := h
  rw [euclideanDiv_mul_left_cancel]

theorem dvd_euclideanDiv_iff_mul_dvd {a b k : Nat} (hb : b ≠ 0) (h : b ∣ a) :
    k ∣ euclideanDiv a b hb ↔ b * k ∣ a := by
  obtain ⟨q, rfl⟩ := h
  rw [euclideanDiv_mul_left_cancel, Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hb)]

theorem euclideanDiv_add_mul (a k : Nat) {b : Nat} (hb : b ≠ 0) :
    euclideanDiv (a + b * k) b hb = euclideanDiv a b hb + k := by
  refine euclideanDiv_eq_of_remainder (r := a % b) hb ?_ (Nat.mod_lt _ (Nat.pos_of_ne_zero hb))
  have h := euclideanDiv_mul_add_mod a b hb
  rw [Nat.mul_add]
  omega

theorem euclideanDiv_add (a c : Nat) {b : Nat} (hb : b ≠ 0) :
    euclideanDiv (a + c) b hb = euclideanDiv a b hb + euclideanDiv c b hb +
      if b ≤ a % b + c % b then 1 else 0 := by
  have ha := euclideanDiv_mul_add_mod a b hb
  have hc := euclideanDiv_mul_add_mod c b hb
  have hra := Nat.mod_lt a (Nat.pos_of_ne_zero hb)
  have hrc := Nat.mod_lt c (Nat.pos_of_ne_zero hb)
  by_cases h : b ≤ a % b + c % b
  · rw [ite_eq_left h]
    refine euclideanDiv_eq_of_remainder (r := a % b + c % b - b) hb ?_ (by omega)
    simp only [Nat.mul_add, Nat.mul_one]
    omega
  · rw [ite_eq_right h, Nat.add_zero]
    refine euclideanDiv_eq_of_remainder (r := a % b + c % b) hb ?_ (Nat.lt_of_not_ge h)
    rw [Nat.mul_add]
    omega

theorem euclideanDiv_euclideanDiv (a : Nat) {b c : Nat} (hb : b ≠ 0) (hc : c ≠ 0) :
    euclideanDiv (euclideanDiv a b hb) c hc = euclideanDiv a (b * c) (Nat.mul_ne_zero hb hc) := by
  have h (k : Nat) : k ≤ euclideanDiv (euclideanDiv a b hb) c hc ↔
      k ≤ euclideanDiv a (b * c) (Nat.mul_ne_zero hb hc) := by
    simp only [le_euclideanDiv_iff_mul_le, Nat.mul_assoc]
  exact Nat.le_antisymm ((h _).1 (Nat.le_refl _)) ((h _).2 (Nat.le_refl _))

theorem euclideanDiv_succ (a : Nat) {b : Nat} (hb : b ≠ 0) :
    euclideanDiv (a + 1) b hb = euclideanDiv a b hb + if b ∣ a + 1 then 1 else 0 := by
  let q := euclideanDiv a b hb
  have h : a + 1 = b * q + (a % b + 1) := by
    rw [← Nat.add_assoc, euclideanDiv_mul_add_mod a b hb]
  have hr : a % b + 1 ≤ b := Nat.mod_lt a (Nat.pos_of_ne_zero hb)
  rcases Nat.eq_or_lt_of_le hr with hr | hr
  · have he : a + 1 = b * (q + 1) := by simpa only [hr, Nat.mul_succ] using h
    rw [ite_eq_left (show b ∣ a + 1 from ⟨q + 1, he⟩)]
    exact euclideanDiv_eq_of_remainder (r := 0) hb (by simpa only [Nat.add_zero] using he)
      (Nat.pos_of_ne_zero hb)
  · have hn : ¬b ∣ a + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero, h, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hr]
      exact Nat.succ_ne_zero _
    rw [ite_eq_right hn, Nat.add_zero]
    exact euclideanDiv_eq_of_remainder hb h hr

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

@[simp] theorem euclideanDiv_mul_left_cancel (a : Int) {b : Int} (hb : b ≠ 0) :
    euclideanDiv (b * a) b hb = a :=
  euclideanDiv_eq_of_remainder (r := 0) hb (by simp) (Int.le_refl _) (by
    simpa only [Int.zero_emod] using Int.emod_lt 0 hb)

@[simp] theorem euclideanDiv_mul_right_cancel (a : Int) {b : Int} (hb : b ≠ 0) :
    euclideanDiv (a * b) b hb = a := by
  rw [Int.mul_comm, euclideanDiv_mul_left_cancel]

@[simp] theorem euclideanDiv_zero (b : Int) (hb : b ≠ 0) : euclideanDiv 0 b hb = 0 := by
  simpa only [Int.mul_zero] using euclideanDiv_mul_left_cancel 0 hb

theorem natCast_euclideanDiv (a b : Nat) (hb : b ≠ 0) :
    (Nat.euclideanDiv a b hb : Int) = euclideanDiv (a : Int) (b : Int) (fun h => hb (Int.ofNat.inj h)) := by
  cases b with
  | zero => exact (hb rfl).elim
  | succ b => rfl

theorem le_euclideanDiv_iff_mul_le {a b k : Int} (hb : 0 < b) :
    k ≤ euclideanDiv a b (Int.ne_of_gt hb) ↔ b * k ≤ a := by
  have hrec := euclideanDiv_mul_add_mod a b (Int.ne_of_gt hb)
  constructor
  · intro h
    have hmul := Int.mul_le_mul_of_nonneg_left h (Int.le_of_lt hb)
    have hr := Int.emod_nonneg a (Int.ne_of_gt hb)
    omega
  · intro h
    by_cases hk : k ≤ euclideanDiv a b (Int.ne_of_gt hb)
    · exact hk
    · have hmul := Int.mul_le_mul_of_nonneg_left
        (show euclideanDiv a b (Int.ne_of_gt hb) + 1 ≤ k by omega) (Int.le_of_lt hb)
      rw [Int.mul_add, Int.mul_one] at hmul
      have hr := Int.emod_lt_of_pos a hb
      omega

theorem euclideanDiv_lt_iff_lt_mul {a b k : Int} (hb : 0 < b) :
    euclideanDiv a b (Int.ne_of_gt hb) < k ↔ a < b * k := by
  rw [← Int.not_le, ← Int.not_le, le_euclideanDiv_iff_mul_le hb]

theorem euclideanDiv_add_mul (a k : Int) {b : Int} (hb : b ≠ 0) :
    euclideanDiv (a + b * k) b hb = euclideanDiv a b hb + k := by
  refine euclideanDiv_eq_of_remainder (r := a % b) hb ?_
    (Int.emod_nonneg _ hb) (Int.emod_lt _ hb)
  have h := euclideanDiv_mul_add_mod a b hb
  rw [Int.mul_add]
  omega

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
