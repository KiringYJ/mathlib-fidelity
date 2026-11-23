/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import Batteries.Logic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Lean.Elab.NativeDivision
public import Mathlib.Tactic.DepRewrite

/-!
# Basic operations on the integers

This file contains some basic lemmas about integers.

See note [foundational algebra order theory].

The integer lemmas use core arithmetic, the notation for natural numbers and integers, and the
nonzero-divisor quotient interface.
-/

@[expose] public section

open Nat

namespace Int

variable {a b c d m n : ℤ}

protected theorem neg_eq_neg {a b : ℤ} (h : -a = -b) : a = b := Int.neg_inj.1 h

/-! ### succ and pred -/

/-- Immediate successor of an integer: `succ n = n + 1` -/
def succ (a : ℤ) := a + 1

/-- Immediate predecessor of an integer: `pred n = n - 1` -/
def pred (a : ℤ) := a - 1

lemma pred_succ (a : ℤ) : pred (succ a) = a := Int.add_sub_cancel _ _

lemma succ_pred (a : ℤ) : succ (pred a) = a := Int.sub_add_cancel _ _

lemma neg_succ (a : ℤ) : -succ a = pred (-a) := Int.neg_add

lemma succ_neg_succ (a : ℤ) : succ (-succ a) = -a := by rw [neg_succ, succ_pred]

lemma neg_pred (a : ℤ) : -pred a = succ (-a) := by
  rw [← Int.neg_eq_comm.mp (neg_succ (-a)), Int.neg_neg]

lemma pred_neg_pred (a : ℤ) : pred (-pred a) = -a := by rw [neg_pred, pred_succ]

lemma pred_nat_succ (n : ℕ) : pred (Nat.succ n) = n := pred_succ n

lemma neg_nat_succ (n : ℕ) : -(Nat.succ n : ℤ) = pred (-n) := neg_succ n

lemma succ_neg_natCast_succ (n : ℕ) : succ (-Nat.succ n) = -n := succ_neg_succ n

@[norm_cast] lemma natCast_pred_of_pos {n : ℕ} (h : 0 < n) : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
  grind

lemma lt_succ_self (a : ℤ) : a < succ a := by unfold succ; lia

lemma pred_self_lt (a : ℤ) : pred a < a := by unfold pred; lia

/--
Induction on integers: prove a proposition `p i` by proving the base case `p 0`,
the upwards induction step `p i → p (i + 1)` and the downwards induction step `p (-i) → p (-i - 1)`.

It is used as the default induction principle for the `induction` tactic.
-/
@[elab_as_elim, induction_eliminator] protected lemma induction_on {motive : ℤ → Prop} (i : ℤ)
    (zero : motive 0) (succ : ∀ i : ℕ, motive i → motive (i + 1))
    (pred : ∀ i : ℕ, motive (-i) → motive (-i - 1)) : motive i := by
  cases i with
  | ofNat i =>
    induction i with
    | zero => exact zero
    | succ i ih => exact succ _ ih
  | negSucc i =>
    suffices ∀ n : ℕ, motive (-n) from this (i + 1)
    intro n; induction n with
    | zero => simp [zero]
    | succ n ih => simpa [natCast_succ, Int.neg_add, Int.sub_eq_add_neg] using pred _ ih

section inductionOn'

variable {motive : ℤ → Sort*} (z b : ℤ) (zero : motive b)
  (succ : ∀ k, b ≤ k → motive k → motive (k + 1)) (pred : ∀ k ≤ b, motive k → motive (k - 1))

/-- Inductively define a function on `ℤ` by defining it at `b`, for the `succ` of a number greater
than `b`, and the `pred` of a number less than `b`. -/
@[elab_as_elim] protected def inductionOn' : motive z :=
  cast (congrArg motive <| show b + (z - b) = z by lia) <|
  match z - b with
  | .ofNat n => pos n
  | .negSucc n => neg n
where
  /-- The positive case of `Int.inductionOn'`. -/
  pos : ∀ n : ℕ, motive (b + n)
  | 0 => cast (by simp) zero
  | n + 1 => cast (by lia) <| succ _ (Int.le_add_of_nonneg_right (natCast_nonneg _)) (pos n)
  /-- The negative case of `Int.inductionOn'`. -/
  neg : ∀ n : ℕ, motive (b + -[n+1])
  | 0 => pred _ Int.le_rfl zero
  | n + 1 => cast (by lia) <| pred _ (by lia) (neg n)

variable {z b zero succ pred}

lemma inductionOn'_self : b.inductionOn' b zero succ pred = zero :=
  cast_eq_iff_heq.mpr <| .symm <| by rw [b.sub_self, ← cast_eq_iff_heq]; rfl

theorem inductionOn'_add_one (hz : b ≤ z) :
    (z + 1).inductionOn' b zero succ pred = succ z hz (z.inductionOn' b zero succ pred) := by
  unfold Int.inductionOn'
  rw! [show z - b = (z - b).toNat by lia, show z + 1 - b = ((z - b).toNat + 1 : ℕ) by lia]
  grind [inductionOn'.pos, show b + (z - b).toNat = z by lia]

theorem inductionOn'_sub_one (hz : z ≤ b) :
    (z - 1).inductionOn' b zero succ pred = pred z hz (z.inductionOn' b zero succ pred) := by
  unfold Int.inductionOn'
  conv => lhs; unfold inductionOn'.neg
  by_cases z = b
  · rw! [show z - 1 - b = -[(b - z).toNat+1] by lia, show z - b = 0 by lia]
    grind [inductionOn'.pos]
  rw! [show z - 1 - b = -[(b - z).toNat+1] by lia, show z - b = -[(b - z - 1).toNat+1] by lia]
  grind

end inductionOn'

/-- Inductively define a function on `ℤ` by defining it on `ℕ` and extending it from `n` to `-n`. -/
@[elab_as_elim] protected def negInduction {motive : ℤ → Sort*} (nat : ∀ n : ℕ, motive n)
    (neg : (∀ n : ℕ, motive n) → ∀ n : ℕ, motive (-n)) : ∀ n : ℤ, motive n
  | .ofNat n => nat n
  | .negSucc n => neg nat <| n + 1

/-- See `Int.inductionOn'` for an induction in both directions. -/
@[elab_as_elim]
protected def leInduction {m : ℤ} {motive : ∀ n, m ≤ n → Sort*} (base : motive m m.le_refl)
    (succ : ∀ n hmn, motive n hmn → motive (n + 1) (le_add_one hmn)) : ∀ n hmn, motive n hmn :=
  fun n ↦ n.inductionOn' m
    (fun _ ↦ base) (fun k hle ih _ ↦ succ k hle <| ih hle) (fun _ _ _ _ ↦ False.elim <| by lia)

@[deprecated (since := "2026-03-25")] protected alias le_induction := Int.leInduction

theorem leInduction_base {m : ℤ} {motive : ∀ n, m ≤ n → Sort*} (base : motive m m.le_refl)
    (succ : ∀ n hmn, motive n hmn → motive (n + 1) (le_add_one hmn)) :
    Int.leInduction (motive := motive) base succ m m.le_refl = base := by
  rw [Int.leInduction, inductionOn'_self]

theorem leInduction_add_one {m : ℤ} {motive : ∀ n, m ≤ n → Sort*} (base : motive m m.le_refl)
    (succ : ∀ n hmn, motive n hmn → motive (n + 1) (le_add_one hmn)) (n : ℤ) (hmn : m ≤ n) :
    Int.leInduction (motive := motive) base succ (n + 1) (by lia) =
      succ n hmn (Int.leInduction (motive := motive) base succ n hmn) := by
  rw [Int.leInduction, inductionOn'_add_one hmn]
  rfl

/-- See `Int.inductionOn'` for an induction in both directions. -/
@[elab_as_elim]
protected def leInductionDown {m : ℤ} {motive : ∀ n, n ≤ m → Sort*} (base : motive m m.le_refl)
    (pred : ∀ n hnm, motive n hnm → motive (n - 1) (by lia)) : ∀ n hnm, motive n hnm :=
  fun n ↦ n.inductionOn' m
    (fun _ ↦ base) (fun _ _ _ _ ↦ False.elim <| by lia) (fun k hle ih _ ↦ pred k hle <| ih hle)

theorem leInductionDown_base {m : ℤ} {motive : ∀ n, n ≤ m → Sort*} (base : motive m m.le_refl)
    (pred : ∀ n hnm, motive n hnm → motive (n - 1) (by lia)) :
    Int.leInductionDown (motive := motive) base pred m m.le_refl = base := by
  rw [Int.leInductionDown, inductionOn'_self]

theorem leInductionDown_sub_one {m : ℤ} {motive : ∀ n, n ≤ m → Sort*} (base : motive m m.le_refl)
    (pred : ∀ n hnm, motive n hnm → motive (n - 1) (by lia)) (n : ℤ) (hnm : n ≤ m) :
    Int.leInductionDown (motive := motive) base pred (n - 1) (by lia) =
      pred n hnm (Int.leInductionDown (motive := motive) base pred n hnm) := by
  rw [Int.leInductionDown, inductionOn'_sub_one hnm]
  rfl

@[deprecated (since := "2026-03-25")] protected alias le_induction_down := Int.leInductionDown

section strongRec

variable {motive : ℤ → Sort*} (lt : ∀ n < m, motive n)
  (ge : ∀ n ≥ m, (∀ k < n, motive k) → motive n)

/-- A strong recursor for `Int` that specifies explicit values for integers below a threshold,
and is analogous to `Nat.strongRec` for integers on or above the threshold. -/
@[elab_as_elim] protected def strongRec (n : ℤ) : motive n := by
  refine if hnm : n < m then lt n hnm else ge n (by lia) (n.inductionOn' m lt ?_ ?_)
  · intro _n _ ih l _
    exact if hlm : l < m then lt l hlm else ge l (by lia) fun k _ ↦ ih k (by lia)
  · exact fun n _ hn l _ ↦ hn l (by lia)

variable {lt ge}
lemma strongRec_of_lt (hn : n < m) : m.strongRec lt ge n = lt n hn := dite_eq_left _

end strongRec

/-! ### mul -/

/-! ### natAbs -/

alias natAbs_sq := natAbs_pow_two

theorem sign_mul_self_eq_natAbs (a : Int) : sign a * a = natAbs a :=
  sign_mul_self a

/-! ### Euclidean quotient and remainder -/

lemma natCast_div (m n : ℕ) (hn : n ≠ 0) :
    (Nat.euclideanDiv m n hn : ℤ) = Int.euclideanDiv m n (Int.ofNat_ne_zero.2 hn) := by
  cases n with
  | zero => exact (hn rfl).elim
  | succ n => rfl

lemma ediv_of_neg_of_pos {a b : ℤ} (Ha : a < 0) (Hb : 0 < b) :
    Int.euclideanDiv a b (Int.ne_of_gt Hb) =
      -(Int.euclideanDiv (-a - 1) b (Int.ne_of_gt Hb) + 1) := by
  match a, b, eq_negSucc_of_lt_zero Ha, eq_succ_of_zero_lt Hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ =>
    rw [show (- -[m+1] : ℤ) = (m + 1 : ℤ) by rfl]; rw [Int.add_sub_cancel]; rfl

@[simp, norm_cast] lemma natCast_mod (m n : ℕ) : (↑(m % n) : ℤ) = ↑m % ↑n := rfl

lemma div_le_iff_of_dvd_of_pos (hb : 0 < b) (hba : b ∣ a) :
    Int.euclideanDiv a b (Int.ne_of_gt hb) ≤ c ↔ a ≤ b * c := by
  simpa only [Int.mul_exactQuotient] using!
    (Int.mul_le_mul_left (b := Int.exactQuotient a b hba (Int.ne_of_gt hb)) (c := c) hb).symm

lemma div_le_iff_of_dvd_of_neg (hb : b < 0) (hba : b ∣ a) :
    Int.euclideanDiv a b (Int.ne_of_lt hb) ≤ c ↔ b * c ≤ a := by
  simpa only [Int.mul_exactQuotient] using!
    (Int.mul_le_mul_left_of_neg (b := c) (c := Int.exactQuotient a b hba (Int.ne_of_lt hb)) hb).symm

lemma div_lt_iff_of_dvd_of_pos (hb : 0 < b) (hba : b ∣ a) :
    Int.euclideanDiv a b (Int.ne_of_gt hb) < c ↔ a < b * c := by
  simpa only [Int.mul_exactQuotient] using!
    (Int.mul_lt_mul_left (b := Int.exactQuotient a b hba (Int.ne_of_gt hb)) (c := c) hb).symm

lemma div_lt_iff_of_dvd_of_neg (hb : b < 0) (hba : b ∣ a) :
    Int.euclideanDiv a b (Int.ne_of_lt hb) < c ↔ b * c < a := by
  simpa only [Int.mul_exactQuotient] using!
    (Int.mul_lt_mul_left_of_neg (b := c) (c := Int.exactQuotient a b hba (Int.ne_of_lt hb)) hb).symm

lemma le_div_iff_of_dvd_of_pos (hc : 0 < c) (hcb : c ∣ b) :
    a ≤ Int.euclideanDiv b c (Int.ne_of_gt hc) ↔ c * a ≤ b := by
  simpa only [Int.mul_exactQuotient] using!
    (Int.mul_le_mul_left (b := a) (c := Int.exactQuotient b c hcb (Int.ne_of_gt hc)) hc).symm

lemma le_div_iff_of_dvd_of_neg (hc : c < 0) (hcb : c ∣ b) :
    a ≤ Int.euclideanDiv b c (Int.ne_of_lt hc) ↔ b ≤ c * a := by
  simpa only [Int.mul_exactQuotient] using!
    (Int.mul_le_mul_left_of_neg (b := Int.exactQuotient b c hcb (Int.ne_of_lt hc)) (c := a) hc).symm

lemma lt_div_iff_of_dvd_of_pos (hc : 0 < c) (hcb : c ∣ b) :
    a < Int.euclideanDiv b c (Int.ne_of_gt hc) ↔ c * a < b := by
  simpa only [Int.mul_exactQuotient] using!
    (Int.mul_lt_mul_left (b := a) (c := Int.exactQuotient b c hcb (Int.ne_of_gt hc)) hc).symm

lemma lt_div_iff_of_dvd_of_neg (hc : c < 0) (hcb : c ∣ b) :
    a < Int.euclideanDiv b c (Int.ne_of_lt hc) ↔ b < c * a := by
  simpa only [Int.mul_exactQuotient] using!
    (Int.mul_lt_mul_left_of_neg (b := Int.exactQuotient b c hcb (Int.ne_of_lt hc)) (c := a) hc).symm

lemma div_le_div_iff_of_dvd_of_pos_of_pos (hb : 0 < b) (hd : 0 < d) (hba : b ∣ a)
    (hdc : d ∣ c) :
    Int.euclideanDiv a b (Int.ne_of_gt hb) ≤ Int.euclideanDiv c d (Int.ne_of_gt hd) ↔
      d * a ≤ c * b := by
  simpa only [Int.mul_assoc, Int.mul_left_comm d b, Int.mul_exactQuotient, Int.mul_comm b c] using!
    (Int.mul_le_mul_left (b := Int.exactQuotient a b hba (Int.ne_of_gt hb))
      (c := Int.exactQuotient c d hdc (Int.ne_of_gt hd)) (Int.mul_pos hd hb)).symm

lemma div_le_div_iff_of_dvd_of_pos_of_neg (hb : 0 < b) (hd : d < 0) (hba : b ∣ a) (hdc : d ∣ c) :
    Int.euclideanDiv a b (Int.ne_of_gt hb) ≤ Int.euclideanDiv c d (Int.ne_of_lt hd) ↔
      c * b ≤ d * a := by
  simpa only [Int.mul_assoc, Int.mul_left_comm d b, Int.mul_exactQuotient, Int.mul_comm b c] using!
    (Int.mul_le_mul_left_of_neg (b := Int.exactQuotient c d hdc (Int.ne_of_lt hd))
      (c := Int.exactQuotient a b hba (Int.ne_of_gt hb)) (Int.mul_neg_of_neg_of_pos hd hb)).symm

lemma div_le_div_iff_of_dvd_of_neg_of_pos (hb : b < 0) (hd : 0 < d) (hba : b ∣ a) (hdc : d ∣ c) :
    Int.euclideanDiv a b (Int.ne_of_lt hb) ≤ Int.euclideanDiv c d (Int.ne_of_gt hd) ↔
      c * b ≤ d * a := by
  simpa only [Int.mul_assoc, Int.mul_left_comm d b, Int.mul_exactQuotient, Int.mul_comm b c] using!
    (Int.mul_le_mul_left_of_neg (b := Int.exactQuotient c d hdc (Int.ne_of_gt hd))
      (c := Int.exactQuotient a b hba (Int.ne_of_lt hb)) (Int.mul_neg_of_pos_of_neg hd hb)).symm

lemma div_le_div_iff_of_dvd_of_neg_of_neg (hb : b < 0) (hd : d < 0) (hba : b ∣ a) (hdc : d ∣ c) :
    Int.euclideanDiv a b (Int.ne_of_lt hb) ≤ Int.euclideanDiv c d (Int.ne_of_lt hd) ↔
      d * a ≤ c * b := by
  simpa only [Int.mul_assoc, Int.mul_left_comm d b, Int.mul_exactQuotient, Int.mul_comm b c] using!
    (Int.mul_le_mul_left (b := Int.exactQuotient a b hba (Int.ne_of_lt hb))
      (c := Int.exactQuotient c d hdc (Int.ne_of_lt hd)) (Int.mul_pos_of_neg_of_neg hd hb)).symm

lemma div_lt_div_iff_of_dvd_of_pos (hb : 0 < b) (hd : 0 < d) (hba : b ∣ a) (hdc : d ∣ c) :
    Int.euclideanDiv a b (Int.ne_of_gt hb) < Int.euclideanDiv c d (Int.ne_of_gt hd) ↔
      d * a < c * b := by
  simpa only [Int.mul_assoc, Int.mul_left_comm d b, Int.mul_exactQuotient, Int.mul_comm b c] using!
    (Int.mul_lt_mul_left (b := Int.exactQuotient a b hba (Int.ne_of_gt hb))
      (c := Int.exactQuotient c d hdc (Int.ne_of_gt hd)) (Int.mul_pos hd hb)).symm

lemma div_lt_div_iff_of_dvd_of_pos_of_neg (hb : 0 < b) (hd : d < 0) (hba : b ∣ a) (hdc : d ∣ c) :
    Int.euclideanDiv a b (Int.ne_of_gt hb) < Int.euclideanDiv c d (Int.ne_of_lt hd) ↔
      c * b < d * a := by
  simpa only [Int.mul_assoc, Int.mul_left_comm d b, Int.mul_exactQuotient, Int.mul_comm b c] using!
    (Int.mul_lt_mul_left_of_neg (b := Int.exactQuotient c d hdc (Int.ne_of_lt hd))
      (c := Int.exactQuotient a b hba (Int.ne_of_gt hb)) (Int.mul_neg_of_neg_of_pos hd hb)).symm

lemma div_lt_div_iff_of_dvd_of_neg_of_pos (hb : b < 0) (hd : 0 < d) (hba : b ∣ a) (hdc : d ∣ c) :
    Int.euclideanDiv a b (Int.ne_of_lt hb) < Int.euclideanDiv c d (Int.ne_of_gt hd) ↔
      c * b < d * a := by
  simpa only [Int.mul_assoc, Int.mul_left_comm d b, Int.mul_exactQuotient, Int.mul_comm b c] using!
    (Int.mul_lt_mul_left_of_neg (b := Int.exactQuotient c d hdc (Int.ne_of_gt hd))
      (c := Int.exactQuotient a b hba (Int.ne_of_lt hb)) (Int.mul_neg_of_pos_of_neg hd hb)).symm

lemma div_lt_div_iff_of_dvd_of_neg_of_neg (hb : b < 0) (hd : d < 0) (hba : b ∣ a) (hdc : d ∣ c) :
    Int.euclideanDiv a b (Int.ne_of_lt hb) < Int.euclideanDiv c d (Int.ne_of_lt hd) ↔
      d * a < c * b := by
  simpa only [Int.mul_assoc, Int.mul_left_comm d b, Int.mul_exactQuotient, Int.mul_comm b c] using!
    (Int.mul_lt_mul_left (b := Int.exactQuotient a b hba (Int.ne_of_lt hb))
      (c := Int.exactQuotient c d hdc (Int.ne_of_lt hd)) (Int.mul_pos_of_neg_of_neg hd hb)).symm

lemma emod_two_eq_zero_or_one (n : ℤ) : n % 2 = 0 ∨ n % 2 = 1 :=
  emod_two_eq n

/-! ### dvd -/

lemma div_dvd_iff_dvd_mul (h : b ∣ a) (hb : b ≠ 0) :
    Int.euclideanDiv a b hb ∣ c ↔ a ∣ b * c := by
  change Int.exactQuotient a b h hb ∣ c ↔ _
  rw [← Int.mul_dvd_mul_iff_left hb, Int.mul_exactQuotient]

lemma dvd_mul_of_div_dvd (hb : b ≠ 0) (h : b ∣ a) (hdiv : Int.euclideanDiv a b hb ∣ c) :
    a ∣ b * c :=
  (div_dvd_iff_dvd_mul h hb).mp hdiv

lemma dvd_div_iff_mul_dvd (hc : c ≠ 0) (hbc : c ∣ b) :
    a ∣ Int.euclideanDiv b c hc ↔ c * a ∣ b := by
  change a ∣ Int.exactQuotient b c hbc hc ↔ _
  rw [← Int.mul_dvd_mul_iff_left hc, Int.mul_exactQuotient]

lemma mul_dvd_of_dvd_div (hc : c ≠ 0) (hcb : c ∣ b) (h : a ∣ Int.euclideanDiv b c hc) : c * a ∣ b :=
  (dvd_div_iff_mul_dvd hc hcb).mp h

lemma dvd_div_of_mul_dvd (ha : a ≠ 0) (h : a * b ∣ c) :
    b ∣ Int.euclideanDiv c a ha :=
  (dvd_div_iff_mul_dvd ha (Int.dvd_trans (Int.dvd_mul_right _ _) h)).mpr h

/-- If `n > 0` then `m` is not divisible by `n` iff it is between `n * k` and `n * (k + 1)`
  for some `k`. -/
lemma exists_lt_and_lt_iff_not_dvd (m : ℤ) (hn : 0 < n) :
    (∃ k, n * k < m ∧ m < n * (k + 1)) ↔ ¬n ∣ m := by
  constructor
  · rintro ⟨k, hlt, hgt⟩ ⟨j, rfl⟩
    rw [Int.mul_lt_mul_left hn] at hlt hgt
    omega
  · intro hd
    refine ⟨Int.euclideanDiv m n (Int.ne_of_gt hn), ?_⟩
    have he := Int.euclideanDiv_mul_add_mod m n (Int.ne_of_gt hn)
    have hne := mt Int.dvd_iff_emod_eq_zero.mpr hd
    have hr₀ := Int.emod_nonneg m (Int.ne_of_gt hn)
    have hr : m % n < n := by
      simpa [Int.natAbs_of_nonneg (Int.le_of_lt hn)] using Int.emod_lt m (Int.ne_of_gt hn)
    rw [Int.mul_add, Int.mul_one]
    omega

lemma eq_mul_div_of_mul_eq_mul_of_dvd_left (hb : b ≠ 0) (hbc : b ∣ c) (h : b * a = c * d) :
    a = Int.euclideanDiv c b hb * d := by
  change a = Int.exactQuotient c b hbc hb * d
  apply Int.eq_of_mul_eq_mul_left hb
  rw [← Int.mul_assoc, Int.mul_exactQuotient]
  exact h

lemma ofNat_add_negSucc_of_ge {m n : ℕ} (h : n.succ ≤ m) :
    ofNat m + -[n+1] = ofNat (m - n.succ) := by
  rw [negSucc_eq, ofNat_eq_natCast, ofNat_eq_natCast, ← Int.natCast_one, ← Int.natCast_add,
    ← Int.sub_eq_add_neg, ← Int.natCast_sub h]

/-! ### Divisibility and ordering -/

lemma le_iff_pos_of_dvd (ha : 0 < a) (hab : a ∣ b) : a ≤ b ↔ 0 < b :=
  ⟨Int.lt_of_lt_of_le ha, (Int.le_of_dvd · hab)⟩

lemma le_add_iff_lt_of_dvd_sub (ha : 0 < a) (hab : a ∣ c - b) : a + b ≤ c ↔ b < c := by
  rw [Int.add_le_iff_le_sub, ← Int.sub_pos, le_iff_pos_of_dvd ha hab]

/-! ### sign -/

lemma sign_add_eq_of_sign_eq : ∀ {m n : ℤ}, m.sign = n.sign → (m + n).sign = n.sign := by
  lia

/-! ### toNat -/

/-
The following lemma is non-confluent with
```
simp only [*, @Int.lt_toNat, CharP.cast_eq_zero, @Nat.cast_pred, Int.ofNat_toNat]
```
from the default simp set, which simplifies the LHS to `max i 0 - 1`.
Therefore we mark this lemma as `@[simp high]`.
-/
@[simp high]
lemma toNat_pred_coe_of_pos {i : ℤ} (h : 0 < i) : ((i.toNat - 1 : ℕ) : ℤ) = i - 1 := by
  simp only [lt_toNat, Int.cast_ofNat_Int, h, natCast_pred_of_pos, Int.le_of_lt h, toNat_of_nonneg]

lemma toNat_lt_of_ne_zero {n : ℕ} (hn : n ≠ 0) : m.toNat < n ↔ m < n := by lia

/-- The modulus of an integer by another as a natural. Uses the E-rounding convention. -/
def natMod (m n : ℤ) : ℕ := (m % n).toNat

lemma natMod_lt {n : ℕ} (hn : n ≠ 0) : m.natMod n < n :=
  (toNat_lt_of_ne_zero hn).2 <| emod_lt_of_pos _ <| by lia

/-- For use in `Mathlib/Tactic/NormNum/Pow.lean` -/
@[simp] lemma pow_eq (m : ℤ) (n : ℕ) : m.pow n = m ^ n := rfl

@[simp] lemma gcd_ofNat_negSucc (m n : ℕ) : gcd m (negSucc n) = m.gcd (n + 1) := by simp [gcd]
@[simp] lemma gcd_negSucc_ofNat (m n : ℕ) : gcd (negSucc m) n = (m + 1).gcd n := by simp [gcd]
@[simp] lemma gcd_negSucc_negSucc (m n : ℕ) :
    (negSucc m).gcd (negSucc n) = (m + 1).gcd (n + 1) := by simp [gcd]

theorem gcd_right_comm (a b c : ℤ) : gcd (gcd a b) c = gcd (gcd a c) b := by
  rw [gcd_assoc, gcd_assoc, gcd_comm b c]

end Int
