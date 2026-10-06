/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.Nat.Log

/-!
# Integer logarithms in a field with respect to a natural base

This file defines two `ℤ`-valued analogs of the logarithm of `r : R` with base `b : ℕ`:

* `Int.log b r`: Lower logarithm, or floor **log**. Greatest `k` such that `↑b^k ≤ r`.
* `Int.clog b r`: Upper logarithm, or **c**eil **log**. Least `k` such that `r ≤ ↑b^k`.

Note that `Int.log` gives the position of the left-most non-zero digit:
```lean
#eval (Int.log 10 (0.09 : ℚ), Int.log 10 (0.10 : ℚ), Int.log 10 (0.11 : ℚ))
--    (-2,                    -1,                    -1)
#eval (Int.log 10 (9 : ℚ),    Int.log 10 (10 : ℚ),   Int.log 10 (11 : ℚ))
--    (0,                     1,                     1)
```
which means it can be used for computing digit expansions
```lean
import Data.Fin.VecNotation
import Mathlib.Data.Rat.Floor

def digits (b : ℕ) (q : ℚ) (n : ℕ) (hb : 1 < b) (hq : 0 < q) : ℕ :=
  ⌊q * ((b : ℚ) ^ (n - Int.log b q))⌋₊ % b

#eval (digits 10 (1/7) · (by norm_num) (by norm_num)) ∘ ((↑) : Fin 8 → ℕ)
-- ![1, 4, 2, 8, 5, 7, 1, 4]
```

## Main results

* For `Int.log`:
  * `Int.zpow_log_le_self`, `Int.lt_zpow_succ_log_self`: the bounds formed by `Int.log`,
    `(b : R) ^ log b r ≤ r < (b : R) ^ (log b r + 1)`.
  * `Int.zpow_log_gi`: the Galois coinsertion between `zpow` and `Int.log`.
* For `Int.clog`:
  * `Int.zpow_pred_clog_lt_self`, `Int.self_le_zpow_clog`: the bounds formed by `Int.clog`,
    `(b : R) ^ (clog b r - 1) < r ≤ (b : R) ^ clog b r`.
  * `Int.clog_zpow_gi`:  the Galois insertion between `Int.clog` and `zpow`.
* `Int.neg_log_inv_eq_clog`, `Int.neg_clog_inv_eq_log`: the link between the two definitions.
-/

@[expose] public section

assert_not_exists Finset

variable {R : Type*} [Semifield R] [LinearOrder R] [IsStrictOrderedRing R] [FloorSemiring R]

namespace Int

open Lean Elab Tactic in
/-- The default discharger for the side conditions `1 < b` and `0 < r` of `Int.log` and `Int.clog`.

It closes the goal with a local hypothesis, or `1 < b` by `nat_log_tac`. Other evidence is passed
explicitly. It never chooses the base or the argument: if they are not determined when the tactic
runs, it fails instead of assigning them from a hypothesis. -/
elab (name := intLogTac) "int_log_tac" : tactic => do
  if (← instantiateMVars (← getMainTarget)).hasExprMVar then
    throwError "the base or the argument of the logarithm is not determined; pass the side \
      condition explicitly"
  evalTactic (← `(tactic|
    first
      | assumption
      | nat_log_tac
      | fail "the logarithms `Int.log b r` and `Int.clog b r` need `1 < b` and `0 < r`"))

/-- The greatest power of `b` such that `b ^ log b r ≤ r`. It exists exactly when `1 < b` and
`0 < r`: for `b ≤ 1` every power of `b` is at most `1`, and for `r ≤ 0` no power of `b` is at most
`r`. The proofs `_hb` and `_hr` can usually be omitted, see `int_log_tac`. -/
@[nolint unusedArguments]
def log (b : ℕ) (r : R) (_hb : 1 < b := by int_log_tac) (_hr : 0 < r := by int_log_tac) : ℤ :=
  if h : 1 ≤ r then Nat.log b ⌊r⌋₊ _hb (Nat.floor_pos.mpr h).ne' else -Nat.clog b ⌈r⁻¹⌉₊

theorem log_of_one_le_right {b : ℕ} (hb : 1 < b) {r : R} (hr : 1 ≤ r) {hr' : 0 < r} :
    log b r hb hr' = Nat.log b ⌊r⌋₊ hb (Nat.floor_pos.mpr hr).ne' :=
  dite_eq_left hr

theorem log_of_right_le_one {b : ℕ} (hb : 1 < b) {r : R} (hr : r ≤ 1) {hr' : 0 < r} :
    log b r hb hr' = -Nat.clog b ⌈r⁻¹⌉₊ := by
  obtain rfl | hr := hr.eq_or_lt
  · rw [log_of_one_le_right hb le_rfl]
    simp [Nat.log_one_right hb]
  · exact dite_eq_right hr.not_ge

@[simp, norm_cast]
theorem log_natCast {b : ℕ} (hb : 1 < b) {n : ℕ} (hn : n ≠ 0) {h : 0 < (n : R)} :
    log b (n : R) hb h = Nat.log b n := by
  rw [log_of_one_le_right hb (Nat.one_le_cast.2 (Nat.pos_of_ne_zero hn))]
  simp only [Nat.floor_natCast]

@[simp]
theorem log_ofNat {b : ℕ} (hb : 1 < b) (n : ℕ) [n.AtLeastTwo] {h : 0 < (ofNat(n) : R)} :
    log b (ofNat(n) : R) hb h = Nat.log b ofNat(n) hb (NeZero.ne _) :=
  log_natCast hb (NeZero.ne _)

theorem zpow_log_le_self {b : ℕ} {r : R} (hb : 1 < b) (hr : 0 < r) : (b : R) ^ log b r ≤ r := by
  rcases le_total 1 r with hr1 | hr1
  · rw [log_of_one_le_right hb hr1]
    rw [zpow_natCast, ← Nat.cast_pow, ← Nat.le_floor_iff hr.le]
    exact Nat.pow_log_le_self hb (Nat.floor_pos.mpr hr1).ne'
  · rw [log_of_right_le_one hb hr1, zpow_neg]
    exact_mod_cast inv_le_of_inv_le₀ hr (Nat.ceil_le.1 <| Nat.le_pow_clog hb _)

theorem lt_zpow_succ_log_self {b : ℕ} (hb : 1 < b) {r : R} (hr : 0 < r) :
    r < (b : R) ^ (log b r + 1) := by
  rcases le_or_gt 1 r with hr1 | hr1
  · rw [log_of_one_le_right hb hr1, Int.ofNat_add_one_out]
    exact_mod_cast Nat.lt_of_floor_lt <| Nat.lt_pow_succ_log_self hb (Nat.floor_pos.mpr hr1).ne'
  · rw [log_of_right_le_one hb hr1.le]
    have hcri : 1 < r⁻¹ := (one_lt_inv₀ hr).2 hr1
    have : 1 ≤ Nat.clog b ⌈r⁻¹⌉₊ :=
      Nat.succ_le_of_lt (Nat.clog_pos hb <| Nat.one_lt_cast.1 <| hcri.trans_le (Nat.le_ceil _))
    rw [neg_add_eq_sub, ← neg_sub, ← Int.ofNat_one, ← Int.ofNat_sub this, zpow_neg, zpow_natCast,
      lt_inv_comm₀ hr (pow_pos (Nat.cast_pos.mpr <| zero_lt_one.trans hb) _), ← Nat.cast_pow]
    refine Nat.lt_ceil.1 ?_
    exact Nat.pow_pred_clog_lt_self hb <| Nat.one_lt_cast.1 <| hcri.trans_le <| Nat.le_ceil _

@[simp]
theorem log_one_right {b : ℕ} (hb : 1 < b) {h : (0 : R) < 1} : log b (1 : R) hb h = 0 := by
  rw [log_of_one_le_right hb le_rfl]
  simp [Nat.log_one_right hb]

theorem log_zpow {b : ℕ} (hb : 1 < b) (z : ℤ) {h : 0 < (b ^ z : R)} :
    log b (b ^ z : R) hb h = z := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg z
  · rw [log_of_one_le_right hb (one_le_zpow₀ (mod_cast hb.le) <| Int.natCast_nonneg _)]
    simp only [zpow_natCast, ← Nat.cast_pow, Nat.floor_natCast, Nat.log_pow hb]
  · rw [log_of_right_le_one hb (zpow_le_one_of_nonpos₀ (mod_cast hb.le) <|
      neg_nonpos.2 (Int.natCast_nonneg _))]
    simp only [zpow_neg, inv_inv, zpow_natCast, ← Nat.cast_pow, Nat.ceil_natCast,
      Nat.clog_pow _ _ hb]

@[mono, gcongr]
theorem log_mono_right {b : ℕ} {hb : 1 < b} {r₁ r₂ : R} {h₀ : 0 < r₁} (h : r₁ ≤ r₂) :
    log b r₁ ≤ log b r₂ hb (lt_of_lt_of_le h₀ h) := by
  have h₀' : 0 < r₂ := lt_of_lt_of_le h₀ h
  rcases le_total r₁ 1 with h₁ | h₁ <;> rcases le_total r₂ 1 with h₂ | h₂
  · rw [log_of_right_le_one hb h₁, log_of_right_le_one hb h₂, neg_le_neg_iff, Nat.cast_le]
    exact Nat.clog_mono_right b <| Nat.ceil_mono <| (inv_le_inv₀ h₀' h₀).2 h
  · rw [log_of_right_le_one hb h₁, log_of_one_le_right hb h₂]
    exact (neg_nonpos.mpr (Int.natCast_nonneg _)).trans (Int.natCast_nonneg _)
  · obtain rfl := le_antisymm h (h₂.trans h₁)
    rfl
  · rw [log_of_one_le_right hb h₁, log_of_one_le_right hb h₂, Nat.cast_le]
    exact Nat.log_mono_right (Nat.floor_mono h)

variable (R) in
/-- Over suitable subtypes, `zpow` and `Int.log` form a Galois coinsertion -/
def zpowLogGi {b : ℕ} (hb : 1 < b) :
    GaloisCoinsertion
      (fun z : ℤ =>
        Subtype.mk ((b : R) ^ z) <| zpow_pos (mod_cast zero_lt_one.trans hb) z)
      fun r : Set.Ioi (0 : R) => Int.log b (r : R) hb r.2 :=
  GaloisCoinsertion.monotoneIntro (fun r₁ _ h => log_mono_right (h₀ := r₁.2) h)
    (fun _ _ hz => Subtype.coe_le_coe.mp <| (zpow_right_strictMono₀ <| mod_cast hb).monotone hz)
    (fun r => Subtype.coe_le_coe.mp <| zpow_log_le_self hb r.2) fun _ => log_zpow (R := R) hb _

/-- `zpow b` and `Int.log b` form a Galois connection on positive elements. -/
theorem lt_zpow_iff_log_lt {b : ℕ} (hb : 1 < b) {x : ℤ} {r : R} (hr : 0 < r) :
    r < (b : R) ^ x ↔ log b r < x :=
  @GaloisConnection.lt_iff_lt _ _ _ _ _ _ (zpowLogGi R hb).gc x ⟨r, hr⟩

/-- `zpow b` and `Int.log b` form a Galois connection on positive elements. -/
theorem zpow_le_iff_le_log {b : ℕ} (hb : 1 < b) {x : ℤ} {r : R} (hr : 0 < r) :
    (b : R) ^ x ≤ r ↔ x ≤ log b r :=
  @GaloisConnection.le_iff_le _ _ _ _ _ _ (zpowLogGi R hb).gc x ⟨r, hr⟩

/-- The least power of `b` such that `r ≤ b ^ clog b r`. It exists exactly when `1 < b` and
`0 < r`: for `b ≤ 1` and `1 < r` no power of `b` is at least `r`, and for `r ≤ 0` every power of
`b` is. The proofs `_hb` and `_hr` can usually be omitted, see `int_log_tac`. -/
def clog (b : ℕ) (r : R) (_hb : 1 < b := by int_log_tac) (_hr : 0 < r := by int_log_tac) : ℤ :=
  if h : 1 ≤ r then Nat.clog b ⌈r⌉₊ else
    -Nat.log b ⌊r⁻¹⌋₊ _hb (Nat.floor_pos.mpr ((one_lt_inv₀ _hr).2 (lt_of_not_ge h)).le).ne'

theorem clog_of_one_le_right {b : ℕ} (hb : 1 < b) {r : R} (hr : 1 ≤ r) {hr' : 0 < r} :
    clog b r hb hr' = Nat.clog b ⌈r⌉₊ :=
  dite_eq_left hr

theorem clog_of_right_lt_one {b : ℕ} (hb : 1 < b) {r : R} (hr' : 0 < r) (hr : r < 1) :
    clog b r hb hr' = -Nat.log b ⌊r⁻¹⌋₊ hb
      (Nat.floor_pos.mpr ((one_lt_inv₀ hr').2 hr).le).ne' :=
  dite_eq_right hr.not_ge

@[simp]
theorem clog_inv {b : ℕ} (hb : 1 < b) {r : R} (hr : 0 < r) {h : 0 < r⁻¹} :
    clog b r⁻¹ hb h = -log b r := by
  obtain hr1 | hr1 := le_total 1 r
  · rw [log_of_one_le_right hb hr1]
    obtain rfl | hr1 := hr1.eq_or_lt
    · simp [clog_of_one_le_right hb, Nat.log_one_right hb]
    · rw [clog_of_right_lt_one hb h (inv_lt_one_of_one_lt₀ hr1)]
      simp only [inv_inv]
  · rw [clog_of_one_le_right hb ((one_le_inv₀ hr).2 hr1), log_of_right_le_one hb hr1, neg_neg]

@[simp]
theorem log_inv {b : ℕ} (hb : 1 < b) {r : R} (hr : 0 < r) {h : 0 < r⁻¹} :
    log b r⁻¹ hb h = -clog b r := by
  have := clog_inv hb h (h := by simpa using hr)
  simp only [inv_inv] at this
  rw [this, neg_neg]

-- note this is useful for writing in reverse
theorem neg_log_inv_eq_clog {b : ℕ} (hb : 1 < b) {r : R} (hr : 0 < r) :
    -log b r⁻¹ hb (inv_pos.2 hr) = clog b r := by
  rw [log_inv hb hr, neg_neg]

theorem neg_clog_inv_eq_log {b : ℕ} (hb : 1 < b) {r : R} (hr : 0 < r) :
    -clog b r⁻¹ hb (inv_pos.2 hr) = log b r := by
  rw [clog_inv hb hr, neg_neg]

@[simp, norm_cast]
theorem clog_natCast {b : ℕ} (hb : 1 < b) {n : ℕ} (hn : n ≠ 0) {h : 0 < (n : R)} :
    clog b (n : R) hb h = Nat.clog b n := by
  rw [clog_of_one_le_right hb (Nat.one_le_cast.2 (Nat.pos_of_ne_zero hn))]
  simp only [Nat.ceil_natCast]

@[simp]
theorem clog_ofNat {b : ℕ} (hb : 1 < b) (n : ℕ) [n.AtLeastTwo] {h : 0 < (ofNat(n) : R)} :
    clog b (ofNat(n) : R) hb h = Nat.clog b ofNat(n) :=
  clog_natCast hb (NeZero.ne _)

theorem self_le_zpow_clog {b : ℕ} (hb : 1 < b) {r : R} (hr : 0 < r) :
    r ≤ (b : R) ^ clog b r := by
  rw [← neg_log_inv_eq_clog hb hr, zpow_neg, le_inv_comm₀ hr (zpow_pos ..)]
  · exact zpow_log_le_self hb (inv_pos.mpr hr)
  · exact Nat.cast_pos.mpr (zero_le_one.trans_lt hb)

theorem zpow_pred_clog_lt_self {b : ℕ} {r : R} (hb : 1 < b) (hr : 0 < r) :
    (b : R) ^ (clog b r - 1) < r := by
  rw [← neg_log_inv_eq_clog hb hr, ← neg_add', zpow_neg, inv_lt_comm₀ _ hr]
  · exact lt_zpow_succ_log_self hb (inv_pos.mpr hr)
  · exact zpow_pos (Nat.cast_pos.mpr <| zero_le_one.trans_lt hb) _

@[simp]
theorem clog_one_right {b : ℕ} (hb : 1 < b) {h : (0 : R) < 1} : clog b (1 : R) hb h = 0 := by
  rw [clog_of_one_le_right hb le_rfl]
  simp

theorem clog_zpow {b : ℕ} (hb : 1 < b) (z : ℤ) {h : 0 < (b ^ z : R)} :
    clog b (b ^ z : R) hb h = z := by
  rw [← neg_log_inv_eq_clog hb h]
  simp only [← zpow_neg]
  rw [log_zpow hb, neg_neg]

@[gcongr, mono]
theorem clog_mono_right {b : ℕ} {hb : 1 < b} {r₁ r₂ : R} {h₀ : 0 < r₁} (h : r₁ ≤ r₂) :
    clog b r₁ ≤ clog b r₂ hb (lt_of_lt_of_le h₀ h) := by
  have h₀' : 0 < r₂ := lt_of_lt_of_le h₀ h
  rw [← neg_log_inv_eq_clog hb h₀, ← neg_log_inv_eq_clog hb h₀', neg_le_neg_iff]
  exact log_mono_right ((inv_le_inv₀ h₀' h₀).2 h)

variable (R) in
/-- Over suitable subtypes, `Int.clog` and `zpow` form a Galois insertion -/
def clogZPowGi {b : ℕ} (hb : 1 < b) :
    GaloisInsertion (fun r : Set.Ioi (0 : R) => Int.clog b (r : R) hb r.2) fun z : ℤ =>
      ⟨(b : R) ^ z, zpow_pos (mod_cast zero_lt_one.trans hb) z⟩ :=
  GaloisInsertion.monotoneIntro
    (fun _ _ hz => Subtype.coe_le_coe.mp <| (zpow_right_strictMono₀ <| mod_cast hb).monotone hz)
    (fun r₁ _ h => clog_mono_right (h₀ := r₁.2) h)
    (fun r => Subtype.coe_le_coe.mp <| self_le_zpow_clog hb r.2) fun _ => clog_zpow (R := R) hb _

/-- `Int.clog b` and `zpow b` form a Galois connection on positive elements. -/
theorem zpow_lt_iff_lt_clog {b : ℕ} (hb : 1 < b) {x : ℤ} {r : R} (hr : 0 < r) :
    (b : R) ^ x < r ↔ x < clog b r :=
  (@GaloisConnection.lt_iff_lt _ _ _ _ _ _ (clogZPowGi R hb).gc ⟨r, hr⟩ x).symm

/-- `Int.clog b` and `zpow b` form a Galois connection on positive elements. -/
theorem le_zpow_iff_clog_le {b : ℕ} (hb : 1 < b) {x : ℤ} {r : R} (hr : 0 < r) :
    r ≤ (b : R) ^ x ↔ clog b r ≤ x :=
  (@GaloisConnection.le_iff_le _ _ _ _ _ _ (clogZPowGi R hb).gc ⟨r, hr⟩ x).symm

end Int
