/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Yaël Dillies, Yury Kudryashov
-/
module

public import Mathlib.Data.Nat.BinaryRec
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Tactic.Bound.Attribute
public import Mathlib.Tactic.Contrapose
public import Mathlib.Tactic.Monotonicity.Attr

/-!
# Natural number logarithms

This file defines two `ℕ`-valued analogs of the logarithm of `n` with base `b`:
* `log b n`: Lower logarithm, or floor **log**. Greatest `k` such that `b^k ≤ n`, defined for
  `1 < b` and `n ≠ 0`.
* `clog b n`: Upper logarithm, or **c**eil **log**. Least `k` such that `n ≤ b^k`, defined for
  `1 < b` or `n ≤ 1`.

These are interesting because, for `1 < b`, `Nat.log b` and `Nat.clog b` are respectively right and
left adjoints of `(b ^ ·)`. See `le_log_iff_pow_le` and `clog_le_iff_le_pow`.

## Implementation notes

We define both functions using recursion on `b`.
In order to compute, e.g., `Nat.log b n`, we compute `e = Nat.log (b * b) n` first,
then figure out whether the answer is `2 * e` or `2 * e + 1`.
The actual implementations use fuel recursion so that `(by decide : Nat.log 2 20 = 4)` works.

Adapted from https://downloads.haskell.org/~ghc/9.0.1/docs/html/libraries/ghc-bignum-1.0/GHC-Num-BigNat.html#v:bigNatLogBase-35-

Note a tail-recursive version of `Nat.log` is also possible:
```
def logTR (b n : ℕ) : ℕ :=
  let rec go : ℕ → ℕ → ℕ | n, acc => if h : b ≤ n ∧ 1 < b then go (n / b) (acc + 1) else acc
  decreasing_by
    have : n / b < n := Nat.div_lt_self (by lia) h.2
    decreasing_trivial
  go n 0
```
but performs worse for large numbers than `Nat.log`:
```
#eval Nat.logTR 2 (2 ^ 1000000)
#eval Nat.log 2 (2 ^ 1000000)
```
-/

@[expose] public section

assert_not_exists OrderTop

namespace Nat

open Lean Elab Tactic in
/-- The default discharger for the side conditions of `Nat.log` (`1 < b` and `n ≠ 0`) and of
`Nat.clog` (`1 < b ∨ n ≤ 1`).

It closes the goal with a local hypothesis, by linear arithmetic from the local hypotheses, or by
evaluating a closed term. Other evidence is passed explicitly. It never chooses the base or the
argument: if they are not determined when the tactic runs, it fails instead of assigning them from
a hypothesis. -/
elab (name := natLogTac) "nat_log_tac" : tactic => do
  if (← instantiateMVars (← getMainTarget)).hasExprMVar then
    throwError "the base or the argument of the logarithm is not determined; pass the side \
      condition explicitly"
  evalTactic (← `(tactic|
    first
      | assumption
      | omega
      | decide
      | fail "the floor logarithm `Nat.log b n` needs `1 < b` and `n ≠ 0`, and the ceiling \
          logarithm `Nat.clog b n` needs `1 < b ∨ n ≤ 1`"))

/-! ### Floor logarithm -/


/-- `log b n` is the floor logarithm of `n` in base `b`: the largest `k : ℕ` such that
`b ^ k ≤ n`, so if `b ^ k = n`, it returns exactly `k`. The largest such `k` exists exactly when
`1 < b` and `n ≠ 0`: for `b ≤ 1` every `k` satisfies the inequality when `n ≠ 0`, and for `n = 0`
none does. The proofs `_hb` and `_hn` can usually be omitted, see `nat_log_tac`. -/
@[pp_nodot, nolint unusedArguments]
def log (b n : ℕ) (_hb : 1 < b := by nat_log_tac) (_hn : n ≠ 0 := by nat_log_tac) : ℕ :=
  (go b n).2 where
  /-- An auxiliary definition for `Nat.log`.

  For `b > 1`, `n ≠ 0`, `n < b ^ fuel`, `Nat.log.go n b fuel = (n / b ^ b.log n, b.log n)`. -/
  go : ℕ → ℕ → ℕ × ℕ
  | _, 0 => (n, 0)
  | b, fuel + 1 =>
    if n < b then
      (n, 0)
    else
      let (q, e) := go (b * b) fuel
      if q < b then (q, 2 * e) else (q / b, 2 * e + 1)

private theorem log.go_aux {n b fuel : ℕ} (hb : 1 < b) (hfuel : n < b ^ (fuel + 1)) (hbn : b ≤ n) :
    n < (b * b) ^ fuel := by
  obtain hfuel₀ : fuel ≠ 0 := by rintro rfl; simp [Nat.not_lt_of_le hbn] at hfuel
  rw [← Nat.pow_two, ← Nat.pow_mul]
  exact Nat.lt_of_lt_of_le hfuel <| Nat.pow_le_pow_right (by grind) (by grind)

lemma log.go_spec {b n fuel : ℕ} (hb : 1 < b) (hn : n ≠ 0) (hfuel : n < b ^ fuel) :
    (log.go n b fuel).1 = n / b ^ (log.go n b fuel).2 ∧
      b ^ (log.go n b fuel).2 ≤ n ∧ n < b ^ ((log.go n b fuel).2 + 1) := by
  induction fuel generalizing b with
  | zero => simp_all
  | succ fuel ih =>
    cases Nat.lt_or_ge n b with
    | inl hnb =>
      simp [go, hnb, one_le_iff_ne_zero, hn]
    | inr hnb =>
      rcases ih (Nat.one_mul 1 ▸ Nat.mul_lt_mul_of_lt_of_lt hb hb) (go_aux hb hfuel hnb)
        with ⟨ih₁, ih₂, ih₃⟩
      simp_all only [go, ite_eq_right (Nat.not_lt_of_le hnb), ← Nat.pow_two, ← Nat.pow_mul,
        Nat.div_lt_iff_lt_mul, Nat.pow_pos (Nat.zero_lt_of_lt hb), Nat.div_div_eq_div_mul,
        ← Nat.pow_add_one, ← Nat.pow_add_one', Nat.mul_add_one]
      split <;> simp_all

theorem log_lt_iff_lt_pow {b : ℕ} (hb : 1 < b) {x y : ℕ} (hy : y ≠ 0) :
    log b y < x ↔ y < b ^ x := by
  rcases log.go_spec hb hy (Nat.lt_pow_self hb) with ⟨-, H₁, H₂⟩
  rw [log]
  cases Nat.lt_or_ge (log.go y b y).snd x with
  | inl h =>
    exact iff_of_true h <| Nat.lt_of_lt_of_le H₂ <| Nat.pow_le_pow_right (Nat.zero_lt_of_lt hb) h
  | inr h =>
    refine iff_of_false (Nat.not_lt_of_ge h) <| Nat.not_lt_of_ge <| Nat.le_trans ?_ H₁
    exact Nat.pow_le_pow_right (Nat.zero_lt_of_lt hb) h

@[simp]
theorem log_eq_zero_iff {b n : ℕ} (hb : 1 < b) (hn : n ≠ 0) : log b n = 0 ↔ n < b := by
  rw [← Nat.lt_one_iff, log_lt_iff_lt_pow hb hn, Nat.pow_one]

theorem log_of_lt {b n : ℕ} (hb : 1 < b) (hn : n ≠ 0) (hnb : n < b) : log b n = 0 :=
  (log_eq_zero_iff hb hn).2 hnb

@[simp]
theorem log_pos_iff {b n : ℕ} (hb : 1 < b) (hn : n ≠ 0) : 0 < log b n ↔ b ≤ n := by
  rw [Nat.pos_iff_ne_zero, Ne, log_eq_zero_iff hb hn, not_lt]

@[bound]
theorem log_pos {b n : ℕ} (hb : 1 < b) (hbn : b ≤ n) : 0 < log b n :=
  (log_pos_iff hb (by omega)).2 hbn

theorem log_of_one_lt_of_le {b n : ℕ} (h : 1 < b) (hn : b ≤ n) :
    log b n = log b (n / b) h (Nat.div_pos hn (Nat.zero_lt_of_lt h)).ne' + 1 := by
  apply eq_of_forall_gt_iff
  rintro (_ | c)
  · simp
  · have : n / b ≠ 0 := (Nat.div_pos hn (Nat.zero_lt_of_lt h)).ne'
    rw [log_lt_iff_lt_pow h (by omega), Nat.add_lt_add_iff_right, log_lt_iff_lt_pow h this,
      Nat.pow_add_one, Nat.div_lt_iff_lt_mul (Nat.zero_lt_of_lt h)]

@[simp]
theorem log_one_right {b : ℕ} (hb : 1 < b) : log b 1 = 0 :=
  log_of_lt hb Nat.one_ne_zero hb

/-- `(b ^ ·)` and `log b` form a Galois connection. See also `Nat.pow_le_of_le_log` and
`Nat.le_log_of_pow_le` for the individual implications. -/
theorem le_log_iff_pow_le {b : ℕ} (hb : 1 < b) {x y : ℕ} (hy : y ≠ 0) :
    x ≤ log b y ↔ b ^ x ≤ y :=
  le_iff_le_iff_lt_iff_lt.mpr <| log_lt_iff_lt_pow hb hy

theorem pow_le_of_le_log {b x y : ℕ} {hb : 1 < b} {hy : y ≠ 0} (h : x ≤ log b y) : b ^ x ≤ y :=
  (le_log_iff_pow_le hb hy).1 h

/-- A positive power of `b` below `y` shows that `y ≠ 0`. -/
theorem ne_zero_of_pow_le {b x y : ℕ} (hb : 1 < b) (h : b ^ x ≤ y) : y ≠ 0 :=
  (Nat.lt_of_lt_of_le (Nat.pow_pos (Nat.zero_lt_of_lt hb)) h).ne'

theorem le_log_of_pow_le {b x y : ℕ} (hb : 1 < b) (h : b ^ x ≤ y) :
    x ≤ log b y hb (ne_zero_of_pow_le hb h) :=
  (le_log_iff_pow_le hb _).2 h

theorem pow_log_le_self {b : ℕ} (hb : 1 < b) {x : ℕ} (hx : x ≠ 0) : b ^ log b x ≤ x :=
  pow_le_of_le_log le_rfl

theorem log_lt_of_lt_pow {b x y : ℕ} (hb : 1 < b) (hy : y ≠ 0) : y < b ^ x → log b y < x :=
  (log_lt_iff_lt_pow hb hy).2

theorem lt_pow_of_log_lt {b x y : ℕ} (hb : 1 < b) (hy : y ≠ 0) : log b y < x → y < b ^ x :=
  (log_lt_iff_lt_pow hb hy).1

lemma log_lt_self {b : ℕ} (hb : 1 < b) {x : ℕ} (hx : x ≠ 0) : log b x < x :=
  log_lt_of_lt_pow hb hx <| Nat.lt_pow_self hb

lemma log_le_self {b : ℕ} (hb : 1 < b) {x : ℕ} (hx : x ≠ 0) : log b x ≤ x :=
  (log_lt_self hb hx).le

theorem lt_pow_succ_log_self {b : ℕ} (hb : 1 < b) {x : ℕ} (hx : x ≠ 0) :
    x < b ^ (log b x).succ :=
  lt_pow_of_log_lt hb hx (lt_succ_self _)

theorem log_eq_iff {b m n : ℕ} (hb : 1 < b) (hn : n ≠ 0) :
    log b n = m ↔ b ^ m ≤ n ∧ n < b ^ (m + 1) := by
  rw [le_antisymm_iff, ← Nat.lt_succ_iff, le_log_iff_pow_le hb hn, log_lt_iff_lt_pow hb hn,
    and_comm]

/-- A pair of bounds `b ^ m ≤ n < b ^ (m + 1)` determines the floor logarithm; they also force
`1 < b` and `n ≠ 0`. -/
theorem log_eq_of_pow_le_of_lt_pow {b m n : ℕ} {hb : 1 < b} {hn : n ≠ 0} (h₁ : b ^ m ≤ n)
    (h₂ : n < b ^ (m + 1)) : log b n = m :=
  (log_eq_iff hb hn).2 ⟨h₁, h₂⟩

@[simp]
theorem log_pow {b : ℕ} (hb : 1 < b) (x : ℕ) {h : b ^ x ≠ 0} : log b (b ^ x) hb h = x :=
  log_eq_of_pow_le_of_lt_pow le_rfl (Nat.pow_lt_pow_right hb x.lt_succ_self)

theorem log_eq_one_iff {b n : ℕ} {hb : 1 < b} {hn : n ≠ 0} :
    log b n = 1 ↔ b ≤ n ∧ n < b * b := by
  rw [log_eq_iff hb hn, Nat.pow_add, Nat.pow_one]

@[simp]
theorem log_mul_base {b n : ℕ} (hb : 1 < b) (hn : n ≠ 0) {h : n * b ≠ 0} :
    log b (n * b) hb h = log b n + 1 := by
  apply log_eq_of_pow_le_of_lt_pow <;> rw [pow_succ', Nat.mul_comm b]
  exacts [Nat.mul_le_mul_right _ (pow_log_le_self hb hn),
    (Nat.mul_lt_mul_right (Nat.zero_lt_one.trans hb)).2 (lt_pow_succ_log_self hb hn)]

@[mono, gcongr]
theorem log_mono_right {b n m : ℕ} {hb : 1 < b} {hn : n ≠ 0} (h : n ≤ m) :
    log b n ≤ log b m :=
  le_log_of_pow_le hb ((pow_log_le_self hb hn).trans h)

theorem log_lt_log_succ_iff {b n : ℕ} (hb : 1 < b) (hn : n ≠ 0) :
    log b n < log b (n + 1) ↔ b ^ log b (n + 1) = n + 1 := by
  refine ⟨fun H ↦ ?_, fun H ↦ ?_⟩
  · apply le_antisymm _ (Nat.lt_pow_of_log_lt hb (by omega) H)
    exact Nat.pow_log_le_self hb (Ne.symm (Nat.zero_ne_add_one n))
  · apply Nat.log_lt_of_lt_pow hb hn
    simp [H]

theorem log_eq_log_succ_iff {b n : ℕ} (hb : 1 < b) (hn : n ≠ 0) :
    log b n = log b (n + 1) ↔ b ^ log b (n + 1) ≠ n + 1 := by
  rw [ne_eq, ← log_lt_log_succ_iff hb hn, not_lt]
  simp only [le_antisymm_iff, and_iff_right_iff_imp]
  exact fun _ ↦ log_mono_right (le_add_right n 1)

theorem log_anti_left {b c n : ℕ} (hc : 1 < c) (hb : c ≤ b) {hn : n ≠ 0} :
    log b n (Nat.lt_of_lt_of_le hc hb) hn ≤ log c n := by
  apply le_log_of_pow_le hc
  calc
    c ^ log b n (Nat.lt_of_lt_of_le hc hb) hn ≤ b ^ log b n (Nat.lt_of_lt_of_le hc hb) hn :=
      Nat.pow_le_pow_left hb _
    _ ≤ n := pow_log_le_self _ hn

@[gcongr, mono]
theorem log_mono {b c m n : ℕ} (hc : 1 < c) (hb : c ≤ b) {hm : m ≠ 0} (hmn : m ≤ n) :
    log b m (Nat.lt_of_lt_of_le hc hb) hm ≤ log c n :=
  (log_anti_left hc hb).trans (log_mono_right hmn)

theorem log_div_base {b n : ℕ} (hb : 1 < b) (hbn : b ≤ n) {h : n / b ≠ 0} :
    log b (n / b) hb h = log b n - 1 := by
  rw [log_of_one_lt_of_le hb hbn, Nat.add_sub_cancel_right]

lemma log_div_base_pow {b n k : ℕ} (hb : 1 < b) (hbn : b ^ k ≤ n) {h : n / b ^ k ≠ 0} :
    log b (n / b ^ k) hb h = log b n hb (ne_zero_of_pow_le hb hbn) - k := by
  have hn : n ≠ 0 := ne_zero_of_pow_le hb hbn
  have hpos : 0 < b ^ k := Nat.pow_pos (Nat.zero_lt_of_lt hb)
  have h1 := pow_log_le_self hb h
  have h2 := lt_pow_succ_log_self hb h
  rw [Nat.le_div_iff_mul_le hpos, ← Nat.pow_add] at h1
  rw [Nat.div_lt_iff_lt_mul hpos, ← Nat.pow_add, Nat.succ_add] at h2
  have := (log_eq_iff hb hn).2 ⟨h1, h2⟩
  omega

@[simp]
theorem log_div_mul_self {b n : ℕ} (hb : 1 < b) (hbn : b ≤ n) {h : n / b * b ≠ 0} :
    log b (n / b * b) hb h = log b n := by
  have hnb : n / b ≠ 0 := (Nat.div_pos hbn (by omega)).ne'
  rw [log_mul_base hb hnb, log_div_base hb hbn,
    Nat.sub_add_cancel (succ_le_iff.2 <| log_pos hb hbn)]

theorem add_pred_div_lt {b n : ℕ} (hb : 1 < b) (hn : 2 ≤ n) : (n + b - 1) / b < n := by
  rw [div_lt_iff_lt_mul (by lia), ← succ_le_iff, ← pred_eq_sub_one,
    succ_pred_eq_of_pos (by lia)]
  exact Nat.add_le_mul hn hb

lemma log_two_bit {b n} (hn : n ≠ 0) {h : n.bit b ≠ 0} :
    Nat.log 2 (n.bit b) Nat.one_lt_two h = Nat.log 2 n + 1 := by
  have h1 := pow_log_le_self Nat.one_lt_two hn
  have h2 := lt_pow_succ_log_self Nat.one_lt_two hn
  rw [Nat.pow_succ] at h2
  rw [log_eq_iff Nat.one_lt_two h, Nat.pow_succ, Nat.pow_succ]
  cases b <;> simp only [Nat.bit, Bool.cond_false, Bool.cond_true] <;> omega

lemma log2_eq_log_two {n : ℕ} (hn : n ≠ 0) : Nat.log2 n = Nat.log 2 n := by
  apply eq_of_forall_le_iff
  intro m
  rw [Nat.le_log2 hn, Nat.le_log_iff_pow_le Nat.one_lt_two hn]

@[simp]
lemma log_pow_left {b k n : ℕ} (hb : 1 < b) (hk : k ≠ 0) (hn : n ≠ 0) {h : 1 < b ^ k} :
    log (b ^ k) n h hn = log b n / k := by
  refine eq_of_forall_le_iff fun c ↦ ?_
  rw [le_log_iff_pow_le h hn, Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hk),
    le_log_iff_pow_le hb hn, Nat.pow_mul']

/-! ### Ceil logarithm -/


/-- `clog b n` is the ceiling logarithm of `n` in base `b`: the smallest `k : ℕ` such that
`n ≤ b ^ k`, so if `b ^ k = n`, it returns exactly `k`. The smallest such `k` exists exactly when
`1 < b` or `n ≤ 1`: for `n ≤ 1` it is `0`, and for `b ≤ 1` and `n ≥ 2` no `k` satisfies the
inequality. The proof `_h` can usually be omitted, see `nat_log_tac`. -/
@[pp_nodot, nolint unusedArguments]
def clog (b n : ℕ) (_h : 1 < b ∨ n ≤ 1 := by nat_log_tac) : ℕ :=
  if 1 < b ∧ 1 < n then (go b n).2 + 1 else 0 where
  /-- An auxiliary definition for `Nat.clog`.

  For `n > 1`, `b > 1`, `n ≤ b ^ fuel`, returns `(b ^ clog b n / n, clog b n - 1)`.
  -/
  go : ℕ → ℕ → ℕ × ℕ
  | b, 0 => (b / n, 0)
  | b, fuel + 1 =>
    if n ≤ b then (b / n, 0)
    else
      let (q, e) := go (b * b) fuel
      if q < b then (q, 2 * e + 1) else (q / b, 2 * e)

theorem clog_of_right_le_one {n : ℕ} (hn : n ≤ 1) (b : ℕ) : clog b n = 0 := by
  grind [clog]

@[simp] lemma clog_zero_right (b : ℕ) : clog b 0 = 0 := clog_of_right_le_one (Nat.zero_le _) _

@[simp]
theorem clog_one_right (b : ℕ) : clog b 1 = 0 :=
  clog_of_right_le_one le_rfl _

theorem clog.go_spec {n b fuel} (hn : 1 < n) (hb : 1 < b) (hfuel : n < b ^ fuel) :
    (go n b fuel).1 = b ^ ((go n b fuel).2 + 1) / n ∧
      b ^ (go n b fuel).2 < n ∧ n ≤ b ^ ((go n b fuel).2 + 1) := by
  induction fuel generalizing b with
  | zero => simp_all
  | succ fuel ih =>
    cases Nat.lt_or_ge b n with
    | inr hbn => simp_all [go]
    | inl hbn =>
      rcases ih (Nat.one_mul 1 ▸ Nat.mul_lt_mul_of_lt_of_lt hb hb)
        (log.go_aux hb hfuel (Nat.le_of_lt hbn)) with ⟨ih₁, ih₂, ih₃⟩
      simp_all only [go, ite_eq_right (Nat.not_le_of_gt hbn), ← Nat.pow_two, ← Nat.pow_mul,
        Nat.div_lt_iff_lt_mul (Nat.zero_lt_of_lt hbn), Nat.div_div_eq_div_mul,
        Nat.mul_comm n b, Nat.mul_add_one, @Nat.pow_add_one' _ (2 * _ + 1),
        Nat.mul_lt_mul_left, Nat.mul_div_mul_left, Nat.zero_lt_of_lt hb]
      split <;> simp_all [Nat.mul_add_one, Nat.pow_add_one']

/-- For `b > 1`, `clog b` and `(b ^ ·)` form a Galois connection. -/
theorem clog_le_iff_le_pow {b : ℕ} (hb : 1 < b) {x y : ℕ} : clog b x ≤ y ↔ x ≤ b ^ y := by
  fun_cases clog with
  | case1 h =>
    rcases clog.go_spec h.2 hb (Nat.lt_pow_self hb) with ⟨-, H₁, H₂⟩
    cases Nat.lt_or_ge (clog.go x b x).2 y with
    | inl hy =>
      rw [← Nat.add_one_le_iff] at hy
      exact iff_of_true hy <| Nat.le_trans H₂ <| Nat.pow_le_pow_right (Nat.zero_lt_of_lt hb) hy
    | inr hy =>
      apply_rules [iff_of_false, Nat.not_le_of_gt, Nat.lt_add_one_of_le]
      exact Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (Nat.zero_lt_of_lt hb) hy) H₁
  | case2 h => grind [Nat.one_le_pow]

theorem clog_pos {b n : ℕ} (hb : 1 < b) (hn : 1 < n) : 0 < clog b n := by
  rw [clog, ite_eq_left]
  exacts [Nat.succ_pos _, ⟨hb, hn⟩]

theorem clog_of_one_lt {b n : ℕ} (hb : 1 < b) (hn : 1 < n) :
    clog b n = clog b ((n + b - 1) / b) + 1 := by
  apply eq_of_forall_ge_iff
  rintro (_ | c)
  · simp [Nat.ne_of_gt <| clog_pos hb hn]
  · simp only [clog_le_iff_le_pow hb, Nat.pow_add_one, Nat.add_le_add_iff_right,
      Nat.zero_lt_of_lt hb, div_le_iff_le_mul]
    grind

theorem clog_of_two_le {b n : ℕ} (hb : 1 < b) (hn : 2 ≤ n) :
    clog b n = clog b ((n + b - 1) / b) + 1 :=
  clog_of_one_lt hb hn

theorem clog_eq_one {b n : ℕ} (hn : 2 ≤ n) (h : n ≤ b) : clog b n = 1 := by
  rw [clog_of_two_le (hn.trans h) hn, clog_of_right_le_one]
  rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul] <;> lia

theorem clog_le_of_le_pow {b x y : ℕ} {h' : 1 < b ∨ x ≤ 1} (h : x ≤ b ^ y) : clog b x ≤ y := by
  rcases h' with hb | hx
  · rwa [clog_le_iff_le_pow hb]
  · rw [clog_of_right_le_one hx]
    exact Nat.zero_le _

theorem lt_clog_iff_pow_lt {b : ℕ} (hb : 1 < b) {x y : ℕ} : y < clog b x ↔ b ^ y < x :=
  lt_iff_lt_of_le_iff_le (clog_le_iff_le_pow hb)

theorem pow_lt_of_lt_clog {b x y : ℕ} {h' : 1 < b ∨ x ≤ 1} (h : y < clog b x) : b ^ y < x :=
  lt_imp_lt_of_le_imp_le clog_le_of_le_pow h

@[simp]
theorem clog_pow (b x : ℕ) (hb : 1 < b) : clog b (b ^ x) = x :=
  eq_of_forall_ge_iff fun z ↦ by rw [clog_le_iff_le_pow hb, Nat.pow_le_pow_iff_right hb]

theorem pow_pred_clog_lt_self {b : ℕ} (hb : 1 < b) {x : ℕ} (hx : 1 < x) :
    b ^ (clog b x).pred < x := by
  rw [← lt_clog_iff_pow_lt hb]
  exact pred_lt (clog_pos hb hx).ne'

theorem le_pow_clog {b : ℕ} (hb : 1 < b) (x : ℕ) : x ≤ b ^ clog b x :=
  (clog_le_iff_le_pow hb).1 le_rfl

@[mono, gcongr]
theorem clog_mono_right (b : ℕ) {n m : ℕ} {hm : 1 < b ∨ m ≤ 1} (h : n ≤ m) :
    clog b n ≤ clog b m := by
  rcases hm with hb | hm
  · rw [clog_le_iff_le_pow hb]
    exact h.trans (le_pow_clog hb _)
  · rw [clog_of_right_le_one (h.trans hm)]
    exact zero_le _

theorem clog_anti_left {b c n : ℕ} (hc : 1 < c) (hb : c ≤ b) : clog b n ≤ clog c n := by
  rw [clog_le_iff_le_pow (lt_of_lt_of_le hc hb)]
  calc
    n ≤ c ^ clog c n := le_pow_clog hc _
    _ ≤ b ^ clog c n := Nat.pow_le_pow_left hb _

theorem clog_monotone {b : ℕ} (hb : 1 < b) : Monotone fun n => clog b n :=
  fun _ _ h => clog_mono_right b h

@[mono, gcongr]
theorem clog_mono {b c m n : ℕ} (hc : 1 < c) (hb : c ≤ b) (hmn : m ≤ n) :
    clog b m ≤ clog c n :=
  (clog_anti_left hc hb).trans <| clog_mono_right c hmn

@[simp]
theorem log_le_clog {b n : ℕ} (hb : 1 < b) (hn : n ≠ 0) : log b n ≤ clog b n :=
  (Nat.pow_le_pow_iff_right hb).1 ((pow_log_le_self hb hn).trans <| le_pow_clog hb _)

theorem clog_lt_clog_succ_iff {b n : ℕ} (hb : 1 < b) :
    clog b n < clog b (n + 1) ↔ b ^ clog b n = n := by
  refine ⟨fun H ↦ ?_, fun H ↦ ?_⟩
  · apply le_antisymm _ (le_pow_clog hb n)
    apply le_of_lt_succ
    exact (lt_clog_iff_pow_lt hb).mp H
  · rw [lt_clog_iff_pow_lt hb, H]
    exact n.lt_add_one

theorem clog_eq_clog_succ_iff {b n : ℕ} (hb : 1 < b) :
    clog b n = clog b (n + 1) ↔ b ^ clog b n ≠ n := by
  rw [ne_eq, ← clog_lt_clog_succ_iff hb, not_lt]
  simp only [le_antisymm_iff, and_iff_right_iff_imp]
  exact fun _ ↦ clog_monotone hb (le_add_right n 1)

/-- This lemma says that `⌈log (b ^ k) n⌉ = ⌈(⌈log b n⌉ / k)⌉`, using operations on natural numbers
to express this equality.

Since Lean has no dedicated function for the ceiling division,
we use `(a + (b - 1)) / b` for `⌈a / b⌉`. -/
theorem clog_pow_left {b k n : ℕ} (hb : 1 < b) (hk : k ≠ 0) {h : 1 < b ^ k ∨ n ≤ 1} :
    clog (b ^ k) n h = (clog b n + (k - 1)) / k := by
  refine eq_of_forall_lt_iff fun c ↦ ?_
  rw [lt_clog_iff_pow_lt (Nat.one_lt_pow hk hb), Nat.lt_div_iff_mul_lt (Nat.pos_of_ne_zero hk),
    Nat.add_sub_cancel, lt_clog_iff_pow_lt hb, Nat.pow_mul']

end Nat
