/-
Copyright (c) 2023 Matthew Robert Ballard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Robert Ballard, Yury Kudryashov
-/
module

public import Mathlib.Basic.Logic.Basic

import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Nat.Notation

/-!
# The maximal power of one natural number dividing another

For `1 < p` and `n ≠ 0`, `p.maxPowDvdDiv n hpn` returns the largest `k : ℕ` such that `p ^ k ∣ n`,
together with the ratio `n / p ^ k`. It defines the `p`-adic valuation `padicValNat p n` of a
natural number, which exists exactly when `p ≠ 1` and `n ≠ 0`, and the quotient `n.divMaxPow p` of
`n` by the largest power of `p` dividing it.

The implementation of `maxPowDvdDiv` recurses through `p, p ^ 2, p ^ 4, …`, so that `padicValNat`
is fast to evaluate.
-/

@[expose] public section

namespace Nat

/-- The extensible part of `padic_val_tac`: each `macro_rules` alternative for `padic_val_core`
tries one way to close a side condition `p ≠ 1` or `n ≠ 0` of a `p`-adic valuation. -/
syntax (name := padicValCore) "padic_val_core" : tactic

macro_rules | `(tactic| padic_val_core) => `(tactic| first | assumption | omega | decide)

open Lean Elab Tactic in
/-- The default discharger for the side conditions `p ≠ 1` and `n ≠ 0` of the `p`-adic valuation
`padicValNat p n` and of the valuations built on it.

It closes the goal with `padic_val_core`: with a local hypothesis, by linear arithmetic from the
local hypotheses, by evaluating a closed term, or by the extensions of later files. Other evidence
is passed explicitly. It never chooses `p` or `n`: if they are not determined when the tactic runs,
it fails instead of assigning them from a hypothesis. -/
elab (name := padicValTac) "padic_val_tac" : tactic => do
  if (← instantiateMVars (← getMainTarget)).hasExprMVar then
    throwError "the base or the argument of the valuation is not determined; pass the side \
      condition explicitly"
  evalTactic (← `(tactic|
    first
      | padic_val_core
      | fail "the `p`-adic valuation needs `p ≠ 1` and a nonzero argument"))

/--
For `1 < p` and `n ≠ 0`, find the largest `k : ℕ` such that `p ^ k ∣ n`, together with the ratio
`n / p ^ k`.

The implementation recurses from `(p, n)` to `(p * p, n)`,
so the recursion depth is $$O(\log(\nu_p(n)))$$, thus it is $$O(\log(\log(n)))$$.
-/
def maxPowDvdDiv (p n : ℕ) (hpn : 1 < p ∧ n ≠ 0) : ℕ × ℕ :=
  go p hpn
  where
  /-- Auxiliary definition for `Nat.maxPowDvdDiv`. -/
  go (p : ℕ) (hp : 1 < p ∧ n ≠ 0) :=
    if hmod : n % p = 0 then
      let (e, q) := go (p * p) <| by simp [Nat.one_lt_mul_iff, hp, Nat.lt_trans Nat.one_pos]
      if q % p = 0 then (2 * e + 1, q / p) else (2 * e, q)
    else
      (0, n)
  termination_by n / p
  decreasing_by
    rw [← Nat.dvd_iff_mod_eq_zero] at hmod
    rcases hmod with ⟨m, rfl⟩
    have hp₀ : 0 < p := Nat.lt_trans Nat.one_pos hp.1
    rw [Nat.mul_div_mul_left _ _ hp₀, Nat.mul_div_cancel_left _ hp₀]
    exact Nat.div_lt_self (by grind) hp.1

set_option linter.unusedVariables false in
/-- The `p`-adic valuation of a natural number `n`: the largest natural number `k` such that
`p ^ k ∣ n`. It exists exactly when `p ≠ 1` and `n ≠ 0`, and it is `0` for `p = 0`. The proofs
`hp` and `hn` can usually be omitted, see `padic_val_tac`. -/
@[nolint unusedArguments]
def _root_.padicValNat (p n : ℕ) (hp : p ≠ 1 := by padic_val_tac)
    (hn : n ≠ 0 := by padic_val_tac) : ℕ :=
  if h : 1 < p then (maxPowDvdDiv p n ⟨h, hn⟩).1 else 0

/-- The quotient of `n` by the largest power of `p` that divides `n`. If `p ≤ 1` or `n = 0`, every
power of `p` that divides `n` gives the quotient `n`. -/
def divMaxPow (n p : ℕ) : ℕ :=
  if h : 1 < p ∧ n ≠ 0 then (maxPowDvdDiv p n h).2 else n

theorem maxPowDvdDiv.go_spec {n p : ℕ} (hnp) :
    (go n p hnp).2 * p ^ (go n p hnp).1 = n ∧ ¬p ∣ (go n p hnp).2 := by
  fun_induction go with
  | case1 p hp hmod e q heq hqp ih =>
    rw [heq] at ih
    rcases ih with ⟨rfl, hdvd⟩
    have hp₀ : 0 < p := Nat.lt_trans Nat.one_pos hp.1
    simp_all [← Nat.dvd_iff_mod_eq_zero, Nat.pow_add', ← Nat.mul_assoc, Nat.div_mul_cancel,
      Nat.two_mul, Nat.mul_pow]
  | case2 p hp hmod e q heq hqp ih =>
    rw [heq] at ih
    rcases ih with ⟨rfl, hdvd⟩
    simp_all [Nat.dvd_iff_mod_eq_zero, Nat.two_mul, Nat.mul_pow, Nat.pow_add]
  | case3 =>
    simp_all [Nat.dvd_iff_mod_eq_zero]

theorem maxPowDvdDiv_spec {p n : ℕ} (hpn : 1 < p ∧ n ≠ 0) :
    (maxPowDvdDiv p n hpn).2 * p ^ (maxPowDvdDiv p n hpn).1 = n ∧
      ¬p ∣ (maxPowDvdDiv p n hpn).2 :=
  maxPowDvdDiv.go_spec hpn

@[simp]
theorem fst_maxPowDvdDiv {p n : ℕ} (hpn : 1 < p ∧ n ≠ 0) :
    (p.maxPowDvdDiv n hpn).1 = padicValNat p n (Nat.ne_of_gt hpn.1) hpn.2 := by
  simp [padicValNat, hpn.1]

@[simp]
theorem snd_maxPowDvdDiv {p n : ℕ} (hpn : 1 < p ∧ n ≠ 0) :
    (p.maxPowDvdDiv n hpn).2 = n.divMaxPow p := by
  simp [divMaxPow, hpn]

@[simp]
theorem _root_.padicValNat_zero_left {n : ℕ} (hn : n ≠ 0) :
    padicValNat 0 n Nat.zero_ne_one hn = 0 := by
  simp [padicValNat]

@[simp]
theorem divMaxPow_zero_right (n : ℕ) : divMaxPow n 0 = n := by simp [divMaxPow]

@[simp]
theorem divMaxPow_one_right (n : ℕ) : divMaxPow n 1 = n := by simp [divMaxPow]

@[simp]
theorem divMaxPow_zero_left (p : ℕ) : divMaxPow 0 p = 0 := by simp [divMaxPow]

theorem maxPowDvdDiv_of_not_dvd {p n : ℕ} (hpn : 1 < p ∧ n ≠ 0) (h : ¬p ∣ n) :
    maxPowDvdDiv p n hpn = (0, n) := by
  cases n with
  | zero => simp at h
  | succ n => simp [maxPowDvdDiv, Nat.dvd_iff_mod_eq_zero.not.mp h, maxPowDvdDiv.go]

@[simp]
theorem maxPowDvdDiv_one_right {p : ℕ} (hpn : 1 < p ∧ 1 ≠ 0) : maxPowDvdDiv p 1 hpn = (0, 1) :=
  maxPowDvdDiv_of_not_dvd hpn (Nat.not_dvd_of_pos_of_lt Nat.one_pos hpn.1)

@[simp]
theorem _root_.padicValNat_one_right {p : ℕ} (hp : p ≠ 1) :
    padicValNat p 1 hp Nat.one_ne_zero = 0 := by
  simp [padicValNat]

@[simp]
theorem divMaxPow_one_left (p : ℕ) : divMaxPow 1 p = 1 := by
  simp [divMaxPow]

@[simp]
theorem divMaxPow_mul_pow_padicValNat {p n : ℕ} (hp : p ≠ 1) (hn : n ≠ 0) :
    divMaxPow n p * p ^ padicValNat p n hp hn = n := by
  by_cases h : 1 < p
  · rw [divMaxPow, dite_eq_left ⟨h, hn⟩, ← fst_maxPowDvdDiv ⟨h, hn⟩]
    exact (maxPowDvdDiv_spec ⟨h, hn⟩).1
  · obtain rfl : p = 0 := by omega
    simp

@[simp]
theorem pow_padicValNat_mul_divMaxPow {p n : ℕ} (hp : p ≠ 1) (hn : n ≠ 0) :
    p ^ padicValNat p n hp hn * divMaxPow n p = n := by
  rw [Nat.mul_comm, divMaxPow_mul_pow_padicValNat]

theorem _root_.pow_padicValNat_dvd {p n : ℕ} {hp : p ≠ 1} {hn : n ≠ 0} :
    p ^ padicValNat p n hp hn ∣ n :=
  ⟨divMaxPow n p, (pow_padicValNat_mul_divMaxPow hp hn).symm⟩

theorem padicValNat_lt_self {p n : ℕ} (hp : p ≠ 1) (hn : n ≠ 0) : padicValNat p n hp hn < n := by
  match p, hp with
  | 0, _ => simp [Nat.pos_of_ne_zero hn]
  | 1, hp => exact absurd rfl hp
  | p + 2, _ =>
    apply (p + 2 |>.pow_lt_pow_iff_right <| by lia).mp
    apply Nat.lt_of_le_of_lt ?_ <| Nat.lt_pow_self <| by lia
    exact le_of_dvd (Nat.pos_of_ne_zero hn) pow_padicValNat_dvd

theorem padicValNat_le_self {p n : ℕ} (hp : p ≠ 1) (hn : n ≠ 0) : padicValNat p n hp hn ≤ n :=
  Nat.le_of_lt <| padicValNat_lt_self hp hn

theorem not_dvd_divMaxPow {p n : ℕ} (hp : 1 < p) (hn : n ≠ 0) : ¬p ∣ divMaxPow n p := by
  rw [divMaxPow, dite_eq_left ⟨hp, hn⟩]
  exact (maxPowDvdDiv_spec ⟨hp, hn⟩).2

private theorem pow_dvd_iff_le_of_spec {p k n a b : ℕ} (hp : 1 < p) (hn : n ≠ 0)
    (hab : p ^ a * b = n) (hb : ¬p ∣ b) : p ^ k ∣ n ↔ k ≤ a := by
  subst hab
  cases Nat.lt_or_ge a k with
  | inl hlt =>
    refine iff_of_false (fun hdvd ↦ ?_) (Nat.not_le_of_lt hlt)
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    rw [Nat.add_assoc, Nat.pow_add,
      Nat.mul_dvd_mul_iff_left (Nat.pow_pos (Nat.zero_lt_of_lt hp))] at hdvd
    exact hb <| Nat.dvd_of_pow_dvd (Nat.le_add_left 1 l) hdvd
  | inr hle =>
    refine iff_of_true (Nat.dvd_mul_right_of_dvd ?_ _) hle
    exact Nat.pow_dvd_pow p hle

/-- For `p ≠ 1` and `n ≠ 0`, `padicValNat p n` is the largest power of `p` that divides `n`. -/
theorem pow_dvd_iff_le_padicValNat {p k n : ℕ} (hp : p ≠ 1) (hn : n ≠ 0) :
    p ^ k ∣ n ↔ k ≤ padicValNat p n hp hn := by
  obtain rfl | hp₁ : p = 0 ∨ 1 < p := by grind
  · rcases k.eq_zero_or_pos with rfl | hk <;> simp [Nat.ne_of_gt, *]
  · exact pow_dvd_iff_le_of_spec hp₁ hn (pow_padicValNat_mul_divMaxPow hp hn)
      (not_dvd_divMaxPow hp₁ hn)

theorem maxPowDvdDiv_of_pow_mul_eq {p n k l : ℕ} (hpn : 1 < p ∧ n ≠ 0) (h : p ^ k * l = n)
    (hl : ¬p ∣ l) : maxPowDvdDiv p n hpn = (k, l) := by
  obtain ⟨hp, hn⟩ := hpn
  have hk : k = (p.maxPowDvdDiv n ⟨hp, hn⟩).1 := by
    rw [fst_maxPowDvdDiv]
    apply Nat.le_antisymm
    · rw [← pow_dvd_iff_le_padicValNat (Nat.ne_of_gt hp) hn, pow_dvd_iff_le_of_spec hp hn h hl]
      apply Nat.le_refl
    · rw [← pow_dvd_iff_le_of_spec hp hn h hl, pow_dvd_iff_le_padicValNat (Nat.ne_of_gt hp) hn]
      apply Nat.le_refl
  have hq := (maxPowDvdDiv_spec ⟨hp, hn⟩).1
  rw [← hk] at hq
  have : p ^ k * (p.maxPowDvdDiv n ⟨hp, hn⟩).2 = p ^ k * l := by rw [Nat.mul_comm, hq, h]
  exact Prod.ext hk.symm (Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (Nat.zero_lt_of_lt hp)) this)

@[simp]
theorem maxPowDvdDiv_base_pow_mul {p n : ℕ} (hp : 1 < p) (hn : n ≠ 0) (k : ℕ)
    {h : 1 < p ∧ p ^ k * n ≠ 0} :
    p.maxPowDvdDiv (p ^ k * n) h =
      (padicValNat p n (Nat.ne_of_gt hp) hn + k, divMaxPow n p) := by
  apply maxPowDvdDiv_of_pow_mul_eq
  · rw [Nat.pow_add, Nat.mul_assoc, Nat.mul_left_comm, pow_padicValNat_mul_divMaxPow]
  · exact not_dvd_divMaxPow hp hn

@[simp]
theorem _root_.padicValNat_base_pow_mul {p n : ℕ} (hp : 1 < p) (hn : n ≠ 0) (k : ℕ)
    {h : p ^ k * n ≠ 0} :
    padicValNat p (p ^ k * n) (Nat.ne_of_gt hp) h = padicValNat p n (Nat.ne_of_gt hp) hn + k := by
  rw [← fst_maxPowDvdDiv ⟨hp, h⟩, maxPowDvdDiv_base_pow_mul hp hn]

@[simp]
theorem divMaxPow_base_pow_mul {p : ℕ} (hp : p ≠ 0) (n k : ℕ) :
    (p ^ k * n).divMaxPow p = n.divMaxPow p := by
  obtain rfl | hp1 : p = 1 ∨ 1 < p := by grind
  · simp
  · rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have h : 1 < p ∧ p ^ k * n ≠ 0 :=
        ⟨hp1, Nat.mul_ne_zero (Nat.ne_of_gt (Nat.pow_pos (Nat.pos_of_ne_zero hp))) hn⟩
      rw [divMaxPow, dite_eq_left h, maxPowDvdDiv_base_pow_mul hp1 hn]

@[simp]
theorem maxPowDvdDiv_base_mul {p n : ℕ} (hp : 1 < p) (hn : n ≠ 0) {h : 1 < p ∧ p * n ≠ 0} :
    p.maxPowDvdDiv (p * n) h = (padicValNat p n (Nat.ne_of_gt hp) hn + 1, divMaxPow n p) := by
  simpa using maxPowDvdDiv_base_pow_mul hp hn 1 (h := ⟨hp, by simpa using h.2⟩)

@[simp]
theorem _root_.padicValNat_base_mul {p n : ℕ} (hp : 1 < p) (hn : n ≠ 0) {h : p * n ≠ 0} :
    padicValNat p (p * n) (Nat.ne_of_gt hp) h = padicValNat p n (Nat.ne_of_gt hp) hn + 1 := by
  rw [← fst_maxPowDvdDiv ⟨hp, h⟩, maxPowDvdDiv_base_mul hp hn]

@[simp]
theorem divMaxPow_base_mul {p : ℕ} (hp : p ≠ 0) (n : ℕ) :
    (p * n).divMaxPow p = n.divMaxPow p := by
  simpa using divMaxPow_base_pow_mul hp n 1

@[simp]
theorem maxPowDvdDiv_base_pow {p : ℕ} (hp : 1 < p) (k : ℕ) {h : 1 < p ∧ p ^ k ≠ 0} :
    p.maxPowDvdDiv (p ^ k) h = (k, 1) := by
  simpa using maxPowDvdDiv_base_pow_mul hp Nat.one_ne_zero k (h := ⟨hp, by simpa using h.2⟩)

@[simp]
theorem _root_.padicValNat_base_pow {p : ℕ} (hp : 1 < p) (k : ℕ) {h : p ^ k ≠ 0} :
    padicValNat p (p ^ k) (Nat.ne_of_gt hp) h = k := by
  rw [← fst_maxPowDvdDiv ⟨hp, h⟩, maxPowDvdDiv_base_pow hp k]

@[simp]
theorem divMaxPow_base_pow {p : ℕ} (hp : p ≠ 0) (k : ℕ) : (p ^ k).divMaxPow p = 1 := by
  simpa using divMaxPow_base_pow_mul hp 1 k

@[simp]
theorem maxPowDvdDiv_self {p : ℕ} (hp : 1 < p) {h : 1 < p ∧ p ≠ 0} :
    p.maxPowDvdDiv p h = (1, 1) := by
  simpa using maxPowDvdDiv_base_pow hp 1 (h := ⟨hp, by simpa using h.2⟩)

@[simp]
theorem _root_.padicValNat_base {p : ℕ} (hp : 1 < p) {h : p ≠ 0} :
    padicValNat p p (Nat.ne_of_gt hp) h = 1 := by
  rw [← fst_maxPowDvdDiv ⟨hp, h⟩, maxPowDvdDiv_self hp]

@[simp]
theorem divMaxPow_self {p : ℕ} (hp : p ≠ 0) : p.divMaxPow p = 1 := by
  simpa using divMaxPow_base_pow hp 1

@[deprecated (since := "2026-03-15")]
alias maxPowDiv := padicValNat

@[deprecated (since := "2026-03-15")]
alias maxPowDiv.base_mul_eq_succ := padicValNat_base_mul

@[deprecated (since := "2026-03-15")]
alias maxPowDiv.base_pow_mul := padicValNat_base_pow_mul

@[deprecated (since := "2026-03-15")]
alias ⟨_, maxPowDiv.le_of_dvd⟩ := pow_dvd_iff_le_padicValNat

@[deprecated (since := "2026-03-15")]
alias maxPowDiv.pow_dvd := pow_padicValNat_dvd

@[deprecated (since := "2026-03-15")]
alias maxPowDiv.zero_base := padicValNat_zero_left

end Nat
