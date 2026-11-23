/-
Copyright (c) 2023 Matthew Robert Ballard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Robert Ballard, Yury Kudryashov
-/
module

import Mathlib.Data.Nat.Notation

/-!
# The maximal power of one natural number dividing another

For `1 < p` and `n ≠ 0`, `p.maxPowDvdDiv n hpn` returns the largest `k : ℕ` such that `p ^ k ∣ n`,
together with the quotient `n / p ^ k`. The implementation recurses through `p, p ^ 2, p ^ 4, …`.
-/

@[expose] public section

namespace Nat

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
      if q % p = 0 then
        (2 * e + 1, Nat.euclideanDiv q p (Nat.ne_of_gt (Nat.lt_trans Nat.one_pos hp.1)))
      else (2 * e, q)
    else
      (0, n)
  termination_by Nat.euclideanDiv n p (Nat.ne_of_gt (Nat.lt_trans Nat.one_pos hp.1))
  decreasing_by
    rw [← Nat.dvd_iff_mod_eq_zero] at hmod
    rcases hmod with ⟨m, rfl⟩
    have hp₀ : 0 < p := Nat.lt_trans Nat.one_pos hp.1
    have hpne := Nat.ne_of_gt hp₀
    rw [Nat.euclideanDiv_mul_left_cancel]
    have hm : 0 < m := by grind
    apply Nat.lt_of_not_ge
    intro h
    have hmul : (p * p) * m ≤ p * m :=
      (Nat.le_euclideanDiv_iff_mul_le (Nat.mul_ne_zero hpne hpne)).mp h
    have hlt : m < p * m := by
      simpa only [Nat.one_mul] using Nat.mul_lt_mul_of_pos_right hp.1 hm
    rw [Nat.mul_assoc] at hmul
    exact Nat.not_le_of_lt (Nat.mul_lt_mul_of_pos_left hlt hp₀) hmul

/-- The quotient of `n` by the largest power of `p` that divides `n`. If `p ≤ 1` or `n = 0`, the quotient is `n`. -/
def divMaxPow (n p : ℕ) : ℕ :=
  if h : 1 < p ∧ n ≠ 0 then (maxPowDvdDiv p n h).2 else n

theorem maxPowDvdDiv.go_spec {n p : ℕ} (hnp) :
    (go n p hnp).2 * p ^ (go n p hnp).1 = n ∧ ¬p ∣ (go n p hnp).2 := by
  fun_induction go with
  | case1 p hp hmod e q heq hqp ih =>
    rw [heq] at ih
    rcases ih with ⟨rfl, hdvd⟩
    have hp₀ := Nat.ne_of_gt (Nat.lt_trans Nat.one_pos hp.1)
    have hq : p * Nat.euclideanDiv q p hp₀ = q := by
      simpa only [hqp, Nat.add_zero] using Nat.euclideanDiv_mul_add_mod q p hp₀
    have hqp' : ¬p ∣ Nat.euclideanDiv q p hp₀ := by
      intro h
      exact hdvd (hq ▸ Nat.mul_dvd_mul_left p h)
    have hq' : Nat.euclideanDiv q p hp₀ * p = q := (Nat.mul_comm _ _).trans hq
    simp_all [Nat.pow_add', ← Nat.mul_assoc, Nat.two_mul, Nat.mul_pow]
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
theorem snd_maxPowDvdDiv {p n : ℕ} (hpn : 1 < p ∧ n ≠ 0) :
    (p.maxPowDvdDiv n hpn).2 = n.divMaxPow p := by
  simp [divMaxPow, hpn]

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
theorem divMaxPow_one_left (p : ℕ) : divMaxPow 1 p = 1 := by
  simp [divMaxPow]

theorem not_dvd_divMaxPow {p n : ℕ} (hp : 1 < p) (hn : n ≠ 0) : ¬p ∣ divMaxPow n p := by
  rw [divMaxPow, dite_eq_left ⟨hp, hn⟩]
  exact (maxPowDvdDiv_spec ⟨hp, hn⟩).2

end Nat
