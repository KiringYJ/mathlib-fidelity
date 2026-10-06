/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Matthew Robert Ballard
-/
module

public import Mathlib.NumberTheory.Divisors
public import Mathlib.NumberTheory.Padics.PadicVal.Defs
public import Mathlib.Data.Nat.MaxPowDiv
public import Mathlib.Data.Nat.Multiplicity
public import Mathlib.Data.Nat.Prime.Int

/-!
# `p`-adic Valuation

This file defines the `p`-adic valuation on `ℕ`, `ℤ`, and `ℚ`.

The `p`-adic valuation on `ℚ` is the difference of the multiplicities of `p` in the numerator and
denominator of `q`. This function obeys the standard properties of a valuation, with the appropriate
assumptions on `p`. The `p`-adic valuations on `ℕ` and `ℤ` agree with that on `ℚ`.

The valuation induces a norm on `ℚ`. This norm is defined in
`Mathlib/NumberTheory/Padics/PadicNorm.lean`.

## Notation

This file uses the local notation `/.` for `Rat.mk`.

## Implementation notes

Much, but not all, of this file assumes that `p` is prime. This assumption is inferred automatically
by taking `[Fact p.Prime]` as a type class argument.

## Calculations with `p`-adic valuations

* `padicValNat_factorial`: Legendre's Theorem. The `p`-adic valuation of `n!` is the sum of the
  quotients `n / p ^ i`. This sum is expressed over the finset `Ico 1 b` where `b` is any bound
  greater than `log p n`. See `Nat.Prime.multiplicity_factorial` for the same result but stated in
  the language of prime multiplicity.

* `sub_one_mul_padicValNat_factorial`: Legendre's Theorem.  Taking (`p - 1`) times
  the `p`-adic valuation of `n!` equals `n` minus the sum of base `p` digits of `n`.

* `padicValNat_choose`: Kummer's Theorem. The `p`-adic valuation of `n.choose k` is the number
  of carries when `k` and `n - k` are added in base `p`. This sum is expressed over the finset
  `Ico 1 b` where `b` is any bound greater than `log p n`. See `Nat.Prime.multiplicity_choose` for
  the same result but stated in the language of prime multiplicity.

* `sub_one_mul_padicValNat_choose_eq_sub_sum_digits`: Kummer's Theorem. Taking (`p - 1`) times the
  `p`-adic valuation of the binomial `n` over `k` equals the sum of the digits of `k` plus the sum
  of the digits of `n - k` minus the sum of digits of `n`, all base `p`.

## References

* [F. Q. Gouvêa, *p-adic numbers*][gouvea1997]
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/P-adic_number>

## Tags

p-adic, p adic, padic, norm, valuation
-/

@[expose] public section

/-- `padic_val_tac` closes nonvanishing goals such as `a * b ≠ 0` or `n ! ≠ 0` with `positivity`. -/
macro_rules | `(tactic| padic_val_core) => `(tactic| positivity)

universe u

open Nat Rat
open scoped Finset

namespace padicValNat

variable {p : ℕ}

/-- If `1 < p`, then `padicValNat p p` is `1`. -/
alias self := padicValNat_base

theorem eq_zero_of_not_dvd {n : ℕ} (h : ¬p ∣ n) {hp : p ≠ 1} {hn : n ≠ 0} :
    padicValNat p n hp hn = 0 :=
  (eq_zero_iff hp hn).2 h

theorem dvd_of_ne_zero {n : ℕ} {hp : p ≠ 1} {hn : n ≠ 0} (h : padicValNat p n hp hn ≠ 0) :
    p ∣ n :=
  not_not.mp (mt (eq_zero_iff hp hn).2 h)

end padicValNat

/-- The `p`-adic valuation of an integer `z`: the largest natural number `k` such that `p ^ k`
divides `z`. It exists exactly when `p ≠ 1` and `z ≠ 0`; the proofs can usually be omitted, see
`padic_val_tac`. -/
def padicValInt (p : ℕ) (z : ℤ) (hp : p ≠ 1 := by padic_val_tac)
    (hz : z ≠ 0 := by padic_val_tac) : ℕ :=
  padicValNat p z.natAbs hp (Int.natAbs_ne_zero.2 hz)

namespace padicValInt

variable {p : ℕ}

theorem of_ne_one_ne_zero (hp : p ≠ 1) {z : ℤ} (hz : z ≠ 0) :
    padicValInt p z =
      multiplicity (p : ℤ) z (Int.finiteMultiplicity_iff.2 ⟨by simpa using hp, hz⟩) := by
  rw [padicValInt, padicValNat_def hp (Int.natAbs_ne_zero.2 hz)]
  exact Int.multiplicity_natAbs p z

/-- `padicValInt p 1` is `0`. -/
@[simp]
protected theorem one {hp : p ≠ 1} {h : (1 : ℤ) ≠ 0} : padicValInt p 1 hp h = 0 := by
  simp [padicValInt]

/-- The `p`-adic value of a natural is its `p`-adic value as an integer. -/
@[simp]
theorem of_nat {n : ℕ} {hp : p ≠ 1} {hn : (n : ℤ) ≠ 0} :
    padicValInt p n hp hn = padicValNat p n hp (Int.natCast_ne_zero.1 hn) := by
  simp [padicValInt]

/-- If `1 < p`, then `padicValInt p p` is `1`. -/
theorem self (hp : 1 < p) : padicValInt p p = 1 := by
  simp [padicValInt, hp]

theorem eq_zero_iff (hp : p ≠ 1) {z : ℤ} (hz : z ≠ 0) :
    padicValInt p z = 0 ↔ ¬(p : ℤ) ∣ z := by
  rw [padicValInt, padicValNat.eq_zero_iff, ← Int.ofNat_dvd_left]

theorem eq_zero_of_not_dvd {z : ℤ} (h : ¬(p : ℤ) ∣ z) {hp : p ≠ 1} {hz : z ≠ 0} :
    padicValInt p z hp hz = 0 :=
  (eq_zero_iff hp hz).2 h

end padicValInt

/-- The `p`-adic valuation of a rational number `q`: the valuation of its numerator minus the
valuation of its denominator. It exists exactly when `p ≠ 1` and `q ≠ 0`; the proofs can usually
be omitted, see `padic_val_tac`. -/
def padicValRat (p : ℕ) (q : ℚ) (hp : p ≠ 1 := by padic_val_tac)
    (hq : q ≠ 0 := by padic_val_tac) : ℤ :=
  padicValInt p q.num hp (Rat.num_ne_zero.2 hq) - padicValNat p q.den hp q.den_nz

lemma padicValRat_def (p : ℕ) (q : ℚ) (hp : p ≠ 1) (hq : q ≠ 0) :
    padicValRat p q =
      padicValInt p q.num hp (Rat.num_ne_zero.2 hq) - padicValNat p q.den hp q.den_nz :=
  rfl

namespace padicValRat

variable {p : ℕ}

/-- `padicValRat p q` is symmetric in `q`. -/
@[simp]
protected theorem neg {q : ℚ} {hp : p ≠ 1} {hq : -q ≠ 0} :
    padicValRat p (-q) hp hq = padicValRat p q hp (neg_ne_zero.1 hq) := by
  simp [padicValRat, padicValInt]

/-- `padicValRat p 1` is `0`. -/
@[simp]
protected theorem one {hp : p ≠ 1} {h : (1 : ℚ) ≠ 0} : padicValRat p 1 hp h = 0 := by
  simp [padicValRat]

/-- The `p`-adic value of an integer is its `p`-adic value as a rational. -/
@[simp]
theorem of_int {z : ℤ} {hp : p ≠ 1} {hz : (z : ℚ) ≠ 0} :
    padicValRat p z hp hz = padicValInt p z hp (Int.cast_ne_zero.1 hz) := by
  simp [padicValRat]

/-- The `p`-adic value of a nonzero integer is the multiplicity of `p` in it. -/
theorem of_int_multiplicity (hp : p ≠ 1) {z : ℤ} (hz : z ≠ 0) :
    padicValRat p (z : ℚ) hp (Int.cast_ne_zero.2 hz) =
      multiplicity (p : ℤ) z (Int.finiteMultiplicity_iff.2 ⟨by simpa using hp, hz⟩) := by
  rw [of_int, padicValInt.of_ne_one_ne_zero hp hz]

theorem multiplicity_sub_multiplicity (hp : p ≠ 1) {q : ℚ} (hq : q ≠ 0) :
    padicValRat p q =
      multiplicity (p : ℤ) q.num
          (Int.finiteMultiplicity_iff.2 ⟨by simpa using hp, Rat.num_ne_zero.2 hq⟩) -
        multiplicity p q.den (Nat.finiteMultiplicity_iff.2 ⟨hp, q.den_pos⟩) := by
  rw [padicValRat, padicValInt.of_ne_one_ne_zero hp (Rat.num_ne_zero.2 hq),
    padicValNat_def hp q.den_nz]

/-- The `p`-adic value of a natural number is its `p`-adic value as a rational. -/
@[simp]
theorem of_nat {n : ℕ} {hp : p ≠ 1} {hn : (n : ℚ) ≠ 0} :
    padicValRat p n hp hn = padicValNat p n hp (Nat.cast_ne_zero.1 hn) := by
  simp [padicValRat]

/-- If `1 < p`, then `padicValRat p p` is `1`. -/
theorem self (hp : 1 < p) : padicValRat p p (Nat.ne_of_gt hp) (by norm_cast; omega) = 1 := by
  simp [hp]

end padicValRat

section padicValNat

variable {p : ℕ}

theorem zero_le_padicValRat_of_nat {n : ℕ} {hp : p ≠ 1} {hn : (n : ℚ) ≠ 0} :
    0 ≤ padicValRat p n hp hn := by
  simp

/-- `padicValRat` coincides with `padicValNat`. -/
@[norm_cast]
theorem padicValRat_of_nat {n : ℕ} {hp : p ≠ 1} {hn : n ≠ 0} :
    ↑(padicValNat p n hp hn) = padicValRat p n hp (Nat.cast_ne_zero.2 hn) := by
  simp

@[simp]
theorem padicValNat_self [Fact p.Prime] {hp : p ≠ 1} {h : p ≠ 0} : padicValNat p p hp h = 1 :=
  padicValNat.self (Fact.out : p.Prime).one_lt

theorem one_le_padicValNat_of_dvd {n : ℕ} [hp : Fact p.Prime] (hn : n ≠ 0) (div : p ∣ n) :
    1 ≤ padicValNat p n := by
  rwa [← ENat.natCast_le_natCast, padicValNat_eq_emultiplicity hn,
    ← pow_dvd_iff_le_emultiplicity, pow_one]

theorem dvd_iff_padicValNat_ne_zero {p n : ℕ} [Fact p.Prime] (hn0 : n ≠ 0) :
    p ∣ n ↔ padicValNat p n ≠ 0 :=
  ⟨fun h => one_le_iff_ne_zero.mp (one_le_padicValNat_of_dvd hn0 h), fun h =>
    Classical.not_not.1 fun hnd ↦ h (padicValNat.eq_zero_of_not_dvd hnd)⟩

end padicValNat

namespace padicValRat

variable {p : ℕ} [hp : Fact p.Prime]

/-- The multiplicity of `p : ℕ` in `a : ℤ` is finite exactly when `a ≠ 0`. -/
theorem finite_int_prime_iff {a : ℤ} : FiniteMultiplicity (p : ℤ) a ↔ a ≠ 0 := by
  simp [Int.finiteMultiplicity_iff, hp.1.ne_one]

/-- A rewrite lemma for `padicValRat p q` when `q` is expressed in terms of `Rat.mk`. -/
protected theorem defn (p : ℕ) [hp : Fact p.Prime] {q : ℚ} {n d : ℤ} (hqz : q ≠ 0)
    (qdf : q = n /. d) :
    padicValRat p q =
      multiplicity (p : ℤ) n (finite_int_prime_iff.2 (Rat.mk_num_ne_zero_of_ne_zero hqz qdf)) -
        multiplicity (p : ℤ) d
          (finite_int_prime_iff.2 (Rat.mk_denom_ne_zero_of_ne_zero hqz qdf)) := by
  have hn : n ≠ 0 := Rat.mk_num_ne_zero_of_ne_zero hqz qdf
  have hd : d ≠ 0 := Rat.mk_denom_ne_zero_of_ne_zero hqz qdf
  obtain ⟨c, hc1, hc2⟩ := Rat.num_den_mk hd qdf
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp.1
  rw [padicValRat.multiplicity_sub_multiplicity hp.out.ne_one hqz]
  subst hc1 hc2
  rw [multiplicity_mul hp', multiplicity_mul hp', Nat.cast_add, Nat.cast_add,
    Int.natCast_multiplicity p q.den]
  ring

/-- A rewrite lemma for `padicValRat p (q * r)` with conditions `q ≠ 0`, `r ≠ 0`. -/
protected theorem mul {q r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) :
    padicValRat p (q * r) = padicValRat p q + padicValRat p r := by
  have : q * r = (q.num * r.num) /. (q.den * r.den) := by
    rw [Rat.mul_eq_mkRat, Rat.mkRat_eq_divInt, Nat.cast_mul]
  have hq' : q.num /. q.den ≠ 0 := by rwa [Rat.num_divInt_den]
  have hr' : r.num /. r.den ≠ 0 := by rwa [Rat.num_divInt_den]
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp.1
  rw [padicValRat.defn p (mul_ne_zero hq hr) this,
    padicValRat.defn p hq (q.num_divInt_den).symm, padicValRat.defn p hr (r.num_divInt_den).symm,
    multiplicity_mul hp', multiplicity_mul hp', Nat.cast_add, Nat.cast_add]
  ring

/-- A rewrite lemma for `padicValRat p (q^k)`. -/
@[simp]
protected theorem pow {q : ℚ} (hq : q ≠ 0) {k : ℕ} :
    padicValRat p (q ^ k) (hq := pow_ne_zero k hq) = k * padicValRat p q := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : padicValRat p (q ^ (k + 1)) (hq := pow_ne_zero (k + 1) hq) =
        padicValRat p (q ^ k * q) (hq := mul_ne_zero (pow_ne_zero k hq) hq) := by
      simp only [_root_.pow_succ]
    rw [e, padicValRat.mul (pow_ne_zero _ hq) hq, ih]
    push_cast
    ring

/-- A rewrite lemma for `padicValRat p (q⁻¹)`. -/
@[simp]
protected theorem inv {q : ℚ} (hq : q ≠ 0) :
    padicValRat p q⁻¹ (hq := inv_ne_zero hq) = -padicValRat p q := by
  rw [eq_neg_iff_add_eq_zero, ← padicValRat.mul (inv_ne_zero hq) hq]
  have e : padicValRat p (q⁻¹ * q) (hq := mul_ne_zero (inv_ne_zero hq) hq) =
      padicValRat p 1 := by
    simp only [inv_mul_cancel₀ hq]
  rw [e, padicValRat.one]

@[simp]
protected theorem zpow {q : ℚ} (hq : q ≠ 0) {k : ℤ} :
    padicValRat p (q ^ k) (hq := zpow_ne_zero k hq) = k * padicValRat p q := by
  induction k using Int.negInduction with
  | nat k =>
    have e : padicValRat p (q ^ (k : ℤ)) (hq := zpow_ne_zero (k : ℤ) hq) =
        padicValRat p (q ^ k) (hq := pow_ne_zero k hq) := by
      simp only [zpow_natCast]
    rw [e, padicValRat.pow hq]
  | neg _ k =>
    have e : padicValRat p (q ^ (-(k : ℤ))) (hq := zpow_ne_zero (-(k : ℤ)) hq) =
        padicValRat p (q ^ k)⁻¹ (hq := inv_ne_zero (pow_ne_zero k hq)) := by
      simp only [zpow_neg, zpow_natCast]
    rw [e, padicValRat.inv (pow_ne_zero k hq), padicValRat.pow hq]
    ring

/-- A rewrite lemma for `padicValRat p (q / r)` with conditions `q ≠ 0`, `r ≠ 0`. -/
protected theorem div {q r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) :
    padicValRat p (q / r) (hq := div_ne_zero hq hr) = padicValRat p q - padicValRat p r := by
  have e : padicValRat p (q / r) (hq := div_ne_zero hq hr) =
      padicValRat p (q * r⁻¹) (hq := mul_ne_zero hq (inv_ne_zero hr)) := by
    simp only [div_eq_mul_inv]
  rw [e, padicValRat.mul hq (inv_ne_zero hr), padicValRat.inv hr, sub_eq_add_neg]

/-- A condition for `padicValRat p (n₁ / d₁) ≤ padicValRat p (n₂ / d₂)`, in terms of
divisibility by `p^n`. -/
theorem padicValRat_le_padicValRat_iff {n₁ n₂ d₁ d₂ : ℤ} (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0)
    (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) :
    padicValRat p (n₁ /. d₁) (hq := Rat.divInt_ne_zero_of_ne_zero hn₁ hd₁) ≤
        padicValRat p (n₂ /. d₂) (hq := Rat.divInt_ne_zero_of_ne_zero hn₂ hd₂) ↔
      ∀ n : ℕ, (p : ℤ) ^ n ∣ n₁ * d₂ → (p : ℤ) ^ n ∣ n₂ * d₁ := by
  have hf1 : FiniteMultiplicity (p : ℤ) (n₁ * d₂) := finite_int_prime_iff.2 (mul_ne_zero hn₁ hd₂)
  have hf2 : FiniteMultiplicity (p : ℤ) (n₂ * d₁) := finite_int_prime_iff.2 (mul_ne_zero hn₂ hd₁)
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp.1
  rw [padicValRat.defn p (Rat.divInt_ne_zero_of_ne_zero hn₁ hd₁) rfl,
    padicValRat.defn p (Rat.divInt_ne_zero_of_ne_zero hn₂ hd₂) rfl, sub_le_iff_le_add',
    ← add_sub_assoc, le_sub_iff_add_le]
  norm_cast
  rw [← multiplicity_mul hp' hf1, add_comm, ← multiplicity_mul hp' hf2,
    hf1.multiplicity_le_multiplicity_iff hf2]
  simp only [Nat.cast_pow]

/-- Sufficient conditions to show that the `p`-adic valuation of `q` is less than or equal to the
`p`-adic valuation of `q + r`. -/
theorem le_padicValRat_add_of_le {q r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) (hqr : q + r ≠ 0)
    (h : padicValRat p q ≤ padicValRat p r) : padicValRat p q ≤ padicValRat p (q + r) := by
  have hqn : q.num ≠ 0 := Rat.num_ne_zero.2 hq
  have hqd : (q.den : ℤ) ≠ 0 := mod_cast Rat.den_nz _
  have hrn : r.num ≠ 0 := Rat.num_ne_zero.2 hr
  have hrd : (r.den : ℤ) ≠ 0 := mod_cast Rat.den_nz _
  have hqreq : q + r = (q.num * r.den + q.den * r.num) /. (q.den * r.den) := Rat.add_num_den _ _
  have hqrd : q.num * r.den + q.den * r.num ≠ 0 := Rat.mk_num_ne_zero_of_ne_zero hqr hqreq
  have hq' : q = q.num /. q.den := q.num_divInt_den.symm
  have hr' : r = r.num /. r.den := r.num_divInt_den.symm
  have key : padicValRat p (q.num /. q.den) (hq := hq' ▸ hq) ≤
      padicValRat p ((q.num * r.den + q.den * r.num) /. (q.den * r.den)) (hq := hqreq ▸ hqr) := by
    rw [padicValRat_le_padicValRat_iff hqn hqrd hqd (mul_ne_zero hqd hrd), ←
      emultiplicity_le_emultiplicity_iff, mul_left_comm,
      emultiplicity_mul (Nat.prime_iff_prime_int.1 hp.1), add_mul]
    have h' : padicValRat p (q.num /. q.den) (hq := hq' ▸ hq) ≤
        padicValRat p (r.num /. r.den) (hq := hr' ▸ hr) := by
      convert h using 2 <;> simp
    rw [padicValRat_le_padicValRat_iff hqn hrn hqd hrd, ←
      emultiplicity_le_emultiplicity_iff] at h'
    calc
      _ ≤ min (emultiplicity ↑p (q.num * r.den * q.den))
              (emultiplicity ↑p (q.den * r.num * q.den)) :=
        le_min
          (by rw [emultiplicity_mul (a := _ * _) (Nat.prime_iff_prime_int.1 hp.1), add_comm])
          (by grw [mul_assoc, emultiplicity_mul (b := _ * _) (Nat.prime_iff_prime_int.1 hp.1), h'])
      _ ≤ _ := min_le_emultiplicity_add
  convert key using 2

/-- The minimum of the valuations of `q` and `r` is at most the valuation of `q + r`. -/
theorem min_le_padicValRat_add {q r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) (hqr : q + r ≠ 0) :
    min (padicValRat p q) (padicValRat p r) ≤ padicValRat p (q + r) :=
  (le_total (padicValRat p q) (padicValRat p r)).elim
  (fun h => by rw [min_eq_left h]; exact le_padicValRat_add_of_le hq hr hqr h)
  (fun h => by
    rw [min_eq_right h]
    have := le_padicValRat_add_of_le (p := p) hr hq (by rwa [add_comm]) h
    convert this using 2
    · exact add_comm q r)

/-- Ultrametric property of a p-adic valuation. -/
lemma add_eq_min {q r : ℚ} (hqr : q + r ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (hval : padicValRat p q ≠ padicValRat p r) :
    padicValRat p (q + r) = min (padicValRat p q) (padicValRat p r) := by
  have h1 := min_le_padicValRat_add (p := p) hq hr hqr
  have h2 := min_le_padicValRat_add (p := p) hqr (neg_ne_zero.2 hr)
    (ne_of_eq_of_ne (add_neg_cancel_right q r) hq)
  have h3 := min_le_padicValRat_add (p := p) hqr (neg_ne_zero.2 hq)
    (ne_of_eq_of_ne (by rw [add_comm q r, add_neg_cancel_right]) hr)
  have e2 : padicValRat p (q + r + -r) (hq := ne_of_eq_of_ne (add_neg_cancel_right q r) hq) =
      padicValRat p q := by congr 1; exact add_neg_cancel_right q r
  have e3 : padicValRat p (q + r + -q)
      (hq := ne_of_eq_of_ne (by rw [add_comm q r, add_neg_cancel_right]) hr) =
      padicValRat p r := by congr 1; rw [add_comm q r, add_neg_cancel_right]
  rw [e2, padicValRat.neg] at h2
  rw [e3, padicValRat.neg] at h3
  omega

lemma add_eq_of_lt {q r : ℚ} (hqr : q + r ≠ 0)
    (hq : q ≠ 0) (hr : r ≠ 0) (hval : padicValRat p q < padicValRat p r) :
    padicValRat p (q + r) = padicValRat p q := by
  rw [add_eq_min hqr hq hr (ne_of_lt hval), min_eq_left (le_of_lt hval)]

lemma lt_add_of_lt {q r₁ r₂ : ℚ} (hq : q ≠ 0) (hr₁ : r₁ ≠ 0) (hr₂ : r₂ ≠ 0) (hqr : r₁ + r₂ ≠ 0)
    (hval₁ : padicValRat p q < padicValRat p r₁) (hval₂ : padicValRat p q < padicValRat p r₂) :
    padicValRat p q < padicValRat p (r₁ + r₂) :=
  lt_of_lt_of_le (lt_min hval₁ hval₂) (padicValRat.min_le_padicValRat_add hr₁ hr₂ hqr)

lemma self_pow_inv (r : ℕ) :
    padicValRat p ((p : ℚ) ^ r)⁻¹ (hq := inv_ne_zero (pow_ne_zero r (mod_cast hp.out.ne_zero))) =
      -r := by
  have hp0 : (p : ℚ) ≠ 0 := mod_cast hp.out.ne_zero
  rw [padicValRat.inv (pow_ne_zero r hp0), neg_inj, padicValRat.pow hp0]
  simp [padicValRat.self hp.out.one_lt]

/-- A finite sum of rationals with positive `p`-adic valuation has positive `p`-adic valuation
(if the sum is non-zero). -/
theorem sum_pos_of_pos {n : ℕ} {F : ℕ → ℚ} (hF0 : ∀ i, i < n → F i ≠ 0)
    (hF : ∀ i (hi : i < n), 0 < padicValRat p (F i) (hq := hF0 i hi))
    (hn0 : ∑ i ∈ Finset.range n, F i ≠ 0) : 0 < padicValRat p (∑ i ∈ Finset.range n, F i) := by
  induction n with
  | zero => exact False.elim (hn0 rfl)
  | succ d hd =>
    have hsum : ∑ x ∈ Finset.range (d + 1), F x = ∑ x ∈ Finset.range d, F x + F d :=
      Finset.sum_range_succ F d
    by_cases h : ∑ x ∈ Finset.range d, F x = 0
    · have : ∑ x ∈ Finset.range (d + 1), F x = F d := by rw [hsum, h, zero_add]
      convert hF d (lt_add_one _) using 2
    · have hlt := lt_of_lt_of_le
        (lt_min (hd (fun i hi => hF0 i (lt_trans hi (lt_add_one _)))
          (fun i hi => hF i (lt_trans hi (lt_add_one _))) h) (hF d (lt_add_one _)))
        (min_le_padicValRat_add (p := p) h (hF0 d (lt_add_one _)) (hsum ▸ hn0))
      convert hlt using 2

/-- If the p-adic valuation of a finite set of positive rationals is greater than a given rational
number, then the p-adic valuation of their sum is also greater than the same rational number. -/
theorem lt_sum_of_lt {p j : ℕ} [hp : Fact (Nat.Prime p)] {F : ℕ → ℚ} {S : Finset ℕ}
    (hS : S.Nonempty) (hn1 : ∀ i : ℕ, 0 < F i)
    (hF : ∀ i, i ∈ S → padicValRat p (F j) (hq := (hn1 j).ne') <
      padicValRat p (F i) (hq := (hn1 i).ne')) :
    padicValRat p (F j) (hq := (hn1 j).ne') <
      padicValRat p (∑ i ∈ S, F i) (hq := (Finset.sum_pos (fun i _ => hn1 i) hS).ne') := by
  induction hS using Finset.Nonempty.cons_induction with
  | singleton k =>
    simp only [Finset.sum_singleton]
    exact hF k (by simp)
  | cons s S' Hnot Hne Hind =>
    simp only [Finset.cons_eq_insert, Finset.sum_insert Hnot]
    exact padicValRat.lt_add_of_lt (hn1 j).ne' (hn1 s).ne'
      (Finset.sum_pos (fun i _ => hn1 i) Hne).ne'
      (ne_of_gt (add_pos (hn1 s) (Finset.sum_pos (fun i _ => hn1 i) Hne)))
      (hF _ (by simp [Finset.mem_insert, true_or]))
      (Hind (fun i hi => hF _ (by rw [Finset.cons_eq_insert, Finset.mem_insert]; exact Or.inr hi)))

end padicValRat

namespace Rat

/-- The numerator or denominator of a nonzero rational number has zero `p`-adic valuation. -/
theorem num_or_den_zero_padicVal {a : ℚ} (ha : a ≠ 0) {p : ℕ} (hp : p.Prime) :
    padicValInt p a.num (hz := Rat.num_ne_zero.2 ha) = 0 ∨
      padicValNat p a.den (hn := a.den_nz) = 0 := by
  have h := a.reduced
  contrapose! h
  apply not_coprime_of_dvd_of_dvd hp.one_lt <;>
    grind [padicValNat.dvd_of_ne_zero h.1, padicValNat.dvd_of_ne_zero h.2]

/-- The numerator and denominator of a nonzero rational number with even `p`-adic valuation
also have even `p`-adic valuation. -/
theorem num_den_even_padicVal_of_even_padicVal {a : ℚ} (ha : a ≠ 0) {p : ℕ} (hp : p.Prime)
    (h : Even (padicValRat p a)) :
    Even (padicValInt p a.num (hz := Rat.num_ne_zero.2 ha)) ∧
      Even (padicValNat p a.den (hn := a.den_nz)) := by
  rcases num_or_den_zero_padicVal ha hp with (h0 | h0) <;>
    simpa [h0, padicValRat_def] using h

/-- A rational number is a square if and only if it is nonnegative,
and, if it is nonzero, has even `p`-adic valuation for all primes `p`. -/
theorem isSquare_iff_even_factorization {a : ℚ} :
    IsSquare a ↔ 0 ≤ a ∧ ∀ (ha : a ≠ 0) (p : ℕ) (hp : p.Prime), Even (padicValRat p a) := by
  constructor
  · refine fun ⟨r, hr⟩ ↦ ⟨by simpa [hr] using mul_self_nonneg r, fun ha p hp ↦ ?_⟩
    have : Fact (p.Prime) := ⟨hp⟩
    have hr0 : r ≠ 0 := by rintro rfl; simp [hr] at ha
    have e : padicValRat p a = padicValRat p (r * r) := by congr 1
    rw [e, padicValRat.mul hr0 hr0]
    exact ⟨_, rfl⟩
  · intro ⟨hR, hf⟩
    rcases eq_or_ne a 0 with rfl | ha
    · exact ⟨0, by simp⟩
    rw [isSquare_iff]
    constructor
    · refine Int.isSquare_iff_nonneg_even_factorization.mpr ⟨num_nonneg.mpr hR, fun p hp ↦ ?_⟩
      have num_even := (num_den_even_padicVal_of_even_padicVal ha hp (hf ha p hp)).1
      rwa [Nat.factorization_def _ hp (Int.natAbs_ne_zero.2 (Rat.num_ne_zero.2 ha))]
    · refine Nat.isSquare_iff_even_factorization.mpr (fun p hp ↦ ?_)
      have den_even := (num_den_even_padicVal_of_even_padicVal ha hp (hf ha p hp)).2
      rwa [Nat.factorization_def _ hp a.den_nz]

end Rat

namespace padicValNat

variable {p a b : ℕ} [hp : Fact p.Prime]

/-- A rewrite lemma for `padicValNat p (a * b)` with conditions `a ≠ 0`, `b ≠ 0`. -/
protected theorem mul (ha : a ≠ 0) (hb : b ≠ 0) :
    padicValNat p (a * b) = padicValNat p a + padicValNat p b := by
  apply Nat.cast_injective (R := ℕ∞)
  rw [Nat.cast_add, padicValNat_eq_emultiplicity (mul_ne_zero ha hb),
    padicValNat_eq_emultiplicity ha, padicValNat_eq_emultiplicity hb,
    emultiplicity_mul (Nat.prime_iff.1 hp.out)]

protected theorem div_of_dvd (ha : a ≠ 0) (h : b ∣ a) {hab : a / b ≠ 0} :
    padicValNat p (a / b) hp.out.ne_one hab =
      padicValNat p a - padicValNat p b (hn := ne_zero_of_dvd_ne_zero ha h) := by
  obtain ⟨k, rfl⟩ := h
  obtain ⟨hb, hk⟩ := mul_ne_zero_iff.mp ha
  have e : b * k / b = k := k.mul_div_cancel_left (Nat.pos_of_ne_zero hb)
  have : padicValNat p (b * k / b) hp.out.ne_one hab = padicValNat p k := by simp only [e]
  rw [this, padicValNat.mul hb hk, Nat.add_sub_cancel_left]

/-- Dividing out by a prime factor reduces the `padicValNat` by `1`. -/
protected theorem div (hb : b ≠ 0) (dvd : p ∣ b) {h : b / p ≠ 0} :
    padicValNat p (b / p) hp.out.ne_one h = padicValNat p b - 1 := by
  rw [padicValNat.div_of_dvd hb dvd, padicValNat_self]

/-- A version of `padicValRat.pow` for `padicValNat`. -/
@[simp]
protected theorem pow (a n : ℕ) (ha : a ≠ 0) : padicValNat p (a ^ n) = n * padicValNat p a := by
  apply Nat.cast_injective (R := ℕ∞)
  rw [Nat.cast_mul, padicValNat_eq_emultiplicity (pow_ne_zero n ha),
    padicValNat_eq_emultiplicity ha, emultiplicity_pow (Nat.prime_iff.1 hp.out)]

protected theorem prime_pow (n : ℕ) : padicValNat p (p ^ n) = n := by
  rw [padicValNat.pow p n hp.out.ne_zero, padicValNat_self, mul_one]

protected theorem div_pow (hb : b ≠ 0) (dvd : p ^ a ∣ b) {h : b / p ^ a ≠ 0} :
    padicValNat p (b / p ^ a) hp.out.ne_one h = padicValNat p b - a := by
  rw [padicValNat.div_of_dvd hb dvd, padicValNat.prime_pow]

protected theorem div' {m : ℕ} (cpm : Coprime p m) {b : ℕ} (hb : b ≠ 0) (dvd : m ∣ b)
    {h : b / m ≠ 0} : padicValNat p (b / m) hp.out.ne_one h = padicValNat p b := by
  rw [padicValNat.div_of_dvd hb dvd, eq_zero_of_not_dvd (hp.out.coprime_iff_not_dvd.mp cpm),
    Nat.sub_zero]

end padicValNat

section padicValNat

variable {p : ℕ}

theorem dvd_of_one_le_padicValNat {n : ℕ} {hp' : p ≠ 1} {hn : n ≠ 0}
    (hp : 1 ≤ padicValNat p n hp' hn) : p ∣ n := by
  by_contra h
  rw [padicValNat.eq_zero_of_not_dvd h] at hp
  exact lt_irrefl 0 (lt_of_lt_of_le zero_lt_one hp)

theorem padicValNat_dvd_iff_le_of_ne_one {p : ℕ} (hp : p ≠ 1) {a n : ℕ} (ha : a ≠ 0) :
    p ^ n ∣ a ↔ n ≤ padicValNat p a := by
  rw [pow_dvd_iff_le_emultiplicity, ← padicValNat_eq_emultiplicity_of_ne_one hp ha, Nat.cast_le]

theorem padicValNat_dvd_iff_le [hp : Fact p.Prime] {a n : ℕ} (ha : a ≠ 0) :
    p ^ n ∣ a ↔ n ≤ padicValNat p a :=
  padicValNat_dvd_iff_le_of_ne_one hp.out.ne_one ha

theorem padicValNat_dvd_iff_of_ne_one {p : ℕ} (hp : p ≠ 1) (n a : ℕ) :
    p ^ n ∣ a ↔ ∀ ha : a ≠ 0, n ≤ padicValNat p a := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · exact iff_of_true (dvd_zero _) (fun ha ↦ absurd rfl ha)
  · rw [padicValNat_dvd_iff_le_of_ne_one hp ha]
    exact ⟨fun h _ ↦ h, fun h ↦ h ha⟩

theorem padicValNat_dvd_iff (n : ℕ) [hp : Fact p.Prime] (a : ℕ) :
    p ^ n ∣ a ↔ ∀ ha : a ≠ 0, n ≤ padicValNat p a :=
  padicValNat_dvd_iff_of_ne_one hp.out.ne_one n a

theorem pow_succ_padicValNat_not_dvd {n : ℕ} [hp : Fact p.Prime] (hn : n ≠ 0) :
    ¬p ^ (padicValNat p n + 1) ∣ n := by
  rw [padicValNat_dvd_iff_le hn, not_le]
  exact Nat.lt_succ_self _

theorem padicValNat_primes {q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (ne : p ≠ q) :
    padicValNat p q = 0 :=
  padicValNat.eq_zero_of_not_dvd <|
    (not_congr (Iff.symm (prime_dvd_prime_iff_eq hp.1 hq.1))).mp ne

theorem padicValNat_prime_prime_pow {q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (n : ℕ) (ne : p ≠ q) : padicValNat p (q ^ n) = 0 := by
  rw [padicValNat.pow _ _ hq.out.ne_zero, padicValNat_primes ne, mul_zero]

theorem padicValNat_mul_pow_left {q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (n m : ℕ) (ne : p ≠ q) {h : p ^ n * q ^ m ≠ 0} :
    padicValNat p (p ^ n * q ^ m) hp.out.ne_one h = n := by
  rw [padicValNat.mul (pow_ne_zero n hp.out.ne_zero) (pow_ne_zero m hq.out.ne_zero),
    padicValNat.prime_pow, padicValNat_prime_prime_pow m ne, add_zero]

theorem padicValNat_mul_pow_right {q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (n m : ℕ) (ne : q ≠ p) {h : p ^ n * q ^ m ≠ 0} :
    padicValNat q (p ^ n * q ^ m) hq.out.ne_one h = m := by
  have : padicValNat q (p ^ n * q ^ m) hq.out.ne_one h =
      padicValNat q (q ^ m * p ^ n) hq.out.ne_one (by rwa [mul_comm]) := by
    simp only [mul_comm (p ^ n) (q ^ m)]
  rw [this]
  exact padicValNat_mul_pow_left m n ne

/-- The p-adic valuation of `n` is less than or equal to its logarithm w.r.t. `p`. -/
lemma padicValNat_le_nat_log (hp : 1 < p) {n : ℕ} (hn : n ≠ 0) :
    padicValNat p n (Nat.ne_of_gt hp) hn ≤ Nat.log p n hp hn :=
  Nat.le_log_of_pow_le hp (le_of_dvd (Nat.pos_of_ne_zero hn) pow_padicValNat_dvd)

lemma padicValNat_add_le_self {a : ℕ} [hp : Fact p.Prime] (ha : p < a) :
    padicValNat p a + p ≤ a := by
  by_cases dvd : p ∣ a
  · rcases dvd with ⟨k, hk⟩
    have hk0 : k ≠ 0 := by rintro rfl; simp at hk; omega
    have : padicValNat p k < k := by calc
      _ ≤ log p k hp.out.one_lt hk0 := padicValNat_le_nat_log hp.out.one_lt hk0
      _ < _ := log_lt_self hp.out.one_lt hk0
    subst hk
    rw [padicValNat.mul hp.out.ne_zero hk0, padicValNat_self]
    calc
      _ ≤ p + k := by lia
      _ ≤ _ := Nat.add_le_mul hp.out.two_le (by lia)
  · rw [padicValNat.eq_zero_of_not_dvd dvd]
    lia

/-- The p-adic valuation of `n` is equal to the logarithm w.r.t. `p` iff
`n` is less than `p` raised to one plus the p-adic valuation of `n`. -/
lemma nat_log_eq_padicValNat_iff {n : ℕ} [hp : Fact (Nat.Prime p)] (hn : n ≠ 0) :
    Nat.log p n hp.out.one_lt hn = padicValNat p n ↔ n < p ^ (padicValNat p n + 1) := by
  rw [Nat.log_eq_iff hp.out.one_lt hn, and_iff_right_iff_imp]
  exact fun _ => Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr hn) pow_padicValNat_dvd

/-- This is false for prime numbers other than 2:
for `p = 3`, `n = 1`, one has `log 3 1 = padicValNat 3 2 = 0`. -/
lemma Nat.log_ne_padicValNat_succ {n : ℕ} (hn : n ≠ 0) : log 2 n ≠ padicValNat 2 (n + 1) := by
  rw [Ne, log_eq_iff (by decide) hn]
  rintro ⟨h1, h2⟩
  rw [← Nat.lt_add_one_iff, ← mul_one (2 ^ _)] at h1
  rw [← add_one_le_iff, Nat.pow_succ] at h2
  refine not_dvd_of_lt_of_lt_mul_succ h1 (lt_of_le_of_ne' h2 ?_) pow_padicValNat_dvd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact pow_succ_padicValNat_not_dvd (p := 2) n.succ_ne_zero ∘ dvd_of_eq

lemma Nat.max_log_padicValNat_succ_eq_log_succ {n : ℕ} (hn : n ≠ 0) [hp : Fact p.Prime] :
    max (log p n hp.out.one_lt hn) (padicValNat p (n + 1)) =
      log p (n + 1) hp.out.one_lt n.succ_ne_zero := by
  apply le_antisymm (max_le (log_mono_right (le_succ n))
    (padicValNat_le_nat_log hp.out.one_lt n.succ_ne_zero))
  rw [le_max_iff, or_iff_not_imp_left, not_le]
  intro h
  have h' := le_antisymm (add_one_le_iff.mpr (lt_pow_of_log_lt hp.out.one_lt hn h))
    (pow_log_le_self hp.out.one_lt n.succ_ne_zero)
  have := padicValNat.prime_pow (p := p) (log p (n + 1) hp.out.one_lt n.succ_ne_zero)
  have e : padicValNat p (p ^ log p (n + 1) hp.out.one_lt n.succ_ne_zero) =
      padicValNat p (n + 1) := by
    simp only [← h']
  rw [e] at this
  exact this.ge

theorem range_pow_padicValNat_subset_divisors {n : ℕ} (hp : p ≠ 1) (hn : n ≠ 0) :
    (Finset.range (padicValNat p n + 1)).image (p ^ ·) ⊆ n.divisors := by
  intro t ht
  simp only [Finset.mem_image, Finset.mem_range] at ht
  obtain ⟨k, hk, rfl⟩ := ht
  rw [Nat.mem_divisors]
  exact ⟨(pow_dvd_pow p (by lia : k ≤ padicValNat p n hp hn)).trans pow_padicValNat_dvd, hn⟩

theorem range_pow_padicValNat_subset_divisors' {n : ℕ} [hp : Fact p.Prime] (hn : n ≠ 0) :
    ((Finset.range (padicValNat p n)).image fun t => p ^ (t + 1)) ⊆ n.divisors.erase 1 := by
  intro t ht
  simp only [Finset.mem_image, Finset.mem_range] at ht
  obtain ⟨k, hk, rfl⟩ := ht
  rw [Finset.mem_erase, Nat.mem_divisors]
  refine ⟨?_, (pow_dvd_pow p <| succ_le_iff.2 hk).trans pow_padicValNat_dvd, hn⟩
  exact (Nat.one_lt_pow k.succ_ne_zero hp.out.one_lt).ne'

/-- The `p`-adic valuation of `(p * n)!` is `n` more than that of `n!`. -/
theorem padicValNat_factorial_mul (n : ℕ) [hp : Fact p.Prime] :
    padicValNat p (p * n)! = padicValNat p n ! + n := by
  apply Nat.cast_injective (R := ℕ∞)
  rw [padicValNat_eq_emultiplicity <| factorial_ne_zero (p * n), Nat.cast_add,
      padicValNat_eq_emultiplicity <| factorial_ne_zero n]
  exact Prime.emultiplicity_factorial_mul hp.out

/-- The `p`-adic valuation of `m` equals zero if it is between `p * k` and `p * (k + 1)` for
some `k`. -/
theorem padicValNat_eq_zero_of_mem_Ioo {m k : ℕ}
    (hm : m ∈ Set.Ioo (p * k) (p * (k + 1))) {hp : p ≠ 1} {hm0 : m ≠ 0} :
    padicValNat p m hp hm0 = 0 :=
  padicValNat.eq_zero_of_not_dvd <| not_dvd_of_lt_of_lt_mul_succ hm.1 hm.2

theorem padicValNat_factorial_mul_add {n : ℕ} (m : ℕ) [hp : Fact p.Prime] (h : n < p) :
    padicValNat p (p * m + n)! = padicValNat p (p * m)! := by
  induction n with
  | zero => rfl
  | succ n hn =>
    have e : (p * m + (n + 1))! = (p * m + n + 1) * (p * m + n)! := by
      rw [← add_assoc, factorial_succ]
    have : padicValNat p (p * m + (n + 1))! = padicValNat p ((p * m + n + 1) * (p * m + n)!) := by
      simp only [e]
    rw [this, padicValNat.mul (succ_ne_zero (p * m + n)) (factorial_ne_zero (p * m + _)),
      hn (lt_of_succ_lt h),
      padicValNat_eq_zero_of_mem_Ioo (m := p * m + n + 1) (k := m)
        ⟨by omega, by rw [Nat.mul_succ]; omega⟩,
      zero_add]

/-- The `p`-adic valuation of `n!` is equal to the `p`-adic valuation of the factorial of the
largest multiple of `p` below `n`, i.e. `(p * ⌊n / p⌋)!`. -/
@[simp] theorem padicValNat_mul_div_factorial (n : ℕ) [hp : Fact p.Prime] :
    padicValNat p (p * (n / p))! = padicValNat p n ! := by
  have := (padicValNat_factorial_mul_add (p := p) (n / p) <| mod_lt n hp.out.pos).symm
  convert this using 3
  exact (div_add_mod n p).symm

/-- **Legendre's Theorem**

The `p`-adic valuation of `n!` is the sum of the quotients `n / p ^ i`. This sum is expressed
over the finset `Ico 1 b` where `b` is any exponent with `n < p ^ b`. -/
theorem padicValNat_factorial {n b : ℕ} [hp : Fact p.Prime] (hnb : n < p ^ b) :
    padicValNat p (n !) = ∑ i ∈ Finset.Ico 1 b, n / p ^ i := by
  exact_mod_cast ((padicValNat_eq_emultiplicity (p := p) <| factorial_ne_zero _) ▸
      Prime.emultiplicity_factorial hp.out hnb)

/-- **Legendre's Theorem**

Taking (`p - 1`) times the `p`-adic valuation of `n!` equals `n` minus the sum of base `p` digits
of `n`. -/
theorem sub_one_mul_padicValNat_factorial [hp : Fact p.Prime] (n : ℕ) :
    (p - 1) * padicValNat p (n !) = n - (p.digits n).sum := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [padicValNat_one_right]
  have hb : n < p ^ succ (log p n hp.out.one_lt hn + 1) :=
    (lt_pow_succ_log_self hp.out.one_lt hn).trans_le
      (Nat.pow_le_pow_right hp.out.pos (le_succ _))
  rw [padicValNat_factorial hb]
  nth_rw 2 [← zero_add 1]
  rw [Nat.succ_eq_add_one, ← Finset.sum_Ico_add' _ 0 _ 1,
    Ico_zero_eq_range, ← sub_one_mul_sum_log_div_pow_eq_sub_sum_digits hp.out.one_lt hn,
    Nat.succ_eq_add_one]

variable (p)

theorem sub_one_mul_padicValNat_factorial_lt_of_ne_zero [hp : Fact p.Prime] {n : ℕ} (hn : n ≠ 0) :
    (p - 1) * padicValNat p n.factorial < n := by
  rw [sub_one_mul_padicValNat_factorial n]
  refine Nat.sub_lt_self ?_ (digit_sum_le p n)
  have hnil : p.digits n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn
  exact List.sum_pos_iff_exists_pos_nat.mpr
    ⟨_, List.getLast_mem hnil, Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero p hn)⟩

theorem padicValNat_factorial_lt_of_ne_zero [hp : Fact p.Prime] {n : ℕ} (hn : n ≠ 0) :
    padicValNat p n.factorial < n := by
  apply lt_of_le_of_lt _ (sub_one_mul_padicValNat_factorial_lt_of_ne_zero p hn)
  conv_lhs => rw [← one_mul (padicValNat p n !)]
  gcongr
  exact le_sub_one_of_lt (Nat.Prime.one_lt hp.elim)

theorem padicValNat_factorial_le [hp : Fact p.Prime] (n : ℕ) : padicValNat p n.factorial ≤ n := by
  by_cases hn : n = 0
  · subst hn
    simp [padicValNat_one_right]
  · exact le_of_lt (padicValNat_factorial_lt_of_ne_zero p hn)

variable {p}

/-- **Kummer's Theorem**

The `p`-adic valuation of `n.choose k` is the number of carries when `k` and `n - k` are added
in base `p`. This sum is expressed over the finset `Ico 1 b` where `b` is any exponent with
`n < p ^ b`. -/
theorem padicValNat_choose {n k b : ℕ} [hp : Fact p.Prime] (hkn : k ≤ n) (hnb : n < p ^ b) :
    padicValNat p (choose n k) (hn := choose_ne_zero hkn) =
      #{i ∈ Finset.Ico 1 b | p ^ i ≤ k % p ^ i + (n - k) % p ^ i} := by
  exact_mod_cast (padicValNat_eq_emultiplicity (p := p) <| (choose_ne_zero hkn)) ▸
    Prime.emultiplicity_choose hp.out hkn hnb

/-- **Kummer's Theorem**

The `p`-adic valuation of `(n + k).choose k` is the number of carries when `k` and `n` are added
in base `p`. This sum is expressed over the finset `Ico 1 b` where `b` is any exponent with
`n + k < p ^ b`. -/
theorem padicValNat_choose' {n k b : ℕ} [hp : Fact p.Prime] (hnb : n + k < p ^ b) :
    padicValNat p (choose (n + k) k) (hn := choose_ne_zero (Nat.le_add_left k n)) =
      #{i ∈ Finset.Ico 1 b | p ^ i ≤ k % p ^ i + n % p ^ i} := by
  exact_mod_cast (padicValNat_eq_emultiplicity (p := p) <| choose_ne_zero <|
    Nat.le_add_left k n) ▸ Prime.emultiplicity_choose' hp.out hnb

/-- **Kummer's Theorem**
Taking (`p - 1`) times the `p`-adic valuation of the binomial `n + k` over `k` equals the sum of the
digits of `k` plus the sum of the digits of `n` minus the sum of digits of `n + k`, all base `p`.
-/
theorem sub_one_mul_padicValNat_choose_eq_sub_sum_digits' {k n : ℕ} [hp : Fact p.Prime] :
    (p - 1) * padicValNat p (choose (n + k) k) (hn := choose_ne_zero (Nat.le_add_left k n)) =
    (p.digits k).sum + (p.digits n).sum - (p.digits (n + k)).sum := by
  have h : k ≤ n + k := by exact Nat.le_add_left k n
  simp only [Nat.choose_eq_factorial_div_factorial h]
  rw [padicValNat.div_of_dvd (factorial_ne_zero _) <| factorial_mul_factorial_dvd_factorial h,
    Nat.mul_sub_left_distrib, padicValNat.mul (factorial_ne_zero _) (factorial_ne_zero _),
    Nat.mul_add]
  simp only [sub_one_mul_padicValNat_factorial]
  rw [← Nat.sub_add_comm <| digit_sum_le p k, Nat.add_sub_cancel n k, ← Nat.add_sub_assoc <|
      digit_sum_le p n, Nat.sub_sub (k + n), ← Nat.sub_right_comm, Nat.sub_sub, sub_add_eq,
      add_comm, tsub_tsub_assoc (Nat.le_refl (k + n)) <| (add_comm k n) ▸ (Nat.add_le_add
      (digit_sum_le p n) (digit_sum_le p k)), Nat.sub_self (k + n), zero_add, add_comm]

/-- **Kummer's Theorem**
Taking (`p - 1`) times the `p`-adic valuation of the binomial `n` over `k` equals the sum of the
digits of `k` plus the sum of the digits of `n - k` minus the sum of digits of `n`, all base `p`.
-/
theorem sub_one_mul_padicValNat_choose_eq_sub_sum_digits {k n : ℕ} [hp : Fact p.Prime]
    (h : k ≤ n) : (p - 1) * padicValNat p (choose n k) (hn := choose_ne_zero h) =
    (p.digits k).sum + (p.digits (n - k)).sum - (p.digits n).sum := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' h
  simpa [Nat.add_sub_cancel] using sub_one_mul_padicValNat_choose_eq_sub_sum_digits' (p := p)
    (k := k) (n := m)

end padicValNat

section padicValInt

variable {p : ℕ}

theorem padicValInt_dvd_iff_of_ne_one (hp : p ≠ 1) (n : ℕ) (a : ℤ) :
    (p : ℤ) ^ n ∣ a ↔ ∀ ha : a ≠ 0, n ≤ padicValInt p a := by
  rcases eq_or_ne a 0 with rfl | ha
  · exact iff_of_true (dvd_zero _) (fun ha ↦ absurd rfl ha)
  · have key : (p : ℤ) ^ n ∣ a ↔ n ≤ padicValInt p a := by
      change _ ↔ n ≤ padicValNat p a.natAbs hp (Int.natAbs_ne_zero.2 ha)
      rw [← Int.natAbs_dvd_natAbs, Int.natAbs_pow, Int.natAbs_natCast,
        padicValNat_dvd_iff_le_of_ne_one hp (Int.natAbs_ne_zero.2 ha)]
    exact ⟨fun h _ ↦ key.1 h, fun h ↦ key.2 (h ha)⟩

theorem padicValInt_dvd_iff [hp : Fact p.Prime] (n : ℕ) (a : ℤ) :
    (p : ℤ) ^ n ∣ a ↔ ∀ ha : a ≠ 0, n ≤ padicValInt p a :=
  padicValInt_dvd_iff_of_ne_one hp.out.ne_one n a

theorem padicValInt_dvd (hp : p ≠ 1) {a : ℤ} (ha : a ≠ 0) : (p : ℤ) ^ padicValInt p a ∣ a :=
  (padicValInt_dvd_iff_of_ne_one hp _ a).2 fun _ ↦ le_rfl

theorem padicValInt_self [hp : Fact p.Prime] : padicValInt p p = 1 :=
  padicValInt.self hp.out.one_lt

theorem padicValInt.mul [hp : Fact p.Prime] {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    padicValInt p (a * b) = padicValInt p a + padicValInt p b := by
  have e : padicValInt p (a * b) = padicValNat p (a.natAbs * b.natAbs) := by
    change padicValNat p (a * b).natAbs _ _ = _
    simp only [Int.natAbs_mul]
  rw [e, padicValNat.mul (Int.natAbs_ne_zero.2 ha) (Int.natAbs_ne_zero.2 hb)]
  rfl

theorem padicValInt_mul_eq_succ [hp : Fact p.Prime] (a : ℤ) (ha : a ≠ 0) :
    padicValInt p (a * p) (hz := mul_ne_zero ha (Int.natCast_ne_zero.mpr hp.out.ne_zero)) =
      padicValInt p a + 1 := by
  rw [padicValInt.mul ha (Int.natCast_ne_zero.mpr hp.out.ne_zero)]
  simp only [padicValInt.of_nat, padicValNat_self]

end padicValInt
