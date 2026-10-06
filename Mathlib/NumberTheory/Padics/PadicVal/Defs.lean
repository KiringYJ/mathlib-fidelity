/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Matthew Robert Ballard
-/
module

public import Mathlib.Data.Nat.MaxPowDiv
public import Mathlib.RingTheory.Multiplicity
public import Mathlib.Data.Nat.Factors

/-!
# `p`-adic Valuation

This file defines the `p`-adic valuation on `ℕ`, `ℤ`, and `ℚ`.

The `p`-adic valuation on `ℚ` is the difference of the multiplicities of `p` in the numerator and
denominator of `q`. This function obeys the standard properties of a valuation, with the appropriate
assumptions on `p`. The `p`-adic valuations on `ℕ` and `ℤ` agree with that on `ℚ`.

The valuation induces a norm on `ℚ`. This norm is defined in
`Mathlib/NumberTheory/Padics/PadicNorm.lean`.
-/

public section

assert_not_exists Field

universe u

open Nat

variable {p : ℕ}

/-- `padic_val_tac` closes `p ≠ 1` for a prime `p` given by a `Fact` instance. -/
macro_rules | `(tactic| padic_val_core) => `(tactic| exact Nat.Prime.ne_one Fact.out)

/-- `padic_val_tac` closes `p ≠ 1` for a prime `p` given by a hypothesis. -/
macro_rules | `(tactic| padic_val_core) => `(tactic| exact Nat.Prime.ne_one ‹_›)

/-- `padic_val_tac` closes `n ≠ 0` from a `NeZero n` instance. -/
macro_rules | `(tactic| padic_val_core) => `(tactic| exact NeZero.ne _)

/-- `padic_val_tac` closes `p ≠ 0` for a prime `p` given by a `Fact` instance. -/
macro_rules | `(tactic| padic_val_core) => `(tactic| exact Nat.Prime.ne_zero Fact.out)

/-- `padic_val_tac` closes `p ≠ 0` for a prime `p` given by a hypothesis. -/
macro_rules | `(tactic| padic_val_core) => `(tactic| exact Nat.Prime.ne_zero ‹_›)

/-- `padic_val_tac` closes `p ^ k ≠ 0` for a prime `p` given by a `Fact` instance. -/
macro_rules
  | `(tactic| padic_val_core) => `(tactic| exact pow_ne_zero _ (Nat.Prime.ne_zero Fact.out))

theorem padicValNat_eq_emultiplicity_of_ne_one (hp : p ≠ 1) {n : ℕ} (hn : n ≠ 0) :
    padicValNat p n hp hn = emultiplicity p n := by
  rw [eq_comm, emultiplicity_eq_coe, pow_dvd_iff_le_padicValNat hp hn,
    pow_dvd_iff_le_padicValNat hp hn]
  simp

@[simp]
theorem Nat.toNat_emultiplicity (hp : p ≠ 1) {n : ℕ} (hn : n ≠ 0) :
    (emultiplicity p n).toNat = padicValNat p n hp hn := by
  simp [← padicValNat_eq_emultiplicity_of_ne_one hp hn]

theorem padicValNat_def (hp : p ≠ 1) {n : ℕ} (hn : n ≠ 0) :
    padicValNat p n hp hn =
      multiplicity p n (Nat.finiteMultiplicity_iff.2 ⟨hp, Nat.pos_of_ne_zero hn⟩) :=
  (multiplicity_eq_of_emultiplicity_eq_some
    (padicValNat_eq_emultiplicity_of_ne_one hp hn).symm).symm

@[deprecated (since := "2026-09-08")] alias padicValNat_def' := padicValNat_def

/-- A simplification of `padicValNat` when one input is prime, by analogy with
`padicValRat_def`. -/
theorem padicValNat_eq_emultiplicity [hp : Fact p.Prime] {n : ℕ} (hn : n ≠ 0) :
    padicValNat p n hp.out.ne_one hn = emultiplicity p n :=
  padicValNat_eq_emultiplicity_of_ne_one hp.out.ne_one hn

namespace padicValNat

@[deprecated (since := "2026-03-15")]
alias maxPowDiv_eq_emultiplicity := padicValNat_eq_emultiplicity

@[deprecated (since := "2026-03-15")]
alias maxPowDiv_eq_multiplicity := padicValNat_def

theorem eq_zero_iff (hp : p ≠ 1) {n : ℕ} (hn : n ≠ 0) : padicValNat p n hp hn = 0 ↔ ¬p ∣ n := by
  simpa using pow_dvd_iff_le_padicValNat (k := 1) hp hn |>.symm |>.not

end padicValNat

open List

theorem le_emultiplicity_iff_replicate_subperm_primeFactorsList {a b : ℕ} {n : ℕ} (ha : a.Prime)
    (hb : b ≠ 0) :
    ↑n ≤ emultiplicity a b ↔ replicate n a <+~ b.primeFactorsList :=
  (replicate_subperm_primeFactorsList_iff ha hb).trans
    pow_dvd_iff_le_emultiplicity |>.symm

theorem le_padicValNat_iff_replicate_subperm_primeFactorsList {a b : ℕ} {n : ℕ} (ha : a.Prime)
    (hb : b ≠ 0) :
    n ≤ padicValNat a b ha.ne_one hb ↔ replicate n a <+~ b.primeFactorsList := by
  rw [← le_emultiplicity_iff_replicate_subperm_primeFactorsList ha hb,
    ← padicValNat_eq_emultiplicity_of_ne_one ha.ne_one hb, ENat.natCast_le_natCast]

/-- A weak upper bound on `padicValNat p n`. -/
theorem mul_padicValNat_le {p n : ℕ} (hp : p ≠ 1) (hn : n ≠ 0) : p * padicValNat p n hp hn ≤ n := by
  grw [Nat.mul_le_pow hp, Nat.le_of_dvd hn.bot_lt pow_padicValNat_dvd]
