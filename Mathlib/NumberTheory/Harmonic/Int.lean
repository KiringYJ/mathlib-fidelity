/-
Copyright (c) 2023 Koundinya Vajjha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Koundinya Vajjha, Thomas Browning
-/
module

public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Tactic.Positivity

/-!

The nth Harmonic number is not an integer. We formalize the proof using
2-adic valuations. This proof is due to Kürschák.

Reference:
https://kconrad.math.uconn.edu/blurbs/gradnumthy/padicharmonicsum.pdf

-/

public section

lemma harmonic_pos {n : ℕ} (Hn : n ≠ 0) : 0 < harmonic n := by
  unfold harmonic
  rw [← Finset.nonempty_range_iff] at Hn
  positivity

/-- The 2-adic valuation of the n-th harmonic number is the negative of the logarithm of n. -/
theorem padicValRat_two_harmonic {n : ℕ} (hn : n ≠ 0) :
    padicValRat 2 (harmonic n) (hq := (harmonic_pos hn).ne') = -Nat.log 2 n := by
  induction n with
  | zero => exact absurd rfl hn
  | succ n ih =>
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    have hn1 : ((n + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr n.succ_ne_zero
    have hinv : (Checked.inv ((n + 1 : ℕ) : ℚ) hn1.isUnit) ≠ 0 := inv_ne_zero
    have key : padicValRat 2 (harmonic n) (hq := (harmonic_pos hn).ne') ≠
        padicValRat 2 (↑(n + 1))⁻¹ (hq := hinv) := by
      rw [ih hn, padicValRat.inv hn1, padicValRat.of_nat, Ne, neg_inj, Nat.cast_inj]
      exact Nat.log_ne_padicValNat_succ hn
    simp only [harmonic_succ]
    rw [padicValRat.add_eq_min (harmonic_succ n ▸ (harmonic_pos n.succ_ne_zero).ne')
        (harmonic_pos hn).ne' hinv key, ih hn, padicValRat.inv hn1,
        padicValRat.of_nat, min_neg_neg, neg_inj, ← Nat.cast_max, Nat.cast_inj]
    exact Nat.max_log_padicValNat_succ_eq_log_succ hn

private lemma padicNorm_two_harmonic_rat {n : ℕ} (hn : n ≠ 0) :
    padicNorm 2 (harmonic n) = 2 ^ Nat.log 2 n := by
  let power (k : ℤ) : ℚ := Checked.zpow 2 k (fun _ ↦ (by norm_num : (2 : ℚ) ≠ 0).isUnit)
  have hq := (harmonic_pos hn).ne'
  have h : -padicValRat 2 (harmonic n) (hq := hq) = (Nat.log 2 n : ℤ) := by
    rw [padicValRat_two_harmonic hn, neg_neg]
  rw [padicNorm.eq_zpow_of_nonzero hq]
  exact congrArg power h

/-- The 2-adic norm of the n-th harmonic number is 2 raised to the logarithm of n in base 2. -/
lemma padicNorm_two_harmonic {n : ℕ} (hn : n ≠ 0) :
    ‖(harmonic n : ℚ_[2])‖ = 2 ^ (Nat.log 2 n) := by
  rw [Padic.eq_padicNorm, padicNorm_two_harmonic_rat hn, Rat.cast_pow, Rat.cast_ofNat]

/-- The n-th harmonic number is not an integer for n ≥ 2. -/
theorem harmonic_not_int {n : ℕ} (h : 2 ≤ n) : ¬ (harmonic n).isInt := by
  apply padicNorm.not_int_of_not_padic_int 2
  rw [padicNorm_two_harmonic_rat (ne_zero_of_lt h)]
  exact one_lt_pow₀ one_lt_two (Nat.log_pos one_lt_two h).ne'
