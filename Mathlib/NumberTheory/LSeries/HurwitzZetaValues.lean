/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Special values of Hurwitz and Riemann zeta functions

This file gives the formula for `ζ (2 * k)`, for `k` a non-zero integer, in terms of Bernoulli
numbers. More generally, we give formulae for any Hurwitz zeta functions at any (strictly) negative
integer in terms of Bernoulli polynomials.

(Note that most of the actual work for these formulae is done elsewhere, in
`Mathlib/NumberTheory/ZetaValues.lean`. This file has only those results which really need the
definition of Hurwitz zeta and related functions, rather than working directly with the defining
sums in the convergence range.)

## Main results

- `hurwitzZeta_neg_nat`: for `k : ℕ` with `k ≠ 0`, and any `x ∈ ℝ / ℤ`, the special value
  `hurwitzZeta x (-k)` is equal to `-(Polynomial.bernoulli (k + 1) x) / (k + 1)`.
- `riemannZeta_neg_nat_eq_bernoulli` : for any `k ∈ ℕ` we have the formula
  `riemannZeta (-k) = (-1) ^ k * bernoulli (k + 1) / (k + 1)`
- `riemannZeta_two_mul_nat`: formula for `ζ(2 * k)` for `k ∈ ℕ, k ≠ 0` in terms of Bernoulli
  numbers

## TODO

* Extend to cover Dirichlet L-functions.
* The formulae are correct for `s = 0` as well, but we do not prove this case, since this requires
  Fourier series which are only conditionally convergent, which is difficult to approach using the
  methods in the library at the present time (May 2024).
-/

public section

open Complex Real Set

open scoped Nat

private theorem two_mul_nat_ne_one (k : ℕ) : (2 * k : ℂ) ≠ 1 := by
  exact_mod_cast (show 2 * k ≠ 1 by omega)

private theorem one_sub_two_mul_nat_ne_one {k : ℕ} (hk : k ≠ 0) : (1 - 2 * k : ℂ) ≠ 1 := by
  intro h
  apply mul_ne_zero (two_ne_zero : (2 : ℂ) ≠ 0) (Nat.cast_ne_zero.mpr hk)
  linear_combination -h

private theorem neg_nat_ne_one (k : ℕ) : (-(k : ℂ)) ≠ 1 := by
  exact_mod_cast (show -(k : ℤ) ≠ 1 by omega)

private theorem neg_two_mul_nat_ne_one (k : ℕ) : (-(2 * k : ℂ)) ≠ 1 := by
  simpa only [Nat.cast_mul, Nat.cast_two] using neg_nat_ne_one (2 * k)

private theorem two_mul_nat_add_one_ne_zero (k : ℕ) : (2 * k + 1 : ℂ) ≠ 0 := by
  exact_mod_cast (show 2 * k + 1 ≠ 0 by omega)

namespace HurwitzZeta

variable {k : ℕ} {x : ℝ}

/-- Express the value of `cosZeta` at a positive even integer as a value
of the Bernoulli polynomial. -/
theorem cosZeta_two_mul_nat (hk : k ≠ 0) (hx : x ∈ Icc 0 1) :
    cosZeta x (2 * k) (by exact Or.inl (two_mul_nat_ne_one k)) =
      (-1) ^ (k + 1) * (2 * π) ^ (2 * k) / 2 / (2 * k)! *
      ((Polynomial.bernoulli (2 * k)).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  rw [← (hasSum_nat_cosZeta x (?_ : 1 < re (2 * k))).tsum_eq]
  · refine Eq.trans ?_ <|
      (congr_arg ofReal (hasSum_one_div_nat_pow_mul_cos hk hx).tsum_eq).trans ?_
    · rw [ofReal_tsum]
      refine tsum_congr fun n ↦ ?_
      simp only [ofReal_mul, ofReal_div, ofReal_pow, ofReal_one, ofReal_natCast]
      have hp : (2 * (k : ℂ)) = ((2 * k : ℕ) : ℂ) := by push_cast; rfl
      simp only [hp, cpow_natCast]
      ring
    · push_cast
      congr 1
      have : (Polynomial.bernoulli (2 * k)).map (algebraMap ℚ ℂ) = _ :=
        (Polynomial.map_map (algebraMap ℚ ℝ) ofRealHom _).symm
      rw [this, ← ofRealHom_eq_coe, ← ofRealHom_eq_coe]
      apply Polynomial.map_aeval_eq_aeval_map (by simp)
  · norm_cast
    lia

/--
Express the value of `sinZeta` at an odd integer `> 1` as a value of the Bernoulli polynomial.

Note that this formula is also correct for `k = 0` (i.e. for the value at `s = 1`), but we do not
prove it in this case, owing to the additional difficulty of working with series that are only
conditionally convergent.
-/
theorem sinZeta_two_mul_nat_add_one (hk : k ≠ 0) (hx : x ∈ Icc 0 1) :
    sinZeta x (2 * k + 1) = (-1) ^ (k + 1) * (2 * π) ^ (2 * k + 1) / 2 / (2 * k + 1)! *
      ((Polynomial.bernoulli (2 * k + 1)).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  rw [← (hasSum_nat_sinZeta x (?_ : 1 < re (2 * k + 1))).tsum_eq]
  · refine Eq.trans ?_ <|
      (congr_arg ofReal (hasSum_one_div_nat_pow_mul_sin hk hx).tsum_eq).trans ?_
    · rw [ofReal_tsum]
      refine tsum_congr fun n ↦ ?_
      simp only [ofReal_mul, ofReal_div, ofReal_pow, ofReal_one, ofReal_natCast]
      have hp : (2 * (k : ℂ) + 1) = ((2 * k + 1 : ℕ) : ℂ) := by push_cast; rfl
      simp only [hp, cpow_natCast]
      ring
    · push_cast
      congr 1
      have : (Polynomial.bernoulli (2 * k + 1)).map (algebraMap ℚ ℂ) = _ :=
        (Polynomial.map_map (algebraMap ℚ ℝ) ofRealHom _).symm
      rw [this, ← ofRealHom_eq_coe, ← ofRealHom_eq_coe]
      apply Polynomial.map_aeval_eq_aeval_map (by simp)
  · norm_cast
    lia

private theorem factorial_prefactor_eq_reciprocalGammaℂ_div {n : ℕ} (hn : n ≠ 0) :
    ((2 * π : ℂ) ^ n / 2 / (n ! : ℂ)) = reciprocalGammaℂ n / n := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hpos : 0 < (n : ℂ).re := by
    rw [natCast_re]
    exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hregular := Gamma_regular_of_re_pos hpos
  have hgamma := Gamma_ne_zero hregular
  have hfact : (n ! : ℂ) = n * Complex.Gamma n := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, Complex.Gamma_nat_eq_factorial]
  rw [reciprocalGammaℂ, reciprocalGamma_eq_inv hregular, cpow_natCast]
  simp only [hfact]
  field

/-- Reformulation of `cosZeta_two_mul_nat` using the reciprocal complex-place Gamma factor. -/
theorem cosZeta_two_mul_nat' (hk : k ≠ 0) (hx : x ∈ Icc (0 : ℝ) 1) :
    cosZeta x (2 * k) (by exact Or.inl (two_mul_nat_ne_one k)) =
      (-1) ^ (k + 1) / (2 * k) * reciprocalGammaℂ (2 * k) *
        ((Polynomial.bernoulli (2 * k)).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  rw [cosZeta_two_mul_nat hk hx]
  congr 1
  have h := factorial_prefactor_eq_reciprocalGammaℂ_div (n := 2 * k) (by omega)
  push_cast at h
  rw [mul_div_assoc₀, mul_div_assoc₀, h]
  field

/-- Rewrite `sinZeta_two_mul_nat_add_one` using the reciprocal complex-place Gamma factor. -/
theorem sinZeta_two_mul_nat_add_one' (hk : k ≠ 0) (hx : x ∈ Icc (0 : ℝ) 1) :
    sinZeta x (2 * k + 1) =
      Checked.div ((-1 : ℂ) ^ (k + 1)) (2 * k + 1)
        (by exact (two_mul_nat_add_one_ne_zero k).isUnit) *
      reciprocalGammaℂ (2 * k + 1) *
      ((Polynomial.bernoulli (2 * k + 1)).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  rw [sinZeta_two_mul_nat_add_one hk hx]
  congr 1
  have h := factorial_prefactor_eq_reciprocalGammaℂ_div (n := 2 * k + 1) (by omega)
  push_cast at h
  rw [mul_div_assoc₀, mul_div_assoc₀, h]
  field

private theorem signed_powers_mul (k : ℕ) : (-1 : ℂ) ^ k * (-1) ^ (k + 1) = -1 := by
  rw [pow_succ, ← mul_assoc, ← mul_pow]
  norm_num

theorem hurwitzZetaEven_one_sub_two_mul_nat (hk : k ≠ 0) (hx : x ∈ Icc (0 : ℝ) 1) :
    hurwitzZetaEven x (1 - 2 * k) (by exact one_sub_two_mul_nat_ne_one hk) =
      -1 / (2 * k) * ((Polynomial.bernoulli (2 * k)).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  have hpos : 0 < (2 * (k : ℂ)).re := by
    rw [← Nat.cast_two, ← Nat.cast_mul, natCast_re]
    exact Nat.cast_pos.mpr (Nat.mul_pos two_pos (Nat.pos_of_ne_zero hk))
  have hregular := Gamma_regular_of_re_pos hpos
  have harg : (π : ℂ) * (2 * k) / 2 = ↑((k : ℝ) * π) := by push_cast; ring
  have hcos : cos ((π : ℂ) * (2 * k) / 2) = (-1) ^ k := by
    rw [harg, ← ofReal_cos, ← sub_zero ((k : ℝ) * π), cos_nat_mul_pi_sub,
      Real.cos_zero, mul_one, ofReal_pow, ofReal_neg, ofReal_one]
  rw [hurwitzZetaEven_one_sub _ hregular (Or.inr (two_mul_nat_ne_one k)), ← Gammaℂ,
    cosZeta_two_mul_nat' hk hx, hcos]
  let B := ((Polynomial.bernoulli (2 * k)).map (algebraMap ℚ ℂ)).eval (x : ℂ)
  calc
    _ = (reciprocalGammaℂ (2 * k) * Gammaℂ (2 * k)) *
        (((-1 : ℂ) ^ k * (-1) ^ (k + 1)) / (2 * k)) * B := by
      field_simp
      rfl
    _ = _ := by rw [reciprocalGammaℂ_mul_Gammaℂ hregular, signed_powers_mul, one_mul]

theorem hurwitzZetaOdd_neg_two_mul_nat (hk : k ≠ 0) (hx : x ∈ Icc (0 : ℝ) 1) :
    hurwitzZetaOdd x (-(2 * k)) =
    Checked.div (-1 : ℂ) (2 * k + 1) (by exact (two_mul_nat_add_one_ne_zero k).isUnit) *
      ((Polynomial.bernoulli (2 * k + 1)).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  have hpos : 0 < (2 * (k : ℂ) + 1).re := by
    rw [← Nat.cast_two, ← Nat.cast_mul, ← Nat.cast_one, ← Nat.cast_add, natCast_re]
    positivity
  have hregular := Gamma_regular_of_re_pos hpos
  have harg : (π : ℂ) * (2 * k + 1) / 2 = ↑((k : ℝ) * π + π / 2) := by push_cast; ring
  have hsin : sin ((π : ℂ) * (2 * k + 1) / 2) = (-1) ^ k := by
    rw [harg, ← ofReal_sin, Real.sin_add_pi_div_two, ← sub_zero ((k : ℝ) * π), cos_nat_mul_pi_sub,
      Real.cos_zero, mul_one, ofReal_pow, ofReal_neg, ofReal_one]
  rw [(by ring : -(2 * k : ℂ) = 1 - (2 * k + 1)), hurwitzZetaOdd_one_sub _ hregular, ← Gammaℂ,
    sinZeta_two_mul_nat_add_one' hk hx, hsin]
  let B := ((Polynomial.bernoulli (2 * k + 1)).map (algebraMap ℚ ℂ)).eval (x : ℂ)
  calc
    _ = (reciprocalGammaℂ (2 * k + 1) * Gammaℂ (2 * k + 1)) *
        Checked.div ((-1 : ℂ) ^ k * (-1) ^ (k + 1)) (2 * k + 1)
          (two_mul_nat_add_one_ne_zero k).isUnit * B := by
      field_simp
      rfl
    _ = _ := by rw [reciprocalGammaℂ_mul_Gammaℂ hregular, signed_powers_mul, one_mul]

-- private because it is superseded by `hurwitzZeta_neg_nat` below
private lemma hurwitzZeta_one_sub_two_mul_nat (hk : k ≠ 0) (hx : x ∈ Icc (0 : ℝ) 1) :
    hurwitzZeta x (1 - 2 * k) (one_sub_two_mul_nat_ne_one hk) =
      -1 / (2 * k) * ((Polynomial.bernoulli (2 * k)).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  suffices hurwitzZetaOdd x (1 - 2 * k) = 0 by
    rw [hurwitzZeta, this, add_zero, hurwitzZetaEven_one_sub_two_mul_nat hk hx]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [Nat.cast_succ, show (1 : ℂ) - 2 * (k + 1) = -2 * k - 1 by ring,
    hurwitzZetaOdd_neg_two_mul_nat_sub_one]

-- private because it is superseded by `hurwitzZeta_neg_nat` below
private lemma hurwitzZeta_neg_two_mul_nat (hk : k ≠ 0) (hx : x ∈ Icc (0 : ℝ) 1) :
    hurwitzZeta x (-(2 * k)) (neg_two_mul_nat_ne_one k) =
      Checked.div (-1 : ℂ) (2 * k + 1) (two_mul_nat_add_one_ne_zero k).isUnit *
      ((Polynomial.bernoulli (2 * k + 1)).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  suffices hurwitzZetaEven x (-(2 * k)) (neg_two_mul_nat_ne_one k) = 0 by
    rw [hurwitzZeta, this, zero_add, hurwitzZetaOdd_neg_two_mul_nat hk hx]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  simpa using hurwitzZetaEven_neg_two_mul_nat_add_one x k

/-- Values of Hurwitz zeta functions at (strictly) negative integers.

TODO: This formula is also correct for `k = 0`; but our current proof does not work in this
case. -/
theorem hurwitzZeta_neg_nat (hk : k ≠ 0) (hx : x ∈ Icc (0 : ℝ) 1) :
    hurwitzZeta x (-k) (by exact neg_nat_ne_one k) =
    -1 / (k + 1) * ((Polynomial.bernoulli (k + 1)).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  rcases Nat.even_or_odd' k with ⟨n, (rfl | rfl)⟩
  · exact_mod_cast hurwitzZeta_neg_two_mul_nat (by lia : n ≠ 0) hx
  · exact_mod_cast hurwitzZeta_one_sub_two_mul_nat (by lia : n + 1 ≠ 0) hx

end HurwitzZeta

open HurwitzZeta

/-- Explicit formula for `ζ (2 * k)`, for `k ∈ ℕ` with `k ≠ 0`, in terms of the Bernoulli number
`bernoulli (2 * k)`.

Compare `hasSum_zeta_nat` for a version formulated in terms of a sum over `1 / n ^ (2 * k)`, and
`riemannZeta_neg_nat_eq_bernoulli` for values at negative integers (equivalent to the above via
the functional equation). -/
theorem riemannZeta_two_mul_nat {k : ℕ} (hk : k ≠ 0) :
    riemannZeta (2 * k) (by exact two_mul_nat_ne_one k) = (-1) ^ (k + 1) * (2 : ℂ) ^ (2 * k - 1)
      * (π : ℂ) ^ (2 * k) * bernoulli (2 * k) / (2 * k)! := by
  have h := zeta_nat_eq_tsum_of_gt_one (k := 2 * k) (by omega)
  simp only [Nat.cast_mul, Nat.cast_two] at h
  rw [h]
  simpa only [ofReal_tsum, ofReal_div, ofReal_mul, ofReal_pow, ofReal_neg, ofReal_one,
    ofReal_natCast, ofReal_ofNat, ofReal_ratCast] using congrArg ofReal (hasSum_zeta_nat hk).tsum_eq

/-- Explicit formula for `ζ (2 * k)`, for `k ∈ ℕ`, in terms of the Bernoulli number
`bernoulli (2 * k)`. Compare `riemannZeta_two_mul_nat` which avoids a cast in an exponent
but requires `k ≠ 0`. -/
theorem riemannZeta_two_mul_nat' {k : ℕ} :
    riemannZeta (2 * k) (by exact two_mul_nat_ne_one k) = (-1) ^ (k + 1) * (2 : ℂ) ^ (2 * k - 1 : ℤ)
      * (π : ℂ) ^ (2 * k) * bernoulli (2 * k) / (2 * k)! := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [riemannZeta_zero]
    norm_num
  · have h (m : ℤ) (hm : m = ((2 * k - 1 : ℕ) : ℤ)) :
        (2 : ℂ) ^ m = (2 : ℂ) ^ (2 * k - 1 : ℕ) := by
      subst m
      exact zpow_natCast₀ _ _
    rw [h _ (by omega), riemannZeta_two_mul_nat hk]

theorem riemannZeta_two : riemannZeta 2 = (π : ℂ) ^ 2 / 6 := by
  simpa only [Nat.cast_ofNat, ofReal_tsum, ofReal_div, ofReal_one, ofReal_pow, ofReal_natCast,
    ofReal_ofNat] using (zeta_nat_eq_tsum_of_gt_one (k := 2) one_lt_two).trans
      (by simpa only [ofReal_tsum, ofReal_div, ofReal_one, ofReal_pow, ofReal_natCast, ofReal_ofNat]
        using congrArg ofReal hasSum_zeta_two.tsum_eq)

theorem riemannZeta_four : riemannZeta 4 = π ^ 4 / 90 := by
  simpa only [Nat.cast_ofNat, ofReal_div, ofReal_pow, ofReal_ofNat] using
    (zeta_nat_eq_tsum_of_gt_one (k := 4) (by omega)).trans
      (by simpa only [ofReal_tsum, ofReal_div, ofReal_one, ofReal_pow, ofReal_natCast, ofReal_ofNat]
        using congrArg ofReal hasSum_zeta_four.tsum_eq)

/-- Value of Riemann zeta at `-ℕ` in terms of `bernoulli'`. -/
theorem riemannZeta_neg_nat_eq_bernoulli' (k : ℕ) :
    riemannZeta (-k) (by exact neg_nat_ne_one k) = -bernoulli' (k + 1) / (k + 1) := by
  rcases eq_or_ne k 0 with rfl | hk
  · have h : riemannZeta (-(0 : ℕ)) (by exact neg_nat_ne_one 0) = -1 / 2 := by
      simpa only [Nat.cast_zero, neg_zero] using riemannZeta_zero
    rw [h]
    norm_num [bernoulli'_one, Rat.cast_div, neg_div₀]
  · rw [← hurwitzZeta_zero, ← QuotientAddGroup.mk_zero, hurwitzZeta_neg_nat hk
      (left_mem_Icc.mpr zero_le_one), ofReal_zero, Polynomial.eval_zero_map,
      Polynomial.bernoulli_eval_zero, Algebra.algebraMap_eq_smul_one, Rat.smul_one_eq_cast,
      div_mul_eq_mul_div₀, neg_one_mul, bernoulli_eq_bernoulli'_of_ne_one (by simp [hk])]

/-- Value of Riemann zeta at `-ℕ` in terms of `bernoulli`. -/
theorem riemannZeta_neg_nat_eq_bernoulli (k : ℕ) :
    riemannZeta (-k) (by exact neg_nat_ne_one k) = (-1 : ℂ) ^ k * bernoulli (k + 1) / (k + 1) := by
  rw [riemannZeta_neg_nat_eq_bernoulli', bernoulli, Rat.cast_mul, Rat.cast_pow, Rat.cast_neg,
    Rat.cast_one, ← neg_one_mul, ← mul_assoc, pow_succ, ← mul_assoc, ← mul_pow, neg_one_mul (-1),
    neg_neg, one_pow, one_mul]
