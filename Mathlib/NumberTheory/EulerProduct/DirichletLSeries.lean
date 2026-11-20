/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.EulerProduct.ExpLog
public import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The Euler Product for the Riemann Zeta Function and Dirichlet L-Series

The first main result of this file is the Euler Product formula for the Riemann ζ function
$$\prod_p \frac{1}{1 - p^{-s}}
   = \lim_{n \to \infty} \prod_{p < n} \frac{1}{1 - p^{-s}} = \zeta(s)$$
for $s$ with real part $> 1$ ($p$ runs through the primes).
`riemannZeta_eulerProduct` is the second equality above. There are versions
`riemannZeta_eulerProduct_hasProd` and `riemannZeta_eulerProduct_tprod` in terms of `HasProd`
and `tprod`, respectively.

The second result is `dirichletLSeries_eulerProduct` (with variants
`dirichletLSeries_eulerProduct_hasProd` and `dirichletLSeries_eulerProduct_tprod`),
which is the analogous statement for Dirichlet L-series.
-/

@[expose] public section

open Complex

variable {s : ℂ}

private lemma zeta_regular_of_one_lt_re (hs : 1 < s.re) : s ≠ 1 := by
  rintro rfl
  simp at hs

/-- When `s ≠ 0`, the map `n ↦ n^(-s)` is completely multiplicative and vanishes at zero. -/
noncomputable
def riemannZetaSummandHom (hs : s ≠ 0) : ℕ →*₀ ℂ where
  toFun n := (n : ℂ) ^ (-s)
  map_zero' := by simp [hs]
  map_one' := by simp
  map_mul' m n := by
    simpa only [Nat.cast_mul, ofReal_natCast]
      using mul_cpow_ofReal_nonneg m.cast_nonneg n.cast_nonneg _

/-- When `χ` is a Dirichlet character and `s ≠ 0`, the map `n ↦ χ n * n^(-s)` is completely
multiplicative and vanishes at zero. -/
noncomputable
def dirichletSummandHom {n : ℕ} (χ : DirichletCharacter ℂ n) (hs : s ≠ 0) : ℕ →*₀ ℂ where
  toFun n := χ n * (n : ℂ) ^ (-s)
  map_zero' := by simp [hs]
  map_one' := by simp
  map_mul' m n := by
    simp_rw [← ofReal_natCast]
    simpa only [Nat.cast_mul, IsUnit.mul_iff, not_and, map_mul, ofReal_mul,
      mul_cpow_ofReal_nonneg m.cast_nonneg n.cast_nonneg _]
      using mul_mul_mul_comm ..

private lemma term_eq_mul_cpow_neg_of_ne_zero (f : ℕ → ℂ) (hs : s ≠ 0) (n : ℕ) :
    LSeries.term f s n = f n * (n : ℂ) ^ (-s) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [hs]
  · rw [LSeries.term_of_ne_zero hn, cpow_neg, div_eq_mul_inv₀]

private lemma riemannZetaSummandHom_eq_term (hs : s ≠ 0) (n : ℕ) :
    riemannZetaSummandHom hs n = LSeries.term 1 s n := by
  rw [term_eq_mul_cpow_neg_of_ne_zero 1 hs]
  exact (one_mul _).symm

/-- When `s.re > 1`, the map `n ↦ n^(-s)` is norm-summable. -/
lemma summable_riemannZetaSummand (hs : 1 < s.re) :
    Summable (fun n ↦ ‖riemannZetaSummandHom (ne_zero_of_one_lt_re hs) n‖) := by
  simpa only [riemannZetaSummandHom_eq_term] using
    (LSeriesSummable_one_iff.mpr hs).norm

lemma tsum_riemannZetaSummand (hs : 1 < s.re) :
    ∑' (n : ℕ), riemannZetaSummandHom (ne_zero_of_one_lt_re hs) n =
      riemannZeta s (by exact zeta_regular_of_one_lt_re hs) := by
  simpa only [riemannZetaSummandHom_eq_term, LSeries] using LSeries_one_eq_riemannZeta hs

/-- When `s.re > 1`, the map `n ↦ χ(n) * n^(-s)` is norm-summable. -/
lemma summable_dirichletSummand {N : ℕ} (χ : DirichletCharacter ℂ N) (hs : 1 < s.re) :
    Summable (fun n ↦ ‖dirichletSummandHom χ (ne_zero_of_one_lt_re hs) n‖) := by
  simp only [dirichletSummandHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, norm_mul]
  exact (summable_riemannZetaSummand hs).of_nonneg_of_le (fun _ ↦ by positivity)
    (fun n ↦ mul_le_of_le_one_left (norm_nonneg _) <| χ.norm_le_one n)

open scoped LSeries.notation in
lemma tsum_dirichletSummand {N : ℕ} (χ : DirichletCharacter ℂ N) (hs : 1 < s.re) :
    ∑' (n : ℕ), dirichletSummandHom χ (ne_zero_of_one_lt_re hs) n = L ↗χ s := by
  simp only [dirichletSummandHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, LSeries,
    term_eq_mul_cpow_neg_of_ne_zero _ (ne_zero_of_one_lt_re hs)]

open Filter Nat EulerProduct

open scoped Topology

private lemma norm_prime_cpow_neg_lt_one {p : ℕ} (hp : p.Prime) (hs : 1 < s.re) :
    ‖(p : ℂ) ^ (-s)‖ < 1 := by
  rw [norm_natCast_cpow_of_pos hp.pos, neg_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)

private lemma isUnit_zetaEulerFactor {p : ℕ} (hp : p.Prime) (hs : 1 < s.re) :
    IsUnit (1 - (p : ℂ) ^ (-s)) :=
  isUnit_one_sub_of_norm_lt_one (norm_prime_cpow_neg_lt_one hp hs)

private lemma isUnit_dirichletEulerFactor {N p : ℕ} (χ : DirichletCharacter ℂ N)
    (hp : p.Prime) (hs : 1 < s.re) : IsUnit (1 - χ p * (p : ℂ) ^ (-s)) :=
  isUnit_one_sub_of_norm_lt_one (by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one p)).trans_lt
      (norm_prime_cpow_neg_lt_one hp hs))

/-- The Euler product for the Riemann ζ function, valid for `s.re > 1`.
This version is stated in terms of `HasProd`. -/
theorem riemannZeta_eulerProduct_hasProd (hs : 1 < s.re) :
    HasProd (fun p : Primes ↦ Checked.inv (1 - (p : ℂ) ^ (-s))
      (by exact isUnit_zetaEulerFactor p.2 hs))
      (riemannZeta s (by exact zeta_regular_of_one_lt_re hs)) := by
  rw [← tsum_riemannZetaSummand hs]
  apply eulerProduct_completely_multiplicative_hasProd <| summable_riemannZetaSummand hs

/-- The Euler product for the Riemann ζ function, valid for `s.re > 1`.
This version is stated in terms of `tprod`. -/
theorem riemannZeta_eulerProduct_tprod (hs : 1 < s.re) :
    (∏' p : Primes, Checked.inv (1 - (p : ℂ) ^ (-s))
      (by exact isUnit_zetaEulerFactor p.2 hs)) =
      riemannZeta s (by exact zeta_regular_of_one_lt_re hs) :=
  (riemannZeta_eulerProduct_hasProd hs).tprod_eq

/-- The Euler product for the Riemann ζ function, valid for `s.re > 1`.
This version is stated in the form of convergence of finite partial products. -/
theorem riemannZeta_eulerProduct (hs : 1 < s.re) :
    Tendsto (fun n : ℕ ↦ ∏ p : primesBelow n, Checked.inv (1 - (p : ℂ) ^ (-s))
      (by exact isUnit_zetaEulerFactor (mem_primesBelow.mp p.2).2 hs)) atTop
      (𝓝 (riemannZeta s (by exact zeta_regular_of_one_lt_re hs))) := by
  rw [← tsum_riemannZetaSummand hs]
  apply eulerProduct_completely_multiplicative <| summable_riemannZetaSummand hs

open scoped LSeries.notation

/-- The Euler product for Dirichlet L-series, valid for `s.re > 1`.
This version is stated in terms of `HasProd`. -/
theorem DirichletCharacter.LSeries_eulerProduct_hasProd {N : ℕ} (χ : DirichletCharacter ℂ N)
    (hs : 1 < s.re) :
    HasProd (fun p : Primes ↦ Checked.inv (1 - χ p * (p : ℂ) ^ (-s))
      (by exact isUnit_dirichletEulerFactor χ p.2 hs)) (L ↗χ s) := by
  rw [← tsum_dirichletSummand χ hs]
  convert! eulerProduct_completely_multiplicative_hasProd <| summable_dirichletSummand χ hs

/-- The Euler product for Dirichlet L-series, valid for `s.re > 1`.
This version is stated in terms of `tprod`. -/
theorem DirichletCharacter.LSeries_eulerProduct_tprod {N : ℕ} (χ : DirichletCharacter ℂ N)
    (hs : 1 < s.re) :
    (∏' p : Primes, Checked.inv (1 - χ p * (p : ℂ) ^ (-s))
      (by exact isUnit_dirichletEulerFactor χ p.2 hs)) = L ↗χ s :=
  (DirichletCharacter.LSeries_eulerProduct_hasProd χ hs).tprod_eq

/-- The Euler product for Dirichlet L-series, valid for `s.re > 1`.
This version is stated in the form of convergence of finite partial products. -/
theorem DirichletCharacter.LSeries_eulerProduct {N : ℕ} (χ : DirichletCharacter ℂ N)
    (hs : 1 < s.re) :
    Tendsto (fun n : ℕ ↦ ∏ p : primesBelow n, Checked.inv (1 - χ p * (p : ℂ) ^ (-s))
      (by exact isUnit_dirichletEulerFactor χ (mem_primesBelow.mp p.2).2 hs)) atTop
      (𝓝 (L ↗χ s)) := by
  rw [← tsum_dirichletSummand χ hs]
  apply eulerProduct_completely_multiplicative <| summable_dirichletSummand χ hs

open LSeries

/-- A variant of the Euler product for Dirichlet L-series. -/
theorem DirichletCharacter.LSeries_eulerProduct_exp_log {N : ℕ} (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    exp (∑' p : Nat.Primes, -log (1 - χ p * p ^ (-s))) = L ↗χ s := by
  let f := dirichletSummandHom χ <| ne_zero_of_one_lt_re hs
  have h n : term ↗χ s n = f n := by
    exact term_eq_mul_cpow_neg_of_ne_zero _ (ne_zero_of_one_lt_re hs) n
  simpa only [LSeries, h]
    using! exp_tsum_primes_log_eq_tsum (f := f) <| summable_dirichletSummand χ hs

open DirichletCharacter

/-- A variant of the Euler product for the L-series of `ζ`. -/
theorem ArithmeticFunction.LSeries_zeta_eulerProduct_exp_log {s : ℂ} (hs : 1 < s.re) :
    exp (∑' p : Nat.Primes, -Complex.log (1 - p ^ (-s))) = L 1 s := by
  convert!
    modOne_eq_one (R := ℂ) ▸
      DirichletCharacter.LSeries_eulerProduct_exp_log (1 : DirichletCharacter ℂ 1) hs using 7
  rw [MulChar.one_apply <| isUnit_of_subsingleton _, one_mul]

/-- A variant of the Euler product for the Riemann zeta function. -/
theorem riemannZeta_eulerProduct_exp_log {s : ℂ} (hs : 1 < s.re) :
    exp (∑' p : Nat.Primes, -Complex.log (1 - p ^ (-s))) =
      riemannZeta s (by exact zeta_regular_of_one_lt_re hs) :=
  LSeries_one_eq_riemannZeta hs ▸ ArithmeticFunction.LSeries_zeta_eulerProduct_exp_log hs

/-!
### Changing the level of a Dirichlet `L`-series
-/

/-- If `χ` is a Dirichlet character and its level `M` divides `N`, then we obtain the L-series
of `χ` considered as a Dirichlet character of level `N` from the L-series of `χ` by multiplying
with `∏ p ∈ N.primeFactors, (1 - χ p * p ^ (-s))`. -/
lemma DirichletCharacter.LSeries_changeLevel {M N : ℕ} [NeZero N]
    (hMN : M ∣ N) (χ : DirichletCharacter ℂ M) {s : ℂ} (hs : 1 < s.re) :
    LSeries ↗(changeLevel hMN χ) s =
      LSeries ↗χ s * ∏ p ∈ N.primeFactors, (1 - χ p * p ^ (-s)) := by
  let S : Finset Primes := N.primeFactors.subtype Nat.Prime
  let g (p : Primes) : ℂ := 1 - χ p * (p : ℂ) ^ (-s)
  have hprod : (∏ p ∈ S, g p) = ∏ p ∈ N.primeFactors, (1 - χ p * p ^ (-s)) :=
    Finset.prod_subtype_of_mem (s := N.primeFactors)
      (fun p ↦ 1 - χ p * (p : ℂ) ^ (-s)) (fun p hp ↦ (Nat.mem_primeFactors.mp hp).1)
  have hg : Multipliable ((S : Set Primes).mulIndicator g) :=
    multipliable_subtype_iff_mulIndicator.mp Multipliable.of_finite
  rw [← hprod, prod_eq_tprod_mulIndicator, ← DirichletCharacter.LSeries_eulerProduct_tprod _ hs,
    ← DirichletCharacter.LSeries_eulerProduct_tprod _ hs,
    ← Multipliable.tprod_mul (DirichletCharacter.LSeries_eulerProduct_hasProd χ hs).multipliable hg]
  refine tprod_congr fun p ↦ ?_
  by_cases hdvd : (p : ℕ) ∣ N
  · have hc : ¬ IsUnit ((p : ℕ) : ZMod N) := fun h ↦ (ZMod.isUnit_prime_iff_not_dvd p.2).mp h hdvd
    have hm : p ∈ (S : Set Primes) :=
      Finset.mem_subtype.mpr (Nat.mem_primeFactors.mpr ⟨p.2, hdvd, NeZero.ne N⟩)
    rw [Set.mulIndicator_of_mem hm g]
    simp only [g, MulChar.map_nonunit _ hc, zero_mul, sub_zero, inv_one₀, inv_mul_cancel₀]
  · have hc : IsUnit ((p : ℕ) : ZMod N) := (ZMod.isUnit_prime_iff_not_dvd p.2).mpr hdvd
    have hm : p ∉ (S : Set Primes) :=
      fun h ↦ hdvd (Nat.mem_primeFactors.mp (Finset.mem_subtype.mp h)).2.1
    have he : changeLevel hMN χ p = χ p := by
      have h := DirichletCharacter.changeLevel_eq_cast_of_dvd χ hMN hc.unit
      rwa [hc.unit_spec, ZMod.cast_natCast hMN] at h
    rw [Set.mulIndicator_of_notMem hm g]
    simp only [mul_one, he]

section LogDirichlet

open Real hiding log exp_nat_mul exp_add
open ArithmeticFunction Summable

variable {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ}

open scoped Classical in
/-- The coefficients of the logarithmic Euler product. The coefficient at a prime power
`p ^ k` is `1 / k`; only prime powers contribute. -/
noncomputable def ArithmeticFunction.vonMangoldtLogCoefficients (n : ℕ) : ℝ :=
  if hn : IsPrimePow n then
    Checked.div (Λ n) (Real.log n) (Real.log_pos (by exact_mod_cast hn.one_lt)).ne'.isUnit
  else 0

private lemma vonMangoldtLogCoefficients_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    vonMangoldtLogCoefficients (p ^ k) = 1 / (k : ℝ) := by
  have h : IsPrimePow (p ^ k) := (isPrimePow_pow_iff hk).mpr hp.isPrimePow
  have hlog : Real.log p ≠ 0 := hp.log_ne_zero
  have hlogPow : Real.log (((p ^ k : ℕ) : ℝ)) = (k : ℝ) * Real.log (p : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
  rw [vonMangoldtLogCoefficients, dite_eq_left h, vonMangoldt_apply_pow hk,
    vonMangoldt_apply_prime hp]
  simp only [hlogPow]
  field

private lemma vonMangoldtLogCoefficients_mem_Icc (n : ℕ) :
    vonMangoldtLogCoefficients n ∈ Set.Icc (0 : ℝ) 1 := by
  unfold vonMangoldtLogCoefficients
  split_ifs with hn
  · have hp : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn.one_lt)
    exact ⟨div_nonneg vonMangoldt_nonneg hp.le, (div_le_one hp).mpr vonMangoldt_le_log⟩
  · exact ⟨le_rfl, zero_le_one⟩

/-- For `1 < s.re`, the sum over primes of `-log (1 - χ p * p ^ (-s))` — the logarithm of the Euler
product — equals the `L`-series of the coefficients of the logarithmic Euler product twisted by
`χ`.
-/
theorem DirichletCharacter.eulerProduct_log_eq_LSeries (hs : 1 < s.re) :
    ∑' p : Primes, -log (1 - χ p * p ^ (-s)) =
      LSeries (fun n ↦ χ n * vonMangoldtLogCoefficients n) s := by
  have hpow_le (p : Primes) : ‖χ p * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one p)).trans_lt
      (norm_prime_cpow_neg_lt_one p.2 hs)
  let f (n : ℕ) : ℂ := χ n * vonMangoldtLogCoefficients n * ((n : ℂ) ^ (-s))
  have hf : Summable f := by
    have h := LSeriesSummable_of_bounded_of_one_lt_re
      (f := fun n ↦ χ n * (vonMangoldtLogCoefficients n : ℝ)) (m := 1) (fun n _ ↦ by
        have hcoeff := vonMangoldtLogCoefficients_mem_Icc n
        rw [norm_mul, Complex.norm_of_nonneg hcoeff.1]
        exact (mul_le_of_le_one_left hcoeff.1 (χ.norm_le_one n)).trans hcoeff.2) hs
    exact h.congr (term_eq_mul_cpow_neg_of_ne_zero _ (ne_zero_of_one_lt_re hs))
  have hsupport : Function.support f ⊆ {n | IsPrimePow n} := by
    intro n hn
    by_contra hp
    change ¬ IsPrimePow n at hp
    exact hn (by simp [f, vonMangoldtLogCoefficients, hp])
  rw [tsum_congr (fun p ↦ (hasSum_taylorSeries_neg_log (hpow_le p)).tsum_eq.symm)]
  calc
    _ = ∑' (p : Primes) (k : ℕ), f ((p : ℕ) ^ (k + 1)) := by
      refine tsum_congr fun p ↦ tsum_congr fun k ↦ ?_
      simp only [f, mul_pow, vonMangoldtLogCoefficients_prime_pow p.2 (Nat.succ_ne_zero k),
        ofReal_div, ofReal_one, ofReal_natCast, map_pow, Nat.cast_pow,
        ← cpow_nat_mul, ← natCast_cpow_natCast_mul]
      simp only [Nat.cast_succ]
      rw [← mul_div_assoc₀, mul_one, div_mul_eq_mul_div₀]
    _ = ∑' n : {n : ℕ // IsPrimePow n}, f n := by
      exact tsum_primes_pow_eq (f := f) (hf.comp_injective Subtype.val_injective)
    _ = ∑' n : ℕ, f n := tsum_subtype_eq_of_support_subset hsupport
    _ = _ := (tsum_congr (term_eq_mul_cpow_neg_of_ne_zero _ (ne_zero_of_one_lt_re hs))).symm

/-- For `1 < s.re`, the Dirichlet L-function is the exponential of the `L`-series of the
coefficients of the logarithmic Euler product twisted by `χ`.
-/
theorem DirichletCharacter.LSeries_eq_exp_LSeries (hs : 1 < s.re) :
    exp (LSeries (fun n ↦ χ n * vonMangoldtLogCoefficients n) s) = L ↗χ s := by
  rw [← eulerProduct_log_eq_LSeries χ hs, LSeries_eulerProduct_exp_log χ hs]

theorem riemannZeta_eq_exp_LSeries {s : ℂ} (hs : 1 < s.re) :
    exp (LSeries (fun n ↦ (vonMangoldtLogCoefficients n : ℂ)) s) =
      riemannZeta s (by exact zeta_regular_of_one_lt_re hs) := by
  rw [← LSeries_one_eq_riemannZeta hs]
  convert LSeries_eq_exp_LSeries (1 : DirichletCharacter ℂ 1) hs
  <;> simp [MulChar.one_apply <| isUnit_of_subsingleton _]

/-- For real `s > 1`, the logarithm of the (real) Riemann zeta function equals
`∑' n, vonMangoldtLogCoefficients n / n ^ s`.
-/
theorem log_riemannZeta_eq {s : ℝ} (hs : 1 < s) :
    Real.log (riemannZeta (s : ℂ) (by exact_mod_cast hs.ne')).re =
      ∑' n : ℕ+, vonMangoldtLogCoefficients n / (n : ℝ) ^ s := by
  have hs' : 1 < (s : ℂ).re := by simpa only [ofReal_re] using hs
  have hsum : LSeries (fun n ↦ (vonMangoldtLogCoefficients n : ℂ)) s =
      ↑(∑' n : ℕ+, vonMangoldtLogCoefficients n / (n : ℝ) ^ s) := by
    rw [LSeries_def, ofReal_tsum]
    refine tsum_congr fun n ↦ ?_
    simp only [ofReal_div, ofReal_cpow (Nat.cast_nonneg (n : ℕ)), ofReal_natCast]
  rw [← riemannZeta_eq_exp_LSeries hs', hsum, exp_ofReal_re, Real.log_exp]

end LogDirichlet
