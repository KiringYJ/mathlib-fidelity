/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, David Loeffler
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.LSeries.Positivity

/-!
# The L-function of a Dirichlet character does not vanish on Re(s) ≥ 1

The main result in this file is `DirichletCharacter.LFunction_ne_zero_of_one_le_re`:
if `χ` is a Dirichlet character, `s ∈ ℂ` with `1 ≤ s.re`, and either `χ` is nontrivial or `s ≠ 1`,
then the L-function of `χ` does not vanish at `s`.

As a consequence, we have the corresponding statement for the Riemann ζ function:
`riemannZeta_ne_zero_of_one_le_re`, for `s ≠ 1` with `1 ≤ s.re`.

These results are prerequisites for the **Prime Number Theorem** and
**Dirichlet's Theorem** on primes in arithmetic progressions.

## Outline of proofs

We split into two cases: first, the special case of (non-trivial) quadratic characters at `s = 1`;
then the remaining case when either `s ≠ 1` or `χ ^ 2 ≠ 1`.

The first case is handled using a positivity argument applied to the series `L χ s * ζ s`: we show
that this function has non-negative Dirichlet coefficients, is strictly positive for `s ≫ 0`, but
vanishes at `s = -2`, so it must have a pole somewhere in between.

The second case is dealt with using the product
`L(χ^0, 1 + x)^3 L(χ, 1 + x + I * y)^4 L(χ^2, 1 + x + 2 * I * y)`, which
we show has absolute value `≥ 1` for all positive `x` and real `y`; if `L(χ, 1 + I * y) = 0` then
this product would have to tend to 0 as `x → 0`, which is a contradiction.
-/

@[expose] public section

/- NB: Many lemmas (and some defs) in this file are private, since they concern properties of
hypothetical objects which we eventually deduce cannot exist. We have only made public the lemmas
whose hypotheses do not turn out to be contradictory.
-/

open Complex Asymptotics Filter
open ArithmeticFunction hiding log

open scoped Topology

-- We use the ordering on `ℂ` given by comparing real parts for fixed imaginary part
open scoped ComplexOrder

variable {N : ℕ}

namespace DirichletCharacter

section quadratic

/-!
### Convolution of a Dirichlet character with ζ

We define `DirichletCharacter.zetaMul χ` to be the arithmetic function obtained by
taking the product (as arithmetic functions = Dirichlet convolution) of the
arithmetic function `ζ` with `χ`.

We then show that for a quadratic character `χ`, this arithmetic function is multiplicative
and takes nonnegative real values.
-/

/-- The complex-valued arithmetic function that is the convolution of the constant
function `1` with `χ`. -/
noncomputable def zetaMul (χ : DirichletCharacter ℂ N) : ArithmeticFunction ℂ :=
  .zeta * toArithmeticFunction (χ ·)

/-- The arithmetic function `zetaMul χ` is multiplicative. -/
lemma isMultiplicative_zetaMul (χ : DirichletCharacter ℂ N) : χ.zetaMul.IsMultiplicative :=
  isMultiplicative_zeta.natCast.mul <| isMultiplicative_toArithmeticFunction χ

lemma LSeriesSummable_zetaMul (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable χ.zetaMul s := by
  refine ArithmeticFunction.LSeriesSummable_mul (LSeriesSummable_zeta_iff.mpr hs) <|
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n hn ↦ ?_) hs
  simpa only [toArithmeticFunction, coe_mk, hn, ↓reduceIte]
  using norm_le_one χ _

set_option backward.isDefEq.respectTransparency.types false in
lemma zetaMul_prime_pow_nonneg {χ : DirichletCharacter ℂ N} (hχ : χ ^ 2 = 1) {p : ℕ}
    (hp : p.Prime) (k : ℕ) :
    0 ≤ zetaMul χ (p ^ k) := by
  simp only [zetaMul, toArithmeticFunction, coe_zeta_mul_apply, coe_mk,
    Nat.sum_divisors_prime_pow hp, pow_eq_zero_iff', hp.ne_zero, ne_eq, false_and, ↓reduceIte,
    Nat.cast_pow, map_pow]
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ p with h | h | h
  · refine Finset.sum_nonneg fun i _ ↦ ?_
    simp only [h, le_refl, pow_nonneg]
  · refine Finset.sum_nonneg fun i _ ↦ ?_
    simp only [h, one_pow, zero_le_one]
  · simp only [h, neg_one_geom_sum]
    split_ifs
    exacts [le_rfl, zero_le_one]

/-- `zetaMul χ` takes nonnegative real values when `χ` is a quadratic character. -/
lemma zetaMul_nonneg {χ : DirichletCharacter ℂ N} (hχ : χ ^ 2 = 1) (n : ℕ) :
    0 ≤ zetaMul χ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [ArithmeticFunction.map_zero, le_refl]
  · simpa only [χ.isMultiplicative_zetaMul.multiplicative_factorization _ hn] using!
      Finset.prod_nonneg
        fun p hp ↦ zetaMul_prime_pow_nonneg hχ (Nat.prime_of_mem_primeFactors hp) _

/-
### "Bad" Dirichlet characters

Our goal is to show that `L(χ, 1) ≠ 0` when `χ` is a (nontrivial) quadratic Dirichlet character.
To do that, we package the contradictory properties in a (private) structure
`DirichletCharacter.BadChar` and derive further statements eventually leading to a contradiction.

This entire section is private.
-/

/-- The object we're trying to show doesn't exist: A nontrivial quadratic Dirichlet character
whose L-function vanishes at `s = 1`. -/
private structure BadChar (N : ℕ) [NeZero N] where
  /-- The character we want to show cannot exist. -/
  χ : DirichletCharacter ℂ N
  χ_ne : χ ≠ 1
  χ_sq : χ ^ 2 = 1
  hχ : χ.LFunction 1 (Or.inl χ_ne) = 0

variable [NeZero N]

namespace BadChar

/-- The product of the Riemann zeta function with the L-function of `B.χ`.
We will show that `B.F (-2) = 0` but also that `B.F (-2)` must be positive,
giving the desired contradiction. -/
private noncomputable
def F (B : BadChar N) : ℂ → ℂ :=
  fun s ↦ ((s - 1) * HurwitzZeta.hurwitzZetaRegularPart 0 s + reciprocalGammaℝ s) *
    dslope (fun z ↦ LFunction B.χ z (Or.inl B.χ_ne)) 1 s

private lemma F_eq_mul (B : BadChar N) {s : ℂ} (hs : s ≠ 1) :
    B.F s = riemannZeta s hs * LFunction B.χ s (Or.inl B.χ_ne) := by
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [F, dslope_of_ne _ hs, slope_def_field, B.hχ, sub_zero, ← HurwitzZeta.hurwitzZeta_zero,
    HurwitzZeta.hurwitzZeta_eq_regularPart_add hs]
  field

/-- `B.F` agrees with the L-series of `zetaMul χ` on `1 < s.re`. -/
private lemma F_eq_LSeries (B : BadChar N) {s : ℂ} (hs : 1 < s.re) :
    B.F s = LSeries B.χ.zetaMul s := by
  rw [zetaMul, ← coe_mul, LSeries_convolution']
  · have hs' : s ≠ 1 := fun h ↦ by simp only [h, one_re, lt_self_iff_false] at hs
    rw [B.F_eq_mul hs', B.χ.LFunction_eq_LSeries hs]
    congr 1
    · simp_rw [← LSeries_zeta_eq_riemannZeta hs, ← natCoe_apply]
    · exact LSeries_congr B.χ.apply_eq_toArithmeticFunction_apply s
  -- summability side goals from `LSeries_convolution'`
  · exact LSeriesSummable_zeta_iff.mpr hs
  · exact (LSeriesSummable_congr _ fun h ↦ (B.χ.apply_eq_toArithmeticFunction_apply h).symm).mpr <|
      ZMod.LSeriesSummable_of_one_lt_re B.χ hs

/-- If `χ` is a bad character, then `F` is an entire function. -/
private lemma F_differentiable (B : BadChar N) : Differentiable ℂ B.F := by
  refine (((differentiable_id.sub_const 1).mul
    (HurwitzZeta.differentiable_hurwitzZetaRegularPart 0)).add
    differentiable_reciprocalGammaℝ).mul ?_
  rw [← differentiableOn_univ, differentiableOn_dslope univ_mem]
  exact (B.χ.differentiable_LFunction B.χ_ne).differentiableOn

/-- The trivial zero at `s = -2` of the zeta function gives that `F (-2) = 0`.
This is used later to obtain a contradiction. -/
private lemma F_neg_two (B : BadChar N) : B.F (-2 : ℝ) = 0 := by
  have h : riemannZeta (-2) (by norm_num) = 0 := by
    simpa only [Nat.cast_zero, zero_add, mul_one] using riemannZeta_neg_two_mul_nat_add_one 0
  rw [ofReal_neg, ofReal_ofNat, B.F_eq_mul (by norm_num), h, zero_mul]

end BadChar

/-- If `χ` is a nontrivial quadratic Dirichlet character, then `L(χ, 1) ≠ 0`. This is private
since it is later superseded by `LFunction_apply_one_ne_zero`. -/
private theorem LFunction_apply_one_ne_zero_of_quadratic {χ : DirichletCharacter ℂ N}
    (hχ : χ ^ 2 = 1) (χ_ne : χ ≠ 1) :
    χ.LFunction 1 (Or.inl χ_ne) ≠ 0 := by
  intro hL
  -- construct a "bad character" and put together a contradiction.
  let B : BadChar N := { χ := χ, χ_sq := hχ, hχ := hL, χ_ne := χ_ne }
  refine B.F_neg_two.not_gt ?_
  refine ArithmeticFunction.LSeries_positive_of_differentiable_of_eqOn (zetaMul_nonneg hχ)
    (χ.isMultiplicative_zetaMul.map_one ▸ zero_lt_one) B.F_differentiable ?_
    (fun _ ↦ B.F_eq_LSeries) _
  exact LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    fun _ a ↦ χ.LSeriesSummable_zetaMul a

end quadratic

section nonvanishing

variable (χ : DirichletCharacter ℂ N)

-- This is the key positivity lemma that is used to show that the L-function
-- of a Dirichlet character `χ` does not vanish for `s.re ≥ 1` (unless `χ^2 = 1` and `s = 1`).
private lemma re_log_comb_nonneg' {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1) {z : ℂ} (hz : ‖z‖ = 1) :
      0 ≤ 3 * (-log (1 - a)).re + 4 * (-log (1 - a * z)).re + (-log (1 - a * z ^ 2)).re := by
  have hac₀ : ‖(a : ℂ)‖ < 1 := by
    simp only [Complex.norm_of_nonneg ha₀, ha₁]
  have hac₁ : ‖a * z‖ < 1 := by rwa [norm_mul, hz, mul_one]
  have hac₂ : ‖a * z ^ 2‖ < 1 := by rwa [norm_mul, norm_pow, hz, one_pow, mul_one]
  rw [← ((hasSum_re <| hasSum_taylorSeries_neg_log hac₀).mul_left 3).add
    ((hasSum_re <| hasSum_taylorSeries_neg_log hac₁).mul_left 4) |>.add
    (hasSum_re <| hasSum_taylorSeries_neg_log hac₂) |>.tsum_eq]
  refine tsum_nonneg fun n ↦ ?_
  have hc : IsUnit ((n : ℂ) + 1) := (Nat.cast_add_one_ne_zero n).isUnit
  have hr : IsUnit ((n : ℝ) + 1) := (Nat.cast_add_one_ne_zero n).isUnit
  have hdiv (w : ℂ) : (Checked.div w ((n : ℂ) + 1) hc).re =
      Checked.div w.re ((n : ℝ) + 1) hr := by
    simpa only [Nat.cast_succ] using
      div_natCast_re w (n + 1) (hn := (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)).isUnit)
  simp only [← ofReal_pow, hdiv, ofReal_re, mul_pow, mul_re, ofReal_im, zero_mul,
    sub_zero, ← mul_div_assoc₀, ← add_div]
  refine div_nonneg ?_ (by positivity)
  rw [← pow_mul, pow_mul', sq, mul_re, ← sq, ← sq, ← sq_norm_sub_sq_re, norm_pow, hz]
  convert! (show 0 ≤ 2 * a ^ (n + 1) * ((z ^ (n + 1)).re + 1) ^ 2 by positivity) using 1
  ring

-- This is the version of the technical positivity lemma for logarithms of Euler factors.
private lemma re_log_comb_nonneg {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 1 < x) (y : ℝ) :
    0 ≤ 3 * (-log (1 - (1 : DirichletCharacter ℂ N) n * n ^ (-x : ℂ))).re +
          4 * (-log (1 - χ n * n ^ (-(x + I * y)))).re +
          (-log (1 - (χ n ^ 2) * n ^ (-(x + 2 * I * y)))).re := by
  by_cases hn' : IsUnit (n : ZMod N)
  · have hn : (n : ℝ) ^ (-x) < 1 := by
      have hp : IsUnit ((n : ℝ) ^ x) :=
        (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (by omega)) x).ne'.isUnit
      rw [Real.rpow_neg (Nat.cast_nonneg n) x (hxy := hp), inv_lt_one_iff₀]
      exact .inr <| Real.one_lt_rpow (mod_cast one_lt_two.trans_le hn) <| zero_lt_one.trans hx
    have hz : ‖χ n * (n : ℂ) ^ (-(I * y))‖ = 1 := by
      rw [norm_mul, ← hn'.unit_spec, DirichletCharacter.unit_norm_eq_one χ hn'.unit,
        ← ofReal_natCast, norm_cpow_eq_rpow_re_of_pos (mod_cast by lia)]
      simp only [neg_re, mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero, sub_self,
        neg_zero, Real.rpow_zero, one_mul]
    rw [MulChar.one_apply hn', one_mul]
    convert! re_log_comb_nonneg' (by positivity) hn hz using 6
    · simp only [ofReal_cpow n.cast_nonneg (-x), ofReal_natCast, ofReal_neg]
    · congr 2
      rw [neg_add, cpow_add _ _ <| mod_cast by lia, ← ofReal_neg, ofReal_cpow n.cast_nonneg (-x),
        ofReal_natCast, mul_left_comm]
    · rw [neg_add, cpow_add _ _ <| mod_cast by lia, ← ofReal_neg, ofReal_cpow n.cast_nonneg (-x),
        ofReal_natCast, show -(2 * I * y) = (2 : ℕ) * -(I * y) by ring, cpow_nat_mul, mul_pow,
        mul_left_comm]
  · simp only [MulChar.map_nonunit _ hn', zero_mul, sub_zero, log_one, neg_zero, zero_re, mul_zero,
      neg_add_rev, add_zero, pow_two, le_refl]

/-- The logarithms of the Euler factors of a Dirichlet L-series form a summable sequence. -/
lemma summable_neg_log_one_sub_mul_prime_cpow {s : ℂ} (hs : 1 < s.re) :
    Summable fun p : Nat.Primes ↦ -log (1 - χ p * (p : ℂ) ^ (-s)) := by
  have (p : Nat.Primes) : ‖χ p * (p : ℂ) ^ (-s)‖ ≤ (p : ℝ) ^ (-s).re := by
    simpa only [norm_mul, norm_natCast_cpow_of_re_ne_zero _ <| re_neg_ne_zero_of_one_lt_re hs]
      using mul_le_of_le_one_left (by positivity) (χ.norm_le_one _)
  refine (Nat.Primes.summable_rpow.mpr ?_).of_nonneg_of_le (fun _ ↦ norm_nonneg _) this
    |>.of_norm.clog_one_sub.neg
  simp only [neg_re, neg_lt_neg_iff, hs]

private lemma one_lt_re_one_add {x : ℝ} (hx : 0 < x) (y : ℝ) :
    1 < (1 + x : ℂ).re ∧ 1 < (1 + x + I * y).re ∧ 1 < (1 + x + 2 * I * y).re := by
  simp only [add_re, one_re, ofReal_re, lt_add_iff_pos_right, hx, mul_re, I_re, zero_mul, I_im,
    ofReal_im, mul_zero, sub_self, add_zero, re_ofNat, im_ofNat, mul_one, mul_im, and_self]

open scoped LSeries.notation in
/-- For positive `x` and nonzero `y` and a Dirichlet character `χ` we have
`|L(χ^0, 1 + x)^3 * L(χ, 1 + x + I * y)^4 * L(χ^2, 1 + x + 2 * I * y)| ≥ 1`. -/
lemma norm_LSeries_product_ge_one {x : ℝ} (hx : 0 < x) (y : ℝ) :
    ‖L ↗(1 : DirichletCharacter ℂ N) (1 + x) ^ 3 * L ↗χ (1 + x + I * y) ^ 4 *
      L ↗(χ ^ 2 :) (1 + x + 2 * I * y)‖ ≥ 1 := by
  have ⟨h₀, h₁, h₂⟩ := one_lt_re_one_add hx y
  have H₀ := summable_neg_log_one_sub_mul_prime_cpow (N := N) 1 h₀
  have H₁ := summable_neg_log_one_sub_mul_prime_cpow χ h₁
  have H₂ := summable_neg_log_one_sub_mul_prime_cpow (χ ^ 2) h₂
  have hsum₀ := (hasSum_re H₀.hasSum).summable.mul_left 3
  have hsum₁ := (hasSum_re H₁.hasSum).summable.mul_left 4
  have hsum₂ := (hasSum_re H₂.hasSum).summable
  rw [← LSeries_eulerProduct_exp_log _ h₀, ← LSeries_eulerProduct_exp_log χ h₁,
    ← LSeries_eulerProduct_exp_log _ h₂]
  simp only [← exp_nat_mul, Nat.cast_ofNat, ← exp_add, norm_exp, add_re, mul_re,
    re_ofNat, im_ofNat, zero_mul, sub_zero, Real.one_le_exp_iff]
  rw [re_tsum H₀, re_tsum H₁, re_tsum H₂, ← tsum_mul_left, ← tsum_mul_left,
    ← hsum₀.tsum_add hsum₁, ← (hsum₀.add hsum₁).tsum_add hsum₂]
  simpa only [neg_add_rev, neg_re, mul_neg, χ.pow_apply' two_ne_zero, ge_iff_le, add_re, one_re,
    ofReal_re, ofReal_add, ofReal_one] using
      tsum_nonneg fun (p : Nat.Primes) ↦ χ.re_log_comb_nonneg p.prop.two_le h₀ y

variable [NeZero N]

/-- The Dirichlet L-function along the horizontal ray to the right of `1 + I * y`. -/
noncomputable def LFunctionHorizontal (χ : DirichletCharacter ℂ N) (y : ℝ)
    (x : Set.Ioi (0 : ℝ)) : ℂ :=
  LFunction χ (1 + (x : ℝ) + I * y) (Or.inr (by
    intro h
    have hx := (one_lt_re_one_add x.2 y).2.1
    simp [h] at hx))

local notation "𝓝₊" => comap (Subtype.val : Set.Ioi (0 : ℝ) → ℝ) (𝓝 0)

/-- A variant of `DirichletCharacter.norm_LSeries_product_ge_one` in terms of the L-functions. -/
lemma norm_LFunction_product_ge_one (x : Set.Ioi (0 : ℝ)) (y : ℝ) :
    ‖LFunctionHorizontal (1 : DirichletCharacter ℂ N) 0 x ^ 3 * LFunctionHorizontal χ y x ^ 4 *
      LFunctionHorizontal (χ ^ 2) (2 * y) x‖ ≥ 1 := by
  have h₀ := (one_lt_re_one_add x.2 0).2.1
  have h₁ := (one_lt_re_one_add x.2 y).2.1
  have h₂ := (one_lt_re_one_add x.2 (2 * y)).2.1
  have hp : I * ((2 * y : ℝ) : ℂ) = 2 * I * y := by push_cast; ring
  simp only [LFunctionHorizontal]
  rw [LFunction_eq_LSeries _ h₀, LFunction_eq_LSeries _ h₁, LFunction_eq_LSeries _ h₂]
  simpa only [ofReal_zero, mul_zero, add_zero, hp] using norm_LSeries_product_ge_one χ x.2 y

lemma LFunctionTrivChar_isBigO_near_one_horizontal :
    LFunctionHorizontal (1 : DirichletCharacter ℂ N) 0 =O[𝓝₊]
      fun x ↦ Checked.inv ((x : ℝ) : ℂ) (ofReal_ne_zero.mpr x.2.ne').isUnit := by
  have hc : Continuous (fun x : ℝ ↦ LFunctionTrivChar₁ N (1 + x)) :=
    (differentiable_LFunctionTrivChar₁ N).continuous.comp (by fun_prop)
  have ht : Tendsto (fun x : Set.Ioi (0 : ℝ) ↦ LFunctionTrivChar₁ N (1 + (x : ℝ))) 𝓝₊
      (𝓝 (LFunctionTrivChar₁ N (1 + (0 : ℝ)))) := (hc.tendsto 0).comp tendsto_comap
  obtain ⟨c, hbound⟩ := isBigO_iff.mp (ht.isBigO_one ℂ)
  refine isBigO_iff.mpr ⟨c, ?_⟩
  filter_upwards [hbound] with x hx
  have hne : ((x : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr x.2.ne'
  have hnorm : LFunctionTrivChar₁ N (1 + (x : ℝ)) =
      (x : ℝ) * LFunctionHorizontal (1 : DirichletCharacter ℂ N) 0 x := by
    rw [LFunctionTrivChar₁, LFunction₁_eq_mul _ (add_ne_left.mpr hne), add_sub_cancel_left]
    simp [LFunctionHorizontal]
  rw [hnorm, norm_mul, norm_one, mul_one] at hx
  rw [norm_inv, ← div_eq_mul_inv₀, le_div_iff₀' (norm_pos_iff.mpr hne)]
  simpa only [mul_comm] using hx

omit [NeZero N] in
private lemma one_add_I_mul_ne_one_or {y : ℝ} (hy : y ≠ 0 ∨ χ ≠ 1) :
    1 + I * y ≠ 1 ∨ χ ≠ 1 := by
  simpa only [ne_eq, add_eq_left, _root_.mul_eq_zero, I_ne_zero, ofReal_eq_zero, false_or]
    using hy

omit [NeZero N] in
private lemma tendsto_LFunctionHorizontal_point {y : ℝ} (hy : y ≠ 0 ∨ χ ≠ 1) :
    Tendsto
      (fun x : Set.Ioi (0 : ℝ) ↦ (⟨1 + (x : ℝ) + I * y, Or.inr (by
        intro h
        have hx := (one_lt_re_one_add x.2 y).2.1
        simp [h] at hx)⟩ : LFunctionDomain χ))
      𝓝₊ (𝓝 (⟨1 + I * y, (one_add_I_mul_ne_one_or χ hy).symm⟩ : LFunctionDomain χ)) := by
  apply tendsto_subtype_rng.mpr
  have hc : Continuous (fun x : ℝ ↦ (1 : ℂ) + x + I * y) := by fun_prop
  have ht := (hc.tendsto 0).comp
    (tendsto_comap : Tendsto (Subtype.val : Set.Ioi (0 : ℝ) → ℝ) 𝓝₊ (𝓝 0))
  change Tendsto (fun x : Set.Ioi (0 : ℝ) ↦ (1 : ℂ) + (x : ℝ) + I * y) 𝓝₊
    (𝓝 ((1 : ℂ) + (0 : ℝ) + I * y)) at ht
  simpa only [ofReal_zero, add_zero] using ht

lemma LFunction_isBigO_horizontal {y : ℝ} (hy : y ≠ 0 ∨ χ ≠ 1) :
    LFunctionHorizontal χ y =O[𝓝₊] fun _ ↦ (1 : ℂ) := by
  have hd := χ.differentiableAt_LFunction _ (one_add_I_mul_ne_one_or χ hy)
  have hc := hd.continuousAt continuousAt_subtype_val
  exact (hc.tendsto.comp (tendsto_LFunctionHorizontal_point χ hy)).isBigO_one ℂ

private lemma LFunction_isBigO_horizontal_of_eq_zero {y : ℝ} (hy : y ≠ 0 ∨ χ ≠ 1)
    (h : LFunction χ (1 + I * y) (one_add_I_mul_ne_one_or χ hy).symm = 0) :
    LFunctionHorizontal χ y =O[𝓝₊] fun x ↦ ((x : ℝ) : ℂ) := by
  have hd := (χ.differentiableAt_LFunction _ (one_add_I_mul_ne_one_or χ hy)).isBigO_sub
  have hb := hd.comp_tendsto (tendsto_LFunctionHorizontal_point χ hy)
  have he : ∀ x : Set.Ioi (0 : ℝ), 1 + (x : ℝ) + I * y - (1 + I * y) = (x : ℂ) := by
    intro x
    ring
  change (fun x ↦ LFunctionHorizontal χ y x -
    LFunction χ (1 + I * y) (one_add_I_mul_ne_one_or χ hy).symm) =O[𝓝₊]
      (fun x : Set.Ioi (0 : ℝ) ↦ 1 + (x : ℝ) + I * y - (1 + I * y)) at hb
  simpa only [h, sub_zero, he] using hb

omit [NeZero N] in
private lemma quadratic_or_horizontal_domain {t : ℝ} (h : χ ^ 2 ≠ 1 ∨ t ≠ 0) :
    t ≠ 0 ∨ χ ≠ 1 := h.symm.imp_right fun hχ htriv ↦ hχ (by rw [htriv, one_pow])

-- intermediate statement, special case of the next theorem
private lemma LFunction_ne_zero_of_not_quadratic_or_ne_one {t : ℝ} (h : χ ^ 2 ≠ 1 ∨ t ≠ 0) :
    LFunction χ (1 + I * t)
      (one_add_I_mul_ne_one_or χ (quadratic_or_horizontal_domain χ h)).symm ≠ 0 := by
  intro Hz
  have hz₁ := quadratic_or_horizontal_domain χ h
  have hz₂ : 2 * t ≠ 0 ∨ χ ^ 2 ≠ 1 :=
    h.symm.imp_left <| mul_ne_zero two_ne_zero
  have help (x : Set.Ioi (0 : ℝ)) :
      Checked.inv ((x : ℝ) : ℂ) (ofReal_ne_zero.mpr x.2.ne').isUnit ^ 3 *
        ((x : ℝ) : ℂ) ^ 4 * 1 = (x : ℂ) := by
    rw [inv_pow₀, pow_succ _ 3, ← mul_assoc, inv_mul_cancel₀, one_mul, mul_one]
  -- put together the various `IsBigO` statements and `norm_LFunction_product_ge_one`
  -- to derive a contradiction
  have H₀ : (fun _ : Set.Ioi (0 : ℝ) ↦ (1 : ℝ)) =O[𝓝₊]
      fun x ↦ LFunctionHorizontal (1 : DirichletCharacter ℂ N) 0 x ^ 3 *
        LFunctionHorizontal χ t x ^ 4 * LFunctionHorizontal (χ ^ 2) (2 * t) x :=
    IsBigO.of_bound' <| Eventually.of_forall
      fun x ↦ (norm_one (α := ℝ)).symm ▸ (χ.norm_LFunction_product_ge_one x t).le
  have H := ((LFunctionTrivChar_isBigO_near_one_horizontal (N := N)).pow 3 |>.mul
    ((χ.LFunction_isBigO_horizontal_of_eq_zero hz₁ Hz).pow 4)).mul
    (LFunction_isBigO_horizontal _ hz₂)
  simp only [help] at H
  -- go via absolute value to translate into a statement over `ℝ`
  replace H := (H₀.trans H).norm_right
  simp only [norm_real] at H
  have : (𝓝₊).NeBot := by
    rw [← map_neBot_iff (Subtype.val : Set.Ioi (0 : ℝ) → ℝ), map_comap, Subtype.range_coe]
    exact inferInstanceAs (𝓝[>] (0 : ℝ)).NeBot
  exact isLittleO_irrefl (.of_forall (fun _ ↦ one_ne_zero)) <|
    H.of_norm_right.trans_isLittleO <| isLittleO_id_one.comp_tendsto tendsto_comap

/-- If `χ` is a Dirichlet character, then `L(χ, s)` does not vanish when `s.re = 1`
except when `χ` is trivial and `s = 1` (then `L(χ, s)` has a simple pole at `s = 1`). -/
theorem LFunction_ne_zero_of_re_eq_one {s : ℂ} (hs : s.re = 1) (hχs : χ ≠ 1 ∨ s ≠ 1) :
    LFunction χ s hχs ≠ 0 := by
  by_cases h : χ ^ 2 = 1 ∧ s = 1
  · obtain ⟨hquad, rfl⟩ := h
    exact LFunction_apply_one_ne_zero_of_quadratic hquad (hχs.resolve_right (fun h ↦ h rfl))
  · have hs' : s = 1 + I * s.im := by
      conv_lhs => rw [← re_add_im s, hs, ofReal_one, mul_comm]
    rw [not_and_or, ← ne_eq, ← ne_eq, hs', add_ne_left] at h
    replace h : χ ^ 2 ≠ 1 ∨ s.im ≠ 0 :=
      h.imp_right (fun H ↦ by exact_mod_cast right_ne_zero_of_mul H)
    have he : (⟨s, hχs⟩ : LFunctionDomain χ) =
        ⟨1 + I * s.im, (one_add_I_mul_ne_one_or χ (quadratic_or_horizontal_domain χ h)).symm⟩ :=
      Subtype.ext hs'
    change LFunctionOn χ ⟨s, hχs⟩ ≠ 0
    rw [he]
    exact χ.LFunction_ne_zero_of_not_quadratic_or_ne_one h

/-- If `χ` is a Dirichlet character, then `L(χ, s)` does not vanish for `s.re ≥ 1`
except when `χ` is trivial and `s = 1` (then `L(χ, s)` has a simple pole at `s = 1`). -/
theorem LFunction_ne_zero_of_one_le_re ⦃s : ℂ⦄ (hχs : χ ≠ 1 ∨ s ≠ 1) (hs : 1 ≤ s.re) :
    LFunction χ s hχs ≠ 0 :=
  hs.eq_or_lt.casesOn (fun hs ↦ LFunction_ne_zero_of_re_eq_one χ hs.symm hχs)
    fun hs ↦ LFunction_eq_LSeries χ hs ▸ LSeries_ne_zero_of_one_lt_re χ hs

-- Interesting special case:
variable {χ} in
/-- The L-function of a nontrivial Dirichlet character does not vanish at `s = 1`. -/
theorem LFunction_apply_one_ne_zero (hχ : χ ≠ 1) : LFunction χ 1 (Or.inl hχ) ≠ 0 :=
  LFunction_ne_zero_of_one_le_re χ (.inl hχ) <| one_re ▸ le_rfl

/-- The Riemann zeta function does not vanish at `s` if `s ≠ 1` and `s.re ≥ 1`. -/
lemma _root_.riemannZeta_ne_zero_of_one_le_re ⦃s : ℂ⦄ (hs₀ : s ≠ 1) (hs : 1 ≤ s.re) :
    riemannZeta s hs₀ ≠ 0 :=
  LFunction_modOne_eq (χ := 1) hs₀ ▸ LFunction_ne_zero_of_one_le_re _ (.inr hs₀) hs

end nonvanishing

end DirichletCharacter
