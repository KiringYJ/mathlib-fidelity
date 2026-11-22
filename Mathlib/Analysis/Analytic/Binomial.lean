/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov, Andrew Yang
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.ConvergenceOnBall
public import Mathlib.Analysis.Complex.OperatorNorm
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.RingTheory.Binomial

/-!
# Binomial Series

This file introduces the binomial series:
$$
\sum_{k=0}^{\infty} \; \binom{a}{k} \; x^k = 1 + a x + \frac{a(a-1)}{2!} x^2 +
  \frac{a(a-1)(a-2)}{3!} x^3 + \cdots
$$
where $a$ is an element of a normed field $\mathbb{K}$,
and $x$ is an element of a normed algebra over $\mathbb{K}$.

## Main Statements

* `binomialSeries_radius_eq_one`: The radius of convergence of the binomial series is `1` when `a`
  is not a natural number.
* `binomialSeries_radius_eq_top_of_nat`: In case `a` is natural, the series converges everywhere,
  since it is finite.
-/

@[expose] public section

open scoped Nat NNReal ENNReal
open FormalMultilinearSeries

universe u v

@[norm_cast]
lemma Complex.ofReal_choose (a : ℝ) (n : ℕ) :
    ↑(Ring.choose a n) = Ring.choose (a : ℂ) n :=
  Ring.map_choose (algebraMap ℝ ℂ) _ _

/-- **Binomial series**: the (scalar) formal multilinear series with coefficients given
by `Ring.choose a`. The sum of this series is `fun x ↦ (1 + x) ^ a` within the radius
of convergence. -/
noncomputable def binomialSeries {𝕂 : Type u} [Field 𝕂] [CharZero 𝕂] (𝔸 : Type v)
    [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸] (a : 𝕂) :
    FormalMultilinearSeries 𝕂 𝔸 𝔸 :=
  .ofScalars 𝔸 (Ring.choose a ·)

@[simp]
theorem binomialSeries_apply {𝕂 : Type u} [Field 𝕂] [CharZero 𝕂] (𝔸 : Type v)
    [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸] (a : 𝕂) {n} (v : Fin n → 𝔸) :
    binomialSeries 𝔸 a n v = Ring.choose a n • (List.ofFn v).prod := by
  simp [binomialSeries, FormalMultilinearSeries.ofScalars]

theorem binomialSeries_eq_ordinaryHypergeometricSeries {𝕂 : Type u} [Field 𝕂] [CharZero 𝕂]
    {𝔸 : Type v} [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸] {a b : 𝕂}
    (h : ∀ (k : ℕ), (k : 𝕂) ≠ -b) :
    binomialSeries 𝔸 a =
    (ordinaryHypergeometricSeries 𝔸 (-a) b b
      (fun n => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
      (ordinaryHypergeometricSeries_pochhammer_ne_zero
        (fun k hk => h k (by simp [hk])))).compContinuousLinearMap (-(.id _ _)) := by
  simp only [binomialSeries, ordinaryHypergeometricSeries,
    FormalMultilinearSeries.ofScalars_comp_neg_id]
  congr! with n
  rw [ordinaryHypergeometricCoefficient, mul_inv_cancel_right₀]
  simp only [Ring.choose_eq_smul, Polynomial.descPochhammer_smeval_eq_ascPochhammer,
    Polynomial.ascPochhammer_smeval_cast, Polynomial.ascPochhammer_smeval_eq_eval,
    ascPochhammer_eval_neg_eq_descPochhammer, descPochhammer_eval_eq_ascPochhammer]
  ring_nf
  simp

/-- The radius of convergence of `binomialSeries 𝔸 a` is `⊤` for natural `a`. -/
theorem binomialSeries_radius_eq_top_of_nat {𝕂 : Type v} [RCLike 𝕂] {𝔸 : Type u}
    [NormedDivisionRing 𝔸] [NormedAlgebra 𝕂 𝔸] {a : ℕ} :
    (binomialSeries 𝔸 (a : 𝕂)).radius = ⊤ := by
  have hb (k : ℕ) : (k : 𝕂) ≠ -(1 : 𝕂) := fun h ↦
    Nat.cast_add_one_ne_zero k (by rw [h]; simp)
  simp [binomialSeries_eq_ordinaryHypergeometricSeries hb,
    ordinaryHypergeometric_radius_top_of_neg_nat₁]

/-- The radius of convergence of `binomialSeries 𝔸 a` is `1`, when `a` is not natural. -/
theorem binomialSeries_radius_eq_one {𝕂 : Type v} [RCLike 𝕂] {𝔸 : Type u} [NormedDivisionRing 𝔸]
    [NormedAlgebra 𝕂 𝔸] {a : 𝕂} (ha : ∀ (k : ℕ), a ≠ k) : (binomialSeries 𝔸 a).radius = 1 := by
  have hb (k : ℕ) : (k : 𝕂) ≠ -(1 : 𝕂) := fun h ↦
    Nat.cast_add_one_ne_zero k (by rw [h]; simp)
  simp only [binomialSeries_eq_ordinaryHypergeometricSeries hb,
    FormalMultilinearSeries.radius_compNeg]
  exact ordinaryHypergeometricSeries_radius_eq_one _ _ _ _ _ _ fun k ↦
    ⟨by simpa only [neg_neg] using (ha k).symm, hb k⟩

theorem binomialSeries_radius_ge_one {𝕂 : Type*} [RCLike 𝕂] {𝔸 : Type*} [NormedDivisionRing 𝔸]
    [NormedAlgebra 𝕂 𝔸] {a : 𝕂} :
    1 ≤ (binomialSeries 𝔸 a).radius := by
  by_cases ha : ∀ (k : ℕ), a ≠ k
  · rw [binomialSeries_radius_eq_one ha]
  · push Not at ha
    rcases ha with ⟨k, rfl⟩
    simp [binomialSeries_radius_eq_top_of_nat]

private theorem one_div_sub_pow_of_one {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜] [CharZero 𝕜] (a : ℕ) {z : 𝕜} (hz : z ≠ 0)
    (hunit : HasFPowerSeriesOnBall (fun x : {x : 𝕜 // 1 - x ≠ 0} ↦ 1 / (1 - x.1) ^ (a + 1))
      (ofScalars 𝕜 (fun n ↦ (Nat.choose (a + n) a : 𝕜))) ⟨0, by simp⟩ 1 Subtype.val) :
    HasFPowerSeriesOnBall (fun x : {x : 𝕜 // z - x ≠ 0} ↦ 1 / (z - x.1) ^ (a + 1))
      (ofScalars 𝕜 (fun n ↦ (z ^ (n + a + 1))⁻¹ * ↑(Nat.choose (a + n) a)))
      ⟨0, by simpa using hz⟩ ‖z‖ₑ Subtype.val := by
  let p := ofScalars 𝕜 (fun n ↦ (Nat.choose (a + n) a : 𝕜))
  let u : 𝕜 →L[𝕜] 𝕜 := z⁻¹ • 1
  have hu (w : 𝕜) : u w = z⁻¹ * w := by simp [u, smul_eq_mul]
  have hp : HasFPowerSeriesOnBall p.sum p (u 0) 1 := by
    rw [map_zero]
    exact (p.hasFPowerSeriesOnBall (hunit.r_pos.trans_le hunit.r_le)).mono hunit.r_pos hunit.r_le
  have hrad : (1 / ‖u‖ₑ) = ‖z‖ₑ := by simp [u, enorm_smul, enorm_inv]
  have hcomp := hp.compContinuousLinearMap (u := u) (x := (0 : 𝕜))
  have hscaled := hcomp.const_smul (c := (z ^ (a + 1))⁻¹)
  have hcoeff : (z ^ (a + 1))⁻¹ • p.compContinuousLinearMap u =
      ofScalars 𝕜 (fun n ↦ (z ^ (n + a + 1))⁻¹ * ↑(Nat.choose (a + n) a)) := by
    ext n
    change (z ^ (a + 1))⁻¹ * p n (fun _ ↦ u 1) = (ofScalars 𝕜 _).coeff n
    rw [coeff_ofScalars, hu, mul_one]
    dsimp only [p]
    rw [ofScalars_apply_eq, smul_eq_mul, inv_pow₀]
    have hpow : z ^ (n + a + 1) = z ^ n * z ^ (a + 1) := by
      rw [Nat.add_assoc, pow_add]
    have hinv : (z ^ (n + a + 1))⁻¹ = (z ^ (a + 1))⁻¹ * (z ^ n)⁻¹ :=
      (inv_inj₀.mpr hpow).trans
        (mul_inv_rev₀ (hab := (hz.isUnit.pow n).mul (hz.isUnit.pow (a + 1))))
    rw [hinv]
    ring
  rw [hrad, hcoeff] at hscaled
  refine ⟨hscaled.r_le, hscaled.r_pos, ?_⟩
  intro w hw
  have heq : 1 - u w.1 = z⁻¹ * (z - w.1) := by rw [hu, mul_sub, inv_mul_cancel₀]
  have hne : 1 - u w.1 ≠ 0 := heq.symm ▸ mul_ne_zero inv_ne_zero w.2
  have hwsmall : ‖w.1‖ < ‖z‖ := by
    have h : (‖w.1‖₊ : ℝ≥0∞) < (‖z‖₊ : ℝ≥0∞) := by
      simpa only [Metric.mem_eball, sub_zero, edist_zero_right, enorm_eq_nnnorm] using hw
    exact_mod_cast h
  have husmall : ‖u w.1‖ < 1 := by
    rw [hu, norm_mul, norm_inv]
    exact (inv_mul_lt_iff₀ (norm_pos_iff.mpr hz)).mpr (by simpa only [mul_one] using hwsmall)
  have hb : u w.1 ∈ Metric.eball (0 : 𝕜) 1 := by
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
    simpa using husmall
  have hvalue : p.sum (u w.1) = 1 / (1 - u w.1) ^ (a + 1) := by
    have hs := hunit.hasSum (y := ⟨u w.1, hne⟩) (by simpa only [sub_zero] using hb)
    simpa only [p, FormalMultilinearSeries.sum, sub_zero] using hs.tsum_eq
  have hlim : (z ^ (a + 1))⁻¹ * p.sum (u w.1) = 1 / (z - w.1) ^ (a + 1) := by
    rw [hvalue, one_div₀, one_div₀]
    calc
      _ = ((1 - u w.1) ^ (a + 1) * z ^ (a + 1))⁻¹ :=
        (mul_inv_rev₀ (hab := (hne.isUnit.pow _).mul (hz.isUnit.pow _))).symm
      _ = _ := inv_inj₀.mpr (by
        rw [← mul_pow, heq, mul_comm _ z, ← mul_assoc, mul_inv_cancel₀, one_mul])
  have hsum := hscaled.hasSum (y := w.1) (by simpa only [id_eq] using hw)
  simpa only [Pi.smul_apply, smul_eq_mul, Function.comp_def, hlim, id_eq] using hsum

namespace Complex

theorem one_add_cpow_hasFPowerSeriesOnBall_zero {a : ℂ} :
    HasFPowerSeriesOnBall (fun x ↦ (1 + x) ^ a) (binomialSeries ℂ a) 0 1 := by
  have hslit (z : ℂ) (hz : z ∈ Metric.eball (0 : ℂ) 1) : 1 + z ∈ slitPlane := by
    apply mem_slitPlane_of_norm_lt_one
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal] at hz
    simpa using hz
  have ha : AnalyticOn ℂ (fun z : ℂ ↦ (1 + z) ^ a) (Metric.eball 0 1) :=
    (analyticOn_const.add analyticOn_id).cpow analyticOn_const hslit
  have hcenter : (0 : ℂ) ∈ Metric.eball (0 : ℂ) 1 := by simp
  obtain ⟨p, hp⟩ := (Metric.isOpen_eball.analyticOn_iff_analyticOnNhd.mp ha) 0 hcenter
  let g (n : ℕ) (z : ℂ) := (descPochhammer ℤ n).smeval a * (1 + z) ^ (a - n)
  have hderiv (n : ℕ) (z : ℂ) (hz : z ∈ Metric.eball (0 : ℂ) 1) :
      HasDerivAt (g n) (g (n + 1) z) z := by
    have h := (((hasDerivAt_id z).const_add (1 : ℂ)).cpow_const (c := a - (n : ℂ))
      (hslit z hz)).const_mul ((descPochhammer ℤ n).smeval a)
    convert h using 1 <;>
      simp only [g, Nat.cast_add, Nat.cast_one, id_eq, mul_one, pow_zero, pow_one,
        show a - (n + 1) = a - n - 1 by ring, descPochhammer_succ_right,
        Polynomial.smeval_mul, Polynomial.smeval_sub, Polynomial.smeval_X,
        Polynomial.smeval_natCast, nsmul_eq_mul, mul_assoc]
  have hiter (n k : ℕ) : HasIteratedDerivAt n (g k) (g (k + n) 0) 0 := by
    induction n generalizing k with
    | zero => rfl
    | succ n ih =>
        refine ⟨g (k + 1), hderiv k 0 hcenter, Or.inr ?_, ?_⟩
        · filter_upwards [Metric.eball_mem_nhds (0 : ℂ) (by simp : (0 : ENNReal) < 1)] with z hz
          exact hderiv k z hz
        · have he : k + 1 + n = k + (n + 1) := by omega
          simpa only [he] using ih (k + 1)
  have hcoeff (n : ℕ) : p.coeff n = Ring.choose a n := by
    have hg : HasIteratedDerivAt n (fun z ↦ (1 + z) ^ a)
        ((descPochhammer ℤ n).smeval a) 0 := by
      simpa [g] using hiter n 0
    have heq := (hp.hasIteratedDerivAt_coeff continuous_id n).unique hg
    apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n) : (n ! : ℂ) ≠ 0)
    simpa only [Ring.descPochhammer_eq_factorial_smul_choose, ← Nat.cast_smul_eq_nsmul ℂ,
      smul_eq_mul] using heq
  have hseries : p = binomialSeries ℂ a := by
    refine FormalMultilinearSeries.ext fun n ↦ ?_
    rw [← ContinuousMultilinearMap.mkPiRing_apply_one_eq_self (p n),
      ← ContinuousMultilinearMap.mkPiRing_apply_one_eq_self (binomialSeries ℂ a n)]
    have hn : p.coeff n = (binomialSeries ℂ a).coeff n := by
      simpa only [binomialSeries, FormalMultilinearSeries.coeff_ofScalars] using hcoeff n
    exact congrArg (ContinuousMultilinearMap.mkPiRing ℂ (Fin n)) hn
  exact ha.hasFPowerSeriesOnSubball (by simp) (hseries ▸ hp) binomialSeries_radius_ge_one

theorem one_add_cpow_hasFPowerSeriesAt_zero {a : ℂ} :
    HasFPowerSeriesAt (fun x ↦ (1 + x) ^ a) (binomialSeries ℂ a) 0 :=
  one_add_cpow_hasFPowerSeriesOnBall_zero.hasFPowerSeriesAt

theorem one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero (a : ℂ) :
    HasFPowerSeriesOnBall (fun x : {x : ℂ // (1 - x) ^ a ≠ 0} ↦ 1 / (1 - x.1) ^ a)
      (.ofScalars ℂ fun n ↦ Ring.choose (a + n - 1) n) ⟨0, by simp⟩ 1 Subtype.val := by
  have H : ((binomialSeries ℂ (-a)).compContinuousLinearMap (-1)) =
      .ofScalars ℂ fun n ↦ Ring.choose (a + n - 1) n := by
    ext n; simp [FormalMultilinearSeries.compContinuousLinearMap, binomialSeries, Ring.choose_neg,
      Units.smul_def, ← pow_add, ← mul_assoc]
  have : HasFPowerSeriesOnBall (fun x ↦ (1 + x) ^ (-a)) (binomialSeries ℂ (-a : ℂ)) (-0) 1 := by
    simpa using one_add_cpow_hasFPowerSeriesOnBall_zero
  have hs : HasFPowerSeriesOnBall (fun x : ℂ ↦ (1 - x) ^ (-a))
      (.ofScalars ℂ fun n ↦ Ring.choose (a + n - 1) n) 0 1 := by
    simpa [Function.comp_def, ← sub_eq_add_neg, H] using
      this.compContinuousLinearMap (u := -1) (x := (0 : ℂ))
  refine ⟨hs.r_le, hs.r_pos, ?_⟩
  intro y hy
  have hsum := hs.hasSum (y := y.1) hy
  simpa only [cpow_neg _ _ (hxy := y.2.isUnit), one_div₀, id_eq] using hsum

theorem one_div_one_sub_pow_hasFPowerSeriesOnBall_zero (a : ℕ) :
    HasFPowerSeriesOnBall (fun x : {x : ℂ // 1 - x ≠ 0} ↦ 1 / (1 - x.1) ^ (a + 1))
      (.ofScalars ℂ (𝕜 := ℂ) fun n ↦ ↑(Nat.choose (a + n) a))
      ⟨0, by simp⟩ 1 Subtype.val := by
  have hs := one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero (a + 1)
  have hcoeff : (ofScalars ℂ fun n ↦ Ring.choose ((a : ℂ) + 1 + n - 1) n) =
      (ofScalars ℂ (𝕜 := ℂ) fun n ↦ ↑(Nat.choose (a + n) a)) := by
    rw [ofScalars_series_eq_iff]
    funext n
    rw [add_right_comm, add_sub_cancel_right, ← Nat.cast_add,
      Ring.choose_natCast, Nat.choose_symm_add]
  rw [hcoeff] at hs
  refine ⟨hs.r_le, hs.r_pos, ?_⟩
  intro y hy
  have hy' : (1 - y.1) ^ ((a : ℂ) + 1) ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl y.2)
  have hsum := hs.hasSum (y := ⟨y.1, hy'⟩) hy
  have hp : (1 - y.1) ^ ((a : ℂ) + 1) = (1 - y.1) ^ (a + 1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using cpow_natCast (1 - y.1) (a + 1)
  have hv : (1 : ℂ) / (1 - y.1) ^ ((a : ℂ) + 1) = 1 / (1 - y.1) ^ (a + 1) := by
    simp only [one_div₀]
    exact inv_inj₀.mpr hp
  exact hv ▸ hsum

theorem one_div_sub_pow_hasFPowerSeriesOnBall_zero (a : ℕ) {z : ℂ} (hz : z ≠ 0) :
    HasFPowerSeriesOnBall (fun x : {x : ℂ // z - x ≠ 0} ↦ 1 / (z - x.1) ^ (a + 1))
      (.ofScalars ℂ (𝕜 := ℂ) fun n ↦ (z ^ (n + a + 1))⁻¹ * ↑(Nat.choose (a + n) a))
      ⟨0, by simpa using hz⟩ ‖z‖ₑ Subtype.val :=
  one_div_sub_pow_of_one a hz (one_div_one_sub_pow_hasFPowerSeriesOnBall_zero a)

theorem one_div_sub_hasFPowerSeriesOnBall_zero {z : ℂ} (hz : z ≠ 0) :
    HasFPowerSeriesOnBall (fun x : {x : ℂ // z - x ≠ 0} ↦ 1 / (z - x.1))
      (.ofScalars ℂ fun n ↦ (z ^ (n + 1))⁻¹) ⟨0, by simpa using hz⟩ ‖z‖ₑ Subtype.val := by
  simpa using one_div_sub_pow_hasFPowerSeriesOnBall_zero (a := 0) hz

theorem one_div_sub_sq_hasFPowerSeriesOnBall_zero {z : ℂ} (hz : z ≠ 0) :
    HasFPowerSeriesOnBall (fun x : {x : ℂ // z - x ≠ 0} ↦ 1 / (z - x.1) ^ 2)
      (.ofScalars ℂ fun n ↦ (z ^ (n + 2))⁻¹ * (n + 1))
      ⟨0, by simpa using hz⟩ ‖z‖ₑ Subtype.val := by
  simpa [add_comm 1] using one_div_sub_pow_hasFPowerSeriesOnBall_zero 1 hz

theorem one_div_one_sub_hasFPowerSeriesOnBall_zero :
    HasFPowerSeriesOnBall (fun x : {x : ℂ // 1 - x ≠ 0} ↦ 1 / (1 - x.1))
      (.ofScalars (𝕜 := ℂ) ℂ 1) ⟨0, by simp⟩ 1 Subtype.val := by
  simpa using! one_div_sub_hasFPowerSeriesOnBall_zero (z := 1)

theorem one_div_one_sub_sq_hasFPowerSeriesOnBall_zero :
    HasFPowerSeriesOnBall (fun x : {x : ℂ // 1 - x ≠ 0} ↦ 1 / (1 - x.1) ^ 2)
      (.ofScalars ℂ fun n ↦ (n + 1 : ℂ)) ⟨0, by simp⟩ 1 Subtype.val := by
  simpa using one_div_sub_sq_hasFPowerSeriesOnBall_zero (z := 1)

/-- `∑ (ai + b) zⁱ = (b - a) / (1 - z) + a / (1 - z)²` -/
theorem hasFPowerSeriesOnBall_ofScalars_mul_add_zero (a b : ℂ) :
    HasFPowerSeriesOnBall (fun x : {x : ℂ // 1 - x ≠ 0} ↦
      (b - a) / (1 - x.1) + a / (1 - x.1) ^ 2)
      (.ofScalars ℂ fun n ↦ a * n + b) ⟨0, by simp⟩ 1 Subtype.val := by
  convert
    (one_div_one_sub_hasFPowerSeriesOnBall_zero.const_smul (c := b - a)).add
      (one_div_one_sub_sq_hasFPowerSeriesOnBall_zero.const_smul (c := a))
  · simp [div_eq_mul_inv₀]
  · ext; simp; ring

lemma one_div_sub_sq_sub_one_div_sq_hasFPowerSeriesOnBall_zero (w x : ℂ) (hw : w ≠ x)
    (hw₀ : w ≠ 0) :
    HasFPowerSeriesOnBall (fun z : {z : ℂ // z - w ≠ 0} ↦ 1 / (z.1 - w) ^ 2 - 1 / w ^ 2)
      (.ofScalars ℂ fun i ↦
        (i + 1) * (w - x) ^ (-↑(i + 2) : ℤ) - i.casesOn (w ^ (-2 : ℤ)) 0)
      ⟨x, sub_ne_zero.mpr hw.symm⟩ ‖w - x‖ₑ Subtype.val := by
  rw [← Pi.sub_def, ← Pi.sub_def, FormalMultilinearSeries.ofScalars_sub]
  refine .sub ?_ ?_
  · have hs := one_div_sub_sq_hasFPowerSeriesOnBall_zero
      (z := w - x) (sub_ne_zero.mpr hw)
    refine ⟨?_, hs.r_pos, ?_⟩
    · simpa only [zpow_neg₀ (sub_ne_zero.mpr hw), zpow_natCast₀, mul_comm] using hs.r_le
    · intro y hy
      have hy' : w - x - (y.1 - x) ≠ 0 := by
        simpa only [sub_sub_sub_cancel_right, sub_ne_zero] using
          (sub_ne_zero.mp y.2).symm
      simpa only [sub_zero, sub_sub_sub_cancel_right, sub_sq_comm w,
        zpow_neg₀ (sub_ne_zero.mpr hw), zpow_natCast₀, mul_comm] using
        hs.hasSum (y := ⟨y.1 - x, hy'⟩) (by simpa using hy)
  · convert! ((hasFPowerSeriesOnBall_const (e := x) (c := 1 / w ^ 2)).comp_domain
      (g := (Subtype.val : {z : ℂ // z - w ≠ 0} → ℂ))
      (x := ⟨x, sub_ne_zero.mpr hw.symm⟩)).mono _ le_top
    · ext (_ | _) <;> simp [zpow_neg₀ hw₀, one_div₀]
    · simpa [sub_eq_zero]

end Complex

namespace Real

attribute [local simp ←] Complex.ofReal_choose in
attribute [-simp] FormalMultilinearSeries.apply_eq_prod_smul_coeff in
theorem one_add_rpow_hasFPowerSeriesOnBall_zero {a : ℝ} :
    HasFPowerSeriesOnBall (fun x ↦ (1 + x) ^ a) (binomialSeries ℝ a) 0 1 := by
  have H : binomialSeries ℂ a = (binomialSeries ℂ (a : ℂ)).restrictScalars (𝕜 := ℝ) := by aesop
  have : HasFPowerSeriesOnBall (fun x ↦ (1 + x) ^ (a : ℂ)) (binomialSeries ℂ a) (.ofRealCLM 0) 1 :=
    Complex.ofRealCLM.map_zero ▸ H ▸ Complex.one_add_cpow_hasFPowerSeriesOnBall_zero.restrictScalars
  convert! (Complex.reCLM.comp_hasFPowerSeriesOnBall this.compContinuousLinearMap).congr ?_
  · ext; simp [Function.comp_def]
  · simp
  · intro x hx; simp_all; norm_cast

theorem one_add_rpow_hasFPowerSeriesAt_zero {a : ℝ} :
    HasFPowerSeriesAt (fun x ↦ (1 + x) ^ a) (binomialSeries ℝ a) 0 :=
  one_add_rpow_hasFPowerSeriesOnBall_zero.hasFPowerSeriesAt

theorem one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero (a : ℝ) :
    HasFPowerSeriesOnBall (fun x : {x : ℝ // (1 - x) ^ a ≠ 0} ↦ 1 / (1 - x.1) ^ a)
      (.ofScalars ℝ fun n ↦ Ring.choose (a + n - 1) n) ⟨0, by simp⟩ 1 Subtype.val := by
  have H : ((binomialSeries ℝ (-a)).compContinuousLinearMap (-1)) =
      .ofScalars ℝ fun n ↦ Ring.choose (a + n - 1) n := by
    ext n
    simp [FormalMultilinearSeries.compContinuousLinearMap, binomialSeries, Ring.choose_neg,
      Units.smul_def, ← pow_add, ← mul_assoc]
  have hneg : HasFPowerSeriesOnBall (fun x ↦ (1 + x) ^ (-a)) (binomialSeries ℝ (-a)) (-0) 1 := by
    simpa using one_add_rpow_hasFPowerSeriesOnBall_zero
  have hs : HasFPowerSeriesOnBall (fun x : ℝ ↦ (1 - x) ^ (-a))
      (.ofScalars ℝ fun n ↦ Ring.choose (a + n - 1) n) 0 1 := by
    simpa [Function.comp_def, ← sub_eq_add_neg, H] using
      hneg.compContinuousLinearMap (u := -1) (x := (0 : ℝ))
  refine ⟨hs.r_le, hs.r_pos, ?_⟩
  intro y hy
  have hyabs : |y.1| < 1 := by simpa [enorm_eq_nnnorm] using! hy
  have hypos : 0 ≤ 1 - y.1 := by grind [le_abs_self y.1]
  simpa only [rpow_neg hypos a (hxy := y.2.isUnit), one_div₀, id_eq] using
    hs.hasSum (y := y.1) hy

theorem one_div_sub_pow_hasFPowerSeriesOnBall_zero (a : ℕ) {r : ℝ} (hr : r ≠ 0) :
    HasFPowerSeriesOnBall (fun x : {x : ℝ // r - x ≠ 0} ↦ 1 / (r - x.1) ^ (a + 1))
      (.ofScalars ℝ (𝕜 := ℝ) fun n ↦ (r ^ (n + a + 1))⁻¹ * ↑(Nat.choose (a + n) a))
      ⟨0, by simpa using hr⟩ ‖r‖ₑ Subtype.val := by
  apply one_div_sub_pow_of_one a hr
  have hs := one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero ((a : ℝ) + 1)
  have hcoeff : (ofScalars ℝ fun n ↦ Ring.choose ((a : ℝ) + 1 + n - 1) n) =
      (ofScalars ℝ (𝕜 := ℝ) fun n ↦ ↑(Nat.choose (a + n) a)) := by
    rw [ofScalars_series_eq_iff]
    funext n
    rw [add_right_comm, add_sub_cancel_right, ← Nat.cast_add,
      Ring.choose_natCast, Nat.choose_symm_add]
  rw [hcoeff] at hs
  refine ⟨hs.r_le, hs.r_pos, ?_⟩
  intro y hy
  have hp : (1 - y.1) ^ ((a : ℝ) + 1) = (1 - y.1) ^ (a + 1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using rpow_natCast (1 - y.1) (a + 1)
  have hne : (1 - y.1) ^ ((a : ℝ) + 1) ≠ 0 := hp.symm ▸ pow_ne_zero (a + 1) y.2
  have hv : (1 : ℝ) / (1 - y.1) ^ ((a : ℝ) + 1) = 1 / (1 - y.1) ^ (a + 1) := by
    simp only [one_div₀]
    exact inv_inj₀.mpr hp
  exact hv ▸ hs.hasSum (y := ⟨y.1, hne⟩) hy

theorem one_div_sub_hasFPowerSeriesOnBall_zero {r : ℝ} (hr : r ≠ 0) :
    HasFPowerSeriesOnBall (fun x : {x : ℝ // r - x ≠ 0} ↦ 1 / (r - x.1))
      (.ofScalars ℝ fun n ↦ (r ^ (n + 1))⁻¹) ⟨0, by simpa using hr⟩ ‖r‖ₑ Subtype.val := by
  simpa using one_div_sub_pow_hasFPowerSeriesOnBall_zero (a := 0) hr

theorem one_div_sub_sq_hasFPowerSeriesOnBall_zero {r : ℝ} (hr : r ≠ 0) :
    HasFPowerSeriesOnBall (fun x : {x : ℝ // r - x ≠ 0} ↦ 1 / (r - x.1) ^ 2)
      (.ofScalars ℝ fun n ↦ (r ^ (n + 2))⁻¹ * (n + 1))
      ⟨0, by simpa using hr⟩ ‖r‖ₑ Subtype.val := by
  simpa [add_comm 1] using one_div_sub_pow_hasFPowerSeriesOnBall_zero 1 hr

theorem one_div_one_sub_hasFPowerSeriesOnBall_zero :
    HasFPowerSeriesOnBall (fun x : {x : ℝ // 1 - x ≠ 0} ↦ 1 / (1 - x.1))
      (.ofScalars (𝕜 := ℝ) ℝ 1) ⟨0, by simp⟩ 1 Subtype.val := by
  simpa using! one_div_sub_hasFPowerSeriesOnBall_zero (r := 1)

theorem one_div_one_sub_sq_hasFPowerSeriesOnBall_zero :
    HasFPowerSeriesOnBall (fun x : {x : ℝ // 1 - x ≠ 0} ↦ 1 / (1 - x.1) ^ 2)
      (.ofScalars ℝ fun n ↦ (n + 1 : ℝ)) ⟨0, by simp⟩ 1 Subtype.val := by
  simpa using one_div_sub_sq_hasFPowerSeriesOnBall_zero (r := 1)

/-- `∑ (ai + b) zⁱ = (b - a) / (1 - z) + a / (1 - z)²` -/
theorem hasFPowerSeriesOnBall_ofScalars_mul_add_zero (a b : ℝ) :
    HasFPowerSeriesOnBall (fun x : {x : ℝ // 1 - x ≠ 0} ↦
      (b - a) / (1 - x.1) + a / (1 - x.1) ^ 2)
      (.ofScalars ℝ (a * · + b)) ⟨0, by simp⟩ 1 Subtype.val := by
  convert!
    (one_div_one_sub_hasFPowerSeriesOnBall_zero.const_smul (c := b - a)).add
      (one_div_one_sub_sq_hasFPowerSeriesOnBall_zero.const_smul (c := a)) using 2
  · simp [div_eq_mul_inv₀]
  · ext; simp; ring

end Real
