/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Integral.PeakFunction
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Fourier inversion formula

In a finite-dimensional real inner product space, we show the Fourier inversion formula, i.e.,
`𝓕⁻ (𝓕 f) v = f v` if `f` and `𝓕 f` are integrable, and `f` is continuous at `v`. This is proved
in `MeasureTheory.Integrable.fourier_inversion`. See also `Continuous.fourier_inversion`
giving `𝓕⁻ (𝓕 f) = f` under an additional continuity assumption for `f`.

We use the following proof. A naïve computation gives
`𝓕⁻ (𝓕 f) v
= ∫_w exp (2 I π ⟪w, v⟫) 𝓕 f (w) dw
= ∫_w exp (2 I π ⟪w, v⟫) ∫_x, exp (-2 I π ⟪w, x⟫) f x dx) dw
= ∫_x (∫_ w, exp (2 I π ⟪w, v - x⟫ dw) f x dx `

However, the Fubini step does not make sense for lack of integrability, and the middle integral
`∫_ w, exp (2 I π ⟪w, v - x⟫ dw` (which one would like to be a Dirac at `v - x`) is not defined.
To gain integrability, one multiplies with a Gaussian function `exp (-c⁻¹ ‖w‖^2)`, with a large
(but finite) `c`. As this function converges pointwise to `1` when `c → ∞`, we get
`∫_w exp (2 I π ⟪w, v⟫) 𝓕 f (w) dw = lim_c ∫_w exp (-c⁻¹ ‖w‖^2 + 2 I π ⟪w, v⟫) 𝓕 f (w) dw`.
One can perform Fubini on the right-hand side for fixed `c`, writing the integral as
`∫_x (∫_w exp (-c⁻¹‖w‖^2 + 2 I π ⟪w, v - x⟫ dw)) f x dx`.
The middle factor is the Fourier transform of a more and more flat function
(converging to the constant `1`), hence it becomes more and more concentrated, around the
point `v`. (Morally, it converges to the Dirac at `v`). Moreover, it has integral one.
Therefore, multiplying by `f` and integrating, one gets a term converging to `f v` as `c → ∞`.
Since it also converges to `𝓕⁻ (𝓕 f) v`, this proves the result.

To check the concentration property of the middle factor and the fact that it has integral one, we
rely on the explicit computation of the Fourier transform of Gaussians.
-/

public section

open Filter MeasureTheory Complex Module Real Bornology

open scoped Topology FourierTransform RealInnerProductSpace Complex

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [SigmaAlgebra V] [BorelSpace V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℂ E] {f : V → E}

namespace Real

lemma tendsto_integral_cexp_sq_smul (hf : Integrable f) :
    Tendsto (fun c : {c : ℝ | IsUnit c} ↦
      ∫ v : V, cexp ((-Checked.inv c.val c.2 * ‖v‖ ^ 2 : ℝ) : ℂ) • f v)
      (comap Subtype.val atTop) (𝓝 (∫ v : V, f v)) := by
  apply tendsto_integral_filter_of_dominated_convergence _ _ _ hf.norm
  · filter_upwards with v
    have hv := (tendsto_inv_atTop_zero.neg.mul_const (‖v‖ ^ 2)).ofReal.cexp.smul_const (f v)
    simp only [neg_zero, zero_mul, ofReal_zero, Complex.exp_zero, one_smul] at hv
    convert hv using 1
    rfl
  · filter_upwards with c using
      AEStronglyMeasurable.smul (Continuous.aestronglyMeasurable (by fun_prop)) hf.1
  · filter_upwards [tendsto_comap.eventually (Ici_mem_atTop (0 : ℝ))] with c (hc : 0 ≤ c.val)
    filter_upwards with v
    rw [norm_smul, Complex.norm_exp, ofReal_re]
    apply mul_le_of_le_one_left (norm_nonneg _)
    exact exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (inv_nonneg.mpr hc)) (sq_nonneg _))

variable [CompleteSpace E]

set_option backward.isDefEq.respectTransparency false in
lemma tendsto_integral_gaussian_smul (hf : Integrable f) (h'f : Integrable (𝓕 f)) (v : V) :
    Tendsto (fun (c : ℝ) ↦
      ∫ w : V, ((π * c) ^ (finrank ℝ V / 2 : ℂ) * cexp (-π ^ 2 * c * ‖v - w‖ ^ 2)) • f w)
    atTop (𝓝 (𝓕⁻ (𝓕 f) v)) := by
  let S : Set ℝ := {c | IsUnit c}
  let a (c : S) : ℝ := Checked.inv c.val c.2
  have A : Tendsto (fun c : S ↦
      ∫ w : V, cexp (-a c * ‖w‖ ^ 2 + 2 * π * I * ⟪v, w⟫) • (𝓕 f) w)
      (comap Subtype.val atTop) (𝓝 (𝓕⁻ (𝓕 f) v)) := by
    have : Integrable (fun w ↦ 𝐞 ⟪w, v⟫ • (𝓕 f) w) := by
      have B : Continuous fun p : V × V => (- innerₗ V) p.1 p.2 := continuous_inner.neg
      simpa using!
        (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar B v).2 h'f
    convert! tendsto_integral_cexp_sq_smul this using 4 with c w
    · rw [Submonoid.smul_def, Real.fourierChar_apply, smul_smul, ← Complex.exp_add, real_inner_comm]
      congr 3
      · simp only [a, ofReal_mul, ofReal_neg, ofReal_pow]
      · push_cast
        ring
    · simp [fourierInv_eq]
  have B : Tendsto (fun c : S ↦
      ∫ w : V, 𝓕 (fun w ↦ cexp (-a c * ‖w‖ ^ 2 + 2 * π * I * ⟪v, w⟫)) w • f w)
      (comap Subtype.val atTop) (𝓝 (𝓕⁻ (𝓕 f) v)) := by
    apply A.congr'
    filter_upwards [tendsto_comap.eventually (Ioi_mem_atTop (0 : ℝ))] with c (hc : 0 < c.val)
    have J : Integrable (fun w ↦ cexp (-a c * ‖w‖ ^ 2 + 2 * π * I * ⟪v, w⟫)) :=
      GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (inv_pos.mpr hc) _ _
    simpa using! (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ V)
      Real.continuous_fourierChar continuous_inner J hf).symm
  have hlarge : Set.range (Subtype.val : S → ℝ) ∈ (atTop : Filter ℝ) := by
    rw [Subtype.range_val]
    exact mem_of_superset (Ioi_mem_atTop (0 : ℝ)) fun c hc ↦ (show 0 < c from hc).ne'.isUnit
  apply (tendsto_comap'_iff hlarge).mp
  apply B.congr'
  filter_upwards [tendsto_comap.eventually (Ioi_mem_atTop (0 : ℝ))] with c (hc : 0 < c.val)
  dsimp only [Function.comp_def]
  congr with w
  rw [fourier_gaussian_innerProductSpace' (inv_pos.mpr hc)]
  have hcUnit : IsUnit (c.val : ℂ) := (ofReal_ne_zero.mpr hc.ne').isUnit
  congr
  · simp [a, div_inv_eq_mul₀]
  · simp [a, div_inv_eq_mul₀]; ring

lemma tendsto_integral_gaussian_smul' (hf : Integrable f) {v : V} (h'f : ContinuousAt f v) :
    Tendsto (fun (c : ℝ) ↦
      ∫ w : V, ((π * c : ℂ) ^ (finrank ℝ V / 2 : ℂ) * cexp (-π ^ 2 * c * ‖v - w‖ ^ 2)) • f w)
    atTop (𝓝 (f v)) := by
  let φ : V → ℝ := fun w ↦ π ^ (finrank ℝ V / 2 : ℝ) * Real.exp (-π ^ 2 * ‖w‖ ^ 2)
  have A : Tendsto (fun (c : ℝ) ↦ ∫ w : V, (c ^ finrank ℝ V * φ (c • (v - w))) • f w)
      atTop (𝓝 (f v)) := by
    apply tendsto_integral_comp_smul_smul_of_integrable'
    · exact fun x ↦ by positivity
    · rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity)]
      have hπ : π / π ^ 2 = π⁻¹ := by
        simp only [pow_two, div_eq_mul_inv₀, mul_inv_rev₀, mul_inv_cancel_left₀]
      simp only [hπ, inv_rpow pi_pos.le, mul_inv_cancel₀]
    · have A : Tendsto (fun (w : V) ↦ π ^ 2 * ‖w‖ ^ 2) (cobounded V) atTop := by
        rw [tendsto_const_mul_atTop_of_pos (by positivity)]
        apply (tendsto_pow_atTop two_ne_zero).comp tendsto_norm_cobounded_atTop
      have B := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (finrank ℝ V / 2) 1
        zero_lt_one |>.comp A |>.const_mul (π ^ (-finrank ℝ V / 2 : ℝ))
      rw [mul_zero] at B
      convert! B using 2 with x
      simp only [neg_mul, one_mul, Function.comp_apply, ← mul_assoc, ← rpow_natCast, φ]
      congr 1
      rw [mul_rpow (by positivity) (by positivity), ← rpow_mul pi_nonneg,
        ← rpow_mul (norm_nonneg _), ← mul_assoc, ← rpow_add pi_pos, mul_comm]
      congr <;> ring
    · exact hf
    · exact h'f
  have B : Tendsto
      (fun (c : ℝ) ↦
        ∫ w : V, ((c ^ (1 / 2 : ℝ)) ^ finrank ℝ V * φ ((c ^ (1 / 2 : ℝ)) • (v - w))) • f w)
      atTop (𝓝 (f v)) :=
    A.comp (tendsto_rpow_atTop (by simp))
  apply B.congr'
  filter_upwards [Ioi_mem_atTop 0] with c (hc : 0 < c)
  congr with w
  rw [← coe_smul]
  congr
  rw [ofReal_mul, ofReal_mul, ofReal_exp, ← mul_assoc]
  congr
  · rw [mul_cpow_ofReal_nonneg pi_nonneg hc.le, ← rpow_natCast, ← rpow_mul hc.le, mul_comm,
      ofReal_cpow pi_nonneg, ofReal_cpow hc.le]
    simp [div_eq_inv_mul₀]
  · norm_cast
    simp only [one_div₀, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, neg_mul, neg_inj,
      ← rpow_natCast, ← rpow_mul hc.le, mul_assoc]
    simp

end Real

variable [CompleteSpace E]

/-- **Fourier inversion formula**: If a function `f` on a finite-dimensional real inner product
space is integrable, and its Fourier transform `𝓕 f` is also integrable, then `𝓕⁻ (𝓕 f) = f` at
continuity points of `f`. -/
theorem MeasureTheory.Integrable.fourierInv_fourier_eq
    (hf : Integrable f) (h'f : Integrable (𝓕 f)) {v : V}
    (hv : ContinuousAt f v) : 𝓕⁻ (𝓕 f) v = f v :=
  tendsto_nhds_unique (Real.tendsto_integral_gaussian_smul hf h'f v)
    (Real.tendsto_integral_gaussian_smul' hf hv)

/-- **Fourier inversion formula**: If a function `f` on a finite-dimensional real inner product
space is continuous, integrable, and its Fourier transform `𝓕 f` is also integrable,
then `𝓕⁻ (𝓕 f) = f`. -/
theorem Continuous.fourierInv_fourier_eq (h : Continuous f)
    (hf : Integrable f) (h'f : Integrable (𝓕 f)) :
    𝓕⁻ (𝓕 f) = f := by
  ext v
  exact hf.fourierInv_fourier_eq h'f h.continuousAt

/-- **Fourier inversion formula**: If a function `f` on a finite-dimensional real inner product
space is integrable, and its Fourier transform `𝓕 f` is also integrable, then `𝓕 (𝓕⁻ f) = f` at
continuity points of `f`. -/
theorem MeasureTheory.Integrable.fourier_fourierInv_eq
    (hf : Integrable f) (h'f : Integrable (𝓕 f)) {v : V}
    (hv : ContinuousAt f v) : 𝓕 (𝓕⁻ f) v = f v := by
  rw [fourierInv_comm]
  exact hf.fourierInv_fourier_eq h'f hv

/-- **Fourier inversion formula**: If a function `f` on a finite-dimensional real inner product
space is continuous, integrable, and its Fourier transform `𝓕 f` is also integrable,
then `𝓕 (𝓕⁻ f) = f`. -/
theorem Continuous.fourier_fourierInv_eq (h : Continuous f)
    (hf : Integrable f) (h'f : Integrable (𝓕 f)) :
    𝓕 (𝓕⁻ f) = f := by
  ext v
  exact hf.fourier_fourierInv_eq h'f h.continuousAt
